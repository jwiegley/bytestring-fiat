Require Import
  ByteString.Lib.Tactics
  ByteString.Lib.Nomega
  ByteString.Lib.Fiat
  ByteString.Lib.FromADT
  ByteString.Lib.TupleEnsembles
  ByteString.Lib.FunMaps
  ByteString.Memory
  ByteString.Heap
  ByteString.HeapState
  ByteString.ByteString
  ByteString.ByteStringHeap
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx
  Hask.Control.Monad
  Hask.Control.Monad.State
  Hask.Control.Monad.Free.

Module HeapFFI (M : WSfun N_as_DT).

Module Import Heap := Heap M.

Import HeapState.
Import FMapExt.

Module Import FunMaps := FunMaps N_as_DT M.

Open Scope N_scope.

Inductive DSL (r : Type) :=
  | MAlloc : Size -> (Ptr -> r) -> DSL r
  | MFree : Ptr -> r -> DSL r.

Program Instance DSL_Functor : Functor DSL := {
  fmap := fun _ _ f x =>
            match x with
            | MAlloc x h => MAlloc x (compose f h)
            | MFree x h => MFree x (f h)
            end
}.

Definition FFI := Free DSL.

Definition nextFreeAddr (h : M.t Size) : Ptr :=
  let final := M.fold (fun k e z => if fst z <=? k
                                    then (k, e)
                                    else z) h (0, 0) in
  fst final + snd final.

Program Definition ffiState `(f : FFI ()) : HeapState :=
  let go A (x : DSL A) : State HeapState A :=
      h <- get;
      match h with
      | Build_HeapState allocs data =>
        match x with
        | MAlloc size f =>
          let addr := nextFreeAddr allocs in
          put (Build_HeapState (M.add addr size allocs) data) ;;
          pure (f addr)
        | MFree addr r =>
          put (Build_HeapState (M.remove addr allocs) data) ;;
          pure r
        end
      end in
  snd (foldFree go f (Build_HeapState (M.empty _) (M.empty _))).

Definition Mem_AbsR (or : Rep HeapSpec) (nr : FFI ()) :=
  match ffiState nr with
    Build_HeapState heap_rep mem_rep =>
    M.Equal heap_rep (resvs or) /\
    M.Equal mem_rep  (bytes or)
  end.

(** In order to refine to a computable heap, we have to add the notion of
    "free memory", from which addresses may be allocated. A further
    optimization here would be to add a free list, to which free blocks are
    returned, in order avoid gaps in the heap. A yet further optimization
    would be to better manage the free space to avoid fragmentation. The
    implementation below simply grows the heap with every allocation. *)

Program Instance FFI_Alternative : Alternative FFI.
Obligation 1.
Admitted.

Theorem HeapFFI : FullySharpened (HeapSpec (m:=FFI)).
Proof.
  start sharpening ADT.

  hone representation over HeapSpec using Mem_AbsR.

  (* refine method emptyS. *)
  {
    rewrite refine_pick.
      instantiate (1 := ret (Pure ())).
      finish honing.

    intros.
    computes_to_inv; subst.
    split; reflexivity.
  }

  (* refine method allocS. *)
  {
    pose proof (liftF (MAlloc (` d) id)) as next.
    unfold find_free_block.
    refine pick val (Some (nextFreeAddr (resvs r_o))).
    {
      simplify with monad laws; simpl.

      refine pick val next.
        simplify with monad laws; simpl.
        rewrite Heqmalloc.
        finish honing.

      symmetry in Heqmalloc.
      destruct malloc as [addr env'].

      eapply malloc_correct; eauto.
    }

    remember (mallocBytes _ _ _) as malloc.
    symmetry in Heqmalloc.
    destruct malloc as [addr env'].
    eapply malloc_correct
           (* jww (2016-09-07): It should be possible to derive this *)
      with (r':={| resvs := M.add addr (` d) (resvs r_o)
                 ; bytes := bytes r_o |})
      in Heqmalloc; eauto.
    breakdown; destruct_computations.
    tsubst; assumption.
  }

  (* refine method freeS. *)
  {
    refine pick val (freeBytes ffi d r_n).
      simplify with monad laws; simpl.
      finish honing.

    eapply free_correct; eauto.
  }

  (* refine method reallocS. *)
  {
    unfold find_free_block.
    refine pick val (fst (reallocBytes ffi d (` d0) r_n)).
    {
      remember (reallocBytes _ _ _ _) as realloc.
      simplify with monad laws.

      refine pick val (snd realloc).
        simplify with monad laws.
        rewrite Heqrealloc.
        finish honing.

      symmetry in Heqrealloc.
      destruct realloc as [addr env'].
      eapply realloc_correct; eauto.
    }

    remember (reallocBytes _ _ _ _) as realloc.
    symmetry in Heqrealloc.
    destruct realloc as [addr env'].
    eapply realloc_correct
      with (r':={| resvs := M.add addr (` d0) (M.remove d (resvs r_o))
                 ; bytes := Ifopt M.find d (resvs r_o) as sz
                            Then copy_bytes d addr (N.min sz (` d0)) (bytes r_o)
                            Else bytes r_o |})
      in Heqrealloc; eauto.
    breakdown; destruct_computations.
    tsubst; assumption.
  }

  (* refine method peekS. *)
  {
    refine pick val (fst (peekPtr ffi d r_n)).
      simplify with monad laws.
      refine pick val r_n.
        simplify with monad laws.
        finish honing.
      assumption.

    remember (peekPtr _ _ _) as peek.
    symmetry in Heqpeek.
    destruct peek as [w env'].
    eapply peek_correct in Heqpeek; eauto.
    breakdown; destruct_computations.
    inversion H3; clear H5; subst.
    simpl in *.
    eassumption.
  }

  (* refine method pokeS. *)
  {
    refine pick val (pokePtr ffi d d0 r_n).
      simplify with monad laws.
      finish honing.

    eapply poke_correct; eauto.
  }

  (* refine method memcpyS. *)
  {
    refine pick val (copyBytes ffi d d1 d0 r_n).
      simplify with monad laws.
      finish honing.

    eapply memcpy_correct; eauto.
  }

  (* refine method memsetS. *)
  {
    refine pick val (fillBytes ffi d d1 d0 r_n).
      simplify with monad laws.
      finish honing.

    eapply memset_correct; eauto.
  }

  finish_SharpeningADT_WithoutDelegation.
Defined.

Definition HeapFFI' {Env : Type} (ffi : HeapIntf Env) (mem : Mem Env) :=
  Eval simpl in projT1 (HeapFFI ffi mem).
Print HeapFFI'.

End HeapFFI.
