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
  Coq.Structures.DecidableTypeEx.

Module HeapFFI (M : WSfun N_as_DT).

Module Import Heap := Heap M.

Import HeapState.
Import FMapExt.

Module Import FunMaps := FunMaps N_as_DT M.

Open Scope N_scope.

Record Mem (Env : Type) := {
  heap_ptr : Env;
  heap_rep : EMap Ptr Size;
  mem_rep  : EMap Ptr Word;
}.

Definition Mem_AbsR (Env : Type) (or : Rep HeapSpec) (nr : Mem Env) :=
  Map_AbsR eq (heap_rep nr) (resvs or) /\
  Map_AbsR eq (mem_rep nr)  (bytes or).

Record HeapIntf (Env : Type) := {
  nullPtr      : Ptr;
  alignPtr     : Ptr -> Size -> Ptr;
  plusPtr      : Ptr -> Size -> Ptr;
  minusPtr     : Ptr -> Size -> Ptr;

  mallocBytes  : Size -> Mem Env -> (Ptr * Mem Env);
  freeBytes    : Ptr -> Mem Env -> Mem Env;
  reallocBytes : Ptr -> Size -> Mem Env -> (Ptr * Mem Env);

  peekPtr      : Ptr -> Mem Env -> (Word * Mem Env);
  peekByteOff  : Ptr -> Size -> Mem Env -> (Word * Mem Env);
  pokePtr      : Ptr -> Word -> Mem Env -> Mem Env;
  pokeByteOff  : Ptr -> Size -> Word -> Mem Env -> Mem Env;

  copyBytes    : Ptr -> Ptr -> Size -> Mem Env -> Mem Env;
  fillBytes    : Ptr -> Word -> Size -> Mem Env -> Mem Env;

  newheap_relates : forall mem, @Mem_AbsR Env newHeapState mem;

  malloc_relates : forall env env' sz ptr,
    mallocBytes (` sz) env = (ptr, env')
      -> forall r r', alloc r sz ↝ (r', ptr)
      -> Mem_AbsR r' env';

  malloc_sound : forall env env' sz ptr,
    mallocBytes sz env = (ptr, env') ->
      All (fun ptr' sz' => ~ overlaps ptr' sz' ptr sz) (heap_rep env);

  free_relates : forall env env' ptr,
    freeBytes ptr env = env'
      -> forall r r', free r ptr ↝ (r', tt)
      -> Mem_AbsR r' env';

  realloc_relates : forall env env' old sz new,
    reallocBytes old (` sz) env = (new, env')
      -> forall r r', realloc r old sz ↝ (r', new)
      -> Mem_AbsR r' env';

  realloc_sound : forall env env' sz old new,
    reallocBytes old sz env = (new, env') ->
      All (fun ptr' sz' => ~ overlaps ptr' sz' new sz)
          (Remove old (heap_rep env));

  peek_relates : forall env env' ptr w,
    peekPtr ptr env = (w, env')
      -> forall r r', peek r ptr ↝ (r', w)
      -> Mem_AbsR r' env';

  peek_sound : forall env env' ptr w,
    Lookup ptr w (mem_rep env) -> peekPtr ptr env = (w, env');

  poke_relates : forall env env' ptr w,
    pokePtr ptr w env = env'
      -> forall r r', poke r ptr w ↝ (r', tt)
      -> Mem_AbsR r' env';

  memcpy_relates : forall env env' addr1 addr2 sz,
    copyBytes addr1 sz addr2 env = env'
      -> forall r r', memcpy r addr1 addr2 sz ↝ (r', tt)
      -> Mem_AbsR r' env';

  memset_relates : forall env env' addr w sz,
    fillBytes addr w sz env = env'
      -> forall r r', memset r addr sz w ↝ (r', tt)
      -> Mem_AbsR r' env'
}.

(** In order to refine to a computable heap, we have to add the notion of
    "free memory", from which addresses may be allocated. A further
    optimization here would be to add a free list, to which free blocks are
    returned, in order avoid gaps in the heap. A yet further optimization
    would be to better manage the free space to avoid fragmentation. The
    implementation below simply grows the heap with every allocation. *)

Theorem HeapFFI {Env : Type} (ffi : HeapIntf Env) (mem : Mem Env) :
  FullySharpened HeapSpec.
Proof.
  intros.
  start sharpening ADT.

  hone representation over HeapSpec using (@Mem_AbsR Env).

  (* refine method emptyS. *)
  {
    rewrite refine_pick.
      instantiate (1 := ret mem).
      finish honing.

    intros.
    apply newheap_relates; assumption.
  }

  (* refine method allocS. *)
  {
    unfold find_free_block.
    refine pick val (fst (mallocBytes ffi (` d) r_n)).
    {
      remember (mallocBytes _ _ _) as malloc.
      simplify with monad laws; simpl.

      refine pick val (snd malloc).
        simplify with monad laws; simpl.
        rewrite Heqmalloc.
        finish honing.

      symmetry in Heqmalloc.
      destruct malloc as [addr env'].

      eapply malloc_relates; eauto.
      repeat econstructor; apply PickComputes.

      destruct H0.
      pose proof (malloc_sound _ _ Heqmalloc) as H2.
      eapply All_Map_AbsR in H2; relational; eauto.
      constructor; split; nomega_.
    }

    remember (mallocBytes _ _ _) as malloc.
    symmetry in Heqmalloc.
    destruct malloc as [addr env'].

    destruct H0.
    pose proof (malloc_sound _ _ Heqmalloc) as H2.
    eapply All_Map_AbsR in H2; relational; eauto.
    constructor; split; nomega_.
  }

  (* refine method freeS. *)
  {
    refine pick val (freeBytes ffi d r_n).
      simplify with monad laws; simpl.
      finish honing.

    eapply free_relates; auto.
    repeat econstructor.
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

      eapply realloc_relates; eauto.
      repeat econstructor; apply PickComputes.

      destruct H0.
      pose proof (realloc_sound _ _ Heqrealloc) as H2.
      eapply All_Map_AbsR in H2; relational; eauto;
      related_maps; eauto.
      constructor; split; nomega_.
    }

    remember (reallocBytes _ _ _ _) as realloc.
    symmetry in Heqrealloc.
    destruct realloc as [addr env'].

    destruct H0.
    pose proof (realloc_sound _ _ Heqrealloc) as H2.
    eapply All_Map_AbsR in H2; relational; eauto;
    related_maps; eauto.
    constructor; split; nomega_.
  }

  (* refine method peekS. *)
  {
    refine pick val (fst (peekPtr ffi d r_n)).
      simplify with monad laws.
      refine pick val r_n.
        simplify with monad laws.
        finish honing.
      assumption.

    intros.
    apply H0 in H1; destruct H1 as [? [? ?]]; subst.
    eapply (peek_sound ffi r_n r_n d) in H1; eauto.
    rewrite H1.
    reflexivity.
  }

  (* refine method pokeS. *)
  {
    refine pick val (pokePtr ffi d d0 r_n).
      simplify with monad laws.
      finish honing.

    eapply poke_relates; eauto.
    repeat econstructor.
  }

  (* refine method memcpyS. *)
  {
    refine pick val (copyBytes ffi d d1 d0 r_n).
      simplify with monad laws.
      finish honing.

    eapply memcpy_relates; eauto.
    repeat econstructor.
  }

  (* refine method memsetS. *)
  {
    refine pick val (fillBytes ffi d d1 d0 r_n).
      simplify with monad laws.
      finish honing.

    eapply memset_relates; eauto.
    repeat econstructor.
  }

  finish_SharpeningADT_WithoutDelegation.
Defined.

Definition HeapFFI' {Env : Type} (ffi : HeapIntf Env) (mem : Mem Env) :=
  Eval simpl in projT1 (HeapFFI ffi mem).
Print HeapFFI'.

End HeapFFI.
