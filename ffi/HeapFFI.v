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
  heap_rep : EMap (Ptr Word) Size;
  mem_rep  : EMap (Ptr Word) Word;
}.

Definition Mem_AbsR (Env : Type) (or : Rep HeapSpec) (nr : Mem Env) :=
  Map_AbsR eq (heap_rep nr) (resvs or) /\
  Map_AbsR eq (mem_rep nr)  (bytes or).

Record HeapIntf (Env : Type) := {
  nullPtr      : Ptr Word;
  alignPtr     : Ptr Word -> Size -> Ptr Word;
  plusPtr      : Ptr Word -> Size -> Ptr Word;
  minusPtr     : Ptr Word -> Size -> Ptr Word;

  mallocBytes  : Size -> Mem Env -> (Ptr Word * Mem Env);
  freeBytes    : Ptr Word -> Mem Env -> Mem Env;
  reallocBytes : Ptr Word -> Size -> Mem Env -> (Ptr Word * Mem Env);

  peekPtr      : Ptr Word -> Mem Env -> (Word * Mem Env);
  peekByteOff  : Ptr Word -> Size -> Mem Env -> (Word * Mem Env);
  pokePtr      : Ptr Word -> Word -> Mem Env -> Mem Env;
  pokeByteOff  : Ptr Word -> Size -> Word -> Mem Env -> Mem Env;

  copyBytes    : Ptr Word -> Ptr Word -> Size -> Mem Env -> Mem Env;
  fillBytes    : Ptr Word -> Word -> Size -> Mem Env -> Mem Env;

  peekArray    : Ptr Word -> Size -> Mem Env -> (list Word * Mem Env);
  pokeArray    : Ptr Word -> list Word -> Mem Env -> Mem Env;

  empty_correct : forall mem, @Mem_AbsR Env newHeapState mem;

  malloc_correct : forall r env env' sz ptr,
    Mem_AbsR r env
      -> mallocBytes (` sz) env = (ptr, env')
      -> forall r', alloc r sz ↝ (r', ptr) /\ Mem_AbsR r' env';

  free_correct : forall r env env' ptr,
    Mem_AbsR r env
      -> freeBytes ptr env = env'
      -> forall r', free r ptr ↝ r' /\ Mem_AbsR r' env';

  realloc_correct : forall r env env' old sz new,
    Mem_AbsR r env
      -> reallocBytes old (` sz) env = (new, env')
      -> forall r', realloc r old sz ↝ (r', new) /\ Mem_AbsR r' env';

  peek_correct : forall r env env' ptr off w,
    Mem_AbsR r env
      -> peekPtr (Memory.plusPtr ptr off) env = (w, env')
      -> forall r', peek r ptr off ↝ (r', w) /\ Mem_AbsR r' env';

  poke_correct : forall r env env' ptr off w,
    Mem_AbsR r env
      -> pokePtr (Memory.plusPtr ptr off) w env = env'
      -> forall r', poke r ptr off w ↝ r' /\ Mem_AbsR r' env';

  memcpy_correct : forall r env env' addr1 off1 addr2 off2 sz,
    Mem_AbsR r env
      -> copyBytes (Memory.plusPtr addr1 off1) sz
                   (Memory.plusPtr addr2 off2) env = env'
      -> forall r', memcpy r addr1 off1 addr2 off2 sz ↝ r' /\ Mem_AbsR r' env';

  memset_correct : forall r env env' addr off w sz,
    Mem_AbsR r env
      -> fillBytes (Memory.plusPtr addr off) w sz env = env'
      -> forall r', memset r addr off sz w ↝ r' /\ Mem_AbsR r' env';

  read_correct : forall r env env' addr off sz xs,
    Mem_AbsR r env
      -> peekArray (Memory.plusPtr addr off) sz env = (xs, env')
      -> forall r', read r addr off sz ↝ (r', xs) /\ Mem_AbsR r' env';

  read_bytes : forall r env addr off sz,
    Mem_AbsR r env
      -> fst (peekArray (Memory.plusPtr addr off) sz env) =
         N.peano_rect
           (fun _ : N => list Word) []
           (fun (i : N) (xs : list Word) =>
              match M.find (Memory.plusPtr (A:=Word) addr
                                           (off + i)) (bytes r) with
              | Some w => w
              | None => Zero
              end :: xs) sz;

  write_correct : forall r env env' addr off xs,
    Mem_AbsR r env
      -> pokeArray (Memory.plusPtr addr off) xs env = env'
      -> forall r', write r addr off xs ↝ r' /\ Mem_AbsR r' env'
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

  eapply transitivityT.
  eapply annotate_ADT with
  (methDefs' := icons {|methBody :=  _|} (* emptyS *)
               (icons {|methBody :=  _|} (* allocS *)
               (icons {|methBody :=  _|} (* freeS *)
               (icons {|methBody :=  _|} (* reallocS *)
               (icons {|methBody :=  _|} (* peekS *)
               (icons {|methBody :=  _|} (* pokeS *)
               (icons {|methBody :=  _|} (* memcpyS *)
               (icons {|methBody :=  _|} (* memsetS *)
               (icons {|methBody :=  _|} (* readS *)
               (icons {|methBody :=  _|} (* writeS *)
                inil ) ) ) ) ) ) ) ) ) )
               (AbsR := @Mem_AbsR Env).
  simpl.
  repeat apply Build_prim_prod;
  simpl; intros;
  try simplify with monad laws; set_evars;
  try exact tt.

  (* refine method emptyS. *)
  {
    apply refine_pick.
    subst H.
    instantiate (1 := ret mem).
    intros.
    apply empty_correct; assumption.
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
        rewrite Heqrealloc; simpl.
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
    refine pick val (fst (peekPtr ffi (Memory.plusPtr d d0) r_n)).
      simplify with monad laws.
      refine pick val r_n.
        simplify with monad laws; simpl.
        finish honing.
      assumption.

    remember (peekPtr _ _ _) as peek.
    symmetry in Heqpeek.
    destruct peek as [w env'].
    eapply peek_correct with (r':=r_o) in Heqpeek; eauto.
    breakdown; destruct_computations.
    inv H4.
    simpl in *.
    eassumption.
  }

  (* refine method pokeS. *)
  {
    refine pick val (pokePtr ffi (Memory.plusPtr d d0) d1 r_n).
      finish honing.

    eapply poke_correct; eauto.
  }

  (* refine method memcpyS. *)
  {
    refine pick val (copyBytes ffi (Memory.plusPtr d d0)
                               d3 (Memory.plusPtr d1 d2) r_n).
      subst_evars.
      finish honing.

    eapply memcpy_correct; eauto.
  }

  (* refine method memsetS. *)
  {
    refine pick val (fillBytes ffi (Memory.plusPtr d d0) d2 d1 r_n).
      finish honing.

    eapply memset_correct; eauto.
  }

  (* refine method readS. *)
  {
    simpl in *.
    clear H.
    refine pick val (fst (peekArray ffi (Memory.plusPtr d d0) d1 r_n)).
      simplify with monad laws; simpl.
      refine pick val (snd (peekArray ffi (Memory.plusPtr d d0) d1 r_n)).
        simplify with monad laws; simpl.
        finish honing.

      eapply read_correct; eauto.
      instantiate (1:=fst (peekArray ffi (Memory.plusPtr d d0) d1 r_n)).
      rewrite <- surjective_pairing.
      reflexivity.
    apply read_bytes.
    assumption.
  }

  (* refine method writeS. *)
  {
    refine pick val (pokeArray ffi (Memory.plusPtr d d0) d1 r_n).
      finish honing.

    eapply write_correct; eauto.
  }

  finish_SharpeningADT_WithoutDelegation.
Defined.

Definition HeapFFI' {Env : Type} (ffi : HeapIntf Env) (mem : Mem Env) :=
  Eval simpl in projT1 (HeapFFI ffi mem).
(* Print HeapFFI'. *)

End HeapFFI.
