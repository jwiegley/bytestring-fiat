Require Import
  Here.ByteString
  Here.Heap
  Here.HeapADT
  Here.Nomega
  Here.BindDep
  Here.FunRelation
  Here.FunMaps
  Here.FMapExt
  Here.Tactics.

Require Import Coq.Structures.OrderedTypeEx.

Module Import E := FunMaps N_as_OT.

Generalizable All Variables.

Section RefinedHeap.

Variable Word8 : Type.
Variable Zero : Word8.

Definition MemoryBlock := MemoryBlock Word8.
Definition HeapSpec := @HeapSpec Word8.

Record MemoryBlockC := {
  memCSize : N;
  memCData : M.t Word8
}.

Require Import
  Fiat.ADT
  Fiat.ADTNotation
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Definition MemoryBlock_AbsR (o : MemoryBlock) (n : MemoryBlockC) : Prop :=
  memSize o = memCSize n /\
  SetMap_AbsR (memData o) (memCData n) eq.

Lemma Empty_MemoryBlock_AbsR : forall n,
  MemoryBlock_AbsR {| memSize  := n; memData  := Empty N Word8 |}
                   {| memCSize := n; memCData := M.empty Word8 |}.
Proof.
  intros.
  split; trivial; simpl; intros.
  exact (Empty_SetMap_AbsR _).
Qed.

Lemma free_test_proper : forall n,
  Proper (eq ==> eq ==> eq)
    (fun (addr : M.key) (blk : MemoryBlockC) => addr + memCSize blk <=? n).
Proof.
  unfold Proper, respectful; intros.
  subst; reflexivity.
Qed.

Hint Resolve free_test_proper.

Ltac remove_dependency :=
  repeat
    match goal with
      | [ |- refine (_ <- `(_|_) <- ret _;
                          ret _;
                     _) _ ] =>
        rewrite refine_bind_dep_ret
      | [ |- refine (_ <- `(_|_) <- _;
                          ret _;
                     _) _ ] =>
        rewrite refine_bind_dep_bind_ret; simpl
      | [ |- refine (`(_|_) <- _;
                     _) _ ] =>
        rewrite refine_bind_dep_ignore
    end.

Definition Heap_AbsR
           (or : { r : Rep HeapSpec
                 | ADTInduction.fromADT HeapSpec r})
           (nr : N * M.t MemoryBlockC) : Prop :=
  SetMap_AbsR (` or) (snd nr) MemoryBlock_AbsR /\
  P.for_all (fun addr blk => addr + memCSize blk <=? fst nr) (snd nr).

Ltac AbsR_prep :=
  repeat
    match goal with
    | [ H : Heap_AbsR _ _ |- _ ] => unfold Heap_AbsR in H; simpl in H
    | [ |- Heap_AbsR _ _ ] => unfold Heap_AbsR; simpl
    | [ H : _ /\ _ |- _ ] => destruct H; simpl in H
    | [ |- _ /\ _ ] => split
    end; simpl.

Lemma HeapImpl : FullySharpened HeapSpec.
Proof.
  start sharpening ADT.
  eapply SharpenStep; [ apply (projT2 (@HeapSpecADT Word8)) |].

  hone representation using Heap_AbsR.

  refine method emptyS.
  {
    unfold empty.
    remove_dependency.
    simplify with monad laws.

    refine pick val (0%N, @M.empty _).
      finish honing.

    AbsR_prep.
    - exact (Empty_SetMap_AbsR _).
    - eapply E.for_all_empty; auto.
  }

  refine method allocS.
  {
    unfold Heap_AbsR, alloc, find_free_block.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val (fst r_n).
      Focus 2.
      intros.
      admit.

    simplify with monad laws; simpl.
    refine pick val (fst r_n + proj1_sig d,
                     M.add (fst r_n)
                           {| memCSize := proj1_sig d
                            ; memCData := M.empty _ |} (snd r_n)).
      simplify with monad laws.
      finish honing.

    AbsR_prep.
    - apply Update_SetMap_AbsR; auto.
      exact (Empty_MemoryBlock_AbsR _).
    - apply E.for_all_add; simpl; auto.
        eapply for_all_impl; eauto; simpl; intros.
        destruct d; simpl.
        clear -l H2.
        undecide.
        apply Nle_add_plus; trivial.
      apply N.leb_refl.
  }

  refine method freeS.
  {
    unfold free, free_block.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val (fst r_n, M.remove d (snd r_n)).
      simplify with monad laws.
      finish honing.

    AbsR_prep.
    - admit.
    - apply for_all_remove; auto.
  }

  refine method reallocS.
  {
    admit.
  }

  refine method peekS.
  {
    unfold Heap_AbsR, peek, found_block.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val
      (Ifopt List.find (fun p =>
                          let blk := snd p in
                          Decidable.Decidable_witness
                            (P:=within (fst p) (memCSize blk) d))
                       (M.elements (snd r_n)) as p
       Then let blk := snd p in
            Ifopt M.find (d - fst p) (memCData blk) as v
            Then v
            Else Zero
       Else Zero).
      Focus 2.
      admit.

    simplify with monad laws; simpl.
    refine pick val r_n.
      simplify with monad laws.
      finish honing.

    AbsR_prep; assumption.
  }

  refine method pokeS.
  {
    unfold poke, set_address.
    remove_dependency.
    simplify with monad laws; simpl.
    refine pick val
      (fst r_n,
       M.mapi (fun addr blk =>
                 IfDec within addr (memCSize blk) d
                 Then {| memCSize := memCSize blk
                       ; memCData := M.add (d - addr) d0
                                           (memCData blk) |}
                 Else blk) (snd r_n)).
      simplify with monad laws.
      finish honing.

    AbsR_prep.
    - apply Map_SetMap_AbsR; auto.
      intros.
      admit.
    - admit.
  }

  refine method memcpyS.
  {
    admit.
  }

  refine method memsetS.
  {
    admit.
  }

  finish_SharpeningADT_WithoutDelegation.
Abort.

End RefinedHeap.
