Require Import
  Here.ByteString
  Here.Heap
  Here.HeapADT
  Here.Nomega
  Here.BindDep
  Here.FunMaps
  Here.FMapExt
  Here.Same_set
  Here.Tactics
  Here.ADTInduction
  Here.TupleEnsembles.

Require Import Coq.Structures.OrderedTypeEx.

Module Import E := FunMaps N_as_OT.

Generalizable All Variables.

Section RefinedHeap.

Variable Word8 : Type.
Variable Zero : Word8.

Definition MemoryBlock := MemoryBlock Word8.
Definition HeapSpec := @HeapSpec Word8.

Section MemoryBlock.

Record MemoryBlockC := {
  memCSize : N;
  memCData : M.t Word8
}.

Definition MemoryBlock_AbsR (o : MemoryBlock) (n : MemoryBlockC) : Prop :=
  memSize o = memCSize n /\ Map_AbsR eq (memData o) (memCData n).

Corollary Empty_MemoryBlock_AbsR : forall n,
  MemoryBlock_AbsR {| memSize  := n; memData  := Empty |}
                   {| memCSize := n; memCData := M.empty Word8 |}.
Proof. split; trivial; simpl; intros; apply Empty_Map_AbsR. Qed.

Corollary MemoryBlock_AbsR_impl : forall s s' d d',
    s = s' -> Map_AbsR eq d d' ->
    MemoryBlock_AbsR {| memSize  := s;  memData  := d |}
                     {| memCSize := s'; memCData := d' |}.
Proof. intros; subst; split; intros; trivial. Qed.

Hint Extern 1 => apply MemoryBlock_AbsR_impl.

End MemoryBlock.

Require Import
  Fiat.ADT
  Fiat.ADTNotation
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Definition within_allocated_mem (n : N) :=
  fun (addr : M.key) (blk : MemoryBlockC) => addr + memCSize blk <=? n.

Lemma within_allocated_mem_Proper : forall n,
  Proper (eq ==> eq ==> eq) (within_allocated_mem n).
Proof.
  unfold Proper, respectful; intros.
  subst; reflexivity.
Qed.

Lemma within_allocated_mem_add : forall n x k e,
  within_allocated_mem n k e
    -> 0 < x
    -> within_allocated_mem (n + x) k e.
Proof.
  unfold within_allocated_mem; intros.
  undecide.
  apply Nle_add_plus; trivial.
Qed.

Lemma within_allocated_mem_at_end : forall n x d,
   within_allocated_mem (n + x) n {| memCSize := x; memCData := d |}.
Proof.
  unfold within_allocated_mem; simpl; intros.
  apply N.leb_refl.
Qed.

Hint Resolve within_allocated_mem_Proper.

Definition Heap_AbsR
           (or : { r : Rep HeapSpec
                 | fromADT HeapSpec r})
           (nr : N * M.t MemoryBlockC) : Prop :=
  Map_AbsR MemoryBlock_AbsR (` or) (snd nr) /\
  P.for_all (within_allocated_mem (fst nr)) (snd nr).

Program Definition Empty_Heap : { r : Rep HeapSpec | fromADT HeapSpec r} :=
  exist _ Empty (empty_fromADT _).
Obligation 1. reflexivity. Qed.

Lemma Empty_Heap_AbsR : Heap_AbsR Empty_Heap (0, M.empty MemoryBlockC).
Proof.
  split; simpl; intros.
    intro addr; split; intros; inv H.
  apply for_all_empty.
  intros ??????; subst; reflexivity.
Qed.

Corollary Lookup_find_block {r_o r_n} (AbsR : Heap_AbsR r_o r_n) addr' blk' :
  Lookup addr' blk' (` r_o)
    -> exists cblk',
         MemoryBlock_AbsR blk' cblk' /\ M.find addr' (snd r_n) = Some cblk'.
Proof.
  intros; destruct AbsR.
  reduction; exists cblk; tauto.
Qed.

Require Import FunctionalExtensionality.

Corollary Proper_within : forall pos,
   Proper (eq ==> eq ==> eq)
          (fun b e => Decidable_witness (P:=within b (memCSize e) pos)).
Proof. intros ???????; subst; reflexivity. Qed.

Definition withinMemBlock (pos : N) (b : N) (e : MemoryBlock) : Prop :=
  within b (memSize e) pos.

Definition withinMemBlockC (pos : N) (b : N) (e : MemoryBlockC) : bool :=
  Decidable_witness (P:=within b (memCSize e) pos).

Notation "f \oo g" := (fun x y => f (g x y)) (at level 90).

Lemma withinMemAbsR : forall base blk cblk pos,
  withinMemBlock pos base blk
    -> MemoryBlock_AbsR blk cblk
    -> withinMemBlockC pos base cblk = true.
Proof.
  intros.
  unfold withinMemBlock, withinMemBlockC in *; simpl in *.
  apply within_reflect in H.
  destruct H0 as [H0 _]; rewrite <- H0.
  assumption.
Qed.

Theorem Peek_in_heap {r_o r_n} (AbsR : Heap_AbsR r_o r_n) pos :
  forall base blk',
    Lookup base blk' (` r_o)
      -> withinMemBlock pos base blk'
      -> exists cblk',
           find_if (withinMemBlockC pos) (snd r_n) = Some (base, cblk') /\
           MemoryBlock_AbsR blk' cblk'.
Proof.
  intros.
  pose proof (find_partitions_a_singleton (proj2_sig r_o) _ H H0).
  destruct AbsR; reduction.
  exists cblk; split; trivial.
  Fail apply find_if_filter.
    Fail apply Proper_within.
Abort.

Theorem Poke_in_heap {r_o r_n} (AbsR : Heap_AbsR r_o r_n) pos val :
  P.for_all (within_allocated_mem (fst r_n))
    (M.mapi
       (fun (addr : M.key) (cblk : MemoryBlockC) =>
        IfDec within addr (memCSize cblk) pos
        Then {| memCSize := memCSize cblk
              ; memCData := M.add (pos - addr) val (memCData cblk) |}
        Else cblk) (snd r_n)).
Proof.
  destruct AbsR as [_ H].
  unfold P.for_all.
  apply P.fold_rec_bis; eauto.
  intros.
  apply F.mapi_mapsto_iff in H0; do 2 destruct H0;
  simpl; intros; subst; auto.
  unfold within_allocated_mem, IfDec_Then_Else; simpl.
  eapply P.for_all_iff in H; eauto.
  unfold within_allocated_mem in H.
  destruct ((k <=? pos) && (pos <? k + memCSize x))%bool; simpl;
  rewrite H; assumption.
Qed.

Lemma Heap_AbsR_outside_mem
      {r_o r_n} (AbsR : Heap_AbsR r_o r_n)
      (d : {len : N | 0 < len}) :
  All (fun addr' blk' =>
         ~ overlaps addr' (memSize blk') (fst r_n) (` d)) (` r_o).
Proof.
  destruct AbsR; intros ???.
  apply LogicFacts.not_and_implication; intros.
  reduction.
  eapply P.for_all_iff with (k:=a) (e:=cblk) in H0; eauto.
    unfold within_allocated_mem in H0; simpl in H0.
    rewrite (proj1 HD).
    unfold not; intros.
    clear -H0 H1.
    undecide; nomega.
  apply F.find_mapsto_iff.
  assumption.
Qed.

Ltac AbsR_prep :=
  repeat
    match goal with
    | [ H : Heap_AbsR _ _ |- _ ] => unfold Heap_AbsR in H; simpl in H
    | [ |- Heap_AbsR _ _ ] => unfold Heap_AbsR; simpl
    | [ H : _ /\ _ |- _ ] => destruct H; simpl in H
    | [ |- _ /\ _ ] => split
    end; simpl.

Corollary eq_impl_eq : forall a b : N, a = b <-> a = b.
Proof. split; intros; assumption. Qed.
Hint Resolve eq_impl_eq.

Corollary neq_impl_neq : forall a b : N, a <> b <-> a <> b.
Proof. split; intros; assumption. Qed.
Hint Resolve neq_impl_neq.

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
    - apply Empty_Map_AbsR; trivial.
    - apply E.for_all_empty; trivial.
  }

  refine method allocS.
  {
    unfold Heap_AbsR, alloc.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val (fst r_n).
      Focus 2.
      apply Heap_AbsR_outside_mem; trivial.

    simplify with monad laws; simpl.
    refine pick val (fst r_n + proj1_sig d,
                     M.add (fst r_n)
                           {| memCSize := proj1_sig d
                            ; memCData := M.empty _ |} (snd r_n)).
      simplify with monad laws.
      finish honing.

    AbsR_prep.
    - apply Update_Map_AbsR; auto.
      apply MemoryBlock_AbsR_impl; auto.
      apply Empty_Map_AbsR; auto.
    - apply E.for_all_add; trivial.
        eapply E.for_all_impl; eauto; intros.
        destruct d; simpl.
        apply within_allocated_mem_add; trivial.
      apply within_allocated_mem_at_end.
  }

  refine method freeS.
  {
    unfold free.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val (fst r_n, M.remove d (snd r_n)).
      simplify with monad laws.
      finish honing.

    AbsR_prep.
    - apply Remove_Map_AbsR; trivial.
    - apply E.for_all_remove; trivial.
  }

  refine method reallocS.
  {
    unfold Heap_AbsR, realloc.
    remove_dependency.
    simplify with monad laws; simpl.

    admit.
  }

  refine method peekS.
  {
    unfold Heap_AbsR, peek.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val
      (Ifopt find_if (withinMemBlockC d) (snd r_n) as p
       Then Ifopt M.find (d - fst p) (memCData (snd p)) as v
            Then v Else Zero
       Else Zero).

    simplify with monad laws; simpl.
    refine pick val r_n.
      simplify with monad laws.
      finish honing.

    AbsR_prep; assumption.
    - intros; subst; clear H.
      Fail destruct (Peek_in_heap H0 H1) as [? [H3 H4]].
      Fail rewrite H3; simpl.
      Fail destruct H4; reduction; subst.
      Fail rewrite HC; reflexivity.
      admit.
  }

  refine method pokeS.
  {
    unfold poke.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val
      (fst r_n,
       M.mapi (fun addr cblk =>
                 IfDec within addr (memCSize cblk) d
                 Then {| memCSize := memCSize cblk
                       ; memCData := M.add (d - addr) d0 (memCData cblk) |}
                 Else cblk) (snd r_n)).
      simplify with monad laws.
      finish honing.

    AbsR_prep.
    - eapply Map_Map_AbsR; auto.
      split; subst; destruct H3.
        decisions; simpl; auto;
        rewrite H3; reflexivity.
      decisions; simpl; auto.
      + apply Update_Map_AbsR; auto.
      + rewrite H2 in Heqe; intuition.
        rewrite Heqe in Heqe0; discriminate.
      + rewrite H2 in Heqe; intuition.
        rewrite Heqe in Heqe0; discriminate.
    - decisions.
      admit.
  }

  refine method memcpyS.
  {
    unfold Heap_AbsR, memcpy.
    remove_dependency.
    simplify with monad laws; simpl.

    admit.
  }

  refine method memsetS.
  {
    unfold memset.
    remove_dependency.
    simplify with monad laws; simpl.

    admit.
  }

  finish_SharpeningADT_WithoutDelegation.
Abort.

End RefinedHeap.
