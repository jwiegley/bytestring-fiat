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
  Here.TupleEnsembles
  Here.TupleEnsemblesFinite
  CoqRel.LogicalRelations.

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

Definition MemoryBlock_Same (x y : MemoryBlock) : Prop :=
  memSize x = memSize y /\ Same (memData x) (memData y).

Definition MemoryBlockC_Equal (x y : MemoryBlockC) : Prop :=
  memCSize x = memCSize y /\ M.Equal (memCData x) (memCData y).

Global Program Instance Finite_Proper {A B} :
  Morphisms.Proper (Same (B:=B) ==> impl) (Finite (A * B)).
Obligation 1.
  relational.
  apply Same_Same_set in H.
  rewrite H.
  reflexivity.
Qed.

Global Program Instance Finite_Proper_flip_1 {A B} :
  Morphisms.Proper (Same (B:=B) ==> flip impl) (Finite (A * B)).
Obligation 1.
  relational.
  apply Same_Same_set in H.
  unfold flip.
  rewrite <- H.
  reflexivity.
Qed.

Global Program Instance Finite_Proper_flip_2 {A B} :
  Morphisms.Proper (Same (B:=B) --> flip impl) (Finite (A * B)).
Obligation 1.
  relational.
  apply Same_Same_set in H.
  unfold flip.
  rewrite H.
  reflexivity.
Qed.

Global Program Instance MemoryBlock_AbsR_Proper :
  Proper (MemoryBlock_Same ==> MemoryBlockC_Equal ==> iff) MemoryBlock_AbsR.
Obligation 1.
  relational; destruct H, H0, H1.
  - split; intros.
      congruence.
    split; intros; subst;
    split; intros.
    + rewrite <- H2 in H5.
      apply H4 in H5; trivial.
      setoid_rewrite H3 in H5.
      trivial.
    + rewrite <- H2.
      apply H4; trivial.
      setoid_rewrite H3.
      trivial.
    + rewrite <- H3 in H5.
      apply H4 in H5; trivial.
      setoid_rewrite H2 in H5.
      trivial.
    + rewrite <- H3.
      apply H4; trivial.
      setoid_rewrite <- H2 in H5.
      trivial.
  - split; intros.
      congruence.
    split; intros; subst;
    split; intros.
    + rewrite H2 in H5.
      apply H4 in H5; trivial.
      setoid_rewrite <- H3 in H5.
      trivial.
    + rewrite H2.
      apply H4; trivial.
      setoid_rewrite <- H3.
      trivial.
    + rewrite H3 in H5.
      apply H4 in H5; trivial.
      setoid_rewrite <- H2 in H5.
      trivial.
    + rewrite H3.
      apply H4; trivial.
      setoid_rewrite H2 in H5.
      trivial.
Qed.

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

Program Instance within_allocated_mem_Proper :
  Proper (eq ==> eq ==> eq ==> eq) within_allocated_mem.
Obligation 1. relational; subst; reflexivity. Qed.

Hint Resolve within_allocated_mem_Proper.

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

Definition Heap_AbsR
           (or : { r : Rep HeapSpec | fromADT HeapSpec r})
           (nr : N * M.t MemoryBlockC) : Prop :=
  Map_AbsR MemoryBlock_AbsR (` or) (snd nr) /\
  P.for_all (within_allocated_mem (fst nr)) (snd nr).

Program Definition Empty_Heap : { r : Rep HeapSpec | fromADT HeapSpec r} :=
  exist _ Empty (empty_fromADT _).
Obligation 1. reflexivity. Qed.

Lemma Empty_Heap_AbsR : Heap_AbsR Empty_Heap (0, M.empty MemoryBlockC).
Proof.
  split.
    apply Empty_Map_AbsR.
  simpl.
  apply for_all_empty.
  apply within_allocated_mem_Proper.
  reflexivity.
Qed.

Require Import FunctionalExtensionality.

Corollary Proper_within : forall pos,
   Proper (eq ==> eq ==> eq)
          (fun b e => Decidable_witness (P:=within b (memCSize e) pos)).
Proof. intros; relational; subst; reflexivity. Qed.

Definition withinMemBlock (pos : N) (b : N) (e : MemoryBlock) : Prop :=
  within b (memSize e) pos.

Definition withinMemBlockC (pos : N) (b : N) (e : MemoryBlockC) : bool :=
  Decidable_witness (P:=within b (memCSize e) pos).

Global Program Instance withinMemBlock_Proper :
  Morphisms.Proper (N.eq ==> eq ==> eq ==> eq) withinMemBlock.
Obligation 1.
  relational.
  subst.
  rewrite H.
  reflexivity.
Qed.

Hint Resolve withinMemBlock_Proper.

Global Program Instance withinMemBlockC_Proper :
  Morphisms.Proper (N.eq ==> eq ==> eq ==> eq) withinMemBlockC.
Obligation 1.
  relational.
  subst.
  rewrite H.
  reflexivity.
Qed.

Hint Resolve withinMemBlockC_Proper.

Global Program Instance withinMemBlock_AbsR :
  withinMemBlock [R eq ==> eq ==> MemoryBlock_AbsR ==> boolR]
  withinMemBlockC.
Obligation 1.
  relational; subst;
  unfold withinMemBlock, withinMemBlockC;
  split; intros.
    apply within_reflect in H.
    rewrite <- (proj1 H1).
    assumption.
  simpl in H.
  apply within_reflect.
  rewrite (proj1 H1).
  assumption.
Qed.

Global Program Instance withinMemBlock_AbsR_applied (pos : N) :
  withinMemBlock pos [R eq ==> MemoryBlock_AbsR ==> boolR]
  withinMemBlockC pos.
Obligation 1. apply withinMemBlock_AbsR; reflexivity. Qed.

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
  forall base blk' cblk',
    MemoryBlock_AbsR blk' cblk'
      -> Lookup base blk' (` r_o)
      -> withinMemBlock pos base blk'
      -> find_if (withinMemBlockC pos) (snd r_n) = Some (base, cblk').
Proof.
  intros.
  pose proof (find_partitions_a_singleton (proj2_sig r_o) _ H0 H1).
  eapply Same_Map_AbsR with (R:=MemoryBlock_AbsR) in H2.
    Focus 2.
    apply Filter_Map_AbsR; eauto.
      apply withinMemBlock_Proper; reflexivity.
      apply withinMemBlockC_Proper; reflexivity.
      apply withinMemBlock_AbsR; eauto.
      apply (proj1 AbsR).
    Focus 2.
    apply Single_Map_AbsR; eauto.
  apply find_if_filter_is_singleton in H2.
    unfold optionP, pairP in H2.
    destruct (find_if (withinMemBlockC pos) (snd r_n)).
      destruct p, H2; subst.
      reflexivity.
    contradiction.
  apply withinMemBlockC_Proper.
  reflexivity.
Qed.

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
  apply within_allocated_mem_Proper; reflexivity.
Qed.

Lemma Heap_AbsR_outside_mem
      {r_o r_n} (AbsR : Heap_AbsR r_o r_n)
      (d : {len : N | 0 < len}) :
  All (fun addr' blk' =>
         ~ overlaps addr' (memSize blk') (fst r_n) (` d)) (` r_o).
Proof.
  intros addr blk H.
  apply AbsR in H; destruct H as [cblk [? ?]].
  rewrite (proj1 H0).
  destruct AbsR as [_ ?].
  eapply P.for_all_iff with (k:=addr) (e:=cblk) in H1; eauto.
    unfold within_allocated_mem in H1; simpl in H1.
    unfold not; intros.
    clear -H1 H2.
    unfold overlaps, within in *.
    undecide.
    nomega.
  apply within_allocated_mem_Proper.
  reflexivity.
Qed.

Ltac AbsR_prep :=
  repeat
    match goal with
    | [ H : Heap_AbsR _ _ |- _ ] => unfold Heap_AbsR in H; simpl in H
    | [ |- Heap_AbsR _ _ ] => unfold Heap_AbsR; simpl
    | [ H : _ /\ _ |- _ ] => destruct H; simpl in H
    | [ |- _ /\ _ ] => split
    end; try monotonicity; simpl; eauto.

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
    refine pick val ((fst r_n + proj1_sig d)%N,
                     M.add (fst r_n)
                           {| memCSize := proj1_sig d
                            ; memCData := M.empty _ |} (snd r_n)).
      simplify with monad laws.
      finish honing.

    AbsR_prep.
    - apply Update_Map_AbsR; auto.
      apply MemoryBlock_AbsR_impl; auto.
      apply Empty_Map_AbsR.
    - apply for_all_add; auto.
      + apply within_allocated_mem_Proper; auto.
      + apply for_all_impl
         with (P':=within_allocated_mem (fst r_n + ` d)) in H1; auto.
        * apply within_allocated_mem_Proper; auto.
        * apply within_allocated_mem_Proper; auto.
        * intros.
          clear -H2.
          unfold within_allocated_mem in *.
          undecide.
          destruct d; simpl.
          apply Nle_add_plus; eauto.
      + destruct d; simpl.
        unfold within_allocated_mem; simpl.
        nomega.
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
    - apply Remove_Map_AbsR; auto.
    - apply for_all_remove; auto.
      apply within_allocated_mem_Proper; auto.
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

    AbsR_prep.
    intros; subst; clear H.
    pose proof H1 as H4.
    apply H0 in H1.
    destruct H1 as [cblk [? ?]].
    erewrite Peek_in_heap; eauto; simpl.
    apply H1 in H3.
    destruct H3 as [mem [? ?]]; subst.
    apply F.find_mapsto_iff in H3.
    rewrite H3; reflexivity.
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

    pose proof (Poke_in_heap H0).
    AbsR_prep.

    apply Map_Map_AbsR; auto.
    - admit.
    - admit.
    - relational; subst.
      rewrite (proj1 H4).
      decisions; auto.
      apply MemoryBlock_AbsR_impl; auto.
      apply Update_Map_AbsR; auto.
      exact (proj2 H4).
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
Admitted.

End RefinedHeap.
