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

Section MemoryBlock.

Record MemoryBlockC := {
  memCSize : N;
  memCData : M.t Word8
}.

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
                 | ADTInduction.fromADT HeapSpec r})
           (nr : N * M.t MemoryBlockC) : Prop :=
  SetMap_AbsR (` or) (snd nr) MemoryBlock_AbsR /\
  P.for_all (within_allocated_mem (fst nr)) (snd nr).

Lemma Lookup_find_block {r_o r_n} (AbsR : Heap_AbsR r_o r_n) addr' blk' :
  Lookup addr' blk' (` r_o)
    -> exists cblk',
        MemoryBlock_AbsR blk' cblk' /\
        M.find addr' (snd r_n) = Some cblk'.
Proof.
  intros.
  destruct AbsR.
  destruct (H0 addr'); clear H0.
  destruct (H2 _ H) as [blk [? ?]]; clear H H2 H3.
  exists blk.
  tauto.
Qed.

Lemma Heap_AbsR_outside_mem
      {r_o r_n} (AbsR : Heap_AbsR r_o r_n)
      (d : {len : N | 0 < len}) :
  forall addr' blk',
    ~ Find (fun a b => overlaps a (memSize b) (fst r_n) (` d))
           addr' blk' (` r_o).
Proof.
  destruct AbsR; intros.
  apply LogicFacts.not_and_implication; intros.
  eapply Lookup_find_block in H1; eauto;
  [| split; [exact H|assumption] ].
  destruct H1 as [cblk' [[? ?] ?]].
  eapply P.for_all_iff with (k:=addr') (e:=cblk') in H0; eauto.
    unfold within_allocated_mem in H0; simpl in H0.
    unfold overlaps.
    destruct d; simpl in *.
    rewrite H1.
    clear -H0 l.
    undecide.
    nomega.
  apply F.find_mapsto_iff.
  assumption.
Qed.

Lemma Heap_Find {r_o r_n} {AbsR : Heap_AbsR r_o r_n} :
  forall d base blk',
    Find (fun (a : N) (b : Heap.MemoryBlock Word8) =>
            within a (memSize b) d) base blk' (` r_o)
      -> exists cblk',
           MemoryBlock_AbsR blk' cblk' /\
           find_if (fun (addr : M.key) (blk : MemoryBlockC) =>
                      Decidable.Decidable_witness
                        (P:=within addr (memCSize blk) d)) (snd r_n)
             = Some (base, cblk').
Proof.
  intros; subst.
  pose proof H as HAA.
  destruct HAA as [HAA HAB].
  pose proof (allocations_only_one_within (proj2_sig r_o) H) as HAC.
  destruct AbsR as [HC _].
  pose proof HC as HD.
  destruct (HD base) as [HE _]; clear HD.
  destruct (HE _ HAA) as [cblk' [HF HG]]; clear HE HAA.
  remember (fun (_ : M.key) _ => _) as P'.
  exists cblk'.
  split; trivial.
  assert (forall a b : N, a = b <-> a = b) as HL by tauto.
  assert (unique_predicate P' (snd r_n)) as HM.
    admit.
  pose proof (find_if_unique HL P' (snd r_n) HM base cblk' HF).
  unfold find_if.
  unfold SetMap_AbsR in HC.
  rewrite F.elements_o in HF.
  setoid_rewrite F.elements_o in HC.
  rewrite M.fold_1.
  induction (M.elements (elt:=MemoryBlockC) (snd r_n)).
    discriminate.
  rewrite fold_Some_cons; auto.
  destruct a; simpl in *; subst.
  unfold F.eqb, F.eq_dec in *.
  destruct (HC k) as [_ HD].
  destruct (N.eq_dec k k); try tauto; clear e.
  destruct (HD m eq_refl) as [blk'' [HI HJ]]; clear HD.
  pose proof (HAC _ _ HI) as HAD.
  destruct (N.eq_dec base k).
    inversion HF; subst; clear HF.
    decisions.
      reflexivity.
    apply within_reflect in HAB.
    destruct HG as [HH ?].
    rewrite HH in HAB.
    rewrite HAB in Heqe.
    discriminate.
  decisions.
    apply within_reflect in Heqe.
    destruct HJ as [HK _]; rewrite <- HK in Heqe.
    specialize (HAD Heqe).
    tauto.
  apply IHl; eauto; clear IHl.
  split; intros;
  destruct (HC addr) as [HD HE]; clear HC.
    clear HE.
    destruct (HD _ H1) as [cblk [HBF HBG]].
    exists cblk.
    admit.
  admit.
Admitted.

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
    - apply Empty_SetMap_AbsR; trivial.
    - apply E.for_all_empty; trivial.
  }

  refine method allocS.
  {
    unfold Heap_AbsR, alloc, find_free_block.
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
    - apply Update_SetMap_AbsR; trivial.
      apply Empty_MemoryBlock_AbsR; trivial.
    - apply E.for_all_add; trivial.
        eapply E.for_all_impl; eauto; intros.
        destruct d; simpl.
        apply within_allocated_mem_add; trivial.
      apply within_allocated_mem_at_end.
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
    - apply Remove_SetMap_AbsR; trivial.
    - apply E.for_all_remove; trivial.
  }

  refine method reallocS.
  {
    unfold Heap_AbsR, realloc, find_free_block.
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
      (Ifopt find_if (fun addr blk =>
                        Decidable.Decidable_witness
                          (P:=within addr (memCSize blk) d)) (snd r_n) as p
       Then let addr := fst p in
            let blk := snd p in
            Ifopt M.find (d - addr) (memCData blk) as v
            Then v
            Else Zero
       Else Zero).

    simplify with monad laws; simpl.
    refine pick val r_n.
      simplify with monad laws.
      finish honing.

    AbsR_prep; assumption.

    intros; subst; clear H.
    destruct (@Heap_Find _ _ H0 _ _ _ H1) as [cblk' [HA HB]].
    rewrite HB; simpl; clear HB.
    destruct HA as [_ HI].
    destruct (HI (d - base)) as [HJ _]; clear HI.
    destruct (HJ _ H2) as [cdata [HK HL]]; clear HJ H2; subst.
    rewrite HK; reflexivity.
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
    - apply Map_SetMap_AbsR; auto; intros.
      admit.
    - admit.
  }

  refine method memcpyS.
  {
    unfold memcpy.
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
