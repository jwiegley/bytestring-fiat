Require Import
  Here.ByteString
  Here.Heap
  Here.HeapADT
  Here.Nomega
  Here.BindDep
  Here.FunRelation
  Here.FunMaps
  Here.FMapExt
  Here.Same_set
  Here.Tactics
  Here.ADTInduction.

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
                 | fromADT HeapSpec r})
           (nr : N * M.t MemoryBlockC) : Prop :=
  SetMap_AbsR (` or) (snd nr) MemoryBlock_AbsR /\
  P.for_all (within_allocated_mem (fst nr)) (snd nr).

Program Definition Empty_Heap : { r : Rep HeapSpec | fromADT HeapSpec r} :=
  exist _ (Empty N MemoryBlock) (empty_fromADT _).
Obligation 1. reflexivity. Qed.

Lemma Empty_Heap_AbsR : Heap_AbsR Empty_Heap (0, M.empty MemoryBlockC).
Proof.
  split; simpl; intros.
    intro addr; split; intros; inv H.
  apply for_all_empty.
  intros ??????; subst; reflexivity.
Qed.

Definition Extend (k : N) (v : MemoryBlock)
           (or : { r : Rep HeapSpec | fromADT HeapSpec r}) :
  ~ Member k (` or)
    -> 0 < memSize v
    -> All (fun p => fst p < memSize v) (memData v)
    -> memData v = Empty N Word8
    -> (forall addr' blk',
          ~ Find (fun addr' blk' =>
                    overlaps addr' (memSize blk') k (memSize v))
                 addr' blk' (` or))
    -> { r : Rep HeapSpec | fromADT HeapSpec r}.
Proof.
  intros.
  exists (Update k v (` or)).
  apply fromADTMethod with (midx:=Fin.FS (Fin.FS Fin.F1)) (r:=` or).
    exact (proj2_sig or).
  unfold fromMethod, fromMethod'; simpl.
  exists k; exists (exist _ (memSize v) H0); exists k; simpl.
  unfold find_free_block, free_block; simpl.
  apply BindComputes with (a:=false).
    apply PickComputes; intros.
    apply LogicFacts.not_exists_forall with (a:=blk) in H.
    simpl; unfold not, Lookup; intros.
    contradiction.
  apply BindComputes with (a:=k).
    apply PickComputes; intros.
    unfold not; intros.
    specialize (H3 addr' blk').
    destruct H4.
    apply Lookup_Remove_inv in H4; destruct H4.
    unfold Find in H3.
    apply (LogicFacts.not_and_implication
             (Lookup _ _ _) (overlaps _ _ _ _)) in H3; eauto.
  unfold fit_to_length, shift_address; simpl.
  destruct v; simpl in *; subst.
  apply ReturnComputes.
Defined.

Definition ExtendC (k : N) (v : MemoryBlockC) (nr : N * M.t MemoryBlockC) :
  fst nr <= k -> ~ M.In k (snd nr) -> N * M.t MemoryBlockC.
Proof.
  intros.
  exact (k + memCSize v, M.add k v (snd nr)).
Defined.

Lemma Extend_Heap_AbsR :
  forall k v v', MemoryBlock_AbsR v v' ->
  forall or nr
    (H1 : ~ Member k (` or))
    (H2 : 0 < memSize v)
    (H3 : All (fun p => fst p < memSize v) (memData v))
    (H4 : memData v = Empty N Word8)
    (H5 : (forall addr' blk',
             ~ Find (fun addr' blk' =>
                       overlaps addr' (memSize blk') k (memSize v))
                    addr' blk' (` or)))
    (H6 : fst nr <= k)
    (H7 : ~ M.In k (snd nr)),
    Heap_AbsR or nr
      -> Heap_AbsR (@Extend k v or H1 H2 H3 H4 H5) (@ExtendC k v' nr H6 H7).
Proof.
  unfold Extend, ExtendC; intros.
  destruct H0.
  split; intros.
    intro addr;
    split; simpl in *; intros.
      inv H9; simplify_ensembles; simpl in *.
        destruct (H0 addr).
        destruct (H10 _ H9) as [cblk [? ?]].
        exists cblk; intuition.
        unfold Ensembles.In in H11; simpl in H11.
        apply F.find_mapsto_iff.
        apply F.add_mapsto_iff.
        right; split.
          intuition.
        apply F.find_mapsto_iff.
        assumption.
      specialize (H5 addr blk).
      unfold Find in H5.
      apply (LogicFacts.not_and_implication
               (Lookup _ _ _) (overlaps _ _ _ _)) in H5; eauto.
        admit.
      admit.
    admit.
  admit.
Admitted.

(*
Theorem Heap_ind
        (P : forall (or : { r : Rep HeapSpec | fromADT HeapSpec r})
                    (nr : N * M.t MemoryBlockC)
                    (AbsR : Heap_AbsR or nr), Prop)
        (P0 : P Empty_Heap (0, M.empty MemoryBlockC) Empty_Heap_AbsR)
        (PE : forall or nr AbsR, P or nr AbsR
                -> forall v v' (H : MemoryBlock_AbsR v v'),
                   forall k, P (Extend k v or) (ExtendC k v' nr)
                               (Extend_Heap_AbsR k H AbsR)) :
  forall (or : { r : Rep HeapSpec | fromADT HeapSpec r})
         (nr : N * M.t MemoryBlockC)
         (AbsR : Heap_AbsR or nr), P or nr AbsR.
Proof.
Admitted.
*)

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

Theorem Partition_partition {r_o r_n} (AbsR : Heap_AbsR r_o r_n) base blk pos :
  Find (withinMemBlock pos) base blk (` r_o)
    -> forall a a',
         Partition (withinMemBlock pos) (` r_o) = (a, a')
           -> Lookup base blk a
    -> exists cblk b b',
         P.partition (withinMemBlockC pos) (snd r_n) = (b, b')
           /\ SetMap_AbsR a b MemoryBlock_AbsR
           /\ SetMap_AbsR a' b' MemoryBlock_AbsR
           /\ M.find base b = Some cblk.
Proof.
  intros.
  destruct H.
  destruct AbsR.
  pose proof H3.
  reduction.
  intros.
  exists cblk.
  exists (P.filter (withinMemBlockC pos) (snd r_n)).
  exists (P.filter (negb \oo withinMemBlockC pos) (snd r_n)).
  split.
    unfold P.partition; f_equal.
  split.
    unfold Partition in H0; inv H0.
    intro addr.
    split; intros.
      simpl in H; destruct H.
      destruct (H3 addr); clear H3 H6.
      destruct (H5 _ H0) as [cblk' [? ?]]; clear H0 H5.
      exists cblk'.
      split; trivial.
      admit.
    destruct (H3 addr); clear H3.
    admit.
  split.
    unfold Partition in H0; inv H0.
    intro addr.
    split; intros.
      simpl in H; destruct H.
      destruct (H3 addr); clear H3 H6.
      destruct (H5 _ H0) as [cblk' [? ?]]; clear H0 H5.
      exists cblk'.
      split; trivial.
      admit.
    destruct (H3 addr); clear H3.
    admit.
  apply F.find_mapsto_iff.
  apply P.filter_iff.
    exact (Proper_within _).
  split.
    apply F.find_mapsto_iff; assumption.
  apply within_reflect.
  destruct HD as [HD _]; rewrite <- HD.
  assumption.
Admitted.

Theorem Peek_not_in_heap {r_o r_n} (AbsR : Heap_AbsR r_o r_n) pos :
  forall base blk',
    ~ Find (withinMemBlock pos) base blk' (` r_o)
      -> find_if (withinMemBlockC pos) (snd r_n) = None.
Proof.
  intros.
Admitted.

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

Lemma Sorted_cons_skip : forall A P (x : A) y l,
  Sorted.Sorted P (x :: y :: l)%list -> Sorted.Sorted P (x :: l)%list.
Proof.
Abort.

Lemma elements_add : forall k e l m',
  M.elements (elt:=MemoryBlockC) m' = ((k, e) :: l)%list
    -> ~ M.In k (P.of_list l) /\
       P.Add k e (P.of_list l) (P.of_list ((k, e) :: l)%list).
Proof.
Abort.

Lemma find_within : forall elt (m : M.t elt) k e P,
  M.find k m = Some e
    -> P k e = true
    -> (forall k' e', k' <> k -> P k' e' = false)
    -> find_if P m = Some (k, e).
Proof.
  intros.
  unfold find_if.
  revert H.
  generalize dependent e.
  apply P.fold_rec; intros.
    apply P.elements_Empty in H.
    rewrite F.elements_o in H2.
    rewrite H in H2.
    inversion H2.
Admitted.

Lemma map_elements_ind :
  forall elt (P : list (M.key * elt) -> Prop) (m : M.t elt),
    P []%list
      -> (forall (k : M.key) (v : elt) (l : list (M.key * elt)),
            P l -> M.find k m = Some v -> P ((k, v) :: l)%list)
      -> P (M.elements (elt:=elt) m).
Proof.
  intros.
  setoid_rewrite F.elements_o in H0.
  induction m using P.map_induction.
    apply P.elements_Empty in H1.
    rewrite H1.
    assumption.
  clear H.
  setoid_rewrite <- F.elements_o in H0.
  setoid_rewrite <- F.elements_o in IHm1.
  pose proof H0.
  specialize (H x e (M.elements (elt:=elt) m1)).
  specialize (H2 x).
Abort.

Theorem Peek_in_heap {r_o r_n} (AbsR : Heap_AbsR r_o r_n) pos :
  forall base blk',
    Find (withinMemBlock pos) base blk' (` r_o)
      -> exists cblk',
           find_if (withinMemBlockC pos) (snd r_n) = Some (base, cblk') /\
           MemoryBlock_AbsR blk' cblk'.
Proof.
  intros.
  destruct H.
  pose proof (allocations_disjoint (proj2_sig r_o) _ H H0).
  destruct AbsR; reduction; exists cblk.
  apply find_within with (P:=withinMemBlockC pos) in HC; auto.
    eapply withinMemAbsR; eauto.
  intros.
  apply not_within_reflect.
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
      (Ifopt find_if (withinMemBlockC d) (snd r_n) as p
       Then Ifopt M.find (d - fst p) (memCData (snd p)) as v
            Then v Else Zero
       Else Zero).

    simplify with monad laws; simpl.
    refine pick val r_n.
      simplify with monad laws.
      finish honing.

    AbsR_prep; assumption.

    intros; subst; clear H.
    admit.
    (* destruct (Peek_in_heap H0 H1) as [? [H3 H4]]. *)
    (* rewrite H3; simpl. *)
    (* destruct H4; reduction; subst. *)
    (* rewrite HC; reflexivity. *)
  }

  refine method pokeS.
  {
    unfold poke, set_address.
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
    - apply Map_SetMap_AbsR; auto; intros; destruct H2.
      split; rewrite H2; decisions; intuition; simpl.
      apply Update_SetMap_AbsR; trivial.
    - apply (Poke_in_heap (conj H0 H1)).
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
