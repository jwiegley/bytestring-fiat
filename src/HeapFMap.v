Require Import
  ByteString.Relations
  ByteString.TupleEnsembles
  ByteString.Nomega
  ByteString.BindDep
  ByteString.ADTInduction
  ByteString.Tactics
  ByteString.Heap
  ByteString.HeapADT
  ByteString.Within
  ByteString.DefineAbsR
  ByteString.Same_set
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Module HeapFMap (M : WSfun N_as_DT).

Module Import Within := Within M.
Module Import Define := Define_AbsR M.

Import Within.Block.
Import Block.FunMaps.

Require Import Fiat.ADT Fiat.ADTNotation.

Definition Heap_AbsR
           (or : Rep HeapSpec)
           (nr : N * M.t MemoryBlockC) : Prop :=
  Map_AbsR MemoryBlock_AbsR or (snd nr) /\
  P.for_all (within_allocated_mem (fst nr)) (snd nr).

Theorem heaps_refine_to_maps : forall r : Rep HeapSpec, fromADT _ r ->
  exists m : M.t MemoryBlockC, Map_AbsR MemoryBlock_AbsR r m.
Proof.
  intros; apply every_finite_map_has_an_associated_fmap; auto.
  - apply heap_is_finite; auto.
  - apply allocations_unique; auto.
Qed.

Ltac apply_for_all :=
  match goal with
  | [ H1 : is_true (P.for_all ?P ?m),
      H2 : M.MapsTo ?k ?e ?m |- _ ] =>
    let H3 := fresh "H3" in
    assert (H3 : Proper (eq ==> eq ==> eq) P) by auto;
    pose proof (proj1 (@P.for_all_iff _ P H3 m) H1 k e H2)
  | [ H1 : P.for_all ?P ?m = true,
      H2 : M.MapsTo ?k ?e ?m |- _ ] =>
    let H3 := fresh "H3" in
    assert (H3 : Proper (eq ==> eq ==> eq) P) by auto;
    pose proof (proj1 (@P.for_all_iff _ P H3 m) H1 k e H2)
  end.

Ltac related_maps' :=
  repeat (
    related_maps; auto with maps;
    try match goal with
      [ |- MemoryBlock_AbsR {| memSize := _;  memData := _ |}
                            {| memCSize := _; memCData := _ |} ] =>
      apply MemoryBlock_AbsR_impl; auto with maps
    end).

Ltac AbsR_prep :=
  repeat
    match goal with
    | [ H : Heap_AbsR _ _ |- _ ] => unfold Heap_AbsR in H; simpl in H
    | [ |- Heap_AbsR _ _ ] => unfold Heap_AbsR; simpl
    | [ H : _ /\ _ |- _ ] => destruct H; simpl in H
    | [ |- _ /\ _ ] => split
    end; simpl; eauto; eauto with maps; related_maps'.

Require Import Fiat.ADTRefinement Fiat.ADTRefinement.BuildADTRefinements.

Lemma Heap_AbsR_outside_mem
      {r_o r_n} (AbsR : Heap_AbsR r_o r_n)
      (d : {len : N | 0 < len}) :
  All (fun addr' blk' =>
         ~ overlaps addr' (memSize blk') (fst r_n) (` d)) r_o.
Proof.
  intros addr blk H.
  apply AbsR in H; destruct H as [? [? ?]].
  rewrite (proj1 H0).
  destruct AbsR as [_ ?].
  apply_for_all. nomega.
Qed.

Lemma refine_set_pair_same : forall A (x z : Comp A) B (y w : B),
  Same_set _ x z -> y = w -> refine (ret (x, y)) (ret (z, w)).
Proof.
  intros; subst; f_equiv; f_equal.
  apply Extensionality_Ensembles; assumption.
Qed.

Theorem Heap_refine_alloc' `(AbsR : Heap_AbsR r_o r_n) d :
 fromADT HeapSpec r_o ->
  refine
    (alloc r_o d)
    (ret (of_map MemoryBlock_AbsR
                 (M.add (fst r_n)
                        {| memCSize := proj1_sig d
                         ; memCData := M.empty _ |} (snd r_n)), fst r_n)).
Proof.
  intros.
  unfold alloc, FindFreeBlock.
  refine pick val (fst r_n).
    simplify with monad laws; simpl.
    apply refine_set_pair_same; auto.
    apply Same_Same_set, of_map_Same.
    destruct AbsR.
    related_maps'.
  apply Heap_AbsR_outside_mem; assumption.
Qed.

Theorem Heap_refine_alloc `(AbsR : Heap_AbsR r_o r_n) d :
 fromADT HeapSpec r_o ->
  refine
    (x <- alloc r_o d;
     r_n' <- {r_n0 : N * M.t MemoryBlockC | Heap_AbsR (fst x) r_n0};
     ret (r_n', snd x))
    (ret ((fst r_n + proj1_sig d,
           M.add (fst r_n)
                 {| memCSize := proj1_sig d
                  ; memCData := M.empty _ |} (snd r_n)), fst r_n)).
Proof.
  intros.
  remember (fst r_n + _, _) as r_n'.
  unfold alloc, FindFreeBlock.
  simplify with monad laws; simpl.
  refine pick val (fst r_n).
    simplify with monad laws; simpl.
    refine pick val r_n'.
      simplify with monad laws; simpl.
      rewrite Heqr_n'.
      reflexivity.
    rewrite Heqr_n'.
    destruct AbsR.
    AbsR_prep.
    apply for_all_add_iff; auto.
      unfold not; intros.
      apply (proj1 (in_mapsto_iff _ _ _)) in H2.
      destruct H2.
      apply_for_all.
      apply H0 in H2; destruct H2, H2.
      pose proof (allocations_have_size H _ _ H2).
      rewrite (proj1 H5) in H6.
      abstract nomega.
    split.
      apply for_all_impl
       with (P':=within_allocated_mem (fst r_n + ` d)) in H1; auto.
      abstract nomega.
    abstract nomega.
  apply Heap_AbsR_outside_mem; assumption.
Qed.

Theorem Heap_refine_free `(AbsR : Heap_AbsR r_o r_n) d :
 fromADT HeapSpec r_o ->
  refine
    (x <- free r_o d;
     r_n' <- {r_n0 : N * M.t MemoryBlockC | Heap_AbsR (fst x) r_n0};
     ret (r_n', snd x))
    (ret ((fst r_n, M.remove d (snd r_n)), tt)).
Proof.
  intros.
  remember (fst r_n, _) as r_n'.
  simplify with monad laws; simpl.
  refine pick val r_n'.
    simplify with monad laws.
    rewrite Heqr_n'.
    finish honing.
  rewrite Heqr_n'.
  destruct AbsR.
  AbsR_prep.
  apply for_all_remove; auto.
Qed.

Theorem Peek_in_heap
        {r_o : { r | fromADT HeapSpec r }}
        {r_n} (AbsR : Heap_AbsR (` r_o) r_n) pos :
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
    apply Filter_Map_AbsR; auto.
      apply withinMemBlock_Proper; reflexivity.
      apply withinMemBlockC_Proper; reflexivity.
      apply withinMemBlock_AbsR_applied; eauto.
      apply (proj1 AbsR).
    Focus 2.
    apply Single_Map_AbsR; eauto.
  apply find_if_filter_is_singleton in H2; auto.
  unfold optionP, pairP in H2.
  destruct (find_if (withinMemBlockC pos) (snd r_n)).
    destruct p, H2; subst; trivial.
  tauto.
Qed.

Theorem Heap_refine_poke `(AbsR : Heap_AbsR r_o r_n) d d0
        T (k : _ -> Comp T) :
 fromADT HeapSpec r_o ->
  refine
    (a <- poke r_o d d0;
     r_n' <- {r_n0 : N * M.t MemoryBlockC | Heap_AbsR (fst a) r_n0 };
     k (r_n', snd a))
    (k ((fst r_n,
         M.mapi (fun addr cblk =>
                   IfDec within addr (memCSize cblk) d
                   Then {| memCSize := memCSize cblk
                         ; memCData := M.add (d - addr) d0
                                             (memCData cblk) |}
                   Else cblk) (snd r_n)), tt)).
Proof.
  intros.
  remember (fst r_n, _) as r_n'.
  simplify with monad laws; simpl.
  refine pick val r_n'.
    simplify with monad laws.
    rewrite Heqr_n'.
    finish honing.
  rewrite Heqr_n'.
  destruct AbsR.
  AbsR_prep; relational.
    swap_sizes; decisions; auto.
    destruct H3.
    related_maps'.
  unfold P.for_all.
  apply P.fold_rec_bis; auto; intros.
  apply F.mapi_mapsto_iff in H2.
  destruct H2, H2.
  simpl; intros; subst; auto.
  unfold within_allocated_mem, IfDec_Then_Else; simpl.
  eapply P.for_all_iff in H1; eauto.
    unfold within_allocated_mem in H1.
    decisions; simpl in *; auto;
    congruence; auto.
  intros; subst; reflexivity.
Qed.

Theorem Heap_refine_memcpy `(AbsR : Heap_AbsR r_o r_n) d d0 d1 :
 fromADT HeapSpec r_o ->
  refine
    (x0 <- memcpy r_o d d0 d1;
     r_n' <- {r_n0 : N * M.t MemoryBlockC | Heap_AbsR (fst x0) r_n0};
     ret (r_n', snd x0))
    (ret ((if 0 <? d1
           then
             match (find_if (withinMemBlockC d) (snd r_n),
                    find_if (withinMemBlockC d0) (snd r_n)) with
             | (Some (saddr, src), Some (daddr, dst)) =>
               if (Decidable_witness (P:=fits saddr (memCSize src) d  d1) &&
                   Decidable_witness (P:=fits daddr (memCSize dst) d0 d1))%bool
               then
                 (fst r_n,
                  M.add daddr
                        {| memCSize := memCSize dst
                           ; memCData :=
                               let soff := d - saddr in
                               let doff := d0 - daddr in
                               let s := keep_keys (within_bool soff d1)
                                                  (memCData src) in
                               let d := keep_keys (negb ∘ within_bool doff d1)
                                                  (memCData dst) in
                               P.update d (shift_keys soff doff s)

                        (* jww (2016-08-11): This version is more efficient in
                        a strictly evaluated environment, but I'm having
                        difficulty proving correspondence of the folds. *)

                        (* let soff := d - saddr in *)
                        (* let doff := d0 - daddr in *)
                        (* M.fold (fun k e m => *)
                        (*           if within_bool soff d1 k *)
                        (*           then M.add (k - soff + doff) e m *)
                        (*           else m) (memCData src) *)
                        (*        (keep_keys (negb ∘ within_bool doff d1) *)
                        (*                   (memCData dst)) *)
                        |}
                        (snd r_n))
               else r_n
             | _ => r_n
             end
           else r_n), tt)).
Proof.
  intros.
  remember (if 0 <? d1 then _ else _) as r_n'.
  unfold memcpy, FindBlockThatFits.
  simplify with monad laws; simpl.

  refine pick val
    (Ifopt find_if (withinMemBlockC d) (snd r_n) as p
     Then if Decidable_witness (P:=fits (fst p) (memCSize (snd p)) d d1)
          then Some (fst p,
                     {| memSize := memCSize (snd p)
                      ; memData := of_map eq (memCData (snd p)) |})
          else None
     Else None).
    Focus 2.
    destruct (find_if _ (snd r_n)) eqn:Heqe1; simpl in *.
    destruct ((fst p <=? d)
                && (d <? fst p + memCSize (snd p))
                && (d + d1 <=? fst p + memCSize (snd p))) eqn:Heqe.
        split; [|nomega].
        apply find_if_inv in Heqe1; auto.
        apply AbsR; exists (snd p); intuition.
      apply find_if_inv in Heqe1; auto.
      unfold withinMemBlockC in Heqe1;
      simpl in Heqe1; destruct Heqe1.
      apply andb_false_iff in Heqe; destruct Heqe.
        congruence.
      apply AbsR in H0; destruct H0 as [blk [? ?]].
      intros ????.
      destruct (fst p =? a) eqn:Heqe2.
        apply Neqb_ok in Heqe2; subst.
        pose proof (allocations_unique H _ _ H0 _ H4); subst.
        rewrite (proj1 H3) in H5.
        nomega.
      apply N.eqb_neq in Heqe2.
      apply within_reflect in H1.
      rewrite <- (proj1 H3) in H1.
      pose proof (allocations_disjoint H _ H0 H1 _ H4 Heqe2).
      nomega.
    apply find_if_not_inv in Heqe1; auto.
    assert (Proper (eq ==> eq ==> eq) (negb \oo withinMemBlockC d)) by auto.
    intros ????.
    apply AbsR in H1; destruct H1 as [cblk [? ?]].
    pose proof (proj1 (P.for_all_iff H0 _) Heqe1 _ _ H1).
    unfold withinMemBlockC in H4; simpl in H4.
    rewrite (proj1 H3) in H2.
    unfold negb in H4.
    destruct ((a <=? d) && (d <? a + memCSize cblk)) eqn:Heqe.
      discriminate.
    nomega.

  simplify with monad laws.
  refine pick val
    (Ifopt find_if (withinMemBlockC d0) (snd r_n) as p
     Then if Decidable_witness (P:=fits (fst p) (memCSize (snd p)) d0 d1)
          then Some (fst p,
                     {| memSize := memCSize (snd p)
                      ; memData := of_map eq (memCData (snd p)) |})
          else None
     Else None).
    Focus 2.
    destruct (find_if (withinMemBlockC d0) (snd r_n)) eqn:Heqe1; simpl in *.
    destruct ((fst p <=? d0)
                && (d0 <? fst p + memCSize (snd p))
                && (d0 + d1 <=? fst p + memCSize (snd p))) eqn:Heqe.
        split; [|nomega].
        apply find_if_inv in Heqe1; auto.
        apply AbsR; exists (snd p); intuition.
      apply find_if_inv in Heqe1; auto.
      unfold withinMemBlockC in Heqe1;
      simpl in Heqe1; destruct Heqe1.
      apply andb_false_iff in Heqe; destruct Heqe.
        congruence.
      apply AbsR in H0; destruct H0 as [blk [? ?]].
      intros ????.
      destruct (fst p =? a) eqn:Heqe2.
        apply Neqb_ok in Heqe2; subst.
        pose proof (allocations_unique H _ _ H0 _ H4); subst.
        rewrite (proj1 H3) in H5.
        nomega.
      apply N.eqb_neq in Heqe2.
      apply within_reflect in H1.
      rewrite <- (proj1 H3) in H1.
      pose proof (allocations_disjoint H _ H0 H1 _ H4 Heqe2).
      nomega.
    apply find_if_not_inv in Heqe1; auto.
    assert (Proper (eq ==> eq ==> eq) (negb \oo withinMemBlockC d0)) by auto.
    intros ????.
    apply AbsR in H1; destruct H1 as [cblk [? ?]].
    pose proof (proj1 (P.for_all_iff H0 _) Heqe1 _ _ H1).
    unfold withinMemBlockC in H4; simpl in H4.
    rewrite (proj1 H3) in H2.
    unfold negb in H4.
    destruct ((a <=? d0) && (d0 <? a + memCSize cblk)) eqn:Heqe.
      discriminate.
    nomega.

  simplify with monad laws; simpl.
  refine pick val r_n'.
    simplify with monad laws.
    rewrite Heqr_n'.
    finish honing.
  rewrite Heqr_n'.
  destruct AbsR.
  AbsR_prep; clear H;
  decisions; auto;
  destruct (find_if (withinMemBlockC d) (snd r_n)) eqn:Heqe1;
  try (apply find_if_inv in Heqe1; auto; destruct Heqe1);
  destruct (find_if (withinMemBlockC d0) (snd r_n)) eqn:Heqe2;
  try (apply find_if_inv in Heqe2; auto; destruct Heqe2);
  simpl; auto; decisions;
  try destruct p;
  try destruct p0; simpl in *;
  decisions; simpl; auto;
  related_maps'; try nomega.
  - apply Union_Map_AbsR; auto.
    * apply KeepKeys_Map_AbsR.
        apply not_within_AbsR.
      apply of_map_Map_AbsR; auto.
    * apply ShiftKeys_Map_AbsR.
        constructor; apply KeepKeys_Map_AbsR.
          apply within_AbsR; try reflexivity.
        apply of_map_Map_AbsR; auto.
      unfold KeepKeys; intros ???.
      repeat teardown.
      apply of_map_MapsTo in H6.
      repeat teardown; subst; nomega.
    * unfold not, compose, KeepKeys, ShiftKeys; intros ????.
      repeat teardown; inv H6.
      apply not_within_reflect in H5; nomega.
  - discriminate.
  - discriminate.
  - rewrite <- remove_add.
    apply for_all_add_true; auto.
      simplify_maps.
    split; trivial.
      apply for_all_remove; auto.
    simpl in *.
    clear H2.
    apply_for_all.
    nomega.
Qed.

Lemma HeapImpl : FullySharpened HeapSpec.
Proof.
  start sharpening ADT.
  eapply SharpenStep; [ apply (projT2 HeapSpecADT) |].

  hone representation using (fun or nr => Heap_AbsR (` or) nr).

  refine method emptyS.
  {
    unfold empty.
    remove_dependency.
    simplify with monad laws.

    refine pick val (0%N, @M.empty _).
      finish honing.

    AbsR_prep.
    - apply P.for_all_iff; auto.
  }

  refine method allocS.
  {
    remove_dependency.
    destruct r_o.
    eapply Heap_refine_alloc; eauto.
  }

  refine method freeS.
  {
    remove_dependency.
    destruct r_o.
    eapply Heap_refine_free; eauto.
  }

  refine method reallocS.
  {
    unfold Heap_AbsR, realloc, FindBlock, FindFreeBlock.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val
      (match M.find d (snd r_n) with
       | Some cblk =>
         Some {| memSize := memCSize cblk
               ; memData := of_map eq (memCData cblk) |}
       | None => None
       end).
      Focus 2.
      destruct (M.find d (snd r_n)) eqn:Heqe; simpl.
        destruct H0.
        normalize.
        eapply Lookup_of_map; eauto.
      unfold not; intros.
      destruct H1.
      apply H0 in H1.
      destruct H1, H1.
      apply F.find_mapsto_iff in H1.
      congruence.

    simplify with monad laws.
    refine pick val
      (Ifopt M.find d (snd r_n) as cblk
       Then If ` d0 <=? memCSize cblk
            Then d
            Else fst r_n
       Else fst r_n).
      Focus 2.
      intros ???.
      repeat teardown.
      pose proof (allocations_no_overlap f b H2).
      apply H0 in H2; do 2 destruct H2.
      destruct H0.
      apply_for_all.
      simpl in *.
      destruct (M.find d t) eqn:Heqe; simpl.
        destruct (x <=? memCSize m) eqn:Heqe1; simpl.
          normalize.
          apply_for_all.
          apply H0 in Heqe; destruct Heqe, H10.
          specialize (H3 _ _ H10 H1).
          rewrite <- (proj1 H11) in Heqe1.
          nomega.
        swap_sizes; nomega.
      swap_sizes; nomega.

    simplify with monad laws.
    refine pick val
      (match M.find d (snd r_n) with
       | Some cblk =>
         let data' := P.filter (fun k _ => k <? ` d0) (memCData cblk) in
         if ` d0 <=? memCSize cblk
         then (fst r_n,
               M.add d {| memCSize := ` d0
                        ; memCData := data' |} (snd r_n))
         else (fst r_n + ` d0,
               M.add (fst r_n) {| memCSize := ` d0
                                ; memCData := data' |} (M.remove d (snd r_n)))
       | None =>
         (fst r_n + ` d0,
          M.add (fst r_n)
                {| memCSize := ` d0
                 ; memCData := M.empty _ |} (snd r_n))
       end).
      simplify with monad laws.
      finish honing.

    AbsR_prep; clear H;
    destruct (M.find d (snd r_n)) eqn:Heqe; simpl;
    decisions; simpl.
    - rewrite <- remove_add.
      related_maps'; relational.
        split; nomega.
      apply of_map_Map_AbsR; auto.
    - related_maps'; relational.
        split; nomega.
      apply of_map_Map_AbsR; auto.
    - related_maps'.
    - normalize.
      apply_for_all.
      rewrite <- remove_add.
      apply for_all_add_true; auto.
        simplify_maps.
      split; trivial.
        apply for_all_remove; auto.
      nomega.
    - normalize.
      apply_for_all.
      apply for_all_add_true; auto.
        unfold not; destruct 1.
        simplify_maps.
        apply_for_all.
        apply H0 in H5; destruct H5, H5.
        pose proof (allocations_have_size (proj2_sig r_o) _ _ H5).
        rewrite (proj1 H7) in H8.
        nomega.
      split; trivial.
        apply for_all_remove; auto.
        eapply for_all_impl; eauto; nomega.
      nomega.
    - normalize.
      rewrite <- remove_add.
      apply for_all_add_true; auto.
        simplify_maps.
      split; trivial.
        apply for_all_remove; auto.
        eapply for_all_impl; eauto; nomega.
      nomega.
  }

  refine method peekS.
  {
    unfold Heap_AbsR, peek, FindBlockThatFits.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val
      (Ifopt find_if (withinMemBlockC d) (snd r_n) as p
       Then Some (fst p,
                  {| memSize := memCSize (snd p)
                   ; memData := of_map eq (memCData (snd p)) |})
       Else None).
      Focus 2.
      destruct (find_if _ (snd r_n)) eqn:Heqe1; simpl in *.
        apply find_if_inv in Heqe1; auto.
        split.
          destruct H0.
          eapply Lookup_of_map; eauto.
          intuition.
        unfold withinMemBlockC in Heqe1; simpl in Heqe1.
        nomega.
      intros ????.
      apply H0 in H1; destruct H1, H1.
      apply find_if_not_inv in Heqe1; auto.
      assert (Proper (eq ==> eq ==> eq) (negb \oo withinMemBlockC d)) by auto.
      pose proof (proj1 (P.for_all_iff H4 _) Heqe1 a x H1).
      unfold withinMemBlockC in H5; simpl in H5.
      rewrite (proj1 H3) in H2.
      unfold negb in H5.
      decisions; [discriminate|nomega].

    simplify with monad laws.
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
    - intros; subst; clear H.
      destruct (find_if (withinMemBlockC d) (snd r_n)) eqn:Heqe;
      [|discriminate]; inv H1; simpl in *.
      apply find_if_inv in Heqe; auto; destruct Heqe.
      apply of_map_MapsTo in H2.
      destruct H2 as [cblk [? ?]]; subst.
      apply F.find_mapsto_iff in H2.
      rewrite H2; reflexivity.
  }

  refine method pokeS.
  {
    remove_dependency.
    destruct r_o.
    erewrite Heap_refine_poke; eauto.
    finish honing.
  }

  refine method memcpyS.
  {
    remove_dependency.
    destruct r_o.
    eapply Heap_refine_memcpy; eauto.
  }

  refine method memsetS.
  {
    unfold memset.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val
      (fst r_n,
       M.mapi (fun addr cblk =>
                 IfDec fits addr (memCSize cblk) d d0
                 Then {| memCSize := memCSize cblk
                       ; memCData :=
                           let base := d - addr in
                           N.peano_rect (fun _ => M.t Word8)
                                        (memCData cblk)
                                        (fun i => M.add (base + i) d1) d0  |}
                 Else cblk) (snd r_n)).
      simplify with monad laws.
      finish honing.

    AbsR_prep; relational; clear H.
    - swap_sizes;
      decisions; auto;
      related_maps';
      apply Define_Map_AbsR; auto;
      exact (proj2 H3).
    - eapply P.for_all_iff; auto; intros.
      do 2 simplify_maps; intros; subst; auto.
      apply_for_all.
      decisions; auto.
  }

  finish_SharpeningADT_WithoutDelegation.
Defined.

End HeapFMap.
