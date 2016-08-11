Require Import
  Here.Relations
  Here.TupleEnsembles
  Here.Nomega
  Here.BindDep
  Here.ADTInduction
  Here.Tactics
  Here.Heap
  Here.Within
  Here.DefineAbsR
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Module HeapFMap (Mem : Memory) (M : WSfun N_as_DT).

Module Import Within := Within Mem M.
Module Import Define := Define_AbsR M.

Import Within.Block.
Import Within.Block.Adt.
Import Within.Block.Adt.Heap.
Import Within.Block.FunMaps.

Require Import Fiat.ADT Fiat.ADTNotation.

Definition Heap_AbsR
           (or : { r : Rep HeapSpec | fromADT HeapSpec r})
           (nr : N * M.t MemoryBlockC) : Prop :=
  Map_AbsR MemoryBlock_AbsR (` or) (snd nr) /\
  P.for_all (within_allocated_mem (fst nr)) (snd nr).

Hint Extern 5 =>
  match goal with
    [ H : fromADT HeapSpec ?R
    |- Finite_sets.Finite (M.key * MemoryBlock) ?R ] =>
    exact (heap_is_finite H)
  end.

Hint Extern 5 =>
  match goal with
    [ H : fromADT HeapSpec ?R |- Functional ?R ] =>
    exact (allocations_unique H)
  end.

Theorem heaps_refine_to_maps : forall r : Rep HeapSpec, fromADT _ r ->
  exists m : M.t MemoryBlockC, Map_AbsR MemoryBlock_AbsR r m.
Proof. intros; apply every_finite_map_has_an_associated_fmap; auto. Qed.

Lemma Heap_AbsR_outside_mem
      {r_o r_n} (AbsR : Heap_AbsR r_o r_n)
      (d : {len : N | 0 < len}) :
  All (fun addr' blk' =>
         ~ overlaps addr' (memSize blk') (fst r_n) (` d)) (` r_o).
Proof.
  intros addr blk H.
  destruct AbsR as [H1 ?].
  apply H1 in H; destruct H as [? [? ?]].
  swap_sizes.
  apply (proj1 (P.for_all_iff _ _)) with (k:=addr) (e:=x) in H0;
  [|exact H].
  unfold within_allocated_mem in H0; simpl in H0.
  unfold not, overlaps, within in *; nomega.
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
  apply P.fold_rec_bis; auto; intros.
  apply F.mapi_mapsto_iff in H0.
  destruct H0, H0.
  simpl; intros; subst; auto.
  unfold within_allocated_mem, IfDec_Then_Else; simpl.
  eapply P.for_all_iff in H; eauto.
    unfold within_allocated_mem in H.
    decisions; simpl in *; auto;
    congruence; auto.
  intros; subst; reflexivity.
Qed.

Ltac AbsR_prep :=
  repeat
    match goal with
    | [ H : Heap_AbsR _ _ |- _ ] => unfold Heap_AbsR in H; simpl in H
    | [ |- Heap_AbsR _ _ ] => unfold Heap_AbsR; simpl
    | [ H : _ /\ _ |- _ ] => destruct H; simpl in H
    | [ |- _ /\ _ ] => split
    end; simpl; eauto; eauto with maps.

Require Import Fiat.ADTRefinement Fiat.ADTRefinement.BuildADTRefinements.

Ltac related_maps' :=
  repeat (
    related_maps; auto with maps;
    try match goal with
      [ |- MemoryBlock_AbsR {| memSize := _;  memData := _ |}
                            {| memCSize := _; memCData := _ |} ] =>
      apply MemoryBlock_AbsR_impl; auto with maps
    end).

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

Lemma Lookup_of_map : forall addr cblk r_o r_n,
  Map_AbsR MemoryBlock_AbsR r_o r_n
    -> M.MapsTo addr cblk r_n
    -> Lookup addr {| memSize := memCSize cblk
                    ; memData := of_map eq (memCData cblk) |} r_o.
Proof.
  intros.
  apply H in H0.
  destruct H0, H0, H1.
  apply of_map_Same in H2.
  apply H.
  exists cblk.
  intuition.
  apply H.
  exists x.
  intuition.
  split; intros; trivial.
  rewrite H2.
  apply of_map_Map_AbsR; auto.
Qed.

(* Adding to an FMap overwrites the previous entry. *)
Lemma remove_add : forall elt k (e : elt) m,
  M.Equal (M.add k e (M.remove k m)) (M.add k e m).
Proof.
  intros.
  induction m using P.map_induction_bis.
  - rewrite <- H; assumption.
  - apply F.Equal_mapsto_iff; split; intros;
    repeat simplify_maps.
  - apply F.Equal_mapsto_iff; split; intros;
    repeat simplify_maps;
    right; intuition; simplify_maps.
Qed.

Lemma Map_set_fold_AbsR : forall r m f,
  (forall x y, f x = f y -> x = y)
    -> r [R Map_AbsR eq] m
    -> Map_set (fun p => (f (fst p), snd p)) r
         [R Map_AbsR eq]
         M.fold (fun k : M.key => M.add (f k)) m (M.empty Mem.Word8).
Proof.
  intros.
  relational; split; intros; split; intros H1.
  - repeat teardown; inv H1.
    apply H0 in H2;
    destruct H2 as [cblk [? ?]]; subst.
    exists cblk; intuition.
    revert H1.
    apply P.fold_rec_bis; auto; intros.
      rewrite <- H1 in H3; intuition.
    repeat simplify_maps.
    right; intuition.
  - reduction.
    revert H1.
    apply P.fold_rec_bis; auto; intros.
    simplify_maps.
    exists (k, x); simpl.
    apply H0 in H1; destruct H1.
    intuition; subst; assumption.
  - revert H1.
    apply P.fold_rec_bis; auto; intros.
    simplify_maps.
    exists cblk; simpl.
    intuition.
    pose proof (Lookup_Map_set (B:=Mem.Word8) (a:=f k) (b:=cblk)
                               (fun p => (f (fst p), snd p))).
    apply H4.
    exists (k, cblk); simpl.
    apply H0 in H1; destruct H1.
    intuition; subst; assumption.
  - repeat teardown; subst; inv H1.
    apply H0 in H3.
    destruct H3 as [blk [? ?]]; subst.
    revert H1.
    apply P.fold_rec_bis; auto; intros.
      rewrite <- H1 in H3; intuition.
    repeat simplify_maps.
    right; intuition.
Qed.

Definition keep_keys (P : M.key -> bool) : M.t Mem.Word8 -> M.t Mem.Word8 :=
  P.filter (const ∘ P).

Definition shift_keys (orig_base : N) (new_base : N) (m : M.t Mem.Word8) :
  M.t Mem.Word8 :=
  M.fold (fun k => M.add (k - orig_base + new_base)) m (M.empty _).

(*
Lemma keep_keys_fold : forall soff doff len s d,
  M.Equal (M.fold (fun k e m =>
                     if within_bool soff len k
                     then M.add (k - soff + doff) e m
                     else m) s d)
          (M.fold (fun k => M.add (k - soff + doff))
                  (keep_keys (within_bool soff len) s) d).

Lemma keep_shift_fold : forall soff doff s d,
  P.for_all (fun k _ => soff <=? k) s ->
  M.Equal (M.fold (fun k => M.add (k - soff + doff)) s d)
          (P.update d (shift_keys soff doff s)).
Proof.
  unfold P.update, shift_keys; intros.
  revert H.
  apply P.fold_rec; intros.
    rewrite P.fold_Empty; auto.
      reflexivity.
    rewrite P.fold_Empty; auto.
    apply M.empty_1.

  apply add_equal_iff in H1.
  rewrite <- H1 in H3.
  apply for_all_add_true in H3;
  destruct H3; auto; relational.
  intuition.

  assert (P.transpose_neqkey M.Equal (@M.add Mem.Word8)).
    intros ??????.
    apply add_associative; tauto.

  assert (Proper (eq ==> eq ==> M.Equal ==> M.Equal) (@M.add Mem.Word8)).
    relational.
    rewrite <- H8.
    reflexivity.

  remember (fun _ => M.add _) as f.
  assert (P.transpose_neqkey M.Equal f).
    intros ??????.
    rewrite Heqf.
    apply add_associative; intros.
    apply N.add_cancel_r in H8.
    apply Nsub_eq in H8.
        contradiction.
      admit.
    admit.

  assert (Proper (eq ==> eq ==> M.Equal ==> M.Equal) f).
    relational.
    rewrite <- H10.
    reflexivity.

  pose proof (@fold_Proper Mem.Word8 _ (@M.add Mem.Word8) M.Equal
                           (F.EqualSetoid _) H6 H2).
  pose proof (@fold_Proper Mem.Word8 _ f M.Equal (F.EqualSetoid _) H8 H7).

  rewrite <- H1.
  apply add_equal_iff in H1.

  erewrite P.fold_add; eauto.
  rewrite H5, Heqf.
  erewrite P.fold_add; eauto.
    reflexivity.
  unfold not; intros; destruct H11.
  contradiction H0.
  exists x.
  revert H11.
  apply P.fold_rec_bis; intros; auto.
    rewrite <- H11.
    intuition.
  repeat simplify_maps.
    left; intuition.
    apply N.add_cancel_r in H15.
    apply (proj1 (P.for_all_iff _ _)) with (k1:=k0) (e0:=x) in H3;
    [|exact H11].
    apply Nsub_eq in H15; auto; nomega.
  right; intuition; subst; tauto.
*)

Lemma KeepKeys_Map_AbsR :
  KeepKeys [R (N.eq ==> boolR) ==> Map_AbsR eq ==> Map_AbsR eq] keep_keys.
Proof.
  unfold KeepKeys, keep_keys, compose, const.
  constructor.
  intros ???.
  apply Filter_Map_AbsR; auto; relational.
  apply H; reflexivity.
Qed.

Hint Resolve KeepKeys_Map_AbsR : maps.

Lemma ShiftKeys_Map_AbsR : forall b d r m,
  r [R Map_AbsR eq] m ->
  All (fun k _ => b <= k) r ->
  (* P.for_all (fun k _ => b <=? k) m -> *)
  ShiftKeys b d r [R Map_AbsR eq] shift_keys b d m.
Proof.
  unfold ShiftKeys, shift_keys, compose, const; intros.
  eapply (All_Map_AbsR (A:=Mem.Word8) (B:=Mem.Word8) (R:=eq)
                       (f:=fun k _ => b <= k) (f':=fun k _ => b <=? k)) in H0.
    Focus 2. relational.
    Focus 2. relational. split; nomega.
    Focus 2. apply logical_prf.
  relational; split; intros; split; intros H1.
  - repeat teardown; inv H1.
    apply H in H2;
    destruct H2 as [cblk [? ?]]; subst.
    pose proof H0.
    apply (proj1 (P.for_all_iff _ _)) with (k:=n) (e:=cblk) in H2; [|exact H1].
    exists cblk; intuition.
    revert H1.
    revert H0.
    apply P.fold_rec_bis; auto; intros.
      rewrite <- H0 in H3, H4; intuition.
    repeat simplify_maps.
    apply for_all_add_true in H4;
    destruct H4; auto; relational.
    right; intuition.
    apply N.add_cancel_r in H6.
    apply Nsub_eq in H6; auto; nomega.
  - reduction.
    revert H1.
    revert H0.
    apply P.fold_rec_bis; auto; intros.
      rewrite <- H0 in H2; intuition.
    apply for_all_add_true in H3;
    destruct H3; auto; relational.
    simplify_maps.
    exists (k, x); simpl.
    apply H in H0; destruct H0.
    intuition; subst; assumption.
  - revert H1.
    revert H0.
    apply P.fold_rec_bis; auto; intros.
      rewrite <- H0 in H2; intuition.
    apply for_all_add_true in H3;
    destruct H3; auto; relational.
    simplify_maps.
    exists cblk; simpl.
    intuition.
    pose proof (Lookup_Map_set (B:=Mem.Word8) (a:=k - b + d) (b:=cblk)
                               (fun p => (fst p - b + d, snd p))).
    apply H2.
    exists (k, cblk); simpl.
    apply H in H0; destruct H0.
    intuition; subst; assumption.
  - repeat teardown; subst; inv H1.
    apply H in H3.
    destruct H3 as [blk [? ?]]; subst.
    revert H1.
    revert H0.
    apply P.fold_rec_bis; auto; intros.
      rewrite <- H0 in H2, H3; intuition.
    apply for_all_add_true in H3;
    destruct H3; auto; relational.
    repeat simplify_maps.
    right; intuition.
    apply (proj1 (P.for_all_iff _ _)) with (k0:=n) (e0:=blk) in H3; [|exact H9].
    apply N.add_cancel_r in H4.
    apply Nsub_eq in H4; auto; nomega.
Qed.

Lemma within_AbsR :
  within [R N.eq ==> N.eq ==> N.eq ==> boolR] within_bool.
Proof.
  intros.
  relational; unfold compose, negb; split; intros.
    rewrite H, H0, H1 in H2.
    decisions; auto; nomega.
  rewrite <- H, <- H0, <- H1 in H2.
  decisions; auto; nomega.
Qed.

Lemma not_within_AbsR : forall b l,
  (not ∘ within b l) [R N.eq ==> boolR] (negb ∘ within_bool b l).
Proof.
  intros.
  relational; unfold compose, negb; split; intros.
    rewrite H in H0.
    decisions; auto; nomega.
  rewrite <- H in H0.
  decisions; auto.
    discriminate.
  nomega.
Qed.

Hint Resolve ShiftKeys_Map_AbsR : maps.

Lemma HeapImpl : FullySharpened HeapSpec.
Proof.
  start sharpening ADT.
  eapply SharpenStep; [ apply (projT2 HeapSpecADT) |].

  hone representation using Heap_AbsR.

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
    - related_maps'.
    - apply for_all_add_iff; auto.
      + unfold not; intros.
        apply (proj1 (in_mapsto_iff _ _ _)) in H2.
        destruct H2.
        apply_for_all.
        apply H0 in H2; destruct H2, H2.
        pose proof (allocations_have_size (proj2_sig r_o) _ _ H2).
        rewrite (proj1 H5) in H6.
        abstract nomega.
      + split.
          apply for_all_impl
           with (P':=within_allocated_mem (fst r_n + ` d)) in H1; auto.
          abstract nomega.
        abstract nomega.
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
    - related_maps'.
    - apply for_all_remove; auto.
  }

  refine method reallocS.
  {
    unfold Heap_AbsR, realloc.
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
      related_maps'.
      apply Filter_Map_AbsR; auto; relational.
        split; nomega.
      apply of_map_Map_AbsR; auto.
    - related_maps'.
      apply Filter_Map_AbsR; auto; relational.
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
    unfold Heap_AbsR, peek.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val
      (Ifopt find_if (withinMemBlockC d) (snd r_n) as p
       Then Ifopt M.find (d - fst p) (memCData (snd p)) as v
            Then v Else Mem.Zero
       Else Mem.Zero).

    simplify with monad laws; simpl.
    refine pick val r_n.
      simplify with monad laws.
      finish honing.

    AbsR_prep.
    - intros; subst; clear H.
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
    - related_maps; relational.
      swap_sizes; decisions; auto.
      related_maps'; exact (proj2 H4).
  }

  refine method memcpyS.
  {
    unfold Heap_AbsR, memcpy.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val
      (if 0 <? d1
       then Ifopt find_if (withinMemBlockC d) (snd r_n) as p
            Then if Decidable_witness (P:=fits (fst p) (memCSize (snd p)) d d1)
                 then Some (fst p,
                            {| memSize := memCSize (snd p)
                             ; memData := of_map eq (memCData (snd p)) |})
                 else None
            Else None
       else None).
      Focus 2.
      intros; decisions; try discriminate. split; [nomega|].
      destruct (find_if _ (snd r_n)) eqn:Heqe1; simpl in *;
      decisions; inv H1.
      split; [|nomega].
      apply find_if_inv in Heqe1; auto.
      apply H0; exists (snd p); intuition.

    simplify with monad laws.
    refine pick val
      (if 0 <? d1
       then Ifopt find_if (withinMemBlockC d0) (snd r_n) as p
            Then if Decidable_witness (P:=fits (fst p) (memCSize (snd p)) d0 d1)
                 then Some (fst p,
                            {| memSize := memCSize (snd p)
                             ; memData := of_map eq (memCData (snd p)) |})
                 else None
            Else None
       else None).
      Focus 2.
      intros; decisions; try discriminate. split; [nomega|].
      destruct (find_if _ (snd r_n)) eqn:Heqe1; simpl in *;
      decisions; inv H1.
      split; [|nomega].
      apply find_if_inv in Heqe1; auto.
      apply H0; exists (snd p); intuition.

    simplify with monad laws.
    refine pick val
      (if 0 <? d1
       then
         match (find_if (withinMemBlockC d) (snd r_n),
                find_if (withinMemBlockC d0) (snd r_n)) with
         | (Some (saddr, src), Some (daddr, dst)) =>
           if (Decidable_witness
                 (P:=fits saddr (memCSize src) d d1) &&
               Decidable_witness
                 (P:=fits daddr (memCSize dst) d0 d1))%bool
           then
             (fst r_n,
              M.add daddr
                {| memCSize := memCSize dst
                 ; memCData :=
                     let soff := d - saddr in
                     let doff := d0 - daddr in
                     let s := keep_keys (within_bool soff d1) (memCData src) in
                     let d := keep_keys (negb ∘ within_bool doff d1)
                                        (memCData dst) in
                     P.update d (shift_keys soff doff s)

                     (* jww (2016-08-11): This version is more efficient in a
                        strictly evaluated environment, but I'm having
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
       else r_n).
      simplify with monad laws.
      finish honing.

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
    - rewrite <- remove_add.
      apply for_all_add_true; auto.
        simplify_maps.
      split; trivial.
        apply for_all_remove; auto.
      simpl in *.
      clear H2.
      apply_for_all.
      nomega.
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
                           N.peano_rect (fun _ => M.t Mem.Word8)
                                        (memCData cblk)
                                        (fun i => M.add (base + i) d1) d0  |}
                 Else cblk) (snd r_n)).
      simplify with monad laws.
      finish honing.

    AbsR_prep.
    - related_maps';
      relational; subst; auto;
      swap_sizes;
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
