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
      a d m i t.
    a d m i t.

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

Lemma Map_set_fold_keys_AbsR : forall elt r (m : M.t elt) f,
  (forall x y : M.key, E.eq (f x) (f y) -> E.eq x y)
    -> r [R Map_AbsR eq] m
    -> Map_set (fun p => (f (fst p), snd p)) r
         [R Map_AbsR eq]
         M.fold (fun k : M.key => M.add (f k)) m (M.empty elt).
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
    apply H in H4.
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
    pose proof (Lookup_Map_set (B:=elt) (a:=f k) (b:=cblk)
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

Lemma overlaps_within : forall addr1 len1 addr2 len2,
  0 < len1 -> overlaps addr1 len1 addr2 len2
                <-> Ifdec addr1 < addr2
                    Then within addr1 len1 addr2
                    Else within addr2 len2 addr1.
Proof. intros; decisions; nomega. Qed.

Corollary not_overlaps_within : forall addr1 len1 addr2 len2,
  0 < len1
    -> ~ overlaps addr1 len1 addr2 len2
         <-> Ifdec addr1 < addr2
             Then ~ within addr1 len1 addr2
             Else ~ within addr2 len2 addr1.
Proof.
  split; intros.
    decisions;
    unfold not; intros;
    apply H0, overlaps_within; trivial;
    decisions; firstorder.
  unfold not; intros;
  apply overlaps_within in H1; trivial;
  decisions; firstorder.
Qed.
