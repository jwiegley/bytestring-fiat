Require Import
  ByteString.Relations
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Module FMapExt (E : DecidableType) (M : WSfun E).

Module P := WProperties_fun E M.
Module F := P.F.

Ltac normalize :=
  repeat match goal with
  | [ H : M.find ?ADDR ?Z = Some ?CBLK |- _ ] => apply F.find_mapsto_iff in H
  | [ |-  M.find ?ADDR ?Z = Some ?CBLK ]      => apply F.find_mapsto_iff
  end.

Ltac simplify_maps :=
  normalize;
  match goal with
  | [ H : M.MapsTo (elt:=?T) ?A ?B (M.add ?K ?E ?M) |- _ ] =>
    apply F.add_mapsto_iff in H;
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    destruct H as [[H1 H2]|[H3 H4]]; [subst|]
  | [ H : M.MapsTo (elt:=?T) ?A ?B (M.remove ?KE ?M) |- _ ] =>
    apply F.remove_mapsto_iff in H;
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    destruct H as [H1 H2]
  | [ H : M.MapsTo (elt:=?T) ?A ?B (M.map ?F ?M) |- _ ] =>
    apply F.map_mapsto_iff in H;
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let cblk := fresh "cblk" in
    destruct H as [cblk [H1 H2]]
  | [ H : M.MapsTo (elt:=?T) ?A ?B (P.filter ?F ?M) |- _ ] =>
    apply P.filter_iff in H;
    [let H1 := fresh "H1" in
     let H2 := fresh "H2" in
     destruct H as [H1 H2]|]
  | [ H : M.MapsTo (elt:=?T) ?A ?B (M.mapi ?F ?M) |- _ ] =>
    apply F.find_mapsto_iff in H;
    rewrite F.mapi_o, <- F.map_o in H;
    apply F.find_mapsto_iff in H
  | [ H : M.MapsTo (elt:=?T) ?A ?B (M.empty ?U) |- _ ] =>
    apply F.empty_mapsto_iff in H; contradiction
  | [ H1 : M.MapsTo (elt:=?T) ?A ?B ?M,
      H2 : M.Empty (elt:=?T) ?M |- _ ] =>
    apply F.find_mapsto_iff in H1;
    apply P.elements_Empty in H2;
    rewrite F.elements_o in H1;
    rewrite H2 in H1;
    inversion H1

  | [ |- M.MapsTo (elt:=?T) ?A ?B (M.add ?K ?E ?M) ] =>
    apply F.add_mapsto_iff
  | [ |- M.MapsTo (elt:=?T) ?A ?B (M.remove ?KE ?M) ] =>
    apply F.remove_mapsto_iff
  | [ |- M.MapsTo (elt:=?T) ?A ?B (M.map ?F ?M) ] =>
    apply F.map_mapsto_iff
  | [ |- M.MapsTo (elt:=?T) ?A ?B (P.filter ?F ?M) ] =>
    apply P.filter_iff
  | [ |- M.MapsTo (elt:=?T) ?A ?B (M.mapi ?F ?M) ] =>
    rewrite F.mapi_o, <- F.map_o;
    apply F.map_mapsto_iff

  | [ |- ~ M.In ?d (M.remove ?d ?r) ] =>
    let H := fresh "H" in
    unfold not; intro H; destruct H; simplify_maps
  end; simpl; auto.

Hint Extern 5 =>
  match goal with
    [ H : M.MapsTo _ _ (M.empty _) |- _ ] =>
      apply F.empty_mapsto_iff in H; contradiction
  end.

Global Program Instance MapsTo_Proper {elt} :
  Proper (E.eq ==> eq ==> M.Equal ==> iff) (@M.MapsTo elt) :=
  (@F.MapsTo_m_Proper elt).

Global Program Instance find_Proper {elt} :
  Proper (E.eq ==> eq ==> M.Equal ==> iff)
         (fun k e m => @M.find elt k m = Some e).
Obligation 1.
  relational.
    rewrite <- H, <- H1; assumption.
  rewrite H, H1; assumption.
Qed.

Global Program Instance fold_Proper {elt A} : forall f (eqA : relation A),
  Equivalence eqA
    -> Proper (E.eq ==> eq ==> eqA ==> eqA) f
    -> P.transpose_neqkey eqA f
    -> Proper (M.Equal (elt:=elt) ==> eqA ==> eqA) (@M.fold elt A f).
Obligation 1. relational; eapply P.fold_Equal2; eauto. Qed.

Lemma add_equal_iff : forall elt k (e : elt) m1 m2,
  P.Add k e m1 m2 <-> M.Equal (M.add k e m1) m2.
Proof.
  split; intros; intro addr;
  specialize (H addr);
  congruence.
Qed.

Global Program Instance filter_Proper {elt} : forall P,
  Proper (E.eq ==> eq ==> eq) P
    -> Proper (M.Equal (elt:=elt) ==> M.Equal) (@P.filter elt P).
Obligation 1.
  relational.
  unfold P.filter at 1.
  generalize dependent y.
  apply P.fold_rec; intros.
    apply F.Equal_mapsto_iff.
    split; intros.
      simplify_maps.
    simplify_maps.
    rewrite <- H1 in H3.
    apply P.elements_Empty in H0.
    apply F.find_mapsto_iff in H3.
    rewrite F.elements_o in H3.
    rewrite H0 in H3.
    inversion H3.
  specialize (H3 m' (F.Equal_refl _)).
  apply add_equal_iff in H2.
  rewrite <- H2 in H4; clear H2 m'' H0.
  destruct (P k e) eqn:Heqe; rewrite H3; clear H3.
    apply F.Equal_mapsto_iff.
    split; intros.
      simplify_maps.
        rewrite <- H2.
        simplify_maps.
        intuition.
        rewrite <- H4.
        simplify_maps.
      simplify_maps.
      simplify_maps.
      intuition.
      rewrite <- H4.
      simplify_maps.
    simplify_maps.
    rewrite <- H4 in H2.
    repeat simplify_maps.
    right.
    intuition.
    simplify_maps.
  apply F.Equal_mapsto_iff.
  split; intros;
  simplify_maps;
  simplify_maps;
  intuition.
    rewrite <- H4; clear H4.
    apply F.add_neq_mapsto_iff; auto.
    unfold not; intros.
    rewrite <- H0 in H2.
    apply F.not_find_in_iff in H1.
    apply F.find_mapsto_iff in H2.
    congruence.
  rewrite <- H4 in H2; clear H4.
  simplify_maps.
  rewrite H0 in Heqe.
  congruence.
Qed.

Global Instance add_Proper {elt} :
  Proper (E.eq ==> eq ==> M.Equal ==> M.Equal) (M.add (elt:=elt)) :=
  (@F.add_m_Proper elt).

Lemma mapi_empty : forall elt (f : M.key -> elt -> elt),
  Proper (E.eq ==> eq ==> eq) f
    -> M.Equal (M.mapi f (M.empty elt)) (M.empty elt).
Proof.
  intros elt f H addr.
  rewrite F.mapi_o, F.empty_o; trivial; intros.
  rewrite H0; reflexivity.
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

Lemma Equal_add_remove : forall elt k (e : elt) m' m'',
  ~ M.In k m' -> M.Equal (M.add k e m') m'' -> M.Equal m' (M.remove k m'').
Proof.
  intros.
  intro addr.
  specialize (H0 addr).
  destruct (E.eq_dec k addr).
    rewrite F.remove_eq_o; auto.
    rewrite F.add_eq_o in H0; auto.
    apply F.not_find_in_iff.
    rewrite <- e0.
    assumption.
  rewrite F.add_neq_o in H0; auto.
  rewrite F.remove_neq_o; auto.
Qed.

Lemma in_mapsto_iff : forall elt k (m : M.t elt),
  M.In (elt:=elt) k m <-> exists e, M.MapsTo (elt:=elt) k e m.
Proof.
  split; intros.
    apply F.mem_in_iff in H.
    rewrite F.mem_find_b in H.
    destruct (M.find (elt:=elt) k m) eqn:Heqe.
      exists e.
      apply F.find_mapsto_iff.
      assumption.
    discriminate.
  apply F.mem_in_iff.
  rewrite F.mem_find_b.
  destruct H.
  apply F.find_mapsto_iff in H.
  rewrite H.
  reflexivity.
Qed.

Theorem add_associative {elt}
        (k : M.key) (e : elt)
        (k0 : M.key) (e0 : elt)
        (z : M.t elt) :
  (E.eq k k0 -> e = e0)
    -> M.Equal (M.add k e (M.add k0 e0 z)) (M.add k0 e0 (M.add k e z)).
Proof.
  intros H addr.
  rewrite !F.add_o.
  destruct (E.eq_dec k addr);
  destruct (E.eq_dec k0 addr); eauto.
  apply E.eq_sym in e2.
  pose proof (E.eq_trans e1 e2).
  rewrite (H H0).
  reflexivity.
Qed.

Section for_all.

Variable elt : Type.
Variable P : M.key -> elt -> bool.
Variable P_Proper : Proper (E.eq ==> eq ==> eq) P.

Global Program Instance for_all_Proper :
  Proper (M.Equal ==> eq) (@P.for_all elt P).
Obligation 1.
  relational.
  revert H.
  unfold P.for_all.
  revert y.
  apply P.fold_rec; intros.
    rewrite P.fold_Empty; eauto.
    rewrite <- H0; assumption.
  apply add_equal_iff in H1.
  rewrite H3 in H1.
  apply add_equal_iff in H1.
  rewrite P.fold_Add; eauto.
  - destruct (P k e); auto.
    apply H2.
    reflexivity.
  - relational.
    rewrite H4; reflexivity.
  - intros ??????.
    destruct (P k0 e0), (P k' e'); auto.
Qed.

Lemma for_all_empty : P.for_all P (M.empty elt) = true.
Proof.
  intros.
  apply P.for_all_iff; trivial; intros.
  apply F.empty_mapsto_iff in H.
  contradiction.
Qed.

Lemma for_all_add_true : forall (m : M.t elt) k e,
  ~ M.In k m
    -> (P.for_all P (M.add k e m) = true
          <-> P.for_all P m = true /\ P k e = true).
Proof.
  unfold P.for_all.
  remember (fun _ _ _ => _) as f.
  assert (Proper (E.eq ==> eq ==> eq ==> eq) f).
    relational.
    rewrite H; reflexivity.
  assert (P.transpose_neqkey eq f).
    rewrite Heqf; intros ??????.
    destruct (P k e), (P k' e'); auto.
  assert (Proper (E.eq ==> eq ==> eq --> flip eq) f).
    unfold flip; relational.
    rewrite H1; reflexivity.
  assert (P.transpose_neqkey (flip eq) f).
    unfold flip; rewrite Heqf; intros ??????.
    destruct (P k e), (P k' e'); auto.
  split; intros.
    rewrite P.fold_Add with (k:=k) (e:=e) (m1:=m) in H4; eauto.
      rewrite Heqf in *.
      destruct (P k e); firstorder.
    constructor.
  rewrite P.fold_Add with (k:=k) (e:=e) (m1:=m); eauto.
    rewrite Heqf in *.
    destruct (P k e); firstorder.
  constructor.
Qed.

Lemma for_all_add_false : forall (m : M.t elt) k e,
  ~ M.In k m
    -> (P.for_all P (M.add k e m) = false
          <-> P.for_all P m = false \/ P k e = false).
Proof.
  unfold P.for_all.
  remember (fun _ _ _ => _) as f.
  assert (Proper (E.eq ==> eq ==> eq ==> eq) f).
    relational.
    rewrite H; reflexivity.
  assert (P.transpose_neqkey eq f).
    rewrite Heqf; intros ??????.
    destruct (P k e), (P k' e'); auto.
  assert (Proper (E.eq ==> eq ==> eq --> flip eq) f).
    unfold flip; relational.
    rewrite H1; reflexivity.
  assert (P.transpose_neqkey (flip eq) f).
    unfold flip; rewrite Heqf; intros ??????.
    destruct (P k e), (P k' e'); auto.
  split; intros.
    rewrite P.fold_Add with (k:=k) (e:=e) (m1:=m) in H4; eauto.
      rewrite Heqf in *.
      destruct (P k e); firstorder.
    constructor.
  rewrite P.fold_Add with (k:=k) (e:=e) (m1:=m); eauto.
    rewrite Heqf in *.
    destruct (P k e); firstorder.
    discriminate.
  constructor.
Qed.

Lemma for_all_add_iff : forall (m : M.t elt) k e b,
  ~ M.In k m
    -> P.for_all P (M.add k e m) = b
         <-> if b
             then P.for_all P m = true /\ P k e = true
             else P.for_all P m = false \/ P k e = false.
Proof.
  intros.
  destruct b.
    split; intros;
    eapply for_all_add_true; auto.
  split; intros;
  eapply for_all_add_false; auto.
Qed.

Lemma for_all_remove : forall (m : M.t elt) (k : M.key),
  P.for_all P m = true
    -> P.for_all P (M.remove k m) = true.
Proof.
  intros.
  apply P.for_all_iff; trivial; intros.
  apply F.remove_mapsto_iff in H0.
  eapply P.for_all_iff in H.
  - exact H.
  - exact P_Proper.
  - tauto.
Qed.

Lemma for_all_impl : forall (P' : M.key -> elt -> bool) m,
  P.for_all P m = true
    -> Proper (E.eq ==> eq ==> eq) P'
    -> (forall k e, P k e = true -> P' k e = true)
    -> P.for_all P' m = true.
Proof.
  intros.
  apply P.for_all_iff; trivial; intros.
  eapply P.for_all_iff in H; eauto.
Qed.

Lemma for_all_filter : forall P Q (m : M.t elt),
  Proper (E.eq ==> eq ==> eq) P ->
  Proper (E.eq ==> eq ==> eq) Q ->
  P.for_all (fun k e => negb (Q k e) || P k e) m = true
    -> P.for_all P (P.filter Q m) = true.
Proof.
  unfold P.for_all, P.filter; intros.
  remember (fun _ _ _ => _) as f.
  remember (fun _ _ _ => if P0 _ _ then _ else _) as g.
  remember (fun _ _ _ => if Q _ _ then _ else _) as h.

  assert (Proper (E.eq ==> eq ==> eq ==> eq) g).
    relational.
    rewrite H2.
    reflexivity.
  assert (P.transpose_neqkey eq g).
    intros ??????.
    rewrite Heqg.
    destruct (P0 k e), (P0 k' e'); auto.

  assert (Proper (E.eq ==> eq ==> M.Equal ==> M.Equal) h).
    relational.
    rewrite H4.
    destruct (Q y y0); trivial.
    rewrite H4, H6; reflexivity.
  assert (P.transpose_neqkey M.Equal h).
    intros ??????.
    rewrite Heqh.
    destruct (Q k e), (Q k' e'); try reflexivity.
    apply add_associative; intros.
    contradiction.

  pose proof (@fold_Proper _ _ g eq _ H2 H3).
  pose proof (@fold_Proper _ _ h M.Equal _ H4 H5).

  revert H1.
  apply P.fold_rec_bis; intros.
  - rewrite <- H1; intuition.
  - rewrite P.fold_Empty; auto.
    rewrite P.fold_Empty; auto;
    apply M.empty_1.
  - rewrite P.fold_add; auto.
    rewrite Heqg in *.
    rewrite Heqh in *.
    rewrite Heqf in *.
    destruct (Q k e) eqn:Heqe; simpl in *.
      rewrite P.fold_add; auto.
        destruct (P0 k e) eqn:Heqe2; simpl in *.
          rewrite (H9 H10); reflexivity.
        assumption.
      unfold not ;intros.
      destruct H11.
      contradiction H8.
      exists x.
      {
        destruct (P0 k e) eqn:Heqe2; simpl in *;
        revert H11;
        apply P.fold_rec_bis; auto; intros.
        - rewrite <- H11; intuition.
        - destruct (Q k0 e0) eqn:Heqe3; simpl in *.
            repeat simplify_maps.
          repeat simplify_maps.
          right; intuition.
          contradiction H12.
          exists x.
          rewrite H13.
          assumption.
        - rewrite <- H11; intuition.
        - destruct (Q k0 e0) eqn:Heqe3; simpl in *.
            repeat simplify_maps.
          repeat simplify_maps.
          right; intuition.
      }
    intuition.
Qed.

End for_all.

Import ListNotations.

Definition take_first {elt} (f : M.key -> elt -> bool) (k : M.key) (e : elt)
           (x0 : option (M.key * elt)) :=
  match x0 with
  | Some _ => x0
  | None => if f k e then Some (k, e) else None
  end.

Program Instance take_first_Proper {elt} :
  Proper ((E.eq ==> eq ==> eq)
            ==> E.eq
            ==> eq
            ==> optionP (pairP E.eq eq)
            ==> optionP (pairP E.eq eq)) (take_first (elt:=elt)).
Obligation 1.
  relational.
  destruct x2, y2.
  - destruct p, p0; simpl in *.
    assumption.
  - contradiction.
  - contradiction.
  - unfold take_first.
    rewrite (H _ _ H0 y1 y1 eq_refl).
    destruct (y y0 y1); auto.
    unfold optionP, pairP; auto.
Qed.

Corollary take_first_None
          {elt} (f : M.key -> elt -> bool) (k : M.key) (e : elt) x :
  take_first f k e (Some x) = Some x.
Proof. reflexivity. Qed.

Definition find_if {elt} (f : M.key -> elt -> bool) (m : M.t elt) :=
  M.fold (take_first f) m None.

Lemma find_if_empty : forall elt (P : M.key -> elt -> bool) m,
  M.Empty m -> find_if P m = None.
Proof.
  unfold find_if; intros.
  apply P.fold_rec; auto; intros.
  apply P.elements_Empty in H.
  apply F.find_mapsto_iff in H0.
  rewrite F.elements_o in H0.
  rewrite H in H0.
  inversion H0.
Qed.

Definition singleton {elt} (k : M.key) (e : elt) : M.t elt :=
  M.add k e (M.empty _).
Arguments singleton {elt} k e /.

Corollary MapsTo_singleton : forall k elt (e : elt),
  M.MapsTo k e (singleton k e).
Proof. unfold singleton; intros; simplify_maps. Qed.

Lemma filter_empty : forall elt (m : M.t elt) P,
  M.Empty (elt:=elt) m -> M.Empty (elt:=elt) (P.filter P m).
Proof.
  intros.
  unfold P.filter.
  revert H.
  apply P.fold_rec; intros.
    apply M.empty_1.
  specialize (H1 k).
  unfold P.Add in H1.
  rewrite F.elements_o in H1.
  apply P.elements_Empty in H3.
  rewrite H3 in H1; simpl in H1.
  rewrite F.add_eq_o in H1; [| apply E.eq_refl].
  discriminate.
Qed.

Lemma filter_for_all : forall elt (m : M.t elt) P,
  Proper (E.eq ==> eq ==> eq) P
    -> M.Equal (P.filter P m) m <-> P.for_all P m = true.
Proof.
  unfold P.for_all; split; intros.
    apply P.fold_rec; auto; intros.
    rewrite <- H0 in H1.
    apply P.filter_iff in H1; trivial.
    rewrite (proj2 H1); assumption.
  revert H0.
  apply P.fold_rec; auto; intros.
    apply F.Equal_mapsto_iff; split; intros; simplify_maps.
  destruct (P k e) eqn:Heqe; try discriminate.
  apply add_equal_iff in H2.
  rewrite <- H2 in *; clear H2.
  apply F.Equal_mapsto_iff; split; intros.
    simplify_maps.
  intuition.
  simplify_maps.
    simplify_maps.
    rewrite H3.
    rewrite H3 in Heqe.
    intuition.
  simplify_maps.
  rewrite <- H5 in H8.
  simplify_maps.
  intuition.
Qed.

Lemma filter_idempotent : forall elt (m : M.t elt) P,
  Proper (E.eq ==> eq ==> eq) P
    -> M.Equal (P.filter P (P.filter P m)) (P.filter P m).
Proof.
  intros.
  unfold P.filter.
  apply P.fold_rec; intros.
    intro k.
    apply P.elements_Empty in H0.
    symmetry; rewrite F.elements_o, H0.
    symmetry; rewrite F.elements_o, P.elements_empty.
    reflexivity.
  pose proof (P.filter_iff H).
  apply H4 in H0; clear H4.
  rewrite (proj2 H0).
  rewrite H3.
  unfold P.Add in H2.
  symmetry.
  exact H2.
Qed.

Lemma filter_for_all_2 : forall elt (m : M.t elt) P,
  Proper (E.eq ==> eq ==> eq) P -> P.for_all P (P.filter P m) = true.
Proof.
  intros.
  apply filter_for_all; eauto.
  unfold P.for_all.
  apply filter_idempotent; assumption.
Qed.

Lemma Oeq_neq_sym : forall x y, ~ E.eq x y -> ~ E.eq y x.
Proof.
  intros.
  unfold not; intros.
  apply E.eq_sym in H0.
  contradiction.
Qed.

Hint Resolve Oeq_neq_sym.

Lemma Proper_Oeq_negb : forall B f,
  Proper (E.eq ==> eq ==> eq) f ->
  Proper (E.eq ==> eq ==> eq) (fun (k : M.key) (e : B) => negb (f k e)).
Proof. intros ?????????; f_equal; subst; rewrite H0; reflexivity. Qed.

Hint Resolve Proper_Oeq_negb.

Lemma for_all_remove_false : forall elt k (m : M.t elt) P,
  Proper (E.eq ==> eq ==> eq) P
    -> (forall k' e', M.MapsTo k' e' m -> ~ E.eq k' k -> P k' e' = false)
    -> P.for_all (fun k e => negb (P k e)) (M.remove k m) = true.
Proof.
  intros.
  apply P.for_all_iff.
    relational.
    rewrite H1; reflexivity.
  intros.
  simplify_maps.
  apply Oeq_neq_sym in H2.
  specialize (H0 _ _ H3 H2).
  rewrite H0.
  reflexivity.
Qed.

Lemma filter_singleton_inv : forall elt k (e : elt) m P,
  Proper (E.eq ==> eq ==> eq) P
    -> M.Equal (P.filter P m) (singleton k e)
    -> M.MapsTo k e m
         /\ P k e = true
         /\ (P.for_all (fun k e => negb (P k e))
                       (M.remove k m) = true).
Proof.
  intros.
  split.
    unfold singleton in H0.
    symmetry in H0.
    apply add_equal_iff in H0.
    specialize (H0 k).
    rewrite F.add_eq_o in H0; auto.
    simplify_maps.
  split.
    unfold singleton in H0.
    specialize (H0 k).
    rewrite F.add_eq_o in H0; auto.
    simplify_maps.
  intros.
  unfold singleton in H0.
  apply for_all_remove_false; intros; auto.
  specialize (H0 k').
  rewrite F.add_neq_o, F.empty_o in H0; auto.
  unfold P.filter in H0.
  induction m using P.map_induction.
    simplify_maps.
  remember (fun _ _ _ => _) as f.
  assert (Proper (E.eq ==> eq ==> M.Equal ==> M.Equal) f).
    relational.
    rewrite H5.
    destruct (P y y0); trivial.
    rewrite H5, H7.
    reflexivity.
  assert (P.transpose_neqkey M.Equal f).
    rewrite Heqf; intros ??????.
    destruct (P k0 e1), (P k'0 e'0); try reflexivity.
    apply add_associative; intros.
    contradiction.
  pose proof (@fold_Proper elt _ f M.Equal (F.EqualSetoid _) H5 H6) as H7.
  apply add_equal_iff in H4.
  rewrite <- H4 in *; clear H4 m2.
  simplify_maps.
    rewrite H4 in *; clear H4.
    rewrite P.fold_Add with (k:=k') (e:=e') (m1:=m1) in H0; eauto;
    [|constructor].
    destruct (P k' e').
      rewrite F.add_eq_o in H0; auto.
      discriminate.
    reflexivity.
  rewrite P.fold_Add with (k:=x) (e:=e0) (m1:=m1) in H0; eauto;
  [|constructor].
  rewrite Heqf in *; clear Heqf H5 H6 H7.
  destruct (P x e0).
    rewrite F.add_neq_o in H0; auto.
  intuition.
Qed.

Lemma add_remove : forall elt k e m,
  ~ M.In k m -> M.Equal (M.remove (elt:=elt) k (M.add k e m)) m.
Proof.
  intros.
  apply F.Equal_mapsto_iff; split; intros.
    apply F.remove_mapsto_iff in H0.
    destruct H0.
    simplify_maps.
    contradiction.
  apply F.not_find_in_iff in H.
  apply F.find_mapsto_iff in H0.
  destruct (E.eq_dec k k0).
    rewrite e1 in H.
    rewrite H in H0.
    discriminate.
  apply F.find_mapsto_iff in H0.
  simplify_maps.
  split; trivial.
  simplify_maps.
Qed.

Lemma filter_add_true : forall elt k (e : elt) m m' P,
  Proper (E.eq ==> eq ==> eq) P
    -> ~ M.In (elt:=elt) k m
    -> M.Equal (P.filter P (M.add k e m)) m'
    -> P k e = true
    -> M.Equal (M.add k e (P.filter P m)) m'.
Proof.
  intros.
  rewrite <- H1; clear H1.
  apply F.Equal_mapsto_iff; split; intros.
    simplify_maps.
      rewrite <- H3.
      simplify_maps; intuition.
      simplify_maps.
    simplify_maps; intuition.
  simplify_maps.
  simplify_maps.
    rewrite H1.
    simplify_maps.
  simplify_maps.
  right; intuition.
  simplify_maps.
Qed.

Lemma filter_add_false : forall elt k (e : elt) m m' P,
  Proper (E.eq ==> eq ==> eq) P
    -> ~ M.In (elt:=elt) k m
    -> M.Equal (P.filter P (M.add k e m)) m'
    -> P k e = false
    -> M.Equal (P.filter P m) m'.
Proof.
  intros.
  rewrite <- H1; clear H1.
  apply F.Equal_mapsto_iff; split; intros.
    simplify_maps.
    simplify_maps; intuition.
    simplify_maps.
    right; intuition.
    rewrite <- H1 in H3.
    contradiction H0.
    apply in_mapsto_iff.
    exists e0; assumption.
  simplify_maps.
  simplify_maps.
    rewrite H1 in H2.
    congruence.
  simplify_maps.
Qed.

Lemma filter_not_in : forall elt k (m : M.t elt) P,
  ~ M.In (elt:=elt) k m -> ~ M.In (elt:=elt) k (P.filter P m).
Proof.
  intros.
  unfold P.filter.
  apply P.fold_rec_nodep; intros.
    unfold not; intros.
    apply F.empty_in_iff in H0.
    contradiction.
  destruct (P k0 e); auto.
  unfold not; intros.
  apply F.add_in_iff in H2; intuition.
  rewrite H3 in *; clear H3.
  apply H.
  apply in_mapsto_iff.
  exists e.
  assumption.
Qed.

Lemma find_if_filter : forall elt (m m' : M.t elt) P,
  Proper (E.eq ==> eq ==> eq) P
    -> M.Equal (P.filter P m) m'
    -> match find_if P m with
       | Some (k, e) => M.MapsTo k e m'
       | None => M.Empty m'
       end.
Proof.
  unfold find_if; intros.
  revert H0.
  revert m'.
  apply P.fold_rec_weak; intros.
  - rewrite <- H0 in H2; intuition.
    apply H1; intuition.
  - rewrite <- H0.
    apply filter_empty.
    apply M.empty_1.
  - unfold take_first.
    destruct (P k e) eqn:Heqe.
      apply filter_add_true in H2; auto.
      destruct a.
        destruct p.
        apply Equal_add_remove in H2.
          specialize (H1 _ H2).
          simplify_maps.
        apply filter_not_in.
        assumption.
      rewrite <- H2.
      simplify_maps.
    apply filter_add_false in H2; auto.
    destruct a; intuition.
    destruct p; intuition.
Qed.

Lemma Empty_add : forall elt k (e : elt) m,
  ~ M.In k m -> ~ M.Empty (M.add k e m).
Proof.
  unfold not; intros.
  apply P.cardinal_Empty in H0.
  rewrite P.cardinal_fold in H0.
  rewrite P.fold_Add with (k:=k) (e:=e) (m1:=m) in H0; auto.
  - discriminate.
  - congruence.
  - congruence.
  - constructor.
Qed.

Lemma find_if_filter_is_singleton : forall elt k (e : elt) m P,
  Proper (E.eq ==> eq ==> eq) P
    -> M.Equal (P.filter P m) (singleton k e)
    -> optionP (pairP E.eq eq) (find_if P m) (Some (k, e)).
Proof.
  simpl; intros.
  apply find_if_filter in H0; trivial.
  destruct (find_if P m).
    destruct p.
    simplify_maps.
  assert (~ M.In k (M.empty elt)).
    unfold not; intros.
    apply F.empty_in_iff in H1.
    contradiction.
  contradiction (Empty_add _ k _ (M.empty elt) H1 H0).
Qed.

Lemma find_if_inv : forall elt p (m : M.t elt) P,
  Proper (E.eq ==> eq ==> eq) P
    -> find_if P m = Some p
    -> M.MapsTo (fst p) (snd p) m /\ P (fst p) (snd p) = true.
Proof.
  unfold find_if, take_first; intros.
  destruct p; simpl.
  revert H0.
  apply P.fold_rec; intros.
    discriminate.
  apply add_equal_iff in H2.
  rewrite <- H2; clear H2.
  destruct a, (P k0 e0) eqn:Heqe;
  try destruct p; simpl in *;
  try inversion H4; subst; clear H4;
  intuition;
  simplify_maps;
  right; intuition;
  apply F.not_find_in_iff in H1;
  rewrite <- H2 in H3;
  apply F.find_mapsto_iff in H3;
  congruence.
Qed.

Ltac for_this :=
  match goal with
  | [ H1 : P.for_all ?P ?r = true,
      H2 : M.MapsTo (elt:=_) ?addr ?cblk ?r |- _ ] =>
    apply (proj1 (P.for_all_iff _ _)) with (k:=addr) (e:=cblk) in H1;
    auto; [|exact H2]
  | [ H1 : is_true (P.for_all ?P ?r),
      H2 : M.MapsTo (elt:=_) ?addr ?cblk ?r |- _ ] =>
    apply (proj1 (P.for_all_iff _ _)) with (k:=addr) (e:=cblk) in H1;
    auto; [|exact H2]
  end.

End FMapExt.
