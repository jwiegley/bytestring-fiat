Require Import
  Here.FunRelation
  Here.FMapExt
  Here.Nomega
  Coq.FSets.FMapAVL
  Coq.FSets.FMapFacts
  Coq.Structures.OrderedTypeEx.

Module FunMaps (O : OrderedType).

Module E := FMapExt(O).
Include E.

Definition SetMap_AbsR {A B}
           (or : FunRel M.key A) (nr : M.t B)
           (AbsR : A -> B -> Prop) : Prop :=
  forall addr,
    (forall data,
       Lookup addr data or
         -> (exists cdata, M.find addr nr = Some cdata /\ AbsR data cdata)) /\
    (forall cdata,
       M.find addr nr = Some cdata
         -> (exists data, Lookup addr data or /\ AbsR data cdata)).

Lemma Empty_SetMap_AbsR : forall A B R,
  SetMap_AbsR (Empty M.key A) (M.empty B) R.
Proof.
  split; intros.
    inversion H.
  apply F.find_mapsto_iff, F.empty_mapsto_iff in H.
  contradiction.
Qed.

Ltac reduction :=
  teardown; subst;
  try match goal with
  | [ H1 : SetMap_AbsR _ _ _,
      H2 : Lookup ?A ?D ?K |- _ ] =>
    let HA := fresh "HA" in
    let HB := fresh "HB" in
    destruct (H1 A) as [HA HB]; clear H1;
    let HC := fresh "HC" in
    let HD := fresh "HD" in
    destruct (HA _ H2) as [cdata [HC HD]]; clear HA HB H2;
    exists cdata
  | [ H1 : SetMap_AbsR _ _ _,
      H2 : M.find ?A ?K = Some ?D |- _ ] =>
    let HA := fresh "HA" in
    let HB := fresh "HB" in
    destruct (H1 A) as [HA HB]; clear H1;
    let HC := fresh "HC" in
    let HD := fresh "HD" in
    destruct (HB _ H2) as [data [HC HD]]; clear HA HB H2;
    exists data
  end.

Section FunMaps_AbsR.

Variables A B : Type.
Variable R    : A -> B -> Prop.
Variable or   : FunRel M.key A.
Variable nr   : M.t B.
Variable H    : SetMap_AbsR or nr R.

Hypothesis Oeq_eq : forall a b, O.eq a b -> a = b.

Lemma Find_find_if P P' a b b' :
  (forall i a b, R a b -> P i a <-> is_true (P' i b))
    -> R b b'
    -> Find P a b or <-> find_if P' nr = Some (a, b').
Proof.
  split; intros.
    destruct H2.
    eapply H0 in H3; eauto.
    destruct (H a); clear H H5.
    destruct (H4 _ H2); clear H2 H4.
    destruct H; clear H.
    unfold find_if.
Abort.

Lemma Update_SetMap_AbsR : forall k v v',
  R v v' -> SetMap_AbsR (Update k v or) (M.add k v' nr) R.
Proof.
  split; intros.
    reduction.
      exists v'.
      split; trivial.
      apply F.find_mapsto_iff, F.add_mapsto_iff.
      left; auto.
    intuition.
    apply F.find_mapsto_iff in HC.
    apply F.find_mapsto_iff, F.add_mapsto_iff.
    right; split; auto.
  apply F.find_mapsto_iff, F.add_mapsto_iff in H1.
  destruct H1; destruct H1; subst.
    exists v.
    split; trivial.
    apply Oeq_eq in H1; subst.
    right; constructor.
  apply F.find_mapsto_iff in H2.
  reduction; intuition.
  left; constructor; auto.
  unfold Ensembles.In; simpl.
  unfold not; intros.
  subst; auto.
Qed.

Lemma Remove_SetMap_AbsR : forall k,
  SetMap_AbsR (Remove k or) (M.remove k nr) R.
Proof.
  split; intros.
    reduction.
    intuition.
    apply F.find_mapsto_iff, F.remove_mapsto_iff.
    split; auto.
    apply F.find_mapsto_iff.
    assumption.
  apply F.find_mapsto_iff, F.remove_mapsto_iff in H0.
  destruct H0.
  apply F.find_mapsto_iff in H1.
  reduction.
  intuition.
  constructor; trivial.
  unfold Ensembles.In; simpl.
  unfold not; intros.
  subst; auto.
Qed.

Lemma Map_SetMap_AbsR : forall f f',
  (forall i a b, R a b -> R (f (i, a)) (f' i b))
    -> SetMap_AbsR (Map f or) (M.mapi f' nr) R.
Proof.
  split; intros.
    teardown; subst.
    destruct (H addr); clear H H3.
    destruct (H1 _ H2) as [cdata [? ?]]; clear H1 H2.
    apply F.find_mapsto_iff in H.
    exists (f' addr cdata).
    split.
      rewrite F.mapi_o, <- F.map_o.
        apply F.find_mapsto_iff.
        apply F.map_mapsto_iff.
        exists cdata; tauto.
      intros.
      apply Oeq_eq in H1.
      subst; reflexivity.
    apply H0; trivial.
  rewrite F.mapi_o, <- F.map_o in H1.
    apply F.find_mapsto_iff in H1.
    apply F.map_mapsto_iff in H1.
    destruct H1; destruct H1; subst.
    apply F.find_mapsto_iff in H2.
    destruct (H addr); clear H H1.
    destruct (H3 _ H2) as [data [? ?]]; clear H2 H3.
    exists (f (addr, data)).
    split.
      apply Lookup_Map; trivial.
    apply H0; trivial.
  intros.
  apply Oeq_eq in H2.
  subst; reflexivity.
Qed.

End FunMaps_AbsR.

End FunMaps.
