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
    (forall blk,
       Lookup addr blk or
         -> (exists cblk, M.find addr nr = Some cblk /\ AbsR blk cblk)) /\
    (forall cblk,
       M.find addr nr = Some cblk
         -> (exists blk, Lookup addr blk or /\ AbsR blk cblk)).

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
    destruct (HA _ H2) as [cblk [HC HD]]; clear HA HB H2;
    exists cblk
  | [ H1 : SetMap_AbsR _ _ _,
      H2 : M.find ?A ?K = Some ?D |- _ ] =>
    let HA := fresh "HA" in
    let HB := fresh "HB" in
    destruct (H1 A) as [HA HB]; clear H1;
    let HC := fresh "HC" in
    let HD := fresh "HD" in
    destruct (HB _ H2) as [blk [HC HD]]; clear HA HB H2;
    exists blk
  end.

Section FunMaps_AbsR.

Variables A B : Type.
Variable R  : A -> B -> Prop.
Variable or : FunRel M.key A.
Variable nr : M.t B.
Variable H  : SetMap_AbsR or nr R.

Hypothesis Oeq_eq : forall a b, O.eq a b -> a = b.

Lemma Find_find_if P P' a b b' :
  (forall i a b, R a b -> P i a <-> is_true (P' i b))
    -> (forall a b c, R a b -> R a c -> b = c)
    -> (forall (a b : M.key) (x y : B),
          is_true (P' a x) -> ~ M.E.eq a b -> P' b y = false)
    -> R b b'
    -> Find P a b or
    -> find_if P' nr = Some (a, b').
Proof.
  intros.
  destruct H4.
  eapply H0 in H5; eauto; clear H0.
  destruct (H a) as [H0 _]; clear H.
  destruct (H0 _ H4) as [b'' [H H6]]; clear H4 H0.
  unfold find_if.
  rewrite F.elements_o in H.
  rewrite M.fold_1.
  induction (M.elements nr).
    discriminate.
  rewrite fold_Some_cons; auto.
  destruct a0; simpl in *.
  unfold F.eqb in H.
  destruct (F.eq_dec a k).
    pose proof (H1 _ _ _ H3 H6); subst.
    clear H1 H2 H3 H6 IHl.
    inversion H; clear H.
    unfold M.E.eq in e.
    apply Oeq_eq in e; subst.
    rewrite H5.
    reflexivity.
  rewrite (IHl H), (H2 _ _ _ _ H5 n).
  reflexivity.
Qed.

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
    destruct (H1 _ H2) as [cblk [? ?]]; clear H1 H2.
    apply F.find_mapsto_iff in H.
    exists (f' addr cblk).
    split.
      rewrite F.mapi_o, <- F.map_o.
        apply F.find_mapsto_iff.
        apply F.map_mapsto_iff.
        exists cblk; tauto.
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
    destruct (H3 _ H2) as [blk [? ?]]; clear H2 H3.
    exists (f (addr, blk)).
    split.
      apply Lookup_Map; trivial.
    apply H0; trivial.
  intros.
  apply Oeq_eq in H2.
  subst; reflexivity.
Qed.

End FunMaps_AbsR.

End FunMaps.
