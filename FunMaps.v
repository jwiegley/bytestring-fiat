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

Section FunMaps_AbsR.

Variables A B : Type.
Variable R    : A -> B -> Prop.
Variable or   : FunRel M.key A.
Variable nr   : M.t B.
Variable H    : SetMap_AbsR or nr R.

Hypothesis Oeq_eq : forall a b, O.eq a b -> a = b.

Lemma Update_SetMap_AbsR : forall k v v',
  R v v' -> SetMap_AbsR (Update k v or) (M.add k v' nr) R.
Proof.
  split; intros.
    teardown; subst.
      exists v'.
      split; trivial.
      apply F.find_mapsto_iff, F.add_mapsto_iff.
      left; auto.
    destruct (H addr); clear H H4.
    destruct (H3 _ H2); clear H2 H3.
    exists x.
    intuition.
    apply F.find_mapsto_iff in H2.
    apply F.find_mapsto_iff, F.add_mapsto_iff.
    right; split; auto.
  apply F.find_mapsto_iff, F.add_mapsto_iff in H1.
  destruct H1; destruct H1; subst.
    exists v.
    split; trivial.
    apply Oeq_eq in H1; subst.
    right; constructor.
  destruct (H addr); clear H H3.
  apply F.find_mapsto_iff in H2.
  destruct (H4 _ H2); clear H2 H4.
  exists x.
  intuition.
  left; constructor; auto.
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
