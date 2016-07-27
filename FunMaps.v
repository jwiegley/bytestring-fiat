Require Import
  Here.FMapExt
  Here.Nomega
  Coq.Sets.Ensembles
  Here.TupleEnsembles
  Coq.FSets.FMapList
  Coq.FSets.FMapFacts
  Coq.Structures.OrderedTypeEx.

Module FunMaps (O : OrderedType).

Module E := FMapExt(O).
Include E.

Definition SetMap_AbsR
           (A B : Type) (R  : A -> B -> Prop)
           (or : Ensemble (M.key * A))
           (nr : M.t B) : Prop :=
  forall addr,
    (forall blk,
       Lookup addr blk or
         -> (exists cblk, M.find addr nr = Some cblk /\ R blk cblk)) /\
    (forall cblk,
       M.find addr nr = Some cblk
         -> (exists blk, Lookup addr blk or /\ R blk cblk)).

Ltac reduction :=
  try repeat teardown; subst;
  match goal with
  | [ _ : ?T -> ?U -> Prop,
      H1 : SetMap_AbsR _ _ _,
      H2 : Lookup ?A ?D ?K |- exists _ : ?U, _ ] =>
    let HA := fresh "HA" in
    destruct (H1 A) as [HA _];
    let HC := fresh "HC" in
    let HD := fresh "HC" in
    let cblk := fresh "cblk" in
    destruct (HA _ H2) as [cblk [HC HD]]; clear HA H2;
    exists cblk; split; trivial
  | [ H1 : SetMap_AbsR _ _ _,
      H2 : Lookup ?A ?D ?K |- _ ] =>
    let HA := fresh "HA" in
    let HB := fresh "HB" in
    destruct (H1 A) as [HA HB];
    let HC := fresh "HC" in
    let HD := fresh "HD" in
    let cblk := fresh "cblk" in
    destruct (HA _ H2) as [cblk [HC HD]]; clear HA HB H2
  | [ _ : ?T -> ?U -> Prop,
      H1 : SetMap_AbsR _ _ _,
      H2 : M.find ?A ?K = Some ?D |- exists _ : ?T, _ ] =>
    let HB := fresh "HB" in
    destruct (H1 A) as [_ HB];
    let HC := fresh "HC" in
    let HD := fresh "HD" in
    let blk := fresh "blk" in
    destruct (HB _ H2) as [blk [HC HD]]; clear HB H2;
    exists blk; split; trivial
  | [ H1 : SetMap_AbsR _ _ _,
      H2 : M.find ?A ?K = Some ?D |- _ ] =>
    let HA := fresh "HA" in
    let HB := fresh "HB" in
    destruct (H1 A) as [HA HB];
    let HC := fresh "HC" in
    let HD := fresh "HD" in
    let blk := fresh "blk" in
    destruct (HB _ H2) as [blk [HC HD]]; clear HA HB H2
  end.

Section FunMaps_AbsR.

Variables A B : Type.
Variable R  : A -> B -> Prop.
Variable or : Ensemble (M.key * A).
Variable nr : M.t B.
Variable AbsR : SetMap_AbsR R or nr.

Lemma Empty_SetMap_AbsR : SetMap_AbsR R Empty (M.empty B).
Proof.
  split; intros.
    inversion H.
  apply F.find_mapsto_iff, F.empty_mapsto_iff in H.
  contradiction.
Qed.

Corollary SetMap_AbsR_prj1 : forall (addr : M.key) (blk : A) cblk,
  Lookup addr blk or
    -> (forall a b c, R a b -> R a c -> b = c)
    -> R blk cblk
    -> M.find (elt:=B) addr nr = Some cblk.
Proof. intros; reduction; rewrite (H0 _ _ _ H1 HD); assumption. Qed.

Corollary SetMap_AbsR_prj1_ex : forall (addr : M.key) (blk : A),
  Lookup addr blk or
    -> exists cblk : B,
         M.find (elt:=B) addr nr = Some cblk /\ R blk cblk.
Proof. intros; reduction. Qed.

Corollary SetMap_AbsR_prj2_ex : forall (addr : M.key) (cblk : B),
  M.find (elt:=B) addr nr = Some cblk
    -> exists blk : A, Lookup addr blk or /\ R blk cblk.
Proof. intros. reduction. Qed.

Hypothesis Oeq_eq : forall a b, O.eq a b -> a = b.

Lemma Update_SetMap_AbsR : forall k v v',
  R v v' -> SetMap_AbsR R (Update k v or) (M.add k v' nr).
Proof.
  split; intros.
  - repeat teardown; subst.
    + exists v'; split; trivial.
      apply F.find_mapsto_iff, F.add_mapsto_iff.
      left; auto.
    + reduction.
      apply F.find_mapsto_iff in HC.
      apply F.find_mapsto_iff, F.add_mapsto_iff.
      right; split; auto.
  - apply F.find_mapsto_iff, F.add_mapsto_iff in H0.
    destruct H0, H0; subst.
      exists v; split; trivial.
      apply Oeq_eq in H0; subst.
      right; constructor.
    apply F.find_mapsto_iff in H1.
    reduction.
    left; constructor; auto.
    unfold Ensembles.In; simpl.
    unfold not; intros.
    subst; auto.
Qed.

Lemma Remove_SetMap_AbsR : forall k,
  SetMap_AbsR R (Remove k or) (M.remove k nr).
Proof.
  split; intros.
    reduction.
    apply F.find_mapsto_iff, F.remove_mapsto_iff.
    split; auto.
    apply F.find_mapsto_iff.
    assumption.
  apply F.find_mapsto_iff, F.remove_mapsto_iff in H.
  destruct H.
  apply F.find_mapsto_iff in H0.
  reduction.
  constructor; trivial.
  unfold Ensembles.In; simpl.
  unfold not; intros.
  subst; auto.
Qed.

Lemma Map_SetMap_AbsR : forall f f',
  (forall i a b, R a b -> R (f i a) (f' i b))
    -> SetMap_AbsR R (Map f or) (M.mapi f' nr).
Proof.
  split; intros.
    repeat teardown; subst.
    destruct (AbsR addr); clear H2.
    destruct (H0 _ H1) as [cblk [? ?]]; clear H0 H1.
    exists (f' addr cblk).
    apply F.find_mapsto_iff in H2.
    split.
      rewrite F.mapi_o, <- F.map_o.
        apply F.find_mapsto_iff.
        apply F.map_mapsto_iff.
        exists cblk; tauto.
      intros.
      apply Oeq_eq in H0.
      subst; reflexivity.
    apply H; trivial.
  rewrite F.mapi_o, <- F.map_o in H0.
    apply F.find_mapsto_iff in H0.
    apply F.map_mapsto_iff in H0.
    repeat teardown; subst.
    apply F.find_mapsto_iff in H1.
    destruct (AbsR addr); clear H0.
    destruct (H2 _ H1) as [blk [? ?]]; clear H1 H2.
    exists (f addr blk).
    split.
      teardown.
    apply H; trivial.
  intros.
  apply Oeq_eq in H1.
  subst; reflexivity.
Qed.

Lemma Proper_Oeq_negb : forall f,
  Proper (O.eq ==> eq ==> eq) f ->
  Proper (O.eq ==> eq ==> eq) (fun (k : M.key) (e : B) => negb (f k e)).
Proof.
  intros.
  intros x y H1 x' y' H2. subst.
  apply Oeq_eq in H1; subst.
  reflexivity.
Qed.

Lemma Single_SetMap_AbsR : forall base blk cblk,
  R blk cblk -> SetMap_AbsR R (Single base blk) (singleton base cblk).
Proof.
  intros.
  intro addr.
  split; intros;
  [exists cblk|exists blk].
    repeat teardown; subst.
    split; trivial.
    unfold P.uncurry.
    rewrite F.elements_o; simpl.
    rewrite eqb_refl.
    reflexivity.
  rewrite F.elements_o in H0; simpl in H0.
  unfold F.eqb in H0.
  destruct (O.eq_dec addr base).
    inversion H0.
    apply Oeq_eq in e.
    subst.
    split; trivial.
    apply Lookup_Single.
  discriminate.
Qed.

End FunMaps_AbsR.

Lemma Same_set_SetMap_AbsR : forall A B (R : A -> B -> Prop) a b r,
  Same a b
    -> SetMap_AbsR R a r
    -> SetMap_AbsR R b r.
Proof.
  intros.
  intros addr.
  destruct (H0 addr).
  split; intros.
    apply H in H3.
    destruct (H1 _ H3) as [cblk [? ?]].
    exists cblk.
    intuition.
  destruct (H2 _ H3) as [blk [? ?]].
  exists blk.
  split; trivial.
  apply H; trivial.
Qed.

Lemma Equal_SetMap_AbsR : forall A B (R : A -> B -> Prop) a b r,
  M.Equal a b
    -> SetMap_AbsR R r a
    -> SetMap_AbsR R r b.
Proof.
  intros.
  intros addr.
  destruct (H0 addr).
  split; intros.
    destruct (H1 _ H3) as [cblk [? ?]].
    exists cblk.
    split; trivial.
    rewrite <- H; trivial.
  rewrite <- H in H3.
  destruct (H2 _ H3) as [blk [? ?]].
  exists blk.
  intuition.
Qed.

End FunMaps.
