Require Import
  Here.FunRelation
  Here.FMapExt
  Here.Nomega
  Coq.FSets.FMapList
  Coq.FSets.FMapFacts
  Coq.Structures.OrderedTypeEx.

Module FunMaps (O : OrderedType).

Module E := FMapExt(O).
Include E.

Program Definition to_rel {A} (m : M.t A) : FunRel M.key A :=
  M.fold (fun k e r => Insert k e r _) m (Empty M.key A).
Obligation 1.
Admitted.

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
    let cblk := fresh "cblk" in
    destruct (HA _ H2) as [cblk [HC HD]]; clear HA HB H2
  | [ H1 : SetMap_AbsR _ _ _,
      H2 : In _ (relEns ?K) (?A, ?D) |- _ ] =>
    let HA := fresh "HA" in
    let HB := fresh "HB" in
    destruct (H1 A) as [HA HB]; clear H1;
    let HC := fresh "HC" in
    let HD := fresh "HD" in
    let cblk := fresh "cblk" in
    destruct (HA _ H2) as [cblk [HC HD]]; clear HA HB H2
  | [ H1 : SetMap_AbsR _ _ _,
      H2 : M.find ?A ?K = Some ?D |- _ ] =>
    let HA := fresh "HA" in
    let HB := fresh "HB" in
    destruct (H1 A) as [HA HB]; clear H1;
    let HC := fresh "HC" in
    let HD := fresh "HD" in
    let blk := fresh "blk" in
    destruct (HB _ H2) as [blk [HC HD]]; clear HA HB H2
  end.

Section FunMaps_AbsR.

Variables A B : Type.
Variable R  : A -> B -> Prop.
Variable or : FunRel M.key A.
Variable nr : M.t B.
Variable H  : SetMap_AbsR or nr R.

Lemma SetMap_AbsR_prj1 : forall (addr : M.key) (blk : A) cblk,
  Ensembles.In _ (relEns or) (addr, blk)
    -> (forall a b c, R a b -> R a c -> b = c)
    -> R blk cblk
    -> M.find (elt:=B) addr nr = Some cblk.
Proof.
  intros.
  destruct (H addr); clear H.
  destruct (H3 _ H0) as [cblk' [? ?]]; clear H0 H3.
  rewrite (H1 _ _ _ H2 H5); assumption.
Qed.

Lemma SetMap_AbsR_prj1_ex : forall (addr : M.key) (blk : A),
  Ensembles.In _ (relEns or) (addr, blk)
    -> exists cblk : B,
         M.find (elt:=B) addr nr = Some cblk /\ R blk cblk.
Proof.
  intros.
  destruct (H addr); clear H.
  destruct (H1 _ H0) as [cblk [? ?]]; clear H0 H1.
  exists cblk; auto.
Qed.

Lemma SetMap_AbsR_prj2_ex : forall (addr : M.key) (cblk : B),
  M.find (elt:=B) addr nr = Some cblk
    -> exists blk : A, Lookup addr blk or /\ R blk cblk.
Proof.
  intros.
  destruct (H addr); clear H.
  destruct (H2 _ H0) as [blk [? ?]]; clear H0 H2.
  exists blk; auto.
Qed.

Hypothesis Oeq_eq : forall a b, O.eq a b -> a = b.

Lemma Update_SetMap_AbsR : forall k v v',
  R v v' -> SetMap_AbsR (Update k v or) (M.add k v' nr) R.
Proof.
  split; intros.
    reduction.
      exists v'.
      split; trivial.
      apply F.find_mapsto_iff, F.add_mapsto_iff.
      left; auto.
    exists cblk.
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
  reduction; exists blk.
  intuition.
  left; constructor; auto.
  unfold Ensembles.In; simpl.
  unfold not; intros.
  subst; auto.
Qed.

Lemma Remove_SetMap_AbsR : forall k,
  SetMap_AbsR (Remove k or) (M.remove k nr) R.
Proof.
  split; intros.
    reduction; exists cblk.
    intuition.
    apply F.find_mapsto_iff, F.remove_mapsto_iff.
    split; auto.
    apply F.find_mapsto_iff.
    assumption.
  apply F.find_mapsto_iff, F.remove_mapsto_iff in H0.
  destruct H0.
  apply F.find_mapsto_iff in H1.
  reduction; exists blk.
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

Lemma Proper_Oeq_negb : forall f,
  Proper (O.eq ==> eq ==> eq) f ->
  Proper (O.eq ==> eq ==> eq) (fun (k : M.key) (e : B) => negb (f k e)).
Proof.
  intros.
  intros x y H1 x' y' H2. subst.
  apply Oeq_eq in H1; subst.
  reflexivity.
Qed.

Lemma Partition_SetMap_AbsR
      (f : M.key -> A -> Prop)
      (f' : M.key -> B -> bool)
      (f'_Proper : Proper (O.eq ==> eq ==> eq) f')  :
  (forall a b, R a b -> forall i, Bool.reflect (f i a) (f' i b))
    -> forall a a', Partition f or = (a, a')
    -> forall b b', P.partition f' nr = (b, b')
    -> SetMap_AbsR a b R /\ SetMap_AbsR a' b' R.
Proof.
  split; intros; split; intros.
  - unfold Partition in H0.
    unfold P.partition in H1.
    inversion H0; subst; clear H0;
    inversion H1; subst; clear H1;
    simpl in H2; destruct H2.
    destruct (H addr) as [H3 _].
    destruct (H3 _ H1) as [cblk [? ?]]; clear H1 H3.
    exists cblk; intuition.
    apply F.find_mapsto_iff.
    apply F.find_mapsto_iff in H2.
    apply P.filter_iff; intuition.
    destruct (X _ _ H4 addr); intuition.
Admitted.
(*
  - destruct (H addr); clear H H1.
    apply F.find_mapsto_iff in H0.
    apply P.filter_iff in H0; trivial.
    destruct H0.
    apply F.find_mapsto_iff in H.
    destruct (H2 _ H) as [blk [? ?]]; clear H H2.
    exists blk; intuition.
    split; intuition.
    destruct (X _ _ H3 addr); intuition.
  - destruct (H addr); clear H H2.
    destruct H0.
    destruct (H1 _ H0) as [cblk [? ?]]; clear H0 H1.
    exists cblk; intuition.
    apply F.find_mapsto_iff.
    apply F.find_mapsto_iff in H2.
    apply P.filter_iff; intuition.
    apply Proper_Oeq_negb; assumption.
    apply negb_true_iff.
    destruct (X _ _ H3 addr); intuition.
  - destruct (H addr); clear H H1.
    apply F.find_mapsto_iff in H0.
    apply P.filter_iff in H0; trivial.
    destruct H0.
    apply negb_true_iff in H0.
    apply F.find_mapsto_iff in H.
    destruct (H2 _ H) as [blk [? ?]]; clear H H2.
    exists blk; intuition.
    split; intuition.
      destruct (X _ _ H3 addr); intuition.
    apply Proper_Oeq_negb; assumption.
Qed.
*)

Lemma Same_set_SetMap_AbsR : forall a b r HF,
  Same_set _ (relEns a) b
    -> SetMap_AbsR a r R
    -> SetMap_AbsR (mkFunRel b HF) r R.
Proof.
  intros.
  intros addr.
  destruct (H1 addr); clear H1.
  split; intros.
    unfold Lookup in H1.
    unfold Same_set, Included in H0.
    destruct H0.
    apply H4 in H1.
    destruct (H2 _ H1) as [cblk [? ?]].
    exists cblk.
    intuition.
  destruct (H3 _ H1) as [blk [? ?]].
  exists blk.
  unfold Same_set, Included in H0.
  destruct H0.
  apply H0 in H4.
  intuition.
Qed.

Lemma foo : forall A x y (z : A),
  (x = Some z <-> y = Some z)
    -> (x = None <-> y = None)
    -> x = y.
Proof.
Admitted.

Lemma Equal_SetMap_AbsR : forall a b b',
  SetMap_AbsR a b R
    -> SetMap_AbsR a b' R
    -> M.Equal b b'.
Proof.
  intros.
  intro addr.
  destruct (H0 addr), (H1 addr).
  destruct (M.find (elt:=B) addr b').
  apply foo with (z:=b0); split; intros; trivial.
Abort.

Lemma Single_SetMap_AbsR : forall base blk cblk,
  R blk cblk -> SetMap_AbsR (Single base blk) (singleton base cblk) R.
Proof.
  intros.
  intro addr.
  split; intros;
  [exists cblk|exists blk].
    inversion H1; subst.
    split; trivial.
    unfold singleton.
    rewrite F.elements_o; simpl.
    rewrite eqb_refl.
    reflexivity.
  rewrite F.elements_o in H1; simpl in H1.
  unfold F.eqb in H1.
  destruct (O.eq_dec addr base).
    inversion H1.
    apply Oeq_eq in e.
    subst.
    split; trivial.
    apply Lookup_Single.
  discriminate.
Qed.

End FunMaps_AbsR.

End FunMaps.
