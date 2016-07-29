Require Export
  Here.TupleEnsembles
  Coq.Sets.Finite_sets
  Coq.Sets.Finite_sets_facts.

Require Import
  Coq.Program.Tactics.

Generalizable All Variables.

Section TupleEnsembleFinite.

Variable A : Type.
Variable B : Type.

Lemma Empty_Finite : Finite _ (@Empty A B).
Proof. constructor. Qed.

Lemma Single_Finite : forall a b, Finite _ (@Single A B a b).
Proof. intros; apply Singleton_is_finite. Qed.

Lemma Insert_Finite : forall a b `(_ : Finite _ r) H, Finite _ (@Insert A B a b r H).
Proof. intros; apply Add_preserves_Finite; assumption. Qed.

Definition finite_ind := Generalized_induction_on_finite_sets.

Lemma Setminus_preserves_finite {U} :
  forall A:Ensemble U,
    Finite U A -> forall X:Ensemble U, Finite U (Setminus U A X).
Proof.
  intros A' ? ?; apply Finite_downward_closed with A'; auto with sets.
  intros ? H0; inversion H0; assumption.
Qed.

Lemma Conjunction_preserves_finite {U} :
  forall A:Ensemble U,
    Finite U A -> forall X:Ensemble U,
      Finite U (fun x : U => In U X x /\ In U A x) <-> Finite U (In U A).
Proof.
  intros A' H' X.
  split; intros.
    apply Finite_downward_closed with A'; auto with sets.
  apply Finite_downward_closed with A'; auto with sets.
  intros ? H0; inversion H0; assumption.
Qed.

Lemma Conjunction_preserves_finite_2 {U} :
  forall A:Ensemble U,
    Finite U A -> forall X:Ensemble U,
      Finite U (fun x : U => In U A x /\ In U X x) -> Finite U (In U A).
Proof.
  intros A' H' X H.
  apply Finite_downward_closed with A'; auto with sets.
Qed.

Lemma Exists_preserves_finite_conj {U V} :
  forall (f : U * V -> V -> U * V) (X : Ensemble (U * V)) z,
    Finite (U * V) (fun x : U * V =>
                      exists b : V, In (U * V) X (f x b)) ->
    Finite (U * V) (fun x : U * V =>
                      exists b : V, In (U * V) X (f x b) /\ z x b).
Proof.
  intros.
  eapply Finite_downward_closed; eauto with sets.
  intros ? H0; inversion H0; intuition; clear H0.
  exists x0.
  assumption.
Qed.

Lemma Exists_finite_forall {U V} :
  forall (X:Ensemble (U * V)),
    Finite (U * V) X ->
    Finite (U * V) (fun x : U * V => exists b : V, In (U * V) X (fst x, b)).
Proof.
  intros.
  inversion H.
    admit.
  eapply Finite_downward_closed; eauto with sets.
  intros ? H3; inversion H3; intuition; clear H3.
  rewrite H2 in H4.
Abort.

Lemma Exists_preserves_finite {U V} :
  forall (X:Ensemble (U * V)),
    Finite (U * V) X ->
    Finite (U * V) (fun x : U * V => exists b : V, In (U * V) X (fst x, b)).
Proof.
  intros.
(*
  apply ex_Included; intros.
  pose proof (ex_Included (U * V) V (fun b x => (fst x, b)) X).
  intros ? H0; inversion H0; intuition; clear H0.
    inversion H.
  inversion IHFinite.
    admit.
  eapply Finite_downward_closed; eauto with sets.
  intros ? H4; inversion H4; intuition; clear H4.
  inversion H5; subst; clear H5.
    admit.
  inversion H4; subst; clear H4.
    contradiction.
  inversion H2; subst; clear H2.
    admit.
  inversion H1; subst; clear H1.
    rewrite (Non_disjoint_union U X x); auto with sets.
  unfold Ensembles.In.
  inversion H2; subst; clear H2.
    exists x1.
    assumption.
  assumption.
*)
Abort.

Lemma Remove_Finite : forall a `(_ : Finite _ r), Finite _ (@Remove A B a r).
Proof. intros; apply Setminus_preserves_finite; assumption. Qed.

Lemma Update_Finite : forall a b `(_ : Finite _ r),
  Finite _ (@Update A B a b r).
Proof.
  intros; apply Add_preserves_Finite, Setminus_preserves_finite; assumption.
Qed.

Lemma Move_Finite : forall a a' `(_ : Finite _ r), Finite _ (@Move A B a a' r).
Proof.
  unfold Move; intros.
  eapply Finite_downward_closed; eauto with sets.
  intros ? H0.
  unfold Ensembles.In in H0.
  destruct H0.
    destruct H; subst.
    admit.
  destruct H.
  teardown.
  destruct H0.
  unfold Lookup in H1.
  rewrite <- surjective_pairing in H1.
  assumption.
Admitted.

Lemma Filter_Finite : forall P `(_ : Finite _ r), Finite _ (@Filter A B P r).
Proof.
  unfold Filter; intros.
  eapply Finite_downward_closed; eauto with sets.
  intros ? H0; inversion H0; clear H0.
  unfold Lookup in H.
  rewrite <- surjective_pairing in H.
  assumption.
Qed.

Lemma Map_Finite : forall f `(_ : Finite _ r), Finite _ (@Map A B f r).
Proof.
  unfold Map, Lookup; intros.
  apply Exists_preserves_finite_conj.
  eapply Finite_downward_closed; eauto with sets.
  intros ? H0.
  destruct H0.
  destruct x; simpl in *.
  induction Finite0.
    admit.
Admitted.

Lemma Modify_Finite : forall a f `(_ : Finite _ r), Finite _ (@Modify A B a f r).
Proof.
  unfold Modify; intros.
  eapply Finite_downward_closed; eauto with sets.
  intros ? H0.
  unfold Ensembles.In in H0.
  destruct H0, H; subst.
  destruct H0, H; subst.
  inversion H0; subst; clear H0.
  unfold Lookup in H.
  admit.
Admitted.

Lemma Define_Finite : forall P b `(_ : Finite _ r), Finite _ (@Define A B P b r).
Proof.
  unfold Define; intros.
  eapply Finite_downward_closed; eauto with sets.
  intros ? H0.
  unfold Ensembles.In in H0.
  admit.
Admitted.

Lemma Overlay_Finite : forall P `(_ : Finite _ r) `(_ : Finite _ r'),
  Finite _ (@Overlay A B P r r').
Proof.
  unfold Overlay; intros.
  eapply Finite_downward_closed; eauto with sets.
  intros ? H0.
  unfold Ensembles.In in H0.
  specialize (H0 (fst x)).
  destruct H0, H; subst.
    unfold Lookup in H0.
    rewrite <- surjective_pairing in H0.
    assumption.
  admit.
Admitted.

End TupleEnsembleFinite.

Ltac finitary :=
  repeat match goal with
    | [ |- Finite _ Empty            ] => eapply Empty_Finite
    | [ |- Finite _ (Single _ _)     ] => eapply Single_Finite
    | [ |- Finite _ (Insert _ _ _ _) ] => eapply Insert_Finite
    | [ |- Finite _ (Remove _ _)     ] => eapply Remove_Finite
    | [ |- Finite _ (Setminus _)     ] => eapply Setminus_preserves_finite
    | [ |- Finite _ (Update _ _ _)   ] => eapply Update_Finite
    | [ |- Finite _ (Move _ _ _)     ] => eapply Move_Finite
    | [ |- Finite _ (Filter _ _)     ] => eapply Filter_Finite
    | [ |- Finite _ (Map _ _)        ] => eapply Map_Finite
    | [ |- Finite _ (Modify _ _ _)   ] => eapply Modify_Finite
    | [ |- Finite _ (Define _ _ _)   ] => eapply Define_Finite
    | [ |- Finite _ (Overlay _ _ _)  ] => eapply Overlay_Finite
    end; eauto.
