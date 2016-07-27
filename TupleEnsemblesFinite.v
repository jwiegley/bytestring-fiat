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
    Finite U A -> forall X:Ensemble U, Finite U (fun x : U => In U X x /\ In U A x).
Proof.
  intros A' H' X; apply Finite_downward_closed with A'; auto with sets.
  intros ? H0; inversion H0; assumption.
Qed.

Lemma Remove_Finite : forall a `(_ : Finite _ r), Finite _ (@Remove A B a r).
Proof.
  unfold Remove; simpl; intros.
  apply Setminus_preserves_finite; assumption.
Qed.

Lemma Update_Finite : forall a b `(_ : Finite _ r), Finite _ (@Update A B a b r).
Proof.
  unfold Remove; simpl; intros.
  apply Add_preserves_Finite, Setminus_preserves_finite; assumption.
Qed.

Lemma Move_Finite : forall a a' `(_ : Finite _ r), Finite _ (@Move A B a a' r).
Proof.
Admitted.

Lemma Filter_Finite : forall P `(_ : Finite _ r), Finite _ (@Filter A B P r).
Proof.
Admitted.

Lemma Map_Finite : forall f `(_ : Finite _ r), Finite _ (@Map A B f r).
Proof.
Admitted.

Lemma Modify_Finite : forall a f `(_ : Finite _ r), Finite _ (@Modify A B a f r).
Proof.
Admitted.

Lemma Define_Finite : forall P b `(_ : Finite _ r), Finite _ (@Define A B P b r).
Proof.
Admitted.

Lemma Overlay_Finite : forall P `(_ : Finite _ r) `(_ : Finite _ r'),
  Finite _ (@Overlay A B P r r').
Proof.
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
