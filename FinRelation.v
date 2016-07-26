Require Export
  Coq.Sets.Ensembles
  Coq.Sets.Finite_sets
  Coq.Sets.Finite_sets_facts
  Here.FunRelation.

Require Import
  Coq.Program.Tactics.

Generalizable All Variables.

Section FinRelation.

Variable A : Type.
Variable B : Type.

Definition FinRel (xs : FunRel A B) := Finite (A * B) (relEns xs).

Lemma Empty_FinRel : FinRel (Empty A B).
Proof. constructor. Qed.

Lemma Single_FinRel : forall a b, FinRel (Single a b).
Proof. intros; apply Singleton_is_finite. Qed.

Lemma Insert_FinRel : forall a b `(_ : FinRel r) H, FinRel (Insert a b r H).
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

Lemma Remove_FinRel : forall a `(_ : FinRel r), FinRel (Remove a r).
Proof.
  unfold Remove, FinRel; simpl; intros.
  apply Setminus_preserves_finite; assumption.
Qed.

Lemma Update_FinRel : forall a b `(_ : FinRel r), FinRel (Update a b r).
Proof.
  unfold Remove, FinRel; simpl; intros.
  apply Add_preserves_Finite, Setminus_preserves_finite; assumption.
Qed.

Lemma Move_FinRel : forall a a' `(_ : FinRel r), FinRel (Move a a' r).
Proof.
Admitted.

Lemma Filter_FinRel : forall P `(_ : FinRel r), FinRel (Filter P r).
Proof.
Admitted.

Lemma Map_FinRel : forall f `(_ : FinRel r), FinRel (Map f r).
Proof.
Admitted.

Lemma Modify_FinRel : forall a f `(_ : FinRel r), FinRel (Modify a f r).
Proof.
Admitted.

Lemma Define_FinRel : forall P b `(_ : FinRel r), FinRel (Define P b r).
Proof.
Admitted.

Lemma Overlay_FinRel : forall P `(_ : FinRel r) `(_ : FinRel r'),
  FinRel (Overlay P r r').
Proof.
Admitted.

Lemma Partition_FinRel : forall P `(_ : FinRel r),
  FinRel (fst (Partition P r)) /\ FinRel (snd (Partition P r)).
Proof.
Admitted.

End FinRelation.

Arguments FinRel : default implicits.