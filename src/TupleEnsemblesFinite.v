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

Lemma Insert_Finite : forall a b `(_ : Finite _ r) H,
  Finite _ (@Insert A B a b r H).
Proof. intros; apply Add_preserves_Finite; assumption. Qed.

Lemma Setminus_preserves_finite {U} :
  forall A:Ensemble U,
    Finite U A -> forall X:Ensemble U, Finite U (Setminus U A X).
Proof.
  intros A' ? ?; apply Finite_downward_closed with A'; auto with sets.
  intros ? H0; inversion H0; assumption.
Qed.

Lemma Remove_Finite : forall a `(_ : Finite _ r), Finite _ (@Remove A B a r).
Proof. intros; apply Setminus_preserves_finite; assumption. Qed.

Lemma Update_Finite : forall a b `(_ : Finite _ r),
  Finite _ (@Update A B a b r).
Proof.
  intros; apply Add_preserves_Finite, Setminus_preserves_finite; assumption.
Qed.

Lemma Filter_Finite : forall P `(_ : Finite _ r), Finite _ (@Filter A B P r).
Proof.
  unfold Filter; intros.
  eapply Finite_downward_closed; eauto with sets.
  intros ? H0; inversion H0; clear H0.
  unfold Lookup in H.
  rewrite <- surjective_pairing in H.
  assumption.
Qed.

Lemma Finite_Add_Subtract : forall T (Y : Ensemble T) x,
  Finite _ (Add T (Subtract T Y x) x) -> Finite _ Y.
Proof.
  intros.
  eapply Finite_downward_closed; eauto with sets; intros ??.
  (* Jason Gross: To avoid the axiom of choice, you'd need a stronger version
     of [Finite], something like having a list of elements together with a
     mapping of elements of the type to indices of the list such that if an
     element of the type is in the subset, then it is equal to the element of
     the list at the corresponding index. In this case, everything is
     constructive, and you shouldn't need either ensemble-extensionality nor
     decidable equality. *)
  elim (classic (x = x0)); intros.
    subst; right; constructor.
  left; constructor; auto.
  unfold not; intros.
  contradiction H1.
  inversion H2.
  reflexivity.
Qed.

Definition Surjective {A B} (X : Ensemble A) (Y : Ensemble B) f :=
  forall y : B, In _ Y y -> exists x : A, In _ X x /\ y = f x.

Lemma Surjective_Add_Subtract : forall T T' X Y f x,
  Surjective (Add T X x) Y f -> Surjective X (Subtract T' Y (f x)) f.
Proof.
  unfold Surjective; intros.
  inversion H0; clear H0.
  destruct (H _ H1) as [? [? ?]]; subst; clear H H1.
  inversion H0; subst; clear H0.
    exists x0; intuition.
  inversion H; subst; clear H.
  contradiction H2.
  constructor.
Qed.

Lemma Surjection_preserves_Finite : forall T T' X Y f,
  Surjective X Y f -> Finite T X -> Finite T' Y.
Proof.
  intros.
  generalize dependent Y.
  induction H0; intros.
    eapply Finite_downward_closed; eauto with sets; intros ??.
    firstorder.
  apply Surjective_Add_Subtract in H1; auto.
  specialize (IHFinite _ H1).
  eapply Finite_Add_Subtract.
  constructor.
  exact IHFinite.
  unfold not; intros.
  inversion H2.
  contradiction H4.
  constructor.
Qed.

Theorem Map_Finite {C} : forall f `(_ : Finite _ r), Finite _ (@Map A B C f r).
Proof.
  unfold Map; intros.
  apply Surjection_preserves_Finite
   with (X:=r) (f:=fun p => (fst p, f (fst p) (snd p))); trivial.
  intros ??.
  unfold Ensembles.In in H.
  do 2 destruct H.
  destruct y; simpl in *; subst.
  exists (a, x); simpl.
  intuition.
Qed.

Theorem Relate_Finite :
  forall A B C D (f : A -> B -> C -> D -> Prop) `(_ : Finite _ r)
         (is_functional : forall k e k' e' k'' e'',
            f k e k' e' -> f k e k'' e'' -> k' = k'' /\ e' = e'')
         (is_total : forall (k : A) (e : B),
            { p : C * D | Lookup k e r -> f k e (fst p) (snd p) }),
    Finite _ (Relate f r).
Proof.
  unfold Relate; intros ????? r ? g k.
  eapply Surjection_preserves_Finite
    with (X:=r) (f:=fun p => proj1_sig (k (fst p) (snd p))); trivial.
  intros ??.
  unfold Ensembles.In in H.
  do 2 destruct H.
  destruct y; simpl in *; subst.
  exists (x, x0); simpl.
  destruct (k x x0), x1.
  simpl in *; intuition.
  destruct (g _ _ _ _ _ _ H H1); subst.
  reflexivity.
Qed.

Lemma Move_Finite : forall a a' `(_ : Finite _ r),
  (forall x y : A, {x = y} + {x <> y})
    -> Finite _ (@Move A B a a' r).
Proof.
  intros.
  apply Relate_Finite; trivial; intros.
    intuition.
      destruct H2, H3; intuition; subst; auto.
    congruence.
  destruct (X k a); subst.
    exists (a', e); simpl; intuition.
    left; intuition.
  destruct (X k a'); subst.
    admit.
  exists (k, e); simpl; intuition.
  right; intuition.
Admitted.

Lemma Modify_Finite : forall a f `(_ : Finite _ r),
  (forall x y : A, {x = y} + {x <> y})
    -> Finite _ (@Modify A B a f r).
Proof.
  intros.
  apply Relate_Finite; trivial; intros.
    intuition.
      destruct H2, H3; intuition; subst; auto.
    destruct H2, H3; intuition; subst; tauto.
Admitted.

Lemma Define_Finite : forall P b `(_ : Finite _ r),
  (forall x : A, {P x} + {~ P x})
    -> Finite _ (@Define A B P b r).
Proof.
  unfold Define; intros.
(*
  eapply Surjection_preserves_Finite
   with (X:=r) (f:=fun p => match X (fst p) with
                            | left _ => (fst p, b)
                            | right _ => p
                            end); trivial.
  intros ??.
  unfold Ensembles.In in H.
  do 2 destruct H;
  destruct y; simpl in *; subst.
    exists (a, b); simpl.
    destruct (X a); simpl in *; intuition.

  exists (a, b0); simpl.
  destruct (X a); simpl in *; intuition.
*)
Admitted.

Lemma Overlay_Finite : forall P `(_ : Finite _ r) `(_ : Finite _ r'),
  Finite _ (@Overlay A B P r r').
Proof.
  intros.
  apply Relate_Finite; trivial; intros.
    intuition.
      destruct (P k'), (P k''); intuition; subst; auto.
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
