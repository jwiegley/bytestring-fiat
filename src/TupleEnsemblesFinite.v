Require Export
  Here.LibExt
  Here.TupleEnsembles
  Here.Relations
  Coq.Sets.Finite_sets
  Coq.Sets.Finite_sets_facts.

Generalizable All Variables.

Global Program Instance Finite_Proper {A B} :
  Proper (Same (B:=B) ==> Basics.impl) (Finite (A * B)).
Obligation 1.
  relational.
  apply Same_Same_set in H.
  rewrite H.
  reflexivity.
Qed.

Global Program Instance Finite_Proper_flip_1 {A B} :
  Proper (Same (B:=B) ==> Basics.flip Basics.impl) (Finite (A * B)).
Obligation 1.
  relational.
  apply Same_Same_set in H.
  rewrite <- H.
  reflexivity.
Qed.

Global Program Instance Finite_Proper_flip_2 {A B} :
  Proper (Same (B:=B) --> Basics.flip Basics.impl) (Finite (A * B)).
Obligation 1.
  relational.
  apply Same_Same_set in H.
  rewrite H.
  reflexivity.
Qed.

Section TupleEnsembleFinite.

Variable A : Type.
Variable B : Type.

Lemma Empty_preserves_Finite : Finite _ (@Empty A B).
Proof. constructor. Qed.

Lemma Single_is_Finite : forall a b, Finite _ (@Single A B a b).
Proof. intros; apply Singleton_is_finite. Qed.

Lemma Insert_preserves_Finite : forall a b `(_ : Finite _ r) H,
  Finite _ (@Insert A B a b r H).
Proof. intros; apply Add_preserves_Finite; assumption. Qed.

Lemma Setminus_preserves_finite {U} :
  forall A:Ensemble U,
    Finite U A -> forall X:Ensemble U, Finite U (Setminus U A X).
Proof.
  intros A' ? ?; apply Finite_downward_closed with A'; auto with sets.
  intros ? H0; inversion H0; assumption.
Qed.

Lemma Remove_preserves_Finite : forall a `(_ : Finite _ r),
  Finite _ (@Remove A B a r).
Proof. intros; apply Setminus_preserves_finite; assumption. Qed.

Lemma Update_preserves_Finite : forall a b `(_ : Finite _ r),
  Finite _ (@Update A B a b r).
Proof.
  intros; apply Add_preserves_Finite, Setminus_preserves_finite; assumption.
Qed.

Lemma Filter_preserves_Finite : forall P `(_ : Finite _ r),
  Finite _ (@Filter A B P r).
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

Lemma Map_preserves_Finite {C} : forall f `(_ : Finite _ r),
  Finite _ (@Map A B C f r).
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

Lemma Map_set_preserves_Finite {T T'} : forall f `(_ : Finite _ r),
  Finite _ (@Map_set T T' f r).
Proof.
  unfold Map_set; intros.
  apply Surjection_preserves_Finite with (X:=r) (f:=f); trivial.
  intros ??.
  unfold Ensembles.In in H.
  do 2 destruct H; subst.
  exists x; simpl.
  intuition.
Qed.

Lemma Relate_preserves_Finite :
  forall A B C D (f : A -> B -> C -> D -> Prop) `(_ : Finite _ r)
         (is_functional : forall k e k' e' k'' e'',
            f k e k' e' -> f k e k'' e'' -> k' = k'' /\ e' = e'')
         (is_total : forall (k : A) (e : B),
            { p : C * D | f k e (fst p) (snd p) }),
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
  destruct (g _ _ _ _ _ _ f0 H1); subst.
  reflexivity.
Qed.

Lemma Relate_Add_preserves_Finite :
  forall A B C D (f : A -> B -> C -> D -> Prop) `(_ : Finite _ r) x
         (is_functional : forall k e k' e' k'' e'',
            f k e k' e' -> f k e k'' e'' -> k' = k'' /\ e' = e'')
         (is_total : forall (k : A) (e : B),
            { p : C * D | f k e (fst p) (snd p) }),
    ~ In (A * B) r x
      -> Finite _ (Relate f r)
      -> Finite _ (Relate f (Add (A * B) r x)).
Proof.
  intros.
  apply Relate_preserves_Finite; auto.
  constructor; auto.
Qed.

Lemma Move_preserves_Finite : forall a a' `(_ : Finite _ r),
  (forall x y : A, {x = y} + {x <> y})
    -> Finite _ (@Move A B a a' r).
Proof.
  intros.
  apply Relate_preserves_Finite; trivial; intros.
    intuition; subst; congruence.
  destruct (X k a); subst.
    exists (a', e); simpl; intuition.
  exists (k, e); simpl; intuition.
Qed.

Lemma Modify_preserves_Finite : forall a f `(_ : Finite _ r),
  (forall x y : A, {x = y} + {x <> y})
    -> Finite _ (@Modify A B a f r).
Proof.
  intros.
  apply Relate_preserves_Finite; trivial; intros.
    intuition.
      destruct H2, H3; intuition; subst; auto.
    destruct H2, H3; intuition; subst; tauto.
  destruct (X k a); subst.
    exists (a, f e); simpl; intuition.
    left; intuition.
  exists (k, e); simpl; intuition.
  right; intuition.
Qed.

Lemma Conjunction_preserves_finite_right {U} :
  forall A:Ensemble U,
    Finite U A -> forall X:Ensemble U,
      Finite U (fun x : U => In U X x /\ In U A x).
Proof.
  intros A' H' X.
  apply Finite_downward_closed with A'; auto with sets.
  intros ? H0; inversion H0; assumption.
Qed.

Lemma Conjunction_preserves_finite_left {U} :
  forall X:Ensemble U,
    Finite U X -> forall A:Ensemble U,
      Finite U (fun x : U => In U X x /\ In U A x).
Proof.
  intros X H' A'.
  apply Finite_downward_closed with X; auto with sets.
  intros ? H0; inversion H0; assumption.
Qed.

Lemma Product_preserves_Finite {T U X Y} :
  Finite T X -> Finite U Y -> Finite (T * U) (Product X Y).
Proof.
  intros.
  generalize dependent Y.
  induction H; intros.
    eapply Finite_downward_closed; eauto with sets.
    intros ? H1; inversion H1; inversion H.
  rewrite Product_Add_left.
  apply Union_preserves_Finite; auto.
  clear IHFinite H0 H A0.
  induction H1.
    eapply Finite_downward_closed; eauto with sets.
    intros ? H1; inversion H1; inversion H0.
  rewrite Product_Add_right.
  apply Union_preserves_Finite; auto.
  rewrite Product_Singleton_Singleton.
  rewrite <- Empty_set_zero'.
  constructor.
    constructor.
  unfold not; intros.
  inversion H0.
Qed.

Lemma Define_preserves_Finite : forall P b `(_ : Finite _ r),
  (forall x : A, {P x} + {~ P x})
    -> Finite _ P -> Finite _ (@Define A B P b r).
Proof.
  unfold Define; intros.
  apply Union_preserves_Finite.
    apply Product_preserves_Finite; auto.
    apply Singleton_is_finite.
  apply Filter_preserves_Finite; auto.
Qed.

End TupleEnsembleFinite.

Hint Resolve Conjunction_preserves_finite_left : sets.
Hint Resolve Conjunction_preserves_finite_right : sets.
Hint Resolve Define_preserves_Finite : sets.
Hint Resolve Empty_preserves_Finite : sets.
Hint Resolve Filter_preserves_Finite : sets.
Hint Resolve Finite_Add_Subtract : sets.
Hint Resolve Insert_preserves_Finite : sets.
Hint Resolve Map_preserves_Finite : sets.
Hint Resolve Modify_preserves_Finite : sets.
Hint Resolve Move_preserves_Finite : sets.
Hint Resolve Product_Add_left : sets.
Hint Resolve Product_Add_right : sets.
Hint Resolve Product_Empty_set_left : sets.
Hint Resolve Product_Empty_set_right : sets.
Hint Resolve Product_Singleton_Singleton : sets.
Hint Resolve Product_preserves_Finite : sets.
Hint Resolve Relate_Add_preserves_Finite : sets.
Hint Resolve Relate_preserves_Finite : sets.
Hint Resolve Remove_preserves_Finite : sets.
Hint Resolve Setminus_preserves_finite : sets.
Hint Resolve Single_is_Finite : sets.
Hint Resolve Surjection_preserves_Finite : sets.
Hint Resolve Surjective_Add_Subtract : sets.
Hint Resolve Update_preserves_Finite : sets.
