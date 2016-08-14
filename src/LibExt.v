(** Basic definitions added to the standard library. *)

Ltac inv H := inversion H; subst; clear H.

Definition first {A B C} (f : A -> C) (p : A * B) : C * B :=
  (f (fst p), snd p).

Definition second {A B C} (f : B -> C) (p : A * B) : A * C :=
  (fst p, f (snd p)).

Require Import
  Coq.Sets.Ensembles
  ByteString.Same_set.

Definition Map_set {A B} (f : A -> B) (r : Ensemble A) : Ensemble B :=
  fun b => exists a : A, In _ r a /\ b = f a.

Lemma Map_set_left_identity {A} (r : Ensemble A) : Same_set A r (Map_set id r).
Proof.
  unfold Map_set; split; intros.
    eexists; intuition.
    assumption.
  intros ??.
  do 2 destruct H.
  unfold id in H0.
  congruence.
Qed.

Lemma Map_set_right_identity {A} (r : Ensemble A) : Same_set A (Map_set id r) r.
Proof.
  unfold Map_set; split; intros.
    intros ??.
    do 2 destruct H.
    unfold id in H0.
    congruence.
  eexists; intuition.
  assumption.
Qed.

Lemma Map_set_composition {A B C} (r : Ensemble A) :
  forall (f : B -> C) (g : A -> B),
   Same_set C (Map_set (fun x => f (g x)) r) (Map_set f (Map_set g r)).
Proof.
  unfold Map_set; split; intros; intros ??.
    do 2 destruct H; subst.
    exists (g x0); simpl in *.
    split; trivial.
    exists x0; simpl.
    intuition.
  do 2 destruct H; subst.
  do 2 destruct H; simpl in *; subst.
  exists x; simpl in *.
  intuition.
Qed.

Definition Product {T U} (X : Ensemble T) (Y : Ensemble U) : Ensemble (T * U) :=
  fun p => In T X (fst p) /\ In U Y (snd p).

Lemma Product_Add_left : forall T U (X : Ensemble T) (Y : Ensemble U) x,
  Same_set _ (Product (Add T X x) Y)
             (Union _ (Product (Singleton _ x) Y) (Product X Y)).
Proof.
  unfold Product; split; intros;
  intros ??; unfold Ensembles.In in *;
  destruct H;
  destruct x0; simpl in *;
  destruct H.
  - right; constructor; simpl; auto.
  - left; constructor; simpl; auto.
  - simpl in *; intuition; right; intuition.
  - simpl in *; intuition; left; intuition.
Qed.

Lemma Product_Add_right : forall T (X : Ensemble T) U (Y : Ensemble U) y,
  Same_set _ (Product X (Add U Y y))
             (Union _ (Product X Y) (Product X (Singleton _ y))).
Proof.
  unfold Product; split; intros;
  intros ??; unfold Ensembles.In in *;
  destruct H;
  destruct x; simpl in *.
  - destruct H0.
    + left; constructor; simpl; auto.
    + right; constructor; simpl; auto.
  - destruct H. intuition; left; intuition.
  - destruct H. intuition; right; intuition.
Qed.

Lemma Product_Empty_set_left : forall T U (X : Ensemble U),
  Same_set _ (Product (Empty_set T) X) (Empty_set (T * U)).
Proof.
  unfold Product; split; intros;
  intros ??; unfold Ensembles.In in *.
  destruct H;
  destruct x; simpl in *;
  destruct H.
  destruct H.
Qed.

Lemma Product_Empty_set_right : forall T (X : Ensemble T) U,
  Same_set _ (Product X (Empty_set U)) (Empty_set (T * U)).
Proof.
  unfold Product; split; intros;
  intros ??; unfold Ensembles.In in *.
  destruct H;
  destruct x; simpl in *.
  destruct H0.
  destruct H.
Qed.

Lemma Product_Singleton_Singleton : forall T U x y,
  Same_set _ (Product (Singleton T x) (Singleton U y))
             (Singleton (T * U) (x, y)).
Proof.
  unfold Product; split; intros;
  intros ??; unfold Ensembles.In in *;
  destruct H.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    rewrite <- surjective_pairing.
    constructor.
  simpl.
  intuition.
Qed.
