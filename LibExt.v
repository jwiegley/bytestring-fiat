Require Import Coq.Sets.Ensembles.

Require Import Here.Same_set.

(** Basic definitions added to the standard library. *)

Ltac inv H := inversion H; subst; clear H.

Definition first {A B C} (f : A -> C) (p : A * B) : C * B :=
  (f (fst p), snd p).

Definition second {A B C} (f : B -> C) (p : A * B) : A * C :=
  (fst p, f (snd p)).

CoInductive stream (A : Type) := scons : A -> stream A -> stream A.

CoFixpoint series (n : nat) : stream nat := scons n (series (S n)).

Fixpoint zip {A B} (xs : stream A) (ys : list B) : list (A * B) :=
  match xs with
  | scons x xs =>
    match ys with
    | nil => nil
    | cons y ys => (x, y) :: zip xs ys
    end
  end.

Require Import Coq.Lists.List.

Lemma In_zip_series : forall A (x : A) xs n i, n <= i
  -> List.In (S i, x) (zip (series n) xs)
  -> exists y, In (i, y) (zip (series n) xs).
Proof.
  Require Import Omega.
  intros.
  generalize dependent n.
  induction xs; intros.
    inversion H0.
  simpl in H0.
  destruct H0.
    inv H0.
    abstract omega.
  simpl.
  specialize (IHxs (S n)).
  destruct (Peano_dec.eq_nat_dec n i).
    exists a.
    subst.
    left; reflexivity.
  assert (not_really_le : forall n i, n <= i -> n <> i -> S n <= i)
    by (intros; abstract omega).
  specialize (IHxs (not_really_le _ _ H n0) H0).
  destruct IHxs.
  exists x0.
  right.
  exact H1.
Qed.

Lemma In_ascending : forall A (x : A) xs n m,
  n < m -> ~ In (n, x) (zip (series m) xs).
Proof.
  unfold not.
  induction xs; simpl; intros.
    contradiction.
  destruct H0.
    inv H0.
    firstorder.
  apply IHxs with (n:=n) (m:=S m).
    omega.
  assumption.
Qed.

Lemma In_zip_at_index : forall i n A (x y : A) xs,
  In (i, x) (zip (series n) xs) -> In (i, y) (zip (series n) xs) -> x = y.
Proof.
  intros.
  generalize dependent n.
  induction xs; simpl; intros.
    contradiction.
  destruct H, H0.
  + inv H; inv H0; reflexivity.
  + inv H.
    apply In_ascending in H0; [contradiction|omega].
  + inv H0.
    apply In_ascending in H; [contradiction|omega].
  + apply (IHxs (S n)); trivial.
Qed.

Lemma pred_S_S : forall n i, Init.Nat.pred n = S i -> n = S (S i).
Proof. intros; omega. Qed.

Require Import Coq.Arith.Arith.

Program Fixpoint nth_safe
        {A : Type} (n : nat) (l : list A) : is_true (n <? length l) -> A :=
  match l as l0 return is_true (n <? length l0) -> A with
  | nil => fun _ => False_rect _ _
  | cons x xs =>
    match n as n0 return is_true (n0 <? length (x :: xs)) -> A with
    | O => fun _ => x
    | S n => @nth_safe A n xs
    end
  end.

Arguments nth_safe {A} n l _.

Require Export
  Coq.Sets.Constructive_sets
  Coq.Sets.Powerset_facts.

Require Import Fiat.ADT.

Ltac single_reduction :=
  match goal with
  | [ |- Strict_Included _ _ _ ] => constructor
  | [ |- Included _ _ _ ] =>
    let x := fresh "x" in
    let Hx := fresh "Hx" in
    intros x Hx
  | [ H : _ /\ _ |- _ ] => destruct H
  | [ |- _ /\ _ ] => split
  | [ H : _ * _ |- _ ] => destruct H
  | [ |- _ * _ ] => split
  | [ H : Ensembles.In _ _ _ |- _ ] => inv H
  | [ H : Ensembles.In _ _ _ |- _ ] => rewrite H in *
  | [ |- Ensembles.In _ _ _ ] => constructor
  | [ |- Ensembles.In _ (Bind _ (fun x => ret _)) _ ] => eexists
  | [ |- Ensembles.In _ _ _ ] => eexists
  | [ H : forall x : ?T, Some ?X = Some x -> _ |- _ ] =>
    specialize (H X eq_refl)
  | [ |- ret ?C ↝ ?V -> _ ] =>
    let H := fresh "H" in intro H; apply Return_inv in H; simpl in H; inv H
  | [ |- Bind ?C ?F ↝ ?V -> _ ] =>
    let H := fresh "H" in intro H; apply Bind_inv in H; simpl in H; inv H
  | [ |- Pick ?S ↝ ?V -> _ ] =>
    let H := fresh "H" in intro H; apply Pick_inv in H; simpl in H; inv H
  | [ H : ret ?C ↝ ?V     |- _ ] => apply Return_inv in H
  | [ H : Bind ?C ?F ↝ ?V |- _ ] => apply Bind_inv in H
  | [ H : Pick ?S ↝ ?V    |- _ ] => apply Pick_inv in H
  | [ |- ret ?C ↝ ?V ]           => apply ReturnComputes
  | [ |- Bind ?C ?F ↝ ?V ]       => apply BindComputes
  | [ |- Pick ?S ↝ ?V ]          => apply PickComputes
  | [ |- context [If_Opt_Then_Else ?V ?T ?E] ] => destruct V
  (* | [ |- context [IfDec_Then_Else ?P ?T ?E] ]  => unfold IfDec_Then_Else *)
  end.

Ltac simplify_ensembles :=
  repeat (single_reduction; simpl; destruct_ex);
  try solve [ intuition | constructor ].

Definition Ensemble_map {A B} (f : A -> B) (x : Comp A) : Comp B :=
  v <- x; ret (f v).
  (* fun b => exists a, Ensembles.In _ x a /\ b = f a. *)

Lemma refine_ret_Same_set : forall (A : Type) (a : A) (b : Comp A),
  Same_set _ b (ret a) -> refine (ret a) b.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Same_set_map : forall A B (f : A -> B) x,
  Same_set _ (fun b => exists a, Ensembles.In _ x a /\ b = f a)
             (v <- x; ret (f v)).
Proof.
  intros.
  split; intros v H.
    inv H.
    destruct H0.
    subst.
    exists x0.
    split.
      exact H.
    constructor.
  inv H.
  destruct H0.
  inv H0.
  exists x0.
  split.
    exact H.
  reflexivity.
Qed.

Lemma Same_set_ret : forall A (X Y : Ensemble A),
  Same_set A X Y -> Same_set (Ensemble A) (ret X) (ret Y).
Proof.
  intros.
  destruct H.
  split; intros z H1;
  inversion H1; subst; clear H1;
  apply Singleton_intro;
  apply Extensionality_Ensembles;
  split; intros z' H1';
  try apply H0, H1';
  apply H, H1'.
Qed.

Add Parametric Morphism {A B} : (@Ensemble_map A B)
  with signature (pointwise_relation _ eq ==> Same_set A ==> Same_set B)
    as Ensemble_map_Same_set.
Proof.
  unfold Ensemble_map, pointwise_relation; intros.
  rewrite H0.
  f_equiv.
  unfold pointwise_relation; intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Ensemble_map_id : forall A (xs : Ensemble A),
  Same_set _ (Ensemble_map id xs) xs.
Proof.
  intros.
  autorewrite with monad laws.
  reflexivity.
Qed.

Lemma Ensemble_map_comp : forall A B C xs (f : B -> C) (g : A -> B),
  Same_set _ (Ensemble_map f (Ensemble_map g xs))
             (Ensemble_map (fun x => f (g x)) xs).
Proof.
  intros.
  autorewrite with monad laws.
  reflexivity.
Qed.

Lemma Ensemble_map_Empty_set : forall A B f,
  Same_set _ (Ensemble_map f (Empty_set A)) (Empty_set B).
Proof.
  unfold Ensemble_map; intros.
  split; intros x H; simplify_ensembles.
Qed.

Lemma Ensemble_Add_Subtract : forall A xs x,
  ~ Ensembles.In A xs x
    -> Same_set _ (Ensembles.Subtract A (Ensembles.Add A xs x) x) xs.
Proof.
  unfold Ensembles.Subtract, Ensembles.Add, Ensembles.Setminus; intros.
  constructor; intros y H0; simplify_ensembles.
  unfold not; intros; simplify_ensembles.
Qed.

Lemma Ensemble_Add_In : forall A xs x,
  Ensembles.In A (Ensembles.Add A xs x) x.
Proof. intros; apply Union_intror; constructor. Qed.

Lemma Ensemble_not_In_inv : forall A a b c d,
  ~ Ensembles.In (nat * A) (Singleton (nat * A) (a, b)) (c, d)
    -> (a = c -> b <> d) \/ (b = d -> a <> c).
Proof.
  intros.
  destruct (Peano_dec.eq_nat_dec a c); subst.
    right.
    intros.
    subst.
    contradiction H.
    constructor.
  left.
  intros.
  contradiction.
Qed.

Lemma Ensemble_fst_eq_inv : forall A a b d,
  ~ Ensembles.In (nat * A) (Singleton (nat * A) (a, b)) (a, d)
    -> b <> d.
Proof.
  intros.
  intro H1.
  subst.
  contradiction H.
  constructor.
Qed.

Ltac In_contradiction IHfromADT :=
  match goal with
    | [ H1 : ?X <> ?Y,
        H2 : Ensembles.In (nat * ?A) ?R (?I, ?X),
        H3 : Ensembles.In (nat * ?A) ?R (?I, ?Y)
      |- False ] =>
      apply (IHfromADT Y X) in H2; trivial; contradiction
  end.

Require Import Fiat.ADTNotation.

Definition lookupMethod
           (sig : DecoratedADTSig)
           (idxMap : BoundedIndex (MethodNames sig) -> MethodIndex sig)
           (idx : BoundedIndex (MethodNames sig)) : MethodIndex sig :=
  idxMap idx.

Definition getADTSig {sig : DecoratedADTSig} : ADT sig -> DecoratedADTSig :=
  fun _ => sig.

Definition get_fin {A : Type} {n : nat} {Bound : Vector.t A n}
                   (idx : BoundedIndex Bound) :=
  ibound (indexb idx).

Lemma refine_comp_to_pick : forall A (c : Comp A),
  refine c { x : A | c ↝ x }.
Proof.
  intros ????.
  apply Pick_inv in H.
  exact H.
Qed.