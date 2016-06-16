Require Import Fiat.ADT.

Require Import Coq.Sets.Ensembles.
Require Import Here.LibExt.

Definition IEnsemble (A : Type) := Ensemble (nat * A).

Definition IEnsemble_size {A} (r : IEnsemble A) : Comp nat :=
  { n : nat | (forall n0, n = S n0 -> exists x, Ensembles.In _ r (n0, x)) /\
              forall m y, n <= m -> ~ Ensembles.In _ r (m, y) }.

Definition IEnsemble_cons (A : Type) (x : A) (xs : IEnsemble A) : IEnsemble A :=
  Ensembles.Add _ (Ensemble_map (first S) xs) (0, x).

Lemma refine_skipped : forall A B (a : Comp A) (b : Comp B) (v : A),
  a ↝ v -> refine (a >> b) b.
Proof.
  intros A B a b v H x H1.
  exists v; firstorder.
Qed.

Lemma IEnsemble_cons_size : forall A (x : A) xs v,
  IEnsemble_size xs ↝ v
    -> refine (n  <- IEnsemble_size xs;
               n' <- IEnsemble_size (IEnsemble_cons x xs);
               { b | decides b (n' = S n) }) (ret true).
Proof.
  intros.
  unfold IEnsemble_size, IEnsemble_cons.
  etransitivity.
    apply refine_bind_pick.
    intros n [H1 H2].
    refine pick val (S n).
      simplify with monad laws.
      refine pick val true.
        higher_order_reflexivity.
      reflexivity.
    split.
      intros n0 H0.
      inv H0.
      induction n0.
        exists x.
        apply Union_intror.
        constructor.
      destruct (H1 n0 eq_refl).
      exists x0.
      apply Union_introl.
      exists (n0, x0); firstorder.
    unfold not; intros x0 y H0 H3.
    inv H3; inv H4.
      destruct x1.
      destruct H3.
      inv H4.
      apply Le.le_S_n in H0.
      contradiction (H2 n0 y H0).
    apply (NPeano.Nat.nle_succ_0 _ H0).
  simpl.
  exists v.
  split.
    apply H.
  apply H0.
Qed.

Definition IEnsemble_snoc (A : Type) (x : A) (xs : IEnsemble A) : IEnsemble A :=
  n <- IEnsemble_size xs;
  Ensembles.Add _ xs (S n, x).

Definition IEnsemble_unsnoc (A : Type) (xs : IEnsemble A) :
  Comp (IEnsemble A * option A) :=
  n <- IEnsemble_size xs;
  { w : IEnsemble A * option A
  | Ifopt snd w as x
    Then forall n0, n = S n0
           /\ Ensembles.In _ xs (n0, x)
           /\ fst w = Ensembles.Subtract _ xs (n0, x)
    Else (fst w = xs) }.

Definition IEnsemble_map {A B} (f : A -> B) : IEnsemble A -> IEnsemble B :=
  Ensemble_map (second f).

Definition IEnsemble_from_list {A} (r : list A) : IEnsemble A :=
  { p : nat * A | List.In p (zip (series 0) r) }.

Require Import Coq.Arith.Arith.

Definition IEnsemble_to_list {A} (r : IEnsemble A) : Comp (list A) :=
  { xs : list A | forall i x, Ensembles.In _ r (i, x) ->
                    forall H : is_true (i <? length xs), x = nth_safe i xs H }.
