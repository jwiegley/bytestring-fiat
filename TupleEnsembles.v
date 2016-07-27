Require Import Coq.Sets.Ensembles.

Generalizable All Variables.

Section TupleEnsemble.

Variables A B : Type.

Definition Empty : Ensemble (A * B) := Empty_set _.

Definition Single (a : A) (b : B) : Ensemble (A * B) :=
  Singleton _ (a, b).

Definition Lookup (a : A) (b : B) (r : Ensemble (A * B)) := In _ r (a, b).

Definition Same (x y : Ensemble (A * B)) : Prop :=
  forall a b, Lookup a b x <-> Lookup a b y.

Definition Member (a : A) (r : Ensemble (A * B)) :=
  exists b, Lookup a b r.

Definition Insert (a : A) (b : B) (r : Ensemble (A * B))
           (H : forall b' : B, ~ Lookup a b' r) : Ensemble (A * B) :=
  Add _ r (a, b).

Definition Remove (a : A) (r : Ensemble (A * B)) : Ensemble (A * B) :=
  Setminus _ r (fun p => fst p = a).

Require Import Coq.Program.Tactics.

Program Definition Update (a : A) (b : B) (r : Ensemble (A * B)) :
  Ensemble (A * B) :=
  Insert a b (Remove a r) _.
Obligation 1. firstorder. Qed.

Definition Move (a a' : A) (r : Ensemble (A * B)) : Ensemble (A * B) :=
  fun p => IF fst p = a'
           then Lookup a (snd p) r
           else Lookup (fst p) (snd p) (Remove a r).

Definition Map (f : A -> B -> B) (r : Ensemble (A * B)) :
  Ensemble (A * B) :=
  fun p : A * B =>
    exists b : B,
      Lookup (fst p) b r /\
      Lookup (fst p) (snd p) (Singleton _ (fst p, f (fst p) b)).

Definition Filter (P : A -> B -> Prop) (r : Ensemble (A * B)) :
  Ensemble (A * B) :=
  fun p => Lookup (fst p) (snd p) r /\ P (fst p) (snd p).

Definition Define (P : A -> Prop) (b : B) (r : Ensemble (A * B)) :
  Ensemble (A * B) :=
  fun p => IF P (fst p) then snd p = b else Lookup (fst p) (snd p) r.

Definition Modify (a : A) (f : B -> B) (r : Ensemble (A * B)) :
  Ensemble (A * B) :=
  fun p => IF fst p = a
           then exists b : B,
                  Lookup (fst p) b r /\
                  Lookup (fst p) (snd p) (Singleton _ (fst p, f b))
           else Lookup (fst p) (snd p) r.

Definition Overlay (P : A -> option A) (r' r : Ensemble (A * B)) :
  Ensemble (A * B) :=
  fun p =>
    forall a,
      IF P (fst p) = Some a
      then Lookup a (snd p) r
      else Lookup (fst p) (snd p) r'.

Definition All (P : A -> B -> Prop) (r : Ensemble (A * B)) : Prop :=
  forall a b, Lookup a b r -> P a b.

Definition Any (P : A -> B -> Prop) (r : Ensemble (A * B)) : Prop :=
  exists a b, Lookup a b r -> P a b.

Lemma Lookup_Empty : forall a b, ~ Lookup a b Empty.
Proof. firstorder. Qed.

Lemma Lookup_Single : forall a b, Lookup a b (Single a b).
Proof. firstorder. Qed.

Lemma Lookup_Single_inv : forall a b c d,
  Lookup a b (Single c d) -> a = c /\ b = d.
Proof. split; inversion H; reflexivity. Qed.

Lemma Lookup_Insert_inv : forall a b c d r H,
  Lookup a b (Insert c d r H) -> (a = c /\ b = d) \/ Lookup a b r.
Proof.
  intros.
  inversion H0; clear H0.
    firstorder.
  inversion H1; clear H1.
  firstorder.
Qed.

Lemma Lookup_Remove : forall a b a' r,
  Lookup a b r -> a <> a' -> Lookup a b (Remove a' r).
Proof. firstorder. Qed.

Lemma Lookup_Remove_ex_r : forall a b r,
  Lookup a b r -> exists a', a <> a' -> Lookup a' b (Remove a r).
Proof. firstorder. Qed.

Lemma Lookup_Remove_inv : forall a b a' r,
  Lookup a b (Remove a' r) -> a <> a' /\ Lookup a b r.
Proof. firstorder. Qed.

Lemma Lookup_Update_inv : forall a b a' b' r,
  Lookup a b (Update a' b' r)
    -> (a = a' /\ b = b') \/ (a <> a' /\ Lookup a b r).
Proof.
  intros.
  inversion H; clear H.
    firstorder.
  inversion H0; clear H0.
  firstorder.
Qed.

Lemma Lookup_Move_inv : forall a b a' a'' r,
  Lookup a b (Move a' a'' r)
    -> (a = a'' /\ Lookup a' b r) \/ (a <> a' /\ Lookup a b r).
Proof. firstorder. Qed.

Lemma Lookup_Map : forall a b f r,
  Lookup a b r -> Lookup a (f a b) (Map f r).
Proof. firstorder. Qed.

Lemma Lookup_Map_inv : forall a b f r,
  Lookup a b (Map f r) -> exists b', f a b' = b /\ Lookup a b' r.
Proof.
  intros.
  inversion H; clear H.
    firstorder.
  inversion H0; clear H0.
  firstorder.
Qed.

Lemma Lookup_Filter : forall a b P r,
  Lookup a b r /\ P a b -> Lookup a b (Filter P r).
Proof. firstorder. Qed.

Lemma Lookup_Filter_inv : forall a b P r,
  Lookup a b (Filter P r) -> P a b /\ Lookup a b r.
Proof. firstorder. Qed.

Lemma Lookup_Define_inv : forall a b c P r,
  Lookup a b (Define P c r) -> (P a /\ b = c) \/ Lookup a b r.
Proof. firstorder. Qed.

Lemma Lookup_Modify_inv : forall a b a' f r,
  Lookup a b (Modify a' f r)
    -> (a = a' /\ exists b', f b' = b /\ Lookup a b' r)
         \/ (a <> a' /\ Lookup a b r).
Proof.
  intros.
  inversion H; clear H;
  destruct H0.
    destruct H0.
    destruct H0.
    inversion H1; simpl in *; subst.
    left; split; trivial.
    exists x.
    split; trivial.
  right; split; trivial.
Qed.

Lemma Lookup_Overlay_inv : forall a b P r' r,
  Lookup a b (Overlay P r' r)
    -> match P a with
       | Some a' => Lookup a' b r
       | None    => Lookup a b r'
       end.
Proof.
  unfold Lookup, Overlay, Ensembles.In; simpl; intros.
  destruct (P a).
    destruct (H a0), H0.
      exact H1.
    tauto.
  destruct (H a), H0.
    discriminate.
  exact H1.
Qed.

Lemma Lookup_Member : forall a b r,
  Lookup a b r -> Member a r.
Proof. firstorder. Qed.

Lemma Member_Lookup_not : forall a r,
  ~ Member a r -> forall b, ~ Lookup a b r.
Proof. firstorder. Qed.

Lemma All_Remove_inv : forall a P r,
  All P (Remove a r) -> ~ Member a r -> All P r.
Proof.
  intros.
  intros ???.
  apply H.
  apply Lookup_Remove.
    assumption.
  unfold not; intros.
  subst.
  unfold Member in H0.
  Require Import Classical_Pred_Type.
  apply not_ex_all_not with (n:=b) in H0.
  contradiction.
Qed.

Lemma All_Remove_Lookup_inv : forall a P r,
  All P (Remove a r) -> forall a' b', a <> a' -> Lookup a' b' r -> P a' b'.
Proof. firstorder. Qed.

End TupleEnsemble.

Arguments Empty {_ _} _.
Arguments Single : default implicits.
Arguments Insert : default implicits.
Arguments Remove : default implicits.
Arguments Update : default implicits.
Arguments Modify : default implicits.
Arguments Move : default implicits.
Arguments Filter : default implicits.
Arguments Map : default implicits.
Arguments All : default implicits.
Arguments Any : default implicits.
Arguments Define : default implicits.
Arguments Overlay : default implicits.
Arguments Lookup : default implicits.
Arguments Same : default implicits.
Arguments Member : default implicits.

Arguments Lookup_Empty : default implicits.

Ltac teardown :=
  match goal with
  | [ H : Lookup _ _ Empty           |- _ ] => contradiction (Lookup_Empty H)
  | [ H : Lookup _ _ (Single _ _)    |- _ ] => apply Lookup_Single_inv in H
  | [ H : Lookup _ _ (Insert _ _ _)  |- _ ] => apply Lookup_Insert_inv in H
  | [ H : Lookup _ _ (Remove _ _)    |- _ ] => apply Lookup_Remove_inv in H
  | [ H : Lookup _ _ (Update _ _ _)  |- _ ] => apply Lookup_Update_inv in H
  | [ H : Lookup _ _ (Move _ _ _)    |- _ ] => apply Lookup_Move_inv in H
  | [ H : Lookup _ _ (Map _ _)       |- _ ] => apply Lookup_Map_inv in H
  | [ H : Lookup _ _ (Filter _ _)    |- _ ] => apply Lookup_Filter_inv in H
  | [ H : Lookup _ _ (Define _ _ _)  |- _ ] => apply Lookup_Define_inv in H
  | [ H : Lookup _ _ (Modify _ _ _)  |- _ ] => apply Lookup_Modify_inv in H
  | [ H : Lookup _ _ (Overlay _ _ _) |- _ ] => apply Lookup_Overlay_inv in H

  | [ H : Member _ Empty           |- _ ] => unfold Member in H
  | [ H : Member _ (Single _ _)    |- _ ] => unfold Member in H
  | [ H : Member _ (Insert _ _ _)  |- _ ] => unfold Member in H
  | [ H : Member _ (Remove _ _)    |- _ ] => unfold Member in H
  | [ H : Member _ (Update _ _ _)  |- _ ] => unfold Member in H
  | [ H : Member _ (Move _ _ _)    |- _ ] => unfold Member in H
  | [ H : Member _ (Map _ _)       |- _ ] => unfold Member in H
  | [ H : Member _ (Filter _ _)    |- _ ] => unfold Member in H
  | [ H : Member _ (Define _ _ _)  |- _ ] => unfold Member in H
  | [ H : Member _ (Modify _ _ _)  |- _ ] => unfold Member in H
  | [ H : Member _ (Overlay _ _ _) |- _ ] => unfold Member in H

  | [ H : Lookup ?X ?Y ?R |- Member ?X ?R ] => exists Y; exact H

  | [ H1 : All ?P ?R, H2 : Lookup ?X ?Y ?R |- _ ] =>
    specialize (H1 _ _ H2); simpl in H1

  | [ H : IF _ then _ else _ |- _ ] => destruct H
  | [ H : _ /\ _             |- _ ] => destruct H
  | [ H : _ * _              |- _ ] => destruct H
  | [ H : exists _, _        |- _ ] => destruct H
  | [ H : @sig _ _           |- _ ] => destruct H
  | [ H : @sigT _ _          |- _ ] => destruct H
  | [ H : bool               |- _ ] => destruct H
  | [ H : option _           |- _ ] => destruct H
  | [ H : _ \/ _             |- _ ] => destruct H

  | [ H : forall x, Some ?X = Some x -> _  |- _ ] => specialize (H X eq_refl)
  | [ H : forall x y, Some (?X, ?Y) = Some (x, y) -> _  |- _ ] =>
    specialize (H X Y eq_refl)

  | [ H1 : ?X = true, H2 : ?X = false |- _ ] => rewrite H1 in H2; discriminate

  end; simpl in *; try tauto.