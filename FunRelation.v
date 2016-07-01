Require Export
  Coq.Sets.Ensembles.

Require Import
  Coq.Program.Tactics.

Section FunRelation.

Variable A : Type.
Variable B : Type.

Record FunRel := mkFunRel {
  relEns : Ensemble (A * B);
  _      : forall a b b',
             In _ relEns (a, b)  ->
             In _ relEns (a, b') -> b = b'
}.

Program Definition Empty : FunRel := mkFunRel (Empty_set (A * B)) _.
Obligation 1. inversion H. Qed.

Program Definition Insert
        (a : A) (b : B) (r : FunRel)
        (H : forall b' : B, ~ In _ (relEns r) (a, b')) : FunRel :=
  mkFunRel (Add _ (relEns r) (a, b)) _.
Obligation 1.
  destruct r; simpl in *.
  inversion H0; inversion H1; clear H0 H1;
  try (inversion H2; clear H2);
  try (inversion H4; clear H4);
  subst; firstorder.
Qed.

Program Definition Remove (a : A) (r : FunRel) : FunRel :=
  mkFunRel (Setminus _ (relEns r) (fun p => fst p = a)) _.
Obligation 1.
  destruct r; simpl in *.
  inversion H; inversion H0; clear H H0;
  subst; firstorder.
Qed.

Lemma Remove_spec : forall a r r',
  Remove a r = r' -> forall b' : B, ~ In _ (relEns r') (a, b').
Proof.
  unfold Remove, relEns, Setminus, In.
  intros; subst.
  firstorder.
Qed.

Program Definition Update (a : A) (b : B) (r : FunRel) : FunRel :=
  Insert a b (Remove a r) _.
Obligation 1.
  unfold Remove, relEns, Setminus, In.
  intros; subst.
  firstorder.
Qed.

Program Definition Move (a a' : A) (r : FunRel) : FunRel :=
  mkFunRel (fun p => IF fst p = a'
                     then relEns r (a, snd p)
                     else relEns (Remove a r) p) _.
Obligation 1.
  unfold Remove, relEns.
  destruct r; simpl in *.
  inversion H; inversion H0; clear H H0;
  firstorder.
Qed.

Program Definition Filter (P : A * B -> Prop) (r : FunRel) : FunRel :=
  mkFunRel (fun p => P p /\ relEns r p) _.
Obligation 1. destruct r; simpl in *; firstorder. Qed.

Program Definition Map (f : A * B -> B) (r : FunRel) : FunRel :=
  mkFunRel (fun p : A * B =>
              exists b : B,
                In _ (relEns r) (fst p, b) /\
                In _ (Singleton _ (fst p, f (fst p, b))) p) _.
Obligation 1.
  destruct r; simpl in *;
  firstorder; simpl in *.
  specialize (e _ _ _ H H0); subst.
  inversion H1; inversion H2; clear H1 H2.
  reflexivity.
Qed.

Program Definition Modify (a : A) (f : B -> B) (r : FunRel) : FunRel :=
  mkFunRel (fun p : A * B =>
              IF fst p = a
              then exists b : B,
                In _ (relEns r) (fst p, b) /\
                In _ (Singleton _ (f b)) (snd p)
              else In _ (relEns r) p) _.
Obligation 1.
  destruct r; simpl in *;
  firstorder; simpl in *.
  specialize (e _ _ _ H1 H3); subst.
  inversion H2; inversion H4; clear H2 H4.
  reflexivity.
Qed.

Definition RemoveIf (P : A * B -> Prop) (r : FunRel) : FunRel :=
  Filter (fun p => ~ P p) r.

Definition All (P : A * B -> Prop) (r : FunRel) : Prop :=
  forall p, In _ (relEns r) p -> P p.

Definition Any (P : A * B -> Prop) (r : FunRel) : Prop :=
  exists p, In _ (relEns r) p -> P p.

Program Definition Define (P : A -> Prop) (b : B) (r : FunRel) : FunRel :=
  mkFunRel (fun p => IF P (fst p) then snd p = b else relEns r p) _.
Obligation 1.
  destruct r; simpl in *.
  unfold In in *; simpl in *.
  firstorder.
  subst.
  reflexivity.
Qed.

Program Definition Transfer (P : A -> option A) (r r' : FunRel) : FunRel :=
  mkFunRel (fun p => forall a,
              IF P a = Some (fst p)
              then relEns r (a, snd p)
              else relEns r' p) _.
Obligation 1.
  destruct r, r'; simpl in *.
  unfold In in *; simpl in *.
  specialize (H a).
  specialize (H0 a).
  destruct H, H0;
  destruct (P a);
  destruct H, H0;
  firstorder.
Qed.

Definition Lookup (a : A) (b : B) (r : FunRel) := In _ (relEns r) (a, b).

Lemma All_Lookup : forall P r, All P r -> forall a b, Lookup a b r -> P (a, b).
Proof.
  unfold All, Lookup; intros.
  firstorder.
Qed.

Lemma Lookup_Remove_inv : forall a b a' r,
  Lookup a b (Remove a' r) -> a <> a' /\ Lookup a b r.
Proof. firstorder. Qed.

Lemma Lookup_Remove : forall a b a' r,
  Lookup a b r -> a <> a' -> Lookup a b (Remove a' r).
Proof. firstorder. Qed.

Lemma Lookup_Update_inv : forall a b a' b' r,
  Lookup a b (Update a' b' r)
    -> IF a = a' then b = b' else Lookup a b r.
Proof.
  intros.
  inversion H; clear H.
    firstorder.
  inversion H0; clear H0.
  firstorder.
Qed.

Lemma Lookup_Move_inv : forall a b a' a'' r,
  Lookup a b (Move a' a'' r)
    -> IF a = a''
       then Lookup a' b r
       else a <> a' /\ Lookup a b r.
Proof. firstorder. Qed.

Lemma Lookup_Map_inv : forall a b f r,
  Lookup a b (Map f r)
    -> exists b', f (a, b') = b /\ Lookup a b' r.
Proof.
  intros.
  inversion H; clear H.
    firstorder.
  inversion H0; clear H0.
  firstorder.
Qed.

Lemma Lookup_Map : forall a b f r,
  Lookup a b r -> Lookup a (f (a, b)) (Map f r).
Proof. firstorder. Qed.

Lemma Lookup_Modify_inv : forall a b a' f r,
  Lookup a b (Modify a' f r)
    -> IF a = a'
       then exists b', f b' = b /\ Lookup a b' r
       else Lookup a b r.
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

Definition Member (a : A) (r : FunRel) := exists b, In _ (relEns r) (a, b).

Lemma Member_Remove (addr : A) mem :
  forall addr', Member addr' mem
    -> addr' <> addr
    -> Member addr' (Remove addr mem).
Proof. firstorder. Qed.

Lemma Member_Lookup : forall a r, Member a r -> exists b, Lookup a b r.
Proof. firstorder. Qed.

Lemma Lookup_Member : forall a b r, Lookup a b r -> Member a r.
Proof. firstorder. Qed.

Definition Find (P : A -> B -> Prop) (a : A) (b : B) (r : FunRel) :=
  Lookup a b r /\ P a b.

Definition FindA (P : A -> Prop) (b : B) (r : FunRel) :=
  forall a, Lookup a b r /\ P a.

Definition FindB (P : B -> Prop) (a : A) (r : FunRel) :=
  forall b, Lookup a b r /\ P b.

Lemma Find_Lookup_iff (P : A -> B -> Prop) (r : FunRel) :
  forall a b, Find (fun _ _ => True) a b r <-> Lookup a b r.
Proof. unfold Find; split; intros; firstorder. Qed.

End FunRelation.

Arguments mkFunRel : default implicits.
Arguments relEns : default implicits.
Arguments Empty : default implicits.
Arguments Insert : default implicits.
Arguments Remove : default implicits.
Arguments Update : default implicits.
Arguments Modify : default implicits.
Arguments Move : default implicits.
Arguments Filter : default implicits.
Arguments Map : default implicits.
Arguments RemoveIf : default implicits.
Arguments All : default implicits.
Arguments Any : default implicits.
Arguments Define : default implicits.
Arguments Transfer : default implicits.
Arguments Lookup : default implicits.
Arguments Member : default implicits.
Arguments Find : default implicits.
Arguments FindA : default implicits.
Arguments FindB : default implicits.

Ltac teardown :=
  repeat
    match goal with
    | [ H : Lookup _ _ (Modify _ _ _) |- _ ] => apply Lookup_Modify_inv in H
    | [ H : Lookup _ _ (Update _ _ _) |- _ ] => apply Lookup_Update_inv in H
    | [ H : Lookup _ _ (Move _ _ _)   |- _ ] => apply Lookup_Move_inv in H
    | [ H : Lookup _ _ (Map _ _)      |- _ ] => apply Lookup_Map_inv in H
    | [ H : Lookup _ _ (Remove _ _)   |- _ ] => apply Lookup_Remove_inv in H

    | [ H : IF _ then _ else _ |- _ ] => destruct H
    | [ H : _ /\ _             |- _ ] => destruct H
    | [ H : exists _, _        |- _ ] => destruct H

    end; try tauto.
