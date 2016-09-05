Require Export Coq.Sets.Ensembles.

Require Import
  ByteString.LibExt
  ByteString.Relations
  ByteString.Same_set.

Generalizable All Variables.

Section TupleEnsemble.

Variables A : Type.
Variables B : A -> Type.

Definition DMap := Ensemble { a : A & B a }.

Definition Empty : DMap := Empty_set _.

Definition Single (a : A) (b : B a) : DMap := Singleton _ (existT _ a b).

Definition Lookup (a : A) (b : B a) (r : DMap) := In _ r (existT _ a b).

Definition Functional (r : DMap) :=
  forall addr blk1, Lookup (a:=addr) blk1 r ->
  forall blk2, Lookup (a:=addr) blk2 r -> blk1 = blk2.

Definition Same (x y : DMap) : Prop :=
  forall a b, Lookup (a:=a) b x <-> Lookup (a:=a) b y.

Global Program Instance Same_Equivalence : Equivalence Same.
Obligation 1.
  constructor; auto.
Qed.
Obligation 2.
  constructor; apply H; auto.
Qed.
Obligation 3.
  constructor; intros.
    apply H0, H; auto.
  apply H, H0; auto.
Qed.

Lemma Same_Same_set : forall x y, Same x y <-> Same_set _ x y.
Proof.
  unfold Same, Lookup.
  split; intros.
    split; intros;
    intros ? H0;
    destruct x0;
    apply H; assumption.
  split; intros;
  apply H; assumption.
Qed.

Require Import
  Coq.Program.Equality
  Coq.Logic.EqdepFacts.

Global Program Instance Lookup_Proper :
  Proper (forall_relation
            (fun x : A =>
               (fun p p' => eq_dep A B x p x p')
                 ==> Same ==> Basics.impl)%signature) Lookup.
Obligation 1.
  intros ?.
  relational; unfold Basics.impl; intros.
  apply H0.
  destruct H.
  assumption.
Qed.

Global Program Instance Lookup_Proper_flip :
  Proper (forall_relation
            (fun x : A =>
               (fun p p' => eq_dep A B x p x p')
                 ==> Same --> Basics.impl)%signature) Lookup.
Obligation 1.
  intros ?.
  relational; unfold Basics.impl; intros.
  apply H0.
  destruct H.
  assumption.
Qed.

Definition Member (a : A) (r : DMap) := exists b, Lookup (a:=a) b r.

Definition Insert (a : A) (b : B a) (r : DMap)
           (H : forall b' : B a, ~ Lookup (a:=a) b' r) : DMap :=
  Add _ r (existT _ a b).

Definition Remove (a : A) (r : DMap) : DMap :=
  Setminus _ r (fun p => projT1 p = a).

Program Definition Update (a : A) (b : B a) (r : DMap) :
  DMap := Insert (a:=a) b (Remove a r) _.
Obligation 1. firstorder. Qed.

Definition Map {C} (f : forall a : A, B a -> C a) (r : DMap) :
  Ensemble { a : A & C a } :=
  fun p => exists b : B (projT1 p),
    Lookup (a:=projT1 p) b r /\ projT2 p = f (projT1 p) b.

Definition Relate {C D}
           (f : forall a : A,  B a -> forall c : C, D c -> Prop) (r : DMap) :
  Ensemble (sigT D) :=
  fun p => exists k' e', Lookup (a:=k') e' r /\ f k' e' (projT1 p) (projT2 p).

Lemma Map_left_identity : forall r, Same r (Map (fun _ x => x) r).
Proof.
  unfold Map; split; intros.
    eexists b.
    intuition.
  do 2 destruct H.
  simpl in *.
  rewrite H0.
  assumption.
Qed.

Lemma Map_right_identity : forall r, Same (Map (fun _ x => x) r) r.
Proof.
  unfold Map; split; intros.
    do 2 destruct H.
    simpl in *.
    rewrite H0.
    assumption.
  eexists b.
  intuition.
Qed.

Lemma Map_composition : forall f g r,
  Same (Map (fun k e => f k (g k e)) r) (Map f (Map g r)).
Proof.
  unfold Map; split; intros.
    destruct H.
    destruct H; simpl in *.
    subst.
    exists (g a x); simpl in *.
    split; trivial.
    exists x; simpl.
    intuition.
  destruct H.
  destruct H; simpl in *.
  subst.
  destruct H; simpl in *.
  exists x0; simpl in *.
  destruct H.
  intuition.
  rewrite <- H0.
  reflexivity.
Qed.

(* Definition Move (a a' : A) (r : DMap) : DMap := *)
(*   Relate (fun k e k' e' => *)
(*             eq_dep _ _ k e k' e' *)
(*               /\ ((k' = a' /\ k = a) \/ (k' <> a /\ k = k'))) r. *)

Definition Filter (P : forall a : A, B a -> Prop) (r : DMap) :
  DMap :=
  fun p => Lookup (a:=projT1 p) (projT2 p) r /\ P (projT1 p) (projT2 p).

Definition Define (P : A -> Prop) (b : forall a : A, B a) (r : DMap) :
  DMap :=
  Ensembles.Union
    _ (fun p => P (projT1 p) /\ In _ (Singleton _ (b (projT1 p))) (projT2 p))
      (Filter (fun k _ => ~ P k) r).

Definition Modify (a : A) (f : forall a : A, B a -> B a) (r : DMap) :
  DMap :=
  Relate (fun k e k' e' =>
            k = k' /\ IF k' = a
                      then eq_dep _ _ k' e' k (f k e)
                      else eq_dep _ _ k' e' k e) r.

Definition All (P : forall a : A, B a -> Prop) (r : DMap) : Prop :=
  forall a b, Lookup (a:=a) b r -> P a b.

Definition Any (P : forall a : A, B a -> Prop) (r : DMap) : Prop :=
  exists a b, Lookup (a:=a) b r /\ P a b.

Lemma Lookup_Empty : forall a b, ~ Lookup (a:=a) b Empty.
Proof. firstorder. Qed.

Lemma Lookup_Single : forall a a' b b',
  eq_dep _ _ a b a' b' -> Lookup (a:=a) b (Single (a:=a') b').
Proof.
  intros.
  destruct H.
  firstorder.
Qed.

Lemma Lookup_Single_inv : forall a b c d,
  Lookup (a:=a) b (Single (a:=c) d) -> eq_dep _ _ a b c d.
Proof.
  intros.
  inversion H.
  constructor.
Qed.

Lemma Lookup_Insert : forall a b c d r H,
  eq_dep _ _ a b c d \/ (~ eq_dep _ _ a b c d /\ Lookup (a:=a) b r)
    -> Lookup (a:=a) b (Insert (a:=c) d r H).
Proof.
  intros.
  intuition.
    destruct H1.
    right; constructor.
  left.
  exact H2.
Qed.

Lemma Lookup_Insert_inv : forall a b c d r H,
  Lookup (a:=a) b (Insert (a:=c) d r H)
    -> eq_dep _ _ a b c d \/ (~ eq_dep _ _ a b c d /\ Lookup (a:=a) b r).
Proof.
  intros.
  inversion H0; clear H0.
    subst.
    right.
    firstorder.
    unfold not; intros; subst.
    destruct H0.
    contradiction (H b).
  inversion H1; clear H1.
  firstorder.
Qed.

Lemma Lookup_Remove : forall a b a' r,
  Lookup (a:=a) b r -> a <> a' -> Lookup (a:=a) b (Remove a' r).
Proof. firstorder. Qed.

Lemma Lookup_Remove_ex_r : forall a b r,
  Lookup (a:=a) b r
    -> exists a' b', a <> a' -> Lookup (a:=a') b' (Remove a r).
Proof. firstorder. Qed.

Lemma Lookup_Remove_inv : forall a b a' r,
  Lookup (a:=a) b (Remove a' r) -> a <> a' /\ Lookup (a:=a) b r.
Proof. firstorder. Qed.

Lemma Lookup_Update : forall a b a' b' r,
  eq_dep _ _ a b a' b' \/ (a <> a' /\ Lookup (a:=a) b r)
    -> Lookup (a:=a) b (Update (a:=a') b' r).
Proof. intros; destruct H, H; [right|left]; constructor; firstorder. Qed.

Lemma Lookup_Update_inv : forall a b a' b' r,
  Lookup (a:=a) b (Update (a:=a') b' r)
    -> eq_dep _ _ a b a' b' \/ (a <> a' /\ Lookup (a:=a) b r).
Proof.
  intros.
  inversion H; clear H.
    firstorder.
  subst.
  inversion H0; subst; clear H0.
  firstorder.
Qed.

Lemma Lookup_Relate :
  forall a b c d (f : forall a : A, B a -> forall a' : A, B a' -> Prop) r,
    Lookup (a:=a) b r -> f a b c d -> Lookup (a:=c) d (Relate f r).
Proof. firstorder. Qed.

Lemma Lookup_Relate_inv :
  forall a b (f : forall a : A, B a -> forall a' : A, B a' -> Prop) r,
    Lookup (a:=a) b (Relate f r)
      -> exists a' b', f a' b' a b /\ Lookup (a:=a') b' r.
Proof. firstorder. Qed.

(* Lemma Lookup_Move : forall k a a' e r, *)
(*   (IF k = a' *)
(*    then Lookup (a:=a) e r *)
(*    else k <> a /\ Lookup (a:=k) e r) *)
(*     -> Lookup (a:=k) e (Move a a' r). *)
(* Proof. firstorder. Qed. *)

(* Lemma Lookup_Move_inv : forall k a a' e r, *)
(*   Lookup (a:=k) e (Move a a' r) *)
(*     -> (k = a' /\ Lookup (a:=a) e r) \/ (k <> a /\ Lookup k e r). *)
(* Proof. *)
(*   firstorder; *)
(*   simpl in *; subst; *)
(*   firstorder. *)
(* Qed. *)

Lemma Lookup_Map : forall a b f r,
  (exists b', f a b' = b /\ Lookup (a:=a) b' r) -> Lookup (a:=a) b (Map f r).
Proof. firstorder. Qed.

Lemma Lookup_Map_inv : forall a b f r,
  Lookup (a:=a) b (Map f r) -> exists b', f a b' = b /\ Lookup (a:=a) b' r.
Proof.
  intros.
  inversion H; clear H.
  firstorder.
Qed.

Lemma dep_surjective_pairing : forall A (B : A -> Type) (x : sigT B),
  x = existT (fun a : A => B a) (projT1 x) (projT2 x).
Proof.
  intros.
  destruct x; simpl.
  apply eq_dep_eq_sigT.
  constructor.
Qed.

Lemma Lookup_Map_set : forall a b f r,
  (exists p', f p' = (existT _ a b) /\ Lookup (a:=projT1 p') (projT2 p') r)
    -> Lookup (a:=a) b (Map_set f r).
Proof.
  unfold Map_set, Lookup, Ensembles.In; simpl.
  intuition.
  do 2 destruct H.
  exists x.
  rewrite <- dep_surjective_pairing in H0.
  intuition.
Qed.

Lemma Lookup_Map_set_inv : forall a b f r,
  Lookup (a:=a) b (Map_set f r)
    -> exists p', f p' = (existT _ a b) /\ Lookup (a:=projT1 p') (projT2 p') r.
Proof.
  intros.
  inversion H; clear H.
  exists x.
  unfold Lookup.
  rewrite <- dep_surjective_pairing.
  firstorder.
Qed.

Lemma Lookup_Filter : forall a b P r,
  Lookup (a:=a) b r /\ P a b -> Lookup (a:=a) b (Filter P r).
Proof. firstorder. Qed.

Lemma Lookup_Filter_inv : forall a b P r,
  Lookup (a:=a) b (Filter P r) -> P a b /\ Lookup (a:=a) b r.
Proof. firstorder. Qed.

Lemma Lookup_Union : forall a b r r',
  Lookup (a:=a) b r \/ Lookup (a:=a) b r'
    -> Lookup (a:=a) b (Union (sigT B) r r').
Proof.
  firstorder.
    left; exact H.
  right; exact H.
Qed.

Lemma Lookup_Union_inv : forall a b r r',
  Lookup (a:=a) b (Union (sigT B) r r')
    -> Lookup (a:=a) b r \/ Lookup (a:=a) b r'.
Proof.
  firstorder.
  unfold Lookup, Ensembles.In in *.
  apply Constructive_sets.Union_inv in H.
  intuition.
Qed.

Lemma Lookup_Define : forall a b c P r,
  (IF P a then In _ (Singleton _ (c _)) b else Lookup (a:=a) b r)
    -> Lookup (a:=a) b (Define P c r).
Proof.
  unfold Define; intros.
  apply Lookup_Union.
  do 2 destruct H.
    left.
    unfold Lookup, Ensembles.In; simpl.
    intuition.
  right.
  apply Lookup_Filter.
  intuition.
Qed.

Lemma Lookup_Define_inv : forall a b c P r,
  Lookup (a:=a) b (Define P c r)
    -> IF P a
       then In _ (Singleton _ (c _)) b
       else Lookup (a:=a) b r.
Proof.
  unfold Define; intros.
  apply Lookup_Union_inv in H.
  destruct H.
    firstorder.
  apply Lookup_Filter_inv in H.
  firstorder.
Qed.

Lemma Lookup_Modify :
  forall (a : A) (b : B a) a' (f : forall a : A, B a -> B a) r,
    (a = a' /\ exists b', eq_dep A B a b a' (f a' b') /\ Lookup (a:=a') b' r)
      \/ (a <> a' /\ Lookup (a:=a) b r)
      -> Lookup (a:=a) b (Modify a' f r).
Proof. firstorder. Qed.

Lemma Lookup_Modify_inv :
  forall (a : A) (b : B a) a' (f : forall a : A, B a -> B a) r,
    Lookup (a:=a) b (Modify a' f r)
      -> (a = a' /\ exists b', eq_dep A B a b a' (f a' b')
                                 /\ Lookup (a:=a') b' r)
           \/ (a <> a' /\ Lookup (a:=a) b r).
Proof.
  firstorder;
  simpl in *; subst.
    left; intuition.
    exists x0.
    intuition.
  right; intuition.
  destruct H2.
  exact H.
Qed.

Lemma Lookup_Member : forall a b r,
  Lookup (a:=a) b r -> Member a r.
Proof. firstorder. Qed.

Lemma Member_Lookup_not : forall a r,
  ~ Member a r -> forall b, ~ Lookup (a:=a) b r.
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
  All P (Remove a r) -> forall a' b', a' <> a -> Lookup (a:=a') b' r -> P a' b'.
Proof. intros; apply H, Lookup_Remove; trivial. Qed.

End TupleEnsemble.

Arguments Functional : default implicits.
Arguments Empty {_ _} _.
Arguments Single : default implicits.
Arguments Insert : default implicits.
Arguments Remove : default implicits.
Arguments Update : default implicits.
Arguments Modify : default implicits.
(* Arguments Move : default implicits. *)
Arguments Filter : default implicits.
Arguments Map : default implicits.
Arguments Relate : default implicits.
Arguments All : default implicits.
Arguments Any : default implicits.
Arguments Define : default implicits.
Arguments Lookup : default implicits.
Arguments Same : default implicits.
Arguments Member : default implicits.

Arguments Lookup_Empty : default implicits.

Ltac t H :=
  unfold Relate;
  split; intros;
  repeat destruct H;
  simpl in *; subst;
  firstorder;
  simpl in *; subst;
  firstorder;
  try match goal with
    [ H0 : eq_dep _ _ _ _ _ _ |- _ ] => destruct H0; assumption
  end.

Lemma Relate_left_identity : forall A (B : A -> Type) (r : DMap B),
  Same r (Relate (eq_dep A B) r).
Proof. t H. Qed.

Lemma Relate_right_identity : forall A (B : A -> Type) (r : DMap B),
  Same (Relate (eq_dep A B) r) r.
Proof. t H. Qed.

Lemma Relate_composition :
  forall A B C D E F
         (f : forall c : C, D c -> forall e : E, F e -> Prop)
         (g : forall a : A, B a -> forall c : C, D c -> Prop) r,
    Same (Relate (fun k e k' e' =>
                  exists k'' e'', g k e k'' e'' /\ f k'' e'' k' e') r)
         (Relate f (Relate g r)).
Proof. t H; exists x1; exists x2; t H. Qed.

Ltac teardown :=
  match goal with
  | [ H : Lookup _ _ Empty            |- _ ] => contradiction (Lookup_Empty H)
  | [ H : Lookup _ _ (Single _ _)     |- _ ] => apply Lookup_Single_inv in H
  | [ H : Lookup _ _ (Insert _ _ _ _) |- _ ] => apply Lookup_Insert_inv in H
  | [ H : Lookup _ _ (Remove _ _)     |- _ ] => apply Lookup_Remove_inv in H
  | [ H : Lookup _ _ (Update _ _ _)   |- _ ] => apply Lookup_Update_inv in H
  (* | [ H : Lookup _ _ (Move _ _ _)     |- _ ] => apply Lookup_Move_inv in H *)
  | [ H : Lookup _ _ (Map _ _)        |- _ ] => apply Lookup_Map_inv in H
  | [ H : Lookup _ _ (Map_set _ _)    |- _ ] => apply Lookup_Map_set_inv in H
  | [ H : Lookup _ _ (Relate _ _)     |- _ ] => apply Lookup_Relate_inv in H
  | [ H : Lookup _ _ (Filter _ _)     |- _ ] => apply Lookup_Filter_inv in H
  | [ H : Lookup _ _ (Define _ _ _)   |- _ ] => apply Lookup_Define_inv in H
  | [ H : Lookup _ _ (Modify _ _ _)   |- _ ] => apply Lookup_Modify_inv in H
  | [ H : Lookup _ _ (Union _ _ _)    |- _ ] => apply Lookup_Union_inv in H

  | [ H : Member _ Empty            |- _ ] => unfold Member in H
  | [ H : Member _ (Single _ _)     |- _ ] => unfold Member in H
  | [ H : Member _ (Insert _ _ _ _) |- _ ] => unfold Member in H
  | [ H : Member _ (Remove _ _)     |- _ ] => unfold Member in H
  | [ H : Member _ (Update _ _ _)   |- _ ] => unfold Member in H
  (* | [ H : Member _ (Move _ _ _)     |- _ ] => unfold Member in H *)
  | [ H : Member _ (Map _ _)        |- _ ] => unfold Member in H
  | [ H : Member _ (Map_set _ _)    |- _ ] => unfold Member in H
  | [ H : Member _ (Relate _ _)     |- _ ] => unfold Member in H
  | [ H : Member _ (Filter _ _)     |- _ ] => unfold Member in H
  | [ H : Member _ (Define _ _ _)   |- _ ] => unfold Member in H
  | [ H : Member _ (Modify _ _ _)   |- _ ] => unfold Member in H
  | [ H : Member _ (Union _ _ _)    |- _ ] => unfold Member in H

  | [ |- Lookup _ _ Empty            ] => apply Lookup_Empty
  | [ |- Lookup _ _ (Single _ _)     ] => apply Lookup_Single
  | [ |- Lookup _ _ (Insert _ _ _ _) ] => apply Lookup_Insert
  | [ |- Lookup _ _ (Remove _ _)     ] => apply Lookup_Remove
  | [ |- Lookup _ _ (Update _ _ _)   ] => apply Lookup_Update
  (* | [ |- Lookup _ _ (Move _ _ _)     ] => apply Lookup_Move *)
  | [ |- Lookup _ _ (Map _ _)        ] => apply Lookup_Map
  | [ |- Lookup _ _ (Map_set _ _)    ] => apply Lookup_Map_set
  | [ |- Lookup _ _ (Relate _ _)     ] => apply Lookup_Relate
  | [ |- Lookup _ _ (Filter _ _)     ] => apply Lookup_Filter
  | [ |- Lookup _ _ (Define _ _ _)   ] => apply Lookup_Define
  | [ |- Lookup _ _ (Modify _ _ _)   ] => apply Lookup_Modify
  | [ |- Lookup _ _ (Union _ _ _)    ] => apply Lookup_Union

  | [ H : Lookup ?X ?Y ?R |- Member ?X ?R ] => exists Y; exact H

  | [ H1 : All ?P ?R, H2 : Lookup ?X ?Y ?R |- _ ] =>
    specialize (H1 _ _ H2); simpl in H1

  | [ H : IF _ then _ else _ |- _ ] => destruct H
  | [ H : _ /\ _             |- _ ] => destruct H
  | [ H : _ \/ _             |- _ ] => destruct H
  | [ H : _ * _              |- _ ] => destruct H
  | [ H : exists _, _        |- _ ] => destruct H
  | [ H : @sig _ _           |- _ ] => destruct H
  | [ H : @sig2 _ _ _        |- _ ] => destruct H
  | [ H : @sigT _ _          |- _ ] => destruct H
  | [ H : @sigT2 _ _ _       |- _ ] => destruct H
  | [ H : bool               |- _ ] => destruct H
  | [ H : option _           |- _ ] => destruct H
  | [ H : sum _ _            |- _ ] => destruct H
  | [ H : sumor _ _          |- _ ] => destruct H
  | [ H : sumbool _ _        |- _ ] => destruct H

  | [ H : forall x, Some ?X = Some x -> _  |- _ ] => specialize (H X eq_refl)
  | [ H : forall x y, Some (?X, ?Y) = Some (x, y) -> _  |- _ ] =>
    specialize (H X Y eq_refl)

  | [ H1 : ?X = true, H2 : ?X = false |- _ ] => rewrite H1 in H2; discriminate

  end; simpl in *; try tauto.
