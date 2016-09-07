Require Export
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.Relations.Relation_Definitions
  Coq.Setoids.Setoid.

Generalizable All Variables.

Class LogicalRelation {A B} (R : A -> B -> Prop) (m : A) (m' : B) := {
  logical_prf : R m m'
}.

Definition related_hetero
           (A B : Type)
           (C : A -> Type) (D : B -> Type)
           (R : A -> B -> Prop)
           (R' : forall (x : A) (y : B), C x -> D y -> Prop) :
  (forall x : A, C x) -> (forall x : B, D x) -> Prop :=
  fun f g => forall x y, R x y -> R' x y (f x) (g y).

Definition related {A B C D} (R : A -> B -> Prop) (R' : C -> D -> Prop)  :
  (A -> C) -> (B -> D) -> Prop :=
  Eval compute in @related_hetero A B (fun _ => C) (fun _ => D)
                                  R (fun _ _ => R').

Class Extranatural {A B C D} (R : A -> B -> Prop) (S : C -> D -> Prop) := {
  transformX : forall (a : A) (b : B) (c : C) (d : D), R a b -> S c d(* ; *)
  (* extranaturality : forall (f : A -> C) (g : B -> D), *)
}.

(** Notations reminiscent of the old syntax for declaring morphisms. *)
Delimit Scope lsignature_scope with lsignature.

Arguments LogicalRelation {A}%type {B}%type R%lsignature m m'.
Arguments related {A B C D}%type (R R')%lsignature _ _.

Module LogicalRelationNotations.

  Notation " R ++> R' " := (@related _ _ _ _ (R%lsignature) (R'%lsignature))
    (right associativity, at level 55) : lsignature_scope.

  Notation " R ==> R' " := (@related _ _ _ _ (R%lsignature) (R'%lsignature))
    (right associativity, at level 55) : lsignature_scope.

  Notation " R --> R' " := (@related _ _ _ _ (Basics.flip (R%lsignature)) (R'%lsignature))
    (right associativity, at level 55) : lsignature_scope.

  Notation "f [R  rel ] f'" := (LogicalRelation rel f f')
    (right associativity, at level 55) : lsignature_scope.

End LogicalRelationNotations.

Export LogicalRelationNotations.

Local Open Scope lsignature_scope.

Arguments LogicalRelation : default implicits.

Program Instance Equality_LogicalRelation : forall A (x : A),
  x [R eq] x.

Definition boolR (P : Prop) (b : bool) : Prop := P <-> b = true.

Definition optionP {A} (P : relation A) : relation (option A) :=
  fun x y => match x, y with
             | Some x', Some y' => P x' y'
             | None, None => True
             | _, _ => False
             end.

Program Instance optionP_Equivalence {A} (P : relation A) :
  Equivalence P -> Equivalence (optionP P).
Obligation 1.
  intro x.
  destruct x; simpl; trivial.
  reflexivity.
Qed.
Obligation 2.
  intros x y Heq.
  destruct x, y; simpl in *; trivial.
  intuition.
Qed.
Obligation 3.
  intros x y z Heq1 Heq2.
  destruct x, y, z; simpl in *; auto;
  firstorder.
Qed.

Definition pairP {A B} (P : relation A) (Q : relation B) : relation (A * B) :=
  fun p p' => match p, p' with
              | (x, y), (x', y') => P x x' /\ Q y y'
              end.

Program Instance pairP_Equivalence {A B} (P : relation A) (Q : relation B) :
  Equivalence P -> Equivalence Q -> Equivalence (pairP P Q).
Obligation 1.
  intro x.
  destruct x; simpl.
  intuition.
Qed.
Obligation 2.
  intros x y Heq.
  destruct x, y; simpl in *.
  intuition.
Qed.
Obligation 3.
  intros x y z Heq1 Heq2.
  destruct x, y, z; simpl in *.
  firstorder.
Qed.

Ltac relational :=
  repeat match goal with
  | [ |- LogicalRelation _ _ _ ] => constructor
  | [ |- Proper _ _ ] => intros ???
  | [ |- related _ _ _ _ ] => intros ???
  | [ |- respectful _ _ _ _ ] => intros ???
  | [ |- iff _ _ ] => split; intro
  end; subst; auto.
