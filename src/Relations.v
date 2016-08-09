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

Ltac relational :=
  repeat match goal with
  | [ |- Proper _ _ ] => intros ???
  | [ |- related _ _ _ _ ] => intros ???
  | [ |- respectful _ _ _ _ ] => intros ???
  | [ |- iff _ _ ] => split; intro
  end; subst; auto.
