Require Export
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Relation_Definitions.

Class LogicalRelation {A B} (R : A -> B -> Prop) (m : A) (m' : B) := {
  logical_prf : R m m'
}.

Class LogicalImpl {A B} (R : A -> B -> Prop)
      (eqv : relation B) (m : A) (m' : B) := {
  impl_logical_rel :> LogicalRelation R m m';
  forward_impl : forall a b c, R a b -> R a c -> eqv b c
}.

Class LogicalDep {A B} (R : A -> B -> Prop)
      (dep : relation A) (m : A) (m' : B) := {
  dep_logical_rel :> LogicalRelation R m m';
  reverse_impl : forall a b c, R a c -> R b c -> dep a b
}.

Definition related_hetero
           (A B : Type)
           (C : A -> Type) (D : B -> Type)
           (R : A -> B -> Prop)
           (R' : forall (x : A) (y : B), C x -> D y -> Prop) :
  (forall x : A, C x) -> (forall x : B, D x) -> Prop :=
  fun f g => forall x y, R x y -> R' x y (f x) (g y).

Definition related {A B C D} (R : A -> B -> Prop)
           (R' : C -> D -> Prop) : (A -> C) -> (B -> D) -> Prop :=
  Eval compute in @related_hetero A B (fun _ => C) (fun _ => D) R (fun _ _ => R').

(** Notations reminiscent of the old syntax for declaring morphisms. *)
Delimit Scope lsignature_scope with lsignature.

Module LogicalRelationNotations.

  Notation " R +++> R' " := (@related _ _ _ _ (R%lsignature) (R'%lsignature))
    (right associativity, at level 55) : lsignature_scope.

  Notation " R ===> R' " := (@related _ _ _ _ (R%lsignature) (R'%lsignature))
    (right associativity, at level 55) : lsignature_scope.

  Notation " R ---> R' " := (@related _ _ _ _ (Basics.flip (R%lsignature)) (R'%lsignature))
    (right associativity, at level 55) : lsignature_scope.

  Notation "f [R  rel ] f'" := (LogicalRelation rel f f')
    (right associativity, at level 55) : lsignature_scope.

End LogicalRelationNotations.

Arguments LogicalRelation {A}%type {B}%type R%lsignature m m'.
Arguments related {A B C D}%type (R R')%lsignature _ _.

Export LogicalRelationNotations.

Local Open Scope lsignature_scope.

Arguments LogicalRelation : default implicits.

Program Instance Equality_LogicalRelation : forall A (x : A),
  x [R eq] x.

Definition boolR (P : Prop) (b : bool) : Prop := P <-> b = true.
