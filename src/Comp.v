Require Export
  Hask.Control.Monad.

Require Import
  Fiat.ADT
  Fiat.ADTNotation.

Program Instance Comp_Functor : Functor Comp := {
  fmap := fun A B f (x : Comp A) => (v <- x; ret (f v))%comp
}.

Program Instance Comp_Applicative : Applicative Comp := {
  pure := fun _ x => (ret x)%comp;
  ap   := fun A B mf mx => (f <- mf; x <- mx; ret (f x))%comp
}.

Program Instance Comp_Alternative : Alternative Comp := {
  empty  := fun A _ => False;
  choose := fun A x y s => x s \/ y s (* jww (2016-01-28): right? *)
}.

Program Instance Comp_Monad : Monad Comp := {
  join := fun A m => (m >>= id)%comp
}.

Module CompLaws.

Require Import Here.Tactics.
Import MonadLaws.

Local Obligation Tactic := simpl; intros; simplify_comp.

Program Instance Comp_FunctorLaws : FunctorLaws Comp.
Program Instance Comp_ApplicativeLaws : ApplicativeLaws Comp.
Program Instance Comp_MonadLaws : MonadLaws Comp.

End CompLaws.

Lemma ret_inj : forall A (x y : A), ret x = ret y -> x = y.
Proof.
  intros.
  assert (forall P Q : Prop, P = Q -> (P <-> Q)) as Heq.
    intros.
    rewrite H0.
    reflexivity.
  pose proof (@equal_f A Prop _ _ H y) as H0.
  apply Heq in H0.
  destruct H0.
  specialize (H1 (Ensembles.In_singleton A y)).
  inversion H1.
  reflexivity.
Qed.

Lemma refineEquiv_fmap_id {A} : refineEquiv (fmap (@id A)) id.
Proof. reflexivity. Qed.

Lemma refineEquiv_fmap_id_x {A x} : refineEquiv (fmap (@id A) x) x.
Proof.
  autorewrite with monad laws.
  reflexivity.
Qed.

Lemma refineEquiv_fmap_comp {A B C} (k : B -> C) (g : A -> B) :
  refineEquiv (fmap k \o fmap g) (fmap (k \o g)).
Proof. reflexivity. Qed.

Lemma refineEquiv_fmap_comp_x {A B C x} (k : B -> C) (g : A -> B) :
  refineEquiv (fmap k (fmap g x)) (fmap (k \o g) x).
Proof.
  autorewrite with monad laws.
  reflexivity.
Qed.

Add Parametric Morphism A B f : (@fmap Comp _ A B f)
  with signature
    ((@refineEquiv A) ==> (@refineEquiv B))
  as refineEquiv_fmap.
Proof.
  intros x y H; simpl.
  rewrite H.
  reflexivity.
Qed.

Add Parametric Morphism A B : (@ap Comp _ A B)
  with signature
    ((@refine (A -> B)) ==> (@refine A) ==> (@refine B))
  as refine_ap.
Proof.
  intros ?? H1 x y H2; simpl.
  rewrite H1.
  intro v; intros.
  do 2 destruct H.
  do 2 destruct H0.
  destruct H3.
  eexists.
  split.
    exact H.
  eexists.
  split.
    rewrite H2.
    exact H0.
  constructor.
Qed.

Require Export Coq.Classes.Morphisms.
Export Coq.Classes.Morphisms.ProperNotations.
Require Export Coq.Classes.SetoidClass.

(* Computations form a setoid over refinement equivalence. *)
Program Instance Comp_Setoid : forall A, Setoid (Comp A) := {
  equiv := refineEquiv;
  setoid_equiv := refineEquiv_Equivalence A
}.

(* Computations and unidirectional refinement form a partial order, where the
   ordering is a subset relation. *)
Program Instance Comp_PreOrder : forall A, PreOrder (@refine A).

(* Computations and their setoid equivalence together form a partial order. *)
Program Instance Comp_PartialOrder :
  forall A, PartialOrder (@refineEquiv A) (@refine A).
Obligation 1. split; intros; apply H. Qed.

(* Based on its being a partial order, we know that it's antisymmetric. *)
Lemma Comp_Antisymmetric :
  forall A, Antisymmetric (Comp A) (@refineEquiv A) (@refine A).
Proof. intros; apply partial_order_antisym, Comp_PartialOrder. Qed.

Notation "p ⊑ q" := (refine q p) (at level 20, only parsing).

Definition galois_connection
  {A} (p : Comp A) (RA : relation A)
  {B} (q : Comp B) (RB : relation B)
  (F : A -> B) (G : B -> A) :=
    forall (a : A), p ↝ a ->
    forall (b : B), q ↝ b ->
    (RB (F a) b <-> RA a (G b)).

Require Import ZArith.

Lemma helper : forall n q, n < Z.to_nat q -> (0 < q)%Z.
Proof.
  intros.
  induction n; simpl.
  - apply Nat2Z.inj_lt in H.
    simpl in H.
    destruct q eqn:Heqe.
    + inversion H.
    + apply Pos2Z.is_pos.
    + inversion H.
  - apply IHn.
    omega.
Qed.

Lemma galois : forall p q, (Z.of_nat p < q)%Z <-> p < Z.to_nat q.
Proof.
  intros; split; intros.
    rewrite <- (Nat2Z.id p).
    apply Z2Nat.inj_lt; omega.
  rewrite <- (Nat2Z.id p) in H.
  apply Z2Nat.inj_lt in H.
  - assumption.
  - omega.
  - apply helper in H.
    omega.
Qed.

Lemma transport_nat_Z : forall (p : Comp nat) (q : Comp Z),
  galois_connection p lt q Z.lt Z.of_nat Z.to_nat.
Proof.
  unfold galois_connection; simpl; intros.
  apply galois.
Qed.

Lemma z_to_nat_pick : forall b e, 0 <= b ->
  refine {z : Z | (Z.of_nat b <= z < Z.of_nat e)%Z}
         (x <- {n : nat | b <= n < e};
          ret (Z.of_nat x)).
Proof.
  unfold refine; intros.
  apply Bind_inv in H0.
  destruct H0.
  destruct H0.
  apply Pick_inv in H0.
  apply Return_inv in H1; subst.
  destruct H0.
  apply PickComputes.
  split; omega.
Qed.

Ltac adjust_refine term :=
  let T := constr:term in
  assert { T' : _ & refine T T'} as T'; [eexists| apply (projT1 T')].

Definition foo_Z : Comp Z :=
  x <- { z : Z | (0  <= z < 10)%Z };
  y <- { z : Z | (10 <= z < 20)%Z };
  z <- { z : Z | (10 <= z < 20)%Z };
  ret (x + y + z)%Z.

Require Import Hask.Control.Monad.Free.
Require Import Coq.Vectors.Vector.
Import VectorNotations.

Inductive Freeified (f : Type -> Type) (a : Type) :
  forall (n : nat), Vector.t Type n -> Type :=
  | Pure' : a -> Freeified f a (nil Type)
  | Join' : forall (t : Type) (n : nat) (ts : Vector.t Type n),
      (t -> Freeified f a ts) -> f t -> Freeified f a (cons Type t _ ts).

Arguments Pure' {f a} _.
Arguments Join' {f a _ n ts} _ _.

Definition example :
  Freeified Comp nat (cons Type Z _ (cons Type Z _ (nil Type))) :=
  Join' (fun x : Z =>
           Join' (fun y : Z =>
                    Pure' (Z.to_nat (x + y)))
                 { z : Z | z = 0%Z })
        { z : Z | z = 0%Z }.

Fixpoint retractified `{Monad f} {n} `(fr : Freeified f a (n:=n) ts) : f a :=
  match fr with
    | Pure' x => pure x
    | Join' _ n ts g h => (h >>= (retractified \o g))%monad
  end.

Eval simpl in retractified example.

Ltac freeify comp :=
  match goal with
    [ |- Freeified Comp ?T ?TS ] =>
    assert { c : Comp T
           & { f : Freeified Comp T TS & refineEquiv (retractified f) c } }
      as freeified
      by (exists comp;
          eexists;
          unfold comp;
          repeat
            match goal with
            | [ |- refineEquiv (retractified _) (Bind ?C _) ] =>
              instantiate (1 := Join' _ C); unfold id; simpl;
              autorewrite with monad laws;
              apply refineEquiv_bind; [ reflexivity |];
              intros ?; unfold id; simpl
            | [ |- refineEquiv (retractified (_ ?X)) (Bind ?C _) ] =>
              instantiate (1 := fun X => Join' _ C); unfold id; simpl;
              autorewrite with monad laws;
              apply refineEquiv_bind; [ reflexivity |];
              intros ?; unfold id; simpl
            | [ |- refineEquiv (retractified _) (Return _) ] =>
              instantiate (1 := fun _ => Pure' _); unfold id; simpl;
              autorewrite with monad laws;
              reflexivity
            end);
    exact (projT1 (projT2 freeified))
  end.

(*
Definition foo_Z_free :
  { n : nat & { TS : Vector.t Type n & Freeified Comp Z TS } }.
Proof.
  eexists.
  eexists.
  freeify foo_Z.
Defined.

Definition foo_Z_free' :=
  Eval compute [foo_Z_free projT1 projT2] in projT2 (projT2 foo_Z_free).
Print foo_Z_free'.
*)

Definition natify (f : Z -> nat) {n} {ts : Vector.t Type n}
  (x : Freeified Comp Z (n:=n) ts) :
  {ts' : Vector.t Type n & Freeified Comp nat (n:=n) ts'}.
Proof.
  induction x.
    exists (nil Type).
    apply Pure'.
    exact (f a).
Abort.

(* Eval compute [natify fmap Free_Functor Free_bind foo_Z_free' comp] *)
(*   in natify Z.to_nat foo_Z_free'. *)

Example foo_nat0 : Comp nat.
Proof.
  adjust_refine (fmap Z.to_nat foo_Z).
  set_evars.
  unfold foo_Z in *; simpl.
  unfold refine; intros.
  eapply BindComputes.
    eapply BindComputes.
    evar (c : Comp nat).
    pose proof (transport_nat_Z c {z : Z | (0 <= z < 10)%Z}).
    unfold galois_connection in H1.
  replace 0%Z with (Z.of_nat 0); trivial.
  replace 10%Z with (Z.of_nat 10); trivial.
  replace 20%Z with (Z.of_nat 20); trivial.
  rewrite z_to_nat_pick; trivial.
Abort.

Example foo_nat0 : Comp nat.
Proof.
  adjust_refine (fmap Z.to_nat foo_Z).
  unfold foo_Z; simpl.
  replace 0%Z with (Z.of_nat 0); trivial.
  replace 10%Z with (Z.of_nat 10); trivial.
  replace 20%Z with (Z.of_nat 20); trivial.
  rewrite z_to_nat_pick; trivial.
  setoid_rewrite (z_to_nat_pick _).
  simplify with monad laws.
  setoid_rewrite <- Nat2Z.inj_add.
Abort.

(* Definition foo_nat0' := *)
(*   Eval compute [foo_nat0 proj1_sig projT1] in foo_nat0. *)
(* Print foo_nat0'. *)

(*
Example foo_nat_bad :
  { c : Comp nat
  | galois_inserted_if (fmap Z.of_nat) (fmap Z.to_nat)
                       (fun z : Z => (0 <= z)%Z) c foo_Z }.
Proof.
  exists (ret 0).
  unfold galois_inserted_if.
  apply transport_nat_Z.
Defined.

Definition foo_nat_bad' :=
  Eval compute [foo_nat_bad proj1_sig projT1] in proj1_sig foo_nat_bad.
Print foo_nat_bad'.
*)

Example foo_nat : Comp nat.
Proof.
  adjust_refine (fmap Z.to_nat foo_Z).
  unfold foo_Z; simpl.
Abort.
(*
  apply transport_nat_Z; simpl.
    intros.
    apply Bind_inv in H.
    do 2 destruct H.
    apply Bind_inv in H0.
    do 2 destruct H0.
    apply Return_inv in H1.
    rewrite <- H1; clear H1.
    apply Pick_inv in H.
    apply Pick_inv in H0.
    abstract omega.
  replace 0%Z with (Z.of_nat 0); trivial.
  replace 10%Z with (Z.of_nat 10); trivial.
  replace 20%Z with (Z.of_nat 20); trivial.
  rewrite z_to_nat_pick; trivial.
  setoid_rewrite (z_to_nat_pick _).
  simplify with monad laws.
  setoid_rewrite <- Nat2Z.inj_add.
  assert (refineEquiv (x0 <- {n : nat | 0 <= n < 10};
                       x1 <- {n : nat | 10 <= n < 20};
                       ret (Z.of_nat (x0 + x1)))
                      (v <- x0 <- {n : nat | 0 <= n < 10};
                            x1 <- {n : nat | 10 <= n < 20};
                            ret (x0 + x1);
                       ret (Z.of_nat v))).
    autorewrite with monad laws.
    reflexivity.
  rewrite H.
  reflexivity.
  Grab Existential Variables.
  abstract omega.
Defined.

Definition foo_nat' := Eval compute [foo_nat proj1_sig projT1] in foo_nat.
Print foo_nat'.
*)
