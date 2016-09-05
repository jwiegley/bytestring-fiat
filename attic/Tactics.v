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
  (* | [ |- context [Ifdec_Then_Else ?P ?T ?E] ]  => unfold Ifdec_Then_Else *)
  end.

Ltac simplify_ensembles :=
  repeat (single_reduction; simpl; destruct_ex);
  try solve [ intuition | constructor ].

Require Import
  Fiat.ADT
  Fiat.ADTNotation.

Tactic Notation "refine" "method" constr(name) :=
  match goal with
    | [ _ : constructorType ?A (consDom {| consID := name
                                         ; consDom := _ |}) |- _ ] =>
      idtac "Constructor"
    | [ _ : methodType ?A (methDom {| methID := name
                                    ; methDom := _
                                    ; methCod := _ |})  _ |- _ ] =>
      idtac "Method"
    | _ =>
      fail "Incorrect method name"
  end.

Require Import
  Coq.Sets.Ensembles
  Fiat.ADT
  Fiat.ADTNotation
  FunctionalExtensionality.

Axiom prop_ext : forall (P Q : Prop), (P <-> Q) -> P = Q.

Ltac shatter :=
  unfold id in *;
  repeat
    match goal with
    | [ H : and _ _            |- _                 ] => destruct H
    | [ H : Bind _ _ _         |- _                 ] => destruct H
    | [ H : In _ _ _           |- _                 ] => destruct H
    | [ H : Datatypes.prod _ _ |- _                 ] => destruct H
    | [                        |- and _ _           ] => split
    | [                        |- Bind _ _ _        ] => eexists
    | [                        |- In _ _ _          ] => constructor
    | [                        |- In _ _ _          ] => solve [ eauto ]
    | [                        |- In _ (Bind _ _) _ ] => eexists
    | [                        |- In _ _ _          ] => econstructor
    end;
  simpl in *.

(** Until the FunctorLaws are expressed in terms of some arbitrary
    equivalence, we need to use functional and propositional
    extensionality. *)

Ltac simplify_comp :=
  repeat let x := fresh "x" in extensionality x;
  try (apply prop_ext; split; intros);
  repeat shatter;
  try constructor; eauto.

Ltac zoom T :=
  let Ty := type of T in
  let U := fresh "U" in evar (U : Ty);
  let H := fresh "H" in assert (T = U) as H;
    [ subst U | setoid_rewrite H; clear H; unfold U; clear U ].

Ltac shift tac := etransitivity; [apply tac|].

Lemma surjective_pairing_r : forall A B (x : A * B),
  (fst x, snd x) = x.
Proof.
  intros.
  destruct x; reflexivity.
Qed.

Ltac adjust term :=
  let T := constr:term in
  assert { T' : _ & T = T'} as T'; [eexists| apply (projT1 T')].

Require Import
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Tactic Notation "refine" "method" constr(name) :=
  match goal with
    | [ _ : constructorType ?A (consDom {| consID := name
                                         ; consDom := _ |}) |- _ ] =>
      idtac "Constructor"
    | [ _ : methodType ?A (methDom {| methID := name
                                    ; methDom := _
                                    ; methCod := _ |})  _ |- _ ] =>
      idtac "Method"
    | _ =>
      fail "Incorrect method name"
  end.

Ltac finish_concrete :=
  match goal with
  | [ |- context[Pick _] ] => idtac
  | _ => finish honing
  end.

Ltac simplify_ADT :=
  try simplify with monad laws; simpl;
  try match goal with
    [ H : _ = _ |- _ ] =>
    rewrite H; clear H
  end;
  try refine pick eq;
  try refine pick val tt; try tauto;
  try simplify with monad laws;
  try finish_concrete.

Lemma refineEquiv_If_Then_Else_Bind :
  forall (A B : Type) (i : bool) (t e : Comp A) (b : A -> Comp B),
    refineEquiv (a <- If i Then t Else e; b a)
                (If i Then a <- t; b a Else (a <- e; b a)).
Proof. split; intros; destruct i; reflexivity. Qed.

Theorem refine_If_Then_Else_bool :
  forall (b : bool) A cpst cpse (res : Comp A),
    (if b then refine cpst res else refine cpse res)
      <-> refine (If b Then cpst Else cpse) res.
Proof. split; intros; destruct b; auto. Qed.

Lemma refineEquiv_Ifopt_Then_Else_Bind :
  forall A B T (i : option T) (t : T -> Comp A) (e : Comp A) (b : A -> Comp B),
    refineEquiv (a <- Ifopt i as p Then t p Else e; b a)
                (Ifopt i as p Then a <- t p; b a Else (a <- e; b a)).
Proof. split; intros; destruct i; reflexivity. Qed.

Require Import ByteString.Decidable.

Lemma refineEquiv_Ifdec_Then_Else_Bind :
  forall A B `{Decidable i} (t e : Comp A) (b : A -> Comp B),
    refineEquiv (a <- Ifdec i Then t Else e; b a)
                (Ifdec i Then a <- t; b a Else (a <- e; b a)).
Proof.
  intros.
  destruct H.
  unfold Ifdec_Then_Else; simpl.
  destruct Decidable_witness; reflexivity.
Qed.

Lemma refine_ret_ret_eq : forall A (a b : A),
  refine (ret a) (ret b) <-> a = b.
Proof.
  split; intros.
    specialize (H b (ReturnComputes b)).
    apply Return_inv; assumption.
  destruct H.
  reflexivity.
Qed.

Require Import ByteString.TupleEnsembles.

Lemma refine_ret_ret_Same : forall A B (a b : EMap A B),
  refine (ret a) (ret b) <-> Same a b.
Proof.
  split; intros.
    specialize (H b (ReturnComputes b)).
    destruct H.
    reflexivity.
  f_equiv.
  apply Extensionality_Ensembles, Same_Same_set.
  assumption.
Qed.

Lemma refine_ret_ret_fst_Same : forall A (x z : Comp A) B (y w : B),
  Same_set _ x z -> y = w -> refine (ret (x, y)) (ret (z, w)).
Proof.
  intros; subst; f_equiv; f_equal.
  apply Extensionality_Ensembles; assumption.
Qed.

Ltac breakdown :=
  match goal with
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
  end.
