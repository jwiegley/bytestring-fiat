Ltac inv H := inversion H; subst; clear H.

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
