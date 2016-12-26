Ltac inv H := inversion H; subst; clear H.

Tactic Notation "by" tactic(H) :=
  H; first [ tauto
           | discriminate
           | auto
           | congruence
           | eauto
           | intuition
           | firstorder ].

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
