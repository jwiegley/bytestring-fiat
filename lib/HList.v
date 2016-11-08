Require Import
  Coq.Lists.List.

Generalizable All Variables.

Import ListNotations.

(****************************************************************************
 * hlist: Type heterogeneous list indexed by a list.
 ****************************************************************************)

Inductive hlist : list Type -> Type :=
  | HNil : hlist []
  | HCons : forall t ts, t -> hlist ts -> hlist (t :: ts).

Arguments HNil : default implicits.
Arguments HCons : default implicits.

Lemma cons_head_eq : forall A (x0 : A) x1 y0 y1,
  x0 :: y0 = x1 :: y1 -> x0 = x1.
Proof.
  intros.
  inversion H.
  intuition.
Defined.

Lemma cons_tail_eq : forall A (x0 : A) x1 y0 y1,
  x0 :: y0 = x1 :: y1 -> y0 = y1.
Proof.
  intros.
  inversion H.
  intuition.
Defined.

Import EqNotations.

Program Definition hlist_head `(l : hlist (t :: ts)) : t :=
  match l in hlist d return d = t :: ts -> t with
  | HNil => fun _ => False_rect _ _
  | HCons x _ => fun H => rew (cons_head_eq _ _ _ _ _ H) in x
  end eq_refl.

Program Definition hlist_tail `(l : hlist (t :: ts)) : hlist ts :=
  match l in hlist d return d = t :: ts -> hlist ts with
  | HNil => fun _ => False_rect _ _
  | HCons _ xs => fun H => rew (cons_tail_eq _ _ _ _ _ H) in xs
  end eq_refl.
