Require Import Hask.Control.Monad.

Generalizable All Variables.

Notation Maybe   := option.
Notation Nothing := None.
Notation Just    := Some.

Definition fromoption `(x : a) (my : option a) : a :=
  match my with
 | Just z  => z
 | Nothing => x
  end.

Definition fold_option `(x : b) `(f : a -> b) (my : option a) : b :=
  match my with
 | Just z  => f z
 | Nothing => x
  end.

Definition option_map `(f : X -> Y) (x : option X) : option Y :=
  match x with
  | Nothing => Nothing
  | Just x' => Just (f x')
  end.

Instance option_Functor : Functor option :=
{ fmap := @option_map
}.

Definition option_apply {X Y} (f : option (X -> Y)) (x : option X) : option Y :=
  match f with
  | Nothing => Nothing
  | Just f' => match x with
    | Nothing => Nothing
    | Just x' => Just (f' x')
    end
  end.

Instance option_Applicative : Applicative option :=
{ is_functor := option_Functor
; pure := @Just
; ap := @option_apply
}.

Definition option_join {X} (x : option (option X)) : option X :=
  match x with
  | Nothing => Nothing
  | Just Nothing => Nothing
  | Just (Just x') => Just x'
  end.

Instance option_Monad : Monad option :=
{ is_applicative := option_Applicative
; join := @option_join
}.

(* jww (2015-06-17): NYI
Ltac simple_solver :=
  intros;
  try extensionality e;
  compute;
  repeat (
    match goal with
    | [ |- context f [match ?X with _ => _ end] ] =>
      is_var X; destruct X; auto
    end);
  auto.

(** By registering our simple_solver as the obligation tactic, all our law
    obligations will be taken care of for us automatically by the Ltac
    scripts above. *)
Obligation Tactic := simple_solver.
*)

Definition isJust {a} (x : option a) := if x then true else false.

Definition option_choose {a} (x y : option a) : option a :=
  match x with
  | Nothing => y
  | Just _  => x
  end.

Instance option_Alternative : Alternative option := {
  empty  := @Nothing;
  choose := @option_choose
  (* some := fun _ x => match x with *)
  (*   | Nothing => Nothing *)
  (*   | Just x => Just [x] *)
  (*   end; *)
  (* many := fun _ x => match x with *)
  (*   | Nothing => Just [] *)
  (*   | Just x => [x] *)
  (*   end *)
}.

Lemma option_choose_spec : forall a (x y : option a),
  isJust (x <|> y) = (isJust x || isJust y)%bool.
Proof.
  intros a x y.
  destruct x; auto.
Qed.