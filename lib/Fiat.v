Require Export
  Fiat.ADT
  Fiat.ADTNotation
  ByteString.Lib.ADTInduction
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Tactic Notation "refine" "method" constr(name) :=
  match goal with
    | [ _ : constructorType ?A (consDom {| consID := name
                                         ; consDom := _ |}) |- _ ] =>
      idtac
    | [ _ : methodType ?A (methDom {| methID := name
                                    ; methDom := _
                                    ; methCod := _ |})  _ |- _ ] =>
      idtac
    | _ =>
      fail "Incorrect method name"
  end.

Ltac destruct_computations :=
  repeat match goal with
  | [ H : computes_to (Bind _ _) _     |- _ ] =>
    let H0 := fresh "H0" in
    apply Bind_inv in H; destruct H as [? [? H0]]
  | [ H : computes_to (Pick _) _       |- _ ] =>
    apply Pick_inv in H
  | [ H : computes_to (Return _) _     |- _ ] =>
    apply Return_inv in H; subst
  | [ H : computes_to _ _ |- _ ] =>
    let H0 := fresh "H0" in
    first [ apply Bind_inv in H; destruct H as [? [? H0]]
          | apply Pick_inv in H
          | apply Return_inv in H; subst ]
  end.

Lemma refineEquiv_If_Then_Else_Bind :
  forall (A B : Type) (i : bool) (t e : Comp A) (b : A -> Comp B),
    refineEquiv (a <- If i Then t Else e; b a)
                (If i Then a <- t; b a Else (a <- e; b a)).
Proof. split; intros; destruct i; reflexivity. Qed.

Lemma refine_If_Then_Else_bool :
  forall (b : bool) A cpst cpse (res : Comp A),
    (if b then refine cpst res else refine cpse res)
      <-> refine (If b Then cpst Else cpse) res.
Proof. split; intros; destruct b; auto. Qed.

Ltac fracture H :=
  repeat (
    try simplify with monad laws; simpl;
    match goal with
    | [ |- refine (If ?B Then ?T Else ?E) _ ] =>
      apply refine_If_Then_Else; [ fracture H | fracture H ]
    | [ |- refine (If ?B Then ?T Else ?E) _ ] =>
      subst H; apply refine_If_Then_Else; [ fracture H | fracture H ]
    | [ |- refine (x <- If ?B Then ?T Else ?E; _) _ ] =>
      rewrite refineEquiv_If_Then_Else_Bind
    | [ |- _ ] => idtac
    end).

Corollary refine_computes_to {A} {c : Comp A} {v} : c ↝ v -> refine c (ret v).
Proof. intros ?? H0; destruct H0; assumption. Qed.

Corollary computes_to_refine {A} {c : Comp A} {v} : refine c (ret v) -> c ↝ v.
Proof. intuition. Qed.

Corollary refine_pick_ret : forall A x,
  refine {a : A | ret x ↝ a} (ret x).
Proof. intuition. Qed.

Corollary refine_inv : forall A old new,
  refine old new -> forall x : A, new ↝ x -> old ↝ x.
Proof. trivial. Qed.

Lemma fst_match_list :
  forall A (xs : list A) B z C z'
         (f : A -> list A -> B) (f' : A -> list A -> C),
    fst match xs with
        | List.nil => (z, z')
        | List.cons x xs => (f x xs, f' x xs)
        end = match xs with
              | List.nil => z
              | List.cons x xs => f x xs
              end.
Proof. induction xs; auto. Qed.

Lemma snd_match_list :
  forall A (xs : list A) B z C z'
         (f : A -> list A -> B) (f' : A -> list A -> C),
    snd match xs with
        | List.nil => (z, z')
        | List.cons x xs => (f x xs, f' x xs)
        end = match xs with
              | List.nil => z'
              | List.cons x xs => f' x xs
              end.
Proof. induction xs; auto. Qed.

Lemma If_Then_Else_fst : forall p A B (a b : A * B),
  fst (If p Then a Else b) = If p Then (fst a) Else (fst b).
Proof. intros; destruct p; trivial. Qed.

Lemma If_Then_Else_snd : forall p A B (a b : A * B),
  snd (If p Then a Else b) = If p Then (snd a) Else (snd b).
Proof. intros; destruct p; trivial. Qed.

Lemma If_Then_Else_pair : forall p A (a b : A) B (c d : B),
  (If p Then a Else b, If p Then c Else d)
    = If p Then (a, c) Else (b, d).
Proof. intros; destruct p; trivial. Qed.

Lemma Ifopt_Then_Else_fst : forall C p A B (a : C -> A * B) (b : A * B),
  fst (Ifopt p as x Then a x Else b) = Ifopt p as x Then (fst (a x)) Else (fst b).
Proof. intros; destruct p; trivial. Qed.

Lemma Ifopt_Then_Else_snd : forall C p A B (a : C -> A * B) (b : A * B),
  snd (Ifopt p as x Then a x Else b) = Ifopt p as x Then (snd (a x)) Else (snd b).
Proof. intros; destruct p; trivial. Qed.

Lemma Ifopt_Then_Else_pair :
  forall C p A (a : C -> A) (b : A) B (c : C -> B) (d : B),
    (Ifopt p as x Then a x Else b, Ifopt p as x Then c x Else d)
      = Ifopt p as x Then (a x, c x) Else (b, d).
Proof. intros; destruct p; trivial. Qed.
