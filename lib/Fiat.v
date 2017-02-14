Require Export
  Fiat.ADT
  Fiat.ADTNotation
  ByteString.Lib.ADTInduction
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Definition getADTSig {sig : DecoratedADTSig} : ADT sig -> DecoratedADTSig :=
  fun _ => sig.

Tactic Notation "refine" "method" constr(name) :=
  match goal with
  | [ _ : methodType ?A (methDom {| methID := name
                                    ; methArity := _
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

Definition IfDep_Then_Else (c : bool) {A} (t : c = true -> A) (e : c = false -> A) : A.
Proof.
  destruct c.
    apply t.
    reflexivity.
  apply e.
  reflexivity.
Defined.

Notation "'IfDep' c 'Then' t 'Else' e" := (@IfDep_Then_Else c _ t e) (at level 100).

Lemma refine_IfDep_Then_Else_bool :
  forall (b : bool) A cpst cpse (res : Comp A),
    (if b as b0 return b = b0 -> Prop
     then fun H => refine (cpst H) res
     else fun H => refine (cpse H) res) eq_refl
      <-> refine (IfDep b Then cpst Else cpse) res.
Proof. split; intros; destruct b; auto. Qed.

Lemma refine_IfDep_Then_Else :
  forall (A : Type) (c : bool)
         (tx ty : c = true -> Comp A),
    (forall H : c = true, refine (tx H) (ty H)) ->
    forall ex ey : c = false -> Comp A,
      (forall H : c = false, refine (ex H) (ey H)) ->
      refine (IfDep c Then tx Else ex) (IfDep c Then ty Else ey).
Proof.
  intros. destruct c; simpl; auto; reflexivity.
Qed.

Lemma refineEquiv_IfDep_Then_Else :
  forall (A : Type) (c : bool)
         (tx ty : c = true -> Comp A),
    (forall H : c = true, refineEquiv (tx H) (ty H)) ->
    forall ex ey : c = false -> Comp A,
      (forall H : c = false, refineEquiv (ex H) (ey H)) ->
      refineEquiv (IfDep c Then tx Else ex) (IfDep c Then ty Else ey).
Proof.
  intros. destruct c; simpl; auto; reflexivity.
Qed.

Lemma refineEquiv_strip_IfDep_Then_Else : forall (c : bool) A (t e : Comp A),
  refineEquiv (IfDep c Then fun _ => t Else fun _ => e)
              (If c Then t Else e).
Proof. intros. destruct c; simpl; reflexivity. Qed.

Lemma refine_IfDep_Then_Else_Bind:
  forall (A B : Type) (i : bool)
         (t : i = true -> Comp A) (e : i = false -> Comp A)
         (b : A -> Comp B),
  refine (a <- IfDep i Then t Else e;
          b a) (IfDep i
                Then fun H => a <- t H; b a
                Else fun H => (a <- e H; b a)).
Proof.
  intros. destruct i; simpl; auto; reflexivity.
Qed.

Lemma refineEquiv_IfDep_Then_Else_Bind:
  forall (A B : Type) (i : bool)
         (t : i = true -> Comp A) (e : i = false -> Comp A)
         (b : A -> Comp B),
  refineEquiv (a <- IfDep i Then t Else e;
               b a) (IfDep i
                     Then fun H => a <- t H; b a
                     Else fun H => (a <- e H; b a)).
Proof.
  intros. destruct i; simpl; auto; reflexivity.
Qed.

Lemma IfDep_Then_Else_fun_Proper A :
  Proper (forall_relation
            (fun b : bool =>
               (pointwise_relation _ eq ==>
                pointwise_relation _ eq ==> eq)%signature))
         (fun b t e => @IfDep_Then_Else b A t e).
Proof.
  intros ???????.
  destruct a; simpl; [apply H | apply H0 ].
Qed.

Corollary strip_IfDep_Then_Else :
  forall (c : bool) (A : Type) (t e : A),
  (IfDep c Then fun _ : c = true => t Else (fun _ : c = false => e)) =
    If c Then t Else e.
Proof. destruct c; trivial. Qed.

Lemma refineEquiv_If_Then_Else :
  forall (A : Type) (c : bool) (x y : Comp A),
    refineEquiv x y ->
    forall x0 y0 : Comp A, refineEquiv x0 y0 ->
    refineEquiv (If c Then x Else x0) (If c Then y Else y0).
Proof. intros; destruct c; auto. Qed.

Lemma refine_skip2 {B} (dummy : Comp B) {A} (a : Comp A) :
  refine a (dummy >> a).
Proof.
  repeat first [ intro
               | computes_to_inv
               | assumption
                 | econstructor; eassumption
                 | econstructor; try eassumption; [] ].
  eauto.
Qed.

Class RefineUnder {A : Type} (a a' : Comp A) := {
  rewrite_under : refine a a'
}.

Instance RefineUnder_Bind {A B : Type}
         (ca ca' : Comp A)
         (b b' : A -> Comp A)
         (refine_a : refine ca ca')
         (refine_b : forall a, ca ↝ a -> refine (b a) (b' a)) :
  RefineUnder (a <- ca; b a) (a' <- ca'; b' a') :=
  {| rewrite_under := refine_under_bind_both b b' refine_a refine_b |}.

Definition refine_skip2_pick {B} (dummy : Comp B) {A} (P : A -> Prop) :
  refine {a | P a} (dummy >> {a | P a}) := @refine_skip2 _ _ _ _.

Definition refine_skip2_bind {B} (dummy : Comp B)
           {A C} (ca : Comp A) (k : A -> Comp C) :
  refine (ca >>= k) (dummy >> (ca >>= k)) := @refine_skip2 _ _ _ _.

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

Ltac if_computes_to_inv :=
  match goal with
    [ H : (If ?B Then _ Else _) ↝ _ |- _ ] =>
    let Heqe := fresh "Heqe" in
    destruct B eqn:Heqe;
    simpl in H;
    computes_to_inv
  end.

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
