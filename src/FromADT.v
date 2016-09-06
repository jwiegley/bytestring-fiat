Require Import
  ByteString.Fiat
  ByteString.ADTInduction.

Generalizable All Variables.

Definition get_ctor
           {dSig : DecoratedADTSig}
           (adt : DecoratedADT dSig)
           (idxMap : BoundedIndex (ConstructorNames dSig)
                       -> ConstructorIndex dSig)
           (idx : BoundedIndex (ConstructorNames dSig)) :
  ConstructorIndex dSig :=
  idxMap idx.

Notation ctor_ adt idx :=
  (get_ctor adt (fun idx => ibound (indexb idx)) {| bindex := idx |}).

Notation "adt @@ idx" :=
  (get_ctor adt (fun idx => ibound (indexb idx)) {| bindex := idx |})
  (at level 100).

Lemma refine_constructor_fromADT
      A (c : Comp (A)) (P : A -> Prop)
      (f : forall v : A, c ↝ v -> P v) :
  refine (r_o' <- c; {r_n0 : {r : A | P r} | r_o' = ` r_n0})
         { r_n0 : { r : A | P r } | c ↝ ` r_n0 }.
Proof.
  intros x ?.
  apply Pick_inv in H.
  apply BindComputes with (a:=` x); trivial.
  apply PickComputes.
  reflexivity.
Qed.

Tactic Notation "apply" "constructor" "knowledge" "for" constr(meth) :=
  apply (fromADTConstructor _ meth _);
  simpl;
  repeat match goal with
         | [ |- fromConstructor _ _ ] => econstructor
         end;
  eauto.

Tactic Notation "resolve" "constructor" constr(meth) :=
  subst; subst_evars;
  etransitivity;
  [ apply refine_constructor_fromADT; intros;
    apply constructor knowledge for meth
  | finish honing ].

Definition get_method
           {dSig : DecoratedADTSig}
           (adt : DecoratedADT dSig)
           (idxMap : BoundedIndex (MethodNames dSig) -> MethodIndex dSig)
           (idx : BoundedIndex (MethodNames dSig)) : MethodIndex dSig :=
  idxMap idx.

Notation method_ adt idx :=
  (get_method adt (fun idx => ibound (indexb idx)) {| bindex := idx |}).

Notation "adt @ idx" :=
  (get_method adt (fun idx => ibound (indexb idx)) {| bindex := idx |})
  (at level 100).

Lemma refine_method_fromADT
      A B (c : Comp (A * B)) (P : A -> Prop)
      (f : forall v : A * B, c ↝ v -> P (fst v)) :
   refine (r_o' <- c;
           r_n' <- {r_n0 : {r : A | P r} | fst r_o' = ` r_n0};
           ret (r_n', snd r_o'))
          { r_n0 : { r : A | P r } * B | c ↝ (` (fst r_n0), snd r_n0) }.
Proof.
  intros [x b] ?.
  apply Pick_inv in H; simpl in H.
  apply BindComputes with (a:=(` x, b)); trivial.
  simpl.
  apply BindComputes with (a:=x); trivial.
  apply PickComputes.
  reflexivity.
Qed.

Tactic Notation "apply" "method" "knowledge" "for"
       constr(S) constr(meth) constr(H) :=
  apply (fromADTMethod (adt:=S) meth _ (proj2_sig H));
  simpl;
  repeat
    match goal with
    | [ |- fromMethod _ _ _ ] => econstructor
    | [ |- fromMethod' _ _ ] => econstructor
    end;
  eauto.

Tactic Notation "resolve" "method" constr(meth) :=
  match goal with
  | [ H : {r : _ | fromADT ?S _} |- _ ] =>
    subst; subst_evars;
    etransitivity;
    [ apply refine_method_fromADT; intros [? ?] ?;
      apply method knowledge for S meth H
    | finish honing ]
  end.

Lemma refine_strip_dependency :
  forall A (P : A -> Prop) x B (k : _ -> Comp B),
    P x ->
    refine (a <- {r_n0 : {r : A | P r} | ret x ↝ ` r_n0}; k (` a))
           (a <- {r_n0 : A | ret x ↝ r_n0}; k a).
Proof.
  intros; intros ??.
  apply Bind_inv in H0; destruct H0 as [? [? ?]].
  apply Pick_inv in H0; destruct H0.
  eapply BindComputes with (a:=exist _ x H); eauto.
Qed.

Ltac strip_dependency_constructor :=
  let x := fresh "x" in
  let H := fresh "H" in
  match goal with
  | [ |- refine (_ <- _; _) _ ] =>
    eapply refine_under_bind_helper; intros x H;
    [ exact H
    | let H := fresh "H" in
      intro H;
      pattern (` x);
      match goal with
      | [ |- (fun h : ?T => refine ?X ?Y) (` x) ] =>
        change (refine ((fun h : T => X) (` x)) Y)
      end;
      exact H
    | rewrite refine_strip_dependency ]
  end;
  revert H;
  revert x;
  try apply refine_inv.

Lemma refine_strip_dependency_pair :
  forall A (P : A -> Prop) B c C (k : A -> B -> Comp C),
    (forall v, c ↝ v -> P (fst v)) ->
    refine (a <- {r_n0 : {r : A | P r} * B
                 | c ↝ (` (fst r_n0), snd r_n0)};
            k (` (fst a)) (snd a))
           (a <- {r_n0 : A * B | c ↝ r_n0};
            k (fst a) (snd a)).
Proof.
  intros; intros ??.
  apply Bind_inv in H0; destruct H0 as [? [? ?]].
  apply Pick_inv in H0.
  apply BindComputes with (a:=(exist _ (fst x) (H _ H0), snd x)); eauto.
  apply PickComputes; simpl.
  rewrite <- surjective_pairing.
  assumption.
Qed.

Ltac strip_dependency_method :=
  let x := fresh "x" in
  let H := fresh "H" in
  match goal with
  | [ |- refine (_ <- _; _) _ ] =>
    eapply refine_under_bind_helper; intros x H;
    [ exact H
    | let H := fresh "H" in
      intro H;
      pattern (snd x);
      pattern (` (fst x));
      match goal with
      | [ |- (fun h : ?T => (fun p : ?U => refine ?X ?Y) (snd x))
               (` (fst x)) ] =>
        change (refine ((fun (h : T) (p : U) => X) (` (fst x)) (snd x)) Y)
      end;
      exact H
    | rewrite refine_strip_dependency_pair ]
  end;
  revert H;
  revert x;
  try apply refine_inv.

Lemma refine_dependency A (X : Comp A) B (f : B -> A) C (k : B -> Comp C) :
  refine (a <- {a : B | X ↝ f a}; k a)
         (x <- X; a <- {a : B | ret x ↝ f a}; k a).
Proof.
  intros ??.
  apply Bind_inv in H; destruct H as [? [? ?]].
  apply computes_to_refine.
  apply Bind_inv in H0; destruct H0 as [? [? ?]].
  refine pick val x0; simpl; trivial.
    simplify with monad laws.
    apply refine_computes_to.
    assumption.
  apply Pick_inv in H0; destruct H0.
  assumption.
Qed.

Tactic Notation "remove" "dependency" constr(meth) :=
  first [ strip_dependency_constructor;
          [| intros; apply constructor knowledge for meth ];
          rewrite refine_pick_ret; simpl
        | strip_dependency_method;
          [ rewrite refine_dependency;
            setoid_rewrite refine_pick_ret; simpl
          | intros ? ? [? ?] ?; simpl;
            match goal with
            | [ Hadt : {r : _ | fromADT ?S _} |- _ ] =>
              apply method knowledge for S meth Hadt
            end ] ];
  try simplify with monad laws; simpl.
