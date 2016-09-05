Require Import
  ByteString.Fiat
  ByteString.ADTInduction.

Generalizable All Variables.

Definition fromADTConstructor'
           {dSig : DecoratedADTSig}
           (adt : DecoratedADT dSig)
           (idxMap : BoundedIndex (ConstructorNames dSig)
                       -> ConstructorIndex dSig)
           (idx : BoundedIndex (ConstructorNames dSig)) :
  forall (r : Rep adt),
    fromConstructor (Constructors adt (idxMap idx)) r
      -> fromADT adt r :=
  fromADTConstructor adt (idxMap idx).

Arguments fromADTConstructor' {dSig} adt idxMap idx r _.

Notation fromCons adt idx :=
  (fromADTConstructor' adt (fun idx => ibound (indexb idx))
                           {| bindex := idx |}).

Tactic Notation "check" "constructor" constr(t) :=
  simpl; intros; apply t;
  repeat match goal with
    | [ H : refine _ (ret _) |- _ ] => apply computes_to_refine in H
    | [ |- fromConstructor _ _ _ ] => eexists
    | [ H : _ ↝ _ |- _ ↝ _ ] => exact H
    | [ H : ?X |- ?X ] => exact H
    end.

Definition fromADTMethod'
           {dSig : DecoratedADTSig}
           (adt : DecoratedADT dSig)
           (idxMap : BoundedIndex (MethodNames dSig) -> MethodIndex dSig)
           (idx : BoundedIndex (MethodNames dSig)) :
  forall (r r' : Rep adt),
    fromADT adt r
      -> fromMethod (Methods adt (idxMap idx)) r r'
      -> fromADT adt r' :=
  fromADTMethod (adt:=adt) (idxMap idx).

Arguments fromADTMethod' {dSig} adt idxMap idx r r' _ _.

Notation fromMeth adt idx :=
  (fromADTMethod' adt (fun idx => ibound (indexb idx)) {| bindex := idx |}).

Tactic Notation "check" "method" constr(t) :=
  simpl; intros;
  apply t;
  repeat match goal with
    | [ H : _ * _ |- _ ] => destruct H; simpl in *
    | [ H : refine _ (ret _) |- _ ] => apply computes_to_refine in H
    | [ |- fromMethod _ _ _ ] => eexists
    | [ |- fromMethod' _ _ ] => eexists
    | [ H : _ ↝ _ |- _ ↝ _ ] => exact H
    | [ H : ?X |- ?X ] => exact H
    end.

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

Ltac resolve_constructor m H0 :=
  subst; subst_evars;
  etransitivity;
  [ apply refine_constructor_fromADT;
    intros ??; apply H0; assumption
  | finish honing].

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

Ltac resolve_method r_n m H0 :=
  subst; subst_evars;
  etransitivity;
  [ apply refine_method_fromADT;
    intros ??; apply H0; assumption
  | finish honing].

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

Ltac remove_dependency HA :=
  first [ strip_dependency_constructor;
          [| intros; apply HA; simpl ];
          rewrite refine_pick_ret; simpl
        | strip_dependency_method;
          [ rewrite refine_dependency;
            setoid_rewrite refine_pick_ret; simpl
          | let H := fresh "H" in
            intros ? ? ? H;
            eapply HA; simpl;
            [ match goal with
                [ HR : { r : _ | _ r } |- _ ] =>
                exact (proj2_sig HR)
              end
            | exact H ] ] ];
  try simplify with monad laws; simpl.
