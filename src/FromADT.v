Require Import
  Fiat.ADT
  Fiat.ADTNotation
  Here.ADTInduction
  Here.LibExt.

Require Import
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Require Import
  Here.BindDep.

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

Lemma refine_computes_to {A} {c : Comp A} {v} :
  c ↝ v -> refine c (ret v).
Proof.
  intros.
  intros ??.
  inv H0.
  exact H.
Qed.

Lemma computes_to_refine {A} {c : Comp A} {v} :
  refine c (ret v) -> c ↝ v.
Proof. intros; exact (H _ (ReturnComputes _)). Qed.

Tactic Notation "check" "constructor" constr(t) :=
  simpl; intros;
  apply t;
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
      (f : forall v : A, refine c (ret v) -> P v) :
   refine (r_o' <- c;
           {r_n0 : {r : A | P r} | r_o' = ` r_n0})
          (`(r_o' | H) <- c;
           ret (exist _ r_o' (f r_o' H))).
Proof.
  intros x?.
  destruct H.
  exists x0.
  destruct H.
  split; trivial.
  destruct i.
  esplit.
Qed.

Lemma refine_method_fromADT
      A B (c : Comp (A * B)) (P : A -> Prop)
      (f : forall v : A * B, refine c (ret v) -> P (fst v)) :
   refine (r_o' <- c;
           r_n' <- {r_n0 : {r : A | P r} | fst r_o' = ` r_n0};
           ret (r_n', snd r_o'))
          (`(r_o' | H) <- c;
           ret (exist _ (fst r_o') (f r_o' H),
                snd r_o')).
Proof.
  intros x?.
  destruct H.
  exists x0.
  destruct H.
  split; trivial.
  destruct i.
  esplit; split.
    Focus 2.
    constructor.
  constructor.
Qed.

Ltac resolve_constructor m H0 :=
  subst; subst_evars;
  etransitivity;
  [ apply (refine_constructor_fromADT _ (c:=m) H0)
  | finish honing].

Ltac resolve_method r_n m H0 :=
  subst; subst_evars;
  etransitivity;
  [ apply (refine_method_fromADT _ (c:=m) H0)
  | finish honing].
