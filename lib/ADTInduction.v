Require Import Fiat.ADT Fiat.ADTNotation.

Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.

Import ListNotations.

Fixpoint fromMethod' {rep : Type} {dom : list Type} :
  forall {cod : option Type}, methodType' rep dom cod -> rep -> Prop :=
  match dom return
        forall {cod : option Type},
          methodType' rep dom cod -> rep -> Prop with
  | [ ] =>
    fun cod =>
      match cod return methodType' rep [ ] cod -> rep -> Prop with
      | None   => fun meth r => computes_to meth r
      | Some C => fun meth r => exists c : C, computes_to meth (r, c)
      end
  | D :: dom' =>
    fun cod meth r => exists d, fromMethod' (meth d) r
  end.

Fixpoint fromMethod
           {arity : nat}
           {rep : Type}
           {dom : list Type}
           {cod : option Type}
           (meth : methodType arity rep dom cod)
           (P : rep -> Prop)
  : rep -> Prop :=
  match arity return
        methodType arity rep dom cod
        -> rep -> Prop with
  | 0 => fun meth' => fromMethod' meth'
  | S n' => fun meth' r => exists r', P r' /\ fromMethod (meth' r') P r
  end meth.

Inductive fromMethod''
           {rep : Type}
           {dom : list Type}
           {cod : option Type}
           (P : rep -> Prop)
  : forall {arity},
    methodType arity rep dom cod -> rep -> Prop :=
| from_Constructor
  : forall r (meth : methodType 0 rep dom cod),
    fromMethod' meth r
    -> fromMethod'' P meth r
| from_Method
  : forall r r' arity' (meth : methodType (S arity') rep dom cod),
    P r
    -> fromMethod'' P (meth r) r'
    -> fromMethod'' P meth r'.

Lemma fromMethod_inv :
  forall {arity : nat}
         {rep : Type}
         {dom : list Type}
         {cod : option Type}
         (meth : methodType arity rep dom cod)
         (P : rep -> Prop)
         (r : rep)
         (H : fromMethod'' P meth r),
    match arity return
            methodType arity rep dom cod
            -> rep -> Prop with
    | 0 => fun meth' => fromMethod' meth'
    | S n' => fun meth' r => exists r', P r' /\ fromMethod'' P (meth' r') r
    end meth r.
Proof.
  intros; induction H; simpl; intros; eauto.
Qed.

Lemma fromMethod_equiv :
  forall {arity : nat}
         {rep : Type}
         {dom : list Type}
         {cod : option Type}
         (meth : methodType arity rep dom cod)
         (P : rep -> Prop)
         (r : rep),
    fromMethod meth P r <-> fromMethod'' P meth r.
Proof.
  induction arity; simpl; split; intros;
    try solve [econstructor; eauto].
  - apply fromMethod_inv in H; eauto.
  - destruct_ex; intuition.
    econstructor; eauto.
    apply IHarity; eauto.
  - apply fromMethod_inv in H;
      destruct_ex; intuition.
    eexists; split; eauto.
    apply IHarity; eauto.
Qed.

Inductive fromADT {sig} (adt : ADT sig) : Rep adt -> Prop :=
  | fromADTMethod :
      forall (midx : MethodIndex sig) (r' : Rep adt),
        fromMethod'' (fromADT adt) (Methods adt midx) r'
        -> fromADT adt r'.

Scheme Induction for fromADT Sort Prop.

Require Import Fiat.Common.IterateBoundedIndex.

Tactic Notation "ADT" "induction" ident(r) :=
  match goal with
  | [ ADT : fromADT ?A ?r |- _ ] =>
    let midx := fresh "midx" in
    let r' := fresh "r'" in
    let IHfromADT := fresh "IHfromADT" in
    induction ADT as [midx r' IHfromADT];
    revert r' IHfromADT;
    match goal with
    | [ midx : MethodIndex _      |- _ ] => pattern midx
    end;
    apply IterateBoundedIndex.Iterate_Ensemble_equiv';
    repeat apply IterateBoundedIndex.Build_prim_and;
    try solve [constructor ] ;
    simpl; intros;
    match goal with
    | [ H : fromMethod'' _ _ _ |- _ ] =>
      apply fromMethod_equiv in H; simpl in H
    | _ => idtac
    end;
    destruct_ex;
    try computes_to_inv;
    try injections;
    subst;
    eauto;
    match goal with
    | [ midx : MethodIndex _      |- _ ] => clear midx
    end
  end.

Fixpoint ADT_ind' {sig} (adt : ADT sig)
         (P : Ensemble (Rep adt))
         (PM : forall midx r', fromMethod'' (fun r => P r /\ fromADT adt r) (Methods adt midx) r' -> P r')
         (r : Rep adt)
         (from_r : fromADT adt r)
         {struct from_r}
  : P r.
Proof.
  intros.
  destruct from_r.
  eapply (PM midx).
  induction H.
  - constructor; auto.
  - econstructor.
    + split.
      apply ADT_ind'.
      apply PM.
      apply H.
      apply H.
    + apply IHfromMethod''.
Qed.

Definition ADT_ind {sig} (adt : ADT sig)
         (P : Ensemble (Rep adt))
         (PM : forall midx r', fromMethod (Methods adt midx) (fun r => P r /\ fromADT adt r) r' -> P r')
         (r : Rep adt)
         (from_r : fromADT adt r)
  : P r.
Proof.
  pattern r. apply ADT_ind'; intros.
  eapply fromMethod_equiv in H; eauto.
  eauto.
Qed.

Definition ARep {sig} (adt : ADT sig) := { r : Rep adt | fromADT adt r }.
