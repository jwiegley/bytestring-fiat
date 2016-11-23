Require Import ByteString.Lib.Fiat.

Definition get_method
           {dSig : DecoratedADTSig}
           (adt : DecoratedADT dSig)
           (idxMap : BoundedIndex (MethodNames dSig) -> MethodIndex dSig)
           (idx : BoundedIndex (MethodNames dSig)) : MethodIndex dSig :=
  idxMap idx.

Notation "adt @ idx" :=
  (get_method adt (fun idx => ibound (indexb idx)) {| bindex := idx |})
  (at level 100) : comp_scope.

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
  apply BindComputes with (a:=(` x, b)); trivial; simpl.
  apply BindComputes with (a:=x); trivial.
  apply PickComputes; reflexivity.
Qed.

Fixpoint annotate_Method'
         {oldRep}
         (dom : list Type)
         (cod : option Type)
         (P : oldRep -> Prop)
         (newRep := { r : oldRep | P r }%type)
         {struct dom}
  : (methodType' oldRep dom cod)
    -> (methodType' newRep dom cod) :=
  match dom return
        methodType' oldRep dom cod ->
        methodType' _ dom cod
  with
  | nil =>
    match cod return
          methodType' oldRep nil cod ->
          methodType' _ nil cod
    with
    | Some codT => fun oldMeth v => oldMeth (` (fst v), snd v)
    | None => fun oldMeth v => oldMeth (`v)
    end
  | cons domT dom' =>
    fun oldMeth d =>
      annotate_Method' dom' cod P (oldMeth d)
  end.

Definition annotate_Method
           {oldRep}
           (arity : nat)
           (dom : list Type)
           (cod : option Type)
           (oldMethod : methodType arity oldRep dom cod)
           (P : oldRep -> Prop)
           (newRep := { r : oldRep | P r }%type)
  : methodType arity newRep dom cod :=
  fun r => annotate_Method' dom cod P (oldMethod (` r)).

Definition annotate_MethDef
           {oldRep}
           (Sig : methSig)
           (oldCons : @methDef oldRep Sig)
           (P : oldRep -> Prop)
  : @methDef _ Sig :=
  {| methBody := annotate_Method (methBody oldCons) P |}.

Tactic Notation "apply" "method" "knowledge" "for"
       constr(S) constr(meth) constr(H) :=
  apply (fromADTMethod (adt:=S) meth _ (proj2_sig H)); simpl;
  repeat
    match goal with
    | [ |- fromMethod _ _ _ ] => econstructor
    | [ |- fromMethod' _ _ ] => econstructor
    end; eauto.

Tactic Notation "resolve" "method" constr(meth) :=
  match goal with
    [ H : { r : _ | fromADT ?S _ } |- _ ] =>
    subst; subst_evars;
    etransitivity;
    [ apply refine_method_fromADT; intros [? ?] ?;
      apply method knowledge for S meth H
    | finish honing ]
  end.

Ltac resolve_method_bodies :=
  match goal with
  | [ H : constructorType
            {r : Rep ?S | fromADT ?S r}
            (consDom (Constructor ?C : rep)) |- _ ] =>
    resolve constructor
      (get_ctor S (fun idx => ibound (indexb idx)) {| bindex := C |})
  | [ H : methodType
            {r : Rep ?S | fromADT ?S r}
            (methDom {| methID := ?M; methDom := _; methCod := _ |})
            (methCod {| methID := ?M; methDom := _; methCod := _ |}) |- _ ] =>
    resolve method
      (get_method S (fun idx => ibound (indexb idx)) {| bindex := M |})
  | _ => idtac
  end.

Tactic Notation "annotate" constr(spec) "ADT" :=
  hone representation using
       (fun (or : Rep spec)
            (nr : { r : Rep spec | fromADT spec r }) => or = ` nr);
  resolve_method_bodies.

Definition refineMethod_w_PreCond
           {oldRep newRep}
           (AbsR : oldRep -> newRep -> Prop)
           (P : oldRep -> Prop)
           {dom : list Type}
           {cod : option Type}
           (oldMethod : methodType oldRep dom cod)
           (newMethod : methodType newRep dom cod)
  := forall r_o r_n,
    P r_o
    -> AbsR r_o r_n
    -> @refineMethod' _ _ AbsR dom cod (oldMethod r_o) (newMethod r_n).

Lemma refineMethod'_trans rep rep' rep'' Dom Cod
      AbsR AbsR'
  : forall m m' m'',
    @refineMethod' rep rep' AbsR Dom Cod m m'
    -> @refineMethod' rep' rep'' AbsR' Dom Cod m' m''
    -> refineMethod' (fun r_o r_n => exists r_o', AbsR r_o r_o' /\ AbsR' r_o' r_n)
                         m m''.
Proof.
  induction Dom.
  - intro; simpl; intros; destruct Cod; subst; intros v Comp_v.
    + destruct_ex; intuition.
      eapply H0 in Comp_v; eauto; computes_to_inv; subst.
      eapply H in Comp_v; eauto; computes_to_inv; subst; eauto.
      repeat computes_to_econstructor; eauto.
    + destruct_ex; intuition.
      eapply H0 in Comp_v; eauto; computes_to_inv; subst.
      eapply H in Comp_v; eauto; computes_to_inv; subst; eauto.
  - simpl; intros.
    destruct_ex; intuition.
    eapply (IHDom (m d)
                  (m' d)
                  (m'' d)); eauto.
Qed.

Lemma refine_absConstructor_fromADT
  : forall oldRep dom
           (P : oldRep -> Prop)
           (c : constructorType oldRep dom),
    (forall r : oldRep, fromConstructor c r -> P r) ->
    refineConstructor (fun (or : {r : oldRep | P r}) (nr : oldRep) => ` or = nr)
                      (absConstructor (fun (or : oldRep) (nr : {r : oldRep | P r}) => or = ` nr) c) c.
Proof.
  induction dom.
  - simpl; unfold refine; intros.
    repeat computes_to_econstructor.
    instantiate (1 := exist _ _ (H _ H0)).
    eexists; split; eauto.
    reflexivity.
  - intros.
    intro; eapply IHdom; intros; eauto.
    eapply H.
    eexists; eauto.
Qed.

Lemma refine_absMethod_fromADT
  : forall oldRep dom cod
           (P : oldRep -> Prop)
           (c : methodType oldRep dom cod),
    (forall r r' : oldRep, P r -> fromMethod c r r' -> P r') ->
    forall r',
    refineMethod' (fun (or : {r : oldRep | P r}) (nr : oldRep) => ` or = nr)
                  (absMethod' (fun (or : oldRep) (nr : {r : oldRep | P r}) => or = ` nr) dom cod c r') (c (` r')).
Proof.
  unfold fromMethod.
  induction dom.
  - destruct cod; simpl; unfold refine; intros.
    + destruct r'; destruct v.
      repeat computes_to_econstructor; intros; subst; simpl in H0.
      instantiate (1 := (exist _ _ ((H _ _ p (ex_intro (fun c0 => c x ↝ (_, c0)) _ H0))), _)); simpl.
      eexists; split; eauto.
      reflexivity.
      computes_to_econstructor.
    + destruct r'.
      repeat computes_to_econstructor; intros; subst; simpl in H0.
      instantiate (1 := exist _ _ ((H _ _ p H0))); simpl.
      eexists; split; eauto.
      reflexivity.
  - simpl; intros; eapply IHdom; eauto.
Qed.

Lemma annotate_ADT
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {n n'}
      {consSigs : Vector.t consSig n}
      {methSigs : Vector.t methSig n'}
      (consDefs : ilist (B := @consDef oldRep) consSigs)
      (consDefs' : ilist (B := @consDef newRep) consSigs)
      (methDefs : ilist (B := @methDef oldRep) methSigs)
      (methDefs' : ilist (B := @methDef newRep) methSigs)
      (ConstructorsRefineSpec
       : IterateBoundedIndex.Iterate_Dep_Type_BoundedIndex
           (fun idx  =>
              refineConstructor
                AbsR
                (dom := consDom (Vector.nth consSigs idx))
                (getConsDef consDefs idx)
                (getConsDef consDefs' idx)))
      (MethodsRefineSpec
       : IterateBoundedIndex.Iterate_Dep_Type_BoundedIndex
           (fun idx  =>
              refineMethod_w_PreCond
                AbsR
                (fromADT (BuildADT consDefs methDefs))
                (dom := methDom (Vector.nth methSigs idx))
                (getMethDef methDefs idx)
                (getMethDef methDefs' idx)))
  :
  refineADT
    (BuildADT consDefs methDefs)
    (BuildADT consDefs' methDefs').
Proof.
  eapply transitivityT.
  - apply refineADT_Build_ADT_Rep_default with
    (AbsR := fun or (nr : { r : oldRep | fromADT (BuildADT consDefs methDefs) r }) =>
               or = ` nr).
  - eapply refinesADT; intros.
    + simpl Constructors.
      generalize (IterateBoundedIndex.Lookup_Iterate_Dep_Type _ ConstructorsRefineSpec idx) as refineCons'; clear; intros;
      eapply refineConstructor_trans with
      (AbsR := fun or nr => `or = nr)
      (AbsR' := AbsR); eauto.
      clear.
      unfold getConsDef.
      generalize (@fromADTConstructor _ (BuildADT consDefs methDefs) idx);
        simpl Constructors.
      eapply refine_absConstructor_fromADT.
    + simpl Methods.
      generalize (IterateBoundedIndex.Lookup_Iterate_Dep_Type _ MethodsRefineSpec idx) as refineMeth'; simpl; clear;
        intros ? [r_o' fromADT_r_o] r_n [ r_o [eq_r_o AbsR_r_o] ];
        simpl in *; subst.
      specialize (refineMeth' _ _ (fromADT_r_o) AbsR_r_o).
      eapply refineMethod'_trans; eauto.
      eapply refine_absMethod_fromADT.
      intros.
      eapply fromADTMethod with (midx := idx); eauto.
Qed.

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
    [ |- refine (_ <- _; _) _ ] =>
    eapply refine_under_bind_helper; intros x H;
    [ exact H
    | let H := fresh "H" in
      intro H;
      pattern (` x);
      match goal with
        [ |- (fun h : ?T => refine ?X ?Y) (` x) ] =>
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
    [ |- refine (_ <- _; _) _ ] =>
    eapply refine_under_bind_helper; intros x H;
    [ exact H
    | let H := fresh "H" in
      intro H;
      pattern (snd x);
      pattern (` (fst x));
      match goal with
        [ |- (fun h : ?T => (fun p : ?U => refine ?X ?Y) (snd x))
               (` (fst x)) ] =>
        change (refine ((fun (h : T) (p : U) => X) (` (fst x)) (snd x)) Y)
      end;
      exact H
    | rewrite refine_strip_dependency_pair ]
  end;
  revert H;
  revert x;
  try apply refine_inv.

Lemma refine_pick_computes_to
      A (X : Comp A) B (f : B -> A) C (k : B -> Comp C) :
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

Tactic Notation "remove" "dependency" constr(S) :=
  match goal with
  | [ H : constructorType _ (consDom (Constructor ?C : rep)) |- _ ] =>
    strip_dependency_constructor;
    [| intros;
       apply constructor knowledge for
             (get_ctor S (fun idx => ibound (indexb idx)) {| bindex := C |}) ];
    rewrite refine_pick_ret
  | [ H : methodType _
            (methDom {| methID := ?M; methDom := _; methCod := _ |})
            (methCod {| methID := ?M; methDom := _; methCod := _ |}) |- _ ] =>
    strip_dependency_method;
    [ rewrite refine_pick_computes_to;
      setoid_rewrite refine_pick_ret; simpl
    | intros ? ? [? ?] ?; simpl;
      match goal with
        [ Hadt : {r : _ | fromADT ?S _} |- _ ] =>
        apply method knowledge for S
              (get_method S (fun idx => ibound (indexb idx)) {| bindex := M |})
              Hadt
      end ]
  | _ => idtac
  end;
  try simplify with monad laws; simpl.

Tactic Notation "hone" "representation" "over" constr(spec) "using" constr(f) :=
  annotate spec ADT;
  hone representation using (fun or => f (` or));
  remove dependency spec;
  try match goal with
    [ H : { r : _ | fromADT spec r } |- _ ] =>
    let Hfrom := fresh "Hfrom" in
    destruct H as [H Hfrom]; simpl in *
  end.
