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

Fixpoint annotate_Method
         {arity}
           {oldRep}
           (dom : list Type)
           (cod : option Type)
           (oldMethod : methodType arity oldRep dom cod)
           (P : oldRep -> Prop)
           (newRep := { r : oldRep | P r }%type)
  : methodType arity newRep dom cod :=
  match arity return methodType arity oldRep dom cod ->
                     methodType arity newRep dom cod with
  | S arity' => fun oldMethod => fun r =>
      annotate_Method (arity := arity') dom cod (oldMethod (` r)) P
  | 0 => fun oldMethod => annotate_Method' dom cod P oldMethod
  end oldMethod.

Definition annotate_MethDef
           {oldRep}
           (Sig : methSig)
           (oldCons : @methDef oldRep Sig)
           (P : oldRep -> Prop)
  : @methDef _ Sig :=
  {| methBody := annotate_Method _ _ (methBody oldCons) P |}.

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

Fixpoint refineMethod_w_PreCond
         (arity : nat)
           {oldRep newRep}
           (AbsR : oldRep -> newRep -> Prop)
           (P : oldRep -> Prop)
           {dom : list Type}
           {cod : option Type}
           (oldMethod : methodType arity oldRep dom cod)
           (newMethod : methodType arity newRep dom cod)
  : Prop :=
    match arity return
          methodType arity oldRep dom cod ->
          methodType arity newRep dom cod ->
          Prop with
    | S arity' =>
      fun oldMethod newMethod =>
        forall r_o r_n,
          P r_o
          -> AbsR r_o r_n
          -> refineMethod_w_PreCond arity' AbsR P (oldMethod r_o) (newMethod r_n)
    | 0 => @refineMethod' _ _ AbsR dom cod
    end oldMethod newMethod.

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

Lemma annotate_ADT
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {n'}
      {methSigs : Vector.t methSig n'}
      (methDefs : ilist (B := @methDef oldRep) methSigs)
      (methDefs' : ilist (B := @methDef newRep) methSigs)
      (MethodsRefineSpec
       : IterateBoundedIndex.Iterate_Dep_Type_BoundedIndex
           (fun idx  =>
              refineMethod_w_PreCond
                _
                AbsR
                (fromADT (BuildADT methDefs))
                (dom := methDom (Vector.nth methSigs idx))
                (getMethDef methDefs idx)
                (getMethDef methDefs' idx)))
  :
  refineADT
    (BuildADT methDefs)
    (BuildADT methDefs').
Proof.
  eapply transitivityT.
  - apply refineADT_Build_ADT_Rep_default with
    (AbsR := fun or (nr : { r : oldRep | fromADT (BuildADT methDefs) r }) =>
               or = ` nr).
  - eapply refinesADT with (AbsR := fun r_o r_n => AbsR (`r_o) r_n); intros.
    + simpl Methods.
      generalize (IterateBoundedIndex.Lookup_Iterate_Dep_Type
                    _ MethodsRefineSpec idx) as refineMeth'; simpl; clear.
      assert (forall r',
                 fromMethod'' (fromADT (BuildADT methDefs)) (ith methDefs idx) r'
                 -> fromADT (BuildADT methDefs) r').
      intros; econstructor 1 with (midx := idx).
      apply H.
      generalize (Vector.nth methSigs idx) (ith methDefs idx) (ith methDefs' idx) H;
        clear.
      intros m m0 m1.
      generalize (methBody m1).
      generalize (methBody m0).
      generalize (methArity m).
      induction n; simpl in *; intros.
      * induction (methDom m); simpl in *.
        { destruct (methCod m); simpl;
          rewrite <- refineMeth'; clear refineMeth';
            intros v Comp_v; computes_to_inv.
          - unfold absMethod; simpl.
            assert (fromADT (BuildADT methDefs) (fst v0))
              by (apply H; econstructor; simpl; eexists (snd v0); destruct v0;
                  simpl; eauto).
            eapply BindComputes
              with (a := (exist (fun v0 => fromADT (BuildADT methDefs) v0)
                                (fst v0) H0, snd v0)).
            computes_to_econstructor.
            eexists; repeat split; try eauto.
            computes_to_econstructor.
            computes_to_econstructor; simpl; eauto.
            subst; computes_to_econstructor.
          - unfold absMethod; simpl.
            assert (fromADT (BuildADT methDefs) v0)
              by (apply H; econstructor; simpl; eauto).
            eapply BindComputes with
            (a := exist (fun v0 => fromADT (BuildADT methDefs) v0) _ H0).
            computes_to_econstructor.
            eexists; repeat split; try eauto.
            computes_to_econstructor; simpl; eauto.
        }
        { simpl; intros.
          simpl; pose proof (fun H' => IHl _ _ H' (refineMeth' d)).
          match type of H0 with
            _ -> ?Q =>
            match goal with
              |- ?Q' => assert (Q = Q') as H' by
                  (unfold absMethod; simpl; repeat f_equal;
                   apply functional_extensionality; intros;
                   destruct (methCod m); reflexivity);
                          rewrite <- H'; apply H0
            end
          end.
          intros; apply H; econstructor.
          apply fromMethod_inv in H1; simpl; eauto.
        }
      * assert (forall r' : oldRep,
                   fromMethod'' (fromADT (BuildADT methDefs)) (m2 (` r_o)) r'
                     -> fromADT (BuildADT methDefs) r').
        intros.
        apply H.
        econstructor.
        apply (proj2_sig r_o); eauto.
        apply H1.
        assert (refineMethod_w_PreCond n AbsR (fromADT (BuildADT methDefs)) (m2 (` r_o)) (m3 r_n)).
        apply refineMeth'; eauto.
        apply (proj2_sig _).
        eapply (@refineMethod_eq_trans'
                  _ _ _ _ _
                  (fun (r_o : {r : oldRep | fromADT (BuildADT methDefs) r})
                       (r_n : newRep) => AbsR (` r_o) r_n)
                  (absMethod (arity := S n) (fun or nr => or = ` nr) m2 r_o)
                  _ (m3 r_n)).
        2: eapply (IHn (m2 (` r_o)) (m3 r_n) H1 H2); clear.
        unfold absMethod; simpl.
        destruct (methCod m).
        {
          simpl; eapply refineMethod_Curry_Some.
          clear; intros ? ? v Comp_v.
          Local Transparent computes_to.
          unfold computes_to; intros.
          subst.
          apply Comp_v.
        }
        {
          simpl; eapply refineMethod_Curry_None.
          clear; intros ? ? v Comp_v.
          Local Transparent computes_to.
          unfold computes_to; intros.
          subst.
          apply Comp_v.
        }
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
  | [ H : methodType _ _
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
