Require Import
  ByteString.Lib.Tactics
  ByteString.Lib.Nomega
  ByteString.Lib.Fiat
  ByteString.Lib.TupleEnsembles
  ByteString.Lib.FunMaps
  ByteString.Lib.FromADT
  ByteString.Lib.HList
  ByteString.Memory
  ByteString.Heap
  ByteString.FFI.HeapFFI
  ByteString.ByteString
  ByteString.ByteStringHeap
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx
  Hask.Data.Functor
  Hask.Control.Monad
  Hask.Control.Monad.Trans.FiatState
  Hask.Control.Monad.Free.

(****************************************************************************
 * ClientDSL: DSL that represents a series of calls against an ADT signature
 ****************************************************************************)

Section ClientDSL.

Variable sig : ADTSig.

Inductive MethodCall (rec : Type) : Type :=
  | Call : forall (midx : MethodIndex sig) dom cod,
      fst (MethodDomCod sig midx) = dom ->
      snd (MethodDomCod sig midx) = Some cod ->
      hlist dom -> (cod -> rec) -> MethodCall rec.

Global Program Instance MethodCall_Functor : Functor MethodCall := {
  fmap := fun A B f x =>
    match x with
    | Call midx _ _ _ _ args k => Call midx _ _ args (f \o k)
    end
}.

Definition ClientDSL := Free MethodCall.

(****************************************************************************
 * ADT_Computes: Relates a [ClientDSL] term to a Fiat computation using an
 * ADT of the same signature.
 ****************************************************************************)

Variable adt : ADT sig.

Program Fixpoint applyArgs
         (dom : list Type)
         {rep A : Type} (meth : methodType rep dom (Some A))
         (args : hlist dom) : rep -> Comp (rep * A) :=
  match dom return hlist dom -> methodType rep dom (Some A)
                     -> rep -> Comp (rep * A) with
  | nil => fun _ => id
  | cons t ts =>
    fun (args : hlist (t :: ts))
        (meth : methodType rep (t :: ts) (Some A)) =>
      applyArgs (fun r => meth r (hlist_head args))
                (hlist_tail args)
  end args meth.

Import EqNotations.

Inductive MethodCall_Computes :
  forall A, MethodCall A -> Rep adt -> Rep adt -> A -> Prop :=
  | CallComputes (midx : MethodIndex sig) dom
                 A (meth : methodType (Rep adt) dom (Some A)) :
      forall (r r' : Rep adt) (v : A) (args : hlist dom),
        applyArgs meth args r ↝ (r', v) ->
      forall B (k : A -> B) x, x = k v ->
      forall (H1 : fst (MethodDomCod sig midx) = dom)
             (H2 : snd (MethodDomCod sig midx) = Some A),
      meth = rew [fun T => methodType (Rep adt) T (Some A)] H1
               in rew H2 in Methods adt midx ->
      MethodCall_Computes (Call midx H1 H2 args k) r r' x

  | CallCompute1 (midx : MethodIndex sig) T1
                 A (meth : methodType (Rep adt) [T1] (Some A)) :
      forall (r r' : Rep adt) (v : A) (a1 : T1),
        meth r a1 ↝ (r', v) ->
      forall B (k : A -> B) x, x = k v ->
      forall (H1 : fst (MethodDomCod sig midx) = [T1])
             (H2 : snd (MethodDomCod sig midx) = Some A),
      meth = rew [fun T => methodType (Rep adt) T (Some A)] H1
               in rew H2 in Methods adt midx ->
      MethodCall_Computes
        (Call midx H1 H2 (HCons a1 HNil) k) r r' x

  | CallCompute2 (midx : MethodIndex sig) T1 T2
                 A (meth : methodType (Rep adt) [T1; T2] (Some A)) :
      forall (r r' : Rep adt) (v : A) (a1 : T1) (a2 : T2),
        meth r a1 a2 ↝ (r', v) ->
      forall B (k : A -> B) x, x = k v ->
      forall (H1 : fst (MethodDomCod sig midx) = [T1; T2])
             (H2 : snd (MethodDomCod sig midx) = Some A),
      meth = rew [fun T => methodType (Rep adt) T (Some A)] H1
               in rew H2 in Methods adt midx ->
      MethodCall_Computes
        (Call midx H1 H2 (HCons a1 (HCons a2 HNil)) k) r r' x

  | CallCompute3 (midx : MethodIndex sig) T1 T2 T3
                 A (meth : methodType (Rep adt) [T1; T2; T3] (Some A)) :
      forall (r r' : Rep adt) (v : A) (a1 : T1) (a2 : T2) (a3 : T3),
             meth r a1 a2 a3 ↝ (r', v) ->
      forall B (k : A -> B) x, x = k v ->
      forall (H1 : fst (MethodDomCod sig midx) = [T1; T2; T3])
             (H2 : snd (MethodDomCod sig midx) = Some A),
      meth = rew [fun T => methodType (Rep adt) T (Some A)] H1
               in rew H2 in Methods adt midx ->
      MethodCall_Computes
        (Call midx H1 H2 (HCons a1 (HCons a2 (HCons a3 HNil))) k) r r' x

  | CallCompute4 (midx : MethodIndex sig) T1 T2 T3 T4
                 A (meth : methodType (Rep adt) [T1; T2; T3; T4] (Some A)) :
      forall (r r' : Rep adt) (v : A) (a1 : T1) (a2 : T2) (a3 : T3) (a4 : T4),
             meth r a1 a2 a3 a4 ↝ (r', v) ->
      forall B (k : A -> B) x, x = k v ->
      forall (H1 : fst (MethodDomCod sig midx) = [T1; T2; T3; T4])
             (H2 : snd (MethodDomCod sig midx) = Some A),
      meth = rew [fun T => methodType (Rep adt) T (Some A)] H1
               in rew H2 in Methods adt midx ->
      MethodCall_Computes
        (Call midx H1 H2 (HCons a1 (HCons a2 (HCons a3 (HCons a4 HNil)))) k) r r' x.

Inductive Free_Computes `{Functor f} {R : Type}
          (crel : forall {A}, f A -> R -> R -> A -> Prop) :
  forall {A}, Free f A -> R -> R -> A -> Prop :=
  | CPure r A (v : A) : Free_Computes crel (Pure v) r r v
  | CJoin r r'' B (v' : B) :
      forall A t k r' v, Free_Computes crel (k v) r' r'' v'
        -> crel A t r r' v
        -> Free_Computes crel (Join k t) r r'' v'.

Definition ADT_Computes {A : Type} := Free_Computes (A:=A) MethodCall_Computes.

(****************************************************************************
 * reflect_ADT_DSL_computation: Helper lemmas to abstract a Fiat
 * computation into its equivalent [ClientDSL] term.
 ****************************************************************************)

Definition reflect_ADT_DSL_computation {A B : Type}
           (c : Rep adt * B -> Comp ((Rep adt * B) * A)) :=
  { f : B -> ClientDSL (B * A)
  & forall r bs r' bs' v, c (r, bs) ↝ ((r', bs'), v)
      -> ADT_Computes (f bs) r r' (bs', v) }.

Lemma reflect_ADT_DSL_computation_simplify {B C : Type} c c'
      (refine_c_c' : forall r, refineEquiv (c r) (c' r))
      (c_DSL : reflect_ADT_DSL_computation c')
  : reflect_ADT_DSL_computation (A := C) (B := B) c.
Proof.
  exists (projT1 c_DSL); intros.
  pose proof (projT2 c_DSL); simpl in *.
  apply H0; apply refine_c_c'; auto.
Defined.

Corollary If_Then_Else_computes_to : forall b A (t e : Comp A) (v : A),
  (If b Then t Else e) ↝ v -> If b Then (t ↝ v) Else (e ↝ v).
Proof. destruct b; trivial. Qed.

Lemma reflect_ADT_DSL_computation_If_Then_Else
      {B C : Type} c c' (t e : _ -> Comp (_ * C))
      (c_DSL : reflect_ADT_DSL_computation t)
      (k_DSL : reflect_ADT_DSL_computation e)
  : (forall r, c r = c' (snd r)) ->
    reflect_ADT_DSL_computation (B:=B) (fun r => If c r Then t r Else e r).
Proof.
  intros.
  exists (fun bs : B =>
            If c' bs
            Then projT1 c_DSL bs
            Else projT1 k_DSL bs).
  intros.
  rewrite H in H0.
  apply If_Then_Else_computes_to in H0.
  simpl in *.
  destruct (c' _).
    destruct c_DSL.
    simpl in *.
    apply a; assumption.
  destruct k_DSL.
  simpl in *.
  apply a; assumption.
Defined.

End ClientDSL.

Arguments MethodCall {sig} rec.
Arguments Call {sig rec} midx {dom cod} _ _ _ _.

(****************************************************************************
 * [reflect_ADT_DSL_computation] compilation tactics
 ****************************************************************************)

Ltac wrapup :=
  first
  [ eassumption
  | higher_order_reflexivity
  | instantiate (1 := eq_sym eq_refl);
    instantiate (1 := eq_sym eq_refl);
    reflexivity ].

Ltac solve_for1 :=
  match goal with
  | [ H : _ _ ?A ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute1
              with (midx := Fin.F1); wrapup ]
  | [ H : _ _ ?A ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute1
              with (midx := Fin.FS Fin.F1); wrapup ]
  | [ H : _ _ ?A ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute1
              with (midx := Fin.FS (Fin.FS Fin.F1)); wrapup ]
  | [ H : _ _ ?A ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute1
              with (midx := Fin.FS (Fin.FS (Fin.FS Fin.F1))); wrapup ]
  | [ H : _ _ ?A ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute1
              with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))); wrapup ]
  | [ H : _ _ ?A ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute1
              with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))); wrapup ]
  | [ H : _ _ ?A ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute1
              with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))));
                wrapup ]
  | [ H : _ _ ?A ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [
      eapply CallCompute1
        with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))));
          wrapup ]
  | [ H : _ _ ?A ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [
      eapply CallCompute1
        with (midx :=
                Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))));
          wrapup ]
  end.

Ltac solve_for2 :=
  match goal with
  | [ H : _ _ ?A ?B ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute2
              with (midx := Fin.F1); wrapup ]
  | [ H : _ _ ?A ?B ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute2
              with (midx := Fin.FS Fin.F1); wrapup ]
  | [ H : _ _ ?A ?B ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute2
              with (midx := Fin.FS (Fin.FS Fin.F1)); wrapup ]
  | [ H : _ _ ?A ?B ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute2
              with (midx := Fin.FS (Fin.FS (Fin.FS Fin.F1))); wrapup ]
  | [ H : _ _ ?A ?B ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute2
              with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))); wrapup ]
  | [ H : _ _ ?A ?B ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute2
              with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))); wrapup ]
  | [ H : _ _ ?A ?B ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute2
              with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))));
                wrapup ]
  | [ H : _ _ ?A ?B ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [
      eapply CallCompute2
        with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))));
          wrapup ]
  | [ H : _ _ ?A ?B ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [
      eapply CallCompute2
        with (midx :=
                Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))));
          wrapup ]
  end.

Ltac solve_for3 :=
  match goal with
  | [ H : _ _ ?A ?B ?C ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute3
              with (midx := Fin.F1); wrapup ]
  | [ H : _ _ ?A ?B ?C ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute3
              with (midx := Fin.FS Fin.F1); wrapup ]
  | [ H : _ _ ?A ?B ?C ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute3
              with (midx := Fin.FS (Fin.FS Fin.F1)); wrapup ]
  | [ H : _ _ ?A ?B ?C ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute3
              with (midx := Fin.FS (Fin.FS (Fin.FS Fin.F1))); wrapup ]
  | [ H : _ _ ?A ?B ?C ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute3
              with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))); wrapup ]
  | [ H : _ _ ?A ?B ?C ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute3
              with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))); wrapup ]
  | [ H : _ _ ?A ?B ?C ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute3
              with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))));
                wrapup ]
  | [ H : _ _ ?A ?B ?C ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [
      eapply CallCompute3
        with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))));
          wrapup ]
  | [ H : _ _ ?A ?B ?C ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [
      eapply CallCompute3
        with (midx :=
                Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))));
          wrapup ]
  end.

Ltac solve_for4 :=
  match goal with
  | [ H : _ _ ?A ?B ?C ?D ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute4
              with (midx := Fin.F1); wrapup ]
  | [ H : _ _ ?A ?B ?C ?D ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute4
              with (midx := Fin.FS Fin.F1); wrapup ]
  | [ H : _ _ ?A ?B ?C ?D ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute4
              with (midx := Fin.FS (Fin.FS Fin.F1)); wrapup ]
  | [ H : _ _ ?A ?B ?C ?D ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute4
              with (midx := Fin.FS (Fin.FS (Fin.FS Fin.F1))); wrapup ]
  | [ H : _ _ ?A ?B ?C ?D ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute4
              with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))); wrapup ]
  | [ H : _ _ ?A ?B ?C ?D ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute4
              with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))); wrapup ]
  | [ H : _ _ ?A ?B ?C ?D ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [ eapply CallCompute4
              with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))));
                wrapup ]
  | [ H : _ _ ?A ?B ?C ?D ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [
      eapply CallCompute4
        with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))));
          wrapup ]
  | [ H : _ _ ?A ?B ?C ?D ↝ (?R, _) |- MethodCall_Computes _ _ _ ?R _ ] =>
    solve [
      eapply CallCompute4
        with (midx :=
                Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))));
          wrapup ]
  end.

Ltac solve_for_call :=
  first [ solve_for1 | solve_for2 | solve_for3 | solve_for4 ].

Ltac tsubst :=
  repeat
    match goal with
    | [ H : (_, _) = (_, _) |- _ ] => inv H
    | [ H : (_, _, _) = (_, _, _) |- _ ] => inv H
    | [ H : (_, _, _, _) = (_, _, _, _) |- _ ] => inv H
    end;
  subst.

Ltac build_computational_spine :=
  repeat match goal with
  | [ |- reflect_ADT_DSL_computation _ _ ] => eexists; intros
  | H : {a' | @?P a'} ↝ _ |- _ => apply Pick_inv in H
  | H : Return ?a ↝ _ |- _ =>
    apply Return_inv in H; tsubst; try apply CPure
  | H : Bind (A := ?A) ?ca ?k ↝ _ |- _ =>
    apply Bind_inv in H;
    let a' := fresh "v" in
    let H' := fresh H "'" in
    destruct H as [a' [H H'] ];
    eapply CJoin
  end;
  computes_to_inv; tsubst; simpl in *;
  repeat match goal with
  | [ H : _ * _ |- _ ] => destruct H
  | [ H : () |- _ ] => destruct H
  end;
  first [ solve_for_call | simpl in *; solve_for_call ].

Ltac simplify_reflection :=
  eapply reflect_ADT_DSL_computation_simplify;
  [ set_evars; intros;
    autorewrite with monad laws; simpl;
    try rewrite refineEquiv_If_Then_Else_Bind;
    finish honing
  | try (eapply reflect_ADT_DSL_computation_If_Then_Else;
         [| | let r := fresh "r" in
              intro r; destruct r; simpl; reflexivity]) ].

Ltac compile_term :=
  repeat (autounfold; simpl);
  repeat (repeat simplify_reflection; build_computational_spine).

(****************************************************************************
 * Denote a [ClientDSL] term into a Fiat computation for a particular ADT.
 * This is strictly the inverse of compilation.
 ****************************************************************************)

Section Denotation.

Variable sig : ADTSig.
Variable adt : ADT sig.

Program Instance ADT_Method_Functor :
  Functor (fun A : Type => Rep adt -> Comp (Rep adt * A)) := {
  fmap := fun _ _ f x r => `(r', a) <- x r; ret (r', f a)
}.

Program Instance ADT_Method_Applicative :
  Applicative (fun A : Type => Rep adt -> Comp (Rep adt * A)) := {
  pure := fun _ x r => ret (r, x);
  ap := fun _ _ mf mx r => `(r', f) <- mf r;
                           `(r', x) <- mx r';
                           ret (r', f x)
}.

Program Instance ADT_Method_Monad :
  Monad (fun A : Type => Rep adt -> Comp (Rep adt * A)) := {
  join := fun _ mm r => `(r', m) <- mm r; m r'
}.

Import EqNotations.

Definition denote {A : Type} : ClientDSL sig A -> Rep adt -> Comp (Rep adt * A) :=
  foldFree (fun T (c : MethodCall T) =>
              match c with
              | Call midx _ _ H1 H2 args k =>
                fun r =>
                  `(r', x) <- applyArgs (rew H2 in Methods adt midx)
                                        (rew <- H1 in args) r;
                  ret (r', k x)
              end).

Corollary denote_Pure : forall A (x : A) r,
  refineEquiv (denote (Pure x) r) (ret (r, x)).
Proof. reflexivity. Qed.

Lemma denote_Join :
  forall A B (k : A -> ClientDSL sig B) (h : MethodCall A) r,
  refineEquiv (denote (Join k h) r)
              (denote (liftF h) r >>= fun p => denote (k (snd p)) (fst p)).
Proof.
  intros.
  destruct h.
  autorewrite with monad laws.
  reflexivity.
Qed.

Lemma denote_Free_bind :
  forall A (x : ClientDSL sig A) B (k : A -> ClientDSL sig B) r,
    refineEquiv (denote (Free_bind k x) r)
                (denote x r >>= fun p => denote (k (snd p)) (fst p)).
Proof.
  intros.
  generalize dependent r.
  induction x; simpl; intros.
    rewrite denote_Pure.
    autorewrite with monad laws; simpl.
    reflexivity.
  rewrite denote_Join.
  setoid_rewrite H.
  rewrite denote_Join.
  autorewrite with monad laws; simpl.
  reflexivity.
Qed.

Corollary denote_If :
  forall b A (t e : ClientDSL sig A) r,
    refineEquiv (denote (If b Then t Else e) r)
                (If b Then denote t r Else denote e r).
Proof. destruct b; simpl; reflexivity. Qed.

Lemma ADT_Computes_denotation : forall A f r r' (v : A),
  denote f r ↝ (r', v) -> ADT_Computes adt f r r' v.
Proof.
  intros.
  generalize dependent r.
  induction f; intros.
    apply denote_Pure in H.
    computes_to_inv; tsubst.
    apply CPure.
  apply denote_Join in H0.
  computes_to_inv; tsubst.
  destruct v0; simpl in *.
  destruct f0;
  revert H0;
  unfold denote; simpl;
  unfold compose, comp, Bind2, Free_bind; simpl;
  intro H0;
  computes_to_inv; tsubst;
  destruct v2;
  eapply CJoin;
  simpl in H0'.
    apply H; eauto.
  simpl in *.
  computes_to_inv; tsubst.
  eapply CallComputes; eauto.
Qed.

End Denotation.

(****************************************************************************
 * Compile [buffer_cons] into a [ClientDSL] term
 ****************************************************************************)

Module ByteStringFFI (M : WSfun N_as_DT).

Module Import ByteStringHeap := ByteStringHeap M.
Module Import FunMaps := FunMaps N_as_DT M.

Import HeapCanonical.
Import Heap.

Hint Unfold id.
Hint Unfold bind.
Hint Unfold Bind2.
Hint Unfold allocate_buffer.
Hint Unfold HeapState.find_free_block.
Hint Unfold make_room_by_growing_buffer.
Hint Unfold make_room_by_shifting_up.
Hint Unfold ByteStringHeap.buffer_cons_obligation_2.
Hint Unfold ByteStringHeap.buffer_cons_obligation_3.
Hint Unfold poke_at_offset.
Hint Unfold buffer_cons.

Definition consDSL w :
  reflect_ADT_DSL_computation HeapSpec
    (fun r => r' <- buffer_cons (fst r) (snd r) w; ret (r', ()))%comp.
Proof.
  Local Opaque poke.
  Local Opaque alloc.
  Local Opaque free.
  Local Opaque peek.
  Local Opaque memcpy.

  Time compile_term.

  Local Transparent poke.
  Local Transparent alloc.
  Local Transparent free.
  Local Transparent peek.
  Local Transparent memcpy.
Defined.

Theorem consDSL_correct : forall (r : Rep HeapSpec) (bs : PS) w,
  refine (buffer_cons r bs w)
         (res <- denote HeapSpec (projT1 (consDSL w) bs) r;
          ret (fst res, fst (snd res))).
Proof.
  intros.
  unfold buffer_cons, consDSL, Bind2; simpl.
  remember (exist (fun len : Size => 0 < len)
                  (psLength bs + 1) _) as ev.
  rewrite denote_If, !refineEquiv_If_Then_Else_Bind; simpl.
  apply refine_If_Then_Else.
    Time autorewrite with monad laws; reflexivity.
  rewrite denote_If, refineEquiv_If_Then_Else_Bind; simpl.
  apply refine_If_Then_Else.
    rewrite denote_Join.
    unfold denote; simpl.
    unfold Bind2, id; simpl.
    do 3 rewrite refineEquiv_bind_unit; simpl.
    rewrite refineEquiv_bind_unit; simpl.
    unfold id; simpl.
    do 3 rewrite refineEquiv_bind_unit; simpl.
    rewrite refineEquiv_bind_unit; simpl.
    autorewrite with monad laws; reflexivity.
  rewrite denote_If, refineEquiv_If_Then_Else_Bind; simpl.
  apply refine_If_Then_Else.
    rewrite denote_Join.
    unfold denote; simpl.
    unfold Bind2, id; simpl.
    unfold HeapState.find_free_block.
    do 5 rewrite refineEquiv_bind_bind.
    setoid_rewrite refineEquiv_bind_unit; simpl.
    unfold make_room_by_growing_buffer, alloc, HeapState.find_free_block.
    unfold Bind2, id; simpl.
    rewrite refineEquiv_bind_bind.
    rewrite refineEquiv_bind_bind.
    do 4 setoid_rewrite refineEquiv_bind_unit; simpl.
    do 2 setoid_rewrite refineEquiv_bind_unit; simpl.
    unfold id; simpl.
    do 3 setoid_rewrite refineEquiv_bind_unit; simpl.
    unfold id; simpl.
    do 3 setoid_rewrite refineEquiv_bind_unit; simpl.
    setoid_rewrite refineEquiv_bind_unit; simpl.
    rewrite Heqev; simpl.
    reflexivity.
  Time autorewrite with monad laws; reflexivity.
Time Qed.

(****************************************************************************
 * Denote a [ClientDSL HeapSpec] term into a GHC computation
 ****************************************************************************)

Axiom IO : Type -> Type.

Axiom fmapIO   : forall {a b : Type}, (a -> b) -> IO a -> IO b.
Axiom bindIO   : forall {a b : Type}, IO a -> (a -> IO b) -> IO b.
Axiom returnIO : forall {a : Type}, a -> IO a.
Axiom failIO   : forall {a : Type}, IO a.
Axiom joinIO   : forall {a : Type}, IO (IO a) -> IO a.

Axiom bindIO_returnIO : forall {a b : Type} (f : a -> b) (x : IO a),
  bindIO x (fun a => returnIO (f a)) = fmapIO f x.

Axiom unsafeDupablePerformIO : forall {a : Type}, IO a -> a.

Axiom malloc  : Size -> IO (Ptr Word).
Axiom free    : Ptr Word -> IO ().
Axiom realloc : Ptr Word -> Size -> IO (Ptr Word).
Axiom peek    : Ptr Word -> IO Word.
Axiom poke    : Ptr Word -> Word -> IO ().
Axiom memcpy  : Ptr Word -> Ptr Word -> Size -> IO ().
Axiom memset  : Ptr Word -> Size -> Word -> IO ().

Definition ghcDenote {A : Type} : ClientDSL (getADTSig HeapSpec) (IO A) -> IO A.
Proof.
  intros.
  eapply (iter _) in X.
  exact X.
  Unshelve.
  clear X.
  destruct 1.
  subst.
  simpl in midx.
  dependent destruction midx; simpl in *.
    inv e0. inv h.
    exact (bindIO (malloc (` X)) i).
  dependent destruction midx; simpl in *.
    inv e0. inv h.
    exact (bindIO (free X) i).
  dependent destruction midx; simpl in *.
    inv e0. inv h. inv X0.
    exact (bindIO (realloc X (` X1)) i).
  dependent destruction midx; simpl in *.
    inv e0. inv h.
    exact (bindIO (peek X) i).
  dependent destruction midx; simpl in *.
    inv e0. inv h. inv X0.
    exact (bindIO (poke X X1) i).
  dependent destruction midx; simpl in *.
    inv e0. inv h. inv X0. inv X2.
    exact (bindIO (memcpy X X1 X0) i).
  dependent destruction midx; simpl in *.
    inv e0. inv h. inv X0. inv X2.
    exact (bindIO (memset X X1 X0) i).
  inversion midx.
Defined.

Corollary bind_If `{Monad f} : forall A B (k : A -> f B) b t e,
  ((If b Then t Else e) >>= k) = If b Then t >>= k Else e >>= k.
Proof. destruct b; reflexivity. Qed.

Corollary fmap_If `{Functor f} : forall A B (k : A -> B) b t e,
  fmap k (If b Then t Else e) = If b Then fmap k t Else fmap k e.
Proof. destruct b; reflexivity. Qed.

Corollary iter_If `{Functor f} : forall A (phi : f A -> A) b t e,
  iter phi (If b Then t Else e) = If b Then iter phi t Else iter phi e.
Proof. destruct b; reflexivity. Qed.

Corollary ghcDenote_If : forall A b (t e : ClientDSL (getADTSig HeapSpec) (IO A)),
  ghcDenote (If b Then t Else e) = If b Then ghcDenote t Else ghcDenote e.
Proof. destruct b; reflexivity. Qed.

Lemma ghcConsDSL :
  { f : PS -> Word -> PS
  & forall bs w,
      f bs w = unsafeDupablePerformIO
                 (ghcDenote ((returnIO \o fst) <$> projT1 (consDSL w) bs)) }.
Proof.
  eexists; intros.
  symmetry.
  simpl projT1.
  unfold comp.
  rewrite !fmap_If.
  etransitivity.
    do 3 setoid_rewrite ghcDenote_If.
    reflexivity.
  simpl.
  do 4 (unfold compose, comp; simpl).
  unfold ghcDenote; simpl.
  unfold solution_left.
  unfold eq_rect_r, eq_rect; simpl.
  unfold simplification_heq.
  unfold solution_right.
  unfold eq_rect_r, eq_rect; simpl.
  repeat (rewrite JMeq_eq_refl; unfold compose, comp; simpl).
  rewrite !bindIO_returnIO.
  higher_order_reflexivity.
Defined.

Definition ghcConsDSL' := Eval simpl in projT1 ghcConsDSL.
Print ghcConsDSL'.

End ByteStringFFI.

(****************************************************************************

This is the code we intend to approximate with the FFI refined version of
ByteString:

  import Data.Word8
  import GHC.ForeignPtr
  import GHC.IO

  data ByteString = PS {-# UNPACK #-} !(ForeignPtr Word8) -- payload
                       {-# UNPACK #-} !Int                -- offset
                       {-# UNPACK #-} !Int                -- length
      deriving (Typeable)

  {--[ cons ]---------------------------------------------------------------}

  mallocByteString :: Int -> IO (ForeignPtr a)
  mallocByteString l = GHC.mallocPlainForeignPtrBytes l

  create :: Int -> (Ptr Word8 -> IO ()) -> IO ByteString
  create l f = do
      fp <- mallocByteString l
      withForeignPtr fp $ \p -> f p
      return $! PS fp 0 l

  unsafeCreate :: Int -> (Ptr Word8 -> IO ()) -> ByteString
  unsafeCreate l f = unsafeDupablePerformIO (create l f)

  foreign import ccall unsafe "string.h memcpy" c_memcpy
      :: Ptr Word8 -> Ptr Word8 -> CSize -> IO (Ptr Word8)

  memcpy :: Ptr Word8 -> Ptr Word8 -> Int -> IO ()
  memcpy p q s = c_memcpy p q (fromIntegral s) >> return ()

  cons :: Word8 -> ByteString -> ByteString
  cons c (PS x s l) = unsafeCreate (l+1) $ \p -> withForeignPtr x $ \f -> do
          poke p c
          memcpy (p `plusPtr` 1) (f `plusPtr` s) (fromIntegral l)

  {--[ uncons ]-------------------------------------------------------------}

  accursedUnutterablePerformIO :: IO a -> a
  accursedUnutterablePerformIO (IO m) = case m realWorld# of (# _, r #) -> r

  uncons :: ByteString -> Maybe (Word8, ByteString)
  uncons (PS x s l)
      | l <= 0    = Nothing
      | otherwise = Just (accursedUnutterablePerformIO $ withForeignPtr x
                                                       $ \p -> peekByteOff p s,
                          PS x (s+1) (l-1))

****************************************************************************)
