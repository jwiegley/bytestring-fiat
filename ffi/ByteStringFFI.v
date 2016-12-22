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

Ltac tsubst :=
  repeat
    match goal with
    | [ H : (_, _) = (_, _) |- _ ] => inv H
    | [ H : (_, _, _) = (_, _, _) |- _ ] => inv H
    | [ H : (_, _, _, _) = (_, _, _, _) |- _ ] => inv H
    end;
  subst.

Section ClientDSL.

Variable sig : ADTSig.

Inductive MethodCall (rec : Type) : Type :=
| Call : forall (midx : MethodIndex sig),
    hlist (fst (MethodDomCod sig midx))
    -> match snd (MethodDomCod sig midx) with
        | Some cod => cod -> rec
        | None => rec end
    -> MethodCall rec.

Definition MethodCall_fmap (A B : Type) (f : A -> B) (mc : MethodCall A) :
  MethodCall B :=
  match mc with
  | Call midx args k =>
    Call B midx args
         (match (snd (MethodDomCod sig midx)) as cod return
                match cod with
                | Some cod => cod -> A
                | None => A end
                -> match cod with
                   | Some cod => cod -> B
                   | None => B end
          with
          | Some cod => fun k cod => f (k cod)
          | None => fun k => f k
          end k)
  end.

Global Program Instance MethodCall_Functor : Functor MethodCall :=
  {
    fmap := MethodCall_fmap
  }.

Definition ClientDSL := Free MethodCall.

(****************************************************************************
 * ADT_Computes: Relates a [ClientDSL] term to a Fiat computation using an
 * ADT of the same signature.
 ****************************************************************************)

Variable adt : ADT sig.

Fixpoint applyArgs
         (dom : list Type)
         {rep : Type}
         (cod : option Type)
         (meth : methodType rep dom cod)
         (args : hlist dom)
  : rep -> Comp match cod with
                | Some A => rep * A
                | _ => rep
                end:=
  match dom return hlist dom
                   -> methodType rep dom cod
                   -> rep
                   -> Comp match cod with
                           | Some A => rep * A
                           | _ => rep
                           end with
  | nil => fun _ =>
             match cod return
                   methodType rep [] cod ->
                   rep -> Comp match cod with
                               | Some A => rep * A
                               | _ => rep
                               end with
             | Some A => id
             | None => id
             end
  | cons t ts =>
    fun (args : hlist (t :: ts))
        (meth : methodType rep (t :: ts) cod) =>
      applyArgs (fun r => meth r (hlist_head args))
                (hlist_tail args)
  end args meth.

Inductive methodType_Computes :
  forall rep dom cod B,
    methodType rep dom cod
    -> rep
    -> hlist dom
    -> rep
    -> (match cod with
        | Some A => A -> B
        | None => B
        end)
    -> B
    -> Prop :=
| CallSome :
    forall rep dom cod B
           (meth : methodType rep dom (Some cod))
           r args r' (k : cod -> B) v x,
      k v = x ->
      applyArgs meth args r ↝ (r', v) ->
      methodType_Computes meth r args r' k x
| CallNone :
    forall rep dom B
           (meth : methodType rep dom None)
           r args r' (k : B) x,
      k = x ->
      applyArgs meth args r ↝ r' ->
      methodType_Computes meth r args r' k k.

Lemma methodType_computes_inv
  : forall rep dom cod B
           (meth : methodType rep dom cod)
           (r : rep)
           (args : hlist dom)
           (r' : rep)
           (k : match cod with
                | Some A => A -> B
                | None => B
                end)
           (v : B)
           (z : methodType_Computes meth r args r' k v),
    match cod return
          match cod with
          | Some A => A -> B
          | None => B
          end ->
          Comp match cod with
               | Some A => rep * A
               | _ => rep
               end
          -> Prop with
    | Some A => fun k meth' =>
                  exists v',
                    k v' = v
                    /\ meth' ↝ (r', v')
    | None => fun k meth'  =>
                  k = v
                  /\ meth' ↝ r'
    end k (applyArgs meth args r).
Proof.
  intros.
  destruct z; eauto.
Qed.

Inductive MethodCall_Computes
  : forall A, MethodCall A -> Rep adt -> Rep adt -> A -> Prop :=
  | CallComputes (midx : MethodIndex sig)
    : forall (r r' : Rep adt) args B k v,
        methodType_Computes (B := B) (Methods adt midx) r args r' k v
        -> MethodCall_Computes (Call _ midx args k) r r' v.

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
 * Denote a [ClientDSL] term into a Fiat computation for a particular ADT.
 * This is strictly the inverse of compilation.
 ****************************************************************************)

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

Definition denote {A : Type} : ClientDSL A -> Rep adt -> Comp (Rep adt * A)
  := foldFree (H := ADT_Method_Monad) (fun T (c : MethodCall T) =>
              match c with
              | Call midx args k =>
                fun r =>
                  (x <- applyArgs (Methods adt midx) args r;
                   ret (match snd (MethodDomCod sig midx) as cod return
                            match cod with
                            | Some A' => Rep adt * A'
                            | _ => Rep adt
                            end
                            ->
                            match cod with
                            | Some A' => A' -> T
                            | _ => T
                            end
                            -> _
                      with
                        | Some _ => fun x k => (fst x, k (snd x))
                        | None => fun x k => (x, k)
                        end x k))%comp
              end).

Corollary denote_Pure : forall A (x : A) r,
  refineEquiv (denote (Pure x) r) (ret (r, x)).
Proof. reflexivity. Qed.

Lemma denote_Join :
  forall A B (k : A -> ClientDSL B) (h : MethodCall A) r,
  refineEquiv (denote (Join k h) r)
              (denote (liftF h) r >>= fun p => denote (k (snd p)) (fst p)).
Proof.
  intros.
  destruct h.
  autorewrite with monad laws.
  reflexivity.
Qed.

Lemma denote_Free_bind :
  forall A (x : ClientDSL A) B (k : A -> ClientDSL B) r,
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
  forall b A (t e : ClientDSL A) r,
    refineEquiv (denote (If b Then t Else e) r)
                (If b Then denote t r Else denote e r).
Proof. destruct b; simpl; reflexivity. Qed.

Lemma ADT_Computes_denotation : forall A f r r' (v : A),
  denote f r ↝ (r', v) <-> ADT_Computes f r r' v.
Proof.
  split; intros.
  - generalize dependent r.
    induction f; intros.
    apply denote_Pure in H.
    computes_to_inv; tsubst.
    apply CPure.
    apply denote_Join in H0.
    computes_to_inv; tsubst.
    destruct v0; simpl in *.
    destruct f0.
    revert H0;
      unfold denote; simpl;
        unfold compose, comp, Bind2, Free_bind; simpl;
          intro H0;
          computes_to_inv; tsubst.
    econstructor.
    apply H; eauto.
    assert (methodType_Computes (Methods adt midx) r h r0 y x0).
    revert y v2 H0 H0'0.
    generalize (Methods adt midx).
    destruct (snd (MethodDomCod sig midx)); intros;
      simpl in *; computes_to_inv; injections; subst.
    destruct v2; simpl in *.
    econstructor; eauto.
    econstructor 2; eauto.
    econstructor; eauto.
  -  generalize dependent r.
     induction f; intros.
     apply computes_to_refine.
     rewrite denote_Pure.
     inv H.
     apply inj_pair2 in H2; subst.
     apply inj_pair2 in H5; subst.
     reflexivity.
     apply computes_to_refine.
     rewrite denote_Join.
     inv H0.
     apply inj_pair2 in H2; subst.
     apply inj_pair2 in H2; subst.
     apply inj_pair2 in H5; subst.
     apply inj_pair2 in H8; subst.
     destruct H9.
     unfold denote at 1; simpl.
     unfold Bind2; simpl.
     autorewrite with monad laws; simpl.
     apply H in H7; clear H.
     revert H0.
     generalize (Methods adt midx); intros.
     etransitivity.
     apply refine_under_bind.
     intros; clear H m H0 H7.
     revert k a.
     instantiate (1 := match (snd (MethodDomCod sig midx)) as cod return
                             match cod with
                             | Some A0 => A0 -> B
                             | None => B
                             end
                             -> match cod with
                             | Some A0 => Rep adt * A0
                             | None => Rep adt
                             end -> _
                       with
                       | Some _ => fun k a => denote (f (k (snd a))) (fst a)
                       | None => fun k a => denote (f k) a
                       end k).
     destruct (snd (MethodDomCod sig midx)); simpl;
       higher_order_reflexivity.
     generalize dependent (snd (MethodDomCod sig midx)); intros.
     apply methodType_computes_inv in H0.
     destruct o; destruct_ex; intuition; subst;
       apply refine_computes_to in H1; rewrite H1;
         simplify with monad laws; simpl;
           eapply refine_computes_to; eauto.
Qed.

(****************************************************************************
 * reflect_ADT_DSL_computation: Helper lemmas to abstract a Fiat
 * computation into its equivalent [ClientDSL] term.
 ****************************************************************************)

Definition reflect_ADT_DSL_computation {A B : Type}
           (c : Rep adt * B -> Comp ((Rep adt * B) * A)) :=
  { f : B -> ClientDSL (B * A)
             & (forall r bs r' bs' v,
                   c (r, bs) ↝ ((r', bs'), v)
                   -> ADT_Computes (f bs) r r' (bs', v) )
               /\ forall r bs r' bs' v,
                 ADT_Computes (f bs) r r' (bs', v)
                 -> c (r, bs) ↝ ((r', bs'), v) }.

Lemma reflect_ADT_DSL_computation_simplify {B C : Type} c c'
      (refine_c_c' : forall r, refineEquiv (c r) (c' r))
      (c_DSL : reflect_ADT_DSL_computation c')
  : reflect_ADT_DSL_computation (A := C) (B := B) c.
Proof.
  exists (projT1 c_DSL); intros.
  destruct (projT2 c_DSL); simpl in *.
  split.
  - intros; apply H; apply refine_c_c'; auto.
  - intros; apply refine_c_c'; auto.
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
  split; intros.
  - rewrite H in H0.
    apply If_Then_Else_computes_to in H0.
    simpl in *.
    destruct (c' _).
    destruct c_DSL.
    simpl in *.
    apply a; assumption.
    destruct k_DSL.
    simpl in *.
    apply a; assumption.
  - rewrite H; simpl.
    destruct (c' bs); simpl in *.
    destruct c_DSL.
    simpl in *.
    apply a; assumption.
    destruct k_DSL.
    simpl in *.
    apply a; assumption.
Defined.

End ClientDSL.

Arguments MethodCall {sig} rec.
Arguments Call {sig rec} midx _ _.

Lemma denote_refineEquiv A B sig adt (comp : Rep adt * B -> Comp (Rep adt * B * A))
  : forall (r : Rep adt) (b : B) (reflected : reflect_ADT_DSL_computation adt comp),
    refineEquiv
      (comp (r, b))
      (r' <- denote (sig := sig) adt (projT1 reflected b) r;
         ret ((fst r', (fst (snd r'))), snd (snd r'))).
Proof.
  unfold reflect_ADT_DSL_computation; intros ? ? [? [? ?]]; simpl.
  specialize (a r b).
  specialize (c r b).
  split.
  - intros [ [? ?] ?] Comp_v; eapply c.
    computes_to_inv; simpl in *; injections.
    generalize v r Comp_v; clear.
    induction (x b); simpl.
    + unfold denote; simpl; intros.
      computes_to_inv; subst; simpl.
      replace (fst a, snd a) with a by (destruct a; reflexivity).
      econstructor.
    +  destruct v as [? [? ?] ]; simpl in *.
       intros.
       eapply denote_Join in Comp_v; computes_to_inv.
       destruct v; simpl in *.
       eapply H in Comp_v'.
       simpl in Comp_v'.
       econstructor.
       eapply Comp_v'.
       unfold denote in Comp_v; simpl in *; unfold Bind2 in *; destruct f0;
         intros; computes_to_inv; injections; subst; simpl in *.
       computes_to_inv; injections; subst.
       clear Comp_v'; econstructor.
       generalize dependent (Methods adt midx).
       generalize dependent (snd (MethodDomCod sig midx)).
       destruct o; intros; simpl in *.
       replace v1 with (fst v1, snd v1) in * by (destruct v1; reflexivity).
       econstructor; try eassumption; reflexivity.
       econstructor; try eassumption; reflexivity.
  - intros [ [? ?] ?] Comp_v; apply a in Comp_v.
    generalize r b0 a0 r0 Comp_v; clear; induction (x b);
      simpl; intros; inversion Comp_v; subst.
    + unfold denote; simpl.
      apply inj_pair2 in H1; subst.
      apply inj_pair2 in H4; subst.
      repeat computes_to_econstructor; eauto.
    + apply inj_pair2 in H1; subst.
      apply inj_pair2 in H4; subst.
      apply inj_pair2 in H1; subst.
      apply inj_pair2 in H7; subst.
      unfold denote; simpl; unfold Bind2; simpl.
      destruct f0.
      repeat apply refine_bind_bind.
      setoid_rewrite refine_bind_unit.
      simpl.
      eapply refine_under_bind; intros.
      set_evars;  rewrite refineEquiv_bind_unit; simpl.
      subst H1. higher_order_reflexivity.
      simpl.
      assert (methodType_Computes (Methods adt midx) r h r' y v).
      { revert H8; clear; intro.
        inversion H8.
        apply inj_pair2 in H2; subst.
        apply inj_pair2 in H3; subst.
        apply inj_pair2 in H6; subst.
        apply inj_pair2 in H3; subst.
        assumption.
      }
      apply methodType_computes_inv in H0.
      clear H8 Comp_v.
      generalize dependent (Methods adt midx).
      generalize dependent (snd (MethodDomCod sig midx)).
      destruct o; intros.
      * destruct_ex; intuition; subst.
        computes_to_econstructor; eauto.
      * intuition; subst.
        computes_to_econstructor; eauto.
Qed.

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
    | [ H : _ _ ?A ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec Fin.F1)
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A HNil);
           [ | eapply H]
          | eapply CallNone with (args := HCons A HNil);
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS Fin.F1))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A HNil);
           [ | eapply H]
          | eapply CallNone with (args := HCons A HNil);
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS Fin.F1)))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A HNil);
           [ | eapply H]
          | eapply CallNone with (args := HCons A HNil);
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A HNil);
           [ | eapply H]
          | eapply CallNone with (args := HCons A HNil);
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1))))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A HNil);
           [ | eapply H]
          | eapply CallNone with (args := HCons A HNil);
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A HNil);
           [ | eapply H]
          | eapply CallNone with (args := HCons A HNil);
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A HNil);
           [ | eapply H]
          | eapply CallNone with (args := HCons A HNil);
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A HNil);
           [ | eapply H]
          | eapply CallNone with (args := HCons A HNil);
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A HNil);
           [ | eapply H]
          | eapply CallNone with (args := HCons A HNil);
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
 end.

Ltac solve_for2 :=
 match goal with
    | [ H : _ _ ?A ?B ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec Fin.F1)
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B HNil));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS Fin.F1))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B HNil));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS Fin.F1)))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B HNil));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B HNil));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1))))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B HNil));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B HNil));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B HNil));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B HNil));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B HNil));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
 end.

Ltac solve_for3 :=
 match goal with
    | [ H : _ _ ?A ?B ?C ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec Fin.F1)
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B (HCons C HNil)));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B (HCons C HNil)));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ?C ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS Fin.F1))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B (HCons C HNil)));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B (HCons C HNil)));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ?C ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS Fin.F1)))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B (HCons C HNil)));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B (HCons C HNil)));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ?C ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B (HCons C HNil)));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B (HCons C HNil)));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ?C ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1))))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B (HCons C HNil)));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B HCons C HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ?C ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B (HCons C HNil)));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B (HCons C HNil)));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ?C ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B (HCons C HNil)));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B (HCons C HNil)));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ?C ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B (HCons C HNil)));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B (HCons C HNil)));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ?C ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B (HCons C HNil)));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B (HCons C HNil)));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
 end.

Ltac solve_for4 :=
 match goal with
    | [ H : _ _ ?A ?B ?C ?D ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec Fin.F1)
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D HNil))));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D HNil))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ?C ?D ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS Fin.F1))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D HNil))));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D HNil))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ?C ?D ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS Fin.F1)))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D HNil))));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D HNil))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ?C ?D ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D HNil))));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D HNil))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ?C ?D ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1))))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D HNil))));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D HNil))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ?C ?D ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D HNil))));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D HNil))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ?C ?D ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D HNil))));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D HNil))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ?C ?D ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons C (HCons D HNil))))));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ _ ?A ?B ?C ?D ↝ (?R, _) |- MethodCall_Computes ?ADTSpec _ ?R' ?R _ ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))))
      with (r := R') (r' := R);
        first
          [eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons C (HCons D HNil))))));
           [ | eapply H]
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    end.

Ltac solve_for_call :=
  first [ solve_for1 | solve_for2 | solve_for3 | solve_for4 ].

Ltac solve_for_call' :=
  match goal with
  | H : ADT_Computes _ _ _ _ _ |- _ =>
    simpl in H; inversion H; subst;
    repeat match goal with
           | H : existT _ _ _ = existT _ _ _ |- _ =>
             apply inj_pair2 in H; subst
           end;
    clear H
  | H : Free_Computes _ _ _ _ _ |- _ =>
    inversion H; subst;
    repeat match goal with
           | H : existT _ _ _ = existT _ _ _ |- _ =>
             apply inj_pair2 in H; subst
           end;
    clear H
  | H : MethodCall_Computes _ _ _ _ _ |- _ =>
    inversion H; simpl in *; subst;
    repeat match goal with
           | H : existT _ _ _ = existT _ _ _ |- _ =>
             apply inj_pair2 in H; subst
           end;
    clear H
  | H : methodType_Computes _ _ _ _ _ _ |- _ =>
    apply methodType_computes_inv in H; destruct_ex; intuition; subst;
    simpl in *; unfold id in *; simpl in *
  end;
  try computes_to_econstructor; injections; try eassumption.

Ltac build_computational_spine :=
repeat match goal with
           | [ |- reflect_ADT_DSL_computation _ _ ] => eexists; split; intros
           | H : {a' | @?P a'} ↝ _ |- _ => apply Pick_inv in H
           | H : Return ?a ↝ _ |- _ =>
             apply Return_inv in H; tsubst; try apply CPure
           | H : Bind (A := ?A) ?ca ?k ↝ _ |- _ =>
             apply Bind_inv in H;
               let r' := fresh "r" in
               let v' := fresh "v" in
               let H' := fresh H "'" in
               destruct H as [ [r' v'] [H H'] ];
                 simpl in *;
                 eapply (@CJoin _ _ _ _  _ _ _ _ _ _ _ r' v')
     end.

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
  repeat simplify_reflection; build_computational_spine;
  first [ solve_for_call | repeat solve_for_call' ].

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
Time Defined.

Theorem consDSL_correct : forall (r : Rep HeapSpec) (bs : PS) w,
  refine (r <- buffer_cons r bs w; ret (fst r, snd r, ()))
         (res <- denote HeapSpec (projT1 (consDSL w) bs) r;
          ret (fst res, fst (snd res), snd (snd res))).
Proof.
  intros.
  rewrite <- denote_refineEquiv; simpl.
  apply refine_under_bind; intros.
  destruct a; simpl; reflexivity.
Qed.

Hint Unfold buffer_uncons.

Definition unconsDSL :
  reflect_ADT_DSL_computation HeapSpec
    (fun r => buffer_uncons (fst r) (snd r))%comp.
Proof.
  Local Opaque poke.
  Local Opaque alloc.
  Local Opaque free.
  Local Opaque peek.
  Local Opaque memcpy.

  repeat (autounfold; simpl).
  simplify_reflection.
    eexists; split; intros.
      simpl in H.
      computes_to_inv; tsubst.
      destruct v0.
      Local Transparent peek.
      unfold peek in H.
      computes_to_inv; tsubst.
      econstructor.
        econstructor.
      eapply (CallComputes HeapSpec (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
        with (r := h) (r' := h).
      eapply CallSome with (args := HCons (psBuffer bs + psOffset bs) HNil).
        instantiate (1 := w).
        higher_order_reflexivity.
      simpl; unfold id; simpl.
      computes_to_econstructor.
        computes_to_econstructor.
        exact H.
      econstructor.
    simpl.
    destruct v.
      solve_for_call'.
        solve_for_call'.
          solve_for_call'.
          solve_for_call'.
          computes_to_inv; tsubst.
          rewrite (H1 _ H); clear H1 H.
          higher_order_reflexivity.
        solve_for_call'.
      solve_for_call'.
      solve_for_call'.
      solve_for_call'.
      computes_to_inv; tsubst.
      higher_order_reflexivity.
    solve_for_call'.
      solve_for_call'.
        solve_for_call'.
        solve_for_call'.
        computes_to_inv; tsubst.
      higher_order_reflexivity.
    solve_for_call'.
    solve_for_call'.
    solve_for_call'.
    computes_to_inv; tsubst.
  compile_term.
  auto.

  Local Transparent poke.
  Local Transparent alloc.
  Local Transparent free.
  Local Transparent peek.
  Local Transparent memcpy.

  Unshelve.
  exact Zero.
Defined.

Theorem unconsDSL_correct : forall (r : Rep HeapSpec) (bs : PS),
  refine (buffer_uncons r bs)
         (res <- denote HeapSpec (projT1 unconsDSL bs) r;
          ret (fst res, fst (snd res), snd (snd res))).
Proof.
  intros.
  rewrite <- denote_refineEquiv; simpl.
  reflexivity.
Qed.

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
  simpl in midx.
  revert h y.
  pattern midx; apply IterateBoundedIndex.Lookup_Iterate_Dep_Type;
    simpl; repeat constructor; intros.
    exact (bindIO (malloc (` (hlist_head h))) y).
    exact (bindIO (free (hlist_head h)) y).
    exact (bindIO (realloc (hlist_head h) (` (hlist_head (hlist_tail h)))) y).
    exact (bindIO (peek (hlist_head h)) y).
    exact (bindIO (poke (hlist_head h) (hlist_head (hlist_tail h))) y).
    exact (bindIO (memcpy (hlist_head h)
                         (hlist_head (hlist_tail h))
                         (hlist_head (hlist_tail (hlist_tail h)))) y).
    exact (bindIO (memset (hlist_head h)
                          (hlist_head (hlist_tail h))
                          (hlist_head (hlist_tail (hlist_tail h)))) y).
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
