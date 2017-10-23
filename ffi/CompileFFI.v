Require Import
  ByteString.Lib.Tactics
  ByteString.Lib.Nomega
  ByteString.Lib.Fiat
  ByteString.Lib.TupleEnsembles
  ByteString.Lib.FunMaps
  ByteString.Lib.FromADT
  ByteString.Lib.HList
  ByteString.Memory
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

Fixpoint repArgs (arity : nat) (rep : Type) : list Type :=
  match arity with
  | 0 => nil
  | S arity' => rep :: (repArgs arity' rep)
  end.

Inductive MethodCall rep (rec : Type) : Type :=
  | Call : forall (midx : MethodIndex sig),
      hlist (repArgs (fst (fst (MethodDomCod sig midx))) rep
               ++ snd (fst (MethodDomCod sig midx)))
        -> (rep -> match snd (MethodDomCod sig midx) with
                   | Some cod => cod -> rec
                   | None => rec
                   end)
        -> MethodCall rep rec.

Definition MethodCall_fmap rep (A B : Type) (f : A -> B) (mc : MethodCall rep A) :
  MethodCall rep B :=
  match mc with
  | Call midx args k =>
    @Call rep B midx args
          (match (snd (MethodDomCod sig midx)) as cod return
                 (rep -> match cod with
                         | Some cod => cod -> A
                         | None => A end)
                -> rep -> match cod with
                   | Some cod => cod -> B
                   | None => B end
          with
          | Some cod => fun k r' cod => f (k r' cod)
          | None => fun k r' => f (k r')
          end k)
  end.

Global Program Instance MethodCall_Functor {rep} : Functor (MethodCall rep) :=
  {
    fmap := @MethodCall_fmap rep
  }.

Definition ClientDSL rep := Free (MethodCall rep).

(****************************************************************************
 * ADT_Computes: Relates a [ClientDSL] term to a Fiat computation using an
 * ADT of the same signature.
 ****************************************************************************)

Variable adt : ADT sig.

Fixpoint applyArgs'
         (dom : list Type)
         {rep : Type}
         (cod : option Type)
         (meth : methodType' rep dom cod)
         (args : hlist dom)
  : Comp match cod with
         | Some A => rep * A
         | _ => rep
         end :=
  match dom return hlist dom
                   -> methodType' rep dom cod
                   -> Comp match cod with
                           | Some A => rep * A
                           | _ => rep
                           end with
  | nil => fun _ =>
             match cod as cod return
                   methodType' rep [] cod
                   -> Comp match cod with
                           | Some A => rep * A
                           | _ => rep
                           end with
             | Some A => id
             | None => id
             end
  | cons t ts =>
    fun (args : hlist (t :: ts))
        (meth : methodType' rep (t :: ts) cod) =>
      applyArgs' cod
                 (meth (hlist_head args))
                 (hlist_tail args)
  end args meth.

Fixpoint applyArgs
         (arity : nat)
         {dom : list Type}
         {rep : Type}
         {cod : option Type}
         (meth : methodType arity rep dom cod)
         (args : hlist (repArgs arity rep ++ dom))
  : Comp match cod with
         | Some A => rep * A
         | _ => rep
         end :=
  match arity return
        hlist (repArgs arity rep ++ dom)
        -> methodType arity rep dom cod
        -> _
  with
  | 0 =>
    fun args meth =>
      applyArgs' _ meth args
  | S arity' =>
    fun args meth =>
      applyArgs arity' (meth (hlist_head args))
                (hlist_tail args)
  end args meth.

Inductive methodType_Computes :
  forall {arity rep dom cod} B,
    methodType arity rep dom cod
    -> hlist (repArgs arity rep ++ dom)
    -> (rep ->
        match cod with
        | Some A => A -> B
        | None => B
        end)
    -> B
    -> Prop :=
| CallSome :
    forall arity rep dom cod B
           (meth : methodType arity rep dom (Some cod))
           args r' (k : rep -> cod -> B) v x,
      k r' v = x ->
      applyArgs arity meth args ↝ (r', v) ->
      @methodType_Computes arity _ dom (Some cod) _ meth args k x
| CallNone :
    forall arity rep dom B
           (meth : methodType arity rep dom None)
           args r' (k : rep -> B) x,
      k r' = x ->
      applyArgs arity meth args ↝ r' ->
      @methodType_Computes arity _ dom None _ meth args k x.

Lemma methodType_computes_inv
  : forall arity rep dom cod B
           (meth : methodType arity rep dom cod)
           (args : hlist _)
           (k : rep ->
                match cod with
                | Some A => A -> B
                | None => B
                end)
           (v : B)
           (z : methodType_Computes meth args k v),
    match cod return
          (rep ->
           match cod with
           | Some A => A -> B
           | None => B
           end) ->
          Comp match cod with
               | Some A => rep * A
               | _ => rep
               end
          -> Prop with
    | Some A => fun k meth' =>
                  exists r' v',
                    k r' v' = v
                    /\ meth' ↝ (r', v')
    | None => fun k meth'  =>
                exists r',
                  k r' = v
                  /\ meth' ↝ r'
    end k (applyArgs arity meth args).
Proof.
  intros.
  destruct z; eauto.
Qed.

Inductive MethodCall_Computes
  : forall A, MethodCall (Rep adt) A -> A -> Prop :=
  | CallComputes (midx : MethodIndex sig)
    : forall args B k v,
        methodType_Computes (B := B) (Methods adt midx) args k v
        -> MethodCall_Computes (@Call _ _ midx args k) v.

Inductive Free_Computes (R : Type)
          `{Functor (f R)}
          (crel : forall A, f R A -> A -> Prop) :
  forall {A}, Free (f R) A -> A -> Prop :=
  | CPure A (v : A) : Free_Computes R crel (Pure v) v
  | CJoin B (v' : B) :
      forall A t (k : A -> Free (f R) B) v,
        Free_Computes R crel (k v) v'
        -> crel A t v
        -> Free_Computes R crel (Join k t) v'.

Definition ADT_Computes {A : Type} :=
  Free_Computes _ (A := A) (@MethodCall_Computes).

(****************************************************************************
 * Denote a [ClientDSL] term into a Fiat computation for a particular ADT.
 * This is strictly the inverse of compilation.
 ****************************************************************************)

(* Program Instance ADT_Method_Functor :
  Functor (fun A : Type => Comp (Rep adt * A)) := {
  fmap := fun _ _ f x => `(r', a) <- x; ret (r', f a)
}.

Program Instance ADT_Method_Applicative :
  Applicative (fun A : Type => Comp (Rep adt * A)) := {
  pure := fun _ x => ret (r, x);
  ap := fun _ _ mf mx r => `(r', f) <- mf r;
                           `(r', x) <- mx r';
                           ret (r', f x)
}.

Program Instance ADT_Method_Monad :
  Monad (fun A : Type => Rep adt -> Comp (Rep adt * A)) := {
  join := fun _ mm r => `(r', m) <- mm r; m r'
}. *)

Instance Comp_Functor :
  Functor Comp := {
  fmap := fun _ _ f x => Bind x (fun a => ret (f a))
}.

Instance Comp_Applicative :
  Applicative Comp := {
  pure := ret;
  ap := fun _ _ mf mx =>
          Bind mf (fun f => Bind mx (fun x => ret (f x)))
                     }.

Instance Comp_Monad :
  Monad Comp :=
  { join := fun _ mm => Bind mm (fun m => m) }.

Import EqNotations.

Fixpoint denote {A : Type} (c : ClientDSL (Rep adt) A) : Comp A.
destruct c.
exact (ret a).
refine (match m with
        | Call midx args k =>
          x' <- applyArgs _ (Methods adt midx) args;
          match snd (MethodDomCod sig midx) as cod
                return
                (Rep adt ->
                 match cod with
                 | Some cod => cod -> x
                 | None => x
                 end) ->
                match cod with
                | Some A => Rep adt * A
                | None => Rep adt
                end -> _
          with
          | Some cod => fun k x => denote _ (f (k (fst x) (snd x)))
          | None => fun k x => denote _ (f (k x))
          end k x'
        end).
Defined.

(*Definition denote {A : Type} : ClientDSL (Rep adt) (Rep adt * A) -> Comp (Rep adt * A)
  := foldFree (H := fun a => @Comp_Monad (Rep) (fun T (c : MethodCall (Rep adt) (Rep adt * T)) =>
              match c with
              | Call midx args k =>
                (x <- applyArgs _ (Methods adt midx) args;
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
              end). *)

Corollary denote_Pure : forall A (x : A),
  refineEquiv (denote (Pure x)) (ret x).
Proof. reflexivity. Qed.

Lemma denote_Join :
  forall A B (k : A -> ClientDSL (Rep adt) (B))
         (h : MethodCall (Rep adt) A),
  refineEquiv (denote (Join k h))
              (denote (liftF h) >>= fun p => denote (k p)).
Proof.
  intros.
  destruct h; simpl.
  autorewrite with monad laws.
  apply refineEquiv_bind_Proper; [reflexivity|]; intro.
  destruct (snd (MethodDomCod sig midx));
  autorewrite with monad laws; reflexivity.
Qed.

Lemma denote_Free_bind :
  forall A (x : ClientDSL (Rep adt) A) B (k : A -> ClientDSL (Rep adt) B),
    refineEquiv (denote (Free_bind k x))
                (denote x >>= fun p => denote (k p)).
Proof.
  intros.
  induction x; simpl; intros.
    autorewrite with monad laws; simpl.
    reflexivity.
  destruct f0; simpl.
  autorewrite with monad laws.
  apply refineEquiv_bind_Proper; [reflexivity|]; intro.
  destruct (snd (MethodDomCod sig midx));
  rewrite H; reflexivity.
Qed.

Corollary denote_If :
  forall b A (t e : ClientDSL (Rep adt) A),
    refineEquiv (denote (If b Then t Else e))
                (If b Then denote t Else denote e).
Proof. destruct b; simpl; reflexivity. Qed.

Lemma ADT_Computes_denotation : forall A f (v : A),
  denote f ↝ v <-> ADT_Computes f v.
Proof.
  split; intros.
  - induction f; intros.
    + apply denote_Pure in H.
      computes_to_inv; tsubst.
      apply CPure.
    + apply denote_Join in H.
      computes_to_inv; tsubst.
      destruct f0.
      simpl in H.
      revert H;
        unfold denote; simpl;
        unfold compose, comp, Bind2, Free_bind; simpl;
          intro H'';
          computes_to_inv; tsubst.
      eapply CJoin.
      eapply H0; eauto.
      econstructor.
      revert v2 H''' H''.
      generalize (Methods adt midx).
      destruct (snd (MethodDomCod sig midx)); intros;
        simpl in *; computes_to_inv; injections; subst.
      destruct v2; simpl in *.
      econstructor; eauto.
      econstructor 2; eauto.
  - induction f; intros.
    + apply computes_to_refine.
      rewrite denote_Pure.
      inv H.
      apply inj_pair2 in H2; subst.
      apply inj_pair2 in H3; subst.
      reflexivity.
    + apply computes_to_refine.
      rewrite denote_Join.
      inv H.
      apply inj_pair2 in H2; subst.
      apply inj_pair2 in H2; subst.
      apply inj_pair2 in H5; subst.
      apply inj_pair2 in H6; subst.
      destruct H7.
      simplify with monad laws.
      apply H0 in H4; clear H0.
      revert H.
      generalize (Methods adt midx); intros.
      etransitivity.
      apply refine_under_bind.
      intros; clear H m H0.
      revert k a.
      instantiate (1 := fun a =>
                          match (snd (MethodDomCod sig midx)) as cod return
                              (Rep adt ->
                               match cod with
                               | Some A0 => A0 -> B
                               | None => B
                               end)
                              ->
                              (match cod with
                               | Some A0 => Rep adt * A0
                               | None => Rep adt
                               end) -> _
                          with
                          | Some _ => fun k a => denote (f (k (fst a) (snd a)))
                          | None => fun k a => denote (f (k a))
                          end k a).
      destruct (snd (MethodDomCod sig midx)); simpl.
      * intros; simplify with monad laws.
        higher_order_reflexivity.
      * intros; simplify with monad laws.
        higher_order_reflexivity.
      * generalize dependent (snd (MethodDomCod sig midx)); intros.
        apply methodType_computes_inv in H.
        destruct o; destruct_ex; intuition; subst;
          apply refine_computes_to in H1; rewrite H1;
            simplify with monad laws; simpl;
              eapply refine_computes_to; eauto.
Qed.

(****************************************************************************
 * reflect_ADT_DSL_computation: Helper lemmas to abstract a Fiat
 * computation into its equivalent [ClientDSL] term.
 ****************************************************************************)

Definition reflect_ADT_DSL_computation {A : Type}
           (c : Comp A) :=
  { f : ClientDSL (Rep adt) A
        & (forall a,
              c ↝ a
              <-> ADT_Computes f a) }.

(*Definition reflect_ADT_DSL_computation {A : Type}
           (c : Comp ((Rep adt * B) * A)) :=
  { f : B -> ClientDSL (Rep adt) (B * A)
             & (forall bs r' bs' v,
                   c bs ↝ ((r', bs'), v)
                   -> ADT_Computes (f bs) (bs', v) )
               /\ forall bs r' bs' v,
                 ADT_Computes (f bs) (bs', v)
                 -> c bs ↝ ((r', bs'), v) }. *)

Lemma reflect_ADT_DSL_computation_simplify {A : Type} c c'
      (refine_c_c' : refineEquiv c c')
      (c_DSL : reflect_ADT_DSL_computation c')
  : reflect_ADT_DSL_computation (A := A) c.
Proof.
  exists (projT1 c_DSL); intros.
  destruct (projT2 c_DSL a); simpl in *.
  split.
  - intros; eapply H; apply refine_c_c'; eauto.
  - intros; eapply refine_c_c'; eauto.
Defined.

Corollary If_Then_Else_computes_to : forall b A (t e : Comp A) (v : A),
  (If b Then t Else e) ↝ v -> If b Then (t ↝ v) Else (e ↝ v).
Proof. destruct b; trivial. Qed.

Lemma reflect_ADT_DSL_computation_If_Then_Else
      {A : Type} c (t e : Comp A)
      (c_DSL : reflect_ADT_DSL_computation t)
      (k_DSL : reflect_ADT_DSL_computation e)
  : reflect_ADT_DSL_computation (If c Then t Else e).
Proof.
  exists (If c Then projT1 c_DSL Else projT1 k_DSL).
  split; intros.
    apply If_Then_Else_computes_to in H.
    simpl in *.
    destruct c.
    destruct c_DSL; simpl in *.
    eapply i; eassumption.
    destruct k_DSL; simpl in *.
    eapply i; eassumption.
  destruct c.
  destruct c_DSL; simpl in *.
  eapply i; eassumption.
  destruct k_DSL; simpl in *.
  eapply i; eassumption.
Defined.

Corollary IfDep_Then_Else_computes_to :
  forall A c (t : c = true -> Comp A) (e : c = false -> Comp A) (v : A),
    (IfDep c Then t Else e) ↝ v
      -> IfDep c
         Then (fun H => t H ↝ v)
         Else (fun H => e H ↝ v).
Proof. destruct c; trivial. Qed.

Lemma reflect_ADT_DSL_computation_IfDep_Then_Else
      {A : Type} c  (t : c = true -> Comp A) (e : c = false -> Comp A)
      (c_DSL : forall H : c = true, reflect_ADT_DSL_computation (t H))
      (k_DSL : forall H : c = false, reflect_ADT_DSL_computation (e H))
  : reflect_ADT_DSL_computation (IfDep c Then t Else e).
Proof.
  exists (IfDep c
          Then (fun H => projT1 (c_DSL H))
          Else (fun H => projT1 (k_DSL H))).
  split; intros.
    apply IfDep_Then_Else_computes_to in H.
    simpl in *.
    destruct c; simpl in *.
    destruct (c_DSL eq_refl).
    simpl in *.
    eapply i; eassumption.
    destruct k_DSL.
    simpl in *.
    eapply i; eassumption.
  destruct c; simpl in *.
  destruct (c_DSL eq_refl).
  simpl in *.
  eapply i; eassumption.
  destruct (k_DSL eq_refl).
  simpl in *.
  eapply i; eassumption.
Defined.

End ClientDSL.

Arguments MethodCall {sig} _ _.
Arguments Call {sig rep rec} midx _ _.

Lemma denote_refineEquiv A sig adt (comp : Comp A)
  : forall (reflected : reflect_ADT_DSL_computation adt comp),
    refineEquiv
      comp
      (denote (sig := sig) adt (projT1 reflected)).
Proof.
  unfold reflect_ADT_DSL_computation; intros [? ?]; simpl.
  setoid_rewrite <- ADT_Computes_denotation in i.
  split.
  - intros ? Comp_v; eapply i; eauto.
  - intros ? Comp_v; eapply i; eauto.
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
    | [ H : _ ?A ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec Fin.F1);
      first
        [destruct R as [? ?];
         eapply CallSome with (args := HCons A HNil);
         [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
        | eapply CallNone with (args := HCons A HNil);
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS Fin.F1));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A HNil);
           [ | eapply H];
           instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A HNil);
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS Fin.F1)));
        first
          [destruct R as [? ?];
           eapply CallSome with (args := HCons A HNil);
           [ | eapply H];
           instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A HNil);
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS Fin.F1))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A HNil);
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A HNil);
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A HNil);
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A HNil);
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A HNil);
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A HNil);
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A HNil);
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A HNil);
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A HNil);
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A HNil);
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A HNil);
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A HNil);
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A HNil);
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A HNil);
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A HNil);
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A HNil);
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
 end.

Ltac solve_for2 :=
 match goal with
    | [ H : _ ?A ?B ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec Fin.F1);
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B HNil));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS Fin.F1));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B HNil));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS Fin.F1)));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B HNil));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS Fin.F1))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B HNil));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B HNil));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B HNil));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B HNil));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B HNil));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B HNil));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B HNil));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B HNil));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
 end.

Ltac solve_for3 :=
 match goal with
    | [ H : _ ?A ?B ?C ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec Fin.F1);
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C HNil)));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C HNil)));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS Fin.F1));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C HNil)));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C HNil)));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS Fin.F1)));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C HNil)));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C HNil)));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS Fin.F1))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C HNil)));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C HNil)));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C HNil)));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B HCons C HNil));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C HNil)));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C HNil)));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C HNil)));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C HNil)));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C HNil)));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C HNil)));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C HNil)));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C HNil)));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C HNil)));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C HNil)));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C HNil)));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C HNil)));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
 end.

Ltac solve_for4 :=
 match goal with
    | [ H : _ ?A ?B ?C ?D ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec Fin.F1);
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D HNil))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D HNil))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS Fin.F1));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D HNil))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D HNil))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS Fin.F1)));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D HNil))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D HNil))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS Fin.F1))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D HNil))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D HNil))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D HNil))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D HNil))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D HNil))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D HNil))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D HNil))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D HNil))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D HNil))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D HNil))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D HNil))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D HNil))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D HNil))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D HNil))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D HNil))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D HNil))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    end.

Ltac solve_for5 :=
 match goal with
    | [ H : _ ?A ?B ?C ?D ?E ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec Fin.F1);
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ?E ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS Fin.F1));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ?E ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS Fin.F1)));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ?E ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS Fin.F1))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ?E ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ?E ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ?E ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ?E ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ?E ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ?E ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ?E ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E HNil)))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    end.

Ltac solve_for6 :=
 match goal with
    | [ H : _ ?A ?B ?C ?D ?E ?F ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec Fin.F1);
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ?E ?F ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS Fin.F1));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ?E ?F ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS Fin.F1)));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ?E ?F ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS Fin.F1))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ?E ?F ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ?E ?F ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ?E ?F ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ?E ?F ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ?E ?F ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ?E ?F ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    | [ H : _ ?A ?B ?C ?D ?E ?F ↝ ?R |- MethodCall_Computes ?ADTSpec _ ?R ] =>
      eapply (CallComputes ADTSpec (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))))));
        first
          [destruct R as [? ?];
         eapply CallSome with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
           [ | eapply H];
         instantiate (1 := fun h p => (h, p)); higher_order_reflexivity
          | eapply CallNone with (args := HCons A (HCons B (HCons C (HCons D (HCons E (HCons F HNil))))));
            [ | eapply H]
          ]; instantiate (1 := id); higher_order_reflexivity
    end.

Ltac solve_for_call :=
  first [ solve_for1 | solve_for2 | solve_for3
        | solve_for4 | solve_for5 | solve_for6 ].

Ltac solve_for_call' :=
  match goal with
  | H : ADT_Computes _ _ _ |- _ =>
    simpl in H; inversion H; subst;
    repeat match goal with
           | H : existT _ _ _ = existT _ _ _ |- _ =>
             apply inj_pair2 in H; subst
           end;
    clear H
  | H : Free_Computes _ _ _ _ |- _ =>
    inversion H; subst;
    repeat match goal with
           | H : existT _ _ _ = existT _ _ _ |- _ =>
             apply inj_pair2 in H; subst
           end;
    clear H
  | H : MethodCall_Computes _ _ _ |- _ =>
    inversion H; simpl in *; subst;
    repeat match goal with
           | H : existT _ _ _ = existT _ _ _ |- _ =>
             apply inj_pair2 in H; subst
           end;
    clear H
  | H : methodType_Computes _ _ _ _ |- _ =>
    apply methodType_computes_inv in H; destruct_ex; intuition; subst;
    simpl in *; unfold id in *; simpl in *
  end;
  try computes_to_econstructor; injections; try eassumption.

Ltac build_computational_spine :=
  match goal with
  | H : {a' | @?P a'} ↝ _ |- _ => apply Pick_inv in H
  | H : Return ?a ↝ _ |- _ =>
    apply Return_inv in H; tsubst; try apply CPure
  | H : Bind (A := ?A) ?ca ?k ↝ _ |- _ =>
    apply Bind_inv in H;
    let v := fresh "v" in
    destruct H as [ v [H ?] ];
    simpl in *;
    eapply (@CJoin _ _ _ _ _ _ _ _ _ v)
  end.

Lemma refineEquiv_reflect_ADT_DSL_computation :
  forall sig (adt : ADT sig) A (x y : Comp A),
  refineEquiv x y
    -> reflect_ADT_DSL_computation adt x
    -> reflect_ADT_DSL_computation adt y.
Proof.
  intros.
  destruct X as [H1 H2].
  exists H1.
  split; intros.
    apply H in H0.
    apply H2; auto.
  apply H, H2; auto.
Qed.

Ltac simplify_reflection :=
  eapply reflect_ADT_DSL_computation_simplify;
  [ set_evars; intros;
    autorewrite with monad laws; simpl;
    try rewrite refineEquiv_If_Then_Else_Bind;
    finish honing
  | try first
      [ eapply reflect_ADT_DSL_computation_If_Then_Else
      | eapply reflect_ADT_DSL_computation_IfDep_Then_Else; intros ] ].

Ltac compile_term :=
  repeat (autounfold; simpl); (* Unfold definitions as necessary *)
  repeat simplify_reflection; (* Do some simplication and break down If expressions *)
  ( eexists; split; intros;   (* Decompose iff into the two equivalence conditions *)
    [ repeat build_computational_spine;
      try solve_for_call
    | repeat solve_for_call' ] ).
