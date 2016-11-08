Require Import
  ByteString.Lib.Tactics
  ByteString.Lib.Nomega
  ByteString.Lib.Fiat
  ByteString.Lib.TupleEnsembles
  ByteString.Lib.FunMaps
  ByteString.Lib.FromADT
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

Inductive hlist : list Type -> Type :=
  | HNil : hlist []
  | HCons : forall t ts, t -> hlist ts -> hlist (t :: ts).

Import EqNotations.

Lemma cons_head_eq : forall A (x0 : A) x1 y0 y1,
  x0 :: y0 = x1 :: y1 -> x0 = x1.
Proof.
  intros.
  inv H.
  intuition.
Defined.

Lemma cons_tail_eq : forall A (x0 : A) x1 y0 y1,
  x0 :: y0 = x1 :: y1 -> y0 = y1.
Proof.
  intros.
  inv H.
  intuition.
Defined.

Program Definition hlist_head `(l : hlist (t :: ts)) : t :=
  match l in hlist d return d = t :: ts -> t with
  | HNil => fun _ => False_rect _ _
  | HCons _ _ x _ => fun H => rew (cons_head_eq H) in x
  end eq_refl.

Program Definition hlist_tail `(l : hlist (t :: ts)) : hlist ts :=
  match l in hlist d return d = t :: ts -> hlist ts with
  | HNil => fun _ => False_rect _ _
  | HCons _ _ _ xs => fun H => rew (cons_tail_eq H) in xs
  end eq_refl.

Section Reflection.

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

Definition CallDSL := Free MethodCall.

Variable adt : ADT sig.

Import EqNotations.

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

Definition reflect_ADT_DSL_computation {A B : Type}
           (c : Rep adt * B -> Comp ((Rep adt * B) * A)) :=
  { f : B -> CallDSL (B * A)
  & forall r bs r' bs' v, c (r, bs) ↝ ((r', bs'), v)
      -> ADT_Computes (f bs) r r' (bs', v) }.

Lemma reflect_computation_ret {A B : Type} (v : A) :
  reflect_ADT_DSL_computation (B:=B) (fun r => ret (r, v)).
Proof.
  exists (fun r => pure (r, v)); intros.
  computes_to_inv; injections.
  eapply CPure.
Defined.

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

End Reflection.

Module ByteStringFFI (M : WSfun N_as_DT).

Module Import ByteStringHeap := ByteStringHeap M.
Module Import FunMaps := FunMaps N_as_DT M.

Import HeapCanonical.
Import Heap.
Import HeapState.
Import FMapExt.

Definition ByteString (r : Rep HeapSpec) := Rep (projT1 (ByteStringHeap r)).

Hint Unfold id.
Hint Unfold bind.
Hint Unfold Bind2.
Hint Unfold allocate_buffer.
Hint Unfold find_free_block.
Hint Unfold make_room_by_growing_buffer.
Hint Unfold make_room_by_shifting_up.
Hint Unfold ByteStringHeap.buffer_cons_obligation_2.
Hint Unfold ByteStringHeap.buffer_cons_obligation_3.
Hint Unfold poke_at_offset.
Hint Unfold buffer_cons.

Ltac simplify_reflection :=
  eapply reflect_ADT_DSL_computation_simplify;
  [ set_evars; intros;
    autorewrite with monad laws; simpl;
    try rewrite refineEquiv_If_Then_Else_Bind;
    finish honing
  | try (eapply reflect_ADT_DSL_computation_If_Then_Else;
         [| | let r := fresh "r" in
              intro r; destruct r; simpl; reflexivity]) ].

Ltac DSL_term :=
  repeat match goal with
    [ H : _ ↝ (?R, _) |- MethodCall_Computes _ _ ?R _ ] =>
    solve [ econstructor; eassumption
          | econstructor; [eassumption|higher_order_reflexivity] ]
  end.

Ltac build_computational_spine :=
  repeat match goal with
  | [ |- reflect_ADT_DSL_computation _ _ ] => eexists; intros
  (* | H : {a' | @?P a'} ↝ _ |- _ => apply Pick_inv in H *)
  (* | H : Return ?a ↝ _ |- _ => *)
  (*   apply Return_inv in H; tsubst; try apply CPure *)
  (* | H : Bind (A := ?A) ?ca ?k ↝ _ |- _ => *)
  (*   apply Bind_inv in H; *)
  (*   let a' := fresh "v" in *)
  (*   let H' := fresh H "'" in *)
  (*   destruct H as [a' [H H'] ]; *)
  (*   eapply CJoin *)
  end;
  computes_to_inv; tsubst; simpl in *;
  repeat match goal with
  | [ H : _ * _ |- _ ] => destruct H
  | [ H : () |- _ ] => destruct H
  end.

Lemma lt_0_n : forall n, 0 < n + 1.
Proof. nomega. Qed.

Ltac wrapup :=
  first
  [ eassumption
  | higher_order_reflexivity
  | instantiate (1 := eq_sym eq_refl);
    instantiate (1 := eq_sym eq_refl);
    reflexivity ].

Definition consDSL w :
  reflect_ADT_DSL_computation HeapSpec
    (fun r => r' <- buffer_cons (fst r) (snd r) w; ret (r', ()))%comp.
Proof.
  Local Opaque poke.
  Local Opaque alloc.
  Local Opaque free.
  Local Opaque peek.
  Local Opaque memcpy.

  repeat (autounfold; simpl).

  simplify_reflection.
    simplify_reflection.
    { build_computational_spine.

      eapply CJoin.
      eapply CPure.

      eapply CallComputes
        with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
             (args := HCons (psBuffer bs + (psOffset bs - 1))
                            (HCons w HNil)); wrapup.
    }

  simplify_reflection.
    simplify_reflection.
    { build_computational_spine.

      eapply CJoin.
      eapply CJoin.
      eapply CPure.

      eapply CallComputes
        with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
             (args := HCons (psBuffer bs + 0) (HCons w HNil)); wrapup.
      eapply CallComputes
        with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))
             (args := HCons (psBuffer bs) (HCons (psBuffer bs + 1) (HCons (psLength bs) HNil)));
        wrapup.
    }

  simplify_reflection.
    simplify_reflection.
    { build_computational_spine.

      eapply CJoin.
      eapply CJoin.
      eapply CJoin.
      eapply CJoin.
      eapply CPure.

      eapply CallCompute2 with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))));
        wrapup.
      eapply CallCompute1 with (midx := Fin.FS Fin.F1);
        wrapup.
      eapply CallCompute3 with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))));
        wrapup.
      simpl in *.
      eapply CallCompute1 with (midx := Fin.F1);
        wrapup.
    }

  simplify_reflection.
    { build_computational_spine.

      eapply CJoin.
      eapply CJoin.
      eapply CPure.

      eapply CallCompute2 with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))));
        wrapup.
      simpl in *.
      eapply CallCompute1 with (midx := Fin.F1);
        wrapup.
    }

  Local Transparent poke.
  Local Transparent alloc.
  Local Transparent free.
  Local Transparent peek.
  Local Transparent memcpy.
Defined.

Definition consDSL' w := Eval simpl in projT1 (consDSL w).
(* Print consDSL'. *)

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
  ap := fun _ _ mf mx r =>
            `(r', f) <- mf r;
            `(r', x) <- mx r';
            ret (r', f x)
}.

Program Instance ADT_Method_Monad :
  Monad (fun A : Type => Rep adt -> Comp (Rep adt * A)) := {
  join := fun _ mm r => `(r', m) <- mm r; m r'
}.

Import EqNotations.

Definition denote {A : Type} : CallDSL sig A -> Rep adt -> Comp (Rep adt * A) :=
  foldFree (fun T (c : MethodCall sig T) =>
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
  forall A B (k : A -> CallDSL sig B) (h : MethodCall sig A) r,
  refineEquiv (denote (Join k h) r)
              (denote (liftF h) r >>= fun p => denote (k (snd p)) (fst p)).
Proof.
  intros.
  destruct h.
  autorewrite with monad laws.
  reflexivity.
Qed.

Lemma denote_Free_bind :
  forall A (x : CallDSL sig A) B (k : A -> CallDSL sig B) r,
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
  forall b A (t e : CallDSL sig A) r,
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

Definition getADTSig {sig : DecoratedADTSig} : ADT sig -> DecoratedADTSig :=
  fun _ => sig.

Definition ghcDenote {A : Type} : CallDSL (getADTSig HeapSpec) A -> A.
Proof.
  intros.
  apply (fmap returnIO) in X.
  eapply (iter _) in X.
  apply unsafeDupablePerformIO in X.
  exact X.
  Unshelve.
  clear X.
  destruct 1.
  subst.
  simpl in midx.
  dependent destruction midx; simpl in *.
    inv e0. inv h. inv X0.
    exact (bindIO (malloc (` X)) i).
  dependent destruction midx; simpl in *.
    inv e0. inv h. inv X0.
    exact (bindIO (free X) i).
  dependent destruction midx; simpl in *.
    inv e0. inv h. inv X0. inv X2.
    exact (bindIO (realloc X (` X1)) i).
  dependent destruction midx; simpl in *.
    inv e0. inv h. inv X0.
    exact (bindIO (peek X) i).
  dependent destruction midx; simpl in *.
    inv e0. inv h. inv X0. inv X2.
    exact (bindIO (poke X X1) i).
  dependent destruction midx; simpl in *.
    inv e0. inv h. inv X0. inv X2. inv X3.
    exact (bindIO (memcpy X X1 X0) i).
  dependent destruction midx; simpl in *.
    inv e0. inv h. inv X0. inv X2. inv X3.
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

Lemma ghcConsDSL :
  { f : PS -> Word -> PS
  & forall bs w, f bs w = ghcDenote (fst <$> projT1 (consDSL w) bs) }.
Proof.
  eexists.
  intros.
  unfold consDSL, ghcDenote, compose, comp.
  symmetry.
  simpl projT1.
  do 6 rewrite fmap_If.
  simpl.
  do 3 setoid_rewrite iter_If.
  simpl.
  unfold If_Then_Else, compose, comp; simpl.
  unfold solution_left, eq_rect_r, eq_rect.
  simpl.
  unfold simplification_heq.
  unfold solution_right, eq_rect_r, eq_rect.
  simpl.
  unfold block.
  simpl.
  unfold eq_sym.
Admitted.

Definition ghcConsDSL' := Eval simpl in projT1 ghcConsDSL.
(* Print ghcConsDSL'. *)

Theorem consDSL_correct : forall (r : Rep HeapSpec) (bs : PS) w,
  refine (buffer_cons r bs w)
         (res <- denote HeapSpec (projT1 (consDSL w) bs) r;
          ret (fst res, fst (snd res))).
Proof.
  intros.
  destruct r.
  unfold buffer_cons, consDSL; simpl.
  repeat rewrite denote_Free_bind; simpl.
  rewrite denote_If; simpl.
  unfold Bind2.
  do 4 rewrite refineEquiv_If_Then_Else_Bind.
  apply refine_If_Then_Else.
    autorewrite with monad laws; reflexivity.
  rewrite denote_If; simpl.
  rewrite refineEquiv_If_Then_Else_Bind.
  apply refine_If_Then_Else.
    autorewrite with monad laws; reflexivity.
  rewrite denote_If; simpl.
  rewrite refineEquiv_If_Then_Else_Bind.
  apply refine_If_Then_Else.
    autorewrite with monad laws; reflexivity.
  autorewrite with monad laws; reflexivity.
Qed.

End ByteStringFFI.

(** This is the code we intend to approximate with the FFI refined version of
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
*)
