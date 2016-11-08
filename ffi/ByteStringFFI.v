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

Module ByteStringFFI (M : WSfun N_as_DT).

Module Import ByteStringHeap := ByteStringHeap M.
Module Import FunMaps := FunMaps N_as_DT M.

Import HeapCanonical.
Import Heap.
Import HeapState.
Import FMapExt.

Inductive callArgs (r : Type) : list Type -> option Type -> Type :=
  | RetVal  : r -> callArgs r [] None
  | ContVal : forall cod, (cod -> r) -> callArgs r [] (Some cod)
  | ArgVal  : forall t ts cod, t -> callArgs r ts cod
                -> callArgs r (t :: ts) cod.

Program Instance callArgs_Functor (dom : list Type) (cod : option Type) :
  Functor (fun r => callArgs r dom cod) := {
  fmap := fun A B f x =>
            let fix go dom cod (z : callArgs A dom cod) :=
                match z with
                | RetVal x          => RetVal (f x)
                | ContVal _ k       => ContVal (f \o k)
                | ArgVal _ _ _ x xs => ArgVal x (go _ _ xs)
                end in
            go _ _ x
}.

Inductive methodCall (sig : ADTSig) (adt : ADT sig) (rec : Type) : Type :=
  | Call : forall (midx : MethodIndex sig)
                  (args : callArgs rec (fst (MethodDomCod sig midx))
                                       (snd (MethodDomCod sig midx))),
      methodCall adt rec.

Program Instance methodCall_Functor (sig : ADTSig) (adt : ADT sig) :
  Functor (methodCall adt) := {
  fmap := fun A B f x =>
            match x with
            | Call midx args => Call adt midx (fmap f args)
            end
}.

Definition CallDSL (sig : ADTSig) (adt : ADT sig) : Type -> Type :=
  Free (methodCall adt).

Inductive call_represented (sig : ADTSig) (adt : ADT sig) :
          forall (dom : list Type) (cod : option Type) A,
            callArgs A dom cod -> methodType' (Rep adt) dom cod -> A -> Prop :=
  | CheckRet : forall A (v : A) (meth : methodType' (Rep adt) [] None),
      call_represented adt (RetVal v) meth v
  | CheckCont : forall cod A (k : cod -> A) (x : cod)
                       (meth : methodType' (Rep adt) [] (Some cod)) v,
      v = k x -> call_represented adt (ContVal k) meth v
  | CheckArg : forall t ts (x : t) (cod : option Type) A
                      (args : callArgs A ts cod)
                      (meth : methodType' (Rep adt) (t :: ts) cod) v,
      call_represented adt args (meth x) v ->
      call_represented adt (ArgVal x args) meth v.

Inductive methodCall_Computes (sig : ADTSig) (adt : ADT sig) :
  forall A, methodCall adt A -> Rep adt -> Rep adt -> A -> Prop :=
  | CallComputes (midx : MethodIndex sig) A
                 (args : callArgs A (fst (MethodDomCod sig midx))
                                    (snd (MethodDomCod sig midx)))
                 (r r' : Rep adt) v :
      fromMethod (Methods adt midx) r r'
        -> call_represented adt args (Methods adt midx r) v
        -> methodCall_Computes (Call adt midx args) r r' v.

Inductive Free_Computes `{Functor f} {R : Type}
          (crel : forall {A}, f A -> R -> R -> A -> Prop) :
  forall {A}, Free f A -> R -> R -> A -> Prop :=
  | CPure r A (v : A) : Free_Computes crel (Pure v) r r v
  | CJoin r r'' B (v' : B) :
      forall A t k r' v,
        Free_Computes crel (k v) r' r'' v'
        -> crel A t r r' v
        -> Free_Computes crel (Join k t) r r'' v'.

Definition ADT_Computes (sig : ADTSig) (adt : ADT sig)
           `(r : CallDSL adt A) :=
  Free_Computes (@methodCall_Computes sig adt) r.

Definition ByteString (r : Rep HeapSpec) := Rep (projT1 (ByteStringHeap r)).

Section Reflection.

Variable sig : ADTSig.
Variable adt : ADT sig.

Definition reflect_ADT_DSL_computation {A B : Type}
           (c : Rep adt * B -> Comp ((Rep adt * B) * A)) :=
  { f : B -> CallDSL adt (B * A)
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
    [ H : _ ↝ (?R, _) |- methodCall_Computes _ _ ?R _ ] =>
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

      apply CallComputes (* poke *)
        with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))).
        repeat eexists; eassumption.
      apply CheckArg with (x := psBuffer bs + (psOffset bs - 1)).
      apply CheckArg with (x := w).
      eapply CheckCont; higher_order_reflexivity.
    }

  simplify_reflection.
    simplify_reflection.
    { build_computational_spine.

      eapply CJoin.
      eapply CJoin.
      eapply CPure.

      apply CallComputes (* poke *)
        with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))).
        repeat eexists; eassumption.
      apply CheckArg with (x := psBuffer bs + 0).
      apply CheckArg with (x := w).
      eapply CheckCont; higher_order_reflexivity.

      apply CallComputes (* memcpy *)
        with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))).
        repeat eexists; eassumption.
      apply CheckArg with (x := psBuffer bs).
      apply CheckArg with (x := psBuffer bs + 1).
      apply CheckArg with (x := psLength bs).
      eapply CheckCont; higher_order_reflexivity.
    }

  simplify_reflection.
    simplify_reflection.
    { build_computational_spine.

      eapply CJoin.
      eapply CJoin.
      eapply CJoin.
      eapply CJoin.
      eapply CPure.

      apply CallComputes (* poke *)
        with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))).
        repeat eexists; eassumption.
      apply CheckArg with (x := p + 0).
      apply CheckArg with (x := w).
      eapply CheckCont; higher_order_reflexivity.

      apply CallComputes (* free *)
        with (midx := Fin.FS Fin.F1).
        repeat eexists; eassumption.
      apply CheckArg with (x := psBuffer bs).
      eapply CheckCont; higher_order_reflexivity.

      apply CallComputes (* memcpy *)
        with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))).
        repeat eexists; eassumption.
      apply CheckArg with (x := psBuffer bs).
      apply CheckArg with (x := p + 1).
      apply CheckArg with (x := psLength bs).
      eapply CheckCont; higher_order_reflexivity.

      simpl in *.
      apply CallComputes (* alloc *)
        with (midx := Fin.F1).
        do 2 eexists; eassumption.
      apply CheckArg with (x := exist _ (psLength bs + 1) (lt_0_n _)).
      apply CheckCont with (x := p); higher_order_reflexivity.
    }

  simplify_reflection.
    { build_computational_spine.

      eapply CJoin.
      eapply CJoin.
      eapply CPure.

      apply CallComputes (* poke *)
        with (midx := Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))).
        repeat eexists; eassumption.
      apply CheckArg with (x := p + 0).
      apply CheckArg with (x := w).
      eapply CheckCont; higher_order_reflexivity.

      simpl in *.
      apply CallComputes (* alloc *)
        with (midx := Fin.F1).
        do 2 eexists; eassumption.
      apply CheckArg with (x := exist _ _ N.lt_0_1).
      apply CheckCont with (x := p); higher_order_reflexivity.
    }

  Local Transparent poke.
  Local Transparent alloc.
  Local Transparent free.
  Local Transparent peek.
  Local Transparent memcpy.

  Unshelve.
  all: exact tt.
Defined.

Definition consDSL' w := Eval simpl in projT1 (consDSL w).
Print consDSL'.

Definition applyArgs
           (dom : list Type) (cod : option Type)
           {rep : Type} (meth : methodType rep dom cod)
           {A : Type} (args : callArgs A dom cod) :
  rep -> Comp (rep * A).
Proof.
  intro r.
  induction dom.
    destruct cod; inv args.
      exact (`(r', t) <- meth r; ret (r', X t)).
    exact (r' <- meth r; ret (r', X))%comp.
  inv args.
  exact (IHdom (fun r => meth r X) X0).
Defined.

Definition denote (sig : ADTSig) (adt : ADT sig) {A : Type} :
  CallDSL adt A -> Rep adt -> Comp (Rep adt * A) :=
  let phi (c : methodCall adt (Rep adt -> Comp (Rep adt * A))) :=
    match c return Rep adt -> Comp (Rep adt * A) with
    | Call midx args => fun r =>
        `(r', k) <- applyArgs (rep:=Rep adt) (Methods adt midx) args r; k r'
    end in
  iter phi \o fmap (fun x r => ret (r, x)).

Corollary denote_Pure (sig : ADTSig) (adt : ADT sig) : forall A (x : A) r,
  refineEquiv (denote (adt:=adt) (Pure x) r) (ret (r, x)).
Proof. reflexivity. Qed.

Lemma denote_Join (sig : ADTSig) (adt : ADT sig) :
  forall A B (k : A -> CallDSL adt B) (h : methodCall adt A) r,
  refineEquiv (denote (Join k h) r)
              (denote (liftF h) r >>= fun p => denote (k (snd p)) (fst p)).
Proof.
  intros.
  destruct h.
Admitted.

Lemma denote_Free_bind (sig : ADTSig) (adt : ADT sig) :
  forall A (x : CallDSL adt A) B (k : A -> CallDSL adt B) r,
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

Corollary denote_If (sig : ADTSig) (adt : ADT sig) :
  forall b A (t e : CallDSL adt A) r,
    refineEquiv (denote (If b Then t Else e) r)
                (If b Then denote t r Else denote e r).
Proof. destruct b; simpl; reflexivity. Qed.

Lemma ADT_Computes_denotation (sig : ADTSig) (adt : ADT sig) :
  forall A f r r' (v : A),
    denote f r ↝ (r', v) -> ADT_Computes (adt:=adt) f r r' v.
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
  destruct v0;
  eapply CJoin;
  simpl in H0';
  [ apply H; eauto | eapply CallComputes ];
  try destruct u; eauto.
Admitted.

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

Definition ghcDenote {A : Type} : CallDSL HeapSpec A -> A.
Proof.
  intros.
  apply (fmap returnIO) in X.
  eapply (iter _) in X.
  apply unsafeDupablePerformIO in X.
  exact X.
  Unshelve.
  clear X.
  destruct 1.
  simpl in *.
  dependent destruction midx; simpl in *.
    inv args. inv X0.
    exact (bindIO (malloc (` X)) X1).
  dependent destruction midx; simpl in *.
    inv args. inv X0.
    exact (bindIO (free X) X1).
  dependent destruction midx; simpl in *.
    inv args. inv X0. inv X2.
    exact (bindIO (realloc X (` X1)) X0).
  dependent destruction midx; simpl in *.
    inv args. inv X0.
    exact (bindIO (peek X) X1).
  dependent destruction midx; simpl in *.
    inv args. inv X0. inv X2.
    exact (bindIO (poke X X1) X0).
  dependent destruction midx; simpl in *.
    inv args. inv X0. inv X2. inv X3.
    exact (bindIO (memcpy X X1 X0) X2).
  dependent destruction midx; simpl in *.
    inv args. inv X0. inv X2. inv X3.
    exact (bindIO (memset X X1 X0) X2).
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
  remember (eq_sym _) as E.
  dependent destruction E.
  simpl.
  rewrite <- HeqE.
  etransitivity.
    simpl.
    reflexivity.
  rewrite !bindIO_returnIO.
  reflexivity.
Defined.

Definition ghcConsDSL' := Eval simpl in projT1 ghcConsDSL.
Print ghcConsDSL'.

Theorem consDSL_correct : forall (r : Rep HeapSpec) (bs : PS) w,
  refine (buffer_cons r bs w)
         (res <- denote (projT1 (consDSL w) bs) r;
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
