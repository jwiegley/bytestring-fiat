Require Import
  ByteString.Lib.Tactics
  ByteString.Lib.Nomega
  ByteString.Lib.Fiat
  ByteString.Lib.TupleEnsembles
  ByteString.Lib.FunMaps
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

Section Refined.

Inductive HeapF (r : Type) : Type :=
  | Alloc   : forall (len : Size | 0 < len) (k : N -> r), HeapF r
  | Free_   : forall (addr : Ptr Word), r -> HeapF r
  | Realloc : forall (addr : Ptr Word) (len : Size | 0 < len) (k : N -> r), HeapF r
  | Peek    : forall (addr : Ptr Word) (k : Word -> r), HeapF r
  | Poke    : forall (addr : Ptr Word) (w : Word), r -> HeapF r
  | Memcpy  : forall (addr : Ptr Word) (addr2 : Ptr Word) (len : Size), r -> HeapF r
  | Memset  : forall (addr : Ptr Word) (len : Ptr Word) (w : Word), r -> HeapF r.

Program Instance HeapF_Functor : Functor HeapF := {
  fmap := fun _ _ f x =>
    match x with
    | Alloc len k             => Alloc len (compose f k)
    | Free_ addr x            => Free_ addr (f x)
    | Realloc addr len k      => Realloc addr len (compose f k)
    | Peek addr k             => Peek addr (compose f k)
    | Poke addr w x           => Poke addr w (f x)
    | Memcpy addr addr2 len x => Memcpy addr addr2 len (f x)
    | Memset addr len w x     => Memset addr len w (f x)
    end
}.

Definition HeapDSL := Free HeapF.

Inductive HeapF_Computes :
  forall {A}, HeapF A -> Rep HeapSpec -> Rep HeapSpec -> A -> Prop :=
  | HAlloc len addr (r r' : Rep HeapSpec) A (k : Ptr Word -> A) x :
      alloc r len ↝ (r', addr) ->
      x = k addr ->
      HeapF_Computes (Alloc len k) r r' x

  | HFree addr (r r' : Rep HeapSpec) A (x : A) :
      free r addr ↝ (r', tt) ->
      HeapF_Computes (Free_ addr x) r r' x

  | HRealloc addr len addr' (r r' : Rep HeapSpec) A (k : Ptr Word -> A) :
      realloc r addr len ↝ (r', addr') ->
      HeapF_Computes (Realloc addr len k) r r' (k addr')

  | HPeek addr w (r r' : Rep HeapSpec) A (k : Word -> A) :
      peek r addr ↝ (r', w) ->
      HeapF_Computes (Peek addr k) r r' (k w)

  | HPoke addr w (r r' : Rep HeapSpec) A (x : A) :
      poke r addr w ↝ (r', tt) ->
      HeapF_Computes (Poke addr w x) r r' x

  | HMemcpy addr addr2 len r r' A (x : A) :
      memcpy r addr addr2 len ↝ (r', tt) ->
      HeapF_Computes (Memcpy addr addr2 len x) r r' x

  | HMemset addr len w r r' A (x : A) :
      memset r addr len w ↝ (r', tt) ->
      HeapF_Computes (Memset addr len w x) r r' x.

Inductive Free_Computes `{Functor f} {R : Type}
          (crel : forall {A}, f A -> R -> R -> A -> Prop) :
  forall {A}, Free f A -> R -> R -> A -> Prop :=
  | CPure r A (v : A) : Free_Computes crel (Pure v) r r v
  | CJoin r r'' B (v' : B) :
      forall A t k r' v,
        Free_Computes crel (k v) r' r'' v'
        -> crel A t r r' v
        -> Free_Computes crel (Join k t) r r'' v'.

Definition HeapDSL_Computes `(h : HeapDSL A) :=
  Free_Computes (@HeapF_Computes) h.

Definition ByteString (r : Rep HeapSpec) := Rep (projT1 (ByteStringHeap r)).

Definition reflect_Heap_DSL_computation {A : Type}
           (c : Rep HeapSpec * PS -> Comp ((Rep HeapSpec * PS) * A)) :=
  { f : PS -> HeapDSL (PS * A)
  & forall r bs r' bs' v, c (r, bs) ↝ ((r', bs'), v)
      -> HeapDSL_Computes (f bs) r r' (bs', v) }.

Lemma reflect_computation_ret {A : Type} (v : A) :
  reflect_Heap_DSL_computation (fun r => ret (r, v)).
Proof.
  exists (fun r => pure (r, v)); intros.
  computes_to_inv; injections.
  eapply CPure.
Defined.

Lemma reflect_Heap_DSL_computation_simplify {B : Type} c c'
      (refine_c_c' : forall r, refineEquiv (c r) (c' r))
      (c_DSL : reflect_Heap_DSL_computation c')
  : reflect_Heap_DSL_computation (A := B) c.
Proof.
  exists (projT1 c_DSL); intros.
  pose proof (projT2 c_DSL); simpl in *.
  apply H0; apply refine_c_c'; auto.
Defined.

Lemma reflect_Heap_DSL_computation_If_Then_Else
      {B : Type} c c' (t e : _ -> Comp (_ * B))
      (c_DSL : reflect_Heap_DSL_computation t)
      (k_DSL : reflect_Heap_DSL_computation e)
  : (forall r, c r = c' (snd r)) ->
    reflect_Heap_DSL_computation (fun r => If c r Then t r Else e r).
Proof.
  intros.
  exists (fun bs : PS =>
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
    apply h; assumption.
  destruct k_DSL.
  simpl in *.
  apply h; assumption.
Defined.

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
  eapply reflect_Heap_DSL_computation_simplify;
  [ set_evars; intros;
    autorewrite with monad laws; simpl;
    try rewrite refineEquiv_If_Then_Else_Bind;
    finish honing
  | try (eapply reflect_Heap_DSL_computation_If_Then_Else;
         [| | let r := fresh "r" in
              intro r; destruct r; simpl; reflexivity]) ].

Ltac prepare_reflection :=
  repeat match goal with
  | [ |- reflect_Heap_DSL_computation _ ] =>
    eexists; intros; try computes_to_inv; tsubst
  | [ H : _ * _ |- _ ] => destruct H
  | [ H : () |- _ ] => destruct H
  end; simpl in *.

Ltac DSL_term :=
  repeat match goal with
    [ H : _ ↝ (?R, _) |- HeapF_Computes _ _ ?R _ ] =>
    solve [ econstructor; eassumption
          | econstructor; [eassumption|higher_order_reflexivity] ]
  end.

Definition consDSL w :
  reflect_Heap_DSL_computation
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
    prepare_reflection.
    eapply CJoin.
      apply CPure.
    DSL_term.

  simplify_reflection.
    simplify_reflection.
    prepare_reflection.
    eapply CJoin.
      eapply CJoin.
        eapply CPure.
      DSL_term.
    DSL_term.

  simplify_reflection.
    simplify_reflection.
    prepare_reflection.
    eapply CJoin.
      eapply CJoin.
        eapply CJoin.
          eapply CJoin.
            eapply CPure.
          DSL_term.
        DSL_term.
      DSL_term.
    DSL_term.

  simplify_reflection.
  prepare_reflection.
  eapply CJoin.
    eapply CJoin.
      apply CPure.
    DSL_term.
  DSL_term.
Defined.

Definition denote {A : Type} :
  HeapDSL A -> Rep HeapSpec -> Comp (Rep HeapSpec * A) :=
  let phi (c : HeapF (Rep HeapSpec -> Comp (Rep HeapSpec * A))) := fun r =>
    match c with
    | Alloc len k             => `(r', addr) <- alloc r len; k addr r'
    | Free_ addr x            => `(r', _)    <- free r addr; x r'
    | Realloc addr len k      => `(r', addr) <- realloc r addr len; k addr r'
    | Peek addr k             => `(r', w)    <- peek r addr; k w r'
    | Poke addr w x           => `(r', _)    <- poke r addr w; x r'
    | Memcpy addr addr2 len x => `(r', _)    <- memcpy r addr addr2 len; x r'
    | Memset addr len w x     => `(r', _)    <- memset r addr len w; x r'
    end in
  iter phi \o fmap (fun x r => ret (r, x)).

Corollary denote_Pure : forall A (x : A) r,
  refineEquiv (denote (Pure x) r) (ret (r, x)).
Proof. reflexivity. Qed.

Lemma denote_Join : forall A B (k : A -> HeapDSL B) (h : HeapF A) r,
  refineEquiv (denote (Join k h) r)
              (denote (liftF h) r >>= fun p => denote (k (snd p)) (fst p)).
Proof.
  intros.
  unfold denote, iter; simpl.
  induction h;
  autorewrite with monad laws; reflexivity.
Qed.

Lemma denote_Free_bind : forall A (x : HeapDSL A) B (k : A -> HeapDSL B) r,
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

Corollary denote_If : forall b A (t e : HeapDSL A) r,
  refineEquiv (denote (If b Then t Else e) r)
              (If b Then denote t r Else denote e r).
Proof. destruct b; simpl; reflexivity. Qed.

Lemma HeapDSL_Computes_denotation : forall A f r r' (v : A),
  denote f r ↝ (r', v) -> HeapDSL_Computes f r r' v.
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
  [ apply H; eauto | eapply HAlloc
  | apply H; eauto | apply HFree
  | apply H; eauto | apply HRealloc
  | apply H; eauto | apply HPeek
  | apply H; eauto | apply HPoke
  | apply H; eauto | apply HMemcpy
  | apply H; eauto | apply HMemset ];
  try destruct u; eauto.
Qed.

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

Axiom IO : Type -> Type.

Axiom fmapIO   : forall {a b : Type}, (a -> b) -> IO a -> IO b.
Axiom bindIO   : forall {a b : Type}, IO a -> (a -> IO b) -> IO b.
Axiom returnIO : forall {a : Type}, a -> IO a.
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

Definition ghcDenote {A : Type} : HeapDSL A -> A :=
  let phi (c : HeapF (IO A)) :=
    match c with
    | Alloc len k             => bindIO (malloc (` len)) k
    | Free_ addr x            => bindIO (free addr) (fun _ => x)
    | Realloc addr len k      => bindIO (realloc addr (` len)) k
    | Peek addr k             => bindIO (peek addr) k
    | Poke addr w x           => bindIO (poke addr w) (fun _ => x)
    | Memcpy addr addr2 len x => bindIO (memcpy addr addr2 len) (fun _ => x)
    | Memset addr len w x     => bindIO (memset addr len w) (fun _ => x)
    end in
  unsafeDupablePerformIO \o iter phi \o fmap returnIO.

Corollary bind_If `{Monad f} : forall A B (k : A -> f B) b t e,
  ((If b Then t Else e) >>= k) = If b Then t >>= k Else e >>= k.
Proof. destruct b; reflexivity. Qed.

Corollary fmap_If `{Functor f} : forall A B (k : A -> B) b t e,
  fmap k (If b Then t Else e) = If b Then fmap k t Else fmap k e.
Proof. destruct b; reflexivity. Qed.

Corollary iter_If `{Functor f} : forall A (phi : f A -> A) b t e,
  iter phi (If b Then t Else e) = If b Then iter phi t Else iter phi e.
Proof. destruct b; reflexivity. Qed.

(*
Lemma ghcConsDSL :
  { f : PS -> Word -> PS
  & forall bs w, f bs w = fst (ghcDenote (projT1 (consDSL w) bs)) }.
Proof.
  eexists.
  intros.
  unfold consDSL, ghcDenote, compose, comp.
  symmetry.
  rewrite !bind_If.
  do 3 rewrite fmap_If.
  etransitivity.
    do 3 setoid_rewrite iter_If.
    simpl.
    unfold If_Then_Else, compose, comp; simpl.
    reflexivity.
  rewrite !bindIO_returnIO.
  reflexivity.
Defined.

Definition ghcConsDSL' := Eval simpl in projT1 ghcConsDSL.
Print ghcConsDSL'.
*)

End Refined.

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
