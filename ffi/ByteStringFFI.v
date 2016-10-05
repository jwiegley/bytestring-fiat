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
  Hask.Control.Monad.Free.

Module ByteStringFFI (M : WSfun N_as_DT).

Module Import ByteStringHeap := ByteStringHeap M.
Module Import HeapFFI := HeapFFI M.

Import HeapCanonical.
Import FunMaps.
Import Heap.
Import HeapState.
Import FMapExt.

Section Refined.

Inductive HeapF (r : Type) : Type :=
  | Empty   : HeapF r
  | Alloc   : forall (len : Size | 0 < len) (k : N -> r), HeapF r
  | Free_   : forall (addr : Ptr), r -> HeapF r
  | Realloc : forall (addr : Ptr) (len : Size | 0 < len) (k : N -> r), HeapF r
  | Peek    : forall (addr : Ptr) (k : Word -> r), HeapF r
  | Poke    : forall (addr : Ptr) (w : Word), r -> HeapF r
  | Memcpy  : forall (addr : Ptr) (addr2 : Ptr) (len : Size), r -> HeapF r
  | Memset  : forall (addr : Ptr) (len : Ptr) (w : Word), r -> HeapF r.

Program Instance HeapF_Functor : Functor HeapF := {
  fmap := fun _ _ f x =>
    match x with
    | Empty                   => Empty _
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

Inductive MonadRefinement `{Monad m} : forall (A B : Type) (AbsR : A -> B -> Prop),
  Comp A -> m B -> Prop :=
  | MBind A B (AbsR : A -> B -> Prop) :
      forall c c', MonadRefinement AbsR c c'
        -> forall k k',
             (forall v v', AbsR v v' -> MonadRefinement AbsR (k v) (k' v'))
        -> MonadRefinement AbsR (c >>= k)%comp (c' >>= k')%monad
  | MReturn A B (AbsR : A -> B -> Prop) x x' :
      AbsR x x'
        -> MonadRefinement AbsR (ret x)%comp (pure x')
  | MRefine A B (AbsR : A -> B -> Prop) c c' d :
      refine c' c
        -> MonadRefinement AbsR c d
        -> MonadRefinement AbsR c' d
  | MIf A B (AbsR : A -> B -> Prop) b t t' e e' :
      (b = true -> MonadRefinement AbsR t t')
        -> (b = false -> MonadRefinement AbsR e e')
        -> MonadRefinement AbsR (If b Then t Else e)%comp (if b then t' else e').

Definition matchPS {A B : Type} (r : PS A) (r' : PS B) : Prop :=
  psBuffer r = psBuffer r' /\
  psBufLen r = psBufLen r' /\
  psOffset r = psOffset r' /\
  psLength r = psLength r'.

Definition ByteString (r : Rep HeapSpec) := Rep (projT1 (ByteStringHeap r)).

Definition cons (r : Rep HeapSpec) (w : Word) (bs : ByteString r) :
  Comp (ByteString r) :=
  Eval simpl in
    (p <- callMeth (projT1 (ByteStringHeap r)) consS bs w; ret (fst p)).

Lemma consDSL :
  { f : Word -> PS unit -> HeapDSL (PS unit)
  & forall r w bs bs',
      matchPS bs bs' ->
      MonadRefinement matchPS (cons (r:=r) w bs) (f w bs') }.
Proof.
  eexists.
  intros.
  destruct H.
  repeat breakdown.
  unfold cons; simpl.
  eapply MRefine; eauto.
    simplify with monad laws; simpl.
    rewrite refine_If_Then_Else_Bind.
    setoid_rewrite H1.
    reflexivity.
  apply MIf; intros.
    eapply MRefine; eauto.
      simplify with monad laws; simpl.
      reflexivity.
    remember (makePS _ _ _ _ _) as P.
    apply MReturn with (x:=P)
      (x':={| psHeap   := tt
            ; psBuffer := psBuffer bs'
            ; psBufLen := psBufLen bs'
            ; psOffset := psOffset bs' - 1
            ; psLength := psLength bs' + 1 |}); subst.
    repeat constructor;
    simpl in *; auto.
      rewrite H1; reflexivity.
    rewrite H2; reflexivity.
  eapply MRefine; eauto.
    rewrite refine_If_Then_Else_Bind.
    setoid_rewrite H2.
    setoid_rewrite H0.
    reflexivity.
  apply MIf; intros.
    unfold make_room_by_shifting_up.
    eapply MRefine; eauto.
      rewrite refine_bind_bind.
      setoid_rewrite refine_bind_unit at 2.
      simpl.
      reflexivity.
    instantiate (1 := liftF (Memcpy (psBuffer bs') (psBuffer bs' + 1)
                                    (psLength bs') bs')).
    admit.
  eapply MRefine; eauto.
    rewrite refine_If_Then_Else_Bind.
    reflexivity.
  apply MIf; intros.
    unfold make_room_by_growing_buffer, Bind2; simpl.
    eapply MRefine; eauto.
      rewrite refine_bind_bind.
      setoid_rewrite refine_bind_bind at 2.
      setoid_rewrite refine_bind_bind at 2.
      setoid_rewrite refine_bind_unit at 3; simpl.
      unfold ByteStringHeap.buffer_cons_obligation_2.
      reflexivity.
    admit.
  unfold allocate_buffer, Bind2; simpl.
  eapply MRefine; eauto.
    rewrite refine_bind_bind.
    setoid_rewrite refine_bind_unit at 1.
    unfold ByteStringHeap.buffer_cons_obligation_3.
    simpl.
    reflexivity.
  admit.
Admitted.

Definition consDSL' := Eval simpl in projT1 consDSL.
Print consDSL'.

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
