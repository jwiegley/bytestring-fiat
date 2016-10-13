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
  | Free_   : forall (addr : Ptr), r -> HeapF r
  | Realloc : forall (addr : Ptr) (len : Size | 0 < len) (k : N -> r), HeapF r
  | Peek    : forall (addr : Ptr) (k : Word -> r), HeapF r
  | Poke    : forall (addr : Ptr) (w : Word), r -> HeapF r
  | Memcpy  : forall (addr : Ptr) (addr2 : Ptr) (len : Size), r -> HeapF r
  | Memset  : forall (addr : Ptr) (len : Ptr) (w : Word), r -> HeapF r.

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

Definition allocM (len : Size | 0 < len) : HeapDSL N :=
  liftF (Alloc len id).

Definition freeM (addr : Ptr) : HeapDSL () :=
  liftF (Free_ addr ()).

Definition reallocM (addr : Ptr) (len : Size | 0 < len) : HeapDSL Ptr :=
  liftF (Realloc addr len id).

Definition peekM (addr : Ptr) : HeapDSL Word :=
  liftF (Peek addr id).

Definition pokeM (addr : Ptr) (w : Word) : HeapDSL () :=
  liftF (Poke addr w ()).

Definition memcpyM (addr : Ptr) (addr2 : Ptr) (len : Size) : HeapDSL () :=
  liftF (Memcpy addr addr2 len ()).

Definition memsetM (addr : Ptr) (len : Ptr) (w : Word) : HeapDSL () :=
  liftF (Memset addr len w ()).

Inductive HeapF_Computes :
  forall {A}, HeapF A -> Rep HeapSpec -> Rep HeapSpec -> A -> Prop :=
  | HAlloc len addr (r r' : Rep HeapSpec) :
      alloc r len ↝ (r', addr) ->
      HeapF_Computes (Alloc len id) r r' addr

  | HFree addr (r r' : Rep HeapSpec) :
      free r addr ↝ (r', tt) ->
      HeapF_Computes (Free_ addr tt) r r' tt

  | HPoke addr w (r r' : Rep HeapSpec) :
      poke r addr w ↝ (r', tt) ->
      HeapF_Computes (Poke addr w tt) r r' tt

  | HMemcpy addr addr2 len r r' :
      memcpy r addr addr2 len ↝ (r', tt) ->
      HeapF_Computes (Memcpy addr addr2 len tt) r r' tt.

Inductive Free_Computes `{Functor f} {R : Type}
          (crel : forall {A}, f A -> R -> R -> A -> Prop) :
  forall {A}, Free f A -> R -> R -> A -> Prop :=
  | CPure r A (v : A) : Free_Computes crel (Pure v) r r v
  | CJoin r r'' B (v' : B) :
      forall A t k r' v, crel A t r r' v
        -> Free_Computes crel (k v) r' r'' v'
        -> Free_Computes crel (Join k t) r r'' v'.

Definition HeapDSL_Computes `(h : HeapDSL A) :=
  Free_Computes (@HeapF_Computes) h.

Definition ByteString (r : Rep HeapSpec) := Rep (projT1 (ByteStringHeap r)).

Definition cons (r : Rep HeapSpec) (w : Word) (bs : ByteString r) :
  Comp (ByteString r) :=
  Eval simpl in
    (p <- callMeth (projT1 (ByteStringHeap r)) consS bs w; ret (fst p)).

Program Instance PS_Functor : Functor PS := {
  fmap := fun _ _ f x =>
            match x with
            | makePS h a b c d => makePS (f h) a b c d
            end
}.

Definition PSU := PS ().

Definition simply_widen_regionM (r : PSU) : PSU :=
  {| psHeap   := psHeap r
   ; psBuffer := psBuffer r
   ; psBufLen := psBufLen r
   ; psOffset := psOffset r - 1
   ; psLength := psLength r + 1 |}.

Program Definition make_room_by_shifting_upM (r : PSU) (n : N | 0 < n) :
  (* We could maybe be smarter by shifting the block so it sits mid-way within
     the buffer. *)
  HeapDSL PSU :=
  _ <- memcpyM (psBuffer r) (psBuffer r + n) (psLength r);
  pure {| psHeap   := tt
        ; psBuffer := psBuffer r
        ; psBufLen := psBufLen r
        ; psOffset := 0
        ; psLength := psLength r + n |}.

Program Definition make_room_by_growing_bufferM (r : PSU) (n : N | 0 < n) :
  HeapDSL PSU :=
  (* We can make a trade-off here by allocating extra bytes in anticipation of
     future calls to [buffer_cons]. *)
  a   <- allocM (psLength r + n);
  _   <- memcpyM (psBuffer r) (a + n) (psLength r);
  _   <- freeM (psBuffer r);
  pure {| psHeap   := tt
        ; psBuffer := a
        ; psBufLen := psLength r + n
        ; psOffset := 0
        ; psLength := psLength r + n |}.
Obligation 1. nomega. Defined.

Program Definition allocate_bufferM (r : PSU) (len : N | 0 < len) :
  HeapDSL PSU :=
  a <- allocM len;
  pure {| psHeap   := tt
        ; psBuffer := a
        ; psBufLen := len
        ; psOffset := 0
        ; psLength := len |}.

Definition poke_at_offsetM (r : PSU) (d : Word) : HeapDSL PSU :=
  _ <- pokeM (psBuffer r + psOffset r) d;
  pure {| psHeap   := tt
        ; psBuffer := psBuffer r
        ; psBufLen := psBufLen r
        ; psOffset := psOffset r
        ; psLength := psLength r |}.

(* This defines how much a buffer is grown by when more space is needed to
   [cons] on a new element. *)
Definition alloc_quantum := 1.
Arguments alloc_quantum /.

Program Definition buffer_consM (r : PSU) (d : Word) : HeapDSL PSU :=
  ps <- If 0 <? psOffset r
        Then pure (simply_widen_regionM r)
        Else
        If psLength r + alloc_quantum <=? psBufLen r
        Then make_room_by_shifting_upM r alloc_quantum
        Else
        If 0 <? psBufLen r
        Then make_room_by_growing_bufferM r alloc_quantum
        Else allocate_bufferM r alloc_quantum;
  poke_at_offsetM ps d.
Obligation 1. nomega. Defined.
Obligation 2. nomega. Defined.
Obligation 3. nomega. Defined.

Lemma consDSL :
  { f : PS () -> Word -> HeapDSL (PS ())
  & forall w (r r' : PSH),
      buffer_cons r w ↝ r' ->
      HeapDSL_Computes (f (() <$ r) w) (psHeap r) (psHeap r')
                       (() <$ r') }.
Proof.
  exists buffer_consM.
  unfold buffer_cons, buffer_consM.
  intros w r r' H.
  destruct r.
  simpl psOffset in *.
  simpl psLength in *.
  simpl psBuffer in *.
  simpl psBufLen in *.
  revert H.
  destruct (0 <? psOffset0) eqn:Heqe1;
  simpl If_Then_Else.
    unfold poke_at_offset, simply_widen_region,
           poke_at_offsetM, simply_widen_regionM.
    autorewrite with monad laws.
    intros; simpl in H.
    eapply CJoin.
      apply HPoke.
      unfold poke.
      higher_order_reflexivity.
    computes_to_inv; subst; simpl.
    apply CPure.
  destruct (psLength0 + 1 <=? psBufLen0) eqn:Heqe2;
  simpl If_Then_Else.
    unfold make_room_by_shifting_up, make_room_by_shifting_upM.
    simpl If_Then_Else.
    autorewrite with monad laws.
    intros; simpl in H.
    eapply CJoin.
      apply HMemcpy.
      unfold memcpy; simpl.
      higher_order_reflexivity.
    unfold poke_at_offsetM.
    eapply CJoin.
      simpl.
      apply HPoke.
      higher_order_reflexivity.
    computes_to_inv; subst; simpl.
    apply CPure.
  destruct (0 <? psBufLen0) eqn:Heqe3;
  simpl If_Then_Else.
    unfold make_room_by_growing_buffer, make_room_by_growing_bufferM.
    simpl If_Then_Else.
    unfold Bind2.
    simpl alloc; simpl memcpy.
    autorewrite with monad laws.
    intros; simpl in H.
    computes_to_inv; subst.
    eapply CJoin.
      apply HAlloc with (addr:=v).
      unfold alloc; simpl.
      computes_to_econstructor.
        exact H.
      constructor.
    eapply CJoin.
      apply HMemcpy.
      higher_order_reflexivity.
    eapply CJoin.
      apply HFree.
      unfold free.
      simpl.
      higher_order_reflexivity.
    unfold poke_at_offsetM.
    eapply CJoin.
      simpl.
      apply HPoke.
      higher_order_reflexivity.
    computes_to_inv; subst; simpl.
    apply CPure.
  unfold allocate_buffer, allocate_bufferM.
  unfold Bind2.
  autorewrite with monad laws.
  intros; simpl in H.
  computes_to_inv; subst.
  eapply CJoin.
    apply HAlloc with (addr:=v).
    unfold alloc; simpl.
    computes_to_econstructor.
      exact H.
    constructor.
  unfold poke_at_offsetM.
  eapply CJoin.
    simpl.
    apply HPoke.
    higher_order_reflexivity.
  computes_to_inv; subst; simpl.
  apply CPure.
Defined.

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
