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
Module Import HeapFFI := HeapFFI M.

Import HeapCanonical.
Import FunMaps.
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

Program Instance Comp_Functor : Functor Comp := {
  fmap := fun A B f (x : Comp A) => (v <- x; ret (f v))%comp
}.

Program Instance Comp_Applicative : Applicative Comp := {
  pure := fun _ x => (ret x)%comp;
  ap   := fun A B mf mx => (f <- mf; x <- mx; ret (f x))%comp
}.

Program Instance Comp_Monad : Monad Comp := {
  join := fun A m => (m >>= id)%comp
}.

Definition CompT := StateT (Rep HeapSpec) Comp.

Definition denote {a : Type} : HeapDSL a -> CompT a :=
  let phi (fx : HeapF (CompT a)) : CompT a :=
      match fx with
      | Alloc len k             => res <- (fun r => alloc r len);
                                   k res
      | Free_ addr x            => v <- x;
                                   res <- (fun r => free r addr);
                                   pure[CompT] v
      | Realloc addr len k      => res <- (fun r => realloc r addr len);
                                   k res
      | Peek addr k             => res <- (fun r => peek r addr);
                                   k res
      | Poke addr w x           => v <- x;
                                   res <- (fun r => poke r addr w);
                                   pure[CompT] v
      | Memcpy addr addr2 len x => v <- x;
                                   res <- (fun r => memcpy r addr addr2 len);
                                   pure[CompT] v
      | Memset addr len w x     => v <- x;
                                   res <- (fun r => memset r addr len w);
                                   pure[CompT] v
      end in
  compose (iter phi) (fmap (pure[CompT])).

Definition ByteString (r : Rep HeapSpec) := Rep (projT1 (ByteStringHeap r)).

Definition cons (r : Rep HeapSpec) (w : Word) (bs : ByteString r) :
  Comp (ByteString r) :=
  Eval simpl in
    (p <- callMeth (projT1 (ByteStringHeap r)) consS bs w; ret (fst p)).

Definition matchPS {A B : Type} (r : PS A) (r' : PS B) : Prop :=
  psBuffer r = psBuffer r' /\
  psBufLen r = psBufLen r' /\
  psOffset r = psOffset r' /\
  psLength r = psLength r'.

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

Corollary ret_denote : forall A (x : A) r,
  refineEquiv (denote (pure x) r) (ret (r, x)).
Proof. reflexivity. Qed.

Lemma bind_denote :
  forall A (c' : HeapDSL A) B (k' : A -> HeapDSL B) r,
    refine (a <- denote c' r;
            denote (k' (snd a)) (fst a))
           (denote (c' >>= k') r).
Proof.
  intros; simpl.
  destruct c'; simpl.
    pose proof ret_denote.
    simpl in H.
    rewrite H.
    simplify with monad laws.
    reflexivity.
  unfold comp.
Admitted.

Lemma buffer_cons_denote : forall r r' w,
  refine (buffer_cons r w)
         (res <- denote (buffer_consM r' w) (psHeap r);
          ret {| psHeap   := fst res
               ; psBuffer := psBuffer (snd res)
               ; psBufLen := psBufLen (snd res)
               ; psOffset := psOffset (snd res)
               ; psLength := psLength (snd res) |}).
Proof.
  intros.
  unfold buffer_cons, buffer_consM.
  rewrite <- bind_denote.
Admitted.

Lemma consDSL :
  { f : PSU -> Word -> HeapDSL PSU
  & forall w bs bs',
      matchPS bs bs' ->
      refine (buffer_cons bs w)
             (res <- denote (f bs' w) (psHeap bs);
              ret {| psHeap   := fst res
                   ; psBuffer := psBuffer (snd res)
                   ; psBufLen := psBufLen (snd res)
                   ; psOffset := psOffset (snd res)
                   ; psLength := psLength (snd res) |}) }.
Proof.
  intros.
  exists buffer_consM.
  intros.
  apply buffer_cons_denote.
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
