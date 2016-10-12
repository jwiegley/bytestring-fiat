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

Record Mem := {
  heap_rep : EMap Ptr Size;
  mem_rep  : EMap Ptr Word;
}.

Inductive HeapDSL_Computes :
  forall {A}, HeapDSL A -> A
    -> (Rep HeapSpec -> Comp (Rep HeapSpec * A))
    -> Rep HeapSpec -> Rep HeapSpec -> Prop :=
  | RPure r T (v : T) c :
      refine (ret (r, v)) (c r) ->
      HeapDSL_Computes (pure v) v c r r

  | RBind r r' r'' T t c (v : T) C k ctk h (v' : C) :
      HeapDSL_Computes t v c r r'
        -> HeapDSL_Computes (k v) v' (h v) r' r''
        -> refine (c r >>= fun p => h (snd p) (fst p)) (ctk r)%comp
        -> HeapDSL_Computes (t >>= k)%monad v' ctk r r''

  | RIf b r r' T (t e : HeapDSL T) c ct ce (v : T) :
      (b = true  -> HeapDSL_Computes t v ct r r') ->
      (b = false -> HeapDSL_Computes e v ce r r') ->
      refine (If b Then ct r Else ce r) (c r) ->
      HeapDSL_Computes (If b Then t Else e) v c r r'

  | RAlloc len addr (r r' : Rep HeapSpec) :
      HeapDSL_Computes (allocM len) addr (fun r => alloc r len) r r'

  | RFree addr (r r' : Rep HeapSpec) :
      free r addr ↝ (r', tt) ->
      HeapDSL_Computes (freeM addr) tt (fun r => free r addr) r r'

  | RPoke addr w (r r' : Rep HeapSpec) :
      poke r addr w ↝ (r', tt) ->
      HeapDSL_Computes (pokeM addr w) tt (fun r => poke r addr w) r r'

  | RMemcpy addr addr2 len r r' c :
      refine (memcpy r addr addr2 len) (c r) ->
      HeapDSL_Computes (memcpyM addr addr2 len) tt c r r'.

  (* | RMemcpy addr addr2 len r r' : *)
  (*     HeapDSL_Computes (memcpyM addr addr2 len) tt *)
  (*                      (fun r => memcpy r addr addr2 len) r r'. *)

Definition Mem_AbsR (or : Rep HeapSpec) (nr : Mem) :=
  Map_AbsR eq (heap_rep nr) (resvs or) /\
  Map_AbsR eq (mem_rep nr)  (bytes or).

Definition ByteString (r : Rep HeapSpec) := Rep (projT1 (ByteStringHeap r)).

(*
Definition HeapRelation
           `(c : R -> Comp (R * A))
           (f : R -> Rep HeapSpec)
           `(t : HeapDSL B)
           (AbsR : R -> B -> Prop)
           (r r' : R) (m m' : Mem) (a : A) :=
  computes_to (c r) (r', a)
    -> Mem_AbsR (f r) m
    -> Mem_AbsR (f r') m'
    -> forall b, AbsR r' b
    -> HeapDSL_Computes t m m' b.
*)

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

Lemma consDSL :
  { f : PS () -> Word -> HeapDSL (PS ())
  & forall w (r r' : PSH) (bs bs' : PS ()),
      matchPS r bs -> matchPS r' bs' ->
      HeapDSL_Computes
        (f bs w) bs'
        (fun h =>
           let ps := {| psHeap   := h
                      ; psBuffer := psBuffer bs
                      ; psBufLen := psBufLen bs
                      ; psOffset := psOffset bs
                      ; psLength := psLength bs |} in
           h' <- buffer_cons ps w;
           ret (psHeap h',
                {| psHeap   := tt
                 ; psBuffer := psBuffer h'
                 ; psBufLen := psBufLen h'
                 ; psOffset := psOffset h'
                 ; psLength := psLength h' |}))%comp
        (psHeap r) (psHeap r') }.
Proof.
  exists buffer_consM.
  unfold buffer_cons, buffer_consM.
  intros.
  destruct H, H1, H2.
  rewrite <- H1, <- H2, <- H3.
  { eapply RBind with (v:=bs') (r':=psHeap r').
    - eapply RIf; intros.
        unfold simply_widen_regionM; simpl.
        apply RPure.
        higher_order_reflexivity.
      apply RIf; intros.
        unfold make_room_by_shifting_upM.
        simpl memcpyM; simpl pure.
        { eapply RBind.
          - apply RMemcpy.
            higher_order_reflexivity.
          - apply RPure.
            higher_order_reflexivity.
          - simplify with monad laws; simpl.
            higher_order_reflexivity.
        }
      apply RIf; intros.
        unfold make_room_by_growing_bufferM.
        simpl allocM; simpl memcpyM; simpl pure.
        { eapply RBind.
          - apply RAlloc.
          - { eapply RBind.
              - apply RMemcpy.
                higher_order_reflexivity.
              - { eapply RBind.
                  - apply RFree.
                    constructor.
                  - apply RPure.
                    higher_order_reflexivity.
                  - simplify with monad laws; simpl.
                    higher_order_reflexivity.
                }
              - simplify with monad laws; simpl.
                higher_order_reflexivity.
            }
          - simplify with monad laws; simpl.
            higher_order_reflexivity.
        }
      unfold allocate_bufferM.
      simpl allocM; simpl pure.
      { eapply RBind.
        - apply RAlloc.
        - apply RPure.
          higher_order_reflexivity.
        - simplify with monad laws; simpl.
          higher_order_reflexivity.
      }
    - unfold poke_at_offsetM.
      { eapply RBind.
        - apply RPoke.
          admit.
        - admit.
        - simplify with monad laws; simpl.
          higher_order_reflexivity.
      }
    - admit.
  }
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
