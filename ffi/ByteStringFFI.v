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
  ByteString.FFI.CompileFFI
  ByteString.ByteString
  ByteString.ByteStringHeap
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx
  Hask.Data.Functor
  Hask.Control.Monad
  Hask.Control.Monad.Trans.FiatState
  Hask.Control.Monad.Free.


(****************************************************************************
 * Compile [buffer_cons] into a [ClientDSL] term
 ****************************************************************************)

Module ByteStringFFI (M : WSfun N_as_DT).

Module Import ByteStringHeap := ByteStringHeap M.
Module Import FunMaps := FunMaps N_as_DT M.

Import HeapCanonical.
Import Heap.

Definition buffer_empty :=
  ret {| psBuffer := 0
       ; psBufLen := 0
       ; psOffset := 0
       ; psLength := 0 |}.

Hint Unfold buffer_empty.

Definition emptyDSL : reflect_ADT_DSL_computation HeapSpec buffer_empty.
Proof.
  Time compile_term.
Defined.

Corollary emptyDSL_correct :
  refine buffer_empty (denote HeapSpec (projT1 emptyDSL)).
Proof. intros; apply denote_refineEquiv. Qed.

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

Definition consDSL r ps w :
  reflect_ADT_DSL_computation HeapSpec (buffer_cons (r, ps) w).
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

Corollary consDSL_correct : forall (r : Rep HeapSpec) (bs : PS) w,
  refine (buffer_cons (r, bs) w)
         (denote HeapSpec (projT1 (consDSL r bs w))).
Proof. intros; apply denote_refineEquiv. Qed.

Hint Unfold buffer_uncons.

Definition unconsDSL r ps:
  reflect_ADT_DSL_computation HeapSpec (buffer_uncons (r, ps)).
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

Corollary unconsDSL_correct : forall (r : Rep HeapSpec) (bs : PS),
  refine (buffer_uncons (r, bs))
         (denote HeapSpec (projT1 (unconsDSL r bs))).
Proof. intros; apply denote_refineEquiv. Qed.

Hint Unfold ByteStringHeap.buffer_append_obligation_1.
Hint Unfold buffer_append.

Definition appendDSL r1 ps1 ps2:
  reflect_ADT_DSL_computation HeapSpec (buffer_append (r1, ps1) (r1, ps2)).
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

Corollary appendDSL_correct : forall (r1 : Rep HeapSpec) (bs1 bs2 : PS),
  refine (buffer_append (r1, bs1) (r1, bs2))
         (denote HeapSpec (projT1 (appendDSL r1 bs1 bs2))).
Proof. intros; apply denote_refineEquiv. Qed.

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
Axiom unsafeDupablePerformIO_inj : forall {a : Type} x y,
  x = y -> @unsafeDupablePerformIO a x = unsafeDupablePerformIO y.

Axiom unsafeDupablePerformIO_returnIO : forall {a : Type} (x : a),
  unsafeDupablePerformIO (returnIO x) = x.

Axiom malloc  : Size -> IO (Ptr Word).
Axiom free    : Ptr Word -> IO ().
Axiom realloc : Ptr Word -> Size -> IO (Ptr Word).
Axiom peek    : Ptr Word -> IO Word.
Axiom poke    : Ptr Word -> Word -> IO ().
Axiom memcpy  : Ptr Word -> Ptr Word -> Size -> IO ().
Axiom memset  : Ptr Word -> Size -> Word -> IO ().

Definition ghcDenote {A : Type} : ClientDSL (getADTSig HeapSpec) (Rep HeapSpec) (IO A) -> IO A.
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

  exact (y HeapState.newHeapState).
  exact (bindIO (malloc (` (hlist_head (hlist_tail h))))
                (y (hlist_head h))).
  exact (bindIO (free (hlist_head (hlist_tail h)))
                (fun _ => y (hlist_head h))).
  exact (bindIO (realloc (hlist_head (hlist_tail h))
                         (` (hlist_head (hlist_tail (hlist_tail h)))))
                (y (hlist_head h))).
  exact (bindIO (peek (hlist_head (hlist_tail h)))
                (y (hlist_head h))).
  exact (bindIO (poke (hlist_head (hlist_tail h))
                      (hlist_head (hlist_tail (hlist_tail h))))
                (fun _ => y (hlist_head h))).
  exact (bindIO (memcpy (hlist_head (hlist_tail h))
                          (hlist_head (hlist_tail (hlist_tail h)))
                          (hlist_head (hlist_tail (hlist_tail (hlist_tail h)))))
                (fun _ => y (hlist_head h))).
  exact (bindIO (memset (hlist_head (hlist_tail h))
                        (hlist_head (hlist_tail (hlist_tail h)))
                        (hlist_head (hlist_tail (hlist_tail (hlist_tail h)))))
                (fun _ => y (hlist_head h))).
Defined.

Corollary bind_If `{Monad f} : forall A B (k : A -> f B) b t e,
  ((If b Then t Else e) >>= k) = If b Then t >>= k Else e >>= k.
Proof. destruct b; reflexivity. Qed.

Corollary bind_IfDep `{Monad f} : forall A B (k : A -> f B) b t e,
  ((IfDep b Then t Else e) >>= k) =
  IfDep b Then (fun H => t H >>= k) Else (fun H => e H >>= k).
Proof. destruct b; reflexivity. Qed.

Corollary fmap_If `{Functor f} : forall A B (k : A -> B) b t e,
  fmap k (If b Then t Else e) = If b Then fmap k t Else fmap k e.
Proof. destruct b; reflexivity. Qed.

Corollary fmap_IfDep `{Functor f} : forall A B (k : A -> B) b t e,
  fmap k (IfDep b Then t Else e) =
  IfDep b Then (fun H => fmap k (t H)) Else (fun H => fmap k (e H)).
Proof. destruct b; reflexivity. Qed.

Corollary iter_If `{Functor f} : forall A (phi : f A -> A) b t e,
  iter phi (If b Then t Else e) = If b Then iter phi t Else iter phi e.
Proof. destruct b; reflexivity. Qed.

Corollary iter_IfDep `{Functor f} : forall A (phi : f A -> A) b t e,
  iter phi (IfDep b Then t Else e) =
  IfDep b Then (fun H => iter phi (t H)) Else (fun H => iter phi (e H)).
Proof. destruct b; reflexivity. Qed.

Corollary ghcDenote_If :
  forall A b (t e : ClientDSL (getADTSig HeapSpec) (Rep HeapSpec) (IO A)),
    ghcDenote (If b Then t Else e) = If b Then ghcDenote t Else ghcDenote e.
Proof. destruct b; reflexivity. Qed.

Corollary ghcDenote_IfDep :
  forall b A (t : b = true -> ClientDSL (getADTSig HeapSpec) (Rep HeapSpec) (IO A))
         (e : b = false -> ClientDSL (getADTSig HeapSpec) (Rep HeapSpec) (IO A)),
    ghcDenote (IfDep b Then t Else e) = IfDep b Then ghcDenote \o t Else ghcDenote \o e.
Proof. destruct b; reflexivity. Qed.

Lemma ghcEmptyDSL :
  { f : PS & f = unsafeDupablePerformIO (ghcDenote (returnIO <$> projT1 emptyDSL)) }.
Proof.
  eexists; intros.
  symmetry.
  unfold comp; simpl.
  unfold ghcDenote; simpl.
  rewrite unsafeDupablePerformIO_returnIO.
  higher_order_reflexivity.
Defined.

Definition ghcEmptyDSL' := Eval simpl in projT1 ghcEmptyDSL.
Print ghcEmptyDSL'.

Lemma ghcConsDSL :
  { f : PS -> Word -> PS
  & forall r bs w,
      f bs w = unsafeDupablePerformIO
                 (ghcDenote ((returnIO \o snd) <$> projT1 (consDSL r bs w))) }.
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
  unfold If_Then_Else.
  higher_order_reflexivity.
Defined.

Definition ghcConsDSL' := Eval simpl in projT1 ghcConsDSL.
Print ghcConsDSL'.

Lemma ghcUnconsDSL :
  { f : PS -> PS * option Word
  & forall r bs,
      f bs = unsafeDupablePerformIO
               (ghcDenote ((fun x => returnIO (snd (fst x), snd x))
                             <$> projT1 (unconsDSL r bs))) }.
Proof.
  eexists; intros.
  symmetry.
  simpl projT1.
  unfold comp.
  simpl If_Then_Else.
  rewrite !fmap_If.
  etransitivity.
    setoid_rewrite ghcDenote_If.
    reflexivity.
  simpl.
  do 4 (unfold compose, comp; simpl).
  unfold ghcDenote; simpl.
  rewrite !bindIO_returnIO.
  unfold If_Then_Else.
  higher_order_reflexivity.
Defined.

Definition ghcUnconsDSL' := Eval simpl in projT1 ghcUnconsDSL.
Print ghcUnconsDSL'.

Lemma ghcAppendDSL :
  { f : PS -> PS -> PS
  & forall r1 bs1 bs2,
      f bs1 bs2 = unsafeDupablePerformIO
                    (ghcDenote ((returnIO \o snd)
                                  <$> projT1 (appendDSL r1 bs1 bs2))) }.
Proof.
  eexists; intros.
  symmetry.
  simpl projT1.
  unfold comp.
  rewrite fmap_IfDep.
  etransitivity.
    setoid_rewrite ghcDenote_IfDep.
    unfold comp.
    apply unsafeDupablePerformIO_inj.
    apply IfDep_Then_Else_fun_Proper; intro H.
      rewrite fmap_IfDep.
      apply ghcDenote_IfDep.
    reflexivity.
  simpl.
  do 4 (unfold compose, comp; simpl).
  unfold ghcDenote; simpl.
  do 2 rewrite strip_IfDep_Then_Else.
  unfold If_Then_Else.
  higher_order_reflexivity.
Defined.

Definition ghcAppendDSL' := Eval simpl in projT1 ghcAppendDSL.
Print ghcAppendDSL'.

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
