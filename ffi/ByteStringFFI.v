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

Definition allocM (len : Size | 0 < len) : HeapDSL N :=
  liftF (Alloc len id).

Definition freeM (addr : Ptr Word) : HeapDSL () :=
  liftF (Free_ addr ()).

Definition reallocM (addr : Ptr Word) (len : Size | 0 < len) : HeapDSL (Ptr Word) :=
  liftF (Realloc addr len id).

Definition peekM (addr : Ptr Word) : HeapDSL Word :=
  liftF (Peek addr id).

Definition pokeM (addr : Ptr Word) (w : Word) : HeapDSL () :=
  liftF (Poke addr w ()).

Definition memcpyM (addr : Ptr Word) (addr2 : Ptr Word) (len : Size) : HeapDSL () :=
  liftF (Memcpy addr addr2 len ()).

Definition memsetM (addr : Ptr Word) (len : Ptr Word) (w : Word) : HeapDSL () :=
  liftF (Memset addr len w ()).

Inductive HeapF_Computes :
  forall {A}, HeapF A -> Rep HeapSpec -> Rep HeapSpec -> A -> Prop :=
  | HAlloc len addr (r r' : Rep HeapSpec) A (k : Ptr Word -> A) :
      alloc r len ↝ (r', addr) ->
      HeapF_Computes (Alloc len k) r r' (k addr)

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
      forall A t k r' v, crel A t r r' v
        -> Free_Computes crel (k v) r' r'' v'
        -> Free_Computes crel (Join k t) r r'' v'.

Ltac retract comp :=
  match goal with
    [ |- Free Comp ?T ?TS ] =>
    assert { c : Comp T
           & { f : Free Comp T TS & refineEquiv (retract f) c } }
      as freeified
      by (exists comp;
          eexists;
          unfold comp;
          repeat
            match goal with
            | [ |- refineEquiv (retract _) (Bind ?C _) ] =>
              instantiate (1 := Join _ C); unfold id; simpl;
              autorewrite with monad laws;
              apply refineEquiv_bind; [ reflexivity |];
              intros ?; unfold id; simpl
            | [ |- refineEquiv (retract (_ ?X)) (Bind ?C _) ] =>
              instantiate (1 := fun X => Join _ C); unfold id; simpl;
              autorewrite with monad laws;
              apply refineEquiv_bind; [ reflexivity |];
              intros ?; unfold id; simpl
            | [ |- refineEquiv (retract _) (Return _) ] =>
              instantiate (1 := fun _ => Pure _); unfold id; simpl;
              autorewrite with monad laws;
              reflexivity
            end);
    exact (projT1 (projT2 freeified))
  end.

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
  a <- allocM (psLength r + n);
  _ <- memcpyM (psBuffer r) (a + n) (psLength r);
  _ <- freeM (psBuffer r);
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

Corollary refineEquiv_Pure : forall A (x : A),
  refineEquiv (ret x) (retract (Pure x)).
Proof. reflexivity. Qed.

Corollary refineEquiv_Join {A B : Type} (c : Comp A) (f : A -> Comp B) :
  refineEquiv (Bind c f) (retract (Join (liftF \o f) c)).
Proof.
  simpl.
  autorewrite with monad laws.
  reflexivity.
Qed.

Definition enwrap (f : Rep HeapSpec -> Comp (Rep HeapSpec)) (h : PSH) :
  Comp PSH :=
  r <- f (psHeap h);
  ret {| psHeap   := r
       ; psBuffer := psBuffer h
       ; psBufLen := psBufLen h
       ; psOffset := psOffset h
       ; psLength := psLength h |}.

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

Corollary Free_bind_Pure `{Functor f} : forall A B (k : A -> B) (c : Free f A),
  Free_bind (fun x : A => Pure (k x)) c = fmap k c.
Proof. destruct c; reflexivity. Qed.

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

Theorem consDSL_correct : forall (r : PSH) w,
  refine (r' <- buffer_cons r w;
          ret (() <$ r'))
         (let ru : PSU := () <$ r in
          r' <- denote (buffer_consM ru w) (psHeap r);
          ret (snd r')).
Proof.
  intros.
  destruct r.
  unfold buffer_cons, buffer_consM; simpl.
  repeat rewrite denote_Free_bind; simpl.
  rewrite denote_If; simpl.
  do 3 rewrite refineEquiv_bind_bind.
  do 4 rewrite refineEquiv_If_Then_Else_Bind.
  apply refine_If_Then_Else.
    unfold poke_at_offsetM, simply_widen_regionM; simpl.
    autorewrite with monad laws; reflexivity.
  rewrite denote_If; simpl.
  rewrite refineEquiv_If_Then_Else_Bind.
  apply refine_If_Then_Else.
    unfold make_room_by_shifting_upM, memcpyM; simpl.
    autorewrite with monad laws; reflexivity.
  rewrite denote_If; simpl.
  rewrite refineEquiv_If_Then_Else_Bind.
  apply refine_If_Then_Else.
    unfold make_room_by_growing_bufferM, allocM, memcpyM, freeM; simpl.
    autorewrite with monad laws; reflexivity.
  unfold allocate_bufferM; simpl.
  autorewrite with monad laws; reflexivity.
Qed.

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
  [ apply HAlloc
  | apply H; eauto
  | apply HFree
  | apply H; eauto
  | apply HRealloc
  | apply H; eauto
  | apply HPeek
  | apply H; eauto
  | apply HPoke
  | apply H; eauto
  | apply HMemcpy
  | apply H; eauto
  | apply HMemset
  | apply H; eauto ];
  try destruct u;
  auto.
Qed.

Lemma consDSL :
  { f : PS () -> Word -> HeapDSL (PS ())
  & forall w (r r' : PSH),
      buffer_cons r w ↝ r' ->
      HeapDSL_Computes (f (() <$ r) w) (psHeap r) (psHeap r')
                       (() <$ r') }.
Proof.
  eexists buffer_consM.
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

Axiom IO : Type -> Type.
Axiom fmapIO : forall {a b : Type}, (a -> b) -> IO a -> IO b.
Axiom returnIO : forall {a : Type}, a -> IO a.
Axiom joinIO : forall {a : Type}, IO (IO a) -> IO a.

Program Instance IO_Functor : Functor IO := {
  fmap := fun _ _ => fmapIO
}.

Program Instance IO_Applicative : Applicative IO := {
  pure := fun _ => returnIO;
  ap   := fun _ _ mf mx =>
            joinIO (fmapIO (fun f => fmapIO (fun x => f x) mx) mf)
}.

Program Instance IO_Monad : Monad IO := {
  join := fun _ => joinIO
}.

Axiom unsafeDupablePerformIO : forall {a : Type}, IO a -> a.
Axiom malloc : Size -> IO (Ptr Word).
Axiom free : Ptr Word -> IO ().
Axiom realloc : Ptr Word -> Size -> IO (Ptr Word).
Axiom peek   : Ptr Word -> IO Word.
Axiom poke   : Ptr Word -> Word -> IO ().
Axiom memcpy : Ptr Word -> Ptr Word -> Size -> IO ().
Axiom memset : Ptr Word -> Size -> Word -> IO ().

Definition ghcDenote {A : Type} : HeapDSL A -> A :=
  let phi (c : HeapF (IO A)) :=
    match c with
    | Alloc len k             => malloc (` len) >>= k
    | Free_ addr x            => free addr >> x
    | Realloc addr len k      => realloc addr (` len) >>= k
    | Peek addr k             => peek addr >>= k
    | Poke addr w x           => poke addr w >> x
    | Memcpy addr addr2 len x => memcpy addr addr2 len >> x
    | Memset addr len w x     => memset addr len w >> x
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

Lemma ghcConsDSL :
  { f : PSU -> Word -> PSU
  & forall bs w, f bs w = ghcDenote (consDSL' bs w) }.
Proof.
  eexists.
  intros.
  unfold consDSL', ghcDenote, buffer_consM, compose, comp.
  symmetry.
  rewrite !bind_If.
  do 3 rewrite fmap_If.
  etransitivity.
    do 3 setoid_rewrite iter_If.
    simpl.
    unfold If_Then_Else, compose, comp; simpl.
    reflexivity.
  reflexivity.
Defined.

Definition ghcConsDSL' := Eval simpl in projT1 ghcConsDSL.
(* Print ghcConsDSL'. *)

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
