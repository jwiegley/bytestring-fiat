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

Module CompLaws.

Axiom prop_ext : forall (P Q : Prop), (P <-> Q) -> P = Q.

Ltac shatter :=
  unfold comp, id in *;
  repeat
    match goal with
    | [ H : and _ _            |- _ ] => destruct H
    | [ H : Bind _ _ _         |- _ ] => destruct H
    | [ H : Ensembles.In _ _ _ |- _ ] => destruct H
    | [ H : Datatypes.prod _ _ |- _ ] => destruct H
    | [ |- and _ _                     ] => split
    | [ |- Bind _ _ _                  ] => eexists
    | [ |- Ensembles.In _ _ _          ] => constructor
    | [ |- Ensembles.In _ _ _          ] => solve [ eauto ]
    | [ |- Ensembles.In _ (Bind _ _) _ ] => eexists
    | [ |- Ensembles.In _ _ _          ] => econstructor
    end;
  simpl in *.

(** jww (2016-04-05): Until the FunctorLaws are expressed in terms of some
    arbitrary equivalence, we need to use functional and propositional
    extensionality. *)

Ltac simplify_comp :=
  repeat let x := fresh "x" in extensionality x;
  try (apply prop_ext; split; intros);
  repeat shatter;
  try constructor; eauto.

Local Obligation Tactic := simpl; intros; simplify_comp.

Import MonadLaws.

Program Instance Comp_FunctorLaws : FunctorLaws Comp.
Program Instance Comp_ApplicativeLaws : ApplicativeLaws Comp.
Program Instance Comp_MonadLaws : MonadLaws Comp.

Lemma fmap_pure_bind `{FunctorLaws f} : forall A B (k : A -> B) v,
  Free_bind id (fmap[Free f] (fun x => Pure (k x)) v) = fmap k v.
Proof.
  intros.
  rewrite <- fmap_comp_x.
  unfold bind, comp, id.
  simpl.
  unfold comp; simpl.
  induction v; simpl.
    reflexivity.
  unfold comp; simpl.
  f_equal.
  extensionality x0.
  apply H1.
Qed.

End CompLaws.

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

Import CompLaws.
Import MonadLaws.

Program Instance HeapF_FunctorLaws : FunctorLaws HeapF.
Obligation 1.
  extensionality x.
  destruct x; auto.
Qed.
Obligation 2.
  extensionality x.
  destruct x; auto.
Qed.

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

Lemma Free_If `{Functor f}
      {R : Type} (crel : forall A, f A -> R -> R -> A -> Prop)
      b r r' B t tr tv e er ev (v : B) :
     (b = true  -> Free_Computes crel t r tr tv)
  -> (b = false -> Free_Computes crel e r er ev)
  -> r' = (if b then tr else er)
  -> v  = (if b then tv else ev)
  -> Free_Computes crel (if b then t else e) r r' v.
Proof.
  intros.
  subst.
  destruct b; eauto.
Qed.

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

(**************************************************************************)

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
Qed.

Lemma reflect_Heap_DSL_computation_If_Then_Else
      {B : Type} c c' (t e : _ -> Comp (_ * B))
      (c_DSL : reflect_Heap_DSL_computation t)
      (k_DSL : reflect_Heap_DSL_computation e)
  : (forall r, c r = c' (snd r)) ->
    reflect_Heap_DSL_computation (fun r => If c r Then t r Else e r).
Proof.
  intros.
  exists (fun bs : PS =>
            if c' bs
            then projT1 c_DSL bs
            else projT1 k_DSL bs).
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
Qed.

Lemma HeapDSL_Computes_inv {A}
  : forall (c : HeapDSL A) r r' v
    (H : HeapDSL_Computes c r r' v),
    match c with
    | Pure a => a = v /\ r = r'
    | Join B f f0 => exists r'' v'',
                       HeapF_Computes f0 r r'' v''
                       /\ HeapDSL_Computes (f v'') r'' r' v
    end.
Proof.
  intros.
  refine (match H with
          | CPure _ _ _ => _
          | CJoin a b c d e f g h i j k => _
          end); auto.
  eexists _, _; eauto.
Qed.

Lemma benjamin r r' r'' bs bs' A (c' : PS -> HeapDSL (PS * A))
      B (f : PS * A -> HeapDSL (PS * B)) (v' : B) x :
  HeapDSL_Computes (c' bs) r r' x
    -> HeapDSL_Computes (f x) r' r'' (bs', v')
    -> HeapDSL_Computes (Free_bind f (c' bs)) r r'' (bs', v').
Proof.
  intros.
  generalize dependent r.
  induction (c' bs); intros.
    eapply HeapDSL_Computes_inv in H.
    destruct H; subst.
    assumption.
  eapply HeapDSL_Computes_inv in H1.
  destruct_ex.
  destruct H1; simpl.
  unfold comp.
  eapply CJoin.
    apply H.
  apply H2.
  assumption.
Qed.

Hint Unfold id.
Hint Unfold bind.
Hint Unfold Bind2.
Hint Unfold allocate_buffer.
Hint Unfold find_free_block.
Hint Unfold make_room_by_growing_buffer.
Hint Unfold make_room_by_shifting_up.
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

Definition consDSL w :
  reflect_Heap_DSL_computation
    (fun r => r' <- buffer_cons (fst r) (snd r) w; ret (r', ())).
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
    apply HPoke; eassumption.

  simplify_reflection.
    simplify_reflection.
    prepare_reflection.
    eapply CJoin.
    eapply CJoin.
    eapply CPure.
    apply HPoke; eassumption.
    apply HMemcpy; eassumption.

  simplify_reflection.
    simplify_reflection.
    prepare_reflection.
    eapply CJoin.
    eapply CJoin.
    eapply CJoin.
    eapply CJoin.
    eapply CPure.
    apply HPoke; eassumption.
    apply HFree; eassumption.
    apply HMemcpy; eassumption.
    eapply HAlloc.
      apply H.
    higher_order_reflexivity.

  simplify_reflection.
  prepare_reflection.
  eapply CJoin.
  eapply CJoin.
  apply CPure.
  apply HPoke; eassumption.
  eapply HAlloc.
    apply H.
  higher_order_reflexivity.
Fail Defined.           (* jww (2016-11-06): what's happening here? *)
Admitted.

(**************************************************************************)

Definition simply_widen_regionM (r : PS) : PS :=
  {| psBuffer := psBuffer r
   ; psBufLen := psBufLen r
   ; psOffset := psOffset r - 1
   ; psLength := psLength r + 1 |}.

Program Definition make_room_by_shifting_upM (r : PS) (n : N | 0 < n) :
  (* We could maybe be smarter by shifting the block so it sits mid-way within
     the buffer. *)
  HeapDSL PS :=
  _ <- memcpyM (psBuffer r) (psBuffer r + n) (psLength r);
  pure {| psBuffer := psBuffer r
        ; psBufLen := psBufLen r
        ; psOffset := 0
        ; psLength := psLength r + n |}.

Program Definition make_room_by_growing_bufferM (r : PS) (n : N | 0 < n) :
  HeapDSL PS :=
  (* We can make a trade-off here by allocating extra bytes in anticipation of
     future calls to [buffer_cons]. *)
  a <- allocM (psLength r + n);
  _ <- memcpyM (psBuffer r) (a + n) (psLength r);
  _ <- freeM (psBuffer r);
  pure {| psBuffer := a
        ; psBufLen := psLength r + n
        ; psOffset := 0
        ; psLength := psLength r + n |}.
Obligation 1. nomega. Defined.

Program Definition allocate_bufferM (r : PS) (len : N | 0 < len) :
  HeapDSL PS :=
  a <- allocM len;
  pure {| psBuffer := a
        ; psBufLen := len
        ; psOffset := 0
        ; psLength := len |}.

Definition poke_at_offsetM (r : PS) (d : Word) : HeapDSL PS :=
  _ <- pokeM (psBuffer r + psOffset r) d;
  pure {| psBuffer := psBuffer r
        ; psBufLen := psBufLen r
        ; psOffset := psOffset r
        ; psLength := psLength r |}.

(* This defines how much a buffer is grown by when more space is needed to
   [cons] on a new element. *)
Definition alloc_quantum := 1.
Arguments alloc_quantum /.

Program Definition buffer_consM (r : PS) (d : Word) : HeapDSL PS :=
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

Theorem consDSL_correct : forall (r : Rep HeapSpec) (bs : PS) w,
  refine (buffer_cons r bs w)
         (denote (buffer_consM bs w) r).
Proof.
  intros.
  destruct r.
  unfold buffer_cons, buffer_consM; simpl.
  repeat rewrite denote_Free_bind; simpl.
  rewrite denote_If; simpl.
  unfold Bind2.
  do 1 rewrite refineEquiv_bind_bind.
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
  [ apply HAlloc   | apply H; eauto
  | apply HFree    | apply H; eauto
  | apply HRealloc | apply H; eauto
  | apply HPeek    | apply H; eauto
  | apply HPoke    | apply H; eauto
  | apply HMemcpy  | apply H; eauto
  | apply HMemset  | apply H; eauto ];
  try destruct u;
  auto.
Qed.

Definition reflect_computation `(c : Rep HeapSpec -> Comp (Rep HeapSpec * A)) :=
  { f : HeapDSL A & forall r r' v, c r ↝ (r', v) -> HeapDSL_Computes f r r' v }.

Lemma reflect_computation' {A : Type} (v : A) :
  { f : HeapDSL A & forall r, ret (r, v) ↝ (r, v) -> HeapDSL_Computes f r r v }.
Proof.
  intros.
  exists (pure v).
  intros.
  eapply CPure.
Defined.

Lemma consDSL' :
  { f : PS -> Word -> HeapDSL PS
  & forall w (r r' : Rep HeapSpec) (bs bs' : PS),
      buffer_cons r bs w ↝ (r', bs') ->
      HeapDSL_Computes (f bs w) r r' bs' }.
Proof.
  Transparent poke.
  Transparent alloc.
  Transparent free.
  Transparent peek.
  Transparent memcpy.
  exists buffer_consM.
  unfold buffer_cons, buffer_consM, Bind2.
  intros w r r' bs bs' H.
  destruct r.
  revert H.
  destruct (0 <? psOffset bs) eqn:Heqe1;
  simpl If_Then_Else.
    unfold poke_at_offset, simply_widen_region,
           poke_at_offsetM, simply_widen_regionM.
    autorewrite with monad laws.
    intros; simpl in H.
    eapply CJoin.
      apply HPoke.
      unfold poke.
      higher_order_reflexivity.
    computes_to_inv; tsubst; simpl.
    unfold id.
    apply CPure.
  destruct (psLength bs + 1 <=? psBufLen bs) eqn:Heqe2;
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
    computes_to_inv; tsubst; simpl.
    apply CPure.
  destruct (0 <? psBufLen bs) eqn:Heqe3;
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
    computes_to_inv; tsubst; simpl.
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
  computes_to_inv; tsubst; simpl.
  apply CPure.
Defined.

Definition consDSL'' := Eval simpl in projT1 consDSL'.

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

Lemma ghcConsDSL :
  { f : PS -> Word -> PS
  & forall bs w, f bs w = ghcDenote (consDSL'' bs w) }.
Proof.
  eexists.
  intros.
  unfold consDSL'', ghcDenote, buffer_consM, compose, comp.
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
