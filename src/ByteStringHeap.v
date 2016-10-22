Require Import
  ByteString.Lib.Tactics
  ByteString.Lib.Nomega
  ByteString.Lib.Fiat
  ByteString.Memory
  ByteString.Heap
  ByteString.HeapCanon
  ByteString.ByteString
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Module ByteStringHeap (M : WSfun N_as_DT).

Module Import HeapCanonical := HeapCanonical M.

Import Heap.
Import HeapState.
Import FMapExt.

Open Scope N_scope.

Record PS (heapType : Type) := makePS {
  psHeap   : heapType;
  psBuffer : Ptr Word;
  psBufLen : Size;
  psOffset : Size;
  psLength : Size
}.

Definition PSH := PS (Rep HeapSpec).

Definition simply_widen_region (r : PSH) : PSH :=
  {| psHeap   := psHeap r
   ; psBuffer := psBuffer r
   ; psBufLen := psBufLen r
   ; psOffset := psOffset r - 1
   ; psLength := psLength r + 1 |}.

Program Definition make_room_by_shifting_up (r : PSH) (n : N | 0 < n) :
  (* We could maybe be smarter by shifting the block so it sits mid-way within
     the buffer. *)
  Comp PSH :=
  res <- memcpy (psHeap r) (psBuffer r) (psBuffer r + n) (psLength r);
  ret {| psHeap   := fst res
       ; psBuffer := psBuffer r
       ; psBufLen := psBufLen r
       ; psOffset := 0
       ; psLength := psLength r + n |}.

Program Definition make_room_by_growing_buffer (r : PSH) (n : N | 0 < n) :
  Comp PSH :=
  (* We can make a trade-off here by allocating extra bytes in anticipation of
     future calls to [buffer_cons]. *)
  `(h, a) <- alloc (psHeap r) (psLength r + n);
  `(h, _) <- memcpy h (psBuffer r) (a + n) (psLength r);
  `(h, _) <- free h (psBuffer r);
  ret {| psHeap   := h
       ; psBuffer := a
       ; psBufLen := psLength r + n
       ; psOffset := 0
       ; psLength := psLength r + n |}.
Obligation 1. nomega. Defined.

Program Definition allocate_buffer (r : Rep HeapSpec) (len : N | 0 < len) :
  Comp PSH :=
  `(h, a) <- alloc r len;
  ret {| psHeap   := h
       ; psBuffer := a
       ; psBufLen := len
       ; psOffset := 0
       ; psLength := len |}.

Definition poke_at_offset (r : PSH) (d : Word) : Comp PSH :=
  res <- poke (psHeap r) (psBuffer r + psOffset r) d;
  ret {| psHeap   := fst res
       ; psBuffer := psBuffer r
       ; psBufLen := psBufLen r
       ; psOffset := psOffset r
       ; psLength := psLength r |}.

(* This defines how much a buffer is grown by when more space is needed to
   [cons] on a new element. *)
Definition alloc_quantum := 1.
Arguments alloc_quantum /.

Program Definition buffer_cons (r : PSH) (d : Word) : Comp PSH :=
  ps <- If 0 <? psOffset r
        Then ret (simply_widen_region r)
        Else
        If psLength r + alloc_quantum <=? psBufLen r
        Then make_room_by_shifting_up r alloc_quantum
        Else
        If 0 <? psBufLen r
        Then make_room_by_growing_buffer r alloc_quantum
        Else allocate_buffer (psHeap r) alloc_quantum;
  poke_at_offset ps d.
Obligation 1. nomega. Defined.
Obligation 2. nomega. Defined.
Obligation 3. nomega. Defined.

Definition buffer_uncons (r : PSH) : Comp (PSH * option Word) :=
  If 0 <? psLength r
  Then (
    w <- peek (psHeap r) (psBuffer r + psOffset r);
    ret ({| psHeap   := psHeap r
          ; psBuffer := psBuffer r
          ; psBufLen := psBufLen r
          ; psOffset := if psLength r =? 1
                        then 0
                        else psOffset r + 1
          ; psLength := psLength r - 1 |}, Some (snd w)))
  Else ret (r, None).

Definition ByteString_list_AbsR (or : Rep ByteStringSpec) (nr : PSH) :=
  length or = N.to_nat (psLength nr) /\
  IF psBufLen nr = 0
  then psOffset nr = 0 /\ psLength nr = 0
  else fits (psBuffer nr) (psBufLen nr)
            (psBuffer nr + psOffset nr) (psLength nr) /\
       M.MapsTo (psBuffer nr) (psBufLen nr) (resvs (psHeap nr)) /\
       (forall i, i < psLength nr
          -> forall x, nth (N.to_nat i) or x = x
          -> forall n, psBuffer nr + psOffset nr + i = n
          -> M.MapsTo n x (bytes (psHeap nr))).

Ltac destruct_AbsR H :=
  let H1 := fresh "H1" in
  let H2 := fresh "H2" in
  destruct H as [H1 H2];
  let H3 := fresh "H3" in
  let H4 := fresh "H4" in
  let data := fresh "data" in
  destruct H2 as [[H [H2 H3]]|[H [H2 [H3 H4]]]];
  [ rewrite ?H, ?H2 in * |].

Ltac construct_AbsR := split; try split; simpl; try nomega.

Corollary If_Then_Else_computes_to : forall b A (t e : Comp A) (v : A),
  (If b Then t Else e) ↝ v -> If b Then (t ↝ v) Else (e ↝ v).
Proof. destruct b; trivial. Qed.

Ltac if_computes_to_inv :=
  match goal with
    [ H : (If ?B Then _ Else _) ↝ _ |- _ ] =>
    let Heqe := fresh "Heqe" in
    destruct B eqn:Heqe;
    simpl in H;
    computes_to_inv
  end.

Tactic Notation "by" tactic(H) :=
  H; first [ tauto
           | discriminate
           | auto
           | congruence
           | eauto
           | intuition
           | firstorder ].

Ltac reduce_peano i :=
  destruct i using N.peano_ind;
  [ left; nomega
  | right; split; [nomega|] ];
  try rewrite N2Nat.inj_succ in *.

Ltac prepare_AbsR AbsR :=
  destruct_computations; simpl in *;
  destruct_AbsR AbsR; construct_AbsR;
  right; split; [nomega|]; split; [nomega|];
  split; trivial; intros; simplify_maps.

Corollary If_Then_Else_MapsTo : forall b k k' elt (e : elt) r,
  (If b
   Then M.MapsTo k  e r
   Else M.MapsTo k' e r) = M.MapsTo (If b Then k Else k') e r.
Proof. destruct b; trivial. Qed.

Lemma buffer_cons_sound : forall r_o r_n,
  ByteString_list_AbsR r_o r_n
    -> forall x r_n', buffer_cons r_n x ↝ r_n'
    -> ByteString_list_AbsR (x :: r_o) r_n'.
Proof.
  unfold buffer_cons; intros ? ? AbsR ???.
  computes_to_inv.
  if_computes_to_inv; subst.
    prepare_AbsR AbsR.
    reduce_peano i; clear IHi.
    eapply H4; eauto; nomega.
  if_computes_to_inv; subst.
    prepare_AbsR AbsR.
    reduce_peano i; clear IHi.
    apply copy_bytes_mapsto.
    destruct (within_bool _ _ n) eqn:Heqe1; simpl;
    eapply H4; eauto; nomega.
  if_computes_to_inv; subst.
    prepare_AbsR AbsR.
      split.
        apply_for_all; nomega.
      simplify_maps.
    reduce_peano i; clear IHi.
    apply copy_bytes_mapsto.
    rewrite If_Then_Else_MapsTo.
    apply H4 with (i:=i); try nomega.
    assert (psOffset r_n = 0) as HA by nomega.
    rewrite HA, <- H6, !N.add_0_r in *; clear HA H6 n.
    setoid_replace (x1 + N.succ i - (x1 + 1) + psBuffer r_n)
      with (psBuffer r_n + i) by nomega.
    destruct (within_bool _ _ _) eqn:Heqe2; simpl; trivial.
    nomega.
  prepare_AbsR AbsR.
  reduce_peano i; nomega.
Qed.

Lemma buffer_uncons_sound : forall r_o r_n a,
  ByteString_list_AbsR r_o r_n
    -> buffer_uncons r_n ↝ a
    -> ByteString_list_AbsR (match r_o with
                             | [] => r_o
                             | _ :: xs => xs
                             end) (fst a).
Proof.
  unfold buffer_uncons; intros.
  apply refine_computes_to in H0.
  apply refine_If_Then_Else_bool in H0.
  destruct (0 <? psLength r_n) eqn:Heqe.
    revert H0.
    autorewrite with monad laws; simpl; intros.
    apply computes_to_refine in H0.
    destruct_computations; simpl.
    destruct_AbsR H; construct_AbsR;
    destruct x; try destruct p; simpl in *;
    destruct r_o; simpl in *;
    try nomega; right;
    split; try nomega; split;
    destruct (@psLength HeapState r_n =? 1) eqn:Heqe2;
    try nomega;
    try (eexists; split; [exact H4|]; nomega).
    split; trivial; intros.
    destruct i using N.peano_ind.
      simpl in *.
      rewrite N.add_0_r, N.add_assoc in H7.
      rewrite <- H7.
      eapply H4; eauto; nomega.
    apply H4 with (i:=N.succ (N.succ i)); try nomega.
    by rewrite !N2Nat.inj_succ in *.
  apply computes_to_refine in H0.
  destruct_computations.
  destruct_AbsR H; construct_AbsR;
  destruct r_o; simpl in *; auto; try nomega.
    left; intuition.
  right; intuition.
Qed.

Lemma buffer_uncons_impl : forall r_o r_n a,
  ByteString_list_AbsR r_o r_n
    -> buffer_uncons r_n ↝ a
    -> snd a = match r_o with
               | [] => None
               | x :: _ => Some x
               end.
Proof.
  unfold buffer_uncons; intros.
  apply refine_computes_to in H0.
  apply refine_If_Then_Else_bool in H0.
  destruct (0 <? psLength r_n) eqn:Heqe.
    revert H0.
    autorewrite with monad laws; simpl; intros.
    apply computes_to_refine in H0.
    destruct_computations.
    destruct_AbsR H; simpl;
    destruct r_o; simpl in *; try nomega.
    f_equal; tsubst.
    apply H0.
    replace (@psBuffer HeapState r_n + @psOffset HeapState r_n)
       with (@psBuffer HeapState r_n + @psOffset HeapState r_n + 0) by nomega.
    eapply H4; eauto; nomega.
  apply computes_to_refine in H0.
  apply Return_inv in H0.
  destruct a; tsubst; simpl in *.
  destruct r_o; simpl in *;
  destruct H, H0; auto.
    destruct H0, H1.
    rewrite H2 in H; simpl in H.
    discriminate.
  nomega.
Qed.

Theorem ByteStringHeap (heap : Rep HeapSpec) :
  { adt : _ & refineADT ByteStringSpec adt }.
Proof.
  eexists.

  hone representation using ByteString_list_AbsR.

  {
    simplify with monad laws.
    refine pick val {| psHeap   := heap
                     ; psBuffer := 0
                     ; psBufLen := 0
                     ; psOffset := 0
                     ; psLength := 0 |}.
      finish honing.
    firstorder.
  }

  {
    simplify with monad laws.
    etransitivity.
      eapply (refine_skip2 (dummy:=buffer_cons r_n d)).
    etransitivity.
      apply refine_under_bind; intros; simpl.
      refine pick val a.
        simplify with monad laws.
        finish honing.
      eapply buffer_cons_sound; eauto.
    simplify with monad laws; simpl.
    finish honing.
  }

  {
    simplify with monad laws.
    etransitivity.
      eapply (refine_skip2 (dummy:=buffer_uncons r_n)).
    etransitivity.
      apply refine_under_bind; intros; simpl.
      pose proof H1.
      eapply buffer_uncons_impl in H1; eauto.
      rewrite fst_match_list, snd_match_list, <- H1.
      refine pick val (fst a).
        simplify with monad laws.
        rewrite <- surjective_pairing.
        finish honing.
      eapply buffer_uncons_sound; eauto.
    simplify with monad laws.
    finish honing.
  }

  apply reflexivityT.
Defined.

End ByteStringHeap.
