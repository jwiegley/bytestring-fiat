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

Record PS := makePS {
  psBuffer : Ptr Word;
  psBufLen : Size;
  psOffset : Size;
  psLength : Size
}.

Definition simply_widen_region (r : PS) (n : N) : PS :=
  {| psBuffer := psBuffer r
   ; psBufLen := psBufLen r
   ; psOffset := psOffset r - n
   ; psLength := psLength r + n |}.

Definition make_room_by_shifting_up
        (h : Rep HeapSpec) (r : PS) (n : N | 0 < n) :
  (* We could maybe be smarter by shifting the block so it sits mid-way within
     the buffer. *)
  Comp (Rep HeapSpec * PS) :=
  res <- memcpy h (psBuffer r) (psBuffer r + ` n) (psLength r);
  ret (res,
       {| psBuffer := psBuffer r
        ; psBufLen := psBufLen r
        ; psOffset := 0
        ; psLength := psLength r + ` n |}).

Program Definition make_room_by_growing_buffer
        (h : Rep HeapSpec) (r : PS) (n : N | 0 < n) :
  Comp (Rep HeapSpec * PS) :=
  (* We can make a trade-off here by allocating extra bytes in anticipation of
     future calls to [buffer_cons]. *)
  `(h, a) <- alloc h (psLength r + n);
  h <- memcpy h (psBuffer r) (a + n) (psLength r);
  h <- free h (psBuffer r);
  ret (h, {| psBuffer := a
           ; psBufLen := psLength r + n
           ; psOffset := 0
           ; psLength := psLength r + n |}).
Obligation 1. nomega_. Defined.

Program Definition allocate_buffer (h : Rep HeapSpec) (len : N | 0 < len) :
  Comp (Rep HeapSpec * PS) :=
  `(h, a) <- alloc h len;
  ret (h, {| psBuffer := a
           ; psBufLen := len
           ; psOffset := 0
           ; psLength := len |}).

Definition poke_at_offset (h : Rep HeapSpec) (r : PS) (d : Word) :
  Comp (Rep HeapSpec * PS) :=
  res <- poke h (psBuffer r + psOffset r) d;
  ret (res,
       {| psBuffer := psBuffer r
        ; psBufLen := psBufLen r
        ; psOffset := psOffset r
        ; psLength := psLength r |}).

(* This defines how much a buffer is grown by when more space is needed to
   [cons] on a new element. *)
Definition alloc_quantum := 1.
Arguments alloc_quantum /.

Program Definition buffer_cons (h : Rep HeapSpec) (r : PS) (d : Word) :
  Comp (Rep HeapSpec * PS) :=
  `(h, ps) <-
    If 0 <? psOffset r
    Then ret (h, simply_widen_region r 1)
    Else
    If psLength r + alloc_quantum <=? psBufLen r
    Then make_room_by_shifting_up h r alloc_quantum
    Else
    If 0 <? psBufLen r
    Then make_room_by_growing_buffer h r alloc_quantum
    Else allocate_buffer h alloc_quantum;
  poke_at_offset h ps d.
Obligation 1. nomega_. Defined.
Obligation 2. nomega_. Defined.
Obligation 3. nomega_. Defined.

Definition buffer_uncons (h : Rep HeapSpec) (r : PS) :
  Comp ((Rep HeapSpec * PS) * option Word) :=
  If 0 <? psLength r
  Then (
    w <- peek h (psBuffer r + psOffset r);
    ret (h, {| psBuffer := psBuffer r
             ; psBufLen := psBufLen r
             ; psOffset := if psLength r =? 1
                           then 0
                           else psOffset r + 1
             ; psLength := psLength r - 1 |}, Some (snd w)))
  Else ret ((h, r), None).

Definition ByteString_list_AbsR
           (or : Rep ByteStringSpec) (nr : Rep HeapSpec * PS) :=
  let ps := snd nr in
  length or = N.to_nat (psLength ps) /\
  IF psBufLen ps = 0
  then psOffset ps = 0 /\ psLength ps = 0
  else fits (psBuffer ps) (psBufLen ps)
            (psBuffer ps + psOffset ps) (psLength ps) /\
       M.MapsTo (psBuffer ps) (psBufLen ps) (resvs (fst nr)) /\
       (forall i, i < psLength ps
          -> forall x, nth (N.to_nat i) or x = x
          -> forall n, psBuffer ps + psOffset ps + i = n
          -> M.MapsTo n x (bytes (fst nr))).

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
    -> forall x r_n', buffer_cons (fst r_n) (snd r_n) x ↝ r_n'
    -> ByteString_list_AbsR (x :: r_o) r_n'.
Proof.
  unfold buffer_cons, Bind2; intros ? ? AbsR ???.
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
    assert (psOffset (snd r_n) = 0) as HA by nomega.
    rewrite HA, <- H6, !N.add_0_r in *; clear HA H6 n.
    setoid_replace (x1 + N.succ i - (x1 + 1) + psBuffer (snd r_n))
      with (psBuffer (snd r_n) + i) by nomega.
    destruct (within_bool _ _ _) eqn:Heqe2; simpl; trivial; nomega.
  prepare_AbsR AbsR.
  reduce_peano i; nomega.
Qed.

Lemma buffer_uncons_sound : forall r_o r_n a,
  ByteString_list_AbsR r_o r_n
    -> buffer_uncons (fst r_n) (snd r_n) ↝ a
    -> ByteString_list_AbsR (match r_o with
                             | [] => r_o
                             | _ :: xs => xs
                             end) (fst a).
Proof.
  unfold buffer_uncons; intros.
  apply refine_computes_to in H0.
  apply refine_If_Then_Else_bool in H0.
  destruct (0 <? psLength (snd r_n)) eqn:Heqe.
    revert H0.
    autorewrite with monad laws; simpl; intros.
    apply computes_to_refine in H0.
    destruct_computations; simpl.
    destruct_AbsR H; construct_AbsR;
    destruct x; try destruct p; simpl in *;
    destruct r_o; simpl in *;
    try nomega; right;
    split; try nomega; split;
    destruct (psLength (snd r_n) =? 1) eqn:Heqe2;
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
    -> buffer_uncons (fst r_n) (snd r_n) ↝ a
    -> snd a = match r_o with
               | [] => None
               | x :: _ => Some x
               end.
Proof.
  unfold buffer_uncons; intros.
  apply refine_computes_to in H0.
  apply refine_If_Then_Else_bool in H0.
  destruct (0 <? psLength (snd r_n)) eqn:Heqe.
    revert H0.
    autorewrite with monad laws; simpl; intros.
    apply computes_to_refine in H0.
    destruct_computations.
    destruct_AbsR H; simpl;
    destruct r_o; simpl in *; try nomega.
    f_equal; tsubst.
    apply H0.
    replace (psBuffer (snd r_n) + psOffset (snd r_n))
       with (psBuffer (snd r_n) + psOffset (snd r_n) + 0) by nomega.
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

Program Definition buffer_append
        (h1 : Rep HeapSpec) (r1 : PS)
        (h2 : Rep HeapSpec) (r2 : PS) :
  Comp (Rep HeapSpec * PS).
Admitted.
  (* `(h, ps) <- *)
  (*   If psLength r2 <? psOffset r1 *)
  (*   Then ret (h, simply_widen_region r (psLength r1)) *)
  (*   Else *)
  (*   If psLength r1 + psLength r2 <=? psBufLen r *)
  (*   Then make_room_by_shifting_up h r alloc_quantum *)
  (*   Else *)
  (*   If 0 <? psBufLen r *)
  (*   Then make_room_by_growing_buffer h r alloc_quantum *)
  (*   Else allocate_buffer h alloc_quantum; *)
  (* poke_at_offset h ps d. *)
(* Obligation 1. nomega_. Defined. *)
(* Obligation 2. nomega_. Defined. *)
(* Obligation 3. nomega_. Defined. *)

Theorem ByteStringHeap (heap : Rep HeapSpec) :
  { adt : _ & refineADT ByteStringSpec adt }.
Proof.
  eexists.

  hone representation using ByteString_list_AbsR.

  {
    simplify with monad laws.
    refine pick val (heap,
                     {| psBuffer := 0
                      ; psBufLen := 0
                      ; psOffset := 0
                      ; psLength := 0 |}).
      finish honing.
    firstorder.
  }

  {
    simplify with monad laws.
    etransitivity.
      eapply (refine_skip2 (dummy:=buffer_cons (fst r_n) (snd r_n) d)).
    etransitivity.
      apply refine_under_bind; intros; simpl.
      set_evars.
      refine pick val a.
        finish honing.
      eapply buffer_cons_sound; eauto.
    simplify with monad laws; simpl.
    finish honing.
  }

  {
    simplify with monad laws.
    etransitivity.
      eapply (refine_skip2 (dummy:=buffer_uncons (fst r_n) (snd r_n))).
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

  {
    (* jww (2016-11-28): [d] is a [list Word] here, when it should be a
       [HeapState * PS]. This is precisely what multi-arity methods will solve
       for us. *)
    simplify with monad laws.
    etransitivity.
    eapply (refine_skip2 (dummy:=buffer_append (fst r_n) (snd r_n)
                                                      (fst r_n0) (snd r_n0))).
      admit.
    (* etransitivity. *)
    (*   apply refine_under_bind; intros; simpl. *)
    (*   pose proof H1. *)
    (*   eapply buffer_uncons_impl in H1; eauto. *)
    (*   rewrite fst_match_list, snd_match_list, <- H1. *)
    (*   refine pick val (fst a). *)
    (*     simplify with monad laws. *)
    (*     rewrite <- surjective_pairing. *)
    (*     finish honing. *)
    (*   eapply buffer_uncons_sound; eauto. *)
    (* simplify with monad laws. *)
    finish honing.
  }

  apply reflexivityT.
Admitted.

End ByteStringHeap.
