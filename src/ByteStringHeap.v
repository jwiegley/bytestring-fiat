Require Import
  ByteString.Tactics
  ByteString.Memory
  ByteString.Nomega
  ByteString.Heap
  ByteString.HeapADT
  ByteString.HeapCanon
  ByteString.ByteString
  ByteString.Fiat
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Generalizable All Variables.

Open Scope N_scope.

Module ByteStringHeap (M : WSfun N_as_DT).

Module Import HeapCanonical := HeapCanonical M.

Import HeapADT.
Import Heap.
Import HeapState.
Import FMapExt.

Record PS := makePS {
  psHeap : Rep HeapSpec;

  psBuffer : Ptr;
  psBufLen : Size;

  psOffset : Size;
  psLength : Size
}.

Definition simply_widen_region (r : PS) : PS :=
  {| psHeap   := psHeap r
   ; psBuffer := psBuffer r
   ; psBufLen := psBufLen r
   ; psOffset := psOffset r - 1
   ; psLength := psLength r + 1 |}.

Program Definition make_room_by_shifting_up (r : PS) (n : N | 0 < n) :
  (* We could maybe be smarter by shifting the block so it sits mid-way within
     the buffer. *)
  Comp PS :=
  res <- memcpy (psHeap r) (psBuffer r) (psBuffer r + n) (psLength r);
  ret {| psHeap   := fst res
       ; psBuffer := psBuffer r
       ; psBufLen := psBufLen r
       ; psOffset := 0
       ; psLength := psLength r + n |}.

Program Definition make_room_by_growing_buffer (r : PS) (n : N | 0 < n) :
  Comp PS :=
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
  Comp PS :=
  `(h, a) <- alloc r len;
  ret {| psHeap   := h
       ; psBuffer := a
       ; psBufLen := len
       ; psOffset := 0
       ; psLength := len |}.

Definition poke_at_offset (r : PS) (d : Word) : Comp PS :=
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

Program Definition buffer_cons (r : PS) (d : Word) : Comp PS :=
  ps <- If 0 <? psOffset r
        Then ret (simply_widen_region r)
        Else If psLength r + alloc_quantum <=? psBufLen r
        Then make_room_by_shifting_up r alloc_quantum
        Else If 0 <? psBufLen r
        Then make_room_by_growing_buffer r alloc_quantum
        Else allocate_buffer (psHeap r) alloc_quantum;
  poke_at_offset ps d.
Obligation 1. nomega. Defined.
Obligation 2. nomega. Defined.
Obligation 3. nomega. Defined.

Definition buffer_uncons (r : PS) : Comp (PS * option Word) :=
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

Definition ByteString_list_AbsR (or : Rep ByteStringSpec) (nr : PS) :=
  length or = N.to_nat (psLength nr) /\
  IF psBufLen nr = 0
  then psOffset nr = 0 /\ psLength nr = 0
  else fits (psBuffer nr) (psBufLen nr)
            (psBuffer nr + psOffset nr) (psLength nr) /\
       M.MapsTo (psBuffer nr) (psBufLen nr) (resvs (psHeap nr)) /\
       (forall i x, i < psLength nr
          -> nth (N.to_nat i) or x = x
          -> M.MapsTo (psBuffer nr + psOffset nr + i) x
                      (bytes (psHeap nr))).

Ltac destruct_AbsR H :=
  let H1 := fresh "H1" in
  let H2 := fresh "H2" in
  destruct H as [H1 H2];
  let H3 := fresh "H3" in
  let H4 := fresh "H4" in
  let data := fresh "data" in
  destruct H2 as [[H [H2 H3]]|[H [H2 [H3 H4]]]];
  [ rewrite ?H, ?H2 in * | ].

Ltac construct_AbsR := split; try split; simpl; try nomega.

Lemma buffer_cons_sound
      (r_o : list Word) (r_n : PS)
      (AbsR : ByteString_list_AbsR r_o r_n) :
  forall x r_n' (H : buffer_cons r_n x ↝ r_n'),
    ByteString_list_AbsR (x :: r_o) r_n'.
Proof.
  unfold buffer_cons; intros.
  apply refine_computes_to in H.
  rewrite refineEquiv_If_Then_Else_Bind in H.
  apply refine_If_Then_Else_bool in H.
  destruct (0 <? psOffset r_n) eqn:Heqe.
    apply computes_to_refine in H.
    {
      destruct_computations; simpl in *.
      destruct_AbsR AbsR; construct_AbsR.
      right; split; trivial; split; [nomega|].
      split; intros;
      destruct_computations; tsubst;
      simpl; trivial.
      simplify_maps.
      destruct i using N.peano_ind.
        left; nomega.
      right; split; [nomega|].
      rewrite <- N.add_assoc.
      rewrite <- N.add_sub_swap; [|nomega].
      rewrite <- N.add_sub_assoc; [|nomega].
      rewrite N.add_assoc.
      apply H4; [nomega|].
      rewrite N2Nat.inj_sub.
      replace (N.to_nat 1) with 1%nat; [|nomega].
      simpl; rewrite N2Nat.inj_succ in *; simpl.
      rewrite Nat.sub_0_r; assumption.
    }
  assert (psOffset r_n = 0) by nomega; clear Heqe.
  rewrite refineEquiv_If_Then_Else_Bind in H.
  apply refine_If_Then_Else_bool in H.
  destruct (psLength r_n + alloc_quantum <=? psBufLen r_n) eqn:Heqe2;
  [| rewrite refineEquiv_If_Then_Else_Bind in H;
     destruct (0 <? psBufLen r_n) eqn:Heqe3; simpl in H ];
  apply computes_to_refine in H; revert H;
  unfold make_room_by_shifting_up, make_room_by_growing_buffer,
         allocate_buffer, poke_at_offset;
  autorewrite with monad laws; simpl;
  rewrite ?N.add_0_r.
  - simpl; intros; destruct_computations;
    destruct_AbsR AbsR; construct_AbsR;
    (right; split; [nomega|]; split; [nomega|]).
    rewrite H0, N.add_0_r in *; clear H0;
    tsubst; simpl in *; subst.
    destruct (psLength r_n =? 0) eqn:Heqe.
      assert (psLength r_n = 0) by nomega.
      rewrite H in *; clear H.
      split; trivial.
      intros; simplify_maps.
      destruct i using N.peano_ind.
        left; nomega.
      nomega.
    split; trivial.
    intros; simplify_maps.
    destruct i using N.peano_ind.
      left; nomega.
    right; split; [nomega|].
    rewrite N2Nat.inj_succ in *; simpl.
    apply copy_bytes_mapsto.
    destruct (within_bool (psBuffer r_n + 1) (psLength r_n)
                          (psBuffer r_n + N.succ i)) eqn:Heqe1; simpl.
      replace (psBuffer r_n + N.succ i - (psBuffer r_n + 1) + psBuffer r_n)
         with (psBuffer r_n + i) by nomega.
      apply H4; trivial.
      nomega.
    nomega.
  - simpl; intros; destruct_computations;
    destruct_AbsR AbsR; construct_AbsR;
    (right; split; [nomega|]; split; [nomega|]).
    rewrite H0, N.add_0_r in *; clear H0;
    tsubst; simpl in *.
    split.
      simplify_maps.
      split.
        apply_for_all; relational.
        nomega.
      simplify_maps.
    intros.
    simplify_maps.
    destruct i using N.peano_ind.
      left; nomega.
    right; split; [nomega|].
    rewrite N2Nat.inj_succ in *; simpl.
    apply copy_bytes_mapsto.
    destruct (within_bool (x0 + 1) (psLength r_n)
                          (x0 + N.succ i)) eqn:Heqe1; simpl.
      replace (x0 + N.succ i - (x0 + 1) + psBuffer r_n)
         with (psBuffer r_n + i) by nomega.
      apply H4; trivial.
      nomega.
    nomega.
  - simpl; intros; destruct_computations;
    destruct_AbsR AbsR; construct_AbsR;
    (right; split; [nomega|]; split; [nomega|]).
    destruct_computations; tsubst; simpl in *.
    rewrite ?N.add_0_r in *; simpl.
    split.
      simplify_maps.
    intros.
    simplify_maps.
    destruct i using N.peano_ind.
      left; nomega.
    right; split; [nomega|].
    rewrite N2Nat.inj_succ in *; simpl.
    nomega.
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
    destruct (psLength r_n =? 1) eqn:Heqe2;
    try nomega;
    try (eexists; split; [exact H4|]; nomega).
    split.
      assumption.
    intros.
    destruct i using N.peano_ind.
      rewrite N.add_0_r, N.add_assoc.
      apply H4; trivial.
      nomega.
    replace (psBuffer r_n + (psOffset r_n + 1) + N.succ i)
       with (psBuffer r_n + psOffset r_n + (N.succ i + 1)) by nomega.
    apply H4.
      nomega.
    rewrite N.add_succ_l.
    rewrite N2Nat.inj_succ in *; simpl.
    rewrite N2Nat.inj_add, Nat.add_1_r.
    assumption.
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
    replace (psBuffer r_n + psOffset r_n)
       with (psBuffer r_n + psOffset r_n + 0) by nomega.
    apply H4; trivial.
    nomega.
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

Section Refined.

Variable heap : Rep HeapSpec.

Theorem ByteStringHeap  : { adt : _ & refineADT ByteStringSpec adt }.
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
    split; simpl; auto.
    left; auto.
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
    unfold buffer_cons, simply_widen_region,
           make_room_by_shifting_up, make_room_by_growing_buffer.
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
    unfold buffer_uncons.
    finish honing.
  }
  apply reflexivityT.
Defined.

End Refined.

End ByteStringHeap.