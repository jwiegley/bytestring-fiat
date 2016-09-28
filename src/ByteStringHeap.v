Require Import
  ByteString.Lib.Tactics
  ByteString.Lib.Nomega
  ByteString.Lib.Fiat
  ByteString.Memory
  ByteString.Heap
  ByteString.HeapCanon
  ByteString.ByteString
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx
  Hask.Control.Applicative
  Hask.Control.Monad.

Module ByteStringHeap (M : WSfun N_as_DT).

Module Import HeapCanonical := HeapCanonical M.

Import Heap.
Import HeapState.
Import FMapExt.

Open Scope N_scope.

Section ByteStringHeap.

Context `{Monad m}.
Context `{Alternative m}.
Context `{Computable m}.

Record PS (heapType : Type) := makePS {
  psHeap : heapType;

  psBuffer : Ptr;
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
  Comp (PSH * m unit) :=
  `(h, mres) <- memcpy (psHeap r) (psBuffer r) (psBuffer r + n) (psLength r);
  ret (if m_computes_to mres
       then {| psHeap   := h
             ; psBuffer := psBuffer r
             ; psBufLen := psBufLen r
             ; psOffset := 0
             ; psLength := psLength r + n |}
       else r, mres).

Program Definition make_room_by_growing_buffer (r : PSH) (n : N | 0 < n) :
  Comp (PSH * m unit) :=
  (* We can make a trade-off here by allocating extra bytes in anticipation of
     future calls to [buffer_cons]. *)
  `(h, ma) <- alloc (psHeap r) (psLength r + n);
  Ifopt m_computes_to ma as a
  Then (
    `(h, mres) <- memcpy h (psBuffer r) (a + n) (psLength r);
    if m_computes_to mres
    then (
      `(h, mres) <- free h (psBuffer r);
      ret (if m_computes_to mres
           then {| psHeap   := h
                 ; psBuffer := a
                 ; psBufLen := psLength r + n
                 ; psOffset := 0
                 ; psLength := psLength r + n |}
           else r, mres)
    )
    else ret (r, mres)
  )
  Else ret (r, fmap (const tt) ma).
Obligation 1. nomega. Defined.

Program Definition allocate_buffer (r : Rep HeapSpec) (len : N | 0 < len) :
  Comp (PSH * m unit) :=
  `(h, ma) <- alloc r len;
  ret (Ifopt m_computes_to ma as a
       Then {| psHeap   := h
             ; psBuffer := a
             ; psBufLen := len
             ; psOffset := 0
             ; psLength := len |}
       Else makePS r 0 0 0 0, tt <$ ma).

Definition poke_at_offset (r : PSH) (d : Word) : Comp (PSH * m unit) :=
  `(h, mres) <- poke (psHeap r) (psBuffer r + psOffset r) d;
  ret (if m_computes_to mres
       then {| psHeap   := h
             ; psBuffer := psBuffer r
             ; psBufLen := psBufLen r
             ; psOffset := psOffset r
             ; psLength := psLength r |}
       else r, mres).

(* This defines how much a buffer is grown by when more space is needed to
   [cons] on a new element. *)
Definition alloc_quantum := 1.
Arguments alloc_quantum /.

Program Definition buffer_cons (r : PSH) (d : Word) : Comp (PSH * m unit) :=
  `(ps, mres) <-
     If 0 <? psOffset r
     Then ret (simply_widen_region r, pure tt)
     Else If psLength r + alloc_quantum <=? psBufLen r
          Then make_room_by_shifting_up r alloc_quantum
          Else If 0 <? psBufLen r
               Then make_room_by_growing_buffer r alloc_quantum
               Else allocate_buffer (psHeap r) alloc_quantum;
  if m_computes_to mres
  then poke_at_offset ps d      (* need to plumb mres through here *)
  else ret (r, mres).
Obligation 1. nomega. Defined.
Obligation 2. nomega. Defined.
Obligation 3. nomega. Defined.

Definition buffer_uncons (r : PSH) : Comp (PSH * m (option Word)) :=
  If 0 <? psLength r
  Then (
    `(r', mw) <- peek (psHeap r) (psBuffer r + psOffset r);
    ret ({| psHeap   := psHeap r
          ; psBuffer := psBuffer r
          ; psBufLen := psBufLen r
          ; psOffset := if psLength r =? 1
                        then 0
                        else psOffset r + 1
          ; psLength := psLength r - 1 |}, fmap Some mw))
  Else ret (r, pure None).

Definition ByteString_list_AbsR (or : Rep ByteStringSpec) (nr : PSH) :=
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

Local Ltac breakdown :=
  repeat (
    destruct_computations; simpl in *;
    computes_to_inv; try tsubst; simpl in *;
    match goal with
      [ H : option _ |- _ ] => destruct H; simpl in *
    end;
    computes_to_inv; try tsubst; simpl in *).

Lemma buffer_cons_sound : forall r_o r_n,
  ByteString_list_AbsR r_o r_n
    -> forall x r_n' mu, buffer_cons r_n x ↝ (r_n', mu)
    -> if m_computes_to mu
       then ByteString_list_AbsR (x :: r_o) r_n'
       else ByteString_list_AbsR r_o r_n'.
Proof.
  unfold buffer_cons; intros ? ? AbsR ????.
  apply refine_computes_to in H2.
  unfold Bind2 in H2.
  rewrite refineEquiv_If_Then_Else_Bind in H2.
  apply refine_If_Then_Else_bool in H2.
  destruct (0 <? psOffset r_n) eqn:Heqe.
    revert H2.
    rewrite refineEquiv_bind_unit; simpl.
    destruct (m_computes_to ((pure[ m]) ())) eqn:Heqe2;
    simpl; intros;
    apply computes_to_refine in H2;
    computes_to_inv; tsubst.
      unfold poke_at_offset, Bind2 in H2.
      computes_to_inv.
      destruct (m_computes_to (snd v)) eqn:Heqe3;
      simpl in *;
      computes_to_inv; tsubst.
        destruct u0.
        rewrite Heqe3.
        admit.
      rewrite Heqe3.
      admit.
    rewrite Heqe2.
    assumption.
(*
    apply computes_to_refine in H2.
    {
      destruct_AbsR AbsR; construct_AbsR.
        breakdown; try nomega.
        unfold poke_at_offset, Bind2 in H2.
        simpl in *.
        computes_to_inv; subst; simpl in *.
        destruct (m_computes_to ((pure[m]) ())); simpl in *.
          computes_to_inv; subst; simpl in *.
          destruct (m_computes_to (snd v)); simpl in *.
            computes_to_inv; tsubst; simpl in *.
            nomega.
          computes_to_inv; tsubst; simpl in *.
          nomega.
        computes_to_inv; tsubst; simpl in *.
*)
(*
        nomega.
        discriminate.
      right; split.
        breakdown; nomega.
      split; intros; simpl.
        breakdown; nomega.
      split; intros.
        breakdown; nomega.
      breakdown.
      - inversion H13; simpl in *; clear H13.
        revert H9.
        subst; simpl in *; intros.
        simplify_maps.
        destruct i using N.peano_ind.
          left; nomega.
        right; split; [nomega|].
        rewrite <- N.add_assoc.
        rewrite <- N.add_sub_swap; [|nomega].
        rewrite <- N.add_sub_assoc; [|nomega].
        rewrite N.add_assoc.
        apply H7; [nomega|].
        rewrite N2Nat.inj_sub.
        replace (N.to_nat 1) with 1%nat; [|nomega].
        simpl; rewrite N2Nat.inj_succ in *; simpl.
        rewrite Nat.sub_0_r; assumption.
      - admit.
      - admit.
      - admit.
      - admit.
    }
  assert (psOffset r_n = 0) by nomega; clear Heqe.
  rewrite refineEquiv_If_Then_Else_Bind in H2.
  apply refine_If_Then_Else_bool in H2.
  destruct (psLength r_n + alloc_quantum <=? psBufLen r_n) eqn:Heqe2;
  [| rewrite refineEquiv_If_Then_Else_Bind in H2;
     destruct (0 <? psBufLen r_n) eqn:Heqe3; simpl in H2 ];
  apply computes_to_refine in H2; revert H2;
  unfold make_room_by_shifting_up, make_room_by_growing_buffer,
         allocate_buffer, poke_at_offset;
  autorewrite with monad laws; simpl;
  rewrite ?N.add_0_r.
  admit.
  admit.
  admit.
(*
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
    rewrite N2Nat.inj_succ in *; nomega.
*)
*)
Admitted.

Lemma buffer_uncons_sound : forall r_o r_n a,
  ByteString_list_AbsR r_o r_n
    -> forall mp, buffer_uncons r_n ↝ (a, mp)
    -> forall p, m_computes_to mp = Some p
    -> ByteString_list_AbsR (match r_o with
                             | [] => r_o
                             | _ :: xs => xs
                             end) a.
Proof.
  unfold buffer_uncons; intros.
  apply refine_computes_to in H3.
  apply refine_If_Then_Else_bool in H3.
  destruct (0 <? psLength r_n) eqn:Heqe.
    revert H3.
    unfold peek, Bind2, conditionally.
    rewrite refineEquiv_bind_bind; intros.
    apply computes_to_refine in H3.
    destruct_computations; simpl.
    admit.
(*
    destruct_AbsR H; construct_AbsR;
    destruct x; try destruct p; simpl in *;
    destruct r_o; simpl in *;
    try nomega; right;
    split; try nomega; split;
    destruct (psLength r_n =? 1) eqn:Heqe2;
    try nomega;
    try (eexists; split; [exact H4|]; nomega).
    split; trivial; intros.
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
    rewrite N2Nat.inj_add, Nat.add_1_r; trivial.
*)
  apply computes_to_refine in H3.
(*
  breakdown.
  destruct_AbsR H; construct_AbsR;
  destruct r_o; simpl in *; auto; try nomega.
    left; intuition.
  right; intuition.
*)
Admitted.

Lemma buffer_uncons_impl : forall r_o r_n a,
  ByteString_list_AbsR r_o r_n
    -> forall mp, buffer_uncons r_n ↝ (a, mp)
    -> forall p, m_computes_to mp = Some p
    -> p = match r_o with
               | [] => None
               | x :: _ => Some x
               end.
Proof.
  unfold buffer_uncons; intros.
  apply refine_computes_to in H3.
  apply refine_If_Then_Else_bool in H3.
  destruct (0 <? psLength r_n) eqn:Heqe.
    revert H3.
    unfold peek, Bind2, conditionally.
    rewrite refineEquiv_bind_bind; intros.
    apply computes_to_refine in H3.
    destruct_computations.
    admit.
(*
    destruct_AbsR H; simpl;
    destruct r_o; simpl in *; try nomega.
    f_equal; tsubst.
    apply H0.
    replace (psBuffer r_n + psOffset r_n)
       with (psBuffer r_n + psOffset r_n + 0) by nomega.
    apply H4; trivial.
    nomega.
*)
  apply computes_to_refine in H3.
  apply Return_inv in H3.
  destruct a; tsubst; simpl in *.
(*
  destruct r_o; simpl in *;
  destruct H, H0; auto
    destruct H0, H1.
    rewrite H2 in H; simpl in H.
    discriminate.
  nomega.
*)
Admitted.

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
      destruct a.
      refine pick val m0; auto.
      simplify with monad laws; simpl.
      refine pick val p.
        simplify with monad laws.
        finish honing.
      pose proof (buffer_cons_sound H3 H4).
      destruct (m_computes_to m0) eqn:Heqe; auto.
    simplify with monad laws; simpl.
    finish honing.
  }

  {
    simplify with monad laws.
    etransitivity.
      eapply (refine_skip2 (dummy:=buffer_uncons r_n)).
    etransitivity.
      apply refine_under_bind; intros; simpl.
      destruct a.
      refine pick val (tt <$ m0); auto.
        simplify with monad laws.
        pose proof H4.
        eapply buffer_uncons_impl in H4; eauto.
        (* rewrite fst_match_list, snd_match_list, <- H4. *)
        refine pick val p.
          simplify with monad laws.
          (* rewrite <- surjective_pairing. *)
          (* finish honing. *)
          admit.
        (* eapply buffer_uncons_sound; eauto. *)
        admit.
      admit.
    simplify with monad laws.
    finish honing.
  }

  apply reflexivityT.
Admitted.

End ByteStringHeap.

End ByteStringHeap.
