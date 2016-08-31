Require Import
  Coq.Lists.List
  Coq.Arith.Arith
  Coq.NArith.NArith
  Fiat.ADT
  Fiat.ADTNotation
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements
  ByteString.ADTInduction
  ByteString.BindDep
  ByteString.ByteString
  ByteString.Heap
  ByteString.HeapADT
  ByteString.Nomega
  ByteString.Relations
  ByteString.Tactics
  ByteString.TupleEnsembles
  ByteString.Within.

Generalizable All Variables.

Module ByteStringHeap (Mem : Memory).

Module Import BS := ByteString Mem.
Module Import Adt := HeapADT Mem.
Import Heap.

Open Scope N_scope.

Definition HSpec := projT1 HeapSpecADT.

Definition memcpy' (r : Rep HSpec) (addr : N) (addr2 : N) (len : N) :
  Comp (Rep HSpec * unit) :=
  Eval simpl in callMeth HSpec memcpyS r addr addr2 len.

Definition alloc' (r : Rep HSpec) (len : N | 0 < len) :
  Comp (Rep HSpec * N) :=
  Eval simpl in callMeth HSpec allocS r len.

Definition free' (r : Rep HSpec) (addr : N) : Comp (Rep HSpec * unit) :=
  Eval simpl in callMeth HSpec freeS r addr.

Definition realloc' (r : Rep HSpec) (addr : N) (len : N | 0 < len) :
  Comp (Rep HSpec * N) :=
  Eval simpl in callMeth HSpec reallocS r addr len.

Definition peek' (r : Rep HSpec) (addr : N) :
  Comp (Rep HSpec * Mem.Word8) :=
  Eval simpl in callMeth HSpec peekS r addr.

Definition poke' (r : Rep HSpec) (addr : N) (w : Mem.Word8) :
  Comp (Rep HSpec * unit) :=
  Eval simpl in callMeth HSpec pokeS r addr w.

Record PS := makePS {
  psHeap : Rep HSpec;

  psBuffer : N;
  psBufLen : N;

  psOffset : N;
  psLength : N
}.

Definition poke_at_offset (r : PS) (d : Mem.Word8) : Comp PS :=
  res <- poke' (psHeap r) (psBuffer r + psOffset r) d;
  ret {| psHeap   := fst res
       ; psBuffer := psBuffer r
       ; psBufLen := psBufLen r
       ; psOffset := psOffset r
       ; psLength := psLength r |}.

Definition simply_widen_region (r : PS) : PS :=
  {| psHeap   := psHeap r
   ; psBuffer := psBuffer r
   ; psBufLen := psBufLen r
   ; psOffset := psOffset r - 1
   ; psLength := psLength r + 1 |}.

Ltac competing_lookups R H A1 H0 A2 :=
  let Heqe := fresh "Heqe" in
  destruct (A1 =? A2) eqn:Heqe;
    [ apply Neqb_ok in Heqe; subst;
      pose proof (allocations_unique (proj2_sig R) _ _ H _ H0);
      subst; try nomega
    | apply N.eqb_neq in Heqe;
      pose proof (allocations_no_overlap (proj2_sig R) _ H _ H0 Heqe);
      try nomega ].

Ltac resolve_contention :=
  match goal with
  | [ H : All _ ?R, H0 : Lookup ?A ?B ?R |- _ ] => destruct (H A B)
  end.

Lemma refine_local_memcpy heap addr size len data :
  fromADT HeapSpec heap ->
  (0 < len -> fits addr size (addr + 1) len) ->
  Lookup addr {| memSize := size; memData := data |} heap ->
  refine
    (ret (If 0 <? len
          Then Update addr
            {| memSize := size
             ; memData :=
                 Union _ (KeepKeys (not ∘ within 1 len) data)
                         (ShiftKeys 0 1 (KeepKeys (within 0 len)
                                                  data)) |}
            heap
          Else heap, tt))
    (memcpy heap addr (addr + 1) len).
Proof.
  unfold memcpy; intro HH; intros.
  unfold IfDec_Then_Else; simpl.
  intros ??.
  destruct (0 <? len) eqn:Heqe; simpl;
  destruct_computations;
  [|repeat teardown; intuition];
  assert (H9 : 0 < len) by nomega; intuition.
  destruct x, x0;
  try destruct p;
  try destruct p0.
  - destruct H1, H2.
    competing_lookups (exist _ heap HH) H n H2 n0;
    competing_lookups (exist _ heap HH) H0 addr H2 n0.
    replace (n0 - n0) with 0 by nomega.
    replace (n0 + 1 - n0) with 1 by nomega.
    constructor.
  - destruct H1.
    competing_lookups (exist _ heap HH) H0 addr H n.
    resolve_contention; auto.
  - destruct H2.
    competing_lookups (exist _ heap HH) H0 addr H n.
    resolve_contention; auto; nomega.
  - resolve_contention; auto.
Qed.

Program Definition make_room_by_shifting_up (r : PS) (n : N | 0 < n) :
  Comp PS :=
  res <- memcpy' (psHeap r) (psBuffer r) (psBuffer r + n) (psLength r);
  ret {| psHeap   := fst res
       ; psBuffer := psBuffer r
       ; psBufLen := psBufLen r
       ; psOffset := 0
       ; psLength := psLength r + n |}.

Program Definition make_room_by_growing_buffer (r : PS) (n : N | 0 < n) :
  Comp PS :=
  (* jww (2016-06-28): We can make a trade-off here by allocating extra bytes
     in anticipation of future calls to [buffer_cons]. *)
  `(h, a) <- alloc' (psHeap r) (psLength r + n);
  `(h, _) <- memcpy' h (psBuffer r) (a + n) (psLength r);
  `(h, _) <- free' h (psBuffer r);
  ret {| psHeap   := h
       ; psBuffer := a
       ; psBufLen := psLength r + n
       ; psOffset := 0
       ; psLength := psLength r + n |}.
Obligation 1. nomega. Qed.

Program Definition allocate_buffer (r : Rep HSpec) (len : N | 0 < len) :
  Comp PS :=
  `(h, a) <- alloc' r len;
  ret {| psHeap   := h
       ; psBuffer := a
       ; psBufLen := len
       ; psOffset := 0
       ; psLength := len |}.

Definition alloc_quantum := 1.
Arguments alloc_quantum /.

Program Definition buffer_cons (r : PS) (d : Mem.Word8) : Comp PS :=
  ps <- If 0 <? psOffset r
        Then ret (simply_widen_region r)
        Else If psLength r <? psBufLen r
        Then make_room_by_shifting_up r alloc_quantum
        Else If 0 <? psBufLen r
        Then make_room_by_growing_buffer r alloc_quantum
        Else allocate_buffer (psHeap r) alloc_quantum;
  poke_at_offset ps d.
Obligation 1. nomega. Qed.
Obligation 2. nomega. Qed.
Obligation 3. nomega. Qed.

Definition buffer_uncons (r : PS) : Comp (PS * option Mem.Word8) :=
  If psOffset r <? psLength r
  Then (
    w <- peek' (psHeap r) (psBuffer r + psOffset r);
    ret ({| psHeap   := psHeap r
          ; psBuffer := psBuffer r
          ; psBufLen := psBufLen r
          ; psOffset := if psLength r - 1 =? 0
                        then 0
                        else psOffset r + 1
          ; psLength := psLength r - 1 |}, Some (snd w)))
  Else ret (r, None).

Definition ByteString_list_AbsR (or : Rep ByteStringSpec) (nr : PS) :=
  length or = N.to_nat (psLength nr) /\
  IF psBufLen nr = 0
  then psOffset nr = 0 /\ psLength nr = 0
  else
    fits (psBuffer nr) (psBufLen nr)
         (psBuffer nr + psOffset nr) (psLength nr) /\
    exists data,
      Lookup (psBuffer nr) {| memSize := psBufLen nr; memData := data |}
             (` (psHeap nr)) /\
      (forall i x, i < psLength nr
                     -> nth (N.to_nat i) or x = x
                     -> Lookup (psOffset nr + i) x data).

Ltac destruct_AbsR H :=
  let H1 := fresh "H1" in
  let H2 := fresh "H2" in
  destruct H as [H1 H2];
  let H3 := fresh "H3" in
  let H4 := fresh "H4" in
  let data := fresh "data" in
  destruct H2 as [[H [H2 H3]]|[H [H2 [data [H3 H4]]]]];
  [ rewrite ?H, ?H2 in * | ].

Ltac construct_AbsR :=
  split; try split; simpl; try nomega.

Lemma simply_within : forall n m A (P Q : A),
  0 < m -> IfDec within n m n Then P Else Q = P.
Proof. intros; decisions; auto; nomega. Qed.

Theorem buffer_cons_sound
        (r_o : list Mem.Word8) (r_n : PS)
        (AbsR : ByteString_list_AbsR r_o r_n) :
  forall x r_n' (H : buffer_cons r_n x ↝ r_n'),
    ByteString_list_AbsR (x :: r_o) r_n'.
Proof.
  unfold buffer_cons; intros.
  apply refine_computes_to_ret in H.
  rewrite refineEquiv_If_Then_Else_Bind in H.
  apply refine_If_Then_Else_bool in H.
  destruct (0 <? psOffset r_n) eqn:Heqe.
    apply refine_computes_to_ret in H.
    {
      destruct_computations; simpl.
      destruct_AbsR AbsR; construct_AbsR.
      right; intuition; [nomega|].
      exists (Update (psOffset r_n - 1) x data).
      split; intros; teardown.
        destruct_computations; tsubst; teardown.
        exists {| memSize := psBufLen r_n; memData := data |}; simpl.
        decisions; intuition.
          f_equal; f_equal; nomega.
        destruct H2; nomega.
      destruct i using N.peano_ind.
        left; nomega.
      right; split; [nomega|].
      rewrite <- N.add_sub_swap; [|nomega].
      rewrite <- N.add_sub_assoc; [|nomega].
      apply H4; [nomega|].
      rewrite N2Nat.inj_sub.
      replace (N.to_nat 1) with 1%nat; [|nomega].
      simpl; rewrite N2Nat.inj_succ in *; simpl.
      rewrite Nat.sub_0_r; assumption.
    }
  assert (psOffset r_n = 0) by nomega; clear Heqe.
  rewrite refineEquiv_If_Then_Else_Bind in H.
  apply refine_If_Then_Else_bool in H.
  destruct (psLength r_n <? psBufLen r_n) eqn:Heqe2;
  [| rewrite refineEquiv_If_Then_Else_Bind in H;
     destruct (0 <? psBufLen r_n) eqn:Heqe3; simpl in H ];
  apply refine_computes_to_ret in H; revert H;
  unfold make_room_by_shifting_up, make_room_by_growing_buffer,
         allocate_buffer, poke_at_offset;
  autorewrite with monad laws; simpl;
  rewrite ?N.add_0_r;
  unfold memcpy', alloc', free', poke';
  rewrite refine_bind_dep_bind_ret; simpl;
  repeat setoid_rewrite refine_bind_dep_bind_ret;
  simpl; intros; destruct_computations;
  destruct_AbsR AbsR; construct_AbsR;
  (right; split; [nomega|]; split; [nomega|]).
  - eapply refine_local_memcpy in x1; eauto;
    [|exact (proj2_sig (psHeap r_n))|];
    destruct (0 <? psLength r_n) eqn:Heqe;
    try nomega; destruct x1, x3; simpl in *.
      eexists.
      split.
        teardown.
        exists {| memSize := psBufLen r_n
                ; memData :=
                    Union _ (KeepKeys (not ∘ within 1 (psLength r_n)) data)
                            (ShiftKeys 0 1 (KeepKeys (within 0 (psLength r_n))
                                                     data)) |}.
        split.
          rewrite simply_within; nomega.
        teardown.
      intros; teardown.
      destruct i using N.peano_ind.
        left; nomega.
      right; split; [nomega|]; clear IHi.
      simpl; rewrite N2Nat.inj_succ in *; simpl.
      rewrite H0 in H4; simpl in H4.
      unfold KeepKeys, ShiftKeys; teardown.
      destruct (within_dec 0 (N.succ (psLength r_n)) (N.succ i)).
        right; teardown.
        exists (i, x0); simpl.
        split.
          f_equal; nomega.
        assert (i < psLength r_n) by nomega.
        specialize (H4 _ _ H6 H5).
        teardown; intuition.
        nomega.
      left; teardown.
      split.
        apply H4; [nomega|].
        rewrite N2Nat.inj_succ, nth_overflow; trivial.
        nomega.
      unfold not, compose; intros.
      contradiction n.
      nomega.
    eexists.
    split.
      teardown.
      exists {| memSize := psBufLen r_n; memData := data |}.
      split; auto.
      rewrite simply_within; nomega.
    intros; teardown.
    destruct i using N.peano_ind.
      left; nomega.
    right; split; [nomega|].
    rewrite H0 in H4; simpl in H4; apply H4; [nomega|].
    simpl; rewrite N2Nat.inj_succ in *; simpl.
    destruct r_o; simpl in *; auto; nomega.
  - unfold alloc, FindFreeBlock in x1.
    unfold free in x5.
    revert x3.
    destruct_computations; simpl in *; intros.
    pose proof (H _ _ H3); simpl in *.
    rewrite H0, ?N.add_0_r in *; simpl in *.
    destruct (psLength r_n =? 0) eqn:Heqe.
      apply Neqb_ok in Heqe.
      rewrite Heqe in *; clear Heqe; simpl.
      exists (Update 0 x Empty);
      split; repeat teardown; subst; simpl; try nomega.
    assert (0 <? psLength r_n = true) by nomega.
    exists (Update
              0 x (ShiftKeys
                     0 1 (KeepKeys (within 0 (psLength r_n)) data))); split.
      teardown.
      exists {| memSize := psLength r_n + 1
              ; memData :=
                  ShiftKeys 0 1 (KeepKeys (within 0 (psLength r_n)) data) |}.
      replace (x1 - x1) with 0 by nomega.
      rewrite simply_within; simpl; [|nomega]; split; auto.
      admit.
    destruct i using N.peano_ind;
    simpl in *; intros; subst; teardown.
    right; split; [nomega|].
    unfold ShiftKeys, KeepKeys.
    teardown; exists (i, x0); split; simpl.
      f_equal; nomega.
    teardown.
    split.
      apply H4.
        nomega.
      rewrite N2Nat.inj_succ in *; simpl.
      assumption.
    nomega.
  - unfold alloc, FindFreeBlock in x1.
    destruct_computations; simpl in *.
    rewrite H3, ?N.add_0_r in *; simpl.
    repeat teardown; subst; simpl; try nomega;
    exists (Update 0 x Empty);
    split; repeat teardown;
    try exists {| memSize := 1; memData := Empty |};
    try split; repeat teardown;
    decisions; simpl; auto;
    replace (x1 - x1) with 0 by nomega; auto;
    try nomega; simpl; intros;
    try (destruct i using N.peano_ind; simpl in *; subst;
         [ teardown | nomega ]).
Admitted.

Lemma refine_ret_eq_r : forall A (a b : A), refine (ret a) (ret b) -> a = b.
Proof.
  intros.
  specialize (H b (ReturnComputes b)).
  apply Return_inv; assumption.
Qed.

Lemma nth_plus_one : forall A (x : A) xs e off,
  (0 < off)%nat -> nth off (x :: xs) e = nth (off - 1) xs e.
Proof.
  intros.
  destruct off.
    nomega.
  simpl.
  rewrite Nat.sub_0_r.
  reflexivity.
Qed.

Theorem buffer_uncons_sound : forall r_o r_n a,
  ByteString_list_AbsR r_o r_n
    -> buffer_uncons r_n ↝ a
    -> ByteString_list_AbsR (match r_o with
                             | [] => r_o
                             | _ :: xs => xs
                             end) (fst a).
Proof.
  unfold buffer_uncons; intros.
  apply refine_computes_to_ret in H0.
  apply refine_If_Then_Else_bool in H0.
(*
  destruct (psOffset r_n <? psLength r_n) eqn:Heqe.
    revert H0.
    unfold peek'.
    rewrite refine_bind_dep_bind_ret; simpl.
    rewrite refine_bind_dep_ignore.
    unfold peek, FindBlockThatFits.
    autorewrite with monad laws; simpl; intros.
    apply refine_computes_to_ret in H0.
    destruct_computations.
    destruct_AbsR H; construct_AbsR;
    destruct x; try destruct p; simpl in *;
    destruct r_o; simpl in *;
    try nomega; right;
    split; try nomega;
    split; try nomega.
      admit.
    (eexists;
     split; [exact H4|];
     intros;
     rewrite <- N.add_assoc;
     apply H5;
     [ apply N.lt_add_lt_sub_l
     | rewrite N.add_1_l, N2Nat.inj_succ ];
     trivial).
  apply refine_computes_to_ret in H0.
  destruct_computations.
  destruct_AbsR H; construct_AbsR;
  destruct r_o; simpl in *; auto; try nomega.
  - left; intuition.
  - 
  - right; intuition.
    eexists; intuition.
      exact H3.
    apply H4; auto.
    destruct r_o; simpl in *; auto.
  nomega.
*)
Admitted.

Theorem buffer_uncons_impl : forall r_o r_n a,
  ByteString_list_AbsR r_o r_n
    -> buffer_uncons r_n ↝ a
    -> snd a = match r_o with
               | [] => None
               | x :: _ => Some x
               end.
Proof.
  unfold buffer_uncons; intros.
  apply refine_computes_to_ret in H0.
  apply refine_If_Then_Else_bool in H0.
  destruct (psOffset r_n <? psLength r_n) eqn:Heqe.
    revert H0.
    unfold peek'.
    rewrite refine_bind_dep_bind_ret; simpl.
    rewrite refine_bind_dep_ignore.
    unfold peek, FindBlockThatFits.
    autorewrite with monad laws; simpl; intros.
    apply refine_computes_to_ret in H0.
    destruct_computations.
    destruct_AbsR H; simpl.
      destruct r_o; simpl in *; nomega.
    destruct r_o; simpl in *.
      nomega.
    f_equal.
    destruct x; tsubst; simpl in *.
      destruct p.
      specialize (H1 w _ _ eq_refl); simpl in *.
      apply H1.
      destruct H0.
      competing_lookups (psHeap r_n) H4 (psBuffer r_n) H0 n.
      simpl in *.
      replace (psBuffer r_n + psOffset r_n - psBuffer r_n)
         with (psOffset r_n + 0) by nomega.
      apply H5; nomega.
    resolve_contention; trivial; nomega.
  apply refine_computes_to_ret in H0.
  apply Return_inv in H0.
  destruct a; tsubst; simpl in *.
  destruct r_o; simpl in *;
  destruct H, H0; auto.
    destruct H0, H1.
    rewrite H2 in H; simpl in H.
    discriminate.
  (* nomega. *)
Admitted.

Lemma fst_match_list :
  forall A (xs : list A) B z C z'
         (f : A -> list A -> B) (f' : A -> list A -> C),
    fst match xs with
        | [] => (z, z')
        | x :: xs => (f x xs, f' x xs)
        end = match xs with
              | [] => z
              | x :: xs => f x xs
              end.
Proof. induction xs; auto. Qed.

Lemma snd_match_list :
  forall A (xs : list A) B z C z'
         (f : A -> list A -> B) (f' : A -> list A -> C),
    snd match xs with
        | [] => (z, z')
        | x :: xs => (f x xs, f' x xs)
        end = match xs with
              | [] => z'
              | x :: xs => f' x xs
              end.
Proof. induction xs; auto. Qed.

Section Refined.

Variable heap : Rep HSpec.

Lemma ByteStringHeap  : { adt : _ & refineADT ByteStringSpec adt }.
Proof.
  eexists.
  hone representation using ByteString_list_AbsR.
  {
    simplify with monad laws.
    refine pick val
      {| psHeap   := heap
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
      rewrite fst_match_list, snd_match_list.
      rewrite <- H1.
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

Definition ByteStringHeap' := Eval simpl in projT1 ByteStringHeap.
Print ByteStringHeap'.

End Refined.

End ByteStringHeap.
