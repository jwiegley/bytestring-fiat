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

Lemma refine_local_memcpy (r : PS) data :
  (0 < psLength r
     -> fits (psBuffer r) (psBufLen r) (psBuffer r + 1) (psLength r)) ->
  Lookup (psBuffer r) {| memSize := psBufLen r
                       ; memData := data |} (` (psHeap r)) ->
  refine
    (ret (If 0 <? psLength r
          Then Update (psBuffer r)
            {| memSize := psBufLen r
             ; memData :=
                 Union _ (KeepKeys (not ∘ within 1 (psLength r)) data)
                         (ShiftKeys 0 1 (KeepKeys (within 0 (psLength r))
                                                  data)) |}
            (` (psHeap r))
          Else ` (psHeap r), tt))
    (memcpy (` (psHeap r)) (psBuffer r) (psBuffer r + 1) (psLength r)).
Proof.
  unfold memcpy; intros.
  unfold IfDec_Then_Else; simpl.
  intros ??.
  destruct (0 <? psLength r) eqn:Heqe; simpl;
  apply Bind_inv in H1;
  destruct H1 as [blk1 [H1 H2]]; apply Pick_inv in H1;
  destruct H2 as [blk2 [H2 H3]]; apply Pick_inv in H2;
  destruct H3;
  destruct blk1, blk2;
  try destruct p;
  try destruct p0;
  try constructor;
  try assert (H9 : 0 < psLength r) by nomega;
  intuition.
  - competing_lookups (psHeap r) H3 n H1 n0;
    competing_lookups (psHeap r) H0 (psBuffer r) H1 n0.
    replace (psBuffer r - psBuffer r) with 0 by nomega.
    replace (psBuffer r + 1 - psBuffer r) with 1 by nomega.
    constructor.
  - competing_lookups (psHeap r) H0 (psBuffer r) H3 n.
    resolve_contention; auto.
  - competing_lookups (psHeap r) H0 (psBuffer r) H3 n.
    resolve_contention; auto; nomega.
  - resolve_contention; auto.
Qed.

Definition make_room_by_shifting_up (r : PS) : Comp PS :=
  res <- memcpy' (psHeap r) (psBuffer r) (psBuffer r + 1) (psLength r);
  ret {| psHeap   := fst res
       ; psBuffer := psBuffer r
       ; psBufLen := psBufLen r
       ; psOffset := 0
       ; psLength := psLength r + 1 |}.

Definition make_room_by_growing_buffer (r : PS) : Comp PS :=
  (* jww (2016-06-28): We could make a trade-off here by allocating
     extra bytes at the beginning in anticipation of future calls to
     [buffer_cons]. *)
  res <- realloc' (psHeap r) (psBuffer r)
                  (exist _ (psLength r + 1) (Nlt_plus_1 _));
  ret {| psHeap   := fst res
       ; psBuffer := snd res
       ; psBufLen := psLength r + 1
       ; psOffset := 0
       ; psLength := psLength r + 1 |}.

Definition buffer_cons (r : PS) (d : Mem.Word8) : Comp PS :=
  ps <- If 0 <? psOffset r
        Then ret (simply_widen_region r)
        Else If psLength r <? psBufLen r
             Then make_room_by_shifting_up r
             Else make_room_by_growing_buffer r;
  poke_at_offset ps d.

Definition buffer_uncons (r : PS) : Comp (PS * option Mem.Word8) :=
  If psLength r =? 0
  Then ret (r, None)
  Else (
    w <- peek' (psHeap r) (psBuffer r + psOffset r);
    ret ({| psHeap   := psHeap r
          ; psBuffer := psBuffer r
          ; psBufLen := psBufLen r
          ; psOffset := psOffset r + 1
          ; psLength := psLength r - 1 |}, Some (snd w))).

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
      (forall i x, nth (N.to_nat i) or x = x
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
      apply H4.
      rewrite N2Nat.inj_sub.
      replace (N.to_nat 1) with 1%nat; [|nomega].
      simpl; rewrite N2Nat.inj_succ in *; simpl.
      rewrite Nat.sub_0_r; assumption.
    }
  assert (psOffset r_n = 0) by nomega; clear Heqe.
  rewrite refineEquiv_If_Then_Else_Bind in H.
  apply refine_If_Then_Else_bool in H.
  destruct (psLength r_n <? psBufLen r_n) eqn:Heqe2;
  apply refine_computes_to_ret in H;
  revert H;
  unfold make_room_by_shifting_up,
         make_room_by_growing_buffer, poke_at_offset;
  autorewrite with monad laws; simpl;
  rewrite ?N.add_0_r;
  unfold memcpy', realloc', poke';
  rewrite refine_bind_dep_bind_ret; simpl;
  setoid_rewrite refine_bind_dep_bind_ret;
  simpl; intros;
  apply Bind_dep_inv in H;
  destruct H as [? [? ?]];
  apply Bind_dep_inv in c;
  destruct c as [? [? ?]]; destruct c;
  destruct_AbsR AbsR; construct_AbsR;
  try (right; split; [nomega|]; split; [nomega|]).
  - eapply refine_local_memcpy in x1; eauto;
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
          decisions; f_equal; f_equal; nomega.
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
        specialize (H4 _ _ H).
        teardown; intuition.
        nomega.
      left; teardown.
      split.
        apply H4.
        rewrite N2Nat.inj_succ, nth_overflow; trivial.
        nomega.
      unfold not, compose; intros.
      contradiction n.
      clear -H5.
      destruct H5.
      split; [nomega|]; simpl.
      rewrite N.add_1_l in H0.
      assumption.
    eexists.
    split.
      teardown.
      exists {| memSize := psBufLen r_n
              ; memData := data |}.
      split; auto.
      decisions; f_equal; f_equal; nomega.
    intros; teardown.
    destruct i using N.peano_ind.
      left; nomega.
    right; split; [nomega|].
    rewrite H0 in H4; simpl in H4; apply H4.
    simpl; rewrite N2Nat.inj_succ in *; simpl.
    destruct r_o; simpl in *; auto.
    nomega.
  - admit.
  - admit.
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

Lemma it_fits : forall base size off len,
  off + 1 < size ->
  fits base size (base + off) len ->
  fits base size (base + off + 1) (len - 1).
Proof. nomega. Qed.

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
  destruct (psLength r_n =? 0) eqn:Heqe.
    apply refine_computes_to_ret in H0.
    apply Return_inv in H0.
    destruct a; tsubst; simpl in *.
    destruct r_o; simpl in *; auto.
    destruct H, H0.
      destruct r_o; simpl in *; nomega.
    nomega.
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
  split; try nomega; split.
  - rewrite N.add_assoc.
    apply it_fits; trivial.
    admit.
  - eexists.
    split.
      exact H4.
    intros.
    rewrite <- N.add_assoc.
    apply H5.
    rewrite N.add_1_l, N2Nat.inj_succ.
    assumption.
  - rewrite N.add_assoc.
    apply it_fits; trivial.
    admit.
  - eexists.
    split.
      exact H4.
    intros.
    rewrite <- N.add_assoc.
    apply H5.
    rewrite N.add_1_l, N2Nat.inj_succ.
    assumption.
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
  destruct (psLength r_n =? 0) eqn:Heqe.
    apply refine_computes_to_ret in H0.
    apply Return_inv in H0.
    destruct a; tsubst; simpl in *.
    destruct r_o; simpl in *;
    destruct H, H0; auto.
      rewrite H0 in H; simpl in H.
      discriminate.
    nomega.
  revert H0.
  unfold peek'.
  rewrite refine_bind_dep_bind_ret; simpl.
  rewrite refine_bind_dep_ignore.
  unfold peek.
  autorewrite with monad laws; simpl.
  intros.
  apply refine_computes_to_ret in H0.
  apply Bind_inv in H0.
  destruct H0, H0.
  apply Return_inv in H1.
  destruct a; tsubst; simpl in *.
  apply Pick_inv in H0.
  destruct H.
  destruct H1.
    nomega.
  destruct H1, H1, H2.
  assert (within (psBuffer r_n) (psBufLen r_n) (psBuffer r_n + psOffset r_n)).
    nomega.
  specialize (H0 _ _ H2 H4); simpl in *.
  destruct r_o.
    nomega.
  f_equal.
  apply H0.
  replace (psBuffer r_n + psOffset r_n - psBuffer r_n)
     with (psOffset r_n); [|nomega].
  replace (psOffset r_n) with (psOffset r_n + 0).
    apply H3.
    reflexivity.
  nomega.
Qed.

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
