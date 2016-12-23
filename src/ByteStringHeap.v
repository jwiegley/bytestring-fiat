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
  let H0 := fresh "H0" in
  let H3 := fresh "H3" in
  let H4 := fresh "H4" in
  let H5 := fresh "H5" in
  let data := fresh "data" in
  destruct H2 as [[H0 [H5 H3]]|[H0 [H5 [H3 H4]]]];
  [ rewrite ?H0, ?H5 in * |].

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
    rewrite HA, !N.add_0_r in *; clear HA H6.
    setoid_replace (n - (x1 + 1) + psBuffer (snd r_n))
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
      eapply H5; eauto; nomega.
    apply H5 with (i:=N.succ (N.succ i)); try nomega.
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
    eapply H5; eauto; nomega.
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

(* jww (2016-12-21): For now, just allocate and copy from both. *)
Program Definition buffer_append
        (h1 : Rep HeapSpec) (r1 : PS)
        (h2 : Rep HeapSpec) (r2 : PS) :
  Comp (Rep HeapSpec * PS) :=
  IfDep 0 <? psLength r1
  Then fun _ =>
    IfDep 0 <? psLength r2
    Then fun _ =>
      `(h1, a) <- alloc h1 (psLength r1 + psLength r2);
      h1 <- memcpy h1 (psBuffer r1 + psOffset r1) a (psLength r1);
      let h1 := {| resvs := resvs h1
                 ; bytes := copy_bytes_between_heaps
                              (psBuffer r2 + psOffset r2) a (psLength r2)
                              (bytes h2) (bytes h1) |} in
      ret (h1, {| psBuffer := a
                ; psBufLen := psLength r1 + psLength r2
                ; psOffset := 0
                ; psLength := psLength r1 + psLength r2 |})
    Else fun _ => ret (h1, r1)
  Else fun _ => ret (h2, r2).
Obligation 1. nomega. Defined.

Lemma refineEquiv_If_Then_Else :
  forall (A : Type) (c : bool) (x y : Comp A),
    refineEquiv x y ->
    forall x0 y0 : Comp A, refineEquiv x0 y0 ->
    refineEquiv (If c Then x Else x0) (If c Then y Else y0).
Proof. intros; destruct c; auto. Qed.

Lemma refineEquiv_buffer_append
      (h1 : Rep HeapSpec) (r1 : PS)
      (h2 : Rep HeapSpec) (r2 : PS) :
  refineEquiv
    (buffer_append h1 r1 h2 r2)
    (If 0 <? psLength r1
     Then If 0 <? psLength r2
       Then
         x0 <- find_free_block (psLength r1 + psLength r2) (resvs h1);
         h0 <- memcpy {| resvs := M.add x0 (psLength r1 + psLength r2) (resvs h1)
                       ; bytes := bytes h1 |}
                      (psBuffer r1 + psOffset r1) x0 (psLength r1);
         ret ({| resvs := resvs h0
               ; bytes := copy_bytes_between_heaps
                            (psBuffer r2 + psOffset r2) x0 (psLength r2)
                            (bytes h2) (bytes h0) |},
              {| psBuffer := x0
               ; psBufLen := psLength r1 + psLength r2
               ; psOffset := 0
               ; psLength := psLength r1 + psLength r2 |})
       Else ret (h1, r1)
     Else ret (h2, r2)).
Proof.
  unfold buffer_append.
  etransitivity.
    apply refineEquiv_IfDep_Then_Else.
      intros.
      apply refineEquiv_IfDep_Then_Else.
        intros.
        unfold allocate_buffer, Bind2,
               make_room_by_growing_buffer, Bind2.
        rewrite refineEquiv_unfold_alloc; simpl.
        Opaque memcpy.
        Opaque free.
        split.
          simplify with monad laws; simpl.
          finish honing.
        simpl.
        autorewrite with monad laws; simpl.
        Transparent memcpy.
        Transparent free.
        reflexivity.
      intros.
      finish honing.
    intros.
    finish honing.
  rewrite refineEquiv_strip_IfDep_Then_Else.
  apply refineEquiv_If_Then_Else.
    rewrite refineEquiv_strip_IfDep_Then_Else.
    reflexivity.
  reflexivity.
Qed.

Lemma buffer_append_sound : forall r_o1 r_o2 r_n1 r_n2,
  ByteString_list_AbsR r_o1 r_n1
    -> ByteString_list_AbsR r_o2 r_n2
    -> forall r_n',
         buffer_append (fst r_n1) (snd r_n1) (fst r_n2) (snd r_n2) ↝ r_n'
    -> ByteString_list_AbsR (r_o1 ++ r_o2) r_n'.
Proof.
  intros.
  apply refine_computes_to in H1.
  rewrite refineEquiv_buffer_append in H1.
  apply refine_If_Then_Else_bool in H1.
  destruct r_n1, p; simpl in H1.
  revert H1.
  destruct psLength0 eqn:Heqe1; simpl; intros.
    apply computes_to_refine in H1.
    destruct_computations.
    destruct_AbsR H; simpl;
    destruct r_o1; simpl in *; try nomega.
  destruct r_n2, p0; simpl in H1.
  revert H1.
  destruct psLength1 eqn:Heqe2; simpl; intros.
    apply computes_to_refine in H1.
    destruct_computations.
    destruct_AbsR H0; simpl;
    destruct r_o2; simpl in *; try nomega;
    rewrite app_nil_r; trivial.
  revert H1.
  unfold find_free_block, memcpy.
  autorewrite with monad laws; simpl.
  intro H1.
  apply computes_to_refine in H1.
  destruct_computations.
  destruct_AbsR H; destruct_AbsR H0; construct_AbsR;
  destruct r_o1, r_o2; simpl in *;
  rewrite ?Pos2Nat.inj_add, <- ?H2, <- ?H3, ?app_length;
  try nomega;
  [ left; intuition;
    rewrite <- positive_nat_N, Pos2Nat.inj_add; nomega
  | right; intuition;
    [ nomega
    | rewrite <- positive_nat_N, Pos2Nat.inj_add; nomega
    | rewrite <- !positive_nat_N, <- ?H2, <- ?H3 ] .. ].
  - admit.
  - admit.
  - admit.
Admitted.

Lemma refine_skip2 {B} (dummy : Comp B) {A} (a : Comp A) :
  refine a (dummy >> a).
Proof.
  repeat first [ intro
               | computes_to_inv
               | assumption
                 | econstructor; eassumption
                 | econstructor; try eassumption; [] ].
  eauto.
Qed.

Class RefineUnder {A : Type} (a a' : Comp A) := {
  rewrite_under : refine a a'
}.

Instance RefineUnder_Bind {A B : Type}
         (ca ca' : Comp A)
         (b b' : A -> Comp A)
         (refine_a : refine ca ca')
         (refine_b : forall a, ca ↝ a -> refine (b a) (b' a)) :
  RefineUnder (a <- ca; b a) (a' <- ca'; b' a') :=
  {| rewrite_under := refine_under_bind_both b b' refine_a refine_b |}.

Definition refine_skip2_pick {B} (dummy : Comp B) {A} (P : A -> Prop) :
  refine {a | P a} (dummy >> {a | P a}) := @refine_skip2 _ _ _ _.

Definition refine_skip2_bind {B} (dummy : Comp B)
           {A C} (ca : Comp A) (k : A -> Comp C) :
  refine (ca >>= k) (dummy >> (ca >>= k)) := @refine_skip2 _ _ _ _.

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
    setoid_rewrite (@refine_skip2_pick _ (buffer_cons (fst r_n) (snd r_n) d)).
    etransitivity.
      refine_under.
        finish honing.
      refine pick val a.
        finish honing.
      eapply buffer_cons_sound; eauto.
    simplify with monad laws; simpl.
    finish honing.
  }

  {
    simplify with monad laws.
    setoid_rewrite (refine_skip2_bind (dummy:=buffer_uncons (fst r_n) (snd r_n))).
    etransitivity.
    - refine_under.
      + finish honing.
      + rewrite fst_match_list, snd_match_list;
          erewrite <- buffer_uncons_impl by eauto.
         refine pick val (fst a).
         simplify with monad laws.
         finish honing.
         eapply buffer_uncons_sound; eauto.
    - simpl; unfold buffer_uncons.
      rewrite refineEquiv_If_Then_Else_Bind.
      refine_under;
      simplify with monad laws; simpl;
      finish honing.
  }

  {
    simplify with monad laws.
    rewrite (refine_skip2_pick (dummy:=buffer_append (fst r_n) (snd r_n)
                                                     (fst r_n0) (snd r_n0))).
    refine_under.
      finish honing.
    refine pick val a.
      finish honing.
    eapply buffer_append_sound; eauto.
  }

  apply reflexivityT.
Defined.

End ByteStringHeap.
