Require Import
  Fiat.ADT
  Fiat.ADTNotation
  Here.Nomega
  Here.Decidable
  Here.BindDep
  Here.FunRelation
  Here.FinRelation
  Here.Tactics
  Here.ADTInduction.

Generalizable All Variables.

Open Scope string_scope.

Definition emptyS   := "empty".
Definition allocS   := "alloc".
Definition reallocS := "realloc".
Definition freeS    := "free".
Definition peekS    := "peek".
Definition pokeS    := "poke".
Definition memcpyS  := "memcpy".
Definition memsetS  := "memset".

Section Heap.

Variable Word8 : Type.
Variable Zero  : Word8.

Record MemoryBlock := {
  memSize : N;
  memData : FunRel N Word8
}.

Ltac tsubst :=
  repeat
    match goal with
    | [ H : (_, _) = (_, _) |- _ ] => inv H
    | [ H : (_, _, _) = (_, _, _) |- _ ] => inv H
    | [ H : (_, _, _, _) = (_, _, _, _) |- _ ] => inv H
    | [ H : {| memSize := _
             ; memData := _ |} =
            {| memSize := _
             ; memData := _ |} |- _ ] => inv H
    end;
  subst.

Record CorrectMemoryBlock (blk : MemoryBlock) : Prop := {
  _ : 0 < memSize blk;
  _ : forall off, Member off (memData blk) -> off < memSize blk
}.

Definition Heap := FunRel N MemoryBlock.

Definition CorrectHeap (mem : Heap) :=
  All (fun p => CorrectMemoryBlock (snd p)) mem.

Ltac against_definition function len tac :=
  unfold CorrectHeap, All, function; intros;
  try destruct len; simpl in *;
  simplify_ensembles; simpl in *; decisions; tsubst;
  simplify_ensembles; simpl in *; decisions; tsubst; firstorder;
  intros; decisions; tsubst;
  tac; decisions; try nomega; firstorder.

Definition shift_address (addr1 addr2 : N) : Heap -> Heap := Move addr1 addr2.

Lemma shift_address_correct `(_ : CorrectHeap mem) :
  forall addr1 addr2, CorrectHeap (shift_address addr1 addr2 mem).
Proof.
  against_definition shift_address len idtac.
Qed.

Definition fit_to_length (addr : N) (len : N | 0 < len) : Heap -> Heap :=
  Modify addr (fun blk =>
                 {| memSize := ` len
                  ; memData := Filter (fun p => fst p < ` len)
                                      (memData blk) |}).

Lemma fit_to_length_correct `(_ : CorrectHeap mem) :
  forall addr len, CorrectHeap (fit_to_length addr len mem).
Proof.
  against_definition fit_to_length len idtac.
Qed.

Definition set_address (addr : N) (w : Word8) : Heap -> Heap :=
  Map (fun p =>
         let (base, blk) := p in
         IfDec within base (memSize blk) addr
         Then {| memSize := memSize blk
               ; memData := Update (addr - base) w (memData blk) |}
         Else blk).

Lemma set_address_correct `(_ : CorrectHeap mem) :
  forall addr w, CorrectHeap (set_address addr w mem).
Proof.
  against_definition set_address len simplify_ensembles.
Qed.

Definition copy_memory
        (addr1 addr2 : N) (len : N) (mem : Heap) : Comp (Heap * unit) :=
  ms <- { ms : option (N * MemoryBlock)
        | forall addr' blk', ms = Some (addr', blk') ->
            0 < len /\ Find (fun addr' blk' =>
                               fits addr' (memSize blk') addr1 len)
                            addr' blk' mem };
  md <- { md : option (N * MemoryBlock)
        | forall addr' blk', md = Some (addr', blk') ->
            0 < len /\ Find (fun addr' blk' =>
                               fits addr' (memSize blk') addr2 len)
                            addr' blk' mem };
  ret (match ms, md with
       | Some (saddr, sblk), Some (daddr, dblk) =>
         Update daddr {| memSize := memSize dblk
                       ; memData :=
                           let soff := addr1 - saddr in
                           let doff := addr2 - daddr in
                           Overlay (fun a =>
                                      IfDec within doff len a
                                      Then Some (soff + (a - doff))
                                      Else None)
                                   (memData dblk) (memData sblk) |} mem
       | _, _ => mem
       end, tt).

Lemma copy_memory_correct `(_ : CorrectHeap mem) :
  forall addr1 addr2 len mem',
    copy_memory addr1 addr2 len mem ↝ (mem', tt) -> CorrectHeap mem'.
Proof.
  unfold CorrectHeap, All, copy_memory; intros.
  simplify_ensembles; simpl in *.
  destruct x, x0;
  simplify_ensembles; simpl in *; decisions; tsubst.
  - inv H0.
      firstorder.
    inv H2.
    rename n1 into saddr.
    rename m1 into sblk.
    rename n into daddr.
    rename m0 into dblk.
    destruct (H saddr sblk eq_refl); clear H.
    destruct (H1 daddr dblk eq_refl); clear H1 H0.
    destruct H2, H3.
    destruct (CorrectHeap0 _ H0).
    destruct (CorrectHeap0 _ H2).
    simpl in *.
    constructor; auto; simpl; intros.
    destruct H8.
    unfold Overlay, Ensembles.In in *; simpl in *.
    specialize (H8 (addr1 - saddr + (off - (addr2 - daddr)))).
    decisions.
    + destruct H8; teardown; intuition.
      unfold Member in *.
      specialize (H5 (addr1 - saddr + (off - (addr2 - daddr)))).
      assert (exists b : Word8,
                 In (N * Word8) (relEns (memData sblk))
                    (addr1 - saddr + (off - (addr2 - daddr)), b)).
        exists x.
        assumption.
      specialize (H5 H10).
      unfold fits in *.
      teardown.
      unfold within in *.
      clear -H1 H12 H H3 H11 H4 H5 H6 Heqe.
      nomega.
    + destruct H8; teardown.
        discriminate.
      firstorder.
  - firstorder.
  - firstorder.
  - firstorder.
Qed.

Definition set_memory (addr : N) (len : N) (w : Word8) :
  Heap -> Heap :=
  Map (fun p =>
         let (base, blk) := p in
         IfDec fits base (memSize blk) addr len
         Then {| memSize := memSize blk
               ; memData := Define (within (addr - base) len) w
                                   (memData blk) |}
         Else blk).

Lemma set_memory_correct `(_ : CorrectHeap mem) :
  forall addr len w, CorrectHeap (set_memory addr len w mem).
Proof.
  against_definition set_memory len ltac:(unfold Ensembles.In in *; simpl in *).
Qed.

Definition free_block (addr : N) : Heap -> Heap := Remove addr.

Lemma free_block_correct `(_ : CorrectHeap mem) :
  forall addr, CorrectHeap (free_block addr mem).
Proof.
  against_definition free_block len idtac.
Qed.

Definition find_free_block (len : N | 0 < len) (mem : Heap) : Comp N :=
  { addr : N | forall addr' blk',
      ~ Find (fun addr' blk' =>
                overlaps addr' (memSize blk') addr (` len))
             addr' blk' mem }.

Lemma find_free_block_spec (len : N | 0 < len) `(_ : CorrectHeap r) :
  forall addr, find_free_block len r ↝ addr -> ~ Member addr r.
Proof.
  simplify_ensembles.
  unfold not; intros.
  apply Member_Lookup in H0; destruct H0.
  specialize (H addr x).
  apply (LogicFacts.not_and_implication (Lookup _ _ _)) in H; eauto.
  destruct (All_Lookup _ _ _ r CorrectHeap0 _ _ H0).
  contradiction (overlaps_irr addr H1 (proj2_sig len)).
Qed.

Definition HeapSpec := Def ADT {
  (* a mapping of addr tokens to a length, and another mapping from
     offsets within a certain block to individual bytes *)
  rep := Heap,

  Def Constructor0 emptyS : rep := ret (Empty _ _),,

  (* Allocation returns the address for the newly allocated block. Note that
     conditions such as out-of-memory are not handled here; the final
     implementation must decide how to handle this operationally, such as
     throwing an exception. *)
  Def Method1 allocS (r : rep) (len : N | 0 < len) : rep * N :=
    addr <- find_free_block len r;
    ret (Update addr {| memSize := ` len
                      ; memData := Empty _ _ |} r, addr),

  (* Freeing an unallocated block is a no-op. *)
  Def Method1 freeS (r : rep) (addr : N) : rep * unit :=
    ret (free_block addr r, tt),

  (* Realloc is not required to reuse the same block. If the address does not
     identify an allociated region, a new memory block is returned without any
     bytes moved. *)
  Def Method2 reallocS (r : rep) (addr : N) (len : N | 0 < len) : rep * N :=
    b <- { b : bool | forall blk, decides b (Lookup addr blk r) };
    naddr <- find_free_block len (free_block addr r);
    ret (If b
         Then fit_to_length naddr len (shift_address addr naddr r)
         Else Update naddr {| memSize := ` len
                            ; memData := Empty _ _ |} r,
         naddr),

  (* Peeking an unallocated address allows any value to be returned. *)
  Def Method1 peekS (r : rep) (addr : N) : rep * Word8 :=
    p <- { p : Word8
         | forall base blk',
             (* There are three cases to consider here:
                1. Peeking an allocated, initialized byte. This must
                   return the same byte that was last poke'd at that
                   position.
                2. Peeking an allocated, uninitialized byte.
                3. Peeking at an unallocated location. *)
             Find (fun a b => within a (memSize b) addr) base blk' r
               -> forall v, Lookup (addr - base) v (memData blk')
               -> p = v };
    ret (r, p),

  (* Poking an unallocated address is a no-op and returns false. *)
  Def Method2 pokeS (r : rep) (addr : N) (w : Word8) : rep * unit :=
    ret (set_address addr w r, tt),

  (* Data may only be copied from one allocated block to another (or within
     the same block), and the region must fit within both source and
     destination. Otherwise, the operation is a no-op and returns false. *)
  Def Method3 memcpyS (r : rep) (addr1 : N) (addr2 : N) (len : N) :
    rep * unit := copy_memory addr1 addr2 len r,

  (* Any attempt to memset bytes outside of an allocated block is a no-op that
     returns false. *)
  Def Method3 memsetS (r : rep) (addr : N) (len : N) (w : Word8) :
    rep * unit :=
    ret (set_memory addr len w r, tt)

}%ADTParsing.

Definition empty : Comp (Rep HeapSpec) :=
  Eval simpl in callCons HeapSpec emptyS.

Definition alloc (r : Rep HeapSpec) (len : N | 0 < len) :
  Comp (Rep HeapSpec * N) :=
  Eval simpl in callMeth HeapSpec allocS r len.

Definition free (r : Rep HeapSpec) (addr : N) :
  Comp (Rep HeapSpec * unit) :=
  Eval simpl in callMeth HeapSpec freeS r addr.

Definition realloc (r : Rep HeapSpec) (addr : N) (len : N | 0 < len) :
  Comp (Rep HeapSpec * N) :=
  Eval simpl in callMeth HeapSpec reallocS r addr len.

Definition peek (r : Rep HeapSpec) (addr : N) : Comp (Rep HeapSpec * Word8) :=
  Eval simpl in callMeth HeapSpec peekS r addr.

Definition poke (r : Rep HeapSpec) (addr : N) (w : Word8) :
  Comp (Rep HeapSpec * unit) :=
  Eval simpl in callMeth HeapSpec pokeS r addr w.

Definition memcpy (r : Rep HeapSpec) (addr : N) (addr2 : N) (len : N) :
  Comp (Rep HeapSpec * unit) :=
  Eval simpl in callMeth HeapSpec memcpyS r addr addr2 len.

Definition memset (r : Rep HeapSpec) (addr : N) (len : N) (w : Word8) :
  Comp (Rep HeapSpec * unit) :=
  Eval simpl in callMeth HeapSpec memsetS r addr len w.

Theorem allocations_are_correct :
  forall r : Rep HeapSpec, fromADT _ r -> CorrectHeap r.
Proof.
  unfold CorrectHeap, All; intros.
  generalize dependent p.
  ADT induction r.
  - constructor; inversion H0.
  - destruct x; simpl in *.
    inv H1.
      inv H2.
      exact (IHfromADT _ H1).
    simplify_ensembles.
    constructor; firstorder.
  - inv H1; firstorder.
  - destruct x0; simpl in *.
    destruct v.
      exact (fit_to_length_correct (@shift_address_correct _ IHfromADT _ _) H1).
    inv H1; firstorder.
      inv H2; trivial.
    inv H2; inv H1.
  - exact (set_address_correct IHfromADT H1).
  - destruct x2.
    pose proof (copy_memory_correct IHfromADT H0).
    exact (H2 _ H1).
  - exact (set_memory_correct IHfromADT H1).
Qed.

Corollary allocations_have_size : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr len data,
    Lookup addr {| memSize := len; memData := data |} r -> 0 < len.
Proof.
  intros.
  destruct (allocations_are_correct H _ H0) as [H1 _].
  exact H1.
Qed.

Ltac reveal_no_overlap r :=
  match goal with
  | [ H1 : forall addr' blk',
        ~ Find (fun a b => overlaps a (memSize b) ?A1 ?B1) addr' blk' _,
        H2 : Lookup ?A2 ?B2 _ |- _ ] =>
    specialize (H1 A2 B2);
    apply (LogicFacts.not_and_implication (Lookup _ _ _)) in H1; eauto
  | [ H1 : forall addr' blk',
        ~ Find (fun a b => overlaps a (memSize b) ?A1 ?B1) addr' blk' _,
        H2 : Ensembles.In _ _ (?A2, ?B2) |- _ ] =>
    specialize (H1 A2 B2);
    apply (LogicFacts.not_and_implication (Lookup _ _ _)) in H1; eauto
  end.

Theorem allocations_unique : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr blk1,
       Lookup addr blk1 r
    -> forall blk2, Lookup addr blk2 r
    -> blk1 = blk2.
Proof.
  intros.
  generalize dependent blk2.
  generalize dependent blk1.
  generalize dependent addr.
  ADT induction r.
  - inversion H0.
  - unfold find_free_block in H0.
    teardown; tsubst; simplify_ensembles.
    reveal_no_overlap r.
  - firstorder.
  - destruct x0; simpl in *.
    unfold fit_to_length, shift_address in H1, H2.
    unfold free_block, find_free_block in H0.
    destruct v; unfold Lookup in *;
    simplify_ensembles; simpl in *; tsubst; eauto.
  - unfold set_address in H1, H2.
    teardown; decisions; tsubst;
    specialize (IHfromADT _ _ H2 _ H3); subst; eauto;
    rewrite Heqe in Heqe0; discriminate.
  - unfold copy_memory in H0.
    unfold Lookup in *.
    simplify_ensembles; simpl in *;
    destruct x3, x4;
    simplify_ensembles; tsubst;
    simplify_ensembles;
    exact (IHfromADT _ _ H1 _ H2).
  - unfold set_memory in H1, H2.
    teardown; decisions; tsubst;
    try destruct x2;
    try destruct x3;
    specialize (IHfromADT _ _ H2 _ H3);
    tsubst; simpl in *; eauto;
    rewrite Heqe in Heqe0; discriminate.
Qed.

Corollary allocations_unique_r : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr1 blk,
       Lookup addr1 blk r
    -> forall addr2, ~ Lookup addr2 blk r
    -> addr1 <> addr2.
Proof.
  intros.
  unfold not; intros; subst.
  ADT induction r.
Qed.

Theorem allocations_no_overlap : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr1 blk1,
       Lookup addr1 blk1 r
    -> forall addr2 blk2, Lookup addr2 blk2 r
    -> addr1 <> addr2
    -> ~ overlaps addr1 (memSize blk1) addr2 (memSize blk2).
Proof.
  intros.
  generalize dependent blk2.
  generalize dependent addr2.
  generalize dependent blk1.
  generalize dependent addr1.
  ADT induction r.
  - inversion H0.
  - unfold find_free_block in H0.
    teardown; tsubst; simplify_ensembles.
    + reveal_no_overlap r.
    + rewrite overlaps_sym.
      reveal_no_overlap r.
    + eapply IHfromADT; eassumption.
  - unfold free_block in H1, H3.
    teardown; eapply IHfromADT; eassumption.
  - destruct x0; simpl in *.
    unfold fit_to_length, shift_address,
           free_block, find_free_block in *.
    destruct v; simpl in *;
    teardown; tsubst; simplify_ensembles; simpl in *.
    + inv H6. reveal_no_overlap r.
      apply Lookup_Remove with (a':=x); trivial.
    + inv H7. reveal_no_overlap r.
        unfold not; intros.
        apply overlaps_sym in H7.
        contradiction.
      apply Lookup_Remove with (a':=x); trivial.
    + inv H6; inv H7.
      eapply IHfromADT; eassumption.
    + inv H1; inv H3; simplify_ensembles.
      * eapply IHfromADT; eassumption.
      * reveal_no_overlap r.
        apply Lookup_Remove with (a':=x); trivial.
        eapply allocations_unique_r; eauto.
      * reveal_no_overlap r.
          unfold not; intros.
          apply overlaps_sym in H1.
          contradiction.
        apply Lookup_Remove with (a':=x); trivial.
        eapply allocations_unique_r; eauto.
  - unfold set_address in H1, H3.
    teardown; decisions; tsubst; simpl;
    eapply IHfromADT; eassumption.
  - unfold copy_memory in H0.
    unfold Lookup in *.
    simplify_ensembles; simpl in *.
    destruct x3, x4;
    try destruct p;
    try destruct p0;
    try specialize (H0 n m eq_refl);
    try specialize (H4 n0 m0 eq_refl);
    simplify_ensembles; tsubst;
    simplify_ensembles;
    try destruct H6;
    try destruct H7;
    eapply IHfromADT; try eassumption.
  - unfold set_memory in H1, H3.
    teardown; decisions; tsubst; simpl;
    eapply IHfromADT; eassumption.
Qed.

Theorem find_partitions_a_singleton : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr base blk,
    Find (fun a b => within a (memSize b) addr) base blk r
      -> Partition (fun a b => within a (memSize b) addr) r
           = (Single base blk, Remove base r).
Proof.
  unfold Same; intros.
  destruct H0.
  pose proof (allocations_no_overlap H _ H0).
  pose proof (allocations_are_correct H).
  pose proof (allocations_unique H _ _ H0).
  destruct (H3 (base, blk)); trivial;
  simpl in *; clear H3 H5.
  unfold Same_set, Included, Partition; f_equal.
    unfold Single.
    apply Compare.
    split; intros.
      unfold Included; intros.
      simplify_ensembles; simpl in *.
      destruct (N.eq_dec base n).
        subst; specialize (H4 _ H7); subst.
        constructor.
      specialize (H2 _ _ H7 n0).
      unfold within, overlaps in *; nomega.
    simplify_ensembles.
  unfold Remove.
  apply Compare.
  split; intros.
    unfold Included; intros.
    simplify_ensembles; simpl in *.
    destruct (N.eq_dec base n).
      subst; specialize (H4 _ H7); subst.
      contradiction.
    apply not_eq_sym.
    exact n0.
  simplify_ensembles.
  unfold Ensembles.In in H5; simpl in H5.
  apply not_eq_sym in H5.
  specialize (H2 _ _ H3 H5).
  unfold within, overlaps in *; nomega.
Qed.

Corollary allocations_disjoint : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr blk, Lookup addr blk r
    -> forall pos, within addr (memSize blk) pos
    -> forall addr' blk',
        Lookup addr' blk' r
          -> addr <> addr'
          -> ~ within addr' (memSize blk') pos.
Proof.
  intros.
  pose proof (allocations_no_overlap H _ H0 _ H2 H3).
  unfold within, overlaps in *; nomega.
Qed.

End Heap.

Ltac tsubst :=
  repeat
    match goal with
    | [ H : (_, _) = (_, _) |- _ ] => inv H
    | [ H : (_, _, _) = (_, _, _) |- _ ] => inv H
    | [ H : (_, _, _, _) = (_, _, _, _) |- _ ] => inv H
    | [ H : {| memSize := _
             ; memData := _ |} =
            {| memSize := _
             ; memData := _ |} |- _ ] => inv H
    end;
  subst.

Theorem neg_x_y_eq__x_y_eq : forall x y : bool,
  negb x = negb y -> x = y.
Proof. destruct 0, x; auto. Qed.
