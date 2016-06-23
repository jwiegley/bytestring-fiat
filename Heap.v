Require Import
  Coq.Sets.Ensembles
  Coq.NArith.NArith
  Omega.

Require Import
  Fiat.ADT
  Fiat.ADTNotation
  Here.ADTInduction
  Here.LibExt
  Here.Decidable.

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

Open Scope N_scope.

Definition within (addr : N) (len : N) (a : N) : Prop :=
  addr <= a < addr + len.

Definition within_le (addr : N) (len : N) (a : N) : Prop :=
  addr <= a <= addr + len.

Definition fits (addr len off sz : N) : Prop :=
  within addr len off /\ off + sz <= len.

Definition overlaps (addr len addr2 len2 : N) : Prop :=
  addr < addr2 + len2 /\ addr2 < addr + len.

Lemma overlaps_sym : forall addr1 len1 addr2 len2,
  overlaps addr1 len1 addr2 len2 <-> overlaps addr2 len2 addr1 len1.
Proof.
  unfold overlaps; split; intros;
  destruct H; split; trivial.
Qed.

Lemma overlaps_irr : forall addr len1 len2,
  0 < len1 -> 0 < len2 -> overlaps addr len1 addr len2.
Proof.
  unfold overlaps; split; intros;
  apply N.lt_add_pos_r; assumption.
Qed.

Record MemoryBlock := {
  memAddr : N;
  memSize : N;
  memData : Ensemble (N * Word8)
}.

Record CorrectMemoryBlock (blk : MemoryBlock) : Prop := {
  _ : 0 < memSize blk;
  _ : forall off val,
        In _ (memData blk) (off, val) -> off < memSize blk;
  _ : forall off val1 val2,
        In _ (memData blk) (off, val1) ->
        In _ (memData blk) (off, val2) -> val1 = val2
}.

Definition CorrectHeap (mem : Ensemble MemoryBlock) : Prop :=
  forall blk, mem ↝ blk -> CorrectMemoryBlock blk.

Definition shift_address (addr1 addr2 : N) (mem : Ensemble MemoryBlock) :
  Ensemble MemoryBlock :=
  blk <- mem;
  ret {| memAddr := IfDec addr1 = memAddr blk
                    Then addr2
                    Else memAddr blk
       ; memSize := memSize blk
       ; memData := memData blk |}.

Lemma shift_address_correct `(_ : CorrectHeap mem) :
  forall addr1 addr2 blk', shift_address addr1 addr2 mem ↝ blk'
    -> CorrectMemoryBlock blk'.
Proof.
  unfold CorrectHeap in CorrectHeap0.
  unfold shift_address, IfDec_Then_Else; simpl.
  intros.
  simplify_ensembles; subst.
  destruct (CorrectHeap0 x H).
  constructor; simpl in *; intros; eauto.
Qed.

Definition fit_to_length (addr : N) (len : N | 0 < len)
           (mem : Ensemble MemoryBlock) :
  Ensemble MemoryBlock :=
  blk <- mem;
  ret (IfDec addr = memAddr blk
       Then {| memAddr := memAddr blk
             ; memSize := proj1_sig len
             ; memData := fun p => fst p < proj1_sig len /\ memData blk p |}
       Else blk).

Lemma fit_to_length_correct `(_ : CorrectHeap mem) :
  forall addr len blk', fit_to_length addr len mem ↝ blk'
    -> CorrectMemoryBlock blk'.
Proof.
  unfold CorrectHeap in CorrectHeap0.
  unfold fit_to_length, IfDec_Then_Else; simpl.
  intros.
  simplify_ensembles.
  pose proof (CorrectHeap0 x H).
  destruct (addr =? memAddr x);
  [| subst; assumption ].
  destruct H1; clear H1 H2.
  simplify_ensembles; subst; simpl.
  destruct len; simpl.
  constructor; simpl in *; intros; trivial;
  unfold Ensembles.In in *; simpl in *; intuition.
  apply (H3 off val1 val2); assumption.
Qed.

Definition set_address (addr : N) (x : Word8) (mem : Ensemble MemoryBlock) :
  Comp (MemoryBlock * bool) :=
  blk <- mem;
  ret (IfDec within (memAddr blk) (memSize blk) addr
       Then ({| memAddr := memAddr blk
              ; memSize := memSize blk
              ; memData :=
                  let off := addr - memAddr blk in
                  Add _ (Setminus _  (memData blk) (fun p => fst p = off))
                        (off, x) |}, true)
       Else (blk, false)).

Lemma set_address_correct `(_ : CorrectHeap mem) :
  forall addr x blk' b, set_address addr x mem ↝ (blk', b)
    -> CorrectMemoryBlock blk'.
Proof.
  unfold CorrectHeap in CorrectHeap0.
  unfold set_address, IfDec_Then_Else; simpl.
  intros.
  simplify_ensembles.
  pose proof (CorrectHeap0 x0 H).
  destruct ((memAddr x0 <=? addr) &&
            (addr <? memAddr x0 + memSize x0))%bool eqn:Heqe; inv H0;
  [| assumption ].
  destruct H1.
  constructor; simpl; intros; trivial.
  - inv H3; inv H4.
      apply (H1 off val); assumption.
    apply Bool.andb_true_iff in Heqe; destruct Heqe.
    apply N.leb_le in H3.
    rewrite N2Z.inj_lt, N2Z.inj_sub; trivial.
    rewrite N2Z.inj_le in H3.
    apply N.ltb_lt in H4.
    rewrite N2Z.inj_lt, N2Z.inj_add in H4.
    omega.
  - inv H3; inv H4; inv H3; inv H5.
    + apply (H2 off); assumption.
    + contradiction H4; constructor.
    + contradiction H6; constructor.
    + reflexivity.
Qed.

Definition copy_memory
           (addr1 addr2 : N) (len : N | 0 < len)
           (mem : Ensemble MemoryBlock) : Comp (MemoryBlock * bool) :=
  dst <- mem;
  IfDec fits (memAddr dst) (memSize dst) addr2 (proj1_sig len)
  Then (
    src <- mem;
    ret (IfDec fits (memAddr src) (memSize src) addr1 (proj1_sig len)
         Then ({| memAddr := memAddr dst
                ; memSize := memSize dst
                ; memData :=
                    fun p =>
                      IfDec within addr2 (proj1_sig len) (fst p)
                      Then memData src (addr2 + (fst p - addr1), snd p)
                      Else memData dst p |}, true)
         Else (dst, false))
  )
  Else ret (dst, false).

Lemma copy_memory_correct `(_ : CorrectHeap mem) :
  forall addr1 addr2 len blk' b, copy_memory addr1 addr2 len mem ↝ (blk', b)
    -> CorrectMemoryBlock blk'.
Proof.
  unfold CorrectHeap in CorrectHeap0.
  unfold copy_memory, IfDec_Then_Else; simpl.
  intros.
  destruct len; simpl in *.
  simplify_ensembles.
  destruct (CorrectHeap0 x0 H); clear H.
  constructor; simpl; intros; trivial.
  - clear -H0 H1.
    destruct ((memAddr x0 <=? addr2) &&
              (addr2 <? memAddr x0 + memSize x0) &&
              (addr2 + x <=? memSize x0))%bool; subst;
    simplify_ensembles;
    [| inv H0; trivial ].
    destruct ((memAddr x1 <=? addr1) &&
              (addr1 <? memAddr x1 + memSize x1) &&
              (addr1 + x <=? memSize x1))%bool;
    simplify_ensembles; inv H0; subst; simpl in *; trivial.
  - clear -H0 H2 H.
    destruct ((memAddr x0 <=? addr2) &&
              (addr2 <? memAddr x0 + memSize x0) &&
              (addr2 + x <=? memSize x0))%bool eqn:Heqe; subst;
    simplify_ensembles; subst; trivial.
      destruct ((memAddr x1 <=? addr1) &&
                (addr1 <? memAddr x1 + memSize x1) &&
                (addr1 + x <=? memSize x1))%bool;
      simplify_ensembles; inv H1; subst; simpl in *.
        unfold Ensembles.In in H; simpl in H.
        destruct ((addr2 <=? off) && (off <? addr2 + x))%bool eqn:Heqe2.
          apply Bool.andb_true_iff in Heqe; destruct Heqe.
          apply Bool.andb_true_iff in Heqe2; destruct Heqe2.
          clear -H3 H4 H5.
          apply N.leb_le in H4.
          apply N.leb_le in H3.
          rewrite N2Z.inj_le, N2Z.inj_add in H3.
          rewrite N2Z.inj_le in H4.
          apply N.ltb_lt in H5.
          rewrite N2Z.inj_lt, N2Z.inj_add in H5.
          rewrite N2Z.inj_lt.
          omega.
        apply (H2 off val); assumption.
      apply (H2 off val); assumption.
    inv H0.
    apply (H2 off val); assumption.
  - clear -H0 H H4 H3 CorrectHeap0.
    destruct ((memAddr x0 <=? addr2) &&
              (addr2 <? memAddr x0 + memSize x0) &&
              (addr2 + x <=? memSize x0))%bool; subst;
    simplify_ensembles; subst; trivial.
      destruct ((memAddr x1 <=? addr1) &&
                (addr1 <? memAddr x1 + memSize x1) &&
                (addr1 + x <=? memSize x1))%bool;
      simplify_ensembles; inv H1; subst; simpl in *.
      {
        destruct (CorrectHeap0 x1 H0).
        unfold Ensembles.In in *; simpl in *.
        destruct ((addr2 <=? off) && (off <? addr2 + x))%bool.
          apply (H5 (addr2 + (off - addr1)) val1 val2); assumption.
        apply (H3 off val1 val2); assumption.
      }
      apply (H3 off val1 val2); assumption.
    inv H0.
    apply (H3 off val1 val2); assumption.
Qed.

Definition set_memory (addr : N) (len : N | 0 < len) (w : Word8)
           (mem : Ensemble MemoryBlock) : Comp (MemoryBlock * bool) :=
  blk <- mem;
  ret (IfDec fits (memAddr blk) (memSize blk) addr (proj1_sig len)
       Then ({| memAddr := memAddr blk
              ; memSize := memSize blk
              ; memData := fun p =>
                             IfDec within addr (proj1_sig len) (fst p)
                             Then snd p = w
                             Else memData blk p |}, true)
       Else (blk, false)).

Lemma set_memory_correct `(_ : CorrectHeap mem) :
  forall addr len w blk' b, set_memory addr len w mem ↝ (blk', b)
    -> CorrectMemoryBlock blk'.
Proof.
  unfold CorrectHeap in CorrectHeap0.
  unfold set_memory, IfDec_Then_Else; simpl.
  intros.
  destruct len; simpl in *.
  simplify_ensembles.
  destruct (CorrectHeap0 x0 H); clear H.
  constructor; simpl; intros; trivial.
  - clear -H0 H1.
    destruct ((memAddr x0 <=? addr) &&
              (addr <? memAddr x0 + memSize x0) &&
              (addr + x <=? memSize x0))%bool; subst;
    simplify_ensembles; inv H0; subst; simpl in *; trivial.
  - clear -H0 H2 H.
    destruct ((memAddr x0 <=? addr) &&
              (addr <? memAddr x0 + memSize x0) &&
              (addr + x <=? memSize x0))%bool eqn:Heqe; subst;
    simplify_ensembles; inv H0; subst; simpl in *;
    [| apply (H2 off val); assumption].
    unfold Ensembles.In in H; simpl in H.
    destruct ((addr <=? off) && (off <? addr + x))%bool eqn:Heqe2;
    [| apply (H2 off val); assumption].
    destruct H; subst.
    apply Bool.andb_true_iff in Heqe; destruct Heqe.
    apply Bool.andb_true_iff in Heqe2; destruct Heqe2.
    clear -H0 H1 H3.
    rewrite N2Z.inj_lt.
    apply N.leb_le in H0.
    rewrite N2Z.inj_le, N2Z.inj_add in H0.
    apply N.leb_le in H1.
    apply N.ltb_lt in H3.
    rewrite N2Z.inj_lt, N2Z.inj_add in H3.
    omega.
  - clear -H0 H H4 H3 CorrectHeap0.
    destruct ((memAddr x0 <=? addr) &&
              (addr <? memAddr x0 + memSize x0) &&
              (addr + x <=? memSize x0))%bool; subst;
    simplify_ensembles; inv H0; subst; trivial;
    [| apply (H3 off val1 val2); assumption ].
    unfold Ensembles.In in *; simpl in *.
    destruct ((addr <=? off) && (off <? addr + x))%bool;
    [| apply (H3 off val1 val2); assumption ].
    destruct H, H4; subst.
    reflexivity.
Qed.

Definition found_block
           (addr : N)
           (addr' len' : N)
           (data' : Ensemble (N * Word8))
           (mem : Ensemble MemoryBlock) : Prop :=
  In _ mem {| memAddr := addr'
            ; memSize := len'
            ; memData := data' |}
  -> within addr' len' addr.

Definition no_block (addr : N) (mem : Ensemble MemoryBlock) : Prop :=
  forall addr' len' data',
    In _ mem {| memAddr := addr'
              ; memSize := len'
              ; memData := data' |}
    -> ~ within addr' len' addr.

Definition HeapSpec := Def ADT {
  (* a mapping of addr tokens to a length, and another mapping from
     offsets within a certain block to individual bytes *)
  rep := Ensemble MemoryBlock,

  Def Constructor0 emptyS : rep := ret (Empty_set _),,

  Def Method1 allocS (r : rep) (len : N | 0 < len) : rep * N :=
    addr <- { addr : N
            | forall addr' len' data',
                In _ r {| memAddr := addr'
                        ; memSize := len'
                        ; memData := data' |}
                -> ~ overlaps addr (proj1_sig len) addr' len' };
    ret (Add _ r {| memAddr := addr
                  ; memSize := proj1_sig len
                  ; memData := Empty_set _ |}, addr),

  Def Method1 freeS (r : rep) (addr : N) : rep * unit :=
    ret (Setminus _ r (fun p => addr = memAddr p), tt),

  Def Method2 reallocS (r : rep) (addr : N) (len : N | 0 < len) :
    rep * N :=
    naddr <- { naddr : N
             | forall addr' len' data',
                 In _ r {| memAddr := addr'
                         ; memSize := len'
                         ; memData := data' |}
                 -> IF addr = addr'
                    then proj1_sig len < len'
                    else ~ overlaps naddr (proj1_sig len) addr' len' };
    ret (fit_to_length naddr len (shift_address addr naddr r),
         naddr),

  Def Method1 peekS (r : rep) (addr : N) : rep * Word8 :=
    p <- { p : Word8
         | forall base len' data',
             found_block addr base len' data' r
             -> In _ data' (addr - base, p) };
    ret (r, p),

  Def Method2 pokeS (r : rep) (addr : N) (w : Word8) : rep * bool :=
    res <- set_address addr w r;
    ret (ret (fst res), snd res),

  (* A restriction is made here that data may only be copied from within one
     allocated block to another (or within the same original block), and that
     the region must fit within both source and destination. Otherwise, the
     operation is a no-op. *)
  Def Method3 memcpyS (r : rep) (addr : N) (addr2 : N) (len : N | 0 < len) :
    rep * bool :=
    res <- copy_memory addr addr2 len r;
    ret (ret (fst res), snd res),

  Def Method3 memsetS (r : rep) (addr : N) (len : N | 0 < len) (w : Word8) :
    rep * bool :=
    res <- set_memory addr len w r;
    ret (ret (fst res), snd res)

}%ADTParsing.

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
  Comp (Rep HeapSpec * bool) :=
  Eval simpl in callMeth HeapSpec pokeS r addr w.

Definition memcpy (r : Rep HeapSpec)
           (addr : N) (addr2 : N) (len : N | 0 < len) :
  Comp (Rep HeapSpec * bool) :=
  Eval simpl in callMeth HeapSpec memcpyS r addr addr2 len.

Definition memset (r : Rep HeapSpec)
           (addr : N) (len : N | 0 < len) (w : Word8) :
  Comp (Rep HeapSpec * bool) :=
  Eval simpl in callMeth HeapSpec memsetS r addr len w.

Theorem allocations_are_correction :
  forall r : Rep HeapSpec, fromADT _ r -> CorrectHeap r.
Proof.
  unfold CorrectHeap; intros.
  generalize dependent blk.
  ADT induction r.
  - constructor; inversion H0.
  - destruct x; simpl in *.
    inv H1.
      apply IHfromADT.
      exact H2.
    inv H2.
    constructor; simpl; trivial; intros; inv H1.
  - inv H1.
    exact (IHfromADT _ H0).
  - exact (fit_to_length_correct (@shift_address_correct _ IHfromADT _ _) H1).
  - destruct v; simpl in *; inv H1.
    exact (set_address_correct IHfromADT H0).
  - destruct v; simpl in *; inv H1.
    exact (copy_memory_correct IHfromADT H0).
  - destruct v; simpl in *; inv H1.
    exact (set_memory_correct IHfromADT H0).
Qed.

Theorem allocations_have_size : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr len data,
    Ensembles.In _ r {| memAddr := addr
                      ; memSize := len
                      ; memData := data |} -> 0 < len.
Proof.
  intros.
  generalize dependent data.
  generalize dependent len.
  generalize dependent addr.
  ADT induction r.
  - inversion H0.
  - simplify_ensembles.
      exact (IHfromADT _ _ _ H2).
    destruct x; trivial.
  - simplify_ensembles; intros.
    exact (IHfromADT _ _ _ H0).
  - destruct x0; simpl in *.
    unfold fit_to_length, shift_address, IfDec_Then_Else in H1; simpl in H1.
    simplify_ensembles; simpl in *.
    destruct (x1 =? (if x =? memAddr x3 then x1 else memAddr x3)); inv H4.
      assumption.
    apply (@IHfromADT (memAddr x3) (memSize x3) (memData x3)).
    destruct x3.
    exact H1.
  - unfold set_address, IfDec_Then_Else in H0; simpl in H0.
    simplify_ensembles.
    destruct ((memAddr x1 <=? x) && (x <? memAddr x1 + memSize x1))%bool;
    inv H1; simpl in *; inv H2.
      apply (@IHfromADT (memAddr x1) (memSize x1) (memData x1)).
      destruct x1.
      exact H0.
    exact (IHfromADT _ _ _ H0).
  - destruct x1; simpl in *.
    unfold copy_memory, IfDec_Then_Else in H0; simpl in H0.
    simplify_ensembles.
    destruct ((memAddr x2 <=? x0) &&
              (x0 <? memAddr x2 + memSize x2) &&
              (x0 + x1 <=? memSize x2))%bool;
    simplify_ensembles.
      destruct ((memAddr x3 <=? x) &&
                (x <? memAddr x3 + memSize x3) &&
                (x + x1 <=? memSize x3))%bool;
      inv H3; simpl in *; inv H2.
        apply (@IHfromADT (memAddr x2) (memSize x2) (memData x2)).
        destruct x2.
        exact H0.
      exact (IHfromADT _ _ _ H0).
    inv H1; simpl in *; inv H2.
    exact (IHfromADT _ _ _ H0).
  - destruct x0; simpl in *.
    unfold set_memory, IfDec_Then_Else in H0; simpl in H0.
    simplify_ensembles.
    destruct ((memAddr x2 <=? x) &&
              (x <? memAddr x2 + memSize x2) &&
              (x + x0 <=? memSize x2))%bool;
    inv H1; simpl in *; inv H2.
      apply (@IHfromADT (memAddr x2) (memSize x2) (memData x2)).
      destruct x2.
      exact H0.
    exact (IHfromADT _ _ _ H0).
Qed.

Theorem allocations_unique : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr len1 data1 len2 data2,
       Ensembles.In _ r {| memAddr := addr
                         ; memSize := len1
                         ; memData := data1 |}
    -> Ensembles.In _ r {| memAddr := addr
                         ; memSize := len2
                         ; memData := data2 |}
    -> len1 = len2 /\ data1 = data2.
Proof.
  intros.
  generalize dependent data2.
  generalize dependent len2.
  generalize dependent data1.
  generalize dependent len1.
  ADT induction r.
  - inversion H0.
  - destruct x; simpl in *.
    simplify_ensembles;
    first [ exact (proj1 (IHfromADT _ _ H2 _ _ H3))
          | exact (proj2 (IHfromADT _ _ H2 _ _ H3))
          | specialize (H0 _ _ _ H3);
            apply (allocations_have_size H) in H3;
            contradiction (overlaps_irr addr l H3)
          | specialize (H0 _ _ _ H2);
            apply (allocations_have_size H) in H2;
            contradiction (overlaps_irr addr l H2) ].
  - simplify_ensembles;
    first [ exact (proj1 (IHfromADT _ _ H2 _ _ H0))
          | exact (proj2 (IHfromADT _ _ H2 _ _ H0)) ].
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Theorem allocations_no_overlap : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr1 len1 data1 addr2 len2 data2,
       Ensembles.In _ r {| memAddr := addr1
                         ; memSize := len1
                         ; memData := data1 |}
    -> Ensembles.In _ r {| memAddr := addr2
                         ; memSize := len2
                         ; memData := data2 |}
    -> addr1 <> addr2
    -> ~ overlaps addr1 len1 addr2 len2.
Proof.
  intros.
  generalize dependent data2.
  generalize dependent len2.
  generalize dependent addr2.
  generalize dependent data1.
  generalize dependent len1.
  generalize dependent addr1.
  ADT induction r.
  - inversion H0.
  - simplify_ensembles.
    + exact (IHfromADT _ _ _ H3 _ H2 _ _ H4).
    + exact (H0 _ _ _ H4).
    + specialize (H0 _ _ _ H3); clear IHfromADT H3.
      unfold not; intros.
      apply overlaps_sym in H1.
      contradiction.
  - simplify_ensembles.
    exact (IHfromADT _ _ _ H3 _ H2 _ _ H0).
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

End Heap.