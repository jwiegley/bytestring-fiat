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

Lemma within_refl : forall addr len,
  0 < len -> within addr len addr.
Proof.
  intros.
  unfold within.
  split.
    apply N.le_refl.
  apply N.lt_add_pos_r.
  assumption.
Qed.

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

Lemma overlaps_within : forall addr1 len1 addr2 len2,
  0 < len1 -> overlaps addr1 len1 addr2 len2
                <-> IfDec addr1 < addr2
                    Then within addr1 len1 addr2
                    Else within addr2 len2 addr1.
Proof.
  unfold overlaps, within, IfDec_Then_Else; simpl.
  split; intros.
    destruct H0.
    rewrite N2Z.inj_lt, N2Z.inj_add in H0, H1.
    destruct (addr1 <? addr2) eqn:Heqe.
      apply N.ltb_lt in Heqe.
      rewrite N2Z.inj_lt in Heqe.
      split.
        rewrite N2Z.inj_le;
        abstract omega.
      rewrite N2Z.inj_lt, N2Z.inj_add;
      abstract omega.
    apply N.ltb_ge in Heqe.
    rewrite N2Z.inj_le in Heqe.
    split.
      rewrite N2Z.inj_le;
      abstract omega.
    rewrite N2Z.inj_lt, N2Z.inj_add;
    abstract omega.
  destruct (addr1 <? addr2) eqn:Heqe;
  [ apply N.ltb_lt in Heqe
  | apply N.ltb_ge in Heqe ];
  destruct H0.
    split; trivial.
    apply N.lt_lt_add_r; assumption.
  split; trivial.
  apply N.lt_eq_cases in Heqe.
  destruct Heqe.
    apply N.lt_lt_add_r; assumption.
  subst.
  apply N.lt_add_pos_r; assumption.
Qed.

Corollary not_overlaps_within : forall addr1 len1 addr2 len2,
  0 < len1 -> ~ overlaps addr1 len1 addr2 len2
                <-> IfDec addr1 < addr2
                    Then ~ within addr1 len1 addr2
                    Else ~ within addr2 len2 addr1.
Proof.
  split; intros.
    unfold IfDec_Then_Else; simpl.
    destruct (addr1 <? addr2) eqn:Heqe;
    unfold not; intros;
    apply H0;
    apply overlaps_within; trivial;
    unfold IfDec_Then_Else; simpl;
    rewrite Heqe;
    assumption.
  unfold not; intros.
  apply overlaps_within in H1; trivial.
  unfold IfDec_Then_Else in *; simpl in *.
  destruct (addr1 <? addr2); contradiction.
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

Definition found_block_at_base
           (addr' len' : N)
           (data' : Ensemble (N * Word8))
           (mem : Ensemble MemoryBlock) : Prop :=
  In _ mem {| memAddr := addr'
            ; memSize := len'
            ; memData := data' |}.

Definition no_block (addr : N) (mem : Ensemble MemoryBlock) : Prop :=
  forall addr' len' data',
    In _ mem {| memAddr := addr'
              ; memSize := len'
              ; memData := data' |}
    -> ~ within addr' len' addr.

Definition free_block (addr : N) (mem : Ensemble MemoryBlock) :
  Ensemble MemoryBlock :=
  Setminus _ mem (fun p => addr = memAddr p).

Lemma free_block_impl (addr : N) (blk : MemoryBlock)
      (mem : Ensemble MemoryBlock) :
  In _ mem blk -> (addr =? memAddr blk) = false
    -> In _ (free_block addr mem) blk.
Proof.
  intros.
  unfold free_block.
  constructor; trivial.
  unfold not; intros.
  unfold Ensembles.In in *.
  apply N.eqb_eq in H1.
  rewrite H0 in H1.
  discriminate.
Qed.

Definition find_free_block (len : N | 0 < len)
           (mem : Ensemble MemoryBlock) : Comp N :=
  { addr : N | forall addr' len' data',
      found_block_at_base addr' len' data' mem
        -> ~ overlaps addr' len' addr (proj1_sig len) }.

Definition HeapSpec := Def ADT {
  (* a mapping of addr tokens to a length, and another mapping from
     offsets within a certain block to individual bytes *)
  rep := Ensemble MemoryBlock,

  Def Constructor0 emptyS : rep := ret (Empty_set _),,

  (* Allocation returns the address for the newly allocated block. Note that
     conditions such as out-of-memory are not handled here; the final
     implementation must decide how to handle this operationally, such as
     throwing an exception. *)
  Def Method1 allocS (r : rep) (len : N | 0 < len) : rep * N :=
    addr <- find_free_block len r;
    ret (Add _ r {| memAddr := addr
                  ; memSize := proj1_sig len
                  ; memData := Empty_set _ |}, addr),

  (* Freeing an unallocated block is a no-op. *)
  Def Method1 freeS (r : rep) (addr : N) : rep * unit :=
    ret (free_block addr r, tt),

  (* Realloc is not required to reuse the same block. If the address does not
     identify an allociated region, a new memory block is returned without any
     bytes moved. *)
  Def Method2 reallocS (r : rep) (addr : N) (len : N | 0 < len) : rep * N :=
    naddr <- find_free_block len (free_block addr r);
    ret (fit_to_length naddr len (shift_address addr naddr r), naddr),

  (* Peeking an unallocated address allows any value to be returned. *)
  Def Method1 peekS (r : rep) (addr : N) : rep * Word8 :=
    p <- { p : Word8
         | forall base len' data',
             found_block addr base len' data' r
               -> In _ data' (addr - base, p) };
    ret (r, p),

  (* Poking an unallocated address is a no-op and returns false. *)
  Def Method2 pokeS (r : rep) (addr : N) (w : Word8) : rep * bool :=
    res <- set_address addr w r;
    ret (ret (fst res), snd res),

  (* Data may only be copied from one allocated block to another (or within
     the same block), and the region must fit within both source and
     destination. Otherwise, the operation is a no-op and returns false. *)
  Def Method3 memcpyS (r : rep) (addr : N) (addr2 : N) (len : N | 0 < len) :
    rep * bool :=
    res <- copy_memory addr addr2 len r;
    ret (ret (fst res), snd res),

  (* Any attempt to memset bytes outside of an allocated block is a no-op that
     returns false. *)
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
    found_block_at_base addr len data r -> 0 < len.
Proof.
  unfold found_block_at_base.
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
  generalize dependent addr.
  ADT induction r.
  - inversion H0.
  - unfold find_free_block, found_block_at_base in H0.
    destruct x; simpl in *.
    pose proof (within_refl addr l) as H9.
    simplify_ensembles;
    first [ exact (proj1 (IHfromADT _ _ _ H2 _ _ H3))
          | exact (proj2 (IHfromADT _ _ _ H2 _ _ H3))
          | specialize (H0 _ _ _ H3);
            apply (allocations_have_size H) in H3;
            apply not_overlaps_within in H0; trivial;
            unfold IfDec_Then_Else in H0; simpl in H0;
            rewrite N.ltb_irrefl in H0;
            contradiction
          | specialize (H0 _ _ _ H2);
            apply (allocations_have_size H) in H2;
            apply not_overlaps_within in H0; trivial;
            unfold IfDec_Then_Else in H0; simpl in H0;
            rewrite N.ltb_irrefl in H0;
            contradiction ].
  - simplify_ensembles;
    first [ exact (proj1 (IHfromADT _ _ _ H2 _ _ H0))
          | exact (proj2 (IHfromADT _ _ _ H2 _ _ H0)) ].
  - unfold find_free_block, no_block in H0.
    destruct x0; simpl in *.
    rename x0 into len.
    rename x into oaddr.
    rename x1 into naddr.
    apply Pick_inv in H0.
    simplify_ensembles;
    unfold IfDec_Then_Else in *; simpl in *;
    destruct (oaddr =? memAddr x0) eqn:Heqe3;
    destruct (oaddr =? memAddr x1) eqn:Heqe4;
    rewrite ?N.eqb_refl in *; simpl in *;
    inv H5; inv H6; trivial.
    + destruct (addr =? memAddr x1) eqn:Heqe; inv H4.
        clear Heqe.
        reflexivity.
      apply N.eqb_neq in Heqe.
      tauto.
    + destruct (addr =? memAddr x0) eqn:Heqe; inv H4.
        clear Heqe.
        reflexivity.
      apply N.eqb_neq in Heqe.
      tauto.
    + destruct (naddr =? memAddr x0) eqn:Heqe1;
      destruct (naddr =? memAddr x1) eqn:Heqe2; inv H4; inv H5.
      * reflexivity.
      * rewrite H4 in Heqe2.
        apply N.eqb_eq in Heqe1.
        apply N.eqb_neq in Heqe2.
        contradiction.
      * rewrite H4 in Heqe2.
        apply N.eqb_neq in Heqe1.
        apply N.eqb_eq in Heqe2.
        contradiction.
      * destruct x0, x1; simpl in *.
        rewrite H4 in H1.
        exact (proj1 (IHfromADT _ _ _ H1 _ _ H2)).
    + extensionality p.
      f_equal.
      destruct x0, x1; simpl in *.
      apply N.eqb_eq in Heqe3;
      apply N.eqb_eq in Heqe4; subst.
      rewrite (proj2 (IHfromADT _ _ _ H1 _ _ H2)).
      reflexivity.
    + destruct (addr =? memAddr x1) eqn:Heqe2; inv H4.
        extensionality p.
        f_equal.
        destruct x1; simpl in *.
        pose proof (allocations_have_size H _ _ _ H1) as H3.
        unfold found_block_at_base in H0.
        apply (free_block_impl oaddr) in H1; trivial.
        specialize (H0 _ _ _ H1).
        apply not_overlaps_within in H0; trivial.
        unfold IfDec_Then_Else in H0; simpl in H0.
        rewrite N.ltb_irrefl in H0.
        contradiction (within_refl memAddr0 l).
      apply N.eqb_neq in Heqe2.
      tauto.
    + destruct (addr =? memAddr x0) eqn:Heqe2; inv H4.
        extensionality p.
        f_equal.
        destruct x0; simpl in *.
        pose proof (allocations_have_size H _ _ _ H2) as H3.
        unfold found_block_at_base in H0.
        apply (free_block_impl oaddr) in H2; trivial.
        specialize (H0 _ _ _ H2).
        apply not_overlaps_within in H0; trivial.
        unfold IfDec_Then_Else in H0; simpl in H0.
        rewrite N.ltb_irrefl in H0.
        contradiction (within_refl memAddr0 l).
      apply N.eqb_neq in Heqe2.
      tauto.
    + destruct (naddr =? memAddr x0) eqn:Heqe1;
      destruct (naddr =? memAddr x1) eqn:Heqe2; inv H4; inv H5.
      * extensionality p.
        f_equal.
        destruct x0, x1; simpl in *.
        rewrite H4 in H1.
        rewrite (proj2 (IHfromADT _ _ _ H1 _ _ H2)).
        reflexivity.
      * rewrite H4 in Heqe2.
        apply N.eqb_eq in Heqe1.
        apply N.eqb_neq in Heqe2.
        contradiction.
      * rewrite H4 in Heqe2.
        apply N.eqb_neq in Heqe1.
        apply N.eqb_eq in Heqe2.
        contradiction.
      * destruct x0, x1; simpl in *.
        rewrite H4 in H1.
        exact (proj2 (IHfromADT _ _ _ H1 _ _ H2)).
  - unfold set_address, IfDec_Then_Else in H0; simpl in H0.
    simplify_ensembles.
    destruct ((memAddr x1 <=? x) && (x <? memAddr x1 + memSize x1))%bool;
    inv H1; simpl in *; inv H2.
    + inv H3; reflexivity.
    + inv H1; reflexivity.
    + simpl in *; subst.
      inv H2; reflexivity.
  - destruct x1; simpl in *.
    unfold copy_memory, IfDec_Then_Else in H0; simpl in H0.
    simplify_ensembles;
    destruct ((memAddr x2 <=? x0) &&
              (x0 <? memAddr x2 + memSize x2) &&
              (x0 + x1 <=? memSize x2))%bool;
    simplify_ensembles;
    try (simpl in *; subst; inv H2; trivial).
  - destruct x0; simpl in *.
    unfold set_memory, IfDec_Then_Else in H0; simpl in H0.
    simplify_ensembles;
    destruct ((memAddr x2 <=? x) &&
              (x <? memAddr x2 + memSize x2) &&
              (x + x0 <=? memSize x2))%bool;
    simplify_ensembles;
    try (simpl in *; subst; inv H2; trivial).
Qed.

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
  - destruct x; simpl in *.
    unfold find_free_block, no_block in H0.
    simplify_ensembles; simpl in *.
    + exact (IHfromADT _ _ _ H3 _ H2 _ _ H4).
    + clear IHfromADT.
      unfold found_block_at_base in H0.
      specialize (H0 _ _ _ H4).
      rewrite overlaps_sym in H0.
      assumption.
    + clear IHfromADT.
      unfold found_block_at_base in H0.
      specialize (H0 _ _ _ H3).
      assumption.
  - simplify_ensembles.
    exact (IHfromADT _ _ _ H3 _ H2 _ _ H0).
  - unfold find_free_block, found_block_at_base in H0.
    destruct x0; simpl in *.
    rename x0 into len.
    rename x into oaddr.
    rename x1 into naddr.
    apply Pick_inv in H0.
    simplify_ensembles;
    unfold IfDec_Then_Else in *; simpl in *;
    destruct (oaddr =? memAddr x0) eqn:Heqe3;
    destruct (oaddr =? memAddr x1) eqn:Heqe4;
    rewrite ?N.eqb_refl in *; simpl in *;
    inv H6; inv H7; trivial.
    + tauto.
    + destruct (addr2 =? memAddr x1) eqn:Heqe; inv H5.
        apply N.eqb_eq in Heqe.
        firstorder.
      apply H0 with (data':=memData x1).
      apply free_block_impl; trivial.
      destruct x1; simpl in *.
      apply H1.
    + destruct (addr1 =? memAddr x0) eqn:Heqe; inv H5.
        apply N.eqb_eq in Heqe.
        firstorder.
      rewrite overlaps_sym.
      apply H0 with (data':=memData x0).
      apply free_block_impl; trivial.
      destruct x0; simpl in *.
      apply H3.
    + destruct (naddr =? memAddr x0) eqn:Heqe1;
      destruct (naddr =? memAddr x1) eqn:Heqe2; inv H5; inv H6.
      * apply N.eqb_eq in Heqe1;
        apply N.eqb_eq in Heqe2; subst.
        rewrite Heqe2 in H2.
        tauto.
      * apply N.eqb_eq in Heqe1; subst.
        apply H0 with (data':=memData x1).
        apply free_block_impl; trivial.
        destruct x1; simpl in *.
        apply H1.
      * apply N.eqb_eq in Heqe2; subst.
        rewrite overlaps_sym.
        apply H0 with (data':=memData x0).
        apply free_block_impl; trivial.
        destruct x0; simpl in *.
        apply H3.
      * apply IHfromADT with (data1:=memData x1) (data2:=memData x0); trivial.
          destruct x1; simpl in *.
          apply H1.
        destruct x0; simpl in *.
        apply H3.
  - unfold set_address, IfDec_Then_Else in H0.
    simplify_ensembles; simpl in *; subst; inv H3.
    destruct ((memAddr x1 <=? x) && (x <? memAddr x1 + memSize x1))%bool;
    inv H1; simpl in *;
    tauto.
  - destruct x1; simpl in *.
    unfold copy_memory, IfDec_Then_Else in H0; simpl in H0.
    simplify_ensembles; simpl in *; subst; inv H3.
    destruct ((memAddr x2 <=? x0) &&
              (x0 <? memAddr x2 + memSize x2) &&
              (x0 + x1 <=? memSize x2))%bool;
    simplify_ensembles;
    try (simpl in *; subst; inv H2; trivial).
  - destruct x0; simpl in *.
    unfold set_memory, IfDec_Then_Else in H0; simpl in H0.
    simplify_ensembles; simpl in *; subst; inv H3.
    destruct ((memAddr x2 <=? x) &&
              (x <? memAddr x2 + memSize x2) &&
              (x + x0 <=? memSize x2))%bool;
    simplify_ensembles;
    try (simpl in *; subst; inv H2; trivial).
Qed.

End Heap.
