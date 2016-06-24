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
  split; intros.
    apply N.le_refl.
  apply N.lt_add_pos_r.
  assumption.
Qed.

Definition fits (addr1 len1 addr2 len2 : N) : Prop :=
  within addr1 len1 addr2 /\ within addr1 len1 (addr2 + len2).

Definition overlaps (addr len addr2 len2 : N) : Prop :=
  addr < addr2 + len2 /\ addr2 < addr + len.

Lemma overlaps_sym : forall addr1 len1 addr2 len2,
  overlaps addr1 len1 addr2 len2 <-> overlaps addr2 len2 addr1 len1.
Proof.
  split; intros;
  destruct H; split; assumption.
Qed.

Lemma overlaps_irr : forall addr len1 len2,
  0 < len1 -> 0 < len2 -> overlaps addr len1 addr len2.
Proof.
  split; intros;
  apply N.lt_add_pos_r; assumption.
Qed.

Ltac decisions :=
  repeat
    match goal with
    | [ H : context [if ?B then _ else _] |- _ ] =>
      let Heqe := fresh "Heqe" in
      destruct B eqn:Heqe
    | [ |- context [if ?B then _ else _] ] =>
      let Heqe := fresh "Heqe" in
      destruct B eqn:Heqe

    | [ H : context[@IfDec_Then_Else _ _ _ _ _] |- _ ] =>
      unfold IfDec_Then_Else in H; simpl in H
    | [ |- context[@IfDec_Then_Else _ _ _ _ _] ] =>
      unfold IfDec_Then_Else; simpl
    end.

Ltac undecide :=
  repeat
    match goal with
    | [ H : (_ <? _)  = true  |- _ ] => apply N.ltb_lt in H
    | [ H : (_ <? _)  = false |- _ ] => apply N.ltb_ge in H
    | [ H : (_ <=? _) = true  |- _ ] => apply N.leb_le in H
    | [ H : (_ <=? _) = false |- _ ] => apply N.leb_gt in H
    | [ H : (_ =? _)  = true  |- _ ] => apply N.eqb_eq in H; subst
    | [ H : (_ =? _)  = false |- _ ] => apply N.eqb_neq in H

    | [ |- (_ <? _)  = true  ] => apply N.ltb_lt
    | [ |- (_ <? _)  = false ] => apply N.ltb_ge
    | [ |- (_ <=? _) = true  ] => apply N.leb_le
    | [ |- (_ <=? _) = false ] => apply N.leb_gt
    | [ |- (_ =? _)  = true  ] => apply N.eqb_eq
    | [ |- (_ =? _)  = false ] => apply N.eqb_neq
    end.

Ltac nomega_reduce :=
  repeat (
    match goal with
    | [ H : (_ && _)%bool = true |- _ ] =>
      apply Bool.andb_true_iff in H; destruct H
    | [ H : (_ && _)%bool = false |- _ ] =>
      apply Bool.andb_false_iff in H; destruct H

    | [ H : _ <  _ <  _ |- _ ] => destruct H
    | [ H : _ <= _ <  _ |- _ ] => destruct H
    | [ H : _ <  _ <= _ |- _ ] => destruct H
    | [ H : _ <= _ <= _ |- _ ] => destruct H

    | [ |- _ <  _ <  _ ] => split
    | [ |- _ <= _ <  _ ] => split
    | [ |- _ <  _ <= _ ] => split
    | [ |- _ <= _ <= _ ] => split

    | [ H : ?N < ?M |- ?N < ?M + ?O ] => apply (N.lt_lt_add_r _ _ _ H)
    | [ H : 0 < ?M  |- ?N < ?N + ?M ] => apply (N.lt_add_pos_r _ _ H)

    | [ H : context[Z.of_N (_ + _)] |- _ ] => rewrite N2Z.inj_add in H
    | [ H : context[Z.of_N (_ - _)] |- _ ] => rewrite N2Z.inj_sub in H; trivial

    | [ |- context[Z.of_N (_ + _)] ] => rewrite N2Z.inj_add
    | [ |- context[Z.of_N (_ - _)] ] => rewrite N2Z.inj_sub

    | [ H : _ = _ |- _ ] => subst

    | [ H : context[_ < _]  |- _ ] => rewrite N2Z.inj_lt in H
    (* | [ H : context[_ = _]  |- _ ] => apply N2Z.inj_iff in H *)
    (* | [ H : context[_ <> _] |- _ ] => apply N2Z.inj_iff in H *)

    (* We need to give _ <= _ alone a chance to be used by N2Z.inj_sub. *)
    | [ H : context[_     <= _ + _] |- _ ] => rewrite N2Z.inj_le in H
    | [ H : context[_ + _ <= _    ] |- _ ] => rewrite N2Z.inj_le in H
    | [ H : context[_ + _ <= _ + _] |- _ ] => rewrite N2Z.inj_le in H
    | [ H : context[_     <= _    ] |- _ ] => rewrite N2Z.inj_le in H

    | [ |- context[_ < _]  ] => rewrite N2Z.inj_lt
    | [ |- context[_ <= _] ] => rewrite N2Z.inj_le
    | [ |- context[_ = _]  ] => apply N2Z.inj_iff
    | [ |- context[_ <> _] ] => apply N2Z.inj_iff
    end; undecide).

Ltac nomega := solve [ nomega_reduce; abstract omega ].

Lemma overlaps_within : forall addr1 len1 addr2 len2,
  0 < len1 -> overlaps addr1 len1 addr2 len2
                <-> IfDec addr1 < addr2
                    Then within addr1 len1 addr2
                    Else within addr2 len2 addr1.
Proof.
  unfold overlaps, within.
  split; intros.
    destruct H0.
    decisions; nomega.
  decisions;
  destruct H0.
    nomega.
  split; trivial.
  undecide.
  apply N.lt_eq_cases in Heqe.
  destruct Heqe; nomega.
Qed.

Corollary not_overlaps_within : forall addr1 len1 addr2 len2,
  0 < len1 -> ~ overlaps addr1 len1 addr2 len2
                <-> IfDec addr1 < addr2
                    Then ~ within addr1 len1 addr2
                    Else ~ within addr2 len2 addr1.
Proof.
  split; intros.
    decisions;
    unfold not; intros;
    apply H0, overlaps_within; trivial;
    decisions; firstorder.
  unfold not; intros;
  apply overlaps_within in H1; trivial;
  decisions; firstorder.
Qed.

Record MemoryBlock := {
  memAddr : N;
  memSize : N;
  memData : Ensemble (N * Word8)
}.

Ltac tsubst :=
  repeat
    match goal with
    | [ H : (_, _) = (_, _) |- _ ] => inv H
    | [ H : (_, _, _) = (_, _, _) |- _ ] => inv H
    | [ H : (_, _, _, _) = (_, _, _, _) |- _ ] => inv H
    | [ H : {| memAddr := _
             ; memSize := _
             ; memData := _ |} =
            {| memAddr := _
             ; memSize := _
             ; memData := _ |} |- _ ] => inv H
    end;
  subst.

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

Ltac against_definition function len CorrectHeap0 x0 H tac :=
  unfold function; intros;
  try destruct len; simpl in *;
  simplify_ensembles;
  decisions;
  simplify_ensembles;
  [| tsubst; firstorder ];
  try (destruct (CorrectHeap0 x0 H); clear H);
  constructor; intros; decisions; tsubst;
  tac; decisions; try nomega; firstorder.

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
  against_definition shift_address len CorrectHeap0 x0 H idtac.
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
  against_definition fit_to_length len CorrectHeap0 x0 H idtac.
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
  against_definition set_address len CorrectHeap0 x0 H simplify_ensembles.
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
                      let off := addr2 - memAddr dst in
                      IfDec within off (proj1_sig len) (fst p)
                      Then memData src (addr2 + (fst p - addr1), snd p)
                      Else memData dst p |}, true)
         Else (dst, false))
  )
  Else ret (dst, false).

Lemma copy_memory_correct `(_ : CorrectHeap mem) :
  forall addr1 addr2 len blk' b, copy_memory addr1 addr2 len mem ↝ (blk', b)
    -> CorrectMemoryBlock blk'.
Proof.
  against_definition copy_memory len CorrectHeap0 x0 H
                     ltac:(unfold Ensembles.In in *; simpl in *).
Qed.

Definition set_memory (addr : N) (len : N | 0 < len) (w : Word8)
           (mem : Ensemble MemoryBlock) : Comp (MemoryBlock * bool) :=
  blk <- mem;
  ret (IfDec fits (memAddr blk) (memSize blk) addr (proj1_sig len)
       Then ({| memAddr := memAddr blk
              ; memSize := memSize blk
              ; memData := fun p =>
                             let off := addr - memAddr blk in
                             IfDec within off (proj1_sig len) (fst p)
                             Then snd p = w
                             Else memData blk p |}, true)
       Else (blk, false)).

Lemma set_memory_correct `(_ : CorrectHeap mem) :
  forall addr len w blk' b, set_memory addr len w mem ↝ (blk', b)
    -> CorrectMemoryBlock blk'.
Proof.
  against_definition set_memory len CorrectHeap0 x0 H
                     ltac:(unfold Ensembles.In in *; simpl in *).
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
  unfold free_block; intros.
  constructor; trivial.
  unfold not; intros.
  unfold Ensembles.In in *.
  apply N.eqb_neq in H0.
  contradiction.
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
      exact (IHfromADT _ H2).
    simplify_ensembles.
    constructor; firstorder.
  - inv H1; firstorder.
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
  unfold found_block_at_base; intros.
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
    unfold fit_to_length, shift_address in H1; simpl in H1.
    simplify_ensembles; decisions; tsubst; trivial.
      undecide; tauto.
    destruct x3.
    exact (IHfromADT _ _ _ H1).
  - unfold set_address in H0;
    simplify_ensembles; decisions; simpl in *; tsubst;
    try destruct x1;
    exact (IHfromADT _ _ _ H0).
  - destruct x1; simpl in *.
    unfold copy_memory in H0;
    simplify_ensembles; decisions; simpl in *; tsubst;
    simplify_ensembles; decisions; simpl in *; tsubst;
    try destruct x2;
    exact (IHfromADT _ _ _ H0).
  - destruct x0; simpl in *.
    unfold set_memory in H0;
    simplify_ensembles; decisions; simpl in *; tsubst;
    try destruct x2;
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
  - destruct x; simpl in *.
    unfold find_free_block, found_block_at_base in H0.
    pose proof (within_refl addr l) as H9.
    simplify_ensembles;
    first
      [ exact (proj1 (IHfromADT _ _ _ H2 _ _ H3))
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
  - simplify_ensembles.
      exact (proj1 (IHfromADT _ _ _ H2 _ _ H0)).
    exact (proj2 (IHfromADT _ _ _ H2 _ _ H0)).
  - destruct x0; simpl in *.
    unfold find_free_block, no_block in H0.
    simplify_ensembles; decisions; simpl in *; tsubst; trivial;
    destruct x3, x4; simpl in *; subst; undecide; try tauto;
    try (rewrite (proj1 (IHfromADT _ _ _ H1 _ _ H2)); reflexivity);
    try (rewrite (proj2 (IHfromADT _ _ _ H1 _ _ H2)); reflexivity);
    unfold found_block_at_base in H0.
    + pose proof (allocations_have_size H _ _ _ H2) as H3.
      apply N.eqb_neq in Heqe2.
      apply (free_block_impl memAddr1) in H2; trivial.
      specialize (H0 _ _ _ H2).
      apply not_overlaps_within in H0; trivial.
      unfold IfDec_Then_Else in H0; simpl in H0.
      rewrite N.ltb_irrefl in H0.
      contradiction (within_refl memAddr0 l).
    + pose proof (allocations_have_size H _ _ _ H1) as H3.
      apply N.eqb_neq in Heqe0.
      apply (free_block_impl memAddr0) in H1; trivial.
      specialize (H0 _ _ _ H1).
      apply not_overlaps_within in H0; trivial.
      unfold IfDec_Then_Else in H0; simpl in H0.
      rewrite N.ltb_irrefl in H0.
      contradiction (within_refl memAddr1 l).
  - unfold set_address in H0;
    simplify_ensembles; decisions; simpl in *; tsubst; reflexivity.
  - unfold copy_memory in H0;
    simplify_ensembles; decisions; simpl in *; tsubst;
    simplify_ensembles; decisions; simpl in *; tsubst; reflexivity.
  - unfold set_memory in H0;
    simplify_ensembles; decisions; simpl in *; tsubst; reflexivity.
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
  - unfold find_free_block, no_block in H0.
    simplify_ensembles; decisions; simpl in *; tsubst.
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
    simplify_ensembles; decisions; simpl in *; tsubst; trivial;
    destruct x3, x4; simpl in *; subst; undecide; try tauto;
    try (eapply IHfromADT; eassumption);
    first [ rewrite overlaps_sym; apply H0 with (data':=memData0)
          | apply H0 with (data':=memData1) ];
    apply free_block_impl; trivial;
    apply N.eqb_neq; tauto.
  - unfold set_address in H0.
    simplify_ensembles; decisions; simpl in *; tsubst; tauto.
  - unfold copy_memory in H0;
    simplify_ensembles; decisions; simpl in *; tsubst;
    simplify_ensembles; decisions; simpl in *; tsubst; tauto.
  - unfold set_memory in H0;
    simplify_ensembles; decisions; simpl in *; tsubst; tauto.
Qed.

End Heap.
