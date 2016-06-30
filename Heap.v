Require Import
  Fiat.ADT
  Fiat.ADTNotation
  Fiat.ADTInduction
  Here.Nomega
  Here.Decidable
  Here.BindDep
  Here.FunRelation
  Here.Tactics.

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

Program Definition copy_memory
        (addr1 addr2 : N) (len : N | 0 < len) (mem : Heap) : Heap :=
  mkFunRel
    (p <- relEns mem;
     let (daddr, dst) := p in
     IfDec fits daddr (memSize dst) addr2 (` len)
     Then (
       src <- relEns mem;
       let (saddr, src) := p in
       ret (IfDec fits saddr (memSize src) addr1 (` len)
            Then (daddr,
                  {| memSize := memSize dst
                   ; memData :=
                       let off1 := addr1 - saddr in
                       let off2 := addr2 - daddr in
                       Transfer (fun a =>
                                   IfDec within off1 (` len) a
                                   Then Some (off2 + (a - off1))
                                   Else None)
                                (memData src) (memData dst) |})
            Else p))
     Else ret p) _.
Obligation 1.
  destruct mem.
  simplify_ensembles;
  decisions;
  simplify_ensembles;
  simpl in *; tsubst;
  try destruct b';
  specialize (e _ _ _ H H0);
  clear H H0;
  subst; firstorder;
  simpl in *;
  nomega.
Qed.

Lemma copy_memory_correct `(_ : CorrectHeap mem) :
  forall addr1 addr2 len, CorrectHeap (copy_memory addr1 addr2 len mem).
Proof.
  against_definition copy_memory len
                     ltac:(unfold Ensembles.In in *; simpl in * ).
  specialize (H1 off); firstorder.
Qed.

Definition set_memory (addr : N) (len : N | 0 < len) (w : Word8) :
  Heap -> Heap :=
  Map (fun p =>
         let (base, blk) := p in
         IfDec fits base (memSize blk) addr (` len)
         Then {| memSize := memSize blk
               ; memData := Define (within (addr - base) (` len)) w
                                   (memData blk) |}
         Else blk).

Lemma set_memory_correct `(_ : CorrectHeap mem) :
  forall addr len w, CorrectHeap (set_memory addr len w mem).
Proof.
  against_definition set_memory len ltac:(unfold Ensembles.In in *; simpl in *).
Qed.

Definition found_block_at_base
           (addr' len' : N)
           (data' : FunRel N Word8) : Heap -> Prop :=
  Lookup addr' {| memSize := len'
                ; memData := data' |}.

Definition found_block
           (addr : N) (addr' len' : N) (data' : FunRel N Word8)
           (mem : Heap) : Prop :=
  found_block_at_base addr' len' data' mem /\ within addr' len' addr.

Definition no_block (addr : N) (mem : Heap) : Prop :=
  forall addr' len' data',
    found_block_at_base addr' len' data' mem /\ ~ within addr' len' addr.

Definition free_block (addr : N) : Heap -> Heap := Remove addr.

Lemma free_block_correct `(_ : CorrectHeap mem) :
  forall addr, CorrectHeap (free_block addr mem).
Proof.
  against_definition free_block len idtac.
Qed.

Definition find_free_block (len : N | 0 < len) (mem : Heap) : Comp N :=
  { addr : N | forall addr' len' data',
      found_block_at_base addr' len' data' mem
        -> ~ overlaps addr' len' addr (` len) }.

Lemma find_free_block_spec (len : N | 0 < len) `(_ : CorrectHeap r) :
  forall addr, find_free_block len r ↝ addr -> ~ Member addr r.
Proof.
  destruct len; simpl.
  unfold find_free_block, found_block_at_base; intros.
  unfold CorrectHeap in CorrectHeap0.
  apply Pick_inv in H; simpl in H.
  unfold not; intros.
  apply Member_Lookup in H0.
  destruct H0.
  assert (CorrectMemoryBlock x0)
    by exact (All_Lookup _ _ _ r CorrectHeap0 _ _ H0).
  destruct x0, H1; simpl in *.
  specialize (H _ _ _ H0).
  contradiction (overlaps_irr addr H1 l).
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
    naddr <- find_free_block len (free_block addr r);
    ret (fit_to_length naddr len (shift_address addr naddr r), naddr),

  (* Peeking an unallocated address allows any value to be returned. *)
  Def Method1 peekS (r : rep) (addr : N) : rep * Word8 :=
    p <- { p : Word8
         | forall base len' data',
             found_block addr base len' data' r
               (* There are three cases to consider here:
                  1. Peeking an allocated, initialized byte. This must
                     return the same byte that was last poke'd at that
                     position.
                  2. Peeking an allocated, uninitialized byte.
                  3. Peeking at an unallocated location. *)
               -> forall v, Lookup (addr - base) v data' -> p = v };
    ret (r, p),

  (* Poking an unallocated address is a no-op and returns false. *)
  Def Method2 pokeS (r : rep) (addr : N) (w : Word8) : rep * unit :=
    ret (set_address addr w r, tt),

  (* Data may only be copied from one allocated block to another (or within
     the same block), and the region must fit within both source and
     destination. Otherwise, the operation is a no-op and returns false. *)
  Def Method3 memcpyS (r : rep) (addr : N) (addr2 : N) (len : N | 0 < len) :
    rep * unit :=
    ret (copy_memory addr addr2 len r, tt),

  (* Any attempt to memset bytes outside of an allocated block is a no-op that
     returns false. *)
  Def Method3 memsetS (r : rep) (addr : N) (len : N | 0 < len) (w : Word8) :
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

Definition memcpy (r : Rep HeapSpec)
           (addr : N) (addr2 : N) (len : N | 0 < len) :
  Comp (Rep HeapSpec * unit) :=
  Eval simpl in callMeth HeapSpec memcpyS r addr addr2 len.

Definition memset (r : Rep HeapSpec)
           (addr : N) (len : N | 0 < len) (w : Word8) :
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
  - exact (fit_to_length_correct (@shift_address_correct _ IHfromADT _ _) H1).
  - exact (set_address_correct IHfromADT H1).
  - exact (copy_memory_correct IHfromADT H1).
  - exact (set_memory_correct IHfromADT H1).
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
  - teardown; tsubst.
      destruct x; simpl; assumption.
    firstorder.
  - firstorder.
  - destruct x0; simpl in *.
    destruct H1; destruct H1;
    tsubst; firstorder; simpl in *.
    inv H2; assumption.
  - unfold set_address in H1.
    teardown; destruct x1;
    decisions; firstorder;
    tsubst; firstorder.
  - unfold copy_memory, Lookup in H1, IHfromADT.
    simplify_ensembles; decisions;
    simplify_ensembles; decisions;
    try destruct m;
    try destruct m0; simpl in *;
    eapply IHfromADT; eassumption.
  - unfold set_memory in H1.
    teardown; destruct x2;
    decisions; firstorder;
    tsubst; firstorder.
Qed.

Theorem allocations_no_overlap : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr1 len1 data1 addr2 len2 data2,
       Lookup addr1 {| memSize := len1
                     ; memData := data1 |} r
    -> Lookup addr2 {| memSize := len2
                     ; memData := data2 |} r
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
    teardown; tsubst; simplify_ensembles.
    + eapply H0; eassumption.
    + rewrite overlaps_sym.
      eapply H0; eassumption.
    + eapply IHfromADT; eassumption.
  - unfold free_block in H1, H3.
    teardown; eapply IHfromADT; eassumption.
  - unfold fit_to_length, shift_address in H1, H3.
    unfold free_block, find_free_block, found_block_at_base in H0.
    teardown; tsubst; simplify_ensembles.
    + apply H0 with (data':=data1).
      apply Lookup_Remove with (a':=x); trivial.
    + rewrite overlaps_sym.
      apply H0 with (data':=data2).
      apply Lookup_Remove with (a':=x); trivial.
    + eapply IHfromADT; eassumption.
  - unfold set_address in H1, H3.
    teardown; decisions; tsubst;
    try destruct x1;
    try destruct x2; simpl in *;
    eapply IHfromADT; eassumption.
  - unfold copy_memory in H1, H3.
    unfold Lookup, relEns in *.
    simplify_ensembles; simpl in *; decisions;
    simplify_ensembles;
    try destruct m;
    try destruct m0;
    try destruct m1;
    try destruct m2;
    eapply IHfromADT; eassumption.
  - unfold set_memory in H1, H3.
    teardown; decisions; tsubst;
    try destruct x2;
    try destruct x3; simpl in *;
    eapply IHfromADT; eassumption.
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
