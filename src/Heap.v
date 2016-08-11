Require Import
  Fiat.ADT
  Fiat.ADTNotation
  Here.TupleEnsembles
  Here.LibExt
  Here.Nomega
  Here.Decidable
  Here.BindDep
  Here.ADTInduction
  Here.Same_set
  Here.TupleEnsemblesFinite.

Generalizable All Variables.

Open Scope string_scope.

Module Type Memory.
  Parameter Word8 : Type.
  Parameter Zero  : Word8.
End Memory.

Module Heap (Mem : Memory).

Record MemoryBlock := {
  memSize : N;
  memData : Ensemble (N * Mem.Word8)
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

Definition KeepKeys (P : N -> Prop) :
  Ensemble (N * Mem.Word8) -> Ensemble (N * Mem.Word8) :=
  Filter (fun k _ => P k).

Definition ShiftKeys (orig_base : N) (new_base : N) :
  Ensemble (N * Mem.Word8) -> Ensemble (N * Mem.Word8) :=
  Map_set (fun p => (fst p - orig_base + new_base, snd p)).

Ltac inspect :=
  repeat (unfold KeepKeys, ShiftKeys in *;
          repeat teardown; tsubst; simpl in *;
          decisions; eauto with sets;
          try congruence).

Definition emptyS   := "empty".
Definition allocS   := "alloc".
Definition reallocS := "realloc".
Definition freeS    := "free".
Definition peekS    := "peek".
Definition pokeS    := "poke".
Definition memcpyS  := "memcpy".
Definition memsetS  := "memset".

Definition HeapSpec := Def ADT {
  (* Map of memory addresses to blocks, which contain another mapping from
     offsets to initialized bytes. *)
  rep := Ensemble (N * MemoryBlock),

  Def Constructor0 emptyS : rep := ret Empty,,

  (* Allocation returns the address for the newly allocated block.
     NOTE: conditions such as out-of-memory are not handled here; the final
     implementation must decide how to handle this operationally, such as by
     throwing an exception. It remains a further research question how to
     specify error handling at this level, when certain errors -- such as
     exhausting memory -- do not belong here, since a mathematical machine has
     no such limits. *)
  Def Method1 allocS (r : rep) (len : N | 0 < len) : rep * N :=
    addr <- { addr : N
            | All (fun addr' blk' =>
                     ~ overlaps addr' (memSize blk') addr (` len)) r };
    ret (Update addr {| memSize := ` len
                      ; memData := Empty |} r, addr),

  (* Freeing an unallocated block is a no-op. *)
  Def Method1 freeS (r : rep) (addr : N) : rep * unit :=
    ret (Remove addr r, tt),

  (* Realloc is not required to reuse the same block. If the address does not
     identify an allociated region, a new memory block is returned without any
     bytes moved. If a block did exist previously, as many bytes as possible
     are copied to the new block. *)
  Def Method2 reallocS (r : rep) (addr : N) (len : N | 0 < len) : rep * N :=
    present <- { blk : option MemoryBlock
               | Ifopt blk as blk'
                 Then Lookup addr blk' r
                 Else ~ Member addr r };
    naddr   <- { naddr : N
               | All (fun addr' blk' =>
                        ~ overlaps addr' (memSize blk') naddr (` len))
                     (Remove addr r) };
    ret (
      Ifopt present as blk
      Then Update naddr {| memSize := ` len
                         ; memData := Filter (fun pos _ => pos < ` len)
                                             (memData blk) |} (Remove addr r)
      Else Update naddr {| memSize := ` len
                         ; memData := Empty |} r,
      naddr),

  (* Peeking an unallocated address allows anydefault value to be returned. *)
  Def Method1 peekS (r : rep) (addr : N) : rep * Mem.Word8 :=
    p <- { p : Mem.Word8
         | forall base blk',
             (* There are three cases to consider here:
                1. Peeking an allocated, initialized byte. This must
                   return the same byte that was last poke'd at that
                   position.
                2. Peeking an allocated, uninitialized byte.
                3. Peeking at an unallocated location. *)
             Lookup base blk' r
               -> within base (memSize blk') addr
               -> forall v, Lookup (addr - base) v (memData blk')
               -> p = v };
    ret (r, p),

  (* Poking an unallocated address is a no-op. *)
  Def Method2 pokeS (r : rep) (addr : N) (w : Mem.Word8) : rep * unit :=
    ret (Map (fun base blk =>
                IfDec within base (memSize blk) addr
                Then {| memSize := memSize blk
                      ; memData := Update (addr - base) w (memData blk) |}
                Else blk) r, tt),

  (* Data may only be copied from one allocated block to another (or within
     the same block), and the region must fit within both source and
     destination. Otherwise, the operation is a no-op. *)
  Def Method3 memcpyS (r : rep) (addr1 : N) (addr2 : N) (len : N) :
    rep * unit :=
    ms <- { ms : option (N * MemoryBlock)
          | forall addr' blk', ms = Some (addr', blk') ->
              0 < len /\ Lookup addr' blk' r /\
              fits addr' (memSize blk') addr1 len };
    md <- { md : option (N * MemoryBlock)
          | forall addr' blk', md = Some (addr', blk') ->
              0 < len /\ Lookup addr' blk' r /\
              fits addr' (memSize blk') addr2 len };
    ret (match ms, md with
         | Some (saddr, sblk), Some (daddr, dblk) =>
           Update daddr
             {| memSize := memSize dblk
              ; memData :=
                  let soff := addr1 - saddr in
                  let doff := addr2 - daddr in
                  (* [s] is the source region to copy from *)
                  let s := KeepKeys (within soff len) (memData sblk) in
                  (* [d] has a hole where the region will be copied to *)
                  let d := KeepKeys (not ∘ within doff len) (memData dblk) in
                  Union _ d (ShiftKeys soff doff s) |} r
         | _, _ => r
         end, tt),

  (* Any attempt to memset bytes outside of an allocated block is a no-op. *)
  Def Method3 memsetS (r : rep) (addr : N) (len : N) (w : Mem.Word8) :
    rep * unit :=
    ret (Map (fun base blk =>
                IfDec fits base (memSize blk) addr len
                Then {| memSize := memSize blk
                      ; memData := Define (within (addr - base) len) w
                                          (memData blk) |}
                Else blk) r, tt)

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

Definition peek (r : Rep HeapSpec) (addr : N) :
  Comp (Rep HeapSpec * Mem.Word8) :=
  Eval simpl in callMeth HeapSpec peekS r addr.

Definition poke (r : Rep HeapSpec) (addr : N) (w : Mem.Word8) :
  Comp (Rep HeapSpec * unit) :=
  Eval simpl in callMeth HeapSpec pokeS r addr w.

Definition memcpy (r : Rep HeapSpec) (addr : N) (addr2 : N) (len : N) :
  Comp (Rep HeapSpec * unit) :=
  Eval simpl in callMeth HeapSpec memcpyS r addr addr2 len.

Definition memset (r : Rep HeapSpec) (addr : N) (len : N) (w : Mem.Word8) :
  Comp (Rep HeapSpec * unit) :=
  Eval simpl in callMeth HeapSpec memsetS r addr len w.

(**
 ** Theorems related to the Heap specification.
 **)

Ltac complete IHfromADT :=
  inspect;
  try match goal with
    [ H : (?X =? ?Y) = true |- _ ] => apply N.eqb_eq in H; subst
  end;
  try (eapply IHfromADT; eassumption);
  try solve [ eapply IHfromADT; try eassumption; inspect
            | try eapply IHfromADT; eassumption
            | inspect;
              try (unfold fits, within in *; inspect; nomega);
              eapply IHfromADT; try eassumption; inspect
            | discriminate ].

Theorem allocations_have_size : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr blk, Lookup addr blk r -> 0 < memSize blk.
Proof.
  intros.
  generalize dependent blk.
  generalize dependent addr.
  ADT induction r; [inversion H0|..]; complete IHfromADT.
Qed.

Theorem allocations_correct_offsets : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr blk, Lookup addr blk r ->
    All (fun off _ => off < memSize blk) (memData blk).
Proof.
  intros.
  generalize dependent blk.
  generalize dependent addr.
  ADT induction r; [inversion H0|..]; intros ???;
  complete IHfromADT.
Qed.

Ltac match_sizes H IHfromADT :=
  match goal with
  | [ H1 : Lookup ?A ?X ?R, H2 : Lookup ?B ?Y ?R |- _ ] =>
    specialize (IHfromADT _ _
                  H1 (allocations_have_size H _ _ H1) _
                  H2 (allocations_have_size H _ _ H2)); subst
  end; inspect; auto.

Ltac match_sizes_r H IHfromADT :=
  match goal with
  | [ H1 : Lookup ?A ?X ?R, H2 : Lookup ?B ?Y ?R |- _ ] =>
    try rewrite <- (IHfromADT _ _
                      H1 (allocations_have_size H _ _ H1) _
                      H2 (allocations_have_size H _ _ H2)) in *
  end; inspect; auto.

Ltac check_overlaps :=
  match goal with
    [ H1 : All (fun addr' blk' => ~ overlaps addr' (memSize blk') ?XA ?XL)
               (Remove ?YA ?R),
      H2 : ?XA <> ?YA,
      H3 : 0 < ?XL,
      H4 : Lookup ?XA ?B ?R,
      H5 : 0 < memSize ?B |- _ ] =>
    eapply All_Remove_Lookup_inv with (a':=XA) in H1; eauto;
    contradiction (overlaps_irr XA H5 H3)
  end.

Theorem allocations_unique : forall r : Rep HeapSpec, fromADT _ r ->
  Functional r.
Proof.
  unfold Functional; intros.
  pose proof (allocations_have_size H _ _ H0).
  pose proof (allocations_have_size H _ _ H1).
  generalize dependent blk2.
  generalize dependent blk1.
  generalize dependent addr.
  ADT induction r; [inversion H0|..]; inspect;
  try solve [ match_sizes H IHfromADT ];
  try discriminate;
  check_overlaps.
Qed.

Theorem all_block_maps_are_unique : forall r : Rep HeapSpec, fromADT _ r ->
  All (fun _ blk => Functional (memData blk)) r.
Proof.
  unfold All, Functional; intros.
  generalize dependent b.
  generalize dependent a.
  generalize dependent blk1.
  generalize dependent blk2.
  generalize dependent addr.
  ADT induction r; inspect.
  - unfold compose in *; nomega.
  - unfold compose in *; nomega.
  - apply N.add_cancel_r in H12.
    apply Nsub_eq in H12.
    + subst.
      clear H6.
      eapply IHfromADT; eauto.
    + nomega.
    + nomega.
  - inv H3; inv H4; congruence.
Qed.

Corollary allocations_unique_r : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr1 blk, Lookup addr1 blk r ->
  forall addr2, ~ Member addr2 r -> addr1 <> addr2.
Proof.
  unfold not; intros; subst; ADT induction r;
  contradiction H1;
  exists blk; assumption.
Qed.

Ltac lookup_uid H :=
  match goal with
  | [ H1 : Lookup ?A ?X ?R, H2 : Lookup ?A ?Y ?R |- _ ] =>
    pose proof (allocations_unique H _ _ H1 _ H2); subst
  end; inspect; auto.

Theorem allocations_no_overlap : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr1 blk1, Lookup addr1 blk1 r ->
  forall addr2 blk2, Lookup addr2 blk2 r
    -> addr1 <> addr2
    -> ~ overlaps addr1 (memSize blk1) addr2 (memSize blk2).
Proof.
  intros.
  pose proof (allocations_have_size H _ _ H0).
  pose proof (allocations_have_size H _ _ H1).
  generalize dependent blk2.
  generalize dependent addr2.
  generalize dependent blk1.
  generalize dependent addr1.
  ADT induction r; [inversion H0|..]; complete IHfromADT;
  try lookup_uid H; eapply All_Remove_Lookup_inv in H0'; eauto;
  try nomega; eapply allocations_unique_r in H0; eauto.
Qed.

Corollary find_partitions_a_singleton : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr base blk,
    Lookup base blk r
      -> within base (memSize blk) addr
      -> Same (Filter (fun a b => within a (memSize b) addr) r)
              (Single base blk).
Proof.
  intros.
  pose proof (allocations_no_overlap H _ H0).
  pose proof (allocations_unique H _ _ H0).
  split; intros; inspect;
  destruct (N.eq_dec base a); subst; auto.
  - specialize (H2 _ _ H5 n); nomega.
  - specialize (H3 _ H5); nomega.
  - specialize (H2 _ _ H5 n); nomega.
Qed.

Corollary allocations_disjoint : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr blk, Lookup addr blk r
    -> forall pos, within addr (memSize blk) pos
    -> forall addr' blk', Lookup addr' blk' r
         -> addr <> addr'
         -> ~ within addr' (memSize blk') pos.
Proof. intros; pose proof (allocations_no_overlap H _ H0 _ H2 H3); nomega. Qed.

Theorem heap_is_finite : forall r : Rep HeapSpec, fromADT _ r -> Finite _ r.
Proof. intros; ADT induction r; inspect; finite_preservation; nomega. Qed.

Lemma added : forall b e,
  b <= e -> Same_set _ (fun x : N => b <= x < N.succ e)
                       (Add _ (fun x : N => b <= x < e) e).
Proof.
  unfold Same_set, Included, Add, Ensembles.In.
  split; intros.
    destruct (N.eq_dec x e); subst.
      right; constructor.
    left; unfold Ensembles.In in *; nomega.
  inv H0; unfold Ensembles.In in *;
  destruct H1; nomega.
Qed.

Lemma not_added : forall b e,
  ~ b <= e -> Same_set _ (fun x : N => b <= x < N.succ e)
                         (fun x : N => b <= x < e).
Proof. unfold Same_set, Included, Add, Ensembles.In; nomega. Qed.

Lemma N_Finite : forall b e, Finite N (fun x : N => b <= x < e).
Proof.
  intros.
  induction e using N.peano_ind; intros.
    eapply Finite_downward_closed; eauto with sets.
    unfold Included, Ensembles.In; nomega.
  destruct (N.le_decidable b e).
    rewrite added; trivial.
    constructor; trivial.
    unfold Ensembles.In; nomega.
  rewrite not_added; trivial.
Qed.

Hint Extern 5 (Finite N (within _ _)) => apply N_Finite.

Theorem all_blocks_are_finite : forall r : Rep HeapSpec, fromADT _ r ->
  All (fun _ blk => Finite _ (memData blk)) r.
Proof.
  unfold All; intros.
  generalize dependent b.
  generalize dependent a.
  ADT induction r; inspect;
  finite_preservation;
  eauto; nomega.
Qed.

End Heap.
