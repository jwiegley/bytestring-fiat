Require Import
  Fiat.ADT
  Fiat.ADTNotation
  Here.TupleEnsembles
  Here.Nomega
  Here.Decidable
  Here.BindDep
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
  memData : Ensemble (N * Word8)
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

Ltac inspect :=
  repeat (
    teardown; tsubst; simpl in *; decisions;
    try match goal with
      | [ H1 : ~ overlaps ?X ?Y ?X ?Z,
          H2 : 0 < ?Y,
          H3 : 0 < ?Z |- _ ] => pose proof (overlaps_irr X H2 H3); contradiction
      | [ H : ~ overlaps ?X ?Y ?A ?B |- ~ overlaps ?A ?B ?X ?Y ] =>
        let H0 := fresh "H0" in
        unfold not; intro H0; apply overlaps_sym in H0; contradiction
    end).

Definition HeapSpec := Def ADT {
  (* a mapping of addr tokens to a length, and another mapping from
     offsets within a certain block to individual bytes *)
  rep := Ensemble (N * MemoryBlock),

  Def Constructor0 emptyS : rep := ret Empty,,

  (* Allocation returns the address for the newly allocated block. Note that
     conditions such as out-of-memory are not handled here; the final
     implementation must decide how to handle this operationally, such as
     throwing an exception. *)
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
     bytes moved. *)
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
      Then IfDec naddr = addr
           Then Modify addr
                  (fun blk =>
                     {| memSize := ` len
                      ; memData := IfDec memSize blk < ` len
                                   Then memData blk
                                   Else Filter (fun pos _ => pos < ` len)
                                               (memData blk) |}) r
           Else Update naddr (IfDec memSize blk < ` len
                              Then blk
                              Else (* No copy is done because it does not fit *)
                                   {| memSize := ` len
                                    ; memData := Empty |}) (Remove addr r)
      Else Update naddr {| memSize := ` len
                         ; memData := Empty |} r,
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
             Lookup base blk' r
               -> within base (memSize blk') addr
               -> forall v, Lookup (addr - base) v (memData blk')
               -> p = v };
    ret (r, p),

  (* Poking an unallocated address is a no-op and returns false. *)
  Def Method2 pokeS (r : rep) (addr : N) (w : Word8) : rep * unit :=
    ret (Map (fun base blk =>
                IfDec within base (memSize blk) addr
                Then {| memSize := memSize blk
                      ; memData := Update (addr - base) w (memData blk) |}
                Else blk) r, tt),

  (* Data may only be copied from one allocated block to another (or within
     the same block), and the region must fit within both source and
     destination. Otherwise, the operation is a no-op and returns false. *)
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
           Update daddr {| memSize := memSize dblk
                         ; memData :=
                             let soff := addr1 - saddr in
                             let doff := addr2 - daddr in
                             Overlay (fun a =>
                                        IfDec within doff len a
                                        Then Some (soff + (a - doff))
                                        Else None)
                                     (memData dblk) (memData sblk) |} r
         | _, _ => r
         end, tt),

  (* Any attempt to memset bytes outside of an allocated block is a no-op that
     returns false. *)
  Def Method3 memsetS (r : rep) (addr : N) (len : N) (w : Word8) :
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
  ADT induction r; [inversion H0|..];
  complete IHfromADT.
Qed.

Theorem allocations_correct_offsets : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr blk, Lookup addr blk r ->
    forall off, Member off (memData blk) -> off < memSize blk.
Proof.
  intros.
  generalize dependent off.
  generalize dependent blk.
  generalize dependent addr.
  ADT induction r; [inversion H0|..]; inspect;
  complete IHfromADT.
  - apply (IHfromADT x) in H2; trivial; nomega.
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
  forall addr blk1, Lookup addr blk1 r ->
  forall blk2, Lookup addr blk2 r -> blk1 = blk2.
Proof.
  intros.
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

Ltac lookup_uid H :=
  match goal with
  | [ H1 : Lookup ?A ?X ?R, H2 : Lookup ?A ?Y ?R |- _ ] =>
    pose proof (allocations_unique H _ _ H1 _ H2); subst
  end; inspect; auto.

Corollary allocations_unique_r : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr1 blk, Lookup addr1 blk r ->
  forall addr2, ~ Member addr2 r -> addr1 <> addr2.
Proof.
  unfold not; intros; subst; ADT induction r;
  contradiction H1;
  exists blk;
  assumption.
Qed.

Corollary not_overlaps_trans : forall a b x y z,
  z < y -> ~ overlaps a b x y -> ~ overlaps a b x z.
Proof. unfold overlaps; intros; nomega. Qed.

Theorem allocations_no_overlap : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr1 blk1, Lookup addr1 blk1 r ->
  forall addr2 blk2, Lookup addr2 blk2 r
    -> addr1 <> addr2 -> ~ overlaps addr1 (memSize blk1) addr2 (memSize blk2).
Proof.
  intros.
  pose proof (allocations_have_size H _ _ H0).
  pose proof (allocations_have_size H _ _ H1).
  generalize dependent blk2.
  generalize dependent addr2.
  generalize dependent blk1.
  generalize dependent addr1.
  ADT induction r; [inversion H0|..];
  complete IHfromADT;
  try lookup_uid H;
  first [ eapply All_Remove_Lookup_inv with (a':=addr1) in H0'; eauto
        | eapply All_Remove_Lookup_inv with (a':=addr2) in H0'; eauto ];
  try (apply not_overlaps_sym; assumption).
  - undecide; eapply not_overlaps_trans; eauto.
  - apply not_overlaps_sym.
    undecide; eapply not_overlaps_trans; eauto.
  - eapply allocations_unique_r in H0; eauto.
  - eapply allocations_unique_r in H0; eauto.
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
  split; intros; inspect.
    destruct (N.eq_dec base a); subst.
      specialize (H3 _ H5); subst.
      inspect.
    specialize (H2 _ _ H5 n).
    unfold overlaps, within in *; nomega.
  split; trivial.
Qed.

Corollary allocations_disjoint : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr blk, Lookup addr blk r
    -> forall pos, within addr (memSize blk) pos
    -> forall addr' blk', Lookup addr' blk' r
         -> addr <> addr'
         -> ~ within addr' (memSize blk') pos.
Proof.
  intros.
  pose proof (allocations_no_overlap H _ H0 _ H2 H3).
  unfold within, overlaps in *; nomega.
Qed.

Require Import Here.TupleEnsemblesFinite.

Theorem finite_heap : forall r : Rep HeapSpec, fromADT _ r -> Finite _ r.
Proof. intros; ADT induction r; inspect; finitary. Qed.

Theorem finite_blocks : forall r : Rep HeapSpec, fromADT _ r ->
  All (fun _ blk => Finite _ (memData blk)) r.
Proof.
  unfold All; intros.
  generalize dependent b.
  generalize dependent a.
  ADT induction r; inspect; finitary.
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
