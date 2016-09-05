Require Import
  ByteString.Tactics
  ByteString.Nomega
  ByteString.Memory
  ByteString.FMapExt
  ByteString.Fiat
  ByteString.HeapState
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Generalizable All Variables.

Module Heap (M : WSfun N_as_DT).

Module Import HeapState := HeapState M.

Import FMapExt.

Open Scope string_scope.

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
  rep := HeapState,

  Def Constructor0 emptyS : rep := ret newHeapState,,

  (* Allocation returns the address for the newly allocated block.
     NOTE: conditions such as out-of-memory are not handled here; the final
     implementation must decide how to handle this operationally, such as by
     throwing an exception. It remains a further research question how to
     specify error handling at this level, when certain errors -- such as
     exhausting memory -- do not belong here, since a mathematical machine has
     no such limits. *)
  Def Method1 allocS (r : rep) (len : Size | 0 < len) : rep * Ptr :=
    addr <- find_free_block (` len) (resvs r);
    ret ({| resvs := M.add addr (` len) (resvs r)
          ; bytes := bytes r |}, addr),

  (* Freeing an unallocated block is a no-op. *)
  Def Method1 freeS (r : rep) (addr : Ptr) : rep * unit :=
    ret ({| resvs := M.remove addr (resvs r)
          ; bytes := bytes r |}, tt),

  (* Realloc is not required to reuse the same block. If the address does not
     identify an allociated region, a new memory block is returned without any
     bytes moved. If a block did exist previously, as many bytes as possible
     are copied to the new block. *)
  Def Method2 reallocS (r : rep) (addr : Ptr) (len : Size | 0 < len) :
    rep * Ptr :=
    naddr <- find_free_block (` len) (M.remove addr (resvs r));
    ret ({| resvs := M.add naddr (` len) (M.remove addr (resvs r))
          ; bytes :=
              Ifopt M.find addr (resvs r) as sz
              Then copy_bytes addr naddr (N.min sz (` len)) (bytes r)
              Else bytes r |}, naddr),

  (* Peeking an uninitialized address allows any value to be returned. *)
  Def Method1 peekS (r : rep) (addr : Ptr) : rep * Word :=
    p <- { p : Word | forall v, M.MapsTo addr v (bytes r) -> p = v };
    ret (r, p),

  Def Method2 pokeS (r : rep) (addr : Ptr) (w : Word) : rep * unit :=
    ret ({| resvs := resvs r
          ; bytes := M.add addr w (bytes r) |}, tt),

  (* Data may only be copied from one allocated block to another (or within
     the same block), and the region must fit within both source and
     destination. Otherwise, the operation is a no-op. *)
  Def Method3 memcpyS (r : rep) (addr1 : Ptr) (addr2 : Ptr) (len : Size) :
    rep * unit :=
    ret ({| resvs := resvs r
          ; bytes := copy_bytes addr1 addr2 len (bytes r) |}, tt),

  (* Any attempt to memset bytes outside of an allocated block is a no-op. *)
  Def Method3 memsetS (r : rep) (addr : Ptr) (len : Size) (w : Word) :
    rep * unit :=
    ret ({| resvs := resvs r
          ; bytes :=
              P.update (bytes r)
                       (N.peano_rect (fun _ => M.t Word) (bytes r)
                                     (fun i => M.add (addr + i)%N w)
                                     len) |}, tt)

}%ADTParsing.

Definition empty : Comp (Rep HeapSpec) :=
  Eval simpl in callCons HeapSpec emptyS.

Definition alloc (r : Rep HeapSpec) (len : Size | 0 < len) :
  Comp (Rep HeapSpec * N) :=
  Eval simpl in callMeth HeapSpec allocS r len.

Definition free (r : Rep HeapSpec) (addr : Ptr) :
  Comp (Rep HeapSpec * unit) :=
  Eval simpl in callMeth HeapSpec freeS r addr.

Definition realloc (r : Rep HeapSpec) (addr : Ptr) (len : Size | 0 < len) :
  Comp (Rep HeapSpec * N) :=
  Eval simpl in callMeth HeapSpec reallocS r addr len.

Definition peek (r : Rep HeapSpec) (addr : Ptr) :
  Comp (Rep HeapSpec * Word) :=
  Eval simpl in callMeth HeapSpec peekS r addr.

Definition poke (r : Rep HeapSpec) (addr : Ptr) (w : Word) :
  Comp (Rep HeapSpec * unit) :=
  Eval simpl in callMeth HeapSpec pokeS r addr w.

Definition memcpy (r : Rep HeapSpec) (addr : Ptr) (addr2 : Ptr) (len : Size) :
  Comp (Rep HeapSpec * unit) :=
  Eval simpl in callMeth HeapSpec memcpyS r addr addr2 len.

Definition memset (r : Rep HeapSpec) (addr : Ptr) (len : Ptr) (w : Word) :
  Comp (Rep HeapSpec * unit) :=
  Eval simpl in callMeth HeapSpec memsetS r addr len w.

(**
 ** Theorems related to the Heap specification.
 **)

Ltac inspect :=
  destruct_computations; simpl in *;
  repeat breakdown;
  repeat (simplify_maps; simpl in *;
          destruct_computations; simpl in *;
          repeat breakdown).

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
  forall addr sz, M.MapsTo addr sz (resvs r) -> 0 < sz.
Proof.
  intros.
  generalize dependent sz.
  generalize dependent addr.
  ADT induction r; complete IHfromADT.
Qed.

Theorem allocations_no_overlap : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr1 sz1, M.MapsTo addr1 sz1 (resvs r) ->
  forall addr2 sz2, M.MapsTo addr2 sz2 (resvs r)
    -> addr1 <> addr2
    -> ~ overlaps addr1 sz1 addr2 sz2.
Proof.
  intros.
  pose proof (allocations_have_size H H0).
  pose proof (allocations_have_size H H1).
  generalize dependent sz2.
  generalize dependent addr2.
  generalize dependent sz1.
  generalize dependent addr1.
  ADT induction r; complete IHfromADT.
  - apply_for_all; nomega.
  - apply_for_all; nomega.
  - eapply M.remove_2 in H4; eauto.
    apply_for_all; nomega.
  - clear H8.
    eapply M.remove_2 in H4; eauto.
    apply not_overlaps_sym.
    apply_for_all; nomega.
Qed.

Theorem allocations_no_overlap_r : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr1 sz1,
    P.for_all (fun a sz => negb (overlaps_bool a sz addr1 sz1)) (resvs r)
      -> 0 < sz1
      -> ~ M.In addr1 (resvs r).
Proof.
  unfold not; intros.
  generalize dependent sz1.
  generalize dependent addr1.
  ADT induction r; complete IHfromADT.
  - inversion H2.
    simplify_maps.
  - apply (proj1 (in_mapsto_iff _ _ _)) in H2.
    destruct H2.
    apply for_all_add_true in H1;
    relational; simpl in *.
      simplify_maps.
        nomega.
      assert (M.In addr1 (resvs r)).
        apply in_mapsto_iff.
        exists x1; assumption.
      eapply IHfromADT; eauto.
      nomega.
    unfold not; intros.
    eapply IHfromADT; eauto.
  - apply (proj1 (in_mapsto_iff _ _ _)) in H2.
    destruct H2.
    simplify_maps.
    eapply for_all_remove_inv in H1; relational.
      eapply IHfromADT; eauto.
      apply in_mapsto_iff.
      exists x0; assumption.
    unfold not; intros.
    apply (proj1 (in_mapsto_iff _ _ _)) in H0.
    destruct H0.
    pose proof (allocations_have_size H H4).
    apply not_eq_sym in H2.
    eapply F.remove_neq_mapsto_iff in H4; eauto.
    apply_for_all; relational.
    nomega.
  - apply (proj1 (in_mapsto_iff _ _ _)) in H2.
    destruct H2.
    simpl in *.
    apply_for_all; relational.
    rewrite <- remove_add in H1.
    simplify_maps.
      apply for_all_add_true in H1; relational; simpl in *.
        nomega.
      simplify_maps.
    rewrite remove_add in H1.
    apply_for_all; relational.
    simplify_maps.
    pose proof (allocations_have_size H H6).
    nomega.
Qed.

Corollary allocations_unique_fits : forall r : Rep HeapSpec, fromADT _ r ->
  forall base sz addr len,
    M.MapsTo base sz (resvs r) ->
    fits base sz addr len ->
    unique (fun a' b' => fits_bool a' b' addr len) base (resvs r).
Proof.
  unfold unique; intros.
  apply P.for_all_iff; relational; intros.
  simplify_maps.
  pose proof (allocations_no_overlap H H0 H4 H3); nomega.
Qed.

Corollary allocations_unique_within : forall r : Rep HeapSpec, fromADT _ r ->
  forall base sz addr,
    M.MapsTo base sz (resvs r) ->
    within base sz addr ->
    unique (fun a' b' => within_bool a' b' addr) base (resvs r).
Proof.
  unfold unique; intros.
  apply P.for_all_iff; relational; intros.
  simplify_maps.
  pose proof (allocations_no_overlap H H0 H4 H3); nomega.
Qed.

Corollary find_partitions_a_singleton : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr base sz,
    M.MapsTo base sz (resvs r)
      -> within base sz addr
      -> M.Equal (P.filter (fun a b => within_bool a b addr) (resvs r))
                 (singleton base sz).
Proof.
  intros.
  pose proof (allocations_no_overlap H H0).
  apply F.Equal_mapsto_iff; intros.
  split; intros.
    unfold singleton.
    simplify_maps; relational.
    simplify_maps.
    destruct (N.eq_dec base k); subst.
      pose proof (F.MapsTo_fun H4 H0); subst.
      left; intuition.
    right; intuition.
    specialize (H2 _ _ H4 n).
    contradiction H2.
    nomega.
  unfold singleton in H3.
  simplify_maps.
  simplify_maps; relational.
  intuition; nomega.
Qed.

Corollary allocations_disjoint : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr sz, M.MapsTo addr sz (resvs r)
    -> forall pos, within addr sz pos
    -> forall addr' sz', M.MapsTo addr' sz' (resvs r)
         -> addr <> addr'
         -> ~ within addr' sz' pos.
Proof. intros; pose proof (allocations_no_overlap H H0 H2 H3); nomega. Qed.

End Heap.
