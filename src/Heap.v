Require Import
  ByteString.Lib.Tactics
  ByteString.Lib.Nomega
  ByteString.Lib.FMapExt
  ByteString.Lib.Fiat
  ByteString.Memory
  ByteString.HeapState
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Module Heap (M : WSfun N_as_DT).

Module Import HeapState := HeapState M.

Import FMapExt.

Open Scope string_scope.

Definition emptyS   := "empty".
Definition allocS   := "alloc".
Definition freeS    := "free".
Definition reallocS := "realloc".
Definition peekS    := "peek".
Definition pokeS    := "poke".
Definition memcpyS  := "memcpy".
Definition memsetS  := "memset".

Definition HeapSpec := Def ADT {
  (* Map of memory addresses to blocks, which contain another mapping from
     offsets to initialized bytes. *)
  rep := HeapState,

  Def Constructor0 emptyS : rep := ret newHeapState,

  (* Allocation returns the address for the newly allocated block.
     NOTE: conditions such as out-of-memory are not handled here; the final
     implementation must decide how to handle this operationally, such as by
     throwing an exception. It remains a further research question how to
     specify error handling at this level, when certain errors -- such as
     exhausting memory -- do not belong here, since a mathematical machine has
     no such limits. *)
  Def Method1 allocS (r : rep) (len : Size | 0 < len) : rep * Ptr Word :=
    addr <- find_free_block (` len) (resvs r);
    ret ({| resvs := M.add addr (` len) (resvs r)
          ; bytes := bytes r |}, addr),

  (* Freeing an unallocated block is a no-op. *)
  Def Method1 freeS (r : rep) (addr : Ptr Word) : rep :=
    ret {| resvs := M.remove addr (resvs r)
         ; bytes := bytes r |},

  (* Realloc is not required to reuse the same block. If the address does not
     identify an allociated region, a new memory block is returned without any
     bytes moved. If a block did exist previously, as many bytes as possible
     are copied to the new block. *)
  Def Method2 reallocS (r : rep) (addr : Ptr Word) (len : Size | 0 < len) :
    rep * Ptr Word :=
    naddr <- find_free_block (` len) (M.remove addr (resvs r));
    ret ({| resvs := M.add naddr (` len) (M.remove addr (resvs r))
          ; bytes :=
              Ifopt M.find addr (resvs r) as sz
              Then copy_bytes addr naddr (N.min sz (` len))
                              (bytes r) (bytes r)
              Else bytes r |}, naddr),

  (* Peeking an uninitialized address allows any value to be returned. *)
  Def Method1 peekS (r : rep) (addr : Ptr Word) : rep * Word :=
    p <- { p : Word
         | M.MapsTo addr p (bytes r) \/ (~ M.In addr (bytes r) /\ p = Zero) };
    ret (r, p),

  Def Method2 pokeS (r : rep) (addr : Ptr Word) (w : Word) : rep :=
    ret {| resvs := resvs r
         ; bytes := M.add addr w (bytes r) |},

  (* Data may only be copied from one allocated block to another (or within
     the same block), and the region must fit within both source and
     destination. Otherwise, the operation is a no-op. *)
  Def Method3 memcpyS (r : rep) (addr1 : Ptr Word) (addr2 : Ptr Word) (len : Size) :
    rep :=
    ret ({| resvs := resvs r
          ; bytes := copy_bytes addr1 addr2 len (bytes r) (bytes r) |}),

  (* Any attempt to memset bytes outside of an allocated block is a no-op. *)
  Def Method3 memsetS (r : rep) (addr : Ptr Word) (len : Size) (w : Word) :
    rep :=
    ret ({| resvs := resvs r
          ; bytes :=
              P.update (bytes r)
                       (N.peano_rect (fun _ => M.t Word) (bytes r)
                                     (fun i => M.add (addr + i)%N w)
                                     len) |})

}%ADTParsing.

Definition empty : Comp (Rep HeapSpec) :=
  Eval simpl in callMeth HeapSpec emptyS.

Definition alloc (r : Rep HeapSpec) (len : Size | 0 < len) :
  Comp (Rep HeapSpec * Ptr Word) :=
  Eval simpl in callMeth HeapSpec allocS r len.

Corollary refineEquiv_unfold_alloc : forall r (x : Size) (H : 0 < x),
  refineEquiv (alloc r (exist _ x H))
              (addr <- find_free_block x (resvs r);
               ret ({| resvs := M.add addr x (resvs r)
                     ; bytes := bytes r |}, addr)).
Proof. intros; reflexivity. Qed.

Definition free (r : Rep HeapSpec) (addr : Ptr Word) :
  Comp (Rep HeapSpec) :=
  Eval simpl in callMeth HeapSpec freeS r addr.

Definition realloc (r : Rep HeapSpec) (addr : Ptr Word) (len : Size | 0 < len) :
  Comp (Rep HeapSpec * Ptr Word) :=
  Eval simpl in callMeth HeapSpec reallocS r addr len.

Definition peek (r : Rep HeapSpec) (addr : Ptr Word) :
  Comp (Rep HeapSpec * Word) :=
  Eval simpl in callMeth HeapSpec peekS r addr.

Definition poke (r : Rep HeapSpec) (addr : Ptr Word) (w : Word) :
  Comp (Rep HeapSpec) :=
  Eval simpl in callMeth HeapSpec pokeS r addr w.

Definition memcpy (r : Rep HeapSpec) (addr : Ptr Word) (addr2 : Ptr Word) (len : Size) :
  Comp (Rep HeapSpec) :=
  Eval simpl in callMeth HeapSpec memcpyS r addr addr2 len.

Definition memset (r : Rep HeapSpec) (addr : Ptr Word) (len : Ptr Word) (w : Word) :
  Comp (Rep HeapSpec) :=
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
  repeat inspect;
  try match goal with
    [ H : (?X =? ?Y) = true |- _ ] => apply N.eqb_eq in H; subst
  end;
  try (eapply IHfromADT; eassumption);
  try solve [ eapply IHfromADT; try eassumption; inspect
            | try eapply IHfromADT; eassumption
            | inspect; try nomega;
              eapply IHfromADT; try eassumption; inspect
            | discriminate ].

Theorem allocations_have_size : forall r : Rep HeapSpec, fromADT _ r ->
  forall addr sz, M.MapsTo addr sz (resvs r) -> 0 < sz.
Proof.
  intros r from_r; pattern r; apply ADT_ind; try eassumption.
  intro midx;
  match goal with
  | [ midx : MethodIndex _      |- _ ] => pattern midx
  end;
  apply IterateBoundedIndex.Iterate_Ensemble_equiv';
  repeat apply IterateBoundedIndex.Build_prim_and;
  try solve [constructor ] ;
  simpl in *; intros;
    simpl in *; destruct_ex; split_and;
      repeat inspect; injections; simpl in *; inspect; eauto.
Qed.

Lemma overlaps_bool_complete_true
  : forall addr2 sz2 x1 x0,
    overlaps_bool addr2 sz2 x1 x0 = true <-> overlaps addr2 sz2 x1 x0.
Proof.
  unfold overlaps, overlaps_bool; intros; setoid_rewrite andb_true_iff.
  nomega.
Qed.

Lemma overlaps_bool_complete_false
  : forall addr2 sz2 x1 x0,
    overlaps_bool addr2 sz2 x1 x0 = false <-> ~ overlaps addr2 sz2 x1 x0.
Proof.
  intros; rewrite <- overlaps_bool_complete_true, <- not_true_iff_false; tauto.
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
  pattern r; apply ADT_ind; try eassumption.
    intro midx;
  match goal with
  | [ midx : MethodIndex _      |- _ ] => pattern midx
  end;
  apply IterateBoundedIndex.Iterate_Ensemble_equiv';
  repeat apply IterateBoundedIndex.Build_prim_and;
  try solve [constructor ]; simpl in *; intros;
    destruct_ex; split_and; repeat inspect;
      injections; simpl in *; inspect; eauto.
  - apply_for_all; nomega.
  - apply_for_all; nomega.
  - eapply M.remove_2 in H4; eauto.
    apply_for_all; nomega.
  - clear H10.
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
    intros r from_r; pattern r; apply ADT_ind; try eassumption.
  intro midx;
  match goal with
  | [ midx : MethodIndex _      |- _ ] => pattern midx
  end;
  apply IterateBoundedIndex.Iterate_Ensemble_equiv';
  repeat apply IterateBoundedIndex.Build_prim_and;
  try solve [constructor ] ;
  simpl in *; intros;
    simpl in *; destruct_ex; split_and;
      repeat inspect; injections; simpl in *; inspect; eauto; intro.
  - apply F.empty_in_iff in H; eauto.
  - apply (proj1 (in_mapsto_iff _ _ _)) in H3.
    destruct_ex.
    apply for_all_add_true in H0;
    relational; simpl in *; eauto.
    simplify_maps.
    + nomega.
    + intuition. eapply H; eauto.
      apply in_mapsto_iff; eauto.
  - apply (proj1 (in_mapsto_iff _ _ _)) in H2.
    destruct H2.
    simplify_maps.
    apply not_eq_sym in H3.
    pose proof (allocations_have_size H4 H5).
    apply not_eq_sym in H3.
    eapply F.remove_neq_mapsto_iff in H5; eauto.
    apply_for_all; relational.
    nomega.
  - apply (proj1 (in_mapsto_iff _ _ _)) in H3.
    destruct H3.
    simpl in *.
    apply_for_all; relational.
    apply F.add_mapsto_iff in H3; intuition; subst.
    nomega.
    simplify_maps.
    pose proof (allocations_have_size H4 H8).
    nomega.
Qed.

Corollary allocations_no_overlap_for_all :
  forall r : Rep HeapSpec, fromADT _ r ->
    forall addr sz,
      M.MapsTo addr sz (resvs r) ->
      P.for_all (fun addr' sz' => negb (overlaps_bool addr' sz' addr sz))
                (M.remove addr (resvs r)).
Proof.
  intros.
  pose proof (allocations_no_overlap H H0).
  apply P.for_all_iff; relational; intros.
  simplify_maps.
  specialize (H1 _ _ H4 H3).
  nomega.
Qed.

(* Ben: This axiom is not consistent for all finite map implementations, *)
(* so I wouldn't recommend using [refine_realloc] *)
Axiom Extensionality_FMap : forall (elt : Type) (A B : M.t elt),
    M.Equal (elt:=elt) A B -> A = B.

(* Reallocation is just an optimization over alloc/memcpy/free. It optimizes
   the case where the newly allocated block resides at the same location, and
   thus no copying is needed. *)
Lemma refine_realloc : forall addr len r,
  forall sz, M.MapsTo addr sz (resvs r)
    -> 0 < sz
    -> sz <= ` len
    -> refine (realloc r addr len)
              (`(r, addr') <- alloc r len;
               r <- memcpy r addr addr' sz;
               r <- free r addr;
               ret (r, addr')).
Proof.
  intros.
  destruct len; simpl in *.
  unfold Bind2.
  autorewrite with monad laws.
  unfold realloc, find_free_block.
  autorewrite with monad laws.
  simpl.
  apply F.find_mapsto_iff in H.
  rewrite H; simpl.
  intros ??.
  computes_to_inv; subst.
  computes_to_econstructor.
    Local Transparent Pick.
    Local Transparent computes_to.
    unfold Pick, computes_to; simpl.
    apply for_all_remove.
      relational.
    apply H2.
  apply eq_ret_compute.
  f_equal.
  f_equal.
    apply Extensionality_FMap.
    destruct (N.eq_dec v0 addr); subst.
      unfold is_true in H1.
      revert H1.
      remember (fun _ _ => _) as P.
      cut (Proper (eq ==> eq ==> eq) P).
        intros HP ?.
        apply F.find_mapsto_iff in H.
        pose proof (proj1 (@P.for_all_iff _ P HP (resvs r)) H2 addr sz H) as H3.
        rewrite HeqP in H3.
        nomega.
      relational.
    apply F.Equal_mapsto_iff; split; intros.
      simplify_maps.
        simplify_maps.
        split.
          intuition.
        simplify_maps.
      repeat simplify_maps.
      split.
        intuition.
      simplify_maps.
    repeat simplify_maps.
    right.
    intuition.
  rewrite N.min_l; trivial.
Qed.

End Heap.
