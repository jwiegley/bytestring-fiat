Require Import
  ByteString.Lib.Tactics
  ByteString.Lib.Nomega
  ByteString.Lib.FMapExt
  ByteString.Lib.Fiat
  ByteString.Memory
  ByteString.HeapState
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx
  Hask.Control.Applicative.

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

Section Heap.

Context `{Alternative m}.

Definition conditionally {rep A : Type} (r : rep)
           (c : Comp (option A)) (Q : A -> Comp rep) : Comp (rep * m A) :=
  mres <- c;
  Ifopt mres as res
  Then (r' <- Q res;
        ret (r', pure res))
  Else ret (r, empty).
Arguments conditionally {rep A} r c Q _ /.

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
  Def Method1 allocS (r : rep) (len : Size | 0 < len) : rep * m Ptr :=
    conditionally r (find_free_block (` len) (resvs r)) (fun addr =>
      ret {| resvs := M.add addr (` len) (resvs r)
           ; bytes := bytes r |}),

  (* Freeing an unallocated block is a no-op. *)
  Def Method1 freeS (r : rep) (addr : Ptr) : rep * m unit :=
    conditionally r { _ | True } (fun _ =>
      ret {| resvs := M.remove addr (resvs r)
           ; bytes := bytes r |}),

  (* Realloc is not required to reuse the same block. If the address does not
     identify an allociated region, a new memory block is returned without any
     bytes moved. If a block did exist previously, as many bytes as possible
     are copied to the new block. *)
  Def Method2 reallocS (r : rep) (addr : Ptr) (len : Size | 0 < len) :
    rep * m Ptr :=
    conditionally r (find_free_block (` len) (M.remove addr (resvs r)))
      (fun naddr =>
         ret {| resvs := M.add naddr (` len) (M.remove addr (resvs r))
              ; bytes :=
                  Ifopt M.find addr (resvs r) as sz
                  Then copy_bytes addr naddr (N.min sz (` len)) (bytes r)
                  Else bytes r |}),

  (* Peeking an uninitialized address allows any value to be returned. *)
  Def Method1 peekS (r : rep) (addr : Ptr) : rep * m Word :=
    conditionally
      r { p : option Word
        | forall v, p = Some v -> M.MapsTo addr v (bytes r) }
      (fun _ => ret r),

  Def Method2 pokeS (r : rep) (addr : Ptr) (w : Word) : rep * m unit :=
    conditionally r { _ | True } (fun _ =>
      ret {| resvs := resvs r
           ; bytes := M.add addr w (bytes r) |}),

  (* Data may only be copied from one allocated block to another (or within
     the same block), and the region must fit within both source and
     destination. Otherwise, the operation is a no-op. *)
  Def Method3 memcpyS (r : rep) (addr1 : Ptr) (addr2 : Ptr) (len : Size) :
    rep * m unit :=
    conditionally r { _ | True } (fun _ =>
      ret {| resvs := resvs r
           ; bytes := copy_bytes addr1 addr2 len (bytes r) |}),

  (* Any attempt to memset bytes outside of an allocated block is a no-op. *)
  Def Method3 memsetS (r : rep) (addr : Ptr) (len : Size) (w : Word) :
    rep * m unit :=
    conditionally r { _ | True } (fun _ =>
      ret {| resvs := resvs r
           ; bytes :=
               P.update (bytes r)
                        (N.peano_rect (fun _ => M.t Word) (bytes r)
                                      (fun i => M.add (addr + i)%N w)
                                      len) |})

}%ADTParsing.

Definition empty : Comp (Rep HeapSpec) :=
  Eval simpl in callCons HeapSpec emptyS.

Definition alloc (r : Rep HeapSpec) (len : Size | 0 < len) :
  Comp (Rep HeapSpec * m N) :=
  Eval simpl in callMeth HeapSpec allocS r len.

Definition free (r : Rep HeapSpec) (addr : Ptr) :
  Comp (Rep HeapSpec * m unit) :=
  Eval simpl in callMeth HeapSpec freeS r addr.

Definition realloc (r : Rep HeapSpec) (addr : Ptr) (len : Size | 0 < len) :
  Comp (Rep HeapSpec * m N) :=
  Eval simpl in callMeth HeapSpec reallocS r addr len.

Definition peek (r : Rep HeapSpec) (addr : Ptr) :
  Comp (Rep HeapSpec * m Word) :=
  Eval simpl in callMeth HeapSpec peekS r addr.

Definition poke (r : Rep HeapSpec) (addr : Ptr) (w : Word) :
  Comp (Rep HeapSpec * m unit) :=
  Eval simpl in callMeth HeapSpec pokeS r addr w.

Definition memcpy (r : Rep HeapSpec) (addr : Ptr) (addr2 : Ptr) (len : Size) :
  Comp (Rep HeapSpec * m unit) :=
  Eval simpl in callMeth HeapSpec memcpyS r addr addr2 len.

Definition memset (r : Rep HeapSpec) (addr : Ptr) (len : Ptr) (w : Word) :
  Comp (Rep HeapSpec * m unit) :=
  Eval simpl in callMeth HeapSpec memsetS r addr len w.

(**
 ** Theorems related to the Heap specification.
 **)

Ltac inspect :=
  destruct_computations; simpl in *;
  repeat breakdown;
  repeat (simplify_maps; simpl in *;
          destruct_computations; simpl in *;
          repeat breakdown);
  simpl in *; tsubst; simpl in *.

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

(* Typeclasses eauto := debug. *)

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
  pose proof (allocations_have_size H0 H1).
  pose proof (allocations_have_size H0 H2).
  generalize dependent sz2.
  generalize dependent addr2.
  generalize dependent sz1.
  generalize dependent addr1.
  ADT induction r; complete IHfromADT.
  - apply_for_all; nomega.
  - apply_for_all; nomega.
  - eapply M.remove_2 in H5; eauto.
    apply_for_all; nomega.
  - clear H9.
    eapply M.remove_2 in H5; eauto.
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
  - inversion H3.
    simplify_maps.
  - apply (proj1 (in_mapsto_iff _ _ _)) in H3.
    destruct H3.
    apply for_all_add_true in H2;
    relational; simpl in *.
      simplify_maps.
        nomega.
      assert (M.In addr1 (resvs r)).
        apply in_mapsto_iff.
        exists x0; assumption.
      eapply IHfromADT; eauto.
      nomega.
    unfold not; intros.
    eapply IHfromADT; eauto.
  - apply (proj1 (in_mapsto_iff _ _ _)) in H3.
    destruct H3.
    simplify_maps.
    eapply for_all_remove_inv in H2; relational.
      eapply IHfromADT; eauto.
      apply in_mapsto_iff.
      exists x0; assumption.
    unfold not; intros.
    apply (proj1 (in_mapsto_iff _ _ _)) in H3.
    destruct H3.
    pose proof (allocations_have_size H0 H6).
    apply not_eq_sym in H5.
    eapply F.remove_neq_mapsto_iff in H6; eauto.
    apply_for_all; relational.
    nomega.
  - apply (proj1 (in_mapsto_iff _ _ _)) in H3.
    destruct H3.
    simpl in *.
    apply_for_all; relational.
    rewrite <- remove_add in H2.
    simplify_maps.
      apply for_all_add_true in H2; relational; simpl in *.
        nomega.
      simplify_maps.
    rewrite remove_add in H2.
    apply_for_all; relational.
    simplify_maps.
    pose proof (allocations_have_size H0 H7).
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
  pose proof (allocations_no_overlap H0 H1).
  apply P.for_all_iff; relational; intros.
  simplify_maps.
  specialize (H2 _ _ H5 H4).
  nomega.
Qed.

End Heap.

End Heap.
