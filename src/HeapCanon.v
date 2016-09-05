Require Import
  ByteString.Tactics
  ByteString.Nomega
  ByteString.Memory
  ByteString.FMapExt
  ByteString.Fiat
  ByteString.FromADT
  ByteString.Heap
  ByteString.HeapADT
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Generalizable All Variables.

Module HeapCanonical (M : WSfun N_as_DT).

Module Import HeapADT := HeapADT M.

Import Heap.
Import HeapState.
Import FMapExt.

Open Scope N_scope.

(** In order to refine to a computable heap, we have to add the notion of
    "free memory", from which addresses may be allocated. A further
    optimization here would be to add a free list, to which free blocks are
    returned, in order avoid gaps in the heap. A yet further optimization
    would be to better manage the free space to avoid fragmentation. The
    implementation below simply grows the heap with every allocation. *)

Theorem HeapCanonical : FullySharpened HeapSpec.
Proof.
  start sharpening ADT.
  eapply SharpenStep; [ apply (projT2 HeapSpecADT) |].

  hone representation using
       (fun or nr =>
          M.Equal (resvs (` or)) (resvs (snd nr)) /\
          M.Equal (bytes (` or)) (bytes (snd nr)) /\
          P.for_all (fun addr sz => addr + sz <=? fst nr)
                    (resvs (snd nr))).

  refine method emptyS.
  {
    remove_dependency (empty_fromADT (ReturnComputes _)).
    refine pick val (0%N, newHeapState).
      finish honing.
    intuition; simpl.
    apply for_all_empty; relational.
  }

  refine method allocS.
  {
    unfold find_free_block.
    remove_dependency alloc_fromADT.

    refine pick val (fst r_n).
    {
      simplify with monad laws; simpl.

      refine pick val (fst r_n + ` d,
                       {| resvs := M.add (fst r_n) (` d) (resvs (snd r_n))
                        ; bytes := bytes (snd r_n) |}).
        simplify with monad laws; simpl.
        finish honing.

      simpl in *; intuition.
      rewrite H1; reflexivity.
      apply for_all_add_true; relational.
        rewrite <- H1.
        destruct d.
        eapply allocations_no_overlap_r; eauto.
          exact (proj2_sig r_o).
        rewrite H1.
        eapply for_all_impl; eauto; relational; intros.
        nomega.
      split.
        eapply for_all_impl; eauto; relational; intros.
        nomega.
      nomega.
    }

    repeat breakdown; simpl in *.
    rewrite H0.
    eapply for_all_impl; eauto;
    relational; nomega.
  }

  refine method freeS.
  {
    remove_dependency free_fromADT.

    refine pick val (fst r_n,
                     {| resvs := M.remove d (resvs (snd r_n))
                      ; bytes := bytes (snd r_n) |}).
      simplify with monad laws; simpl.
      finish honing.

    simpl in *; intuition.
    - rewrite H1; reflexivity.
    - apply for_all_remove; relational.
  }

  refine method reallocS.
  {
    unfold find_free_block.
    remove_dependency realloc_fromADT.

    refine pick val (Ifopt M.find d (resvs (snd r_n)) as sz
                     Then If ` d0 <=? sz Then d Else fst r_n
                     Else fst r_n).
    {
      simplify with monad laws.

      refine pick val
        (Ifopt M.find d (resvs (snd r_n)) as sz
         Then If ` d0 <=? sz
              Then
                (fst r_n,
                 {| resvs := M.add d (` d0) (resvs (snd r_n)) (* update *)
                  ; bytes := bytes (snd r_n) |})
              Else
                (fst r_n + ` d0,
                 {| resvs := M.add (fst r_n) (` d0)
                                   (M.remove d (resvs (snd r_n)))
                  ; bytes := copy_bytes d (fst r_n) sz
                                        (bytes (snd r_n)) |})
         Else
           (fst r_n + ` d0,
            {| resvs := M.add (fst r_n) (` d0) (resvs (snd r_n))
             ; bytes := bytes (snd r_n) |})).
        simplify with monad laws.
        finish honing.

      simpl in *; intuition; rewrite ?H1;
      (destruct (M.find d _) as [sz|] eqn:Heqe;
       [ destruct (` d0 <=? sz) eqn:Heqe1;
         simpl; rewrite ?Heqe1 |]); simpl.
      - rewrite remove_add; reflexivity.
      - reflexivity.
      - apply F.add_m; auto.
        apply F.Equal_mapsto_iff; split; intros.
          simplify_maps.
        simplify_maps; intuition.
        subst.
        apply F.find_mapsto_iff in H2.
        congruence.
      - rewrite copy_bytes_idem; assumption.
      - rewrite N.min_l.
          rewrite H0; reflexivity.
        nomega.
      - assumption.
      - normalize.
        apply_for_all; relational.
        rewrite <- remove_add.
        apply for_all_add_true; relational.
          simplify_maps.
        split.
          apply for_all_remove; relational.
        nomega.
      - normalize.
        apply_for_all; relational.
        rewrite <- remove_add.
        apply for_all_add_true; relational.
          simplify_maps.
        split.
          apply for_all_remove; relational.
          apply for_all_remove; relational.
          eapply for_all_impl; eauto;
          relational; nomega.
        nomega.
      - rewrite <- remove_add.
        apply for_all_add_true; relational.
          simplify_maps.
        split.
          apply for_all_remove; relational.
          eapply for_all_impl; eauto;
          relational; nomega.
        nomega.
    }
    simpl in *; intuition; rewrite ?H1;
    (destruct (M.find d _) as [sz|] eqn:Heqe;
     [ destruct (` d0 <=? sz) eqn:Heqe1;
       simpl; rewrite ?Heqe1 |]); simpl.
    - normalize.
      rewrite <- H1 in Heqe.
      pose proof (allocations_no_overlap (proj2_sig r_o) Heqe).
      apply P.for_all_iff; relational; intros.
      simplify_maps.
      rewrite <- H1 in H6.
      specialize (H2 _ _ H6 H5).
      nomega.
    - normalize.
      apply_for_all; relational.
      apply for_all_remove; relational.
      eapply for_all_impl; eauto;
      relational; nomega.
    - apply for_all_remove; relational.
      eapply for_all_impl; eauto;
      relational; nomega.
  }

  refine method peekS.
  {
    remove_dependency peek_fromADT.

    refine pick val (Ifopt M.find d (bytes (snd r_n)) as v
                     Then v
                     Else Zero).
    {
      simplify with monad laws.
      refine pick val r_n.
        simplify with monad laws.
        finish honing.
      simpl in *; intuition.
    }
    simpl in *; intuition.
    destruct (M.find d _) as [sz|] eqn:Heqe;
    simpl; normalize.
      rewrite H0 in H2.
      pose proof (F.MapsTo_fun Heqe H2).
      assumption.
    rewrite H0 in H2.
    apply F.find_mapsto_iff in H2.
    congruence.
  }

  refine method pokeS.
  {
    remove_dependency poke_fromADT.

    refine pick val (fst r_n,
                     {| resvs := resvs (snd r_n)
                      ; bytes := M.add d d0 (bytes (snd r_n)) |}).
      simplify with monad laws.
      finish honing.

    simpl in *; intuition;
    destruct (d <? fst r_n) eqn:Heqe; simpl; trivial;
    rewrite H0; reflexivity.
  }

  refine method memcpyS.
  {
    remove_dependency memcpy_fromADT.

    refine pick val (fst r_n,
                     {| resvs := resvs (snd r_n)
                      ; bytes := copy_bytes d d0 d1 (bytes (snd r_n)) |}).
      simplify with monad laws.
      finish honing.

    simpl in *; intuition;
    rewrite H0; reflexivity.
  }

  refine method memsetS.
  {
    remove_dependency memset_fromADT.

    refine pick val
       (fst r_n,
        {| resvs := resvs (snd r_n)
         ; bytes :=
             P.update (bytes (snd r_n))
                      (N.peano_rect (fun _ => M.t Word)
                                    (bytes (snd r_n))
                                    (fun i => M.add (d + i)%N d1) d0) |}).
      simplify with monad laws.
      finish honing.

    simpl in *; intuition.
    apply P.update_m; trivial.
    induction d0 using N.peano_ind; simpl; trivial.
    rewrite !N.peano_rect_succ.
    apply F.add_m; trivial.
  }

  finish_SharpeningADT_WithoutDelegation.
Defined.

End HeapCanonical.
