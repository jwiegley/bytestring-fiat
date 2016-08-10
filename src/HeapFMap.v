Require Import
  Here.Relations
  Here.TupleEnsembles
  Here.Nomega
  Here.BindDep
  Here.ADTInduction
  Here.Tactics
  Here.Heap
  Here.Within
  Here.DefineAbsR
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Module HeapFMap (Mem : Memory) (M : WSfun N_as_DT).

Module Import Within := Within Mem M.
Module Import Define := Define_AbsR M.

Import Block.                  (* Within -> MemoryBlockC *)
Import Block.Adt.              (* Within -> MemoryBlockC -> HeapADT *)
Import Block.Adt.Heap.         (* Within -> MemoryBlockC -> HeapADT -> Heap *)
Include FunMaps.               (* DefineAbsR -> FunMaps *)

Require Import Fiat.ADT Fiat.ADTNotation.

Definition Heap_AbsR
           (or : { r : Rep HeapSpec | fromADT HeapSpec r})
           (nr : N * M.t MemoryBlockC) : Prop :=
  Map_AbsR MemoryBlock_AbsR (` or) (snd nr) /\
  P.for_all (within_allocated_mem (fst nr)) (snd nr).

Theorem heaps_refine_to_maps : forall r : Rep HeapSpec, fromADT _ r ->
  exists m : M.t MemoryBlockC, Map_AbsR MemoryBlock_AbsR r m.
Proof.
  intros.
  apply every_finite_map_has_an_associated_fmap; auto.
  - apply heap_is_finite; auto.
  - apply allocations_unique; auto.
Qed.

Lemma Heap_AbsR_outside_mem
      {r_o r_n} (AbsR : Heap_AbsR r_o r_n)
      (d : {len : N | 0 < len}) :
  All (fun addr' blk' =>
         ~ overlaps addr' (memSize blk') (fst r_n) (` d)) (` r_o).
Proof.
  intros addr blk H.
  apply AbsR in H; destruct H as [cblk [? ?]].
  rewrite (proj1 H0).
  destruct AbsR as [_ ?].
  eapply P.for_all_iff with (k:=addr) (e:=cblk) in H1; eauto; auto.
  unfold within_allocated_mem in H1; simpl in H1.
  unfold not, overlaps, within in *.
  nomega.
Qed.

Theorem Peek_in_heap {r_o r_n} (AbsR : Heap_AbsR r_o r_n) pos :
  forall base blk' cblk',
    MemoryBlock_AbsR blk' cblk'
      -> Lookup base blk' (` r_o)
      -> withinMemBlock pos base blk'
      -> find_if (withinMemBlockC pos) (snd r_n) = Some (base, cblk').
Proof.
  intros.
  pose proof (find_partitions_a_singleton (proj2_sig r_o) _ H0 H1).
  eapply Same_Map_AbsR with (R:=MemoryBlock_AbsR) in H2.
    Focus 2.
    apply Filter_Map_AbsR; auto.
      apply withinMemBlock_Proper; reflexivity.
      apply withinMemBlockC_Proper; reflexivity.
      apply withinMemBlock_AbsR_applied; eauto.
      apply (proj1 AbsR).
    Focus 2.
    apply Single_Map_AbsR; eauto.
  apply find_if_filter_is_singleton in H2; auto.
  unfold optionP, pairP in H2.
  destruct (find_if (withinMemBlockC pos) (snd r_n)).
    destruct p, H2; subst; trivial.
  tauto.
Qed.

Theorem Poke_in_heap {r_o r_n} (AbsR : Heap_AbsR r_o r_n) pos val :
  P.for_all (within_allocated_mem (fst r_n))
    (M.mapi
       (fun (addr : M.key) (cblk : MemoryBlockC) =>
        IfDec within addr (memCSize cblk) pos
        Then {| memCSize := memCSize cblk
              ; memCData := M.add (pos - addr) val (memCData cblk) |}
        Else cblk) (snd r_n)).
Proof.
  destruct AbsR as [_ H].
  unfold P.for_all.
  apply P.fold_rec_bis; auto; intros.
  apply F.mapi_mapsto_iff in H0.
  destruct H0, H0.
  simpl; intros; subst; auto.
  unfold within_allocated_mem, IfDec_Then_Else; simpl.
  eapply P.for_all_iff in H; eauto.
    unfold within_allocated_mem in H.
    decisions; simpl in *; auto;
    congruence; auto.
  intros; subst; reflexivity.
Qed.

Ltac AbsR_prep :=
  repeat
    match goal with
    | [ H : Heap_AbsR _ _ |- _ ] => unfold Heap_AbsR in H; simpl in H
    | [ |- Heap_AbsR _ _ ] => unfold Heap_AbsR; simpl
    | [ H : _ /\ _ |- _ ] => destruct H; simpl in H
    | [ |- _ /\ _ ] => split
    end; simpl; eauto; eauto with maps.

Require Import Fiat.ADTRefinement Fiat.ADTRefinement.BuildADTRefinements.

Lemma HeapImpl : FullySharpened HeapSpec.
Proof.
  start sharpening ADT.
  eapply SharpenStep; [ apply (projT2 HeapSpecADT) |].

  hone representation using Heap_AbsR.

  refine method emptyS.
  {
    unfold empty.
    remove_dependency.
    simplify with monad laws.

    refine pick val (0%N, @M.empty _).
      finish honing.

    AbsR_prep.
    - apply P.for_all_iff; auto.
  }

  refine method allocS.
  {
    unfold Heap_AbsR, alloc.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val (fst r_n).
      Focus 2.
      apply Heap_AbsR_outside_mem; trivial.

    simplify with monad laws; simpl.
    refine pick val ((fst r_n + proj1_sig d)%N,
                     M.add (fst r_n)
                           {| memCSize := proj1_sig d
                            ; memCData := M.empty _ |} (snd r_n)).
      simplify with monad laws.
      finish honing.

    AbsR_prep.
    - apply Update_Map_AbsR; auto.
      apply MemoryBlock_AbsR_impl; auto with maps.
    - apply for_all_add_iff; auto.
      + unfold not; intros.
        apply (proj1 (in_mapsto_iff _ _ _)) in H2.
        destruct H2.
        pose proof H2.
        apply H0 in H3.
        do 2 destruct H3.
        eapply P.for_all_iff
          with (f:=within_allocated_mem (fst r_n)) in H2; auto.
        unfold within_allocated_mem in H2.
        undecide.
        pose proof (allocations_have_size (proj2_sig r_o) _ _ H3).
        rewrite (proj1 H4) in H5.
        reduction.
        clear -H2 H5.
        eapply Nle_impossible; eauto.
      + split.
        {
          apply for_all_impl
           with (P':=within_allocated_mem (fst r_n + ` d)) in H1; auto.
          intros.
          clear -H2.
          unfold within_allocated_mem in *.
          undecide.
          destruct d; simpl.
          apply Nle_add_plus; eauto.
        }
        destruct d; simpl.
        unfold within_allocated_mem; simpl.
        nomega.
  }

  refine method freeS.
  {
    unfold free.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val (fst r_n, M.remove d (snd r_n)).
      simplify with monad laws.
      finish honing.

    AbsR_prep.
    - apply Remove_Map_AbsR; auto.
    - apply for_all_remove; auto.
  }

  refine method reallocS.
  {
    unfold Heap_AbsR, realloc.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val
      (match M.find d (snd r_n) with
       | Some cblk =>
         Some {| memSize := memCSize cblk
               ; memData := of_map eq (memCData cblk) |}
       | None => None
       end).
      Focus 2.
      destruct (M.find (elt:=MemoryBlockC) d (snd r_n)) eqn:Heqe.
        apply F.find_mapsto_iff, H0 in Heqe.
        destruct Heqe, H1, H2; simpl.
        apply of_map_Same in H3.
        apply H0 in H1; apply H0.
        destruct H1, H1; exists x0.
        intuition.
        split; intros; simpl.
          rewrite <- (proj1 H4).
          congruence.
        rewrite <- H3.
        exact (proj2 H4).
      simpl.
      unfold not; intros.
      destruct H1.
      apply H0 in H1.
      destruct H1, H1.
      apply F.find_mapsto_iff in H1.
      congruence.

    simplify with monad laws.
    refine pick val
      (Ifopt M.find d (snd r_n) as cblk
       Then If ` d0 <? memCSize cblk
            Then d
            Else fst r_n
       Else fst r_n).
      Focus 2.
      intros ???.
      destruct (M.find (elt:=MemoryBlockC) d (snd r_n)) eqn:Heqe;
      destruct d0; simpl in *;
      decisions; undecide;
      teardown;
      try discriminate.
        inv Heqe.
        reduction.
        admit.
      destruct H0, H1; simpl in *.
      apply H0 in H3.
      do 2 destruct H3.
      eapply P.for_all_iff with (k:=a) (e:=x0) in H3; eauto; auto.
      rewrite (proj1 H4).
      unfold within_allocated_mem in H3; undecide.
      unfold overlaps, not; intros.
      clear -H3 H5.
      nomega.

    simplify with monad laws.
    refine pick val
      (match M.find (elt:=MemoryBlockC) d (snd r_n) with
       | Some cblk =>
         if ` d0 <? memCSize cblk
         then (fst r_n,
               M.add d {| memCSize := ` d0
                        ; memCData := P.filter (fun k e => k <? ` d0)
                                               (memCData cblk)
                        |} (M.remove d (snd r_n)))
         else (* jww (2016-08-08): Next step: find a better free block *)
              ((fst r_n + ` d0)%N,
               M.add (fst r_n)
                     {| memCSize := ` d0
                      ; memCData := memCData cblk |}
                     (M.remove d (snd r_n)))
       | None =>
         ((fst r_n + ` d0)%N,
          M.add (fst r_n)
                {| memCSize := ` d0
                 ; memCData := M.empty _ |} (snd r_n))
       end).
      simplify with monad laws.
      finish honing.

    AbsR_prep.
    - destruct (M.find (elt:=MemoryBlockC) d (snd r_n)) eqn:Heqe; simpl.
      + decisions.
        * admit.
        * apply Update_Map_AbsR; auto.
            apply MemoryBlock_AbsR_impl.
              admit.
            admit.
          apply Remove_Map_AbsR; auto.
        * apply Update_Map_AbsR; auto.
            apply MemoryBlock_AbsR_impl; auto.
            admit.
          apply Remove_Map_AbsR; auto.
        * admit.
        * apply Update_Map_AbsR; auto.
            apply MemoryBlock_AbsR_impl; auto.
              admit.
            admit.
          apply Remove_Map_AbsR; auto.
        * apply Update_Map_AbsR; auto.
            apply MemoryBlock_AbsR_impl; auto.
            admit.
          apply Remove_Map_AbsR; auto.
      + apply Update_Map_AbsR; auto.
        apply MemoryBlock_AbsR_impl; auto with maps.
    - destruct (M.find (elt:=MemoryBlockC) d (snd r_n)) eqn:Heqe; simpl.
      + decisions; simpl; auto.
        * admit.
        * admit.
      + admit.
  }

  refine method peekS.
  {
    unfold Heap_AbsR, peek.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val
      (Ifopt find_if (withinMemBlockC d) (snd r_n) as p
       Then Ifopt M.find (d - fst p) (memCData (snd p)) as v
            Then v Else Mem.Zero
       Else Mem.Zero).

    simplify with monad laws; simpl.
    refine pick val r_n.
      simplify with monad laws.
      finish honing.

    AbsR_prep.
    - intros; subst; clear H.
      pose proof H1 as H4.
      apply H0 in H1.
      destruct H1 as [cblk [? ?]].
      erewrite Peek_in_heap; eauto; simpl.
      apply H1 in H3.
      destruct H3 as [mem [? ?]]; subst.
      apply F.find_mapsto_iff in H3.
      rewrite H3; reflexivity.
  }

  refine method pokeS.
  {
    unfold poke.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val
      (fst r_n,
       M.mapi (fun addr cblk =>
                 IfDec within addr (memCSize cblk) d
                 Then {| memCSize := memCSize cblk
                       ; memCData := M.add (d - addr) d0 (memCData cblk) |}
                 Else cblk) (snd r_n)).
      simplify with monad laws.
      finish honing.

    pose proof (Poke_in_heap H0).
    AbsR_prep.
    - apply Map_Map_AbsR; auto;
      relational; subst; auto.
      constructor; relational.
      rewrite (proj1 H4).
      decisions; auto.
      apply MemoryBlock_AbsR_impl; auto.
      apply Update_Map_AbsR; auto.
      exact (proj2 H4).
  }

  refine method memcpyS.
  {
    unfold Heap_AbsR, memcpy.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val
      (if 0 <? d1
       then Ifopt find_if (withinMemBlockC d) (snd r_n) as p
            Then if Decidable_witness (P:=fits (fst p) (memCSize (snd p)) d d1)
                 then Some (fst p,
                            {| memSize := memCSize (snd p)
                             ; memData := of_map eq (memCData (snd p)) |})
                 else None
            Else None
       else None).
      Focus 2.
      intros.
      decisions; [|discriminate].
      undecide; intuition;
      destruct (find_if (withinMemBlockC d) (snd r_n)) eqn:Heqe1;
      try discriminate; simpl in H1; inv H1; simpl.
        admit.
      admit.

    simplify with monad laws.
    refine pick val
      (if 0 <? d1
       then Ifopt find_if (withinMemBlockC d0) (snd r_n) as p
            Then if Decidable_witness (P:=fits (fst p) (memCSize (snd p)) d0 d1)
                 then Some (fst p,
                            {| memSize := memCSize (snd p)
                             ; memData := of_map eq (memCData (snd p)) |})
                 else None
            Else None
       else None).
      Focus 2.
      intros.
      decisions; [|discriminate].
      undecide; intuition;
      destruct (find_if (withinMemBlockC d0) (snd r_n)) eqn:Heqe1;
      try discriminate; simpl in H1; inv H1; simpl.
        admit.
      admit.

    simplify with monad laws.
    refine pick val
      (if 0 <? d1
       then match (find_if (withinMemBlockC d) (snd r_n),
                   find_if (withinMemBlockC d0) (snd r_n)) with
            | (Some (saddr, src), Some (daddr, dst)) =>
              if (Decidable_witness
                    (P:=fits saddr (memCSize src) d d1) &&
                  Decidable_witness
                    (P:=fits daddr (memCSize dst) d0 d1))%bool
              then (fst r_n,
                    let soff := d - saddr in
                    let doff := d0 - daddr in
                    M.add d0 {| memCSize := memCSize dst
                              ; memCData :=
                                  let d :=
                                      P.filter (fun k _ =>
                                                  Decidable_witness
                                                    (P:=~ within doff d1 k))
                                               (memCData dst) in
                                  let s :=
                                      P.filter (fun k _ =>
                                                  Decidable_witness
                                                    (P:=~ within soff d1 k))
                                               (memCData src) in
                                  P.update d s |}
                          (M.remove d0 (snd r_n)))
              else r_n
            | _ => r_n
            end
       else r_n).
      simplify with monad laws.
      finish honing.

    AbsR_prep.
    - destruct (0 <? d1); simpl; auto.
      destruct (find_if (withinMemBlockC d) (snd r_n)) eqn:Heqe1;
      destruct (find_if (withinMemBlockC d0) (snd r_n)) eqn:Heqe2;
      simpl; auto;
      decisions; simpl; auto;
      try destruct p;
      try destruct p0; simpl in *;
      decisions; simpl; auto.
      + apply Update_Map_AbsR; auto.
        * admit.
        * apply MemoryBlock_AbsR_impl; auto.
          (* apply Union_Map_AbsR; auto. *)
          admit.
        * admit.
      + admit.
      + admit.
      + admit.
    - destruct (0 <? d1); simpl; auto;
      destruct (find_if (withinMemBlockC d) (snd r_n)) eqn:Heqe1;
      destruct (find_if (withinMemBlockC d0) (snd r_n)) eqn:Heqe2;
      simpl; auto;
      decisions; simpl; auto;
      try destruct p;
      try destruct p0; simpl in *;
      decisions; simpl; auto.
      admit.
  }

  refine method memsetS.
  {
    unfold memset.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val
      (fst r_n,
       M.mapi (fun addr cblk =>
                 IfDec fits addr (memCSize cblk) d d0
                 Then {| memCSize := memCSize cblk
                       ; memCData :=
                           let base := d - addr in
                           N.peano_rect (fun _ => M.t Mem.Word8)
                                        (memCData cblk)
                                        (fun i => M.add (base + i)%N d1) d0  |}
                 Else cblk) (snd r_n)).
      simplify with monad laws.
      finish honing.

    AbsR_prep.
    - apply Map_Map_AbsR; auto;
      relational; subst; auto.
      constructor; relational.
      destruct x0, y0, H3; simpl in *; subst.
      eapply MemoryBlock_AbsR_impl; eauto;
      decisions; auto.
      apply Define_Map_AbsR; auto.
    - eapply P.for_all_iff; auto.
      intros.
      do 2 simplify_maps; intros; subst; auto.
      apply P.for_all_iff with (k:=k) (e:=cblk) in H1; auto.
      decisions; auto.
  }

  finish_SharpeningADT_WithoutDelegation.
Admitted.

End HeapFMap.
