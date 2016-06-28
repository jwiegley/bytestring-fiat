Require Import Fiat.ADT Fiat.ADTNotation.

Require Import
  Coq.FSets.FMapAVL
  Coq.FSets.FMapFacts
  Coq.Structures.OrderedTypeEx.

Module M := FMapAVL.Make(N_as_OT).
Module F := FMapFacts.Facts M.

Require Import
  Here.ByteString
  Here.LibExt
  Here.Heap
  Here.HeapADT
  Here.Nomega
  Here.BindDep.

Generalizable All Variables.

Open Scope N_scope.

Section RefinedHeap.

Variable Word8 : Type.
Variable Zero : Word8.

Definition MemoryBlock := MemoryBlock Word8.
Definition HeapSpec    := @HeapSpec Word8 Zero.

Record MemoryBlockC := {
  memCAddr : N;
  memCSize : N;
  memCData : M.t Word8
}.

Ltac tsubst :=
  Heap.tsubst;
  repeat
    match goal with
    | [ H : {| memCAddr := _
             ; memCSize := _
             ; memCData := _ |} =
            {| memCAddr := _
             ; memCSize := _
             ; memCData := _ |} |- _ ] => inv H
    end;
  subst.

Require Import
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Lemma HeapImpl : FullySharpened HeapSpec.
Proof.
  start sharpening ADT.
  eapply SharpenStep; [ apply (projT2 (@HeapSpecADT Word8 Zero)) |].
  hone representation using
    (fun (or : { r : Ensemble MemoryBlock
               | ADTInduction.fromADT HeapSpec r})
         (nr : N * M.t MemoryBlockC) =>
       forall addr size,
         (forall data,
            In _ (` or) {| memAddr := addr
                         ; memSize := size
                         ; memData := data |} ->
            (addr + size <= fst nr /\
             exists cdata,
               M.find addr (snd nr)
                 = Some {| memCAddr := addr
                         ; memCSize := size
                         ; memCData := cdata |} /\
               (forall i v,
                  In _ data (i, v) <-> M.find i cdata = Some v))) /\
         (forall cdata,
            M.find addr (snd nr)
              = Some {| memCAddr := addr
                      ; memCSize := size
                      ; memCData := cdata |} ->
            (addr + size <= fst nr /\
             exists data,
               In _ (` or) {| memAddr := addr
                            ; memSize := size
                            ; memData := data |} /\
               (forall i v,
                  In _ data (i, v) <-> M.find i cdata = Some v)))).

  refine method emptyS.
  {
    unfold empty.
    rewrite refine_bind_dep_ret.
    simplify with monad laws.
    refine pick val (0%N, @M.empty _).
      finish honing.
    simpl; split; intros.
      inv H0.
    apply F.find_mapsto_iff, F.empty_mapsto_iff in H0.
    contradiction.
  }

  refine method allocS.
  {
    unfold alloc, find_free_block.
    rewrite refine_bind_dep_bind_ret; simpl.
    rewrite refine_bind_dep_ignore.
    simplify with monad laws; simpl.
    refine pick val (fst r_n).
      simplify with monad laws.
      refine pick val (fst r_n + proj1_sig d,
                       M.add (fst r_n)
                             {| memCAddr := fst r_n
                              ; memCSize := proj1_sig d
                              ; memCData := M.empty _ |}
                             (snd r_n)).
        simplify with monad laws.
        finish honing.
      intros.
      destruct (H0 addr size) as [? ?]; clear H0.
      simpl; split; intros.
        apply Add_inv in H0.
        destruct H0.
          destruct (H1 data H0) as [? ?].
          split.
            destruct d; simpl.
            apply Nle_add_plus; trivial.
          destruct H4.
          exists x.
          split; intros.
            apply F.find_mapsto_iff, F.add_mapsto_iff.
            right.
            split.
              destruct H4.
              destruct (H2 _ H4).
              destruct H7.
              destruct H7.
              pose proof (allocations_have_size (proj2_sig r_o) _ _ _ H7).
              clear -H3 H9.
              unfold not; intros; subst.
              eapply Nle_impossible; eassumption.
            apply F.find_mapsto_iff.
            apply H4.
          apply H4.
        tsubst.
        split; intros.
          nomega.
        exists (M.empty Word8).
        split; intros.
          apply F.find_mapsto_iff, F.add_mapsto_iff.
          left; tauto.
        split; intros.
          inv H0.
        apply F.find_mapsto_iff, F.empty_mapsto_iff in H0.
        contradiction.
      apply F.find_mapsto_iff in H0.
      apply F.add_mapsto_iff in H0.
      destruct H0; destruct H0; tsubst.
        split; intros.
          nomega.
        exists (Empty_set (N * Word8)).
        split.
          right; constructor.
        split; intros.
          inv H0.
        apply F.find_mapsto_iff, F.empty_mapsto_iff in H0.
        contradiction.
      apply F.find_mapsto_iff in H3.
      destruct (H2 _ H3).
      split.
        destruct d; simpl in *.
        apply Nle_add_plus; trivial.
      destruct H5.
      exists x.
      split; intros.
        left; tauto.
      apply H5.
    intros.
    destruct (H0 addr' len'); clear H0.
    unfold found_block_at_base in H1.
    destruct (H2 _ H1).
    unfold overlaps.
    nomega.
  }

  refine method freeS.
  {
    unfold free, free_block.
    rewrite refine_bind_dep_ret.
    simplify with monad laws; simpl.

    refine pick val (fst r_n, M.remove d (snd r_n)).
      simplify with monad laws.
      finish honing.

    intros.
    destruct (H0 addr size) as [? ?]; simpl in *.
    split; intros.
      inv H3.
      destruct (H1 _ H4) as [? ?].
      split; trivial.
      destruct H6.
      exists x.
      split.
        rewrite F.remove_neq_o.
          apply H6.
        unfold Ensembles.In in H4.
        exact H5.
      apply H6.
    apply F.find_mapsto_iff, F.remove_mapsto_iff in H3.
    destruct H3.
    apply F.find_mapsto_iff in H4.
    destruct (H2 _ H4).
    split; trivial.
    destruct H6.
    exists x.
    split.
      constructor.
        apply H6.
      unfold not; intros.
      unfold Ensembles.In in H7; simpl in H7; subst.
      tauto.
    tauto.
  }

  refine method reallocS.
  {
    admit.
  }

  refine method peekS.
  {
    unfold peek, found_block.
    rewrite refine_bind_dep_bind_ret.
    etransitivity.
      apply refine_bind_dep
       with (x:=(` r_o,
                  Ifopt List.find
                   (fun p =>
                      let blk := snd p in
                      (* jww (2016-06-24): Unnecessarily inefficient *)
                      (fst p =? memCAddr (snd p)) &&
                      Decidable.Decidable_witness
                        (P:=within (memCAddr blk) (memCSize blk) d))
                   (M.elements (snd r_n)) as p
                 Then let blk := snd p in
                      Ifopt M.find (d - memCAddr blk) (memCData blk) as v
                      Then v
                      Else Zero
                 Else Zero)).
    simpl.

    refine pick val r_n.
      simplify with monad laws.
      unfold If_Opt_Then_Else; simpl.
      finish honing.

    intros.
    destruct (H0 addr size) as [? ?]; clear H0.
    split; intros.
      destruct (H1 _ H0); clear H1 H2.
      split; trivial.
    destruct (H2 _ H0); clear H1 H2.
    split; trivial.
  }

  refine method pokeS.
  {
    unfold poke, set_address.
    rewrite refine_bind_dep_bind_ret; simpl.
    rewrite refine_bind_dep_ignore.
    simplify with monad laws; simpl.
    refine pick val
      (fst r_n,
       M.map (fun blk =>
                IfDec within (memCAddr blk) (memCSize blk) d
                Then {| memCAddr := memCAddr blk
                      ; memCSize := memCSize blk
                      ; memCData := M.add (d - memCAddr blk) d0
                                          (memCData blk) |}
                Else blk) (snd r_n)).
      simplify with monad laws.
      finish honing.

    intros.
    destruct (H0 addr size) as [? ?]; clear H0; simpl in *.
    split; intros.
    {
      simplify_ensembles; decisions; simpl in *; tsubst;
      try destruct x; simpl in *.
      - firstorder.
      - firstorder.
      - destruct (H1 _ H0) as [? ?]; clear H1; trivial.
        destruct H4.
        exists (M.add (d - memAddr) d0 x).
        destruct H1.
        split; intros.
          apply F.find_mapsto_iff in H1.
          apply F.find_mapsto_iff.
          apply F.map_mapsto_iff.
          exists {| memCAddr := memAddr
                  ; memCSize := memSize
                  ; memCData := x |}; simpl.
          rewrite Heqe.
          split; trivial.
        split; intros.
          rewrite F.add_o.
          unfold M.E.eq_dec.
          simplify_ensembles.
            unfold Ensembles.In in H7; simpl in H7.
            decisions.
              rewrite e in H7.
              tauto.
            apply H4; assumption.
          destruct (N.eq_dec (d - memAddr) (d - memAddr)).
            reflexivity.
          tauto.
        rewrite F.add_o in H5.
        unfold M.E.eq_dec in H5.
        destruct (N.eq_dec (d - memAddr) i).
          inv H5.
          right; constructor.
        left.
        constructor.
          apply H4; assumption.
        unfold Ensembles.In; simpl.
        firstorder.
      - destruct (H1 _ H0) as [? ?]; clear H1; trivial.
        destruct H4.
        exists x.
        destruct H1.
        apply F.find_mapsto_iff in H1.
        split.
          apply F.find_mapsto_iff.
          apply F.map_mapsto_iff.
          exists {| memCAddr := addr
                  ; memCSize := size
                  ; memCData := x |}; simpl.
          rewrite Heqe.
          split; trivial.
        exact H4.
    }
    admit.
  }

  refine method memcpyS.
  {
    admit.
  }

  refine method memsetS.
  {
    admit.
  }

  finish_SharpeningADT_WithoutDelegation.
Abort.

End RefinedHeap.
