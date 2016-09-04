Require Import
  Coq.Lists.List
  Coq.Arith.Arith
  Coq.NArith.NArith
  Fiat.ADT
  Fiat.ADTNotation
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements
  ByteString.ADTInduction
  ByteString.BindDep
  ByteString.ByteString
  ByteString.ByteStringEnsHeap
  ByteString.HeapEns
  ByteString.HeapEnsADT
  ByteString.HeapEnsFMap
  ByteString.Nomega
  ByteString.Relations
  ByteString.Tactics
  ByteString.TupleEnsembles
  ByteString.Same_set
  ByteString.Within
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Generalizable All Variables.

Module ByteStringFMap (M : WSfun N_as_DT).

Module Import HF := HeapFMap M.

Import Within.
Import Within.Block.
Import Within.Block.FunMaps.

Section Refined.

Variable heap  : Rep HSpec.
Variable heap' : ComputationalADT.cRep (projT1 HeapImpl).

Variable heap_AbsR : Heap_AbsR (` heap) heap'.

(* This style of computational refinement makes use of a separately refined
   heap. Another approach is to refine the heap methods directly, which would
   mean going directly to the metal (but would require replicating much of the
   proof word that is done in HeapFMap.v). *)

Record PS' := {
  ps'Heap : ComputationalADT.cRep (projT1 HeapImpl);

  ps'Buffer : N;
  ps'BufLen : N;

  ps'Offset : N;
  ps'Length : N
}.

Lemma ByteStringImpl : FullySharpened (projT1 (ByteStringHeap heap)).
Proof.
  start sharpening ADT.
  hone representation using
       (fun (or : PS) (nr : PS') =>
          Heap_AbsR (` (psHeap or)) (ps'Heap nr) /\
          psBuffer or = ps'Buffer nr /\
          psBufLen or = ps'BufLen nr /\
          psOffset or = ps'Offset nr /\
          psLength or = ps'Length nr);
  try simplify with monad laws; simpl.
  {
    refine pick val {| ps'Heap   := heap'
                     ; ps'Buffer := 0
                     ; ps'BufLen := 0
                     ; ps'Offset := 0
                     ; ps'Length := 0 |}.
      finish honing.
    simpl; intuition.
  }
  {
    repeat match goal with
      [ H : _ /\ _ |- _ ] => destruct H
    end; subst.
    destruct r_o, psHeap; simpl in *.
    rewrite H1, H2, H3, H4.
    rewrite refineEquiv_If_Then_Else_Bind.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.
      unfold poke'; simpl.
      remove_dependency; simpl.
      erewrite Heap_refine_poke; eauto.
      simplify with monad laws; simpl.
      remember (M.mapi _ _) as M.
      refine pick val {| ps'Heap   := (fst (ps'Heap r_n), M)
                       ; ps'Buffer := ps'Buffer r_n
                       ; ps'BufLen := ps'BufLen r_n
                       ; ps'Offset := ps'Offset r_n - 1
                       ; ps'Length := ps'Length r_n + 1 |};
      rewrite HeqM; clear HeqM; simpl.
        simplify with monad laws.
        finish honing.
      intuition.
      destruct H0.
      apply of_map_Heap_AbsR; auto.
      apply for_all_within_allocated_mem_mapi; auto; intros.
      clear; decisions; nomega.
    rewrite refineEquiv_If_Then_Else_Bind.
    subst H.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.
      unfold memcpy', poke'; simpl.
      remove_dependency; simpl.
      setoid_rewrite refine_bind_dep_bind_ret; simpl.
      do 2 setoid_rewrite refine_bind_dep_ignore.
      erewrite Heap_refine_memcpy; eauto.
      unfold wrap, FMap_memcpy.
      rewrite refine_bind_unit; simpl.
      erewrite Heap_refine_poke; eauto; simpl.
        Focus 2.
        destruct H0.
        apply of_map_Heap_AbsR; auto.
        destruct (0 <? ps'Length r_n) eqn:Heqe,
                 (find_if _ _) eqn:Heqe1; simpl.
              apply for_all_within_allocated_mem_mapi; auto; intros.
                exact i.
              decisions; nomega.
            auto.
          auto.
        auto.
      simplify with monad laws; simpl.
      remember (M.mapi _ _) as M.
      refine pick val {| ps'Heap   := (fst (ps'Heap r_n), M)
                       ; ps'Buffer := ps'Buffer r_n
                       ; ps'BufLen := ps'BufLen r_n
                       ; ps'Offset := 0
                       ; ps'Length := ps'Length r_n + 1 |};
      rewrite HeqM; clear HeqM; simpl.
        simplify with monad laws.
        finish honing.
      intuition.
      destruct H0.
      apply of_map_Heap_AbsR; auto.
      apply for_all_within_allocated_mem_mapi; auto; intros.
        destruct (0 <? ps'Length r_n) eqn:Heqe,
                 (find_if _ _) eqn:Heqe1; simpl.
              apply for_all_within_allocated_mem_mapi; auto; intros.
              decisions; nomega.
            auto.
          auto.
        auto.
      decisions; nomega.
    rewrite refineEquiv_If_Then_Else_Bind.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.
      unfold alloc', memcpy', poke'.
      remove_dependency; simpl.
      do 3 setoid_rewrite refine_bind_dep_bind_ret.
      simpl; remove_dependency.
      do 3 setoid_rewrite refine_bind_dep_ignore.
      unfold ByteStringEnsHeap.buffer_cons_obligation_2.
      erewrite Heap_refine_alloc; eauto.
      unfold wrap, FMap_alloc.
      rewrite refine_bind_unit; simpl.
      erewrite Heap_refine_memcpy; eauto.
        Focus 2.
        destruct H0.
        apply of_map_Heap_AbsR; auto.
        eapply for_all_within_allocated_mem_add
          with (o:=fst (ps'Heap r_n) + ps'Length r_n + alloc_quantum); auto.
            exact i.
          nomega.
        nomega.
      unfold wrap, FMap_memcpy.
      rewrite refine_bind_unit; simpl.
      erewrite Heap_refine_free; eauto.
        Focus 2.
        destruct H0.
        apply of_map_Heap_AbsR; auto.
        destruct (0 <? ps'Length r_n) eqn:Heqe,
                 (find_if _ _) eqn:Heqe1; simpl.
              apply for_all_within_allocated_mem_mapi; auto; intros.
                eapply for_all_within_allocated_mem_add
                  with (o:=fst (ps'Heap r_n) + ps'Length r_n
                             + alloc_quantum); auto.
                    exact i.
                  nomega.
                nomega.
              decisions; nomega.
            eapply for_all_within_allocated_mem_add; eauto; nomega.
          eapply for_all_within_allocated_mem_add; eauto; nomega.
        eapply for_all_within_allocated_mem_add.
            exact i.
          nomega.
        nomega.
      unfold wrap, FMap_free.
      rewrite refine_bind_unit; simpl.
      erewrite Heap_refine_poke; eauto.
        Focus 2.
        destruct H0.
        apply of_map_Heap_AbsR; auto.
        apply for_all_within_allocated_mem_remove.
        destruct (0 <? ps'Length r_n) eqn:Heqe,
                 (find_if _ _) eqn:Heqe1; simpl.
              apply for_all_within_allocated_mem_mapi; auto; intros.
                eapply for_all_within_allocated_mem_add
                  with (o:=fst (ps'Heap r_n) + ps'Length r_n
                             + alloc_quantum); auto.
                    exact i.
                  nomega.
                nomega.
              decisions; nomega.
            eapply for_all_within_allocated_mem_add; eauto; nomega.
          eapply for_all_within_allocated_mem_add; eauto; nomega.
        eapply for_all_within_allocated_mem_add; eauto; nomega.
      unfold wrap, FMap_poke.
      rewrite refine_bind_unit; simpl.
      remember (M.mapi _ _) as M.
      refine pick val {| ps'Heap   := (fst (ps'Heap r_n) + ps'Length r_n
                                         + alloc_quantum, M)
                       ; ps'Buffer := fst (ps'Heap r_n)
                       ; ps'BufLen := ps'Length r_n + alloc_quantum
                       ; ps'Offset := 0
                       ; ps'Length := ps'Length r_n + alloc_quantum |};
      rewrite HeqM; clear HeqM; simpl.
        simplify with monad laws.
        finish honing.
      intuition.
      destruct H0.
      apply of_map_Heap_AbsR; auto.
      apply for_all_within_allocated_mem_mapi; auto; intros.
        apply for_all_within_allocated_mem_remove; auto; intros.
        destruct (0 <? ps'Length r_n) eqn:Heqe,
                 (find_if _ _) eqn:Heqe1; simpl.
              apply for_all_within_allocated_mem_mapi; auto; intros.
                eapply for_all_within_allocated_mem_add; eauto; nomega.
              decisions; nomega.
            eapply for_all_within_allocated_mem_add; eauto; nomega.
          eapply for_all_within_allocated_mem_add; eauto; nomega.
        eapply for_all_within_allocated_mem_add; eauto; nomega.
      decisions; nomega.
    unfold allocate_buffer, alloc', poke'.
    remove_dependency; simpl.
    unfold Bind2.
    rewrite refine_bind_bind.
    remove_dependency.
    setoid_rewrite refine_bind_dep_bind_ret.
    autorewrite with monad laws; simpl.
    remove_dependency.
    setoid_rewrite refine_bind_dep_ignore.
    erewrite Heap_refine_alloc; eauto.
    unfold wrap, FMap_alloc.
    rewrite refine_bind_unit; simpl.
    erewrite Heap_refine_poke; eauto.
      Focus 2.
      destruct H0.
      apply of_map_Heap_AbsR; auto.
      eapply for_all_within_allocated_mem_add
        with (o:=fst (ps'Heap r_n) + ps'Length r_n
                   + alloc_quantum); auto.
          exact i.
        nomega.
      nomega.
    unfold wrap, FMap_poke.
    rewrite refine_bind_unit; simpl.
    remember (M.mapi _ _) as M.
    refine pick val {| ps'Heap   := (fst (ps'Heap r_n) + 1, M)
                     ; ps'Buffer := fst (ps'Heap r_n)
                     ; ps'BufLen := 1
                     ; ps'Offset := 0
                     ; ps'Length := 1 |};
    rewrite HeqM; clear HeqM; simpl.
      simplify with monad laws.
      finish honing.
    intuition.
    destruct H0.
    apply of_map_Heap_AbsR; auto.
    apply for_all_within_allocated_mem_mapi; auto; intros.
      eapply for_all_within_allocated_mem_add; eauto; intros; nomega.
    decisions; nomega.
  }
  {
    repeat match goal with
      [ H : _ /\ _ |- _ ] => destruct H
    end; subst.
    rewrite H1, H2, H3, H4.
    rewrite refineEquiv_If_Then_Else_Bind.
    subst H.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.
      unfold peek'.
      remove_dependency.
      erewrite Heap_refine_peek; eauto.
      unfold wrap, FMap_peek.
      rewrite refine_bind_unit; simpl.
      refine pick val {| ps'Heap   := ps'Heap r_n
                       ; ps'Buffer := ps'Buffer r_n
                       ; ps'BufLen := ps'BufLen r_n
                       ; ps'Offset := if ps'Length r_n =? 1
                                      then 0
                                      else ps'Offset r_n + 1
                       ; ps'Length := ps'Length r_n - 1 |}.
        simplify with monad laws.
        finish honing.
      intuition.
    simplify with monad laws; simpl.
    refine pick val r_n.
      simplify with monad laws; simpl.
      finish honing.
    intuition.
  }
  finish_SharpeningADT_WithoutDelegation.
Defined.

(* Strip away the proofy bits. *)
(*
Lemma ByteStringStrip :
  { adt : _ & refineADT (projT1 (ByteStringHeap heap)) adt }.
Proof.
  eexists.
  hone representation using
       (fun (or : PS) (nr : PS') =>
          (* Same (` (psHeap or)) (ps'Heap nr) /\ *)
          ` (psHeap or) = ps'Heap nr /\
          psBuffer or = ps'Buffer nr /\
          psBufLen or = ps'BufLen nr /\
          psOffset or = ps'Offset nr /\
          psLength or = ps'Length nr);
  try simplify with monad laws; simpl.
  {
    refine pick val {| ps'Heap   := ` heap
                     ; ps'Buffer := 0
                     ; ps'BufLen := 0
                     ; ps'Offset := 0
                     ; ps'Length := 0 |}.
      finish honing.
    simpl; intuition.
  }
  {
    repeat match goal with
      [ H : _ /\ _ |- _ ] => destruct H
    end; subst.
    destruct r_o, psHeap; simpl in *.
    rewrite H1, H2, H3, H4.
    rewrite refineEquiv_If_Then_Else_Bind.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.
      unfold poke'; simpl.
      remove_dependency; simpl.
      etransitivity.
        apply refine_under_bind; intros.
        refine pick val {| ps'Heap   := fst a
                         ; ps'Buffer := ps'Buffer r_n
                         ; ps'BufLen := ps'BufLen r_n
                         ; ps'Offset := ps'Offset r_n - 1
                         ; ps'Length := ps'Length r_n + 1 |}.
          simplify with monad laws.
          finish honing.
        intuition.
      rewrite H0.
      finish honing.
    rewrite refineEquiv_If_Then_Else_Bind.
    subst H.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.
      unfold memcpy', poke'; simpl.
      remove_dependency; simpl.
      setoid_rewrite refine_bind_dep_bind_ret; simpl.
      do 2 setoid_rewrite refine_bind_dep_ignore.
      etransitivity.
        apply refine_under_bind; intros.
        etransitivity.
          apply refine_under_bind; intros.
          refine pick val {| ps'Heap   := fst a0
                           ; ps'Buffer := ps'Buffer r_n
                           ; ps'BufLen := ps'BufLen r_n
                           ; ps'Offset := 0
                           ; ps'Length := ps'Length r_n + 1 |}.
            simplify with monad laws.
            finish honing.
          intuition.
        simpl.
        finish honing.
      simpl.
      rewrite H0.
      finish honing.
    rewrite refineEquiv_If_Then_Else_Bind.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.
      unfold alloc', memcpy', poke'.
      remove_dependency; simpl.
      do 3 setoid_rewrite refine_bind_dep_bind_ret.
      simpl; remove_dependency.
      do 3 setoid_rewrite refine_bind_dep_ignore.
      unfold ByteStringHeap.buffer_cons_obligation_2.
      etransitivity.
        apply refine_under_bind; intros.
        etransitivity.
          apply refine_under_bind; intros.
          etransitivity.
            apply refine_under_bind; intros.
            etransitivity.
              apply refine_under_bind; intros.
              refine pick val {| ps'Heap   := fst a2
                               ; ps'Buffer := snd a
                               ; ps'BufLen := ps'Length r_n +1
                               ; ps'Offset := 0
                               ; ps'Length := ps'Length r_n + 1 |}.
                simplify with monad laws.
                finish honing.
              intuition.
            simpl; finish honing.
          simpl; finish honing.
        simpl; finish honing.
      unfold alloc; simpl.
      rewrite H0.
      simpl; finish honing.
    unfold allocate_buffer, alloc', poke'.
    simplify with monad laws; simpl.
    remove_dependency; simpl.
    setoid_rewrite refine_bind_dep_ret.
    autorewrite with monad laws; simpl.
    remove_dependency.
    unfold ByteStringHeap.buffer_cons_obligation_3.
    etransitivity.
      apply refine_under_bind; intros.
      remember (Map _ _) as M.
      refine pick val {| ps'Heap   := M
                       ; ps'Buffer := snd a
                       ; ps'BufLen := 1
                       ; ps'Offset := 0
                       ; ps'Length := 1 |}.
        simplify with monad laws.
        rewrite HeqM.
        finish honing.
      intuition.
    unfold alloc; simpl.
    rewrite H0.
    finish honing.
  }
  {
    repeat match goal with
      [ H : _ /\ _ |- _ ] => destruct H
    end; subst.
    rewrite H1, H2, H3, H4.
    rewrite refineEquiv_If_Then_Else_Bind.
    subst H.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.
      unfold peek'.
      remove_dependency.
      rewrite H0.
      etransitivity.
        apply refine_under_bind; intros.
        refine pick val {| ps'Heap   := ps'Heap r_n
                         ; ps'Buffer := ps'Buffer r_n
                         ; ps'BufLen := ps'BufLen r_n
                         ; ps'Offset := if ps'Length r_n =? 1
                                        then 0
                                        else ps'Offset r_n + 1
                         ; ps'Length := ps'Length r_n - 1 |}.
          simplify with monad laws.
          finish honing.
        intuition.
      simpl.
      finish honing.
    simplify with monad laws; simpl.
    rewrite H0.
    refine pick val r_n.
      simplify with monad laws; simpl.
      finish honing.
    intuition.
  }
  apply reflexivityT.
Defined.

Record CPS := {
  cpsHeap : ComputationalADT.cRep (projT1 HeapImpl);

  cpsBuffer : N;
  cpsBufLen : N;

  cpsOffset : N;
  cpsLength : N
}.

Variable cheap : ComputationalADT.cRep (projT1 HeapImpl).
Variable AbsR : Heap_AbsR (` heap) cheap.

Lemma ByteStringFMap : { adt : _ & refineADT (projT1 ByteStringStrip) adt }.
Proof.
  eexists.
  hone representation using
       (fun (or : PS') (nr : CPS) =>
          Heap_AbsR (ps'Heap or) (cpsHeap nr) /\
          ps'Buffer or = cpsBuffer nr /\
          ps'BufLen or = cpsBufLen nr /\
          ps'Offset or = cpsOffset nr /\
          ps'Length or = cpsLength nr);
  try simplify with monad laws; simpl.
  {
    refine pick val {| cpsHeap   := cheap
                     ; cpsBuffer := 0
                     ; cpsBufLen := 0
                     ; cpsOffset := 0
                     ; cpsLength := 0 |}.
      finish honing.
    intuition.
  }
  {
    repeat match goal with
      [ H : _ /\ _ |- _ ] => destruct H
    end; subst.
    rewrite H1, H2, H3, H4.
    rewrite refineEquiv_If_Then_Else_Bind.
    apply refine_If_Then_Else.
      erewrite Heap_refine_poke; eauto.
      simplify with monad laws; simpl.
      remember (M.mapi _ _) as M.
      refine pick val {| cpsHeap   := (fst (cpsHeap r_n), M)
                       ; cpsBuffer := cpsBuffer r_n
                       ; cpsBufLen := cpsBufLen r_n
                       ; cpsOffset := cpsOffset r_n - 1
                       ; cpsLength := cpsLength r_n + 1 |}.
        simplify with monad laws; simpl.
        rewrite HeqM; clear HeqM.
        finish honing.
      rewrite HeqM; clear HeqM.
      intuition; simpl.
      destruct H0.
      apply of_map_Heap_AbsR.

    split; simpl.
      split; intros.
      apply Map_Map_AbsR.
    rewrite refineEquiv_If_Then_Else_Bind.
    subst H.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.

    rewrite refineEquiv_If_Then_Else_Bind.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.

    simplify with monad laws; simpl.

  }
  {
    repeat match goal with
      [ H : _ /\ _ |- _ ] => destruct H
    end; subst.
    rewrite H1, H2, H3, H4.
    rewrite refineEquiv_If_Then_Else_Bind.
    subst H.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.

    simplify with monad laws; simpl.
    refine pick val r_n.
      simplify with monad laws; simpl.
      finish honing.
    intuition.
  }
  apply reflexivityT.
*)

End Refined.

End ByteStringFMap.
