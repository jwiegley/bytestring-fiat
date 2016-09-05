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
  ByteString.ByteStringHeap
  ByteString.Memory
  ByteString.Heap
  ByteString.Nomega
  ByteString.Relations
  ByteString.Tactics
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Generalizable All Variables.

Module ByteStringFMap (M : WSfun N_as_DT).

Module Import ByteStringHeap := ByteStringHeap M.
Import HeapCanonical.
Import HeapCanonical.HeapADT.
Import HeapCanonical.HeapADT.Heap.
Import HeapCanonical.HeapADT.Heap.FMapExt.
Import HeapCanonical.HeapADT.Heap.FMapExt.P.
Import HeapCanonical.HeapADT.Heap.FMapExt.F.

Section Refined.

Definition cHeapRep := ComputationalADT.cRep (projT1 HeapCanonical).

Variable heap  : Rep HSpec.
Variable heap' : cHeapRep.

Definition Heap_AbsR (or : Rep HeapSpec) nr :=
  M.Equal (resvs or) (resvs (snd nr)) /\
  M.Equal (bytes or) (bytes (snd nr)) /\
  P.for_all (within_allocated_mem (fst nr)) (resvs (snd nr)).

Variable heap_AbsR : Heap_AbsR (` heap) heap'.

(* This style of computational refinement makes use of a separately refined
   heap. Another approach is to refine the heap methods directly, which would
   mean going directly to the metal (but would require replicating much of the
   proof word that is done in HeapFMap.v). *)

Record PS' := {
  ps'Heap : cHeapRep;

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
      unfold poke.
      simplify with monad laws; simpl.
      refine pick val
             {| ps'Heap   :=
                  (fst (ps'Heap r_n),
                   {| resvs := resvs (snd (ps'Heap r_n))
                    ; bytes := M.add (ps'Buffer r_n + (ps'Offset r_n - 1)) d
                                     (bytes (snd (ps'Heap r_n))) |})
              ; ps'Buffer := ps'Buffer r_n
              ; ps'BufLen := ps'BufLen r_n
              ; ps'Offset := ps'Offset r_n - 1
              ; ps'Length := ps'Length r_n + 1 |}.
        simplify with monad laws.
        finish honing.
      simpl in *; intuition.
      destruct H0, H5.
      split; simpl; trivial.
      split; trivial.
      apply add_m; eauto.
    rewrite refineEquiv_If_Then_Else_Bind.
    subst H.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.
      unfold memcpy', poke'; simpl.
      remove_dependency; simpl.
      setoid_rewrite refine_bind_dep_bind_ret; simpl.
      do 2 setoid_rewrite refine_bind_dep_ignore.
      unfold memcpy, poke.
      simplify with monad laws; simpl.
      refine pick val
             {| ps'Heap   :=
                  (fst (ps'Heap r_n),
                   {| resvs := resvs (snd (ps'Heap r_n))
                    ; bytes :=
                        M.add (ps'Buffer r_n + 0) d
                              (copy_bytes (ps'Buffer r_n) (ps'Buffer r_n + 1)
                                          (ps'Length r_n)
                                          (bytes (snd (ps'Heap r_n)))) |})
              ; ps'Buffer := ps'Buffer r_n
              ; ps'BufLen := ps'BufLen r_n
              ; ps'Offset := 0
              ; ps'Length := ps'Length r_n + 1 |}.
        simplify with monad laws.
        finish honing.
      simpl in *; intuition.
      destruct H0, H0.
      split; simpl; trivial.
      split; trivial.
      apply add_m; auto.
      rewrite H0; reflexivity.
    rewrite refineEquiv_If_Then_Else_Bind.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.
      unfold alloc', memcpy', poke'.
      remove_dependency; simpl.
      do 3 setoid_rewrite refine_bind_dep_bind_ret.
      simpl; remove_dependency.
      do 3 setoid_rewrite refine_bind_dep_ignore.
      unfold ByteStringHeap.buffer_cons_obligation_2.
      unfold alloc, memcpy, free, poke, find_free_block.
      simplify with monad laws; simpl.
      refine pick val (fst (ps'Heap r_n)).
        simplify with monad laws; simpl.
        refine pick val
               {| ps'Heap   :=
                    (fst (ps'Heap r_n) + ps'Length r_n + alloc_quantum,
                     {| resvs :=
                          M.remove (ps'Buffer r_n)
                                   (M.add (fst (ps'Heap r_n))
                                          (ps'Length r_n + 1)
                                          (resvs (snd (ps'Heap r_n))))
                      ; bytes :=
                          M.add (fst (ps'Heap r_n) + 0) d
                                (copy_bytes (ps'Buffer r_n)
                                            (fst (ps'Heap r_n) + 1)
                                            (ps'Length r_n)
                                            (bytes (snd (ps'Heap r_n)))) |})
                ; ps'Buffer := fst (ps'Heap r_n)
                ; ps'BufLen := ps'Length r_n + alloc_quantum
                ; ps'Offset := 0
                ; ps'Length := ps'Length r_n + alloc_quantum |}.
          simplify with monad laws.
          finish honing.
        simpl in *; intuition.
        destruct H0, H0.
        split; simpl.
           rewrite H; reflexivity.
        split.
          rewrite H0; reflexivity.
        rewrite <- remove_add.
        apply for_all_remove; relational.
        apply for_all_add_true; relational.
          simplify_maps.
        split.
          apply for_all_remove; relational.
          eapply for_all_impl; auto; relational.
            exact H5.
          intros.
          unfold within_allocated_mem in *.
          nomega.
        nomega.
      destruct H0, H0.
      rewrite H.
      eapply for_all_impl; eauto; relational.
      intros.
      unfold within_allocated_mem in *.
      nomega.
    unfold allocate_buffer, alloc', poke'.
    remove_dependency; simpl.
    unfold Bind2.
    rewrite refine_bind_bind.
    remove_dependency.
    setoid_rewrite refine_bind_dep_bind_ret.
    autorewrite with monad laws; simpl.
    remove_dependency.
    setoid_rewrite refine_bind_dep_ignore.
    unfold alloc, find_free_block.
    simplify with monad laws; simpl.
    refine pick val (fst (ps'Heap r_n)).
      simplify with monad laws; simpl.
      refine pick val
             {| ps'Heap   :=
                  (fst (ps'Heap r_n) + 1,
                   {| resvs := M.add (fst (ps'Heap r_n)) 1
                                     (resvs (snd (ps'Heap r_n)))
                    ; bytes := M.add (fst (ps'Heap r_n) + 0) d
                                     (bytes (snd (ps'Heap r_n))) |})
              ; ps'Buffer := fst (ps'Heap r_n)
              ; ps'BufLen := 1
              ; ps'Offset := 0
              ; ps'Length := 1 |}.
        simplify with monad laws.
        finish honing.
      simpl in *; intuition.
      destruct H0, H0.
      split; simpl.
        rewrite H; reflexivity.
      split.
        rewrite H0; reflexivity.
      rewrite <- remove_add.
      apply for_all_add_true; relational.
        simplify_maps.
      split.
        apply for_all_remove; relational.
        eapply for_all_impl; auto; relational.
          exact H5.
        intros.
        unfold within_allocated_mem in *.
        nomega.
      nomega.
    destruct H0, H0.
    rewrite H.
    eapply for_all_impl; eauto; relational.
    intros.
    unfold within_allocated_mem in *.
    nomega.
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
      unfold peek.
      simplify with monad laws; simpl.
      refine pick val (Ifopt M.find (ps'Buffer r_n + ps'Offset r_n)
                                    (bytes (snd (ps'Heap r_n))) as v
                       Then v
                       Else Zero).
        simplify with monad laws; simpl.
        refine pick val {| ps'Heap   := ps'Heap r_n
                         ; ps'Buffer := ps'Buffer r_n
                         ; ps'BufLen := ps'BufLen r_n
                         ; ps'Offset := if ps'Length r_n =? 1
                                        then 0
                                        else ps'Offset r_n + 1
                         ; ps'Length := ps'Length r_n - 1 |}.
          simplify with monad laws.
          finish honing.
        simpl in *; intuition.
      intros.
      destruct H0, H5.
      destruct (M.find _ _) eqn:Heqe; simpl.
        rewrite H5 in H.
        normalize.
        eapply F.MapsTo_fun; eauto.
      apply F.find_mapsto_iff in H.
      congruence.
    simplify with monad laws; simpl.
    refine pick val r_n.
      simplify with monad laws; simpl.
      finish honing.
    intuition.
  }
  finish_SharpeningADT_WithoutDelegation.
Defined.

End Refined.

End ByteStringFMap.
