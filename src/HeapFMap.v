Require Import
  ByteString.Relations
  ByteString.TupleEnsembles
  ByteString.Nomega
  ByteString.BindDep
  ByteString.ADTInduction
  ByteString.Tactics
  ByteString.Heap
  ByteString.HeapADT
  ByteString.Within
  ByteString.DefineAbsR
  ByteString.Same_set
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Module HeapFMap (M : WSfun N_as_DT).

Module Import Within := Within M.
Module Import Define := Define_AbsR M.

Import Within.Block.
Import Block.FunMaps.

Require Import Fiat.ADT Fiat.ADTNotation.

Definition Heap_AbsR
           (or : Rep HeapSpec)
           (nr : N * M.t MemoryBlockC) : Prop :=
  Map_AbsR MemoryBlock_AbsR or (snd nr) /\
  P.for_all (within_allocated_mem (fst nr)) (snd nr).

Theorem heaps_refine_to_maps : forall r : Rep HeapSpec, fromADT _ r ->
  exists m : M.t MemoryBlockC, Map_AbsR MemoryBlock_AbsR r m.
Proof.
  intros; apply every_finite_map_has_an_associated_fmap; auto.
  - apply heap_is_finite; auto.
  - apply allocations_functional; auto.
Qed.

Ltac related_maps' :=
  repeat (
    related_maps; auto with maps;
    try match goal with
      [ |- MemoryBlock_AbsR {| memSize := _;  memData := _ |}
                            {| memCSize := _; memCData := _ |} ] =>
      apply MemoryBlock_AbsR_impl; auto with maps
    end).

Ltac AbsR_prep :=
  repeat
    match goal with
    | [ H : Heap_AbsR _ _ |- _ ] => unfold Heap_AbsR in H; simpl in H
    | [ |- Heap_AbsR _ _ ] => unfold Heap_AbsR; simpl
    | [ H : _ /\ _ |- _ ] => destruct H; simpl in H
    | [ |- _ /\ _ ] => split
    end; simpl; eauto; eauto with maps; related_maps'.

Require Import Fiat.ADTRefinement Fiat.ADTRefinement.BuildADTRefinements.

Ltac apply_for_all :=
  match goal with
  | [ H1 : is_true (P.for_all ?P ?m),
      H2 : M.MapsTo ?k ?e ?m |- _ ] =>
    let H3 := fresh "H3" in
    assert (H3 : Proper (eq ==> eq ==> eq) P) by auto;
    pose proof (proj1 (@P.for_all_iff _ P H3 m) H1 k e H2)
  | [ H1 : P.for_all ?P ?m = true,
      H2 : M.MapsTo ?k ?e ?m |- _ ] =>
    let H3 := fresh "H3" in
    assert (H3 : Proper (eq ==> eq ==> eq) P) by auto;
    pose proof (proj1 (@P.for_all_iff _ P H3 m) H1 k e H2)
  end.

Lemma Heap_AbsR_outside_mem
      {r_o r_n} (AbsR : Heap_AbsR r_o r_n)
      (d : {len : N | 0 < len}) :
  All (fun addr' blk' =>
         ~ overlaps addr' (memSize blk') (fst r_n) (` d)) r_o.
Proof.
  intros addr blk H.
  apply AbsR in H; destruct H as [? [? ?]].
  rewrite (proj1 H0).
  destruct AbsR as [_ ?].
  apply_for_all. nomega.
Qed.

Lemma of_map_Heap_AbsR : forall sz m,
  P.for_all (within_allocated_mem sz) m
    -> Heap_AbsR (of_map MemoryBlock_AbsR m) (sz, m).
Proof.
  split; intros; trivial.
  apply of_map_Map_AbsR; auto.
Qed.

Definition wrap A (x : (N * M.t MemoryBlockC) * A) : Comp (Rep HeapSpec * A) :=
  ret (of_map MemoryBlock_AbsR (snd (fst x)), snd x).
Arguments wrap {A} x _ /.

Definition FMap_alloc (r_n : N * M.t MemoryBlockC)
           (len : N | 0 < len) :=
  ((fst r_n + ` len,
    M.add (fst r_n) {| memCSize := ` len
                     ; memCData := M.empty _ |} (snd r_n)),
   fst r_n).

Theorem Heap_refine_alloc `(AbsR : Heap_AbsR r_o r_n) len :
  refine (alloc r_o len) (wrap (FMap_alloc r_n len)).
Proof.
  unfold wrap, FMap_alloc; intros; simpl.
  unfold alloc, FindFreeBlock.

  refine pick val (fst r_n).
    simplify with monad laws; simpl.
    apply refine_ret_ret_fst_Same; auto.
    apply Same_Same_set, of_map_Same.
    destruct AbsR.
    related_maps'.

  apply Heap_AbsR_outside_mem; assumption.
Qed.

Definition FMap_free (r_n : N * M.t MemoryBlockC) addr :=
  ((fst r_n, M.remove addr (snd r_n)), tt).

Theorem Heap_refine_free `(AbsR : Heap_AbsR r_o r_n) addr :
  refine (free r_o addr) (wrap (FMap_free r_n addr)).
Proof.
  unfold wrap, FMap_free; intros; simpl.
  unfold free, FindBlock.
  apply refine_ret_ret_fst_Same; trivial.
  apply Same_Same_set, of_map_Same.
  destruct AbsR.
  related_maps'.
Qed.

Definition FMap_realloc (r_n : N * M.t MemoryBlockC)
           addr (len : N | 0 < len) :=
  match M.find addr (snd r_n) with
  | Some cblk =>
    let data := P.filter (fun k _ => k <? ` len) (memCData cblk) in
    if ` len <=? memCSize cblk
    then ((fst r_n,
           M.add addr {| memCSize := ` len
                       ; memCData := data |} (snd r_n)), addr)
    else ((fst r_n + ` len,
           M.add (fst r_n) {| memCSize := ` len
                            ; memCData := data |}
                 (M.remove addr (snd r_n))), fst r_n)
  | None => ((fst r_n + ` len,
              M.add (fst r_n)
                    {| memCSize := ` len
                     ; memCData := M.empty _ |} (snd r_n)), fst r_n)
  end.

Theorem Heap_refine_realloc `(AbsR : Heap_AbsR r_o r_n) addr len :
  (forall addr1 blk1, Lookup addr1 blk1 r_o ->
   forall addr2 blk2, Lookup addr2 blk2 r_o -> addr1 <> addr2 ->
     ~ overlaps addr1 (memSize blk1) addr2 (memSize blk2)) ->
  refine (realloc r_o addr len) (wrap (FMap_realloc r_n addr len)).
Proof.
  unfold wrap, FMap_realloc; intros H9; simpl.
  unfold realloc, FindBlock, FindFreeBlock.

  refine pick val (option_map to_MemoryBlock (M.find addr (snd r_n))).
    Focus 2.
    destruct (M.find _ _) eqn:Heqe; simpl.
      normalize.
      apply AbsR.
      exists m.
      intuition.
    unfold not; intros.
    destruct AbsR.
    eapply Member_Map_AbsR in H0; eauto.
    rewrite F.mem_find_b, Heqe in H0.
    destruct H0.
    intuition.

  simplify with monad laws.
  refine pick val
    (Ifopt M.find addr (snd r_n) as cblk
     Then If ` len <=? memCSize cblk
          Then addr
          Else fst r_n
     Else fst r_n).
    Focus 2.
    intros ???.
    repeat teardown.
    pose proof (H9 _ b H0).
    apply AbsR in H0; do 2 destruct H0.
    destruct AbsR.
    apply_for_all.
    simpl in *.
    destruct (M.find _ _) eqn:Heqe; simpl.
      destruct (_ <=? memCSize m) eqn:Heqe1; simpl.
        normalize.
        apply_for_all.
        apply H3 in Heqe; destruct Heqe, H10.
        specialize (H1 _ _ H10 H).
        rewrite <- (proj1 H11) in Heqe1.
        nomega.
      swap_sizes; nomega.
    swap_sizes; nomega.

  simplify with monad laws.
  destruct (M.find _ (snd r_n)) eqn:Heqe; simpl;
  [ destruct (_ <=? memCSize m) eqn:Heqe1; simpl | ];
  apply refine_ret_ret_fst_Same; trivial;
  apply Same_Same_set, of_map_Same;
  destruct AbsR.
  - rewrite <- remove_add.
    related_maps'; relational.
      split; nomega.
    apply of_map_Map_AbsR; auto.
  - related_maps'; relational.
      split; nomega.
    apply of_map_Map_AbsR; auto.
  - related_maps'.
Qed.

Definition FMap_peek (r_n : N * M.t MemoryBlockC) addr :=
  (r_n,
   Ifopt find_if (withinMemBlockC addr) (snd r_n) as p
   Then Ifopt M.find (addr - fst p) (memCData (snd p)) as v
        Then v Else Zero
   Else Zero).

Theorem Peek_in_heap
        {r_o : { r | fromADT HeapSpec r }}
        {r_n} (AbsR : Heap_AbsR (` r_o) r_n) pos :
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

Theorem Heap_refine_peek `(AbsR : Heap_AbsR r_o r_n) addr :
  refine (peek r_o addr) (wrap (FMap_peek r_n addr)).
Proof.
  unfold wrap, FMap_peek; intros; simpl.
  unfold peek, FindBlockThatFits.

  refine pick val
    (Ifopt find_if (withinMemBlockC addr) (snd r_n) as p
     Then Some (fst p, to_MemoryBlock (snd p))
     Else None).
    Focus 2.
    destruct (find_if _ (snd r_n)) eqn:Heqe1; simpl in *.
      apply find_if_inv in Heqe1; auto.
      split.
        destruct AbsR.
        eapply Lookup_of_map; eauto.
        intuition.
      unfold withinMemBlockC in Heqe1; simpl in Heqe1.
      nomega.
    intros ????.
    apply AbsR in H; destruct H, H.
    apply find_if_not_inv in Heqe1; auto.
    assert (Proper (eq ==> eq ==> eq)
                   (negb \oo withinMemBlockC addr)) by auto.
    pose proof (proj1 (P.for_all_iff H2 _) Heqe1 a x H).
    unfold withinMemBlockC in H3; simpl in H3.
    rewrite (proj1 H1) in H0.
    unfold negb in H3.
    decisions; [discriminate|nomega].

  simplify with monad laws.
  refine pick val
    (Ifopt find_if (withinMemBlockC addr) (snd r_n) as p
     Then Ifopt M.find (addr - fst p) (memCData (snd p)) as v
          Then v Else Zero
     Else Zero).
    Focus 2.
    destruct (find_if _ (snd r_n)) eqn:Heqe; simpl; intros;
    [|discriminate]; inv H; simpl in *.
    apply find_if_inv in Heqe; auto; destruct Heqe.
    apply of_map_MapsTo in H0.
    destruct H0 as [cblk [? ?]]; subst.
    apply F.find_mapsto_iff in H0.
    rewrite H0; reflexivity.

  simplify with monad laws; simpl.
  apply refine_ret_ret_fst_Same; trivial;
  apply Same_Same_set, of_map_Same;
  destruct AbsR; assumption.
Qed.

Definition FMap_poke (r_n : N * M.t MemoryBlockC) addr w :=
  ((fst r_n,
    M.mapi (fun addr' cblk' =>
              Ifdec within addr' (memCSize cblk') addr
              Then {| memCSize := memCSize cblk'
                    ; memCData := M.add (addr - addr') w
                                        (memCData cblk') |}
              Else cblk') (snd r_n)), tt).

Theorem Heap_refine_poke `(AbsR : Heap_AbsR r_o r_n) addr w :
  refine (poke r_o addr w) (wrap (FMap_poke r_n addr w)).
Proof.
  unfold wrap, FMap_poke; intros; simpl.
  unfold poke.
  apply refine_ret_ret_fst_Same; trivial;
  apply Same_Same_set, of_map_Same;
  destruct AbsR.
  related_maps'; relational.
  swap_sizes.
  decisions; trivial.
  destruct H2.
  related_maps'.
Qed.

Definition FMap_memcpy (r_n : N * M.t MemoryBlockC) addr1 addr2 len :=
  ((fst r_n,
    If 0 <? len
    Then
      Ifopt find_if (fun addr src => fits_bool addr (memCSize src) addr1 len)
                    (snd r_n) as p
      Then
        M.mapi (fun daddr dst =>
                  Ifdec fits daddr (memCSize dst) addr2 len
                  Then {| memCSize := memCSize dst
                        ; memCData :=
                            let soff := addr1 - fst p in
                            let doff := addr2 - daddr in
                            copy_block (snd p) soff dst doff len |}
                  Else dst)
               (snd r_n)
      Else snd r_n
    Else snd r_n), tt).

Theorem Heap_refine_memcpy `(AbsR : Heap_AbsR r_o r_n) addr1 addr2 len :
  refine (memcpy r_o addr1 addr2 len)
         (wrap (FMap_memcpy r_n addr1 addr2 len)).
Proof.
  unfold wrap, FMap_memcpy; intros; simpl.
  unfold memcpy, FindBlockThatFits.

  etransitivity.
    apply refine_Ifdec_Then_Else; intros.
    refine pick val
      (Ifopt find_if (fun addr src =>
                        fits_bool addr (memCSize src) addr1 len)
                     (snd r_n) as p
       Then Some (fst p,
                  {| memSize := memCSize (snd p)
                   ; memData := of_map eq (memCData (snd p)) |})
       Else None).
      Focus 2.
      destruct AbsR.
      destruct (find_if _ (snd r_n)) eqn:Heqe1; simpl in *.
        apply find_if_inv in Heqe1; relational.
        split.
          apply Lookup_of_map with (r_n:=snd r_n); intuition.
        nomega.
      apply find_if_not_inv in Heqe1; relational.
      eapply All_Map_AbsR in Heqe1; eauto; relational.
      swap_sizes.
      destruct (fits_bool _ _ _)%bool eqn:Heqe2; split; intros; nomega.
      simplify with monad laws.
      finish honing.
    reflexivity.

  destruct AbsR.
  decisions; simpl;
  apply refine_ret_ret_fst_Same; trivial;
  apply Same_Same_set, of_map_Same; trivial.

  destruct (find_if _ _) eqn:Heqe1; simpl; trivial.
  related_maps'; relational.
  swap_sizes.
  decisions; trivial.
  related_maps'; relational.
  apply CopyBlock_Map_AbsR; auto.
Qed.

Definition FMap_memset (r_n : N * M.t MemoryBlockC) addr len w :=
  ((fst r_n,
    M.mapi (fun addr' cblk' =>
              Ifdec fits addr' (memCSize cblk') addr len
              Then {| memCSize := memCSize cblk'
                    ; memCData :=
                        let base := addr - addr' in
                        N.peano_rect (fun _ => M.t Word8)
                                     (memCData cblk')
                                     (fun i => M.add (base + i) w) len |}
              Else cblk') (snd r_n)), tt).

Theorem Heap_refine_memset `(AbsR : Heap_AbsR r_o r_n) addr len w :
  refine (memset r_o addr len w) (wrap (FMap_memset r_n addr len w)).
Proof.
  unfold wrap, FMap_memset; intros; simpl.
  unfold memset.

  destruct AbsR.
  decisions; simpl;
  apply refine_ret_ret_fst_Same; trivial;
  apply Same_Same_set, of_map_Same; trivial.

  related_maps'; relational.
  swap_sizes.
  decisions; trivial.
  related_maps'; relational.
  destruct H2.
  apply Define_Map_AbsR; auto.
Qed.

Tactic Notation "refine" "pick" "map" "with" constr(v) :=
  match goal with
  | [ |- context[Heap_AbsR (of_map _ ?M) _] ] =>
    let m := fresh "m" in
    let Heqm := fresh "Heqm" in
    remember M as m eqn:Heqm;
    refine pick val (v, m); rewrite Heqm; clear Heqm;
    [ simplify with monad laws; simpl
    | apply of_map_Heap_AbsR ]
  end.

Ltac sharpen_method H v :=
  match goal with
  | [ r_o : { r : EMap N MemoryBlock | fromADT HeapSpec r },
      AbsR : Heap_AbsR _ _ |- _ ] =>
    let Hr_o := fresh "Hr_o" in
    remove_dependency; destruct r_o as [r_o Hr_o];
    erewrite H with (r_o:=r_o) || erewrite H; eauto;
    try (
      simplify with monad laws; simpl;
      refine pick map with v;
      [ try simplify with monad laws; simpl; finish honing
      | destruct AbsR; simpl in * ])
  end; auto.

Lemma HeapImpl : FullySharpened HeapSpec.
Proof.
  start sharpening ADT.
  eapply SharpenStep; [ apply (projT2 HeapSpecADT) |].

  hone representation using (fun or nr => Heap_AbsR (` or) nr).

  refine method emptyS.
  {
    remove_dependency.
    simplify with monad laws.
    refine pick val (0%N, @M.empty _).
      finish honing.
    AbsR_prep.
  }

  refine method allocS.
  {
    sharpen_method @Heap_refine_alloc (fst r_n + ` d).
    eapply for_all_within_allocated_mem_add; eauto; nomega.
  }

  refine method freeS.
    sharpen_method @Heap_refine_free (fst r_n).

  refine method reallocS.
  {
    sharpen_method @Heap_refine_realloc
                   (Ifopt M.find d (snd r_n) as cblk
                    Then If ` d0 <=? memCSize cblk
                         Then fst r_n
                         Else fst r_n + ` d0
                    Else fst r_n + ` d0).

    - unfold FMap_realloc.
      destruct (M.find _ (snd r_n)) eqn:Heqe; simpl;
      [ destruct (_ <=? memCSize _) eqn:Heqe1; simpl | ];
      normalize; try apply_for_all;
      eapply for_all_within_allocated_mem_add; eauto; simpl; nomega.
    - apply allocations_no_overlap; assumption.
  }

  refine method peekS.
    sharpen_method @Heap_refine_peek (fst r_n).

  refine method pokeS.
  {
    sharpen_method @Heap_refine_poke (fst r_n).
    apply for_all_within_allocated_mem_mapi; auto; intros.
    decisions; nomega.
  }

  refine method memcpyS.
  {
    sharpen_method @Heap_refine_memcpy (fst r_n).
    destruct (0 <? d1) eqn:Heqe, (find_if _ _) eqn:Heqe1; simpl; auto.
    apply for_all_within_allocated_mem_mapi; auto; intros.
    decisions; nomega.
  }

  refine method memsetS.
  {
    sharpen_method @Heap_refine_memset (fst r_n).
    apply for_all_within_allocated_mem_mapi; auto; intros.
    decisions; nomega.
  }

  finish_SharpeningADT_WithoutDelegation.
Defined.

End HeapFMap.
