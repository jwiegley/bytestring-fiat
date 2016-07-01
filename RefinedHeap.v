Require Import
  Here.ByteString
  Here.Heap
  Here.HeapADT
  Here.Nomega
  Here.BindDep
  Here.FunRelation
  Here.FunMaps
  Here.FMapExt
  Here.Tactics.

Require Import Coq.Structures.OrderedTypeEx.

Module Import E := FunMaps N_as_OT.

Generalizable All Variables.

Section RefinedHeap.

Variable Word8 : Type.
Variable Zero : Word8.

Definition MemoryBlock := MemoryBlock Word8.
Definition HeapSpec := @HeapSpec Word8.

Section MemoryBlock.

Record MemoryBlockC := {
  memCSize : N;
  memCData : M.t Word8
}.

Definition MemoryBlock_AbsR (o : MemoryBlock) (n : MemoryBlockC) : Prop :=
  memSize o = memCSize n /\
  SetMap_AbsR (memData o) (memCData n) eq.

Lemma Empty_MemoryBlock_AbsR : forall n,
  MemoryBlock_AbsR {| memSize  := n; memData  := Empty N Word8 |}
                   {| memCSize := n; memCData := M.empty Word8 |}.
Proof.
  intros.
  split; trivial; simpl; intros.
  exact (Empty_SetMap_AbsR _).
Qed.

End MemoryBlock.

Require Import
  Fiat.ADT
  Fiat.ADTNotation
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Definition within_allocated_mem (n : N) :=
  fun (addr : M.key) (blk : MemoryBlockC) => addr + memCSize blk <=? n.

Lemma within_allocated_mem_Proper : forall n,
  Proper (eq ==> eq ==> eq) (within_allocated_mem n).
Proof.
  unfold Proper, respectful; intros.
  subst; reflexivity.
Qed.

Lemma within_allocated_mem_add : forall n x k e,
  within_allocated_mem n k e
    -> 0 < x
    -> within_allocated_mem (n + x) k e.
Proof.
  unfold within_allocated_mem; intros.
  undecide.
  apply Nle_add_plus; trivial.
Qed.

Lemma within_allocated_mem_at_end : forall n x d,
   within_allocated_mem (n + x) n {| memCSize := x; memCData := d |}.
Proof.
  unfold within_allocated_mem; simpl; intros.
  apply N.leb_refl.
Qed.

Hint Resolve within_allocated_mem_Proper.

Definition Heap_AbsR
           (or : { r : Rep HeapSpec
                 | ADTInduction.fromADT HeapSpec r})
           (nr : N * M.t MemoryBlockC) : Prop :=
  SetMap_AbsR (` or) (snd nr) MemoryBlock_AbsR /\
  P.for_all (within_allocated_mem (fst nr)) (snd nr).

Lemma Lookup_find_block {r_o r_n} (AbsR : Heap_AbsR r_o r_n) addr' blk' :
  Lookup addr' blk' (` r_o)
    -> exists cblk',
        MemoryBlock_AbsR blk' cblk' /\
        M.find addr' (snd r_n) = Some cblk'.
Proof.
  intros.
  destruct AbsR.
  destruct (H0 addr'); clear H0.
  destruct (H2 _ H) as [blk [? ?]]; clear H H2 H3.
  exists blk.
  tauto.
Qed.

Lemma Heap_AbsR_outside_mem
      {r_o r_n} (AbsR : Heap_AbsR r_o r_n)
      (d : {len : N | 0 < len}) :
  forall addr' blk',
    ~ Find (fun a b => overlaps a (memSize b) (fst r_n) (` d))
           addr' blk' (` r_o).
Proof.
  destruct AbsR; intros.
  apply LogicFacts.not_and_implication; intros.
  eapply Lookup_find_block in H1; eauto;
  [| split; [exact H|assumption] ].
  destruct H1 as [cblk' [[? ?] ?]].
  eapply P.for_all_iff with (k:=addr') (e:=cblk') in H0; eauto.
    unfold within_allocated_mem in H0; simpl in H0.
    unfold overlaps.
    destruct d; simpl in *.
    rewrite H1.
    clear -H0 l.
    undecide.
    nomega.
  apply F.find_mapsto_iff.
  assumption.
Qed.

Ltac AbsR_prep :=
  repeat
    match goal with
    | [ H : Heap_AbsR _ _ |- _ ] => unfold Heap_AbsR in H; simpl in H
    | [ |- Heap_AbsR _ _ ] => unfold Heap_AbsR; simpl
    | [ H : _ /\ _ |- _ ] => destruct H; simpl in H
    | [ |- _ /\ _ ] => split
    end; simpl.

Lemma HeapImpl : FullySharpened HeapSpec.
Proof.
  start sharpening ADT.
  eapply SharpenStep; [ apply (projT2 (@HeapSpecADT Word8)) |].

  hone representation using Heap_AbsR.

  refine method emptyS.
  {
    unfold empty.
    remove_dependency.
    simplify with monad laws.

    refine pick val (0%N, @M.empty _).
      finish honing.

    AbsR_prep.
    - apply Empty_SetMap_AbsR; trivial.
    - apply E.for_all_empty; trivial.
  }

  refine method allocS.
  {
    unfold Heap_AbsR, alloc, find_free_block.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val (fst r_n).
      Focus 2.
      apply Heap_AbsR_outside_mem; trivial.

    simplify with monad laws; simpl.
    refine pick val (fst r_n + proj1_sig d,
                     M.add (fst r_n)
                           {| memCSize := proj1_sig d
                            ; memCData := M.empty _ |} (snd r_n)).
      simplify with monad laws.
      finish honing.

    AbsR_prep.
    - apply Update_SetMap_AbsR; trivial.
      apply Empty_MemoryBlock_AbsR; trivial.
    - apply E.for_all_add; trivial.
        eapply E.for_all_impl; eauto; intros.
        destruct d; simpl.
        apply within_allocated_mem_add; trivial.
      apply within_allocated_mem_at_end.
  }

  refine method freeS.
  {
    unfold free, free_block.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val (fst r_n, M.remove d (snd r_n)).
      simplify with monad laws.
      finish honing.

    AbsR_prep.
    - apply Remove_SetMap_AbsR; trivial.
    - apply E.for_all_remove; trivial.
  }

  refine method reallocS.
  {
    unfold Heap_AbsR, realloc, find_free_block.
    remove_dependency.
    simplify with monad laws; simpl.

    admit.
  }

  refine method peekS.
  {
    unfold Heap_AbsR, peek.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val
      (Ifopt find_nearest d (snd r_n) as p
       Then IfDec within (fst p) (memCSize (snd p)) d
            Then Ifopt M.find (d - fst p) (memCData (snd p)) as v
                 Then v
                 Else Zero
            Else Zero
       Else Zero).

    simplify with monad laws; simpl.
    refine pick val r_n.
      simplify with monad laws.
      finish honing.

    AbsR_prep; assumption.

    intros; subst; clear H.
    destruct H1.
    admit.
  }

  refine method pokeS.
  {
    unfold poke, set_address.
    remove_dependency.
    simplify with monad laws; simpl.

    refine pick val
      (fst r_n,
       M.mapi (fun addr blk =>
                 IfDec within addr (memCSize blk) d
                 Then {| memCSize := memCSize blk
                       ; memCData := M.add (d - addr) d0
                                           (memCData blk) |}
                 Else blk) (snd r_n)).
      simplify with monad laws.
      finish honing.

    AbsR_prep.
    - apply Map_SetMap_AbsR; auto; intros.
      admit.
    - admit.
  }

  refine method memcpyS.
  {
    unfold memcpy.
    remove_dependency.
    simplify with monad laws; simpl.

    admit.
  }

  refine method memsetS.
  {
    unfold memset.
    remove_dependency.
    simplify with monad laws; simpl.

    admit.
  }

  finish_SharpeningADT_WithoutDelegation.
Abort.

End RefinedHeap.
