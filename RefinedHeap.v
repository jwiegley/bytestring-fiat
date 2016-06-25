Require Import Fiat.ADT Fiat.ADTNotation.

Require Import
  Coq.Lists.List
  Coq.Arith.Arith
  Coq.NArith.NArith
  Coq.FSets.FMapAVL
  Coq.FSets.FMapFacts
  Coq.Structures.OrderedTypeEx
  Omega.

Module M := FMapAVL.Make(N_as_OT).
Module F := FMapFacts.Facts M.

Require Import
  Here.ByteString
  Here.LibExt
  Here.Heap.

Require Import
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Tactic Notation "refine" "method" constr(name) :=
  match goal with
    | [ _ : constructorType ?A (consDom {| consID := name
                                         ; consDom := _ |}) |- _ ] =>
      idtac "Constructor"
    | [ _ : methodType ?A (methDom {| methID := name
                                    ; methDom := _
                                    ; methCod := _ |})  _ |- _ ] =>
      idtac "Method"
    | _ =>
      fail "Incorrect method name"
  end.

Generalizable All Variables.

Open Scope N_scope.

Theorem Nle_add_plus : forall n m o, 0 < o -> n <= m -> n <= m + o.
Proof.
  intros.
  rewrite <- (N.add_0_r n).
  apply N.add_le_mono; nomega.
Qed.

Theorem Nle_impossible : forall n m, 0 < m -> n + m <= n -> False.
Proof.
  intros.
  rewrite <- (N.add_0_r n) in H0 at 2.
  apply N.add_le_mono_l in H0.
  nomega.
Qed.

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

Lemma within_reflect : forall x y a,
  within x y a <-> (x <=? a) && (a <? x + y) = true.
Proof.
  intros.
  unfold within.
  split; intros; try nomega.
  apply andb_true_iff; split; nomega.
Qed.

Theorem Mfind_List_find : forall d base m x,
  M.find base m = Some x
    -> base = memCAddr x
    -> within (memCAddr x) (memCSize x) d
    -> (forall a b i,
           M.In (memCAddr a) m ->
           M.In (memCAddr b) m ->
           within (memCAddr a) (memCSize a) i ->
           within (memCAddr b) (memCSize b) i ->
           a = b)
    -> List.find (fun p : M.key * MemoryBlockC =>
                    (fst p =? memCAddr (snd p)) &&
                    ((memCAddr (snd p) <=? d) &&
                     (d <? memCAddr (snd p) + memCSize (snd p))))
                 (M.elements m) = Some (base, x).
Proof.
  intros.
  rewrite F.elements_o in H.
  setoid_rewrite F.in_find_iff in H2.
  setoid_rewrite F.elements_o in H2.
  generalize dependent base.
  induction (M.elements (elt:=MemoryBlockC) m); simpl in *.
    discriminate.
  destruct a; simpl in *; intros.
  unfold F.eqb, M.E.eq_dec in H.
  destruct (N.eq_dec base k); subst; inv H.
    rewrite N.eqb_refl, andb_true_l.
    apply within_reflect in H1.
    setoid_rewrite H1.
    reflexivity.
  decisions.
    apply andb_true_iff in Heqe.
    destruct Heqe.
    apply within_reflect in H0.
    specialize (H2 m0 x k).
    apply N.eqb_eq in H; subst.
    (* jww (2016-06-24): I need a way of knowing that if two memory blocks
       overlap the same point, they must be the same block. *)
    admit.
  apply IHl; intros.
  - eapply H2.
    + unfold F.eqb, M.E.eq_dec.
      destruct (N.eq_dec (memCAddr a) k).
        unfold not; intros; discriminate.
      exact H.
    + unfold F.eqb, M.E.eq_dec.
      destruct (N.eq_dec (memCAddr b) k).
        unfold not; intros; discriminate.
      exact H0.
    + exact H4.
    + exact H5.
  - exact H3.
  - reflexivity.
Admitted.

Lemma HeapImpl : FullySharpened HeapSpec.
Proof.
  start sharpening ADT.
  hone representation using
    (fun (or : Ensemble MemoryBlock) (nr : N * M.t MemoryBlockC) =>
       ADTInduction.fromADT HeapSpec or /\
       forall addr size,
         (forall data,
            In _ or {| memAddr := addr
                     ; memSize := size
                     ; memData := data |} ->
            (addr + size <= fst nr /\
             exists cdata,
               M.find addr (snd nr)
                 = Some {| memCAddr := addr
                         ; memCSize := size
                         ; memCData := cdata |} /\
               (forall i v, In _ data (i, v) <-> M.find i cdata = Some v))) /\
         (forall cdata,
             M.find addr (snd nr)
               = Some {| memCAddr := addr
                       ; memCSize := size
                       ; memCData := cdata |} ->
             (addr + size <= fst nr /\
              exists data,
                In _ or {| memAddr := addr
                         ; memSize := size
                         ; memData := data |} /\
                (forall i v, In _ data (i, v) <-> M.find i cdata = Some v)))).

  refine method emptyS.
  {
    simplify with monad laws.
    refine pick val (0%N, @M.empty _).
      finish honing.
    split; intros.
      apply ADTInduction.fromADTConstructor with (cidx:=Fin.F1).
      constructor.
    simpl; split; intros.
      inv H0.
    apply F.find_mapsto_iff, F.empty_mapsto_iff in H0.
    contradiction.
  }

  refine method allocS.
  {
    unfold find_free_block.
    simplify with monad laws.
    refine pick val (fst r_n).
      simplify with monad laws.
      refine pick val (fst r_n + proj1_sig d,
                       M.add (fst r_n)
                             {| memCAddr := fst r_n
                              ; memCSize := proj1_sig d
                              ; memCData := M.empty _ |}
                             (snd r_n)).
        simplify with monad laws; simpl.
        finish honing.
      clear H.
      destruct H0.
      split; intros.
        apply ADTInduction.fromADTMethod
          with (midx:=Fin.F1) (r:=r_o); trivial.
        exists d.
        exists (fst r_n).
        simpl.
        apply BindComputes with (a:=fst r_n).
          unfold find_free_block.
          apply PickComputes; intros.
          unfold found_block_at_base in H1.
          destruct (H0 addr' len') as [H2 _]; clear H0.
          destruct (H2 data' H1) as [H3 _]; clear H2.
          unfold overlaps.
          nomega.
        reflexivity.
      simpl; split; intros.
        apply Add_inv in H1.
        destruct H1.
          destruct (H0 addr size) as [? ?]; clear H0;
          destruct (H2 data H1) as [? ?].
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
              destruct (H3 _ H4).
              destruct H7.
              destruct H7.
              pose proof (allocations_have_size H _ _ _ H7).
              clear -H0 H9.
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
          inv H1.
        apply F.find_mapsto_iff, F.empty_mapsto_iff in H1.
        contradiction.
      apply F.find_mapsto_iff in H1.
      apply F.add_mapsto_iff in H1.
      destruct H1; destruct H1; tsubst.
        split; intros.
          nomega.
        destruct (H0 (fst r_n) (` d)).
        eexists.
        split; intros.
          right; constructor.
        split; intros.
          inv H3.
        apply F.find_mapsto_iff, F.empty_mapsto_iff in H3.
        contradiction.
      apply F.find_mapsto_iff in H2.
      destruct (H0 addr size); clear H0.
      destruct (H4 _ H2).
      destruct d; simpl in *.
      split; intros.
        apply Nle_add_plus; trivial.
      destruct H5.
      exists x0.
      split; intros.
        left.
        apply H5.
      apply H5.
    clear H.
    unfold found_block_at_base.
    intros.
    destruct H0.
    destruct (H1 addr' len'); clear H1.
    destruct (H2 _ H).
    unfold overlaps.
    nomega.
  }

  refine method freeS.
  {
    unfold free_block.
    simplify with monad laws; simpl.
    refine pick val (fst r_n, M.remove d (snd r_n)).
      simplify with monad laws; simpl.
      finish honing.
    destruct H0; simpl in *.
    split; intros.
      apply ADTInduction.fromADTMethod
        with (midx:=Fin.FS (Fin.F1)) (r:=r_o); trivial.
      exists d.
      exists tt.
      simpl.
      constructor.
    unfold free_block.
    split; intros.
      destruct (H1 addr size); clear H1 H4.
      inv H2.
      destruct (H3 _ H1).
      split; intros; trivial.
      destruct H5.
      exists x.
      split; intros.
        rewrite F.remove_neq_o.
          apply H5.
        unfold Ensembles.In in H4.
        exact H4.
      apply H5.
    destruct (H1 addr size); clear H1 H3.
    apply F.find_mapsto_iff in H2.
    apply F.remove_mapsto_iff in H2.
    destruct H2.
    apply F.find_mapsto_iff in H2.
    destruct (H4 _ H2); clear H2 H4.
    split; trivial.
    destruct H5.
    exists x.
    split.
      constructor.
        apply H2.
      unfold not; intros.
      unfold Ensembles.In in H4; simpl in H4; subst.
      tauto.
    apply H2.
  }

  refine method reallocS.
  {
    admit.
  }

  refine method peekS.
  {
    unfold found_block.
    simplify with monad laws; simpl.
    refine pick val
      (Ifopt List.find (fun p =>
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
       Else Zero).
      simplify with monad laws; simpl.
      refine pick val r_n.
        simplify with monad laws; simpl.
        unfold If_Opt_Then_Else; simpl.
        finish honing.
      apply H0.
    intros; simpl; clear H.
    destruct H0, H1.
    destruct (H0 base len'); clear H4.
    destruct (H3 _ H1); clear H3.
    destruct H5.
    destruct H3.
    rewrite Mfind_List_find
      with (base:=base)
           (x:={| memCAddr := base
                ; memCSize := len'
                ; memCData := x |}); simpl; trivial.
      destruct (M.find (elt:=Word8) (d - base) x) eqn:Heqe; simpl.
        left; apply H5; assumption.
      right; reflexivity.
    admit.
  }

  refine method pokeS.
  {
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