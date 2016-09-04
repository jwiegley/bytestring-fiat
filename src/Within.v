Require Import
  ByteString.Nomega
  ByteString.HeapEns
  ByteString.HeapEnsADT
  ByteString.FMapExt
  ByteString.Relations
  ByteString.MemoryBlockC
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Module Within (M : WSfun N_as_DT).

Module X := FMapExt N_as_DT M.
Include X.

Module Import Block := MemoryBlockC M.

Definition within_allocated_mem (n : N) :=
  fun (addr : M.key) (blk : MemoryBlockC) => addr + memCSize blk <=? n.
Arguments within_allocated_mem n addr blk /.

Program Instance within_allocated_mem_Proper :
  Proper (eq ==> eq ==> eq ==> eq) within_allocated_mem.
Obligation 1. relational; subst; reflexivity. Qed.

Hint Extern 4 (Proper (eq ==> eq ==> eq) (within_allocated_mem _)) =>
  apply within_allocated_mem_Proper; auto.

Lemma within_allocated_mem_add : forall n x k e,
  within_allocated_mem n k e = true
    -> 0 < x
    -> within_allocated_mem (n + x) k e = true.
Proof. nomega. Qed.

Lemma within_allocated_mem_at_end : forall n x d,
   within_allocated_mem (n + x) n {| memCSize := x; memCData := d |} = true.
Proof. nomega. Qed.

Lemma for_all_within_allocated_mem_add : forall n m o addr blk,
  P.for_all (within_allocated_mem n) m = true ->
  n <= o -> addr + memCSize blk <= o ->
  P.for_all (within_allocated_mem o) (M.add addr blk m) = true.
Proof.
  intros.
  apply P.for_all_iff; auto; intros.
  simplify_maps.
    nomega.
  eapply P.for_all_iff in H; relational; [|exact H6].
  unfold within_allocated_mem in H.
  nomega.
Qed.

Hint Resolve for_all_within_allocated_mem_add.

Lemma for_all_within_allocated_mem_empty :
  P.for_all (within_allocated_mem 0) (M.empty MemoryBlockC) = true.
Proof.
  apply P.for_all_iff; auto.
Qed.

Hint Resolve for_all_within_allocated_mem_empty.

Lemma for_all_within_allocated_mem_remove : forall n m addr,
  P.for_all (within_allocated_mem n) m = true ->
  P.for_all (within_allocated_mem n) (M.remove addr m) = true.
Proof.
  intros.
  apply for_all_remove; auto.
Qed.

Hint Resolve for_all_within_allocated_mem_remove.

Require Import Fiat.ADT Fiat.ADTNotation.

Lemma for_all_within_allocated_mem_If n m (mres : bool) f :
  (If mres
   Then P.for_all (within_allocated_mem f) m
   Else P.for_all (within_allocated_mem n) m) = true ->
  P.for_all (within_allocated_mem
               (If mres
                Then f
                Else n)) m.
Proof. destruct mres; simpl; intros; assumption. Qed.

Hint Resolve for_all_within_allocated_mem_If.

Lemma for_all_within_allocated_mem_Ifopt n m A (mres : option A) f :
  (Ifopt mres as p
   Then P.for_all (within_allocated_mem (f p)) m
   Else P.for_all (within_allocated_mem n) m) = true ->
  P.for_all (within_allocated_mem
               (Ifopt mres as p
                Then f p
                Else n)) m.
Proof. destruct mres; simpl; intros; assumption. Qed.

Hint Resolve for_all_within_allocated_mem_Ifopt.

Lemma for_all_within_allocated_mem_Ifdec n m `{Decidable mres} f :
  (Ifdec mres
   Then P.for_all (within_allocated_mem f) m
   Else P.for_all (within_allocated_mem n) m) = true ->
  P.for_all (within_allocated_mem
               (Ifdec mres
                Then f
                Else n)) m.
Proof. decisions; intros; assumption. Qed.

Hint Resolve for_all_within_allocated_mem_Ifdec.

Lemma for_all_within_allocated_mem_If_r n m (mres : bool) f :
  (If mres
   Then P.for_all (within_allocated_mem n) f
   Else P.for_all (within_allocated_mem n) m) = true ->
  P.for_all (within_allocated_mem n) (If mres
                                      Then f
                                      Else m).
Proof. destruct mres; simpl; intros; assumption. Qed.

Hint Resolve for_all_within_allocated_mem_If_r.

Lemma for_all_within_allocated_mem_Ifopt_r n m A (mres : option A) f :
  (Ifopt mres as p
   Then P.for_all (within_allocated_mem n) (f p)
   Else P.for_all (within_allocated_mem n) m) = true ->
  P.for_all (within_allocated_mem n) (Ifopt mres as p
                                      Then f p
                                      Else m).
Proof. destruct mres; simpl; intros; assumption. Qed.

Hint Resolve for_all_within_allocated_mem_Ifopt_r.

Lemma for_all_within_allocated_mem_Ifdec_r n m `{Decidable mres} f :
  (Ifdec mres
   Then P.for_all (within_allocated_mem n) f
   Else P.for_all (within_allocated_mem n) m) = true ->
  P.for_all (within_allocated_mem n) (Ifdec mres
                                      Then f
                                      Else m).
Proof. decisions; intros; assumption. Qed.

Hint Resolve for_all_within_allocated_mem_Ifdec_r.

(*
Lemma for_all_within_allocated_mem_realloc r_n d d0 :
  P.for_all (within_allocated_mem (fst r_n)) (snd r_n) = true ->
  P.for_all
    (within_allocated_mem
       (Ifopt M.find d (snd r_n) as cblk
        Then If ` d0 <=? memCSize cblk Then fst r_n Else fst r_n + ` d0
        Else fst r_n + ` d0)) (snd (fst (FMap_realloc r_n d d0))).
Proof.
  unfold FMap_realloc; intros.
  rename d into addr.
  destruct d0, (M.find _ (snd r_n)) eqn:Heqe; simpl;
  [ destruct (_ <=? memCSize _) eqn:Heqe1; simpl | ];
  rename x into len;
  normalize; try apply_for_all.
  - rewrite <- remove_add.
    apply for_all_add_true; auto.
      simplify_maps.
    split; trivial.
      apply for_all_remove; auto.
    unfold within_allocated_mem in H0.
    nomega.
  - apply for_all_add_true; auto.
      unfold not; destruct 1.
      simplify_maps.
      apply_for_all.
      apply H0 in H6; destruct H6, H6.
      pose proof (allocations_have_size Hr_o _ _ H6).
      rewrite (proj1 H8) in H9.
      unfold within_allocated_mem in H7.
      nomega.
    split; trivial.
      apply for_all_remove; auto.
      eapply for_all_impl; eauto; nomega.
    nomega.
  + rewrite <- remove_add.
    apply for_all_add_true; auto.
      simplify_maps.
    split; trivial.
      apply for_all_remove; auto.
      eapply for_all_impl; eauto; nomega.
    nomega.
Qed.
*)

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

Lemma for_all_within_allocated_mem_mapi : forall n m f,
  P.for_all (within_allocated_mem n) m = true ->
  (forall k blk, memCSize (f k blk) <=? memCSize blk) ->
  P.for_all (within_allocated_mem n) (M.mapi f m) = true.
Proof.
  intros.
  apply P.for_all_iff; auto; intros.
  do 2 simplify_maps; intros; subst; auto.
  specialize (H0 k cblk).
  apply_for_all.
  unfold within_allocated_mem in H2.
  nomega.
Qed.

Hint Resolve for_all_within_allocated_mem_mapi.

Corollary Proper_within : forall pos,
   Proper (eq ==> eq ==> eq)
          (fun b e => within_bool b (memCSize e) pos).
Proof. intros; relational; subst; reflexivity. Qed.

Definition withinMemBlock (pos : N) (b : N) (e : MemoryBlock) : Prop :=
  within b (memSize e) pos.
Arguments withinMemBlock pos b e /.

Definition withinMemBlockC (pos : N) (b : N) (e : MemoryBlockC) : bool :=
  within_bool b (memCSize e) pos.
Arguments withinMemBlockC pos b e /.

Global Program Instance withinMemBlock_Proper :
  Proper (N.eq ==> eq ==> eq ==> eq) withinMemBlock.
Obligation 1.
  relational; subst.
  rewrite H; reflexivity.
Qed.

Hint Extern 4 (Proper (eq ==> eq ==> eq) (withinMemBlock _)) =>
  apply withinMemBlock_Proper; reflexivity.

Global Program Instance withinMemBlockC_Proper :
  Proper (N.eq ==> eq ==> eq ==> eq) withinMemBlockC.
Obligation 1.
  relational; subst.
  rewrite H; reflexivity.
Qed.

Hint Extern 4 (Proper (eq ==> eq ==> eq) (withinMemBlockC _)) =>
  apply withinMemBlockC_Proper; reflexivity.

Open Scope lsignature_scope.

Global Program Instance withinMemBlock_AbsR :
  withinMemBlock [R eq ==> eq ==> MemoryBlock_AbsR ==> boolR]
  withinMemBlockC.
Obligation 1. relational; subst; simpl; split; swap_sizes; nomega. Qed.

Global Program Instance withinMemBlock_AbsR_applied (pos : N) :
  withinMemBlock pos [R eq ==> MemoryBlock_AbsR ==> boolR]
  withinMemBlockC pos.
Obligation 1. apply withinMemBlock_AbsR; reflexivity. Qed.

Notation "f \oo g" := (fun x y => f (g x y)) (at level 90).

Lemma withinMemAbsR : forall base blk cblk pos,
  withinMemBlock pos base blk
    -> MemoryBlock_AbsR blk cblk
    -> withinMemBlockC pos base cblk = true.
Proof. simpl; intros; swap_sizes; nomega. Qed.

Hint Resolve within_allocated_mem_Proper.
Hint Resolve withinMemBlock_Proper.
Hint Resolve withinMemBlockC_Proper.

End Within.
