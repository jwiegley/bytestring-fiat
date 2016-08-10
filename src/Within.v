Require Import
  Here.Nomega
  Here.Heap
  Here.HeapADT
  Here.FMapExt
  Here.Relations
  Here.MemoryBlockC
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Module Within (Mem : Memory) (M : WSfun N_as_DT).

Module Import Block := MemoryBlockC Mem M.
Import Adt.
Import Adt.Heap.

Module X := FMapExt N_as_DT M.
Include X.

Definition within_allocated_mem (n : N) :=
  fun (addr : M.key) (blk : MemoryBlockC) => addr + memCSize blk <=? n.

Program Instance within_allocated_mem_Proper :
  Proper (eq ==> eq ==> eq ==> eq) within_allocated_mem.
Obligation 1. relational; subst; reflexivity. Qed.

Lemma within_allocated_mem_add : forall n x k e,
  within_allocated_mem n k e = true
    -> 0 < x
    -> within_allocated_mem (n + x) k e = true.
Proof.
  unfold within_allocated_mem; intros.
  undecide.
  apply Nle_add_plus; trivial.
Qed.

Lemma within_allocated_mem_at_end : forall n x d,
   within_allocated_mem (n + x) n {| memCSize := x; memCData := d |} = true.
Proof.
  unfold within_allocated_mem; simpl; intros.
  apply N.leb_refl.
Qed.

Corollary Proper_within : forall pos,
   Proper (eq ==> eq ==> eq)
          (fun b e => Decidable_witness (P:=within b (memCSize e) pos)).
Proof. intros; relational; subst; reflexivity. Qed.

Definition withinMemBlock (pos : N) (b : N) (e : MemoryBlock) : Prop :=
  within b (memSize e) pos.

Definition withinMemBlockC (pos : N) (b : N) (e : MemoryBlockC) : bool :=
  Decidable_witness (P:=within b (memCSize e) pos).

Global Program Instance withinMemBlock_Proper :
  Proper (N.eq ==> eq ==> eq ==> eq) withinMemBlock.
Obligation 1.
  relational.
  subst.
  rewrite H.
  reflexivity.
Qed.

Global Program Instance withinMemBlockC_Proper :
  Proper (N.eq ==> eq ==> eq ==> eq) withinMemBlockC.
Obligation 1.
  relational.
  subst.
  rewrite H.
  reflexivity.
Qed.

Open Scope lsignature_scope.

Global Program Instance withinMemBlock_AbsR :
  withinMemBlock [R eq ==> eq ==> MemoryBlock_AbsR ==> boolR]
  withinMemBlockC.
Obligation 1.
  relational; subst;
  unfold withinMemBlock, withinMemBlockC;
  split; intros.
    apply within_reflect in H.
    rewrite <- (proj1 H1).
    assumption.
  simpl in H.
  apply within_reflect.
  rewrite (proj1 H1).
  assumption.
Qed.

Global Program Instance withinMemBlock_AbsR_applied (pos : N) :
  withinMemBlock pos [R eq ==> MemoryBlock_AbsR ==> boolR]
  withinMemBlockC pos.
Obligation 1. apply withinMemBlock_AbsR; reflexivity. Qed.

Notation "f \oo g" := (fun x y => f (g x y)) (at level 90).

Lemma withinMemAbsR : forall base blk cblk pos,
  withinMemBlock pos base blk
    -> MemoryBlock_AbsR blk cblk
    -> withinMemBlockC pos base cblk = true.
Proof.
  intros.
  unfold withinMemBlock, withinMemBlockC in *; simpl in *.
  apply within_reflect in H.
  destruct H0 as [H0 _]; rewrite <- H0.
  assumption.
Qed.

Hint Resolve within_allocated_mem_Proper.
Hint Resolve withinMemBlock_Proper.
Hint Resolve withinMemBlockC_Proper.

End Within.
