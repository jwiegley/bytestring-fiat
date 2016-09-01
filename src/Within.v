Require Import
  ByteString.Nomega
  ByteString.Heap
  ByteString.HeapADT
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

Corollary Proper_within : forall pos,
   Proper (eq ==> eq ==> eq)
          (fun b e => Decidable_witness (P:=within b (memCSize e) pos)).
Proof. intros; relational; subst; reflexivity. Qed.

Definition withinMemBlock (pos : N) (b : N) (e : MemoryBlock) : Prop :=
  within b (memSize e) pos.
Arguments withinMemBlock pos b e /.

Definition withinMemBlockC (pos : N) (b : N) (e : MemoryBlockC) : bool :=
  Decidable_witness (P:=within b (memCSize e) pos).
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
