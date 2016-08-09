Require Import
  Here.Nomega
  Here.TupleEnsembles
  Here.FunMaps
  Here.Relations
  Here.Heap
  Coq.FSets.FMapAVL
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx
  Coq.Structures.OrderedTypeEx.

Module MemoryBlockC (Mem : Memory).

Module Import H := Heap Mem.
Module Import M := FMapAVL.Make(N_as_OT).
Module Import U := FunMaps N_as_DT M.

Module P := WProperties_fun N_as_DT M.
Module F := P.F.

Definition MemoryBlock_Same (x y : MemoryBlock) : Prop :=
  memSize x = memSize y /\ Same (memData x) (memData y).

Global Program Instance MemoryBlock_Proper :
  Proper (eq ==> @Same _ _ ==> MemoryBlock_Same) Build_MemoryBlock.
Obligation 1. relational; split; simpl; subst; auto. Qed.

Record MemoryBlockC := {
  memCSize : N;
  memCData : M.t Mem.Word8
}.

Definition MemoryBlockC_Equal (x y : MemoryBlockC) : Prop :=
  memCSize x = memCSize y /\ M.Equal (memCData x) (memCData y).

Global Program Instance MemoryBlockC_Proper :
  Proper (eq ==> @M.Equal _ ==> MemoryBlockC_Equal) Build_MemoryBlockC.
Obligation 1. relational; split; simpl; subst; auto. Qed.

Definition MemoryBlock_AbsR (o : MemoryBlock) (n : MemoryBlockC) : Prop :=
  memSize o = memCSize n /\ Map_AbsR eq (memData o) (memCData n).

Open Scope lsignature_scope.

Global Program Instance MemoryBlock_AbsR_AbsR :
  Build_MemoryBlock [R eq ==> Map_AbsR eq ==> MemoryBlock_AbsR]
  Build_MemoryBlockC.
Obligation 1. relational; split; simpl; subst; auto. Qed.

Global Program Instance MemoryBlock_AbsR_Proper :
  Proper (MemoryBlock_Same ==> MemoryBlockC_Equal ==> iff) MemoryBlock_AbsR.
Obligation 1.
  relational; destruct H, H0, H1.
  - split; intros.
      congruence.
    split; intros; subst;
    split; intros.
    + rewrite <- H2 in H5.
      apply H4 in H5; trivial.
      setoid_rewrite H3 in H5.
      trivial.
    + rewrite <- H2.
      apply H4; trivial.
      setoid_rewrite H3.
      trivial.
    + rewrite <- H3 in H5.
      apply H4 in H5; trivial.
      setoid_rewrite H2 in H5.
      trivial.
    + rewrite <- H3.
      apply H4; trivial.
      setoid_rewrite <- H2 in H5.
      trivial.
  - split; intros.
      congruence.
    split; intros; subst;
    split; intros.
    + rewrite H2 in H5.
      apply H4 in H5; trivial.
      setoid_rewrite <- H3 in H5.
      trivial.
    + rewrite H2.
      apply H4; trivial.
      setoid_rewrite <- H3.
      trivial.
    + rewrite H3 in H5.
      apply H4 in H5; trivial.
      setoid_rewrite <- H2 in H5.
      trivial.
    + rewrite H3.
      apply H4; trivial.
      setoid_rewrite H2 in H5.
      trivial.
Qed.

Corollary MemoryBlock_AbsR_impl : forall s s' d d',
    s = s' -> Map_AbsR eq d d' ->
    MemoryBlock_AbsR {| memSize  := s;  memData  := d |}
                     {| memCSize := s'; memCData := d' |}.
Proof. intros; subst; split; intros; trivial. Qed.

Corollary Empty_MemoryBlock_AbsR : forall n,
  MemoryBlock_AbsR {| memSize  := n; memData  := TupleEnsembles.Empty |}
                   {| memCSize := n; memCData := M.empty Mem.Word8 |}.
Proof.
  split; trivial; simpl; intros; apply Empty_Map_AbsR. Qed.

(* [M.Equal] maps are not necessary identical -- for example, there is no
   ordering requirement -- but for the purposes of proof, they are at least
   extensionally equal. *)
Axiom Extensionality_FMap : forall (elt : Type) (A B : M.t elt),
  M.Equal (elt:=elt) A B -> A = B.

Lemma MemoryBlock_AbsR_FunctionalRelation :
  FunctionalRelation MemoryBlock_AbsR.
Proof.
  intros ?????.
  destruct H, H0, x, y, z; simpl in *.
  subst; f_equal.
  apply Extensionality_FMap.
  apply F.Equal_mapsto_iff; split; intros.
    apply H2, H1; trivial.
  apply H1, H2; trivial.
Qed.

Lemma MemoryBlock_AbsR_InjectiveRelation :
  InjectiveRelation MemoryBlock_AbsR.
Proof.
  intros ?????.
  destruct H, H0, x, y, z; simpl in *.
  subst; f_equal.
  apply Extensionality_Ensembles.
  split; intros;
  intros ??; destruct x.
    apply H2, H1; trivial.
  apply H1, H2; trivial.
Qed.

Lemma eq_FunctionalRelation : forall A, FunctionalRelation (A:=A) (B:=A) eq.
Proof. intros ??????; subst; reflexivity. Qed.

Lemma eq_InjectiveRelation : forall A,
  InjectiveRelation (A:=A) (B:=A) eq.
Proof. intros ??????; subst; reflexivity. Qed.

Hint Resolve MemoryBlock_AbsR_FunctionalRelation.
Hint Resolve MemoryBlock_AbsR_InjectiveRelation.
Hint Resolve eq_FunctionalRelation.
Hint Resolve eq_InjectiveRelation.

End MemoryBlockC.
