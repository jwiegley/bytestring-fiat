Require Import
  ByteString.Nomega
  ByteString.TupleEnsembles
  ByteString.FunMaps
  ByteString.Relations
  ByteString.HeapEns
  ByteString.HeapEnsADT
  ByteString.FMapExt
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Module MemoryBlockC (M : WSfun N_as_DT).

Module Import FunMaps := FunMaps N_as_DT M.
Import FunMaps.FMapExt.
Module P := FunMaps.FMapExt.P.
Module F := P.F.

Record MemoryBlockC := {
  memCSize : N;
  memCData : M.t Word8
}.

Definition MemoryBlockC_Equal (x y : MemoryBlockC) : Prop :=
  memCSize x = memCSize y /\ M.Equal (memCData x) (memCData y).

Definition to_MemoryBlock (x : MemoryBlockC) : MemoryBlock :=
  {| memSize := memCSize x
   ; memData := of_map eq (memCData x) |}.

Global Program Instance MemoryBlockC_Proper :
  Proper (eq ==> @M.Equal _ ==> MemoryBlockC_Equal) Build_MemoryBlockC.
Obligation 1. relational; split; simpl; subst; auto. Qed.

Definition MemoryBlock_AbsR (o : MemoryBlock) (n : MemoryBlockC) : Prop :=
  memSize o = memCSize n /\ Map_AbsR eq (memData o) (memCData n).

Lemma to_MemoryBlock_Same : forall o n,
  MemoryBlock_AbsR o n -> MemoryBlock_Same o (to_MemoryBlock n).
Proof.
  unfold to_MemoryBlock.
  split; intros.
    rewrite (proj1 H); reflexivity.
  simpl.
  destruct H.
  apply of_map_Same; assumption.
Qed.

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
                   {| memCSize := n; memCData := M.empty Word8 |}.
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
  apply Extensionality_FMap.    (* can we be free of this? *)
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

Require Import
  Fiat.ADT
  Fiat.ADTNotation
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements
  ByteString.ADTInduction.

Lemma MemoryBlock_AbsR_TotalMapRelation :
  forall r : Rep HeapSpec, fromADT _ r
    -> TotalMapRelation MemoryBlock_AbsR r.
Proof.
  intros; intros ???.
  pose proof (all_blocks_are_finite H _ _ H0).
  pose proof (all_block_maps_are_functional H _ _ H0).
  simpl in *.
  elimtype ((exists size : N, memSize x = size) /\
            (exists data : M.t Word8, Map_AbsR eq (memData x) data)).
    do 2 destruct 1.
    eexists {| memCSize := x0; memCData := x1 |}.
    constructor; auto.
  split; eauto.
  apply every_finite_map_has_an_associated_fmap; auto.
  intros ???.
  exists x0.
  reflexivity.
Qed.

Hint Resolve MemoryBlock_AbsR_TotalMapRelation.

Lemma MemoryBlock_AbsR_TotalMapRelation_r :
  forall m : M.t MemoryBlockC,
    TotalMapRelation_r MemoryBlock_AbsR m.
Proof.
  intros; intros ???.
  exists {| memSize := memCSize y
          ; memData := of_map eq (memCData y) |}.
  destruct y; simpl.
  apply MemoryBlock_AbsR_impl; trivial.
  apply of_map_Map_AbsR; auto.
  intros ???.
  exists y.
  reflexivity.
Qed.

Hint Resolve MemoryBlock_AbsR_TotalMapRelation_r.

Lemma TotalMapRelation_r_eq : forall elt (m : M.t elt), TotalMapRelation_r eq m.
Proof. intros ?????; exists y; reflexivity. Qed.

Hint Resolve TotalMapRelation_r_eq.

Lemma of_map_MemoryBlock_AbsR : forall x,
  MemoryBlock_AbsR {| memSize := memCSize x
                    ; memData := of_map eq (memCData x) |} x.
Proof. split; intros; auto; apply of_map_Map_AbsR; auto. Qed.

Hint Resolve of_map_MemoryBlock_AbsR.

Corollary to_MemoryBlock_AbsR : forall m, MemoryBlock_AbsR (to_MemoryBlock m) m.
Proof. apply of_map_MemoryBlock_AbsR. Qed.

Hint Resolve to_MemoryBlock_AbsR.

Lemma Lookup_of_map : forall addr cblk r_o r_n,
  Map_AbsR MemoryBlock_AbsR r_o r_n
    -> M.MapsTo addr cblk r_n
    -> Lookup addr {| memSize := memCSize cblk
                    ; memData := of_map eq (memCData cblk) |} r_o.
Proof.
  intros.
  apply H in H0.
  destruct H0, H0, H1.
  apply of_map_Same in H2.
  apply H.
  exists cblk.
  intuition.
  apply H.
  exists x.
  intuition.
  split; intros; trivial.
  rewrite H2.
  apply of_map_Map_AbsR; auto.
Qed.

Hint Resolve Lookup_of_map.

Ltac swap_sizes :=
  match goal with
  | [ H : MemoryBlock_AbsR ?blk ?cblk |- context [memSize ?blk] ] =>
    rewrite (proj1 H)
  | [ H : MemoryBlock_AbsR ?blk ?cblk |- context [memCSize ?cblk] ] =>
    rewrite <- (proj1 H)
  end.

Definition keep_keys (P : M.key -> bool) : M.t Word8 -> M.t Word8 :=
  P.filter (const ∘ P).

Definition shift_keys (orig_base : N) (new_base : N) (m : M.t Word8) :
  M.t Word8 :=
  M.fold (fun k => M.add (k - orig_base + new_base)) m (M.empty _).

Lemma KeepKeys_Map_AbsR :
  KeepKeys [R (N.eq ==> boolR) ==> Map_AbsR eq ==> Map_AbsR eq] keep_keys.
Proof.
  unfold KeepKeys, keep_keys, compose, const.
  constructor.
  intros ???.
  apply Filter_Map_AbsR; auto; relational.
  apply H; reflexivity.
Qed.

Lemma ShiftKeys_Map_AbsR : forall b d r m,
  r [R Map_AbsR eq] m ->
  All (fun k _ => b <= k) r ->
  (* P.for_all (fun k _ => b <=? k) m -> *)
  ShiftKeys b d r [R Map_AbsR eq] shift_keys b d m.
Proof.
  unfold ShiftKeys, shift_keys, compose, const; intros.
  eapply (All_Map_AbsR (A:=Word8) (B:=Word8) (R:=eq)
                       (f:=fun k _ => b <= k) (f':=fun k _ => b <=? k)) in H0.
    Focus 2. relational.
    Focus 2. relational. split; nomega.
    Focus 2. apply logical_prf.
  relational; split; intros; split; intros H1.
  - repeat teardown.
    inversion H1; subst; clear H1.
    apply H in H2;
    destruct H2 as [cblk [? ?]]; subst.
    pose proof H0.
    apply (proj1 (P.for_all_iff _ _)) with (k:=n) (e:=cblk) in H2; [|exact H1].
    exists cblk; intuition.
    revert H1.
    revert H0.
    apply P.fold_rec_bis; auto; intros.
      rewrite <- H0 in H3, H4; intuition.
    repeat simplify_maps.
    apply for_all_add_true in H4;
    destruct H4; auto; relational.
    right; intuition.
    apply N.add_cancel_r in H6.
    apply Nsub_eq in H6; auto; nomega.
  - reduction.
    revert H1.
    revert H0.
    apply P.fold_rec_bis; auto; intros.
      rewrite <- H0 in H2; intuition.
    apply for_all_add_true in H3;
    destruct H3; auto; relational.
    simplify_maps.
    exists (k, x); simpl.
    apply H in H0; destruct H0.
    intuition; subst; assumption.
  - revert H1.
    revert H0.
    apply P.fold_rec_bis; auto; intros.
      rewrite <- H0 in H2; intuition.
    apply for_all_add_true in H3;
    destruct H3; auto; relational.
    simplify_maps.
    exists cblk; simpl.
    intuition.
    pose proof (Lookup_Map_set (B:=Word8) (a:=k - b + d) (b:=cblk)
                               (fun p => (fst p - b + d, snd p))).
    apply H2.
    exists (k, cblk); simpl.
    apply H in H0; destruct H0.
    intuition; subst; assumption.
  - repeat teardown; subst.
    inversion H1; subst; clear H1.
    apply H in H3.
    destruct H3 as [blk [? ?]]; subst.
    revert H1.
    revert H0.
    apply P.fold_rec_bis; auto; intros.
      rewrite <- H0 in H2, H3; intuition.
    apply for_all_add_true in H3;
    destruct H3; auto; relational.
    repeat simplify_maps.
    right; intuition.
    apply (proj1 (P.for_all_iff _ _)) with (k0:=n) (e0:=blk) in H3; [|exact H9].
    apply N.add_cancel_r in H4.
    apply Nsub_eq in H4; auto; nomega.
Qed.

Definition copy_block sblk soff dblk doff len :=
  (* [s] is the source region to copy from *)
  let s := keep_keys (within_bool soff len) (memCData sblk) in
  (* [d] is where the region will be copied *)
  let d := keep_keys (negb ∘ within_bool doff len) (memCData dblk) in
  P.update d (shift_keys soff doff s).

Lemma CopyBlock_Map_AbsR :
  CopyBlock [R MemoryBlock_AbsR ==> eq ==>
               MemoryBlock_AbsR ==> eq ==> eq ==> Map_AbsR eq] copy_block.
Proof.
  relational.
  destruct H, H1.
  apply Union_Map_AbsR; auto.
  - apply KeepKeys_Map_AbsR; trivial.
    apply not_within_AbsR.
  - apply ShiftKeys_Map_AbsR.
      constructor; apply KeepKeys_Map_AbsR.
        apply within_AbsR; try reflexivity.
      assumption.
    unfold KeepKeys; intros ???.
    repeat teardown.
    nomega.
  - unfold not, compose, KeepKeys, ShiftKeys; intros ????.
    repeat teardown; inversion H4; subst; clear H4.
    apply not_within_reflect in H3; nomega.
Qed.

End MemoryBlockC.
