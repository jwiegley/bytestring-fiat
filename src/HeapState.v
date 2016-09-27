Require Import
  ByteString.Lib.Tactics
  ByteString.Lib.Nomega
  ByteString.Lib.FMapExt
  ByteString.Lib.Fiat
  ByteString.Memory
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Module HeapState (M : WSfun N_as_DT).

Module Import FMapExt := FMapExt N_as_DT M.
Module P := FMapExt.P.
Module F := P.F.

Open Scope N_scope.

Record HeapState := {
  resvs : M.t Size;
  bytes : M.t Word
}.

Definition HeapState_Equal (x y : HeapState) : Prop :=
  M.Equal (resvs x) (resvs y) /\ M.Equal (bytes x) (bytes y).

Global Program Instance Build_HeapState_Proper :
  Proper (M.Equal ==> M.Equal ==> HeapState_Equal) Build_HeapState.
Obligation 1. relational; unfold HeapState_Equal; simpl; intuition. Qed.

Ltac tsubst :=
  repeat
    match goal with
    | [ H : (_, _) = (_, _) |- _ ] => inv H
    | [ H : (_, _, _) = (_, _, _) |- _ ] => inv H
    | [ H : (_, _, _, _) = (_, _, _, _) |- _ ] => inv H
    | [ H : {| resvs := _
             ; bytes := _ |} =
            {| resvs := _
             ; bytes := _ |} |- _ ] => inv H
    end;
  subst.

Definition newHeapState :=
  {| resvs := M.empty _
   ; bytes := M.empty _ |}.

Definition within (addr : N) (len : N) (a : N) : Prop :=
  addr <= a < addr + len.
Hint Unfold within.

Definition within_bool (addr : N) (len : N) (a : N) : bool :=
  ((addr <=? a) && (a <? addr + len))%bool.
Hint Unfold within_bool.

Definition fits (addr1 len1 addr2 len2 : N) : Prop :=
  within addr1 len1 addr2 /\ addr2 + len2 <= addr1 + len1.
Hint Unfold fits.

Definition fits_bool (addr1 len1 addr2 len2 : N) : bool :=
  (within_bool addr1 len1 addr2 && (addr2 + len2 <=? addr1 + len1))%bool.
Hint Unfold fits_bool.

Definition overlaps (addr len addr2 len2 : N) : Prop :=
  addr < addr2 + len2 /\ addr2 < addr + len.
Hint Unfold overlaps.

Definition overlaps_bool (addr len addr2 len2 : N) : bool :=
  ((addr <? addr2 + len2) && (addr2 <? addr + len))%bool.
Hint Unfold overlaps_bool.

Lemma not_overlaps_sym : forall addr1 len1 addr2 len2,
  ~ overlaps addr1 len1 addr2 len2 <-> ~ overlaps addr2 len2 addr1 len1.
Proof. autounfold; nomega. Qed.

Corollary not_overlaps_trans : forall a b x y z,
  z < y -> ~ overlaps a b x y -> ~ overlaps a b x z.
Proof.
  unfold not; intros.
  autounfold in *.
  apply H0; nomega.
Qed.

Definition find_free_block (len : Size) (r : M.t Ptr) : Comp (option Ptr) :=
  { addr : option N
  | forall addr', addr = Some addr'
      -> P.for_all (fun a sz => negb (overlaps_bool a sz addr' len)) r }.

Definition keep_range {elt} (addr : M.key) (len : N) : M.t elt -> M.t elt :=
  keep_keys (within_bool addr len).

Definition drop_range {elt} (addr : M.key) (len : N) : M.t elt -> M.t elt :=
  keep_keys (fun p => negb (within_bool addr len p)).

Definition copy_bytes {elt} (from to : M.key) (len : N) (m : M.t elt) :
  M.t elt :=
  P.update (drop_range to len m)
           (M.fold (fun k e rest =>
                      If within_bool from len k
                      Then M.add (k - from + to) e rest
                      Else rest)
                   m (M.empty _)).

Program Instance copy_bytes_Proper :
  Proper (eq ==> eq ==> eq ==> M.Equal ==> @M.Equal elt) copy_bytes.
Obligation 1.
  relational.
  unfold copy_bytes, drop_range, keep_range, keep_keys.
  apply P.update_m; trivial.
    rewrite H2; reflexivity.
  apply P.fold_Equal; eauto; relational.
  - destruct (within_bool y y1 y3); simpl;
    rewrite H1; reflexivity.
  - intros ??????.
    destruct (within_bool y y1 k) eqn:Heqe; simpl;
    destruct (within_bool y y1 k') eqn:Heqe1; simpl;
    try reflexivity.
    rewrite add_associative.
      reflexivity.
    intros.
    apply N.add_cancel_r in H0.
    nomega.
Qed.

Lemma copy_bytes_mapsto : forall elt k (e : elt) addr1 addr2 len m,
  M.MapsTo k e (copy_bytes addr1 addr2 len m)
    <-> (If within_bool addr2 len k
         Then M.MapsTo ((k - addr2) + addr1) e m
         Else M.MapsTo (elt:=elt) k e m).
Proof.
  unfold copy_bytes, drop_range, keep_range, keep_keys,
         const, not, compose.
  split; intros.
    apply P.update_mapsto_iff in H.
    destruct H.
      revert H.
      apply P.fold_rec_bis; simpl; intros; intuition.
        destruct (within_bool addr2 len k) eqn:Heqe; simpl in *;
        rewrite <- H; assumption.
      destruct (within_bool addr2 len k) eqn:Heqe; simpl in *.
        destruct (within_bool addr1 len k0) eqn:Heqe1; simpl in *.
          simplify_maps.
            simplify_maps.
            nomega.
          simplify_maps; right; split; [nomega|intuition].
        simplify_maps; right; split; [nomega|intuition].
      destruct (within_bool addr1 len k0) eqn:Heqe1; simpl in *.
        simplify_maps.
          simplify_maps.
          nomega.
        simplify_maps.
        right.
        split.
          specialize (H1 H6).
          unfold not; intros; subst.
          contradiction H0.
          apply in_mapsto_iff.
          exists e.
          assumption.
        intuition.
      simplify_maps.
      right.
      split.
        specialize (H1 H2).
        unfold not; intros; subst.
        contradiction H0.
        apply in_mapsto_iff.
        exists e.
        assumption.
      intuition.
    destruct H.
    destruct (within_bool addr2 len k) eqn:Heqe; simpl in *.
      simplify_maps; relational.
      nomega.
    simplify_maps; relational.
  apply P.update_mapsto_iff.
  destruct (within_bool addr2 len k) eqn:Heqe; simpl in *.
    left.
    revert H.
    apply P.fold_rec_bis; simpl; intros; intuition.
      rewrite <- H in H1.
      intuition.
    destruct (within_bool addr1 len k0) eqn:Heqel; simpl.
      simplify_maps.
        simplify_maps.
        nomega.
      simplify_maps.
      right.
      split.
        nomega.
      intuition.
    simplify_maps.
    nomega.
  right.
  split.
    simplify_maps; relational.
    split; trivial.
    nomega.
  apply P.fold_rec_bis; simpl; intros; intuition.
    inversion H0.
    simplify_maps.
  destruct (within_bool addr1 len k0) eqn:Heqel; simpl in *.
    apply (proj1 (in_mapsto_iff _ _ _)) in H3.
    destruct H3.
    simplify_maps.
      nomega.
    contradiction H2.
    apply in_mapsto_iff.
    exists x.
    assumption.
  contradiction.
Qed.

Lemma copy_bytes_idem d len elt (m : M.t elt) :
  M.Equal (copy_bytes d d len m) m.
Proof.
  apply F.Equal_mapsto_iff; split; intros;
  [ apply copy_bytes_mapsto in H
  | apply copy_bytes_mapsto ];
  destruct (within_bool d len k) eqn:Heqe; simpl in *; trivial;
  revert H; replace (k - d + d) with k by nomega; trivial.
Qed.

End HeapState.