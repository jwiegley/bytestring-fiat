Require Import
  ByteString.Lib.Tactics
  ByteString.Lib.Nomega
  ByteString.Lib.FMapExt
  ByteString.Lib.Fiat
  ByteString.Memory
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Module HeapState (M : WSfun Ptr_as_DT).

Module Import FMapExt := FMapExt Ptr_as_DT M.
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

Definition within `(addr : Ptr A) (len : N) (a : Ptr A) : Prop :=
  addr <= a < plusPtr addr len.
Hint Unfold within.

Definition within_bool `(addr : Ptr A) (len : N) (a : Ptr A) : bool :=
  ((addr <=? a) && (a <? plusPtr addr len))%bool.
Hint Unfold within_bool.

Corollary within_zero : forall A (n m : Ptr A),
  within_bool n 0 m = false.
Proof. intros; destruct (Nlt_dec m n); nomega. Qed.

Definition fits `(addr1 : Ptr A) (len1 : N) (addr2 : Ptr A) (len2 : N) : Prop :=
  within addr1 len1 addr2 /\ plusPtr addr2 len2 <= plusPtr addr1 len1.
Hint Unfold fits.

Definition fits_bool `(addr1 : Ptr A) (len1 : N) (addr2 : Ptr A) (len2 : N) : bool :=
  (within_bool addr1 len1 addr2 &&
   (plusPtr addr2 len2 <=? plusPtr addr1 len1))%bool.
Hint Unfold fits_bool.

Definition overlaps `(addr : Ptr A) (len : N) (addr2 : Ptr A) (len2 : N) : Prop :=
  addr < plusPtr addr2 len2 /\ addr2 < plusPtr addr len.
Hint Unfold overlaps.

Definition overlaps_bool `(addr : Ptr A) (len : N) (addr2 : Ptr A) (len2 : N) : bool :=
  ((addr <? plusPtr addr2 len2) && (addr2 <? plusPtr addr len))%bool.
Hint Unfold overlaps_bool.

Lemma not_overlaps_sym : forall A (addr1 addr2 : Ptr A) len1 len2,
  ~ overlaps addr1 len1 addr2 len2 <-> ~ overlaps addr2 len2 addr1 len1.
Proof. autounfold; nomega. Qed.

Corollary not_overlaps_trans : forall A (a x : Ptr A) b y z,
  z < y -> ~ overlaps a b x y -> ~ overlaps a b x z.
Proof.
  unfold not; intros.
  autounfold in *.
  apply H0; nomega.
Qed.

Definition find_free_block (len : Size) `(r : M.t (Ptr A)) : Comp (Ptr A) :=
  { addr : Ptr A | P.for_all (fun a sz => negb (overlaps_bool a sz addr len)) r }.

Definition keep_range {elt} `(addr : Ptr A) (len : N) : M.t elt -> M.t elt :=
  keep_keys (within_bool addr len).

Definition drop_range {elt} `(addr : Ptr A) (len : N) : M.t elt -> M.t elt :=
  keep_keys (fun p => negb (within_bool addr len p)).

Definition copy_bytes {elt A} (from to : Ptr A) (len : N)
           (mfrom mto : M.t elt) : M.t elt :=
  P.update (drop_range to len mto)
           (M.fold (fun k e rest =>
                      If within_bool from len k
                      Then M.add (plusPtr to (k - from)) e rest
                      Else rest)
                   mfrom (M.empty _)).

Program Instance copy_bytes_Proper : forall A,
  Proper (eq ==> eq ==> eq ==> M.Equal ==> M.Equal ==> @M.Equal elt)
         (copy_bytes (A:=A)).
Obligation 1.
  relational.
  unfold copy_bytes, drop_range, keep_range, keep_keys.
  apply P.update_m; trivial.
    rewrite H3; reflexivity.
  apply P.fold_Equal; eauto; relational.
  - destruct (within_bool y y1 y4); simpl;
    rewrite H1; reflexivity.
  - intros ??????.
    destruct (within_bool y y1 k) eqn:Heqe; simpl;
    destruct (within_bool y y1 k') eqn:Heqe1; simpl;
    try reflexivity.
    rewrite add_associative.
      reflexivity.
    intros.
    unfold plusPtr in H0.
    nomega.
Qed.

Lemma copy_bytes_mapsto :
  forall elt k (e : elt) A (addr1 addr2 : Ptr A) len m1 m2,
    M.MapsTo k e (copy_bytes addr1 addr2 len m1 m2)
      <-> If within_bool addr2 len k
          Then M.MapsTo (plusPtr addr1 (k - addr2)) e m1
          Else M.MapsTo (elt:=elt) k e m2.
Proof.
  unfold copy_bytes, drop_range, keep_range, keep_keys,
         const, not, compose.
  split; intros.
    apply P.update_mapsto_iff in H.
    destruct H.
      revert H.
      apply P.fold_rec_bis; simpl; intros; intuition.
        destruct (within_bool addr2 len k) eqn:Heqe; simpl in *; trivial.
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
        nomega.
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

Lemma copy_bytes_find :
  forall A (a1 a2 : Ptr A) k l elt (m1 m2 : M.t elt),
    M.find k (copy_bytes a1 a2 l m1 m2)
      = If within_bool a2 l k
        Then M.find (plusPtr a1 (k - a2)) m1
        Else M.find k m2.
Proof.
  intros.
  unfold copy_bytes, drop_range, keep_keys.
  destruct (within_bool a2 l k) eqn:Heqe; simpl.
  {
    rewrite update_find_r.
    apply P.fold_rec_weak; intros.
    - rewrite <- H; assumption.
    - rewrite !F.empty_o; trivial.
    - destruct (within_bool a1 l k0) eqn:Heqe2; simpl.
        destruct (N.eq_dec (plusPtr a2 (k0 - a1)) k); subst.
          replace (plusPtr a1 (plusPtr a2 (k0 - a1) - a2)) with k0 by nomega.
          rewrite !F.add_eq_o; trivial.
        assert (k0 <> plusPtr a1 (k - a2)) by nomega.
        rewrite !F.add_neq_o; trivial.
      assert (k0 <> plusPtr a1 (k - a2)) by nomega.
      rewrite F.add_neq_o; trivial.
    - unfold not; intros.
      destruct (proj1 (in_mapsto_iff _ _ _) H); clear H.
      simplify_maps; relational.
      nomega.
  }
  {
    rewrite update_find_l.
      unfold P.filter.
      apply P.fold_rec_weak; intros; trivial.
        rewrite <- H; assumption.
      destruct (N.eq_dec k0 k); subst.
        rewrite Heqe; simpl.
        rewrite !F.add_eq_o; trivial.
      destruct (negb (within_bool a2 l k0));
      rewrite !F.add_neq_o; trivial.
    apply P.fold_rec_weak; intros; trivial;
    unfold not; intros.
      apply F.empty_in_iff in H; trivial.
    destruct (within_bool a1 l k0) eqn:Heqe1; simpl in H1.
      destruct H1.
      simplify_maps.
        nomega.
      contradiction H0.
      exists x.
      assumption.
    nomega.
  }
Qed.

Lemma copy_bytes_zero {elt A} (addr1 addr2 : Ptr A) (m1 m2 : M.t elt) :
  M.Equal (elt:=elt) (copy_bytes addr1 addr2 0 m1 m2) m2.
Proof.
  apply F.Equal_mapsto_iff; split; intros;
  [ apply copy_bytes_mapsto in H
  | apply copy_bytes_mapsto ];
  destruct (within_bool addr2 0 k) eqn:Heqe; simpl in *; trivial;
  nomega.
Qed.

Lemma copy_bytes_idem {A} (d : Ptr A) len elt (m : M.t elt) :
  M.Equal (copy_bytes d d len m m) m.
Proof.
  apply F.Equal_mapsto_iff; split; intros;
  [ apply copy_bytes_mapsto in H
  | apply copy_bytes_mapsto ];
  destruct (within_bool d len k) eqn:Heqe; simpl in *; trivial;
  revert H; replace (plusPtr d (k - d)) with k by nomega; trivial.
Qed.

Lemma copy_bytes_find_at : forall A (b k : Ptr A) l elt (m1 m2 : M.t elt),
  0 < l -> M.find k (copy_bytes b k l m1 m2) = M.find b m1.
Proof.
  intros.
  rewrite copy_bytes_find.
  assert (within_bool k l k = true) by nomega.
  rewrite H0; simpl.
  replace (plusPtr b (k - k)) with b by nomega.
  reflexivity.
Qed.

Lemma increase_heap_ceiling : forall A (n : Ptr A) m r,
  P.for_all (fun (addr : Ptr A) sz => plusPtr addr sz <=? n) r ->
  P.for_all (fun (addr : Ptr A) sz => plusPtr addr sz <=? plusPtr n m) r.
Proof.
  intros.
  eapply for_all_impl; auto;
  relational; eauto; nomega.
Qed.

Lemma Equal_If_Opt_Then_Else_Proper:
  forall (A B : Type) (c : option A),
    Proper (pointwise_relation A M.Equal ==> @M.Equal B ==> M.Equal)
           (If_Opt_Then_Else c).
Proof.
  intros.
  relational.
  destruct c; eauto.
Qed.

End HeapState.
