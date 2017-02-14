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

Global Program Instance HeapState_Equal_Equivalence : Equivalence HeapState_Equal.
Obligation 1.
  constructor; reflexivity.
Defined.
Obligation 2.
  constructor; destruct H; symmetry; assumption.
Defined.
Obligation 3.
  constructor; destruct H, H0.
    transitivity (resvs y); assumption.
  transitivity (bytes y); assumption.
Defined.

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
  (addr <= a < plusPtr addr len)%Ptr.
Hint Unfold within.

Definition within_bool `(addr : Ptr A) (len : N) (a : Ptr A) : bool :=
  ((addr <=? a) && (a <? plusPtr addr len))%Ptr.
Hint Unfold within_bool.

Corollary within_zero : forall A (n m : Ptr A),
  within_bool n 0 m = false.
Proof. intros; destruct (Nlt_dec m n); nomega. Qed.

Definition fits `(addr1 : Ptr A) (len1 : N) (addr2 : Ptr A) (len2 : N) : Prop :=
  within addr1 len1 addr2
    /\ (lePtr (A:=A) (plusPtr addr2 len2) (plusPtr addr1 len1))%Ptr.
Hint Unfold fits.

Definition fits_bool `(addr1 : Ptr A) (len1 : N) (addr2 : Ptr A) (len2 : N) : bool :=
  (within_bool addr1 len1 addr2 &&
   (lebPtr (A:=A) (plusPtr addr2 len2) (plusPtr addr1 len1)))%Ptr.
Hint Unfold fits_bool.

Definition overlaps `(addr : Ptr A) (len : N) (addr2 : Ptr A) (len2 : N) : Prop :=
  (addr < plusPtr addr2 len2 /\ addr2 < plusPtr addr len)%Ptr.
Hint Unfold overlaps.

Definition overlaps_bool `(addr : Ptr A) (len : N) (addr2 : Ptr A) (len2 : N) : bool :=
  ((addr <? plusPtr addr2 len2) && (addr2 <? plusPtr addr len))%Ptr.
Hint Unfold overlaps_bool.

Lemma not_overlaps_sym : forall A (addr1 addr2 : Ptr A) len1 len2,
  ~ overlaps addr1 len1 addr2 len2 <-> ~ overlaps addr2 len2 addr1 len1.
Proof. nomega. Qed.

Corollary not_overlaps_trans : forall A (a x : Ptr A) b y z,
  z < y -> ~ overlaps a b x y -> ~ overlaps a b x z.
Proof.
  unfold not; intros.
  apply H0; nomega.
Qed.

Definition find_free_block (len : Size) `(r : M.t (Ptr A)) : Comp (Ptr A) :=
  { addr : Ptr A | P.for_all (fun a sz => negb (overlaps_bool a sz addr len)) r }.

Definition keep_range {elt} `(addr : Ptr A) (len : N) : M.t elt -> M.t elt :=
  keep_keys (within_bool addr len).

Definition drop_range {elt} `(addr : Ptr A) (len : N) : M.t elt -> M.t elt :=
  keep_keys (fun p => negb (within_bool addr len p)).

Definition copy_bytes {elt A} (from to : Ptr A) (len : N) (m : M.t elt) : M.t elt :=
  P.update (drop_range to len m)
           (M.fold (fun k e rest =>
                      If within_bool from len k
                      Then M.add (plusPtr to (minusPtr k from)) e rest
                      Else rest)
                   m (M.empty _)).

Program Instance copy_bytes_Proper : forall A,
  Proper (eq ==> eq ==> eq ==> M.Equal ==> @M.Equal elt)
         (copy_bytes (A:=A)).
Obligation 1.
  relational.
  unfold copy_bytes, drop_range, keep_range, keep_keys.
  apply P.update_m; trivial.
    rewrite H2; reflexivity.
  apply P.fold_Equal; eauto; relational.
  - destruct (within_bool y y1 y3) eqn:Heqe; simpl;
    destruct (within_bool y y1 x) eqn:Heqe1; simpl;
    rewrite H1; nomega.
  - intros ??????.
    destruct (within_bool y y1 k) eqn:Heqe; simpl;
    destruct (within_bool y y1 k') eqn:Heqe1; simpl;
    try reflexivity.
    rewrite add_associative.
      reflexivity.
    nomega.
Qed.

Lemma copy_bytes_mapsto :
  forall elt k (e : elt) A (addr1 addr2 : Ptr A) len m,
    M.MapsTo k e (copy_bytes addr1 addr2 len m)
      <-> If within_bool addr2 len k
          Then M.MapsTo (plusPtr addr1 (minusPtr k addr2)) e m
          Else M.MapsTo (elt:=elt) k e m.
Proof.
  unfold copy_bytes, drop_range, keep_range, keep_keys,
         const, not, compose.
  split; intros.
    apply P.update_mapsto_iff in H.
    destruct H.
      revert H.
      apply P.fold_rec_bis; simpl; intros; intuition.
        destruct (within_bool addr2 len k) eqn:Heqe; simpl in *; trivial;
        rewrite <- H; assumption.
      destruct (within_bool addr2 len k) eqn:Heqe; simpl in *.
        destruct (within_bool addr1 len k0) eqn:Heqe1; simpl in *.
          simplify_maps.
            simplify_maps.
            nomega.
          simplify_maps; right; split; [nomega|intuition].
        simplify_maps; right; split; [nomega|intuition].
      destruct (within_bool addr1 len k0) eqn:Heqe1; simpl in *.
        simplify_maps; simplify_maps.
          nomega.
        right; intuition.
        rewrite H1 in *.
        contradiction H0.
        exists e.
        assumption.
      simplify_maps.
      right; intuition.
      rewrite H1 in *.
      contradiction H0.
      exists e.
      assumption.
    destruct H.
    destruct (within_bool addr2 len k) eqn:Heqe; simpl in *;
    simplify_maps; relational; nomega.
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
    simplify_maps; relational; nomega.
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
  forall A (a1 a2 : Ptr A) k l elt (m : M.t elt),
    M.find k (copy_bytes a1 a2 l m)
      = If within_bool a2 l k
        Then M.find (plusPtr a1 (minusPtr k a2)) m
        Else M.find k m.
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
        destruct (N.eq_dec (plusPtr a2 (minusPtr k0 a1)) k); subst.
          replace (plusPtr a1 (minusPtr (plusPtr a2 (minusPtr k0 a1)) a2)) with k0 by nomega.
          rewrite !F.add_eq_o; auto.
        assert (k0 <> plusPtr a1 (minusPtr k a2)) by nomega.
        rewrite !F.add_neq_o; trivial.
      assert (k0 <> plusPtr a1 (k - a2)) by nomega.
      rewrite F.add_neq_o; trivial.
    - unfold not; intros.
      destruct (proj1 (in_mapsto_iff _ _ _) H); clear H.
      simplify_maps; relational; nomega.
  }
  {
    rewrite update_find_l.
      unfold P.filter.
      apply P.fold_rec_weak; intros; trivial.
        rewrite <- H; assumption.
      destruct (N.eq_dec k0 k); subst.
        rewrite Heqe; simpl.
        rewrite !F.add_eq_o; auto.
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

Lemma copy_bytes_zero {elt A} (addr1 addr2 : Ptr A) (m : M.t elt) :
  M.Equal (elt:=elt) (copy_bytes addr1 addr2 0 m) m.
Proof.
  apply F.Equal_mapsto_iff; split; intros;
  [ apply copy_bytes_mapsto in H
  | apply copy_bytes_mapsto ];
  destruct (within_bool addr2 0 k) eqn:Heqe; simpl in *; trivial;
  nomega.
Qed.

Lemma copy_bytes_idem {A} (d : Ptr A) len elt (m : M.t elt) :
  M.Equal (copy_bytes d d len m) m.
Proof.
  apply F.Equal_mapsto_iff; split; intros;
  [ apply copy_bytes_mapsto in H
  | apply copy_bytes_mapsto ];
  destruct (within_bool d len k) eqn:Heqe; simpl in *; trivial;
  revert H; replace (plusPtr d (minusPtr k d)) with k by nomega; trivial.
Qed.

Lemma copy_bytes_find_at : forall A (b k : Ptr A) l elt (m : M.t elt),
  0 < l -> M.find k (copy_bytes b k l m) = M.find b m.
Proof.
  intros.
  rewrite copy_bytes_find.
  assert (within_bool k l k = true) by nomega.
  rewrite H0; simpl.
  replace (plusPtr b (minusPtr k k)) with b by nomega.
  reflexivity.
Qed.

Lemma increase_heap_ceiling : forall A (n : Ptr A) m r,
  P.for_all (fun (addr : Ptr A) sz =>
               lebPtr (A:=A) (plusPtr addr sz) n) r ->
  P.for_all (fun (addr : Ptr A) sz =>
               lebPtr (A:=A) (plusPtr addr sz) (plusPtr n m)) r.
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

Definition load_into_map {elt} (k : M.key) (xs : list elt) (m : M.t elt) :=
  fst (fold_left (fun (acc : M.t elt * Ptr Word) x =>
                    let (m, i) := acc in
                    (M.add i x m, plusPtr (A:=Word) i 1)) xs (m, k)).

Corollary load_into_map_singleton : forall b elt a (m : M.t elt),
  M.Equal (load_into_map b [a] m) (M.add b a m).
Proof. reflexivity. Qed.

Corollary load_into_map_cons b elt a xs (m : M.t elt) :
  M.Equal (load_into_map b (a :: xs) m)
          (load_into_map (plusPtr (A:=Word) b 1) xs (M.add b a m)).
Proof. reflexivity. Qed.

Lemma load_into_map_add : forall b k elt a xs (m : M.t elt),
  ltPtr b k ->
    M.Equal (load_into_map k xs (M.add b a m)) (M.add b a (load_into_map k xs m)).
Proof.
  intros.
  generalize dependent b.
  generalize dependent k.
  generalize dependent a.
  generalize dependent m.
  induction xs; simpl; intros.
    unfold load_into_map; simpl.
    reflexivity.
  rewrite !load_into_map_cons.
  repeat rewrite IHxs by nomega.
  rewrite add_associative.
  f_equiv.
  nomega.
Qed.

Lemma load_into_map_Proper {elt} :
  Proper (N.eq ==> eq ==> @M.Equal elt ==> @M.Equal elt) (@load_into_map elt).
Proof.
  relational.
  rewrite H; clear H x.
  generalize dependent y.
  generalize dependent x1.
  generalize dependent y1.
  induction y0; simpl; intros; subst.
    assumption.
  rewrite !load_into_map_cons.
  apply IHy0.
  f_equiv.
  assumption.
Qed.

Lemma load_into_map_app b elt xs ys (m : M.t elt) :
  M.Equal (load_into_map b (xs ++ ys) m)
          (load_into_map b xs (load_into_map (plusPtr (A:=Word) b
                                                      (N.of_nat (length xs)))
                                             ys m)).
Proof.
  intros.
  generalize dependent b.
  generalize dependent m.
  generalize dependent ys.
  induction xs; simpl; intros.
    unfold load_into_map; simpl.
    rewrite plusPtr_zero.
    reflexivity.
  rewrite load_into_map_cons.
  rewrite IHxs; clear IHxs.
  rewrite load_into_map_cons.
  apply load_into_map_Proper; auto.
    reflexivity.
  rewrite load_into_map_add by nomega.
  f_equiv.
  apply load_into_map_Proper; auto.
    unfold N.eq.
    nomega.
  reflexivity.
Qed.

Lemma find_load_into_map : forall (b x : N) A (xs : list A) m,
  b <= x < b + N.of_nat (length xs)
    -> M.find x (load_into_map b xs m) = nth_error xs (N.to_nat (x - b)%N).
Proof.
  intros.
  generalize dependent b.
  induction xs; simpl; intros.
    nomega.
  rewrite load_into_map_cons.
  destruct (N.eq_dec x b); subst;
  rewrite load_into_map_add by nomega.
    rewrite F.add_eq_o; auto.
    replace (b - b) with 0 by nomega.
    reflexivity.
  rewrite F.add_neq_o; auto.
  rewrite IHxs.
    replace (a :: xs) with ([a] ++ xs) by auto.
    rewrite nth_error_app2; auto.
      f_equal.
      nomega.
    nomega.
  nomega.
Qed.

End HeapState.
