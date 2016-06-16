Require Import Fiat.ADT Fiat.ADTNotation.

Require Import Coq.Sets.Ensembles.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.

Require Import
  Here.ByteString
  Here.LibExt
  Here.Same_set
  Here.ADTInduction.

(** Proofs of general properties of ByteStrings *)

Section ByteString.

Variable Word8 : Type.

Definition ByteStringSpec := ByteStringSpec Word8.
Definition ByteString     := ByteString Word8.

(** Theorem: There are no gaps in the key space of ByteStrings. *)

Theorem indices_contiguous :
  forall (r : Rep ByteStringSpec), fromADT _ r
    -> forall i x, Ensembles.In _ r (S i, x)
    -> exists y, Ensembles.In _ r (i, y).
Proof.
  intros.
  generalize dependent i.
  ADT induction r.
  - inversion H0.
Abort.
(*
  - inversion H0.
  - apply H in H0.
    destruct (In_zip_series x x0 (Le.le_0_n _) H0) as [x1 ?].
    exists x1.
    apply H; trivial.
  - simplify_ensembles.
    destruct i.
      exists x0.
      right; constructor.
    apply IHfromADT in H0.
    destruct_ex.
    exists x1.
    unfold Ensemble_map, first.
    simplify_ensembles.
      exact H0.
    constructor.
  - destruct H0 as [n [[H0 H2] H3]]; subst.
    destruct H0 as [x1 H0].
    destruct (Peano_dec.eq_nat_dec n i); subst;
    inv H1.
    + specialize (H2 (S i) x).
      intuition.
    + inv H3.
      exists x1.
      constructor.
      assumption.
    + destruct (IHfromADT _ H3) as [x3 ?].
      exists x3.
      constructor.
      assumption.
    + inv H3; tauto.
  - unfold If_Opt_Then_Else in *.
    destruct x0; [| apply IHfromADT; trivial ].
    specialize (H0 w eq_refl).
    simplify_ensembles.
    apply pred_S_S in H4; simpl in H4; subst.
    apply IHfromADT in H2.
    destruct_ex.
    exists x0.
    simplify_ensembles.
      exact H1.
      unfold not; intros; inversion H2.
    constructor.
  - destruct x0.
      specialize (H0 w eq_refl).
      specialize (H0' w).
      destruct_ex.
      do 2 destruct H0, H2.
      destruct_ex.
      subst.
      inversion H1; clear H1.
      pose proof H4.
      apply IHfromADT in H4.
      destruct_ex.
      exists x4.
      eexists.
        assumption.
      unfold not; intros.
      inv H8.
      specialize (H6 (S i) x).
      intuition.
    clear H0.
    specialize (H0' x).
    destruct_ex.
    do 2 destruct H0.
    destruct_ex.
    subst.
    inversion H1; clear H1.
    pose proof H2.
    apply IHfromADT in H2.
    destruct_ex.
    exists x2.
    constructor.
      assumption.
    unfold not; intros.
    inv H5.
    specialize (H3 (S i) x2).
    intuition.
Qed.
*)

(** Theorem: There are no repeated keys. *)

Theorem indices_unique :
  forall (r : Rep ByteStringSpec), fromADT _ r
    -> forall i x, Ensembles.In _ r (i, x)
    -> forall y, x <> y -> ~ Ensembles.In _ r (i, y).
Proof.
  intros.
  generalize dependent i.
  generalize dependent x.
  generalize dependent y.
  ADT induction r; try (unfold not); intros.
  - inversion H0.
  - simplify_ensembles.
Abort.
(*
  - apply H in H0.
    apply H in H2.
    pose proof (In_zip_at_index i 0 _ x x0 H2 H0).
    congruence.
  - inv H0; inv H2; inv H0; inv H3; simplify_ensembles.
    In_contradiction IHfromADT.
  - do 2 destruct H0; subst.
    do 2 destruct H0.
    simplify_ensembles.
    + In_contradiction IHfromADT.
    + specialize (H4 (S x1) y); intuition.
    + specialize (H4 (S x1) x); intuition.
  - unfold If_Opt_Then_Else in *.
    destruct x0.
    + specialize (H0 w eq_refl).
      inv H2; inv H3; simplify_ensembles.
      destruct n, n0.
      * In_contradiction IHfromADT.
      * apply Ensemble_fst_eq_inv in H6.
        In_contradiction IHfromADT.
      * apply Ensemble_fst_eq_inv in H5.
        In_contradiction IHfromADT.
      * rewrite !Nat.pred_succ in H7; subst.
        In_contradiction IHfromADT.
    + In_contradiction IHfromADT.
  - destruct x0.
    + specialize (H0 w eq_refl).
      specialize (H0' w).
      destruct_ex.
      destruct H0, H4; subst.
      inv H2; inv H3.
      In_contradiction IHfromADT.
    + clear H0.
      specialize (H0' x).
      destruct_ex.
      destruct H0; subst.
      inv H2; inv H3.
      In_contradiction IHfromADT.
Qed.
*)

(*
Corollary index_limit :
  forall (r : Rep ByteStringSpec) n m x, fromADT _ r ->
    is_final_index r n -> n < m
      -> ~ Ensembles.In (nat * Word8) r (m, x).
Proof.
  intros.
  generalize dependent n.
  generalize dependent x.
  unfold is_final_index.
  ADT induction r; try (unfold not); intros.
  - inv H.
  - inv H; omega.
  - destruct H0.
    destruct_ex.
    exact (H3 _ _ H1 H2).
  - destruct H1.
    destruct_ex.
    exact (H3 _ _ H2 H0).
  - destruct H1.
    destruct_ex.
    exact (H4 _ _ H2 H3).
  - destruct H1.
    destruct_ex.
    exact (H4 _ _ H2 H3).
  - destruct H1.
    destruct_ex.
    exact (H4 _ _ H2 H3).
Qed.
*)

Corollary indices_unique_impl :
  forall (r : Rep ByteStringSpec), fromADT _ r
    -> forall i x y, Ensembles.In _ r (i, x)
    -> Ensembles.In _ r (i, y) -> x = y.
Proof.
  intros.
  generalize dependent i.
  generalize dependent x.
  generalize dependent y.
  ADT induction r.
  - inv H0.
Admitted.
(*
  - inv H0; inv H1.
    reflexivity.
  - apply H in H0.
    apply H in H1.
    apply In_zip_at_index with (i:=i) (n:=0) (xs:=x0); trivial.
  - inv H1; inv H2; inv H0; inv H1; simplify_ensembles.
    exact (IHfromADT _ _ _ H2 H0).
  - destruct_ex; destruct H0; subst.
    inv H1; inv H2; simplify_ensembles.
    + exact (IHfromADT _ _ _ H3 H1).
    + apply index_limit with (m:=S x1) (x:=x) in H0; intuition.
    + apply index_limit with (m:=S x1) (x:=y) in H0; intuition.
  - unfold If_Opt_Then_Else in *.
    destruct x0.
    + specialize (H0 w eq_refl).
      inv H2; inv H3; simplify_ensembles.
      destruct n, n0.
      * apply IHfromADT with (i:=0); trivial.
      * apply Ensemble_fst_eq_inv in H4.
        specialize (IHfromADT _ _ _ H0 H3); contradiction.
      * apply Ensemble_fst_eq_inv in H5.
        specialize (IHfromADT _ _ _ H0 H2); contradiction.
      * rewrite !Nat.pred_succ in H6; subst.
        exact (IHfromADT _ _ _ H2 H3).
    + exact (IHfromADT _ _ _ H1 H2).
  - destruct x0.
    + specialize (H0 w eq_refl).
      specialize (H0' w).
      destruct_ex.
      destruct H0, H3; subst.
      inv H1; inv H2.
      exact (IHfromADT _ _ _ H5 H1).
    + clear H0.
      specialize (H0' x).
      destruct_ex.
      destruct H0; subst.
      inv H1; inv H2.
      exact (IHfromADT _ _ _ H3 H1).
Qed.
*)

Lemma uncons_reduces :
  forall bs : Rep ByteStringSpec, fromADT _ bs ->
    forall v, uncons bs ↝ v ->
      match v with
      | (bs', Some _) => subset (Ensemble_map (first S) bs') bs
      | (bs', None)   => Same_set _ bs' bs
      end.
Proof.
  intros.
  destruct v.
  unfold uncons in H0; simpl in H0.
  unfold If_Opt_Then_Else in H0.
  apply Pick_inv in H0; simpl in H0.
  destruct o.
  - destruct H0.
    unfold Ensemble_map, first in *.
    split; setoid_rewrite H1; clear H1;
    autorewrite with monad laws.
    + intros x Hx; destruct Hx; simplify_ensembles.
      destruct (Peano_dec.eq_nat_dec n 0); subst.
      * pose proof (indices_unique_impl H 0 w w1 H0 H2).
        subst; contradiction H3; constructor.
      * rewrite Nat.succ_pred; trivial.
    + unfold not; intros.
      specialize (H1 (0, w) H0).
      destruct H1; simplify_ensembles.
  - subst; simplify_ensembles.
Qed.

Lemma guarded_uncons (bs : ByteString) :
  fromADT _ bs ->
  Comp { p : ByteString * option Word8
       | uncons bs ↝ p /\ fromADT _ (fst p) }.
Proof.
  intros.
  eapply (Bind_dep (uncons bs)).
  intros v H0.
  refine (ret (exist _ v _)).
  split; trivial.
  eapply (fromADTMethod (lookupMethod (getADTSig ByteStringSpec)
                                      get_fin ``unconsS) _ H).
  exists (snd v).
  rewrite <- surjective_pairing.
  exact H0.
Qed.

End ByteString.