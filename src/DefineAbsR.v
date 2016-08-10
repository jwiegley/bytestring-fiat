Require Import
  Here.LibExt
  Here.Nomega
  Here.FMapExt
  Here.FunMaps
  Here.TupleEnsembles
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Generalizable All Variables.

Module Define_AbsR (M : WSfun N_as_DT).

Module F := WFacts_fun N_as_DT M.

Module Import FunMaps := FunMaps N_as_DT M.
Import FMapExt.

Lemma find_define : forall Word8 addr len pos v w m,
  (IfDec within addr len pos
   Then v = w
   Else M.MapsTo pos v m)
    -> M.MapsTo pos v (N.peano_rect (fun _ => M.t Word8) m
                                    (fun i => M.add (addr + i)%N w) len).
Proof.
  intros.
  decisions; subst.
    apply Bool.andb_true_iff in Heqe.
    destruct Heqe.
    undecide.
    induction len using N.peano_ind; simpl in *.
      rewrite N.add_0_r in H0.
      nomega.
    rewrite N.peano_rect_succ.
    destruct (N.eq_dec pos (addr + len)); subst.
      intuition.
    apply F.add_mapsto_iff.
    right; split; trivial.
      apply not_eq_sym; assumption.
    rewrite N.add_succ_r in H0.
    apply N.lt_succ_r in H0.
    pose proof (proj2 (N.le_neq pos (addr + len)) (conj H0 n)).
    apply IHlen; assumption.
  apply Bool.andb_false_iff in Heqe.
  destruct Heqe; undecide;
  induction len using N.peano_ind; simpl in *; auto;
  rewrite N.peano_rect_succ.
    simplify_maps.
    right; split; trivial.
    unfold not; intros; subst.
    rewrite <- (N.add_0_r addr) in H0 at 2.
    apply N.add_lt_cases in H0.
    destruct H0.
      nomega.
    contradiction (N.nlt_0_r len).
  rewrite N.add_succ_r in H0.
  simplify_maps.
  right; split.
    unfold not; intros; subst.
    apply N.le_succ_l in H0.
    nomega.
  apply IHlen.
  apply N.le_succ_l in H0.
  nomega.
Qed.

Lemma Nle_ne_succ : forall n m,
  n <> m -> n < N.succ m -> n < m.
Proof.
  intros.
  apply N.le_succ_l in H0.
  apply N.succ_le_mono in H0.
  apply N.le_neq; intuition.
Qed.

Lemma find_define_inv : forall Word8 addr len pos v w m,
  M.MapsTo pos v (N.peano_rect (fun _ => M.t Word8) m
                               (fun i => M.add (addr + i)%N w) len)
    -> IfDec within addr len pos
       Then v = w
       Else M.MapsTo pos v m.
Proof.
  intros.
  induction len using N.peano_ind; simpl in *;
  decisions; auto.
  - apply Bool.andb_true_iff in Heqe;
    destruct Heqe; undecide.
    rewrite N.add_0_r in H1.
    nomega.
  - rewrite N.peano_rect_succ in H.
    simplify_maps; auto.
  - rewrite N.peano_rect_succ in H.
    simplify_maps; auto.
      nomega.
    apply Bool.andb_true_iff in Heqe;
    destruct Heqe; undecide.
    apply Bool.andb_false_iff in Heqe0;
    destruct Heqe0; undecide.
      nomega.
    intuition; subst.
    rewrite N.add_succ_r in H1.
    apply N.le_succ_l in H1.
    nomega.
  - rewrite N.peano_rect_succ in H.
    simplify_maps; auto.
    intuition.
    apply Bool.andb_true_iff in Heqe0;
    destruct Heqe0; undecide.
    apply Bool.andb_false_iff in Heqe;
    destruct Heqe; undecide.
      nomega.
    rewrite N.add_succ_r in H1.
    apply not_eq_sym in H3.
    pose proof (Nle_ne_succ H3 H1).
    nomega.
  - rewrite N.peano_rect_succ in H.
    simplify_maps; auto.
    intuition.
    apply Bool.andb_false_iff in Heqe0;
    destruct Heqe0; undecide;
    apply Bool.andb_false_iff in Heqe;
    destruct Heqe; undecide.
    + rewrite <- N.add_0_r in H0.
      apply N.add_lt_cases in H0.
      destruct H0.
        nomega.
      contradiction (N.nlt_0_r len).
    + rewrite <- N.add_0_r in H.
      apply N.add_lt_cases in H.
      destruct H.
        nomega.
      contradiction (N.nlt_0_r len).
    + rewrite <- N.add_0_r in H0.
      apply N.add_lt_cases in H0.
      destruct H0.
        nomega.
      contradiction (N.nlt_0_r len).
    + rewrite N.add_succ_r in H.
      apply N.le_succ_l in H.
      nomega.
Qed.

Lemma Define_Map_AbsR : forall Word8 x y b len w,
  Map_AbsR eq x y
    -> Map_AbsR eq (Define (within b len) w x)
                (N.peano_rect (fun _ => M.t Word8) y
                              (fun i => M.add (b + i)%N w) len).
Proof.
  intros.
  relational_maps.
  - teardown.
    destruct H0, H0; [inv H1|];
    exists blk; intuition;
    apply find_define;
    unfold IfDec_Then_Else; simpl.
      apply within_reflect in H0.
      rewrite H0; reflexivity.
    apply not_within_reflect in H0.
    rewrite H0.
    apply H.
    exists blk; intuition.
  - reduction.
    apply find_define_inv in H0.
    decisions; auto; subst.
      left.
      apply within_reflect in Heqe.
      intuition.
    right.
    apply not_within_reflect in Heqe.
    apply H in H0.
    destruct H0, H0; subst.
    intuition.
  - reduction.
    apply find_define_inv in H0.
    decisions; auto; subst.
      apply within_reflect in Heqe.
      exists w; intuition.
      teardown.
      left; intuition.
    apply not_within_reflect in Heqe.
    apply H in H0.
    destruct H0, H0; subst.
    exists cblk; intuition.
    teardown.
    right; intuition.
  - repeat teardown; subst; [inv H2|];
    apply find_define;
    unfold IfDec_Then_Else; simpl.
      apply within_reflect in H0.
      rewrite H0; reflexivity.
    apply not_within_reflect in H0.
    rewrite H0.
    apply H.
    exists cblk; intuition.
Qed.

End Define_AbsR.
