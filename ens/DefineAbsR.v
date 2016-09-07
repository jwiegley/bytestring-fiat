Require Import
  ByteString.Lib.LibExt
  ByteString.Lib.Nomega
  ByteString.Lib.FMapExt
  ByteString.Lib.FunMaps
  ByteString.Lib.TupleEnsembles
  ByteString.HeapState
  ByteString.Ens.Decidable
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Generalizable All Variables.

Module Define_AbsR (M : WSfun N_as_DT).

Module F := WFacts_fun N_as_DT M.

Module Import FunMaps := FunMaps N_as_DT M.
Import FMapExt.

Lemma find_define : forall Word8 addr len pos v w m,
  (Ifdec within addr len pos
   Then v = w
   Else M.MapsTo pos v m)
    -> M.MapsTo pos v (N.peano_rect (fun _ => M.t Word8) m
                                    (fun i => M.add (addr + i)%N w) len).
Proof.
  intros.
  decisions; subst;
  induction len using N.peano_ind; simpl in *; trivial.
  - nomega.
  - rewrite N.peano_rect_succ.
    destruct (N.eq_dec pos (addr + len)); subst.
      intuition.
    apply F.add_mapsto_iff.
    right; split; trivial.
      nomega.
    apply IHlen; nomega.
  - rewrite N.peano_rect_succ.
    simplify_maps.
    right; split; trivial.
      nomega.
    apply IHlen; nomega.
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
    -> Ifdec within addr len pos
       Then v = w
       Else M.MapsTo pos v m.
Proof.
  intros.
  induction len using N.peano_ind; simpl in *;
  decisions; auto; try nomega;
  rewrite N.peano_rect_succ in H;
  simplify_maps; nomega.
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
    unfold Ifdec_Then_Else; simpl.
      decisions; nomega.
    decisions.
      contradiction H0; nomega.
    apply H; firstorder.
  - reduction.
    apply find_define_inv in H0.
    decisions; auto; subst.
      left; intuition; nomega.
    right; intuition.
      nomega.
    apply H in H0.
    destruct H0, H0; subst.
    intuition.
  - reduction.
    apply find_define_inv in H0.
    decisions; auto; subst.
      exists w; intuition; teardown.
      left; intuition; nomega.
    apply H in H0.
    destruct H0, H0; subst.
    exists cblk; intuition; teardown.
    right; intuition; nomega.
  - repeat teardown; subst; [inv H2|];
    apply find_define;
    unfold Ifdec_Then_Else; simpl.
      decisions; nomega.
    apply H in H2.
    decisions.
      nomega.
    destruct H2, H1; subst.
    intuition.
Qed.

End Define_AbsR.
