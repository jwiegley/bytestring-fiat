Require Import
  Here.FMapExt
  Here.Nomega
  Coq.Sets.Ensembles
  Here.TupleEnsembles
  Here.LogicalRelations
  Coq.FSets.FMapList
  Coq.FSets.FMapFacts
  Coq.Structures.OrderedTypeEx.

Module FunMaps (O : OrderedType).

Module E := FMapExt(O).
Include E.

Definition Map_AbsR
           (A B : Type) (R  : A -> B -> Prop)
           (or : Ensemble (M.key * A))
           (nr : M.t B) : Prop :=
  forall addr,
    (forall blk,
       Lookup addr blk or
         -> (exists cblk, M.find addr nr = Some cblk /\ R blk cblk)) /\
    (forall cblk,
       M.find addr nr = Some cblk
         -> (exists blk, Lookup addr blk or /\ R blk cblk)).

Ltac reduce_context :=
  try repeat teardown; subst;
  match goal with
  | [ H1 : Map_AbsR _ _ _,
      H2 : Lookup ?A ?D ?K |- _ ] =>
    let HA := fresh "HA" in
    let HB := fresh "HB" in
    destruct (H1 A) as [HA HB];
    let HC := fresh "HC" in
    let HD := fresh "HD" in
    let cblk := fresh "cblk" in
    destruct (HA _ H2) as [cblk [HC HD]]; clear HA HB H2
  | [ H1 : Map_AbsR _ _ _,
      H2 : M.find ?A ?K = Some ?D |- _ ] =>
    let HA := fresh "HA" in
    let HB := fresh "HB" in
    destruct (H1 A) as [HA HB];
    let HC := fresh "HC" in
    let HD := fresh "HD" in
    let blk := fresh "blk" in
    destruct (HB _ H2) as [blk [HC HD]]; clear HA HB H2
  end.

Ltac reduction :=
  try repeat teardown; subst;
  match goal with
  | [ _ : ?T -> ?U -> Prop,
      H1 : Map_AbsR _ _ _,
      H2 : Lookup ?A ?D ?K |- exists _ : ?U, _ ] =>
    let HA := fresh "HA" in
    destruct (H1 A) as [HA _];
    let HC := fresh "HC" in
    let HD := fresh "HC" in
    let cblk := fresh "cblk" in
    destruct (HA _ H2) as [cblk [HC HD]]; clear HA H2;
    exists cblk; split; trivial
  | [ H1 : Map_AbsR _ _ _,
      H2 : Lookup ?A ?D ?K |- _ ] =>
    let HA := fresh "HA" in
    let HB := fresh "HB" in
    destruct (H1 A) as [HA HB];
    let HC := fresh "HC" in
    let HD := fresh "HD" in
    let cblk := fresh "cblk" in
    destruct (HA _ H2) as [cblk [HC HD]]; clear HA HB H2
  | [ _ : ?T -> ?U -> Prop,
      H1 : Map_AbsR _ _ _,
      H2 : M.find ?A ?K = Some ?D |- exists _ : ?T, _ ] =>
    let HB := fresh "HB" in
    destruct (H1 A) as [_ HB];
    let HC := fresh "HC" in
    let HD := fresh "HD" in
    let blk := fresh "blk" in
    destruct (HB _ H2) as [blk [HC HD]]; clear HB H2;
    exists blk; split; trivial
  | [ H1 : Map_AbsR _ _ _,
      H2 : M.find ?A ?K = Some ?D |- _ ] =>
    let HA := fresh "HA" in
    let HB := fresh "HB" in
    destruct (H1 A) as [HA HB];
    let HC := fresh "HC" in
    let HD := fresh "HD" in
    let blk := fresh "blk" in
    destruct (HB _ H2) as [blk [HC HD]]; clear HA HB H2
  end.

Ltac simplify_maps :=
  match goal with
  | [ H : M.find (elt:=?T) ?A (M.add ?K ?E ?M) = Some ?B |- _ ] =>
    apply F.find_mapsto_iff, F.add_mapsto_iff in H;
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    destruct H as [[H1 H2]|[H3 H4]];
    [subst|apply F.find_mapsto_iff in H4]
  | [ H : M.find (elt:=?T) ?A (M.remove ?KE ?M) = Some ?B |- _ ] =>
    apply F.find_mapsto_iff, F.remove_mapsto_iff in H;
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    destruct H as [H1 H2];
    apply F.find_mapsto_iff in H2
  | [ H : M.find (elt:=?T) ?A (M.map ?F ?M) = Some ?B |- _ ] =>
    apply F.find_mapsto_iff, F.map_mapsto_iff in H;
    let cblk := fresh "cblk" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    destruct H as [cblk [H1 H2]];
    apply F.find_mapsto_iff in H2
  | [ H : M.find (elt:=?T) ?A (P.filter ?F ?M) = Some ?B |- _ ] =>
    apply F.find_mapsto_iff, P.filter_iff in H;
    [let H1 := fresh "H1" in
     let H2 := fresh "H2" in
     destruct H as [H1 H2];
     apply F.find_mapsto_iff in H1|]
  | [ H : M.find (elt:=?T) ?A (M.mapi ?F ?M) = Some ?B |- _ ] =>
    rewrite F.mapi_o, <- F.map_o in H
  | [ H : M.find (elt:=?T) ?A (M.empty ?U) = Some ?B |- _ ] =>
    apply F.find_mapsto_iff, F.empty_mapsto_iff in H;
    contradiction
  | [ H1 : M.find (elt:=?T) ?A ?M = Some ?B,
      H2 : M.Empty (elt:=?T) ?M |- _ ] =>
    apply P.elements_Empty in H2;
    rewrite F.elements_o in H1;
    rewrite H2 in H1;
    inversion H1
  end.

Corollary Map_AbsR_A {A B} (R : A -> B -> Prop)
          (or : Ensemble (M.key * A))
          (nr : M.t B) :
  Map_AbsR R or nr ->
  forall addr blk,
    Lookup addr blk or ->
      exists cblk, M.find addr nr = Some cblk /\ R blk cblk.
Proof. intros; reduction. Qed.

Corollary Map_AbsR_B {A B} (R : A -> B -> Prop)
          (or : Ensemble (M.key * A))
          (nr : M.t B) :
  Map_AbsR R or nr ->
  forall addr cblk,
    M.find addr nr = Some cblk ->
      exists blk, Lookup addr blk or /\ R blk cblk.
Proof. intros; reduction. Qed.

Lemma Oeq_neq_sym : forall x y, ~ O.eq x y -> ~ O.eq y x.
Proof.
  intros.
  unfold not; intros.
  rewrite H0 in H.
  contradiction H.
  apply O.eq_refl.
Qed.

Section FunMaps_AbsR.

Variables A B : Type.
Variable R : (A -> B -> Prop).

Hypothesis Oeq_eq : forall a b, O.eq a b <-> a = b.
Hypothesis Oeq_neq : forall a b, ~ O.eq a b <-> a <> b.

Ltac equalities :=
  repeat
    match goal with
    | [ H : O.eq ?X ?Y |- _ ] =>
      apply Oeq_eq in H; subst
    | [ H : ?X <> ?X |- _ ] =>
      contradiction H; reflexivity
    | [ H : ?X <> ?Y |- _ ] =>
      apply Oeq_neq in H; subst
    | [ |- ?X <> ?Y ] =>
      unfold not; intros; subst
    | [ |- ~ O.eq ?X ?Y ] =>
      let H := fresh "H" in
      unfold not; intro H;
      apply Oeq_eq in H; subst
    | [ |- O.eq ?X ?Y -> False ] =>
      let H := fresh "H" in
      unfold not; intro H;
      apply Oeq_eq in H; subst
    | [ |- O.eq ?X ?X ] =>
      apply O.eq_refl
    | [ H : ~ O.eq ?X ?X |- _ ] =>
      contradiction H; apply O.eq_refl
    | [ H : O.eq ?X ?X -> False |- _ ] =>
      contradiction H; apply O.eq_refl
    | [ |- ?X = ?X ] =>
      reflexivity
    end.

Corollary Proper_Oeq_negb : forall B f,
  Proper (O.eq ==> eq ==> eq) f ->
  Proper (O.eq ==> eq ==> eq) (fun (k : M.key) (e : B) => negb (f k e)).
Proof. intros ?????????; equalities. Qed.

Export LogicalRelationNotations.

Open Scope lsignature_scope.

Program Instance Empty_Map_AbsR : Empty [R Map_AbsR R] (M.empty _).
Obligation 1. split; intros; [ inversion H | simplify_maps ]. Qed.

Program Instance Single_Map_AbsR :
  (@Single _ _) [R O.eq ===> R ===> Map_AbsR R] singleton.
Obligation 1.
  intros ??????.
  split; intros;
  [exists y0|exists x0];
  equalities.
    repeat teardown; subst.
    split; trivial.
    unfold P.uncurry; simpl.
    rewrite F.elements_o; simpl.
    rewrite eqb_refl; trivial.
  rewrite F.elements_o in H1; simpl in H1.
  unfold F.eqb in H1.
  destruct (O.eq_dec addr y).
    inversion H1.
    equalities.
    split; trivial.
    apply Lookup_Single.
  discriminate.
Qed.

Program Instance Lookup_Map_AbsR
        `{LogicalImpl _ _ R eq} `{LogicalDep _ _ R eq} :
  (@Lookup _ _) [R O.eq ===> R ===> Map_AbsR R ===> iff]
  (fun k e m => M.find k m = Some e).
Obligation 1.
  intros ?????????.
  split; intros; equalities; reduction;
  [ pose proof (forward_impl _ _ _ H2 HD)
  | pose proof (reverse_impl _ _ _ H2 HD) ];
  subst; assumption.
Qed.

Program Instance Lookup_MapsTo_Map_AbsR
        `{LogicalImpl _ _ R eq} `{LogicalDep _ _ R eq} :
  (@Lookup _ _) [R O.eq ===> R ===> Map_AbsR R ===> iff]
  (fun k e m => M.find k m = Some e).
Obligation 1.
  intros ?????????.
  split; intros; equalities; reduction;
  [ pose proof (forward_impl _ _ _ H2 HD)
  | pose proof (reverse_impl _ _ _ H2 HD) ];
  subst; assumption.
Qed.

Program Instance Same_Map_AbsR
        `{LogicalImpl _ _ R eq} `{LogicalDep _ _ R eq} :
  (@Same _ _) [R Map_AbsR R ===> Map_AbsR R ===> iff] M.Equal.
Obligation 1.
  intros ??????.
  split; intros.
    apply F.Equal_mapsto_iff; split; intros.
      apply F.find_mapsto_iff in H4;
      apply F.find_mapsto_iff.
      reduce_context.
      rewrite H3 in HC.
      reduction.
      pose proof (forward_impl _ _ _ HD HD0);
      subst; assumption.
    apply F.find_mapsto_iff in H4;
    apply F.find_mapsto_iff.
    reduction.
    apply H3 in HC.
    reduction.
    pose proof (forward_impl _ _ _ HD HD0);
    subst; assumption.
  split; intros.
    reduction.
    rewrite H3 in HC.
    reduction.
    pose proof (reverse_impl _ _ _ HD HD0);
    subst; assumption.
  reduction.
  rewrite <- H3 in HC.
  reduction.
  pose proof (reverse_impl _ _ _ HD HD0);
  subst; assumption.
Qed.

Program Instance Member_Map_AbsR :
  (@Member _ _) [R O.eq ===> Map_AbsR R ===> boolR] (@M.mem _).
Obligation 1.
  unfold Member; intros ??????.
  rewrite F.mem_find_b.
  split; intros; equalities.
    reduction.
    rewrite HC.
    reflexivity.
  destruct (M.find (elt:=B) y y0) eqn:Heqe.
    reduction.
    exists blk.
    assumption.
  discriminate.
Qed.

Lemma has_Some : forall A B (a : option A) (b : B),
  a <> None -> exists b, a = Some b.
Proof.
  intros.
  destruct a.
    exists a; reflexivity.
  contradiction H.
  reflexivity.
Qed.

Program Instance Member_In_Map_AbsR :
  (@Member _ _) [R O.eq ===> Map_AbsR R ===> iff] (@M.In _).
Obligation 1.
  unfold Member; intros ??????.
  split; intros; equalities.
    destruct H1.
    reduction.
    apply F.in_find_iff.
    rewrite HC.
    apply Common.Some_ne_None.
  apply F.in_find_iff in H1.
  eapply has_Some in H1; eauto.
  destruct H1.
  reduction.
  exists blk.
  assumption.
Qed.

(* Insert *)

Program Instance Remove_Map_AbsR :
  (@Remove _ _) [R O.eq ===> Map_AbsR R ===> Map_AbsR R] (@M.remove _).
Obligation 1.
  intros ??????.
  split; intros.
  - reduction; equalities.
    apply Oeq_neq_sym in H1.
    rewrite F.remove_neq_o; trivial.
  - simplify_maps; reduction.
    teardown; equalities.
Qed.

Program Instance Update_Map_AbsR :
  (@Update _ _) [R O.eq ===> R ===> Map_AbsR R ===> Map_AbsR R] (@M.add _).
Obligation 1.
  intros ?????????.
  split; intros; repeat teardown; subst.
  - exists y0; intuition.
    apply F.add_eq_o; symmetry; assumption.
  - reduction; equalities.
    apply Oeq_neq_sym in H2.
    rewrite F.add_neq_o; trivial.
  - simplify_maps.
      exists x0.
      intuition; equalities.
      right; constructor.
    reduction; teardown.
    right; constructor;
    equalities; assumption.
Qed.

(* Move *)

Program Instance Map_Map_AbsR :
  (@Map _ _) [R (O.eq ===> R ===> R) ===> Map_AbsR R ===> Map_AbsR R]
  (@M.mapi _ _).
Obligation 1.
  intros ??????.
  split; intros.
  - teardown.
    do 2 destruct H1.
    reduce_context.
    exists (y addr cblk).
    split.
      rewrite F.mapi_o, <- F.map_o.
        apply F.find_mapsto_iff, F.map_mapsto_iff.
        exists cblk; intuition.
        apply F.find_mapsto_iff; assumption.
      intros; equalities.
    apply H; trivial.
  - simplify_maps.
      simplify_maps.
      reduce_context.
      exists (x addr blk).
      split.
        teardown.
      apply H; trivial.
    intros; equalities.
Qed.

Program Instance Filter_Map_AbsR :
  (@Filter _ _) [R (O.eq ===> R ===> boolR) ===> Map_AbsR R ===> Map_AbsR R]
  (@P.filter _).
Obligation 1.
  intros ??????.
  split; intros.
    reduction.
    apply F.find_mapsto_iff, P.filter_iff.
      intros ??????; subst; equalities.
    split.
      apply F.find_mapsto_iff; trivial.
    eapply H in H1; eauto.
  simplify_maps.
  reduction.
  eexists; simpl; trivial.
    eapply H in H3; eauto.
  intros ??????; subst; equalities.
Qed.

(* Define *)
(* Modify *)
(* Overlay *)

Program Instance All_Map_AbsR :
  (@All _ _) [R (O.eq ===> R ===> boolR) ===> Map_AbsR R ===> boolR]
  (@P.for_all _).
Obligation 1.
  intros ??????.
  split; intros;
  unfold All, P.for_all in *.
    apply P.fold_rec_bis; intros; trivial; subst.
    apply F.find_mapsto_iff in H2.
    reduction.
    apply H1 in HC.
    eapply H in HC; eauto.
    rewrite HC.
    reflexivity.
  intros.
  reduction.
  eapply H; eauto.
  revert H1.
  revert HC.
  apply P.fold_rec; intros; subst; intuition.
    simplify_maps.
  rewrite H3 in HC.
  simplify_maps.
    equalities.
    destruct (y a cblk) eqn:Heqe; intuition.
  destruct (y k e) eqn:Heqe; intuition.
Qed.

Program Instance Any_Map_AbsR :
  (@Any _ _) [R (O.eq ===> R ===> boolR) ===> Map_AbsR R ===> boolR]
  (@P.exists_ _).
Obligation 1.
  intros ??????.
  split; intros;
  unfold Any in *.
    apply P.exists_iff.
      intros ??????; subst; equalities.
    do 3 destruct H1.
    reduction.
    exists (x1, cblk).
    split; simpl.
      apply F.find_mapsto_iff; assumption.
    eapply H; eauto.
  apply P.exists_iff in H1.
    do 2 destruct H1.
    apply F.find_mapsto_iff in H1.
    reduction.
    exists k.
    exists blk.
    split; trivial.
    eapply H; eauto.
  intros ??????; subst; equalities.
Qed.

End FunMaps_AbsR.

Program Instance Same_set_Map_AbsR : forall A B (R : A -> B -> Prop),
  Proper (eq ==> @Same _ _ ==> @M.Equal _ ==> iff) (@Map_AbsR A B).
Obligation 1.
  intros ?????????.
  split; intros;
  split; intros; subst.
  - apply H0 in H3; reduction.
    rewrite <- H1; assumption.
  - rewrite <- H1 in H3; reduction.
    apply H0 in HC; assumption.
  - apply H0 in H3; reduction.
    rewrite H1; assumption.
  - rewrite H1 in H3; reduction.
    apply H0; assumption.
Qed.

End FunMaps.
