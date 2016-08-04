Require Import
  Here.FMapExt
  Here.Nomega
  Here.TupleEnsembles
  Here.TupleEnsemblesFinite
  Coq.FSets.FMapList
  Coq.FSets.FMapFacts
  Coq.Structures.OrderedTypeEx.

Require Import
  CoqRel.LogicalRelations
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.Setoids.Setoid
  Coq.Classes.Equivalence
  Here.Same_set.

Notation "f [R  rel ] f'" := (Related rel f f')
  (right associativity, at level 55) : rel_scope.

Module FunMaps (O : OrderedType).

Lemma Oeq_neq_sym : forall x y, ~ O.eq x y -> ~ O.eq y x.
Proof.
  intros.
  unfold not; intros.
  apply O.eq_sym in H0.
  contradiction.
Qed.

Hint Resolve Oeq_neq_sym.

Module E := FMapExt(O).
Include E.

Lemma Proper_Oeq_negb : forall B f,
  Proper (O.eq ==> eq ==> eq) f ->
  Proper (O.eq ==> eq ==> eq) (fun (k : M.key) (e : B) => negb (f k e)).
Proof. intros ?????????; f_equal; subst; rewrite H0; reflexivity. Qed.

Hint Resolve Proper_Oeq_negb.

Open Scope rel_scope.

Definition Map_AbsR `(R : A -> B -> Prop)
           (or : Ensemble (M.key * A)) (nr : M.t B) : Prop :=
  forall addr,
    (forall blk, Lookup addr blk or
       <-> exists cblk, M.MapsTo addr cblk nr /\ R blk cblk) /\
    (forall cblk, M.MapsTo addr cblk nr
       <-> exists blk, Lookup addr blk or /\ R blk cblk).

Ltac normalize :=
  repeat match goal with
  | [ H : M.find ?ADDR ?Z = Some ?CBLK |- _ ] => apply F.find_mapsto_iff in H
  | [ |-  M.find ?ADDR ?Z = Some ?CBLK ]      => apply F.find_mapsto_iff
  end.

Ltac reduction :=
  try repeat teardown; subst; normalize;
  repeat match goal with
  | [ R : ?A -> ?B -> Prop,
      H1 : Map_AbsR ?R ?X ?Y,
      H2 : Lookup ?ADDR ?BLK ?X |- _ ] =>
    let HA := fresh "HA" in
    let HB := fresh "HB" in
    let cblk := fresh "cblk" in
    destruct (proj1 (proj1 (H1 ADDR (* H *)) BLK) H2) as [cblk [HA HB]];
    clear H1 H2
  | [ R : ?A -> ?B -> Prop,
      H1 : Map_AbsR ?R ?X ?Y,
      H2 : M.MapsTo ?ADDR ?CBLK ?Y |- _ ] =>
    let HC := fresh "HC" in
    let HD := fresh "HD" in
    let blk := fresh "blk" in
    destruct (proj1 (proj2 (H1 ADDR (* H *)) CBLK) H2) as [blk [HC HD]];
    clear H1 H2
  end; auto.

Ltac related :=
  match goal with
  | [ R : ?A -> ?B -> Prop,
      cblk : ?B,
      H1 : ?R ?BLK ?CBLK |- exists b : ?B, _ /\ ?R ?BLK b ] =>
    exists CBLK; split; [| exact H1]
  | [ R : ?A -> ?B -> Prop,
      blk : ?A,
      H1 : ?R ?BLK ?CBLK |- exists a : ?A, _ /\ ?R a ?CBLK ] =>
    exists BLK; split; [| exact H1]
  end.

Ltac equalities :=
  normalize;
  repeat match goal with
  | [ H : ?X <> ?X |- _ ]            => contradiction H; reflexivity
  | [ |- ?X <> ?Y ]                  => unfold not; intros; subst
  | [ |- ?X = ?X ]                   => reflexivity
  | [ |- O.eq ?X ?X ]                => apply O.eq_refl
  | [ H : O.eq ?X ?Y |- _ ]          => rewrite !H in *; clear H
  | [ H : ~ O.eq ?X ?X |- _ ]        => contradiction H; apply O.eq_refl
  | [ H : O.eq ?X ?X -> False |- _ ] => contradiction H; apply O.eq_refl

  | [ H1 : Same ?X ?Y, _ : Map_AbsR _ ?Y _, H2 : Lookup _ _ ?X |- _ ] =>
      apply H1 in H2
  | [ H1 : Same ?X ?Y, _ : Map_AbsR _ ?Y _ |- Lookup _ _ ?X ] =>
      apply H1

  | [ H1 : Same ?X ?Y, _ : Map_AbsR _ ?X _, H2 : Lookup _ _ ?Y |- _ ] =>
      apply H1 in H2
  | [ H1 : Same ?X ?Y, _ : Map_AbsR _ ?X _ |- Lookup _ _ ?Y ] =>
      apply H1

  | [ H1 : M.Equal ?X ?Y, _ : Map_AbsR _ ?Y _, H2 : M.MapsTo _ _ ?X |- _ ] =>
      rewrite H1 in H2
  | [ H1 : M.Equal ?X ?Y, _ : Map_AbsR _ ?Y _ |- M.MapsTo _ _ ?X ] =>
      rewrite H1
  | [ H1 : M.Equal ?X ?Y, _ : Map_AbsR _ ?Y _
    |- exists _, M.MapsTo _ _ ?X /\ _ ] => rewrite H1

  | [ H1 : M.Equal ?X ?Y, _ : Map_AbsR _ ?X _, H2 : M.MapsTo _ _ ?Y |- _ ] =>
      rewrite <- H1 in H2
  | [ H1 : M.Equal ?X ?Y, _ : Map_AbsR _ ?X _ |- M.MapsTo _ _ ?Y ] =>
      rewrite <- H1
  | [ H1 : M.Equal ?X ?Y, _ : Map_AbsR _ ?X _
    |- exists _, M.MapsTo _ _ ?Y /\ _ ] => rewrite <- H1

  | [ Oeq_eq : forall x y : O.t, O.eq x y -> x = y,
      H1 : O.eq ?X ?Y |- _ ] => apply Oeq_eq in H1; subst
  end.

Ltac relational :=
  repeat match goal with
  | [ |- Map_AbsR _ _ _ ]  => split; intros; intuition
  | [ |- Proper _ _ ] => intros ???
  | [ |- Monotonic _ _ ] => intros ???
  | [ |- arrow_rel _ _ _ _ ] => intros ???
  | [ |- respectful _ _ _ _ ] => intros ???
  | [ |- iff _ _ ] => split; intro
  end.

Corollary Map_AbsR_Lookup_R `(R : A -> B -> Prop)
          (or : Ensemble (M.key * A)) (nr : M.t B) :
  Map_AbsR R or nr ->
  forall addr blk cblk,
    Lookup addr blk or -> R blk cblk -> M.MapsTo addr cblk nr.
Proof. intros; eapply H; eauto. Qed.

Hint Resolve Map_AbsR_Lookup_R.

Corollary Map_AbsR_find_R `(R : A -> B -> Prop)
          (or : Ensemble (M.key * A)) (nr : M.t B) :
  Map_AbsR R or nr ->
  forall addr blk cblk,
    M.MapsTo addr cblk nr -> R blk cblk -> Lookup addr blk or.
Proof. intros; eapply H; eauto. Qed.

Hint Resolve Map_AbsR_find_R.

Global Program Instance Map_AbsR_Proper :
  Proper (@Same _ _ ==> @M.Equal _ ==> iff) (@Map_AbsR A B R).
Obligation 1.
  relational; equalities.
  - reduction; related.
    rewrite <- H0; trivial.
  - reduction.
    rewrite <- H0 in H2; eauto.
  - rewrite <- H0 in H2.
    reduction; related.
    rewrite <- H; trivial.
  - reduction; equalities.
    rewrite <- H0; eauto.
  - reduction; related.
    rewrite H0; trivial.
  - reduction.
    rewrite H0 in H2; eauto.
  - rewrite H0 in H2.
    reduction; related.
    rewrite H; trivial.
  - reduction; equalities.
    rewrite H0; eauto.
Qed.

Section FunMaps_AbsR.

Variables A B : Type.
Variable R : (A -> B -> Prop).

Hypothesis Oeq_eq : forall x y, O.eq x y -> x = y.

Global Program Instance Empty_Map_AbsR : Empty [R Map_AbsR R] (M.empty _).
Obligation 1.
  relational; repeat teardown.
    inversion H.
  simplify_maps.
Qed.

Global Program Instance MapsTo_Map_AbsR :
  (@Lookup _ _) [R O.eq ==> R ==> Map_AbsR R ==> iff] (@M.MapsTo _).
Obligation 1. relational; equalities; eauto. Qed.

Global Program Instance Lookup_Map_AbsR :
  (@Lookup _ _) [R O.eq ==> R ==> Map_AbsR R ==> iff]
  (fun k e m => M.find k m = Some e).
Obligation 1. relational; equalities; eauto. Qed.

Global Program Instance Same_Map_AbsR :
  (@Same _ _) [R Map_AbsR R ==> Map_AbsR R ==> iff] M.Equal.
Obligation 1.
  relational.
    rewrite <- H1 in H0; clear H1.
    apply F.Equal_mapsto_iff; split; intros.
      apply H in H1; eapply H0; exact H1.
    apply H0 in H1; eapply H; exact H1.
  rewrite <- H1 in H0.
  split; intros.
    apply H in H2; eapply H0; exact H2.
  apply H0 in H2; eapply H; exact H2.
Qed.

Definition boolR (P : Prop) (b : bool) : Prop := P <-> b = true.

Global Program Instance Member_Map_AbsR :
  (@Member _ _) [R O.eq ==> Map_AbsR R ==> boolR] (@M.mem _).
Obligation 1.
  relational.
  equalities.
  split; intros.
    destruct H.
    reduction.
    rewrite F.mem_find_b.
    apply F.find_mapsto_iff in HA.
    rewrite HA.
    reflexivity.
  destruct (M.find (elt:=B) y y0) eqn:Heqe.
    reduction.
    exists blk.
    assumption.
  rewrite F.mem_find_b, Heqe in H.
  discriminate.
Qed.

Lemma has_Some : forall A B (a : option A) (b : B),
  a <> None -> exists b, a = Some b.
Proof.
  intros.
  destruct a.
    exists a; reflexivity.
  congruence.
Qed.

Lemma in_mapsto_iff : forall elt k m,
  M.In (elt:=elt) k m <-> exists e, M.MapsTo (elt:=elt) k e m.
Proof.
  split; intros.
    apply F.mem_in_iff in H.
    rewrite F.mem_find_b in H.
    destruct (M.find (elt:=elt) k m) eqn:Heqe.
      exists e.
      apply F.find_mapsto_iff.
      assumption.
    discriminate.
  apply F.mem_in_iff.
  rewrite F.mem_find_b.
  destruct H.
  apply F.find_mapsto_iff in H.
  rewrite H.
  reflexivity.
Qed.

Global Program Instance Member_In_Map_AbsR :
  (@Member _ _) [R O.eq ==> Map_AbsR R ==> iff] (@M.In _).
Obligation 1.
  relational; equalities.
    destruct H1.
    reduction.
    apply in_mapsto_iff; eauto.
  apply (proj1 (in_mapsto_iff _ _)) in H1.
  destruct H1.
  reduction.
  exists blk.
  assumption.
Qed.

(* Insert *)

Global Program Instance Remove_Map_AbsR :
  (@Remove _ _) [R O.eq ==> Map_AbsR R ==> Map_AbsR R] (@M.remove _).
Obligation 1.
  relational; equalities.
  - repeat teardown.
    reduction.
    related.
    simplify_maps.
    firstorder.
  - teardown.
      reduction.
      simplify_maps.
      eauto.
    reduction.
    simplify_maps.
    equalities.
  - simplify_maps.
    reduction.
    related.
    teardown.
    equalities.
  - simplify_maps.
    firstorder.
Qed.

Global Program Instance Update_Map_AbsR :
  (@Update _ _) [R O.eq ==> R ==> Map_AbsR R ==> Map_AbsR R] (@M.add _).
Obligation 1.
  relational; equalities.
  - repeat teardown; subst.
      related.
      simplify_maps.
      firstorder.
    reduction.
    related.
    simplify_maps.
    firstorder.
  - reduction.
    simplify_maps.
      equalities.
      left; intuition.
      admit.
    right.
    split; eauto.
    equalities.
  - simplify_maps.
      related.
      teardown.
      equalities.
      intuition.
    reduction.
    related.
    teardown.
    right.
    split; trivial.
    equalities.
  - repeat teardown; subst.
    simplify_maps.
      left; intuition.
      admit.
    simplify_maps.
    right.
    split; eauto.
Admitted.

Corollary Single_is_Update : forall (x : M.key) (y : A),
  Same (Single x y) (Update x y Empty).
Proof. split; intros; repeat teardown. Qed.

Global Program Instance Single_Map_AbsR :
  (@Single _ _) [R O.eq ==> R ==> Map_AbsR R] singleton.
Obligation 1.
  intros ??????.
  rewrite Single_is_Update.
  unfold singleton.
  apply Update_Map_AbsR; auto.
  apply Empty_Map_AbsR; auto.
Qed.

(* Move *)

Global Program Instance Map_Map_AbsR :
  (@Map _ _ _) [R (O.eq ==> R ==> R) ==> Map_AbsR R ==> Map_AbsR R]
  (@M.mapi _ _).
Obligation 1.
(*
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
    admit.
  - simplify_maps.
      simplify_maps.
      reduce_context.
      exists (x addr blk).
      split.
        teardown.
      apply H; trivial.
    intros; equalities.
*)
Admitted.

Global Program Instance Filter_Map_AbsR :
  (@Filter _ _) [R (O.eq ==> R ==> boolR) ==> Map_AbsR R ==> Map_AbsR R]
  (@P.filter _).
Obligation 1.
(*
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
*)
Admitted.

(* Define *)
(* Modify *)
(* Overlay *)

Global Program Instance All_Proper :
  Proper ((O.eq ==> eq ==> iff) ==> Same (B:=A) ==> iff) (All (B:=A)).
Obligation 1.
Admitted.

Global Program Instance for_all_Proper :
  Proper ((O.eq ==> eq ==> eq) ==> M.Equal ==> eq) (P.for_all (elt:=B)).
Obligation 1.
Admitted.

Global Program Instance All_Map_AbsR
       `{Hsym : Equivalence B Q}
       `{HQ : Proper _ (O.eq ==> Q ==> eq) f'} :
  f [R O.eq ==> R ==> boolR] f' ->
  All f [R Map_AbsR R ==> boolR] P.for_all f'.
Obligation 1.
(*
  unfold All, P.for_all in *.
    apply P.fold_rec_bis; intros; trivial; subst.
    apply F.find_mapsto_iff in H2.
    reduction.
    apply H1 in HC.
    eapply H in HC; eauto.
    rewrite HC; reflexivity.
  intros.
  reduction.
  eapply H; eauto.
  revert H1.
  revert HC.
  apply P.fold_rec; intros; subst; intuition.
    simplify_maps.
  rewrite H3 in HC.
  simplify_maps.
    rewrite <- H6.
    destruct (f' k cblk) eqn:Heqe; intuition.
  destruct (f' k e) eqn:Heqe; intuition.
Qed.
*)
Admitted.

Global Program Instance Any_Map_AbsR :
  (@Any _ _) [R (O.eq ==> R ==> boolR) ==> Map_AbsR R ==> boolR]
  (@P.exists_ _).
Obligation 1.
(*
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
*)
Admitted.

End FunMaps_AbsR.

Lemma Map_AbsR_impl :
  forall A B (R : A -> B -> Prop)
         `{HB : Equivalence B Q}
         `{HQ : Proper _ (equiv ==> equiv ==> iff)%signature Q}
         a b c,
    (forall a b c, R a b -> R a c -> Q b c)
      -> Map_AbsR R a b -> Map_AbsR R a c -> M.Equal b c.
Proof.
(*
  apply F.Equal_mapsto_iff; split; intros;
  apply F.find_mapsto_iff in H2;
  apply F.find_mapsto_iff.
    reduction; clear H0; reduction.
    pose proof (H _ _ _ HD HD0); subst.
    rewrite H0.
    assumption.
  reduction; clear H1; reduction.
  pose proof (forward_impl _ _ _ HD HD0); subst.
*)
Admitted.

End FunMaps.
