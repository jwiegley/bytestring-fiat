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

Global Program Instance Insert_Map_AbsR : forall k e e' r m,
  forall H : ~ Member k r, R e e' -> Map_AbsR R r m
    -> Insert k e r (not_ex_all_not _ _ H) [R Map_AbsR R] M.add k e' m.
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
      left; intuition.
      admit.
    right.
    split; eauto.
    equalities.
  - simplify_maps.
      related.
      teardown.
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
      left; intuition.
      admit.
    right.
    split; eauto.
    equalities.
  - simplify_maps.
      related.
      teardown.
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
  Proper (O.eq ==> eq ==> eq) f ->
  Proper (O.eq ==> eq ==> eq) f'
    -> f [R O.eq ==> R ==> R] f'
    -> (@Map _ _ _ f) [R Map_AbsR R ==> Map_AbsR R] (@M.mapi _ _ f').
Obligation 1.
  relational.
  - repeat teardown.
    reduction.
    exists (f' addr cblk).
    split.
      apply F.mapi_mapsto_iff; eauto; intros.
      rewrite H2.
      reflexivity.
    apply H1; auto.
  - teardown.
    reduction.
    apply F.mapi_mapsto_iff in H3.
      reduction.
      exists blk0.
      split; trivial.
      eapply (H1 addr) in HD; eauto.
      admit.
    intros.
    rewrite H6.
    reflexivity.
  - apply F.mapi_mapsto_iff in H3.
      reduction.
      exists (f addr blk).
      split; trivial.
        teardown.
        exists blk.
        intuition.
      apply H1; auto.
    intros.
    rewrite H5.
    reflexivity.
  - apply F.mapi_mapsto_iff; eauto; intros.
      rewrite H4.
      reflexivity.
    reduction.
    exists cblk0.
    split; trivial.
    eapply (H1 addr) in HB; eauto.
    admit.
Admitted.

Global Program Instance Filter_Map_AbsR :
  Proper (O.eq ==> eq ==> eq) f ->
  Proper (O.eq ==> eq ==> eq) f'
    -> f [R O.eq ==> R ==> boolR] f'
    -> (@Filter _ _ f) [R Map_AbsR R ==> Map_AbsR R] (@P.filter _ f').
Obligation 1.
  relational.
  - reduction.
    related.
    simplify_maps; auto.
    intuition.
    eapply H1; eauto.
  - reduction.
    simplify_maps; auto.
    reduction.
    intuition.
      admit.
    eapply H1; eauto.
  - simplify_maps; auto.
    reduction.
    related.
    teardown.
    intuition.
    eapply H1; eauto.
  - simplify_maps; auto.
    reduction.
    intuition.
      admit.
    eapply H1; eauto.
Admitted.

(* Define *)
(* Modify *)
(* Overlay *)

(* Global Program Instance All_Proper : *)
(*   Proper ((O.eq ==> eq ==> iff) ==> Same (B:=A) ==> iff) (All (B:=A)). *)
(* Obligation 1. *)

(* Global Program Instance for_all_Proper : *)
(*   Proper ((O.eq ==> eq ==> eq) ==> M.Equal ==> eq) (P.for_all (elt:=B)). *)
(* Obligation 1. *)

Global Program Instance All_Map_AbsR
       `{Hsym : Equivalence B Q}
       `{HQ : Proper _ (O.eq ==> Q ==> eq) f'} :
  f [R O.eq ==> R ==> boolR] f'
    -> All f [R Map_AbsR R ==> boolR] P.for_all f'.
Obligation 1.
  relational.
  unfold All, P.for_all in *.
  split; intros.
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
  revert HA.
  apply P.fold_rec; intros; subst; intuition.
    simplify_maps.
  apply add_equal_iff in H2.
  rewrite <- H2 in HA.
  simplify_maps.
    rewrite <- H5.
    destruct (f' k cblk) eqn:Heqe; intuition.
  destruct (f' k e) eqn:Heqe; intuition.
Qed.

Global Program Instance Any_Map_AbsR :
  (@Any _ _) [R (O.eq ==> R ==> boolR) ==> Map_AbsR R ==> boolR]
  (@P.exists_ _).
Obligation 1.
  relational.
  split; intros;
  unfold Any in *.
    apply P.exists_iff.
      intros ??????; subst; equalities.
    do 3 destruct H1.
    reduction.
    exists (x1, cblk).
    split; simpl.
      assumption.
    eapply H; eauto.
  apply P.exists_iff in H1.
    do 2 destruct H1.
    reduction.
    exists k.
    exists blk.
    split; trivial.
    eapply H; eauto.
  intros ??????; subst; equalities.
Qed.

End FunMaps_AbsR.

Lemma Map_AbsR_impl :
  forall A B (R : A -> B -> Prop) a b c,
    (forall a b c, R a b -> R a c -> b = c)
      -> Map_AbsR R a b -> Map_AbsR R a c -> M.Equal b c.
Proof.
  relational.
  intros.
  apply F.Equal_mapsto_iff; split; intros;
  reduction; reduction;
  pose proof (H _ _ _ HD HB); subst;
  assumption.
Qed.

Lemma Functional_Add : forall elt r k e,
  Functional (Ensembles.Add (M.key * elt) r (k, e))
    -> Functional r.
Proof.
  unfold Functional; intros.
  eapply H.
    left; exact H0.
  left; exact H1.
Qed.

Theorem every_finite_map_has_an_associated_fmap
        (Oeq_eq : forall x y, O.eq x y -> x = y) :
  forall A B (R : A -> B -> Prop) (r : Ensemble (M.key * A)),
    Finite _ r
      -> Functional r
      -> (forall k e, Lookup k e r -> exists e', R e e')
      -> exists m : M.t B, Map_AbsR R r m.
Proof.
  intros.
  induction H.
    exists (M.empty _).
    apply Empty_Map_AbsR.
  destruct x; simpl in *.
  unfold Functional in H0.
  destruct (IHFinite (Functional_Add H0)), (H1 k a).
  - right; constructor.
  - intros.
    eapply H1.
    left; exact H4.
  - right; constructor.
  - clear IHFinite H1.
    exists (M.add k x0 x).
    eapply Insert_Map_AbsR; eauto.
    Grab Existential Variables.
    unfold Member.
    apply all_not_not_ex.
    unfold not; intros.
    specialize (H0 k a (Union_intror _ _ _ _ (In_singleton _ _))
                     n (Union_introl (M.key * A) A0 _ _ H1)).
    subst.
    contradiction.
Qed.

End FunMaps.
