Require Import
  Here.FMapExt
  Here.Nomega
  Here.TupleEnsembles
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

Module E := FMapExt(O).
Include E.

Open Scope rel_scope.

Class DeterminingRelation {A B : Type} (R : A -> B -> Prop) := {
  R_injective  : forall a, exists b, R a b;
  R_surjective : forall b, exists a, R a b;
  A_determines_B : forall a b b', R a b -> R a b' -> b = b';
  B_determines_A : forall a a' b, R a b -> R a' b -> a = a'
}.

Arguments A_determines_B {A B} R {_ a b b'} _ _.
Arguments B_determines_A {A B} R {_ a a' b} _ _.

Definition Map_AbsR {A B : Type} (R : A -> B -> Prop)
           (or : Ensemble (M.key * A)) (nr : M.t B) : Prop :=
  forall addr blk cblk `{DeterminingRelation A B R},
    R blk cblk -> (Lookup addr blk or <-> M.find addr nr = Some cblk).

Ltac reduction :=
  try repeat teardown; subst;
  repeat match goal with
  | [ R : ?A -> ?B -> Prop,
      H : DeterminingRelation ?R,
      H1 : Map_AbsR ?R ?X ?Y,
      H2 : Lookup ?ADDR ?BLK ?X,
      H3 : ?R ?BLK ?CBLK |- _ ] =>
    apply (H1 ADDR BLK CBLK H H3) in H2; clear H1
  | [ R : ?A -> ?B -> Prop,
      H : DeterminingRelation ?R,
      H1 : Map_AbsR ?R ?X ?Y,
      H2 : Lookup ?ADDR ?BLK ?X |- _ ] =>
    let cblk := fresh "cblk" in
    destruct (R_injective BLK) as [cblk ?]
  | [ H1 : Map_AbsR ?R ?X ?Y,
      H2 : Lookup ?ADDR ?BLK ?Z,
      H3 : Same ?X ?Z |- _ ] =>
    apply H3 in H2
  | [ H1 : Map_AbsR ?R ?X ?Y,
      H2 : Lookup ?ADDR ?BLK ?Z,
      H3 : Same ?Z ?X |- _ ] =>
    apply H3 in H2
  | [ R : ?A -> ?B -> Prop,
      H : DeterminingRelation ?R,
      H1 : Map_AbsR ?R ?X ?Y,
      H2 : M.find ?ADDR ?Y = Some ?CBLK,
      H3 : ?R ?BLK ?CBLK |- _ ] =>
    apply (H1 ADDR BLK CBLK H H3) in H2; clear H1
  | [ R : ?A -> ?B -> Prop,
      H : DeterminingRelation ?R,
      H1 : Map_AbsR ?R ?X ?Y,
      H2 : M.find ?ADDR ?Y = Some ?CBLK |- _ ] =>
    let cblk := fresh "cblk" in
    destruct (R_surjective CBLK) as [blk ?]
  | [ H1 : Map_AbsR ?R ?X ?Y,
      H2 : M.find ?ADDR ?Z = Some ?CBLK,
      H3 : M.Equal ?Y ?Z |- _ ] =>
    rewrite <- H3 in H2
  | [ H1 : Map_AbsR ?R ?X ?Y,
      H2 : M.find ?ADDR ?Z = Some ?CBLK,
      H3 : M.Equal ?Z ?Y |- _ ] =>
    rewrite H3 in H2
  | [ R : ?A -> ?B -> Prop,
      H : DeterminingRelation ?R,
      H1 : Map_AbsR ?R ?X ?Y,
      H2 : M.MapsTo ?ADDR ?CBLK ?Y,
      H3 : ?R ?BLK ?CBLK |- _ ] =>
    apply F.find_mapsto_iff in H2;
    apply (H1 ADDR BLK CBLK H H3) in H2; clear H1
  | [ R : ?A -> ?B -> Prop,
      H : DeterminingRelation ?R,
      H1 : Map_AbsR ?R ?X ?Y,
      H2 : M.MapsTo ?ADDR ?CBLK ?Y |- _ ] =>
    let cblk := fresh "cblk" in
    destruct (R_surjective CBLK) as [blk ?]
  | [ H1 : Map_AbsR ?R ?X ?Y,
      H2 : M.MapsTo ?ADDR ?CBLK ?Z,
      H3 : M.Equal ?Y ?Z |- _ ] =>
    apply F.find_mapsto_iff in H2;
    rewrite <- H3 in H2
  | [ H1 : Map_AbsR ?R ?X ?Y,
      H2 : M.MapsTo ?ADDR ?CBLK ?Z,
      H3 : M.Equal ?Z ?Y |- _ ] =>
    apply F.find_mapsto_iff in H2;
    rewrite H3 in H2
  end; auto.

(*
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
*)

Ltac equalities :=
  match goal with
  | [ H : ?X <> ?X |- _ ]            => contradiction H; reflexivity
  | [ |- ?X <> ?Y ]                  => unfold not; intros; subst
  | [ |- ?X = ?X ]                   => reflexivity
  | [ |- O.eq ?X ?X ]                => apply O.eq_refl
  | [ H : O.eq ?X ?Y |- _ ]          => rewrite !H in *; clear H
  | [ H : ~ O.eq ?X ?X |- _ ]        => contradiction H; apply O.eq_refl
  | [ H : O.eq ?X ?X -> False |- _ ] => contradiction H; apply O.eq_refl
  end.

Ltac determined R :=
  match goal with
  | [ H1 : R ?X ?Y, H2 : R ?X ?Z |- _ ] =>
    pose proof (A_determines_B R H1 H2); subst
  | [ H1 : R ?X ?Z, H2 : R ?Y ?Z |- _ ] =>
    pose proof (B_determines_A R H1 H2); subst
  end.

Ltac relational :=
  repeat match goal with
  | [ |- Map_AbsR _ _ _ ]  => split; intros; intuition
  | [ |- Proper _ _ ] => intros ???
  | [ |- Monotonic _ _ ] => intros ???
  | [ |- arrow_rel _ _ _ _ ] => intros ???
  | [ |- respectful _ _ _ _ ] => intros ???
  | [ |- iff _ _ ] => split; intro
  end;
  try equalities;
  repeat teardown; subst;
  try equalities;
  try simplify_maps; subst;
  try equalities; subst;
  try simplify_maps; subst;
  auto.

Global Program Instance Map_AbsR_Proper :
  Proper (@Same _ _ ==> @M.Equal _ ==> iff) (@Map_AbsR A B R).
Obligation 1.
  relational;
  match goal with
  | [ H1 : Same ?X ?Y, H2 : Lookup _ _ ?Y |- _ ] => apply H1 in H2
  | [ H  : Same ?X ?Y    |- Lookup _ _ ?Y ]      => apply H
  | [ H1 : Same ?X ?Y, H2 : Lookup _ _ ?X |- _ ] => apply H1 in H2
  | [ H  : Same ?X ?Y    |- Lookup _ _ ?X ]      => apply H
  end;
  match goal with
  | [ H1 : M.Equal ?X ?Y, H2 : M.find _ ?Y = _ |- _ ] => rewrite <- H1 in H2
  | [ H  : M.Equal ?X ?Y    |- M.find _ ?Y = _ ]      => rewrite <- H
  | [ H1 : M.Equal ?X ?Y, H2 : M.find _ ?X = _ |- _ ] => rewrite H1 in H2
  | [ H  : M.Equal ?X ?Y    |- M.find _ ?X = _ ]      => rewrite H
  end;
  reduction.
(*
  - apply H2 in H5; reduction.
      rewrite <- H3; assumption.
    eapply H1 in HC0; eauto.
  - rewrite <- H3 in H5; reduction.
      apply H2 in HC; assumption.
    eapply H1 in HD; eauto.
  - apply H2 in H5; reduction.
      rewrite H3; assumption.
    eapply H1 in HC0; eauto.
  - rewrite H3 in H5; reduction.
      apply H2; assumption.
    eapply H1 in HD; eauto.
*)
Qed.

(*
Corollary Map_AbsR_Lookup {A B} (R : A -> B -> Prop)
          (or : Ensemble (M.key * A)) (nr : M.t B) :
  Map_AbsR R or nr ->
  forall addr blk,
    Lookup addr blk or ->
      exists cblk, M.find addr nr = Some cblk /\ R blk cblk.
Proof. intros; reduction. Qed.

Definition optionR {A} (R : relation A) (mx my : option A) : Prop :=
  match mx, my with
  | Some x, Some y => R x y
  | None, None => True
  | _, _ => False
  end.

Global Program Instance Some_Q_Proper `{Reflexive B Q} :
  Proper (Q ==> optionR Q) Some.
Obligation 1.
  intros ???.
  unfold optionR.
  assumption.
Qed.
*)

Global Program Instance MapsTo_Proper :
  Proper (O.eq ==> @eq B ==> M.Equal ==> iff) (@M.MapsTo _).
Obligation 1. relational; rewrite H1 in *; assumption. Qed.

Global Program Instance find_iff_Proper :
  Proper (O.eq ==> eq ==> M.Equal ==> iff)
         (fun k e m => @M.find B k m = Some e).
Obligation 1. relational; rewrite H1 in *; assumption. Qed.

Lemma Oeq_neq_sym : forall x y, ~ O.eq x y -> ~ O.eq y x.
Proof.
  intros.
  unfold not; intros.
  rewrite H0 in H.
  contradiction H.
  apply O.eq_refl.
Qed.

Hint Resolve Oeq_neq_sym.

Lemma Proper_Oeq_negb : forall B f,
  Proper (O.eq ==> eq ==> eq) f ->
  Proper (O.eq ==> eq ==> eq) (fun (k : M.key) (e : B) => negb (f k e)).
Proof. intros; relational. Qed.

Hint Resolve Proper_Oeq_negb.

Section FunMaps_AbsR.

Variables A B : Type.
Variable R : (A -> B -> Prop).
Context `{DeterminingRelation A B R}.

Hypothesis Oeq_eq : forall x y, O.eq x y -> x = y.

Global Program Instance Empty_Map_AbsR : Empty [R Map_AbsR R] (M.empty _).
Obligation 1. relational. Qed.

Global Program Instance Single_Map_AbsR :
  (@Single _ _) [R O.eq ==> R ==> Map_AbsR R] singleton.
Obligation 1.
  relational; determined R; try apply F.add_eq_o; auto.
(*
  intros ??????.
  split; intros;
  [exists y0|exists x0].
    repeat teardown.
    rewrite <- H, H1.
    split; trivial.
      rewrite F.elements_o; simpl.
      rewrite eqb_refl; trivial.
    rewrite H2; assumption.
  unfold singleton in H1.
  rewrite <- H in H1.
  destruct (O.eq_dec addr x).
    rewrite <- e in H1.
    apply Oeq_eq in e; subst.
    simplify_maps.
      intuition.
      apply Lookup_Single; trivial.
    equalities.
  simplify_maps.
    symmetry in H2.
    contradiction.
  inversion H5.
*)
Qed.

(*
Corollary Map_AbsR_Lookup_R (or : Ensemble (M.key * A)) (nr : M.t B) :
  Map_AbsR R or nr ->
  forall addr blk cblk,
    Lookup addr blk or -> R blk cblk -> M.find addr nr = Some cblk.
Proof.
  intros.
  reduction.
Admitted.

Corollary Map_AbsR_find_R (or : Ensemble (M.key * A)) (nr : M.t B) :
  Map_AbsR R or nr ->
  forall addr blk cblk,
    M.find addr nr = Some cblk -> R blk cblk -> Lookup addr blk or.
Proof.
  intros.
  reduction.
Admitted.
*)

Global Program Instance MapsTo_Map_AbsR :
  (@Lookup _ _) [R O.eq ==> R ==> Map_AbsR R ==> iff] (@M.MapsTo _).
Obligation 1.
  relational.
    reduction.
    rewrite <- H0.
    apply F.find_mapsto_iff.
    assumption.
  rewrite <- H0 in H3.
  reduction.
(*
Global Program Instance Lookup_Map_AbsR :
  (@Lookup _ _) [R O.eq ===> R ===> Map_AbsR R ===> iff]
  (fun k e m => M.find k m = Some e).
Obligation 1.
  intros ?????????.
  split; intros.
    rewrite <- H.
    eapply Map_AbsR_Lookup_R; eauto.
  rewrite <- H in H2.
  eapply Map_AbsR_find_R; eauto.
*)
Qed.

Global Program Instance Same_Map_AbsR :
  (@Same _ _) [R Map_AbsR R ==> Map_AbsR R ==> iff] M.Equal.
Obligation 1.
  relational.
    apply F.Equal_mapsto_iff; split; intros;
    apply F.find_mapsto_iff;
    reduction.
  split; intros; reduction.
Qed.

Definition boolR (P : Prop) (b : bool) : Prop := P <-> b = true.

Global Program Instance Member_Map_AbsR :
  (@Member _ _) [R O.eq ==> Map_AbsR R ==> boolR] (@M.mem _).
Obligation 1.
  relational.
  split; intros.
    rewrite <- H0.
    unfold Member in H2.
    destruct H2.
    reduction.
    rewrite F.mem_find_b, H2.
    reflexivity.
(*
  split; intros; equalities.
    reduction.
    rewrite HC.
    reflexivity.
  destruct (M.find (elt:=B) y y0) eqn:Heqe.
    reduction.
    exists blk.
    assumption.
  discriminate.
*)
Admitted.

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
  unfold Member; intros ??????.
(*
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
*)
Admitted.

(* Insert *)

Global Program Instance Remove_Map_AbsR :
  (@Remove _ _) [R O.eq ==> Map_AbsR R ==> Map_AbsR R] (@M.remove _).
Obligation 1.
  intros ??????.
  split; intros.
(*
  - reduction; equalities.
    apply Oeq_neq_sym in H1.
    rewrite F.remove_neq_o; trivial.
  - simplify_maps; reduction.
    teardown; equalities.
*)
Admitted.

Global Program Instance Update_Map_AbsR :
  (@Update _ _) [R O.eq ==> R ==> Map_AbsR R ==> Map_AbsR R] (@M.add _).
Obligation 1.
  intros ?????????.
(*
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
*)
Admitted.

(* Move *)

Global Program Instance Map_Map_AbsR :
  (@Map _ _) [R (O.eq ==> R ==> R) ==> Map_AbsR R ==> Map_AbsR R]
  (@M.mapi _ _).
Obligation 1.
  intros ??????.
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
  intros ??????.
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
  intros ???; split; intros.
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
  intros ??????.
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
  intros.
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
