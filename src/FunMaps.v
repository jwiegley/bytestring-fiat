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

Lemma MapsTo_fun : forall (elt:Type) m x `{Equivalence elt R} (e e':elt),
  M.MapsTo x e m -> M.MapsTo x e' m -> R e e'.
Proof.
intros.
generalize (M.find_1 H0) (M.find_1 H1); clear H0 H1.
intros.
rewrite H0 in H1; injection H1; intros; subst.
reflexivity.
Qed.

Lemma add_mapsto_iff' : forall elt m x y `{Equivalence elt R} e e',
  Proper (O.eq ==> R ==> M.Equal ==> iff) (@M.MapsTo _) ->
  M.MapsTo y e' (M.add x e m) <->
     (O.eq x y /\ R e e') \/
     (~O.eq x y /\ M.MapsTo y e' m).
Proof.
  intros.
  intuition.
  - destruct (O.eq_dec x y); [left|right];
    simplify_maps; intuition.
  - rewrite <- H3.
    simplify_maps; intuition.
  - simplify_maps; intuition.
Qed.

Lemma Proper_Oeq_negb : forall B f,
  Proper (O.eq ==> eq ==> eq) f ->
  Proper (O.eq ==> eq ==> eq) (fun (k : M.key) (e : B) => negb (f k e)).
Proof. intros ?????????; f_equal; subst; rewrite H0; reflexivity. Qed.

Hint Resolve Proper_Oeq_negb.

Open Scope rel_scope.

Class DeterminingRelation `(P : relation A) `(Q : relation B)
      (R : A -> B -> Prop) := {
  P_Equivalence :> Equivalence P;
  Q_Equivalence :> Equivalence Q;
  P_Lookup_Proper
    :> Proper (O.eq ==> P ==> @Same _ _ ==> iff) (@Lookup M.key A);
  Q_MapsTo_Proper :> Proper (O.eq ==> Q ==> M.Equal ==> iff) (@M.MapsTo B);
  A_determines_B : forall a b b', R a b -> R a b' -> Q b b';
  B_determines_A : forall a a' b, R a b -> R a' b -> P a a'
}.

Arguments DeterminingRelation {A} P {B} Q R.
Arguments A_determines_B {A} P {B} Q R {_ a b b'} _ _.
Arguments B_determines_A {A} P {B} Q R {_ a a' b} _ _.

Definition Map_AbsR `(P : relation A) `(Q : relation B) (R : A -> B -> Prop)
           (or : Ensemble (M.key * A)) (nr : M.t B) : Prop :=
  forall addr `{DeterminingRelation _ P _ Q R},
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
      H : DeterminingRelation ?R _ _,
      H1 : Map_AbsR ?R ?X ?Y,
      H2 : Lookup ?ADDR ?BLK ?X |- _ ] =>
    let HA := fresh "HA" in
    let HB := fresh "HB" in
    let cblk := fresh "cblk" in
    destruct (proj1 (proj1 (H1 ADDR H) BLK) H2) as [cblk [HA HB]];
    clear H1 H2
  | [ R : ?A -> ?B -> Prop,
      H : DeterminingRelation ?R _ _,
      H1 : Map_AbsR ?R ?X ?Y,
      H2 : M.MapsTo ?ADDR ?CBLK ?Y |- _ ] =>
    let HC := fresh "HC" in
    let HD := fresh "HD" in
    let blk := fresh "blk" in
    destruct (proj1 (proj2 (H1 ADDR H) CBLK) H2) as [blk [HC HD]];
    clear H1 H2
  end; auto.

Ltac related :=
  match goal with
  | [ R : ?A -> ?B -> Prop,
      H : DeterminingRelation ?R _ _,
      cblk : ?B,
      H1 : ?R ?BLK ?CBLK |- exists b : ?B, _ /\ ?R ?BLK b ] =>
    exists CBLK; split; [| exact H1]
  | [ R : ?A -> ?B -> Prop,
      H : DeterminingRelation ?R _ _,
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

Ltac determined R :=
  match goal with
  | [ H1 : R ?X ?Y, H2 : R ?X ?Z |- _ ] =>
    pose proof (A_determines_B R _ _ H1 H2); subst
  | [ H1 : R ?X ?Z, H2 : R ?Y ?Z |- _ ] =>
    pose proof (B_determines_A R _ _ H1 H2); subst
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

Instance Map_AbsR_DeterminingRelation
        `(P : relation A) `(Q : relation B) (R : A -> B -> Prop) :
  DeterminingRelation (@Same M.key A) M.Equal (@Map_AbsR A P B Q R).
Proof.
  intros.
  constructor.
  - apply Same_Equivalence.
  - apply F.EqualSetoid.
  - relational'.
    apply H2.
    rewrite <- H0.
Obligation 1.
  relational.
  destruct H1.
  rewrite H2 in H5.
  apply H3 in H4.
Obligation 1.
  apply F.Equal_mapsto_iff;
  split; intros; reduction.
  eapply H2 in H4; trivial.
  do 2 destruct H4.
  eapply H3 in H4; trivial.
  do 2 destruct H4.
  rewrite <- H5.
  determined R.
Qed.
Obligation 2.
  split; intros; reduction;
  determined R; assumption.
Qed.

Global Program Instance Map_AbsR_Proper :
  Proper (@Same _ _ ==> @M.Equal _ ==> iff) (@Map_AbsR A B R).
Obligation 1.
  relational; equalities; reduction;
  first [ rewrite <- H0 in * | rewrite H0 in * ];
  try related; reduction;
  try determined R; auto;
  related; apply H; auto.
Qed.

Section FunMaps_AbsR.

Variables A B : Type.
Variable R : (A -> B -> Prop).
Context `{DeterminingRelation A B R eq eq}.

Hypothesis Oeq_eq : forall x y, O.eq x y -> x = y.

Global Program Instance Empty_Map_AbsR : Empty [R Map_AbsR R] (M.empty _).
Obligation 1. relational; inversion H1. Qed.

Global Program Instance Single_Map_AbsR :
  (@Single _ _) [R O.eq ==> R ==> Map_AbsR R] singleton.
Obligation 1.
  unfold singleton.
  relational.
  - related; simplify_maps; intuition.
  - determined R; reflexivity.
  - related; teardown.
  - determined R; intuition.
Qed.

Corollary Map_AbsR_Lookup_R (or : Ensemble (M.key * A)) (nr : M.t B) :
  Map_AbsR R or nr ->
  forall addr blk cblk,
    Lookup addr blk or -> R blk cblk -> M.MapsTo addr cblk nr.
Proof. intros; eapply H0; eauto. Qed.

Corollary Map_AbsR_find_R (or : Ensemble (M.key * A)) (nr : M.t B) :
  Map_AbsR R or nr ->
  forall addr blk cblk,
    M.MapsTo addr cblk nr -> R blk cblk -> Lookup addr blk or.
Proof. intros; eapply H0; eauto. Qed.

Global Program Instance MapsTo_Map_AbsR :
  (@Lookup _ _) [R O.eq ==> R ==> Map_AbsR R ==> iff] (@M.MapsTo _).
Obligation 1. relational; reduction; determined R; assumption. Qed.

Global Program Instance Lookup_Map_AbsR :
  (@Lookup _ _) [R O.eq ==> R ==> Map_AbsR R ==> iff]
  (fun k e m => M.find k m = Some e).
Obligation 1. relational; reduction; determined R; assumption. Qed.

Global Program Instance Same_Map_AbsR :
  (@Same _ _) [R Map_AbsR R ==> Map_AbsR R ==> iff] M.Equal.
Obligation 1.
  relational.
    rewrite H2 in H0; clear H2;
    apply F.Equal_mapsto_iff; split; intros;
    reduction;
    determined R;
    reduction.
  split; intros; reduction;
  [ rewrite H2 in HA | rewrite <- H2 in HA ];
  reduction;
  determined R;
  assumption.
Qed.

Definition boolR (P : Prop) (b : bool) : Prop := P <-> b = true.

Global Program Instance Member_Map_AbsR :
  (@Member _ _) [R O.eq ==> Map_AbsR R ==> boolR] (@M.mem _).
Obligation 1.
  relational.
  split; intros.
    destruct H0.
    reduction.
    rewrite F.mem_find_b.
    apply F.find_mapsto_iff in HA.
    rewrite HA.
    reflexivity.
  destruct (M.find (elt:=B) y y0) eqn:Heqe.
    reduction.
    exists blk.
    assumption.
  rewrite F.mem_find_b in H0.
  rewrite Heqe in H0.
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
    apply F.mem_in_iff in H0.
    rewrite F.mem_find_b in H0.
    destruct (M.find (elt:=elt) k m) eqn:Heqe.
      exists e.
      apply F.find_mapsto_iff.
      assumption.
    discriminate.
  apply F.mem_in_iff.
  rewrite F.mem_find_b.
  destruct H0.
  apply F.find_mapsto_iff in H0.
  rewrite H0.
  reflexivity.
Qed.

Global Program Instance Member_In_Map_AbsR :
  (@Member _ _) [R O.eq ==> Map_AbsR R ==> iff] (@M.In _).
Obligation 1.
  relational.
    destruct H2.
    reduction.
    apply in_mapsto_iff; eauto.
  apply (proj1 (in_mapsto_iff _ _)) in H2.
  destruct H2.
  reduction.
  exists blk.
  assumption.
Qed.

(* Insert *)

Global Program Instance Remove_Map_AbsR :
  (@Remove _ _) [R O.eq ==> Map_AbsR R ==> Map_AbsR R] (@M.remove _).
Obligation 1.
  relational; reduction.
  - related.
    simplify_maps.
    firstorder.
  - determined R.
    assumption.
  - related.
    teardown.
    equalities.
  - determined R.
    firstorder.
Qed.

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
