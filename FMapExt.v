Require Import
  Coq.FSets.FMapList
  Coq.FSets.FMapFacts
  Coq.Structures.OrderedTypeEx.

Lemma fold_right_filter : forall A B (f : A -> B -> B) z P l,
  fold_right f z (filter P l) =
  fold_right (fun x rest => if P x then f x rest else rest) z l.
Proof.
  intros.
  induction l; simpl; trivial.
  rewrite <- IHl; clear IHl.
  destruct (P a); reflexivity.
Qed.

Module FMapExt (O : OrderedType).

Module M := FMapList.Make(O).
Module P := FMapFacts.Properties M.
Module F := P.F.

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

Section for_all.

Variable elt : Type.
Variable P : M.key -> elt -> bool.
Variable P_Proper : Proper (O.eq ==> eq ==> eq) P.

Lemma for_all_empty : P.for_all P (M.empty elt) = true.
Proof.
  intros.
  apply P.for_all_iff; trivial.
  intros.
  apply F.empty_mapsto_iff in H.
  contradiction.
Qed.

Lemma for_all_add : forall (m : M.t elt) (k : M.key) v,
  P.for_all P m = true
    -> (forall x y, O.eq x y -> x = y)
    -> P k v = true
    -> P.for_all P (M.add k v m) = true.
Proof.
  intros.
  apply P.for_all_iff; trivial.
  intros.
  apply F.add_mapsto_iff in H2.
  destruct H2; destruct H2.
    apply H0 in H2.
    subst.
    exact H1.
  eapply P.for_all_iff in H3.
  - exact H3.
  - exact P_Proper.
  - exact H.
Qed.

Lemma for_all_remove : forall (m : M.t elt) (k : M.key),
  P.for_all P m = true
    -> P.for_all P (M.remove k m) = true.
Proof.
  intros.
  apply P.for_all_iff; trivial.
  intros.
  apply F.remove_mapsto_iff in H0.
  eapply P.for_all_iff in H.
  - exact H.
  - exact P_Proper.
  - tauto.
Qed.

Lemma mapi_empty :
  forall (f : M.key -> elt -> elt),
    Proper (O.eq ==> eq ==> eq) f
      -> M.Equal (M.mapi f (M.empty elt)) (M.empty elt).
Proof.
  intros f k H.
  rewrite F.mapi_o, F.empty_o; trivial.
  intros.
  rewrite H0.
  reflexivity.
Qed.

Lemma fold_Some (m : list (M.key * elt))
      A (z : A) (f : M.key * elt -> option A) :
  List.fold_left (fun (x : option A) (k : M.key * elt) =>
                    match x with
                    | Some _ => x
                    | None => f k
                    end) m (Some z) = Some z.
Proof.
  induction m; simpl; intros.
    reflexivity.
  rewrite IHm.
  reflexivity.
Qed.

Lemma fold_Some_cons (m : list (M.key * elt))
      A (z : A) y (f : M.key * elt -> option A) :
  List.fold_left (fun (x : option A) (k : M.key * elt) =>
                    match x with
                    | Some _ => x
                    | None => f k
                    end) (y :: m) None =
  match f y with
  | Some x => Some x
  | None =>
    List.fold_left (fun (x : option A) (k : M.key * elt) =>
                      match x with
                      | Some _ => x
                      | None => f k
                      end) m None
  end.
Proof.
  induction m; simpl; intros.
    destruct (f y); reflexivity.
  destruct (f y); simpl.
    rewrite fold_Some; reflexivity.
  reflexivity.
Qed.

Definition build_map_left (x : M.t elt) (k : M.key * elt) :=
  if P (fst k) (snd k)
  then M.add (fst k) (snd k) x
  else x.

Global Program Instance build_map_left_Proper :
  Proper (M.Equal ==> (fun p p' => O.eq (fst p) (fst p') /\ snd p = snd p')
                  ==> M.Equal) build_map_left.
Obligation 1.
  intros ???????.
  unfold build_map_left.
  destruct x0, y0; simpl in *.
  destruct H0; subst.
  rewrite H0.
  destruct (P t0 e0).
    rewrite H0, H.
    reflexivity.
  rewrite H.
  reflexivity.
Qed.

Definition build_map_right (k : M.key * elt) (x : M.t elt) :=
  if P (fst k) (snd k)
  then M.add (fst k) (snd k) x
  else x.

Global Program Instance build_map_right_Proper :
  Proper ((fun p p' => O.eq (fst p) (fst p') /\ snd p = snd p')
            ==> M.Equal ==> M.Equal) build_map_right.
Obligation 1.
  intros ???????.
  unfold build_map_right.
  destruct x, y; simpl in *.
  destruct H; subst.
  rewrite H.
  destruct (P t0 e0).
    rewrite H0, H.
    reflexivity.
  rewrite H0.
  reflexivity.
Qed.

Global Program Instance fold_left_Equal_Proper (m : list (M.key * elt)) :
  Proper (M.Equal ==> M.Equal) (fold_left build_map_left m).
Obligation 1.
  intros ???; subst.
  generalize dependent x.
  generalize dependent y.
  induction m; simpl; trivial.
  destruct a; simpl.
  destruct (P k e); simpl; intros;
  apply IHm;
  rewrite H;
  reflexivity.
Qed.

Require Import Coq.Sorting.Permutation.

Theorem add_transitive
        (k : M.key) (e : elt)
        (k0 : M.key) (e0 : elt)
        (z : M.t elt) :
  (O.eq k k0 -> e = e0)
    -> M.Equal (M.add k e (M.add k0 e0 z)) (M.add k0 e0 (M.add k e z)).
Proof.
  intros H addr.
  rewrite !F.add_o.
  destruct (O.eq_dec k addr);
  destruct (O.eq_dec k0 addr); eauto.
  apply O.eq_sym in e2.
  pose proof (O.eq_trans e1 e2).
  rewrite (H H0).
  reflexivity.
Qed.

Lemma fold_add_cons (m : list (M.key * elt)) (z : M.t elt) y :
  (forall k e, O.eq k (fst y) -> e = snd y) ->
  M.Equal
    (List.fold_left
       (fun (x : M.t elt) (k : M.key * elt) =>
          if P (fst k) (snd k) then M.add (fst k) (snd k) x else x)
       (y :: m) z)
    (if P (fst y) (snd y)
     then M.add (fst y) (snd y)
                (List.fold_left
                   (fun (x : M.t elt) (k : M.key * elt) =>
                      if P (fst k) (snd k) then M.add (fst k) (snd k) x else x)
                   m z)
     else List.fold_left
            (fun (x : M.t elt) (k : M.key * elt) =>
               if P (fst k) (snd k) then M.add (fst k) (snd k) x else x)
            m z).
Proof.
  intros.
  destruct y as [k e]; simpl in *.
  destruct (P k e); simpl.
    generalize dependent z.
    generalize dependent e.
    generalize dependent k.
    induction m; simpl.
      reflexivity.
    destruct a; simpl; intros.
    rewrite <- IHm; clear IHm.
      destruct (P k e); simpl.
        apply fold_left_Equal_Proper, add_transitive.
        apply H.
      reflexivity.
    apply H.
  reflexivity.
Qed.

Lemma for_all_mapi :
  forall elt' (m : M.t elt') (k : M.key)
         (f : M.key -> elt' -> elt),
    Proper (O.eq ==> eq ==> eq) f
      -> P.for_all P (M.mapi f m) = true
      <-> P.for_all (fun k e => P k (f k e)) m = true.
Proof.
Abort.

Lemma for_all_impl : forall (P' : M.key -> elt -> bool) m,
  P.for_all P m = true
    -> Proper (O.eq ==> eq ==> eq) P'
    -> (forall k e, P k e = true -> P' k e = true)
    -> P.for_all P' m = true.
Proof.
  intros.
  apply P.for_all_iff; trivial.
  intros.
  eapply P.for_all_iff in H; eauto.
Qed.

End for_all.

Import ListNotations.

Definition find_if {elt} (f : M.key -> elt -> bool) (m : M.t elt) :
  option (M.key * elt) :=
  M.fold (fun (k : M.key) (e : elt) x =>
            match x with
            | Some _ => x
            | None => if f k e then Some (k, e) else None
            end) m None.

Lemma find_if_empty : forall elt (P : M.key -> elt -> bool) m,
  M.Empty m -> find_if P m = None.
Proof.
  intros.
  unfold find_if.
  apply P.fold_rec; auto; intros.
  apply P.elements_Empty in H.
  apply F.find_mapsto_iff in H0.
  rewrite F.elements_o in H0.
  rewrite H in H0.
  inversion H0.
Qed.

Lemma add_equal_iff : forall elt k (e : elt) m1 m2,
  P.Add k e m1 m2 <-> M.Equal (M.add k e m1) m2.
Proof.
  split; intros; intro addr;
  specialize (H addr);
  congruence.
Qed.

Global Program Instance fold_Proper {elt A} : forall f,
  Proper (O.eq ==> @eq elt ==> @eq A ==> @eq A) f
    -> P.transpose_neqkey eq f
    -> Proper (M.Equal (elt:=elt) ==> @eq A ==> @eq A)
              (@M.fold elt A f).
Obligation 1.
  intros ??????; subst.
  revert H1.
  revert y.
  apply P.fold_rec; intros.
    rewrite P.fold_Empty; auto.
    rewrite <- H2.
    assumption.
  rewrite P.fold_Add; eauto.
    apply H; auto.
    apply H4; reflexivity.
  congruence.
Qed.

Global Program Instance filter_Proper {elt} : forall P,
  Proper (O.eq ==> eq ==> eq) P
    -> Proper (M.Equal (elt:=elt) ==> M.Equal) (@P.filter elt P).
Obligation 1.
  intros ???; subst.
  unfold P.filter at 1.
  generalize dependent y.
  apply P.fold_rec; intros.
    apply F.Equal_mapsto_iff.
    split; intros.
      inversion H2.
    apply P.filter_iff in H2; auto.
    destruct H2.
    rewrite <- H1 in H2.
    apply P.elements_Empty in H0.
    apply F.find_mapsto_iff in H2.
    rewrite F.elements_o in H2.
    rewrite H0 in H2.
    inversion H2.
  specialize (H3 m' (F.Equal_refl _)).
  apply add_equal_iff in H2.
  rewrite <- H2 in H4; clear H2 m'' H0.
  destruct (P k e) eqn:Heqe; rewrite H3; clear H3.
    apply F.Equal_mapsto_iff.
    split; intros.
      apply P.filter_iff; auto.
      apply F.find_mapsto_iff in H0.
      simplify_maps.
        rewrite <- H4, H2.
        intuition.
          apply F.find_mapsto_iff.
          rewrite F.add_eq_o; auto.
        rewrite <- H2.
        assumption.
      apply F.find_mapsto_iff in H6.
      apply P.filter_iff in H6; auto.
      rewrite <- H4.
      intuition.
      apply F.find_mapsto_iff.
      rewrite F.add_neq_o; auto.
      apply F.find_mapsto_iff.
      assumption.
    apply P.filter_iff in H0; auto.
    destruct H0.
    rewrite <- H4 in H0.
    apply F.find_mapsto_iff in H0.
    simplify_maps.
      rewrite H3.
      apply F.find_mapsto_iff.
      rewrite F.add_eq_o; auto.
    apply F.find_mapsto_iff.
    rewrite F.add_neq_o; auto.
    apply F.find_mapsto_iff.
    apply P.filter_iff; auto.
    apply F.find_mapsto_iff in H7.
    intuition.
  apply F.Equal_mapsto_iff.
  split; intros;
  apply P.filter_iff in H0; auto;
  apply P.filter_iff; auto;
  intuition.
    rewrite <- H4; clear H4.
    apply F.add_neq_mapsto_iff; auto.
    unfold not; intros.
    rewrite <- H0 in H2.
    apply F.not_find_in_iff in H1.
    apply F.find_mapsto_iff in H2.
    congruence.
  rewrite <- H4 in H2; clear H4.
  apply F.find_mapsto_iff in H2.
  simplify_maps.
    rewrite H0 in Heqe.
    congruence.
  apply F.find_mapsto_iff.
  assumption.
Qed.

Lemma fold_Some_f_Proper {elt} : forall (P : M.key -> elt -> bool),
  Proper (O.eq ==> eq ==> eq ==> eq)
         (fun (k : M.key) (e : elt) (x0 : option (M.key * elt)) =>
            match x0 with
            | Some _ => x0
            | None => if P k e then Some (k, e) else None
            end).
Proof.
Admitted.

Lemma fold_Some_f_negkey {elt} : forall (P : M.key -> elt -> bool),
  P.transpose_neqkey
    eq (fun (k : M.key) (e : elt) (x0 : option (M.key * elt)) =>
          match x0 with
          | Some _ => x0
          | None => if P k e then Some (k, e) else None
          end).
Proof.
Admitted.

Global Program Instance find_if_Proper :
  forall elt (P : M.key -> elt -> bool),
    Proper (O.eq ==> eq ==> eq) P ->
    Proper (M.Equal ==> (fun p p' =>
                           match p, p' return Prop with
                           | Some (k, e), Some (k', e') =>
                             O.eq k k' /\ e = e'
                           | None, None => True
                           | _, _ => False
                           end)) (find_if P).
Obligation 1.
  unfold find_if; intros ???.
  pose proof
    (fold_Proper
       (fun (k : M.key) (e : elt) (x0 : option (M.key * elt)) =>
          match x0 with
          | Some _ => x0
          | None => if P k e then Some (k, e) else None
          end)
       (fold_Some_f_Proper _)
       (fold_Some_f_negkey _) x y H0).
  erewrite H1; eauto; clear x H1 H0.
  apply P.fold_rec; intros; auto.
  destruct a; auto.
  destruct (P k e); auto.
Qed.

Definition singleton {elt} (k : M.key) (e : elt) : M.t elt :=
  M.add k e (M.empty _).
Arguments singleton {elt} k e /.

Corollary MapsTo_singleton : forall k elt (e : elt),
  M.MapsTo k e (singleton k e).
Proof. intros; constructor; reflexivity. Qed.

Corollary fold_left_singleton : forall elt k (e : elt) A (z : A) f,
  M.fold f (M.add k e (M.empty elt)) z = f k e z.
Proof. intros; rewrite M.fold_1; reflexivity. Qed.

Lemma find_if_singleton : forall elt (P : M.key -> elt -> bool) k k' e e',
  find_if P (singleton k e) = Some (k', e')
  -> k = k' /\ e = e' /\ P k e = true.
Proof.
  unfold find_if, singleton; intros.
  rewrite M.fold_1 in H.
  simpl in H.
  destruct (P k e).
    intuition; congruence.
  discriminate.
Qed.

Lemma filter_empty : forall elt (m : M.t elt) P,
  M.Empty (elt:=elt) m -> M.Empty (elt:=elt) (P.filter P m).
Proof.
  intros.
  unfold P.filter.
  revert H.
  apply P.fold_rec; intros.
    apply M.empty_1.
  specialize (H1 k).
  unfold P.Add in H1.
  rewrite F.elements_o in H1.
  apply P.elements_Empty in H3.
  rewrite H3 in H1; simpl in H1.
  rewrite F.add_eq_o in H1; [| apply O.eq_refl].
  discriminate.
Qed.

Lemma fold_left_cons {elt}
      (m : list (M.key * elt)) (z : list (M.key * elt)) p
      (f : M.key -> elt -> bool) :
  List.fold_left (fun m' p => if f (fst p) (snd p)
                              then (fst p, snd p) :: m'
                              else m') (p :: m) z =
  if f (fst p) (snd p)
  then List.fold_left (fun m' p => if f (fst p) (snd p)
                                        then (fst p, snd p) :: m'
                                        else m') m ([p] ++ z)
  else List.fold_left (fun m' p => if f (fst p) (snd p)
                                   then (fst p, snd p) :: m'
                                   else m') m z.
Proof.
  generalize dependent z.
  induction m; simpl; intros.
    rewrite <- surjective_pairing.
    destruct (f _ _); reflexivity.
  destruct (f _ _); simpl; auto.
  rewrite <- !surjective_pairing; auto.
Qed.

Lemma fold_right_rapp : forall A B (xs : list (A * B)) (P : A -> B -> bool) a,
  fold_right (fun p m' => if P (fst p) (snd p) then p :: m' else m')
             [] (xs ++ [a]) =
  fold_right (fun p m' => if P (fst p) (snd p) then p :: m' else m')
             [] xs ++ (if P (fst a) (snd a) then [a] else []).
Proof.
  induction xs; intros; simpl; trivial.
  destruct (P _ _); simpl.
    f_equal.
    apply IHxs.
  apply IHxs.
Qed.

Lemma rev_fold_right : forall A B (xs : list (A * B)) (P : A -> B -> bool),
  List.fold_right (fun p m' => if P (fst p) (snd p)
                               then p :: m'
                               else m') [] xs =
  rev (List.fold_right (fun p m' => if P (fst p) (snd p)
                                    then p :: m'
                                    else m') [] (rev xs)).
Proof.
  intros.
  induction xs; simpl; trivial.
  rewrite fold_right_rapp.
  destruct (P _ _); simpl; trivial.
    rewrite rev_unit.
    f_equal; apply IHxs.
  rewrite app_nil_r.
  apply IHxs.
Qed.

Lemma fold_elements : forall elt (m : M.t elt) (P : M.key -> elt -> bool),
  M.elements (elt:=elt)
    (M.fold (fun k e m' => if P k e
                           then M.add k e m'
                           else m') m (M.empty elt)) =
  List.fold_right (fun p m' => if P (fst p) (snd p)
                               then p :: m'
                               else m') [] (M.elements m).
Proof.
  intros.
  rewrite rev_fold_right.
  replace (fun p m' => if P (fst p) (snd p) then p :: m' else m')
     with (P.uncurry (fun k e m' => if P k e then (k, e) :: m' else m')).
    Focus 2.
    unfold P.uncurry.
    Require Import FunctionalExtensionality.
    extensionality p.
    extensionality m'.
    rewrite <- surjective_pairing.
    reflexivity.
  rewrite <- P.fold_spec_right.
  rewrite !M.fold_1.
  induction (M.elements (elt:=elt) m); trivial; simpl.
  destruct (P _ _); trivial.
Abort.

Lemma filter_elements : forall elt (m : M.t elt) P,
  M.Equal (P.filter P m)
          (P.of_list (List.filter (fun p => P (fst p) (snd p))
                                  (M.elements m))).
Proof.
  intros.
  unfold P.of_list, P.uncurry.
  rewrite fold_right_filter.
  unfold P.filter.
  rewrite P.fold_spec_right.
  unfold P.uncurry.
  induction m using P.map_induction.
Abort.

Lemma filter_for_all : forall elt (m : M.t elt) P,
  Proper (O.eq ==> eq ==> eq) P
    -> M.Equal (P.filter P m) m -> P.for_all P m = true.
Proof.
  unfold P.for_all; intros.
  unfold P.for_all.
  apply P.fold_rec; auto; intros.
  rewrite <- H0 in H1.
  apply P.filter_iff in H1; trivial.
  rewrite (proj2 H1); assumption.
Qed.

Lemma filter_idempotent : forall elt (m : M.t elt) P,
  Proper (O.eq ==> eq ==> eq) P
    -> M.Equal (P.filter P (P.filter P m)) (P.filter P m).
Proof.
  intros.
  unfold P.filter.
  apply P.fold_rec; intros.
    intro k.
    apply P.elements_Empty in H0.
    symmetry; rewrite F.elements_o, H0.
    symmetry; rewrite F.elements_o, P.elements_empty.
    reflexivity.
  pose proof (P.filter_iff H).
  apply H4 in H0; clear H4.
  rewrite (proj2 H0).
  rewrite H3.
  unfold P.Add in H2.
  symmetry.
  exact H2.
Qed.

Lemma filter_for_all_2 : forall elt (m : M.t elt) P,
  Proper (O.eq ==> eq ==> eq) P -> P.for_all P (P.filter P m) = true.
Proof.
  intros.
  apply filter_for_all; eauto.
  unfold P.for_all.
  apply filter_idempotent; assumption.
Qed.

Lemma add_singleton :
  forall k k0 A (e e0 : A) m,
    M.Equal (M.add k0 e0 m) (singleton k e) ->
      O.eq k0 k /\ e0 = e /\ M.Empty m.
Proof.
  unfold singleton; intros.
  induction m as [IHm|m' m'' IHm k' e' H1 H2] using P.map_induction;
  eapply F.Equal_mapsto_iff in H;
  destruct H as [_ H];
  specialize (H (MapsTo_singleton k _ e));
  apply F.find_mapsto_iff in H;
  simplify_maps.
  - intuition.
  - simplify_maps.
  - intuition.
Abort.

Lemma eqb_refl : forall k, F.eqb k k = true.
Proof.
  unfold F.eqb; intros.
  destruct (O.eq_dec k k); trivial.
  contradiction n; reflexivity.
Qed.

Lemma compare_refl : forall t H, O.compare t t = EQ H.
Proof.
  intros.
  destruct (O.compare t t).
  - pose proof l.
    apply O.lt_not_eq in H0.
    contradiction.
  - f_equal.
    Require Import ProofIrrelevance.
    apply proof_irrelevance.
  - pose proof l.
    apply O.lt_not_eq in H0.
    contradiction.
Qed.

Lemma singleton_of_list : forall elt (m : M.t elt) l,
  Sorted (M.lt_key (elt:=elt)) l
    -> M.Equal m (P.of_list l) -> M.elements m = l.
Proof.
  intros.
  induction m using P.map_induction.
Abort.

Lemma filter_singleton_elements : forall elt k (e : elt) m P,
  Proper (O.eq ==> eq ==> eq) P
    -> M.Equal (P.filter P m) (singleton k e)
    -> M.elements (P.filter P m) = [(k, e)].
Proof.
  intros.
  eapply F.Equal_mapsto_iff in H0.
  destruct H0.
  specialize (H1 (MapsTo_singleton k _ e)).
  apply F.find_mapsto_iff in H1.
  simplify_maps; trivial.
  clear H0.
  revert H2.
  unfold P.filter.
  apply P.fold_rec; intros.
Abort.

Lemma equal_add :
  forall k0 k elt (e0 e : elt) m,
    M.Equal (M.add k0 e0 m) (M.add k e (M.empty elt))
      -> (O.eq k k0 /\ e0 = e) \/ M.Equal m (M.empty elt).
Proof.
  intros.
  destruct (O.eq_dec k k0).
  - left.
    specialize (H k0).
    rewrite !F.add_o in H.
    destruct (O.eq_dec k0 k0);
    destruct (O.eq_dec k k0).
    + inversion H; subst.
      intuition.
    + intuition.
    + contradiction n.
      reflexivity.
    + contradiction.
  - right.
Abort.

Lemma find_if_filter : forall elt (m : M.t elt) P,
  Proper (O.eq ==> eq ==> eq) P
    -> find_if P (P.filter P m) = find_if P m.
Proof.
  intros.
Admitted.

Lemma find_if_filter_is_singleton :
  forall elt k (e : elt) m P,
    Proper (O.eq ==> eq ==> eq) P
      -> M.Equal (P.filter P m) (singleton k e)
      -> find_if P m = Some (k, e).
Proof.
  intros.
  rewrite <- find_if_filter.
  pose proof (find_if_Proper
                _ P H (P.filter P m) (singleton k e) H0).
  simpl in H1.
  destruct (find_if P (P.filter P m)) eqn:Heqe1.
    destruct p.
    destruct (find_if P (M.add k e (M.empty elt))) eqn:Heqe2.
      destruct p.
      pose proof (find_if_singleton _ P _ _ _ _ Heqe2).
      intuition; subst.
      rewrite <- Heqe1, <- Heqe2.
      admit.
  rewrite H0.
  unfold find_if; intros.
  
Abort.

End FMapExt.
