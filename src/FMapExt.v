Require Import
  Coq.FSets.FMapList
  Coq.FSets.FMapFacts
  Coq.Structures.OrderedTypeEx
  Coq.Sorting.Permutation.

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
  | [ H : M.MapsTo (elt:=?T) ?A ?B (M.add ?K ?E ?M) |- _ ] =>
    apply F.add_mapsto_iff in H;
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    destruct H as [[H1 H2]|[H3 H4]]; [subst|]
  | [ H : M.MapsTo (elt:=?T) ?A ?B (M.remove ?KE ?M) |- _ ] =>
    apply F.remove_mapsto_iff in H;
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    destruct H as [H1 H2]
  | [ H : M.MapsTo (elt:=?T) ?A ?B (M.map ?F ?M) |- _ ] =>
    apply F.map_mapsto_iff in H;
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let cblk := fresh "cblk" in
    destruct H as [cblk [H1 H2]]
  | [ H : M.MapsTo (elt:=?T) ?A ?B (P.filter ?F ?M) |- _ ] =>
    apply P.filter_iff in H;
    [let H1 := fresh "H1" in
     let H2 := fresh "H2" in
     destruct H as [H1 H2]|]
  | [ H : M.MapsTo (elt:=?T) ?A ?B (M.mapi ?F ?M) |- _ ] =>
    rewrite F.mapi_o, <- F.map_o in H
  | [ H : M.MapsTo (elt:=?T) ?A ?B (M.empty ?U) |- _ ] =>
    apply F.empty_mapsto_iff in H; contradiction
  | [ H1 : M.MapsTo (elt:=?T) ?A ?B ?M,
      H2 : M.Empty (elt:=?T) ?M |- _ ] =>
    apply F.find_mapsto_iff in H1;
    apply P.elements_Empty in H2;
    rewrite F.elements_o in H1;
    rewrite H2 in H1;
    inversion H1

  | [ |- M.MapsTo (elt:=?T) ?A ?B (M.add ?K ?E ?M) ] =>
    apply F.add_mapsto_iff
  | [ |- M.MapsTo (elt:=?T) ?A ?B (M.remove ?KE ?M) ] =>
    apply F.remove_mapsto_iff
  | [ |- M.MapsTo (elt:=?T) ?A ?B (M.map ?F ?M) ] =>
    apply F.map_mapsto_iff
  | [ |- M.MapsTo (elt:=?T) ?A ?B (P.filter ?F ?M) ] =>
    apply P.filter_iff
  | [ |- M.MapsTo (elt:=?T) ?A ?B (M.mapi ?F ?M) ] =>
    rewrite F.mapi_o, <- F.map_o;
    apply F.map_mapsto_iff

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

Ltac relational' :=
  repeat match goal with
  | [ |- Proper _ _ ] => intros ???
  | [ |- respectful _ _ _ _ ] => intros ???
  | [ |- iff _ _ ] => split; intro
  end;
  try simplify_maps; subst;
  auto.

Global Program Instance MapsTo_Proper {elt} :
  Proper (O.eq ==> eq ==> M.Equal ==> iff) (@M.MapsTo elt) :=
  (@F.MapsTo_m_Proper elt).

Global Program Instance find_iff_Proper {elt} :
  Proper (O.eq ==> eq ==> M.Equal ==> iff)
         (fun k e m => @M.find elt k m = Some e).
Obligation 1.
  relational'.
    rewrite <- H, <- H1.
    assumption.
  rewrite H, H1.
  assumption.
Qed.

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
  relational'.
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
  relational'.
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
  relational'.
  generalize dependent x.
  generalize dependent y.
  induction m; simpl; trivial.
  destruct a; simpl.
  destruct (P k e); simpl; intros;
  apply IHm;
  rewrite H;
  reflexivity.
Qed.

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

Definition take_first {elt} (f : M.key -> elt -> bool) (k : M.key) (e : elt)
           (x0 : option (M.key * elt)) :=
  match x0 with
  | Some _ => x0
  | None => if f k e then Some (k, e) else None
  end.

Definition optionP {A} (P : relation A) : relation (option A) :=
  fun x y => match x, y with
             | Some x', Some y' => P x' y'
             | None, None => True
             | _, _ => False
             end.

Program Instance optionP_Equivalence {A} (P : relation A) :
  Equivalence P -> Equivalence (optionP P).
Obligation 1.
  intro x.
  destruct x; simpl; trivial.
  reflexivity.
Qed.
Obligation 2.
  intros x y Heq.
  destruct x, y; simpl in *; trivial.
  intuition.
Qed.
Obligation 3.
  intros x y z Heq1 Heq2.
  destruct x, y, z; simpl in *; auto;
  firstorder.
Qed.

Definition pairP {A B} (P : relation A) (Q : relation B) : relation (A * B) :=
  fun p p' => match p, p' with
              | (x, y), (x', y') => P x x' /\ Q y y'
              end.

Program Instance pairP_Equivalence {A B} (P : relation A) (Q : relation B) :
  Equivalence P -> Equivalence Q -> Equivalence (pairP P Q).
Obligation 1.
  intro x.
  destruct x; simpl.
  intuition.
Qed.
Obligation 2.
  intros x y Heq.
  destruct x, y; simpl in *.
  intuition.
Qed.
Obligation 3.
  intros x y z Heq1 Heq2.
  destruct x, y, z; simpl in *.
  firstorder.
Qed.

Program Instance take_first_Proper {elt} :
  Proper ((O.eq ==> eq ==> eq)
            ==> O.eq
            ==> eq
            ==> optionP (pairP O.eq eq)
            ==> optionP (pairP O.eq eq)) (take_first (elt:=elt)).
Obligation 1.
  relational'.
  destruct x2, y2.
  - destruct p, p0; simpl in *.
    assumption.
  - contradiction.
  - contradiction.
  - unfold take_first.
    rewrite (H _ _ H0 y1 y1 eq_refl).
    destruct (y y0 y1); auto.
    unfold optionP, pairP; auto.
Qed.

Corollary take_first_None
          {elt} (f : M.key -> elt -> bool) (k : M.key) (e : elt) x :
  take_first f k e (Some x) = Some x.
Proof. reflexivity. Qed.

Definition find_if {elt} (f : M.key -> elt -> bool) (m : M.t elt) :=
  M.fold (take_first f) m None.

Lemma find_if_empty : forall elt (P : M.key -> elt -> bool) m,
  M.Empty m -> find_if P m = None.
Proof.
  unfold find_if; intros.
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

Global Program Instance fold_Proper {elt A} : forall f (eqA : relation A),
  Equivalence eqA
    -> Proper (O.eq ==> eq ==> eqA ==> eqA) f
    -> P.transpose_neqkey eqA f
    -> Proper (M.Equal (elt:=elt) ==> eqA ==> eqA) (@M.fold elt A f).
Obligation 1.
  relational'.
  revert H2.
  revert y.
  apply P.fold_rec; intros.
    rewrite P.fold_Empty; auto.
    rewrite <- H4.
    assumption.
  rewrite (P.fold_Add (eqA:=eqA)); eauto.
  - f_equiv.
    apply H6.
    congruence.
  - congruence.
Qed.

Global Program Instance filter_Proper {elt} : forall P,
  Proper (O.eq ==> eq ==> eq) P
    -> Proper (M.Equal (elt:=elt) ==> M.Equal) (@P.filter elt P).
Obligation 1.
  relational'.
  unfold P.filter at 1.
  generalize dependent y.
  apply P.fold_rec; intros.
    apply F.Equal_mapsto_iff.
    split; intros.
      inversion H2.
    simplify_maps; auto.
    rewrite <- H1 in H3.
    apply P.elements_Empty in H0.
    apply F.find_mapsto_iff in H3.
    rewrite F.elements_o in H3.
    rewrite H0 in H3.
    inversion H3.
  specialize (H3 m' (F.Equal_refl _)).
  apply add_equal_iff in H2.
  rewrite <- H2 in H4; clear H2 m'' H0.
  destruct (P k e) eqn:Heqe; rewrite H3; clear H3.
    apply F.Equal_mapsto_iff.
    split; intros.
      simplify_maps; auto.
        rewrite <- H2.
        simplify_maps; auto.
        intuition.
        rewrite <- H4.
        simplify_maps; auto.
      simplify_maps; auto.
      simplify_maps; auto.
      intuition.
      rewrite <- H4.
      simplify_maps; auto.
    simplify_maps; auto.
    rewrite <- H4 in H2.
    repeat simplify_maps; auto.
    right.
    intuition.
    simplify_maps; auto.
  apply F.Equal_mapsto_iff.
  split; intros;
  simplify_maps; auto;
  simplify_maps; auto;
  intuition.
    rewrite <- H4; clear H4.
    apply F.add_neq_mapsto_iff; auto.
    unfold not; intros.
    rewrite <- H0 in H2.
    apply F.not_find_in_iff in H1.
    apply F.find_mapsto_iff in H2.
    congruence.
  rewrite <- H4 in H2; clear H4.
  simplify_maps; auto.
  rewrite H0 in Heqe.
  congruence.
Qed.

Lemma Equal_add_remove : forall elt k (e : elt) m' m'',
  ~ M.In k m' -> M.Equal (M.add k e m') m'' -> M.Equal m' (M.remove k m'').
Proof.
  intros.
  intro addr.
  specialize (H0 addr).
  destruct (O.eq_dec k addr).
    rewrite F.remove_eq_o; auto.
    rewrite F.add_eq_o in H0; auto.
    apply F.not_find_in_iff.
    rewrite <- e0.
    assumption.
  rewrite F.add_neq_o in H0; auto.
  rewrite F.remove_neq_o; auto.
Qed.

Global Program Instance find_if_Proper {elt} :
  Proper ((O.eq ==> @eq elt ==> eq)
            ==> M.Equal
            ==> optionP (pairP O.eq eq)) find_if.
Obligation 1.
  relational'.
  unfold find_if.
  revert H0.
  revert x0.
  apply P.fold_rec; simpl; intros.
    rewrite <- H1 in H0.
    exact (P.fold_Empty _ (take_first x) None H0).
  apply add_equal_iff in H2.
  rewrite <- H4 in H2; clear H4 m''.
  apply Equal_add_remove in H2; auto.
  symmetry in H2.
  specialize (H3 _ H2); clear H2 H1 H0 y0.
  unfold optionP, pairP in *.
  destruct a; simpl in *.
    destruct p; simpl in *.
    admit.
  admit.
(*
  unfold P.Add in H2.
  rewrite P.fold_Add; eauto.
  -
  - apply optionP_Equivalence.
    apply pairP_Equivalence.
    apply F.KeySetoid.
    apply eq_equivalence.
  - apply take_first_Proper.
  - intros ??????.
*)
Admitted.

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

Lemma find_if_filter_is_singleton :
  forall elt k (e : elt) m P,
    Proper (O.eq ==> eq ==> eq) P
      -> M.Equal (P.filter P m) (singleton k e)
      -> find_if P m = Some (k, e).
Proof.
  unfold find_if, P.filter; intros.
Abort.

Lemma build_map_left_add :
  forall elt (l : list (M.key * elt)) k e
         (P : M.key -> elt -> bool) m,
    Proper (O.eq ==> eq ==> eq) P
      -> (forall k0 e0, O.eq k k0 -> e = e0)
      -> M.elements (fold_left (build_map_left _ P) l (M.add k e m)) =
         M.elements ((M.add k e (fold_left (build_map_left _ P) l m))).
Proof.
  intros.
  generalize dependent m.
  generalize dependent e.
  generalize dependent k.
  induction l; intros.
    reflexivity.
  unfold build_map_left in *.
  destruct a; simpl.
  destruct (P k0 e0); simpl.
    simpl in IHl.
    rewrite <- IHl.
    f_equal.
    f_equal.
    unfold M.add. simpl.
Admitted.

Corollary fold_right_filter : forall A P (l : list A),
  List.filter P l =
  fold_right (fun x rest => if P x then x :: rest else rest) [] l.
Proof. intros; induction l; simpl; auto. Qed.

Lemma filter_elements : forall elt (P : M.key -> elt -> bool) m,
  Proper (O.eq ==> eq ==> eq) P
    -> M.elements (P.filter P m) =
       List.filter (fun p => P (fst p) (snd p)) (M.elements m).
Proof.
  intros.
  unfold P.filter.
  rewrite P.fold_spec_right, fold_right_filter.
  unfold P.uncurry.
Abort.

End FMapExt.
