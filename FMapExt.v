Require Import
  Coq.FSets.FMapList
  Coq.FSets.FMapFacts
  Coq.Structures.OrderedTypeEx.

Module FMapExt (O : OrderedType).

Module M := FMapList.Make(O).
Module P := FMapFacts.Properties M.
Module F := P.F.

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

Lemma mapi_empty (Oeq_eq : forall a b, O.eq a b -> a = b) :
  forall (f : M.key -> elt -> elt),
    M.Equal (M.mapi f (M.empty elt)) (M.empty elt).
Proof.
  intros f k.
  rewrite F.mapi_o, F.empty_o; trivial.
  intros.
  apply Oeq_eq in H; subst.
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

Lemma for_all_mapi (Oeq_eq : forall a b, O.eq a b -> a = b) :
  forall elt' (m : M.t elt') (k : M.key)
         (f : M.key -> elt' -> elt),
    P.for_all P (M.mapi f m) = true
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

Definition singleton {elt} (k : M.key) (e : elt) : M.t elt :=
  P.of_list [(k, e)].
Arguments singleton {elt} k e /.

Corollary fold_left_singleton : forall elt k (e : elt) A (z : A) f,
  M.fold f (M.add k e (M.empty elt)) z = f k e z.
Proof. intros; rewrite M.fold_1; reflexivity. Qed.

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
  M.elements (P.filter P m)
    = List.filter (fun p => P (fst p) (snd p)) (M.elements m).
Proof.
  unfold P.filter; intros.
  Fail rewrite fold_elements.
  induction (M.elements (elt:=elt) m); trivial.
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

Lemma find_if_1 : forall elt (m : M.t elt) P,
  find_if P m = match M.elements (P.filter P m) with
                | [] => None
                | x :: _ => Some x
                end.
Proof.
  unfold find_if; intros.
  Fail rewrite M.fold_1, filter_elements.
  induction (M.elements (elt:=elt) m); trivial.
  simpl filter.
  Fail rewrite fold_Some_cons, <- surjective_pairing; auto.
  Fail destruct (P (fst a) (snd a)); auto.
Abort.

(* Lemma findA_nil : forall l, *)
(*   (forall y : M.key, findA (F.eqb y) l = []) -> l = []. *)

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
    admit.
  destruct l.
    admit.
  specialize (H0 x).
  rewrite !F.elements_o in H0; simpl in H0.
Abort.

Lemma filter_singleton_elements : forall elt k (e : elt) m P,
  M.Equal (P.filter P m) (singleton k e)
    -> M.elements (P.filter P m) = [(k, e)].
Proof.
  intros.
  induction m using P.map_induction.
    apply filter_empty with (P:=P) in H0.
    apply P.elements_Empty in H0.
    specialize (H k).
    rewrite !F.elements_o, H0 in H.
    simpl in H; rewrite eqb_refl in H.
    discriminate.
  Fail apply singleton_of_list.
    Fail constructor; constructor.
  simpl.
  unfold P.uncurry; simpl.
  Fail exact H.
Abort.

Lemma find_if_filter : forall elt k (e : elt) m P,
  Proper (O.eq ==> eq ==> eq) P
    -> M.Equal (P.filter P m) (singleton k e)
    -> find_if P m = Some (k, e).
Proof.
  unfold singleton; intros.
  Fail rewrite find_if_1.
  Fail rewrite (filter_singleton_elements _ _ _ _ _ H0).
  Fail reflexivity.
Abort.

End FMapExt.
