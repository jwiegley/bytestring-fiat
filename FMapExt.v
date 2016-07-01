Require Import
  Coq.FSets.FMapAVL
  Coq.FSets.FMapFacts
  Coq.Structures.OrderedTypeEx.

Module FMapExt (O : OrderedType).

Module M := FMapAVL.Make(O).
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

Definition unique_predicate {elt} (f : M.key -> elt -> bool) (m : M.t elt) :=
  forall a  b,  M.find a  m = Some b  -> is_true (f a  b)  ->
  forall a' b', M.find a' m = Some b' -> is_true (f a' b') -> a = a' /\ b = b'.

Definition find_if {elt} (f : M.key -> elt -> bool) (m : M.t elt) :
  option (M.key * elt) :=
  M.fold (fun (k : M.key) (e : elt) x =>
            match x with
            | Some _ => x
            | None => if f k e then Some (k, e) else None
            end) m
         None.

Lemma fold_Some {elt} (m : list (M.key * elt))
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

Lemma fold_Some_cons {elt} (m : list (M.key * elt))
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

Lemma findA_if_invert (Oeq_eq : forall a b, O.eq a b <-> a = b) :
  forall elt a k e f l,
    (forall (a2 : M.key) (b2 : elt),
        (if F.eqb a2 k then Some e else findA (F.eqb a2) l) = Some b2 ->
        ~ O.eq a a2 -> f a2 b2 = false) ->
    (forall (a2 : M.key) (b2 : elt),
        is_true (F.eqb a2 k) ->
        Some e = Some b2 ->
        ~ O.eq a a2 -> f a2 b2 = false) \/
    (forall (a2 : M.key) (b2 : elt),
        findA (F.eqb a2) l = Some b2 ->
        ~ O.eq a a2 -> f a2 b2 = false).
Proof.
  intros.
  specialize (H k).
  unfold F.eqb, M.E.eq_dec in *.
  destruct (O.eq_dec k k).
    left; intros.
    destruct (O.eq_dec a2 k).
      apply Oeq_eq in e1; subst.
      firstorder.
    discriminate.
  right; intros.
  contradiction n.
  apply Oeq_eq.
  reflexivity.
Qed.

Lemma map_injective : forall elt a (b b' : elt) m,
  M.find a m = Some b -> M.find a m = Some b' -> b = b'.
Proof.
  intros.
  rewrite F.elements_o in H, H0.
  induction (M.elements (elt:=elt) m).
    discriminate.
  destruct a0; simpl in *.
  unfold F.eqb, M.E.eq_dec in *.
  destruct (O.eq_dec a k).
    inversion H; inversion H0; subst.
    assumption.
  intuition.
Qed.

Theorem find_if_unique
        (Oeq_eq : forall a b, O.eq a b <-> a = b)
        {elt}  (f : M.key -> elt -> bool) (m : M.t elt) :
  unique_predicate f m
    -> forall a b,
         M.find a m = Some b
           -> is_true (f a b)
           -> find_if f m = Some (a, b).
Proof.
  unfold unique_predicate, find_if; intros.
  specialize (H _ _ H0 H1).
  apply F.find_mapsto_iff in H0.
  apply P.fold_rec_nodep.
    admit.
  intros; subst.
  reflexivity.
Admitted.

End FMapExt.
