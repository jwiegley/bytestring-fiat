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

End FMapExt.