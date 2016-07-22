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

End FMapExt.
