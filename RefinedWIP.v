Definition foldr_lists {A} : (Word8 -> A -> A) -> A -> list Word8 -> A :=
  @List.fold_right A Word8.

Definition ByteString_list_AbsR (or : ByteString) (nr : list Word8) :=
  forall i x, Ensembles.In _ or (i, x)
    <-> forall H : i <? length nr, x = nth_safe i nr H.

(*
Lemma foldr_Impl {A : Type} :
  refineFun_AbsR (fDom:=[Word8->A->A; A])
                 (fCod:=A) ByteString_list_AbsR
                 foldr_Spec
                 (fun xs f z =>
                    let res := @foldr_lists A f z xs in
                    ret (xs, res)).
Proof.
  intros.
  unfold foldr_Spec; intros.
  unfold refineFun_AbsR, ByteString_list_AbsR in *; simpl; intros.
  etransitivity.
    pose proof (@Finish_refining_LeastFixedPoint
              [list Word8; Word8 -> A -> A; A]
              (list Word8)
              A
              (fun l1 l2 : list Word8 => length l1 < length l2)
              (@length_wf Word8)).
    simpl in H.
Abort.
*)

(*
  {
    apply refine_bind.
      pose proof (Finish_refining_LeastFixedPoint
                    (fDom := [Word8 -> A -> A; A])
                    (fCod := list Word8 * A)
                    (recT := list Word8)
                    (P := fun l1 l2 => length l1 < length l2)
                    (@length_wf _)) as H4.
      simpl in H4.
      admit.                    (* jww (2016-05-25): how to proceed? *)
    intros r_o'; simpl.
    refine pick val r_n.
      simplify with monad laws.
      finish honing.
    intros.
    admit.                      (* need to know that [r_o = fst r_o'] *)
  }
*)
