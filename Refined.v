Require Import Fiat.ADT Fiat.ADTNotation.

Require Import
  Coq.Lists.List
  Coq.Arith.Arith
  Coq.NArith.NArith.

Require Import
  Here.ByteString
  Here.LibExt
  Here.Heap.

Require Import
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Section ByteString.

Variable Word8 : Type.

Definition ByteStringSpec := ByteStringSpec Word8.
Definition ByteString     := ByteString Word8.
Definition HeapSpec       := HeapSpec Word8.

Record PS := makePS {
  psHeap : Rep HeapSpec;

  psBuffer : N;
  psBufLen : N;

  psOffset : N;
  psLength : N;

  psError  : bool
}.

  (* psBufInHeap : psBufLen = 0 \/ Ensembles.In _ (fst heap) (psBuffer, psBufLen); *)

  (* psBegInBlock : psBufLen = 0 \/ within psBuffer psBufLen psOffset; *)
  (* psEndInBlock : psBufLen = 0 \/ within psBuffer psBufLen (psOffset + psLength) *)

Definition ByteString_list_AbsR (or : Rep ByteStringSpec) (nr : PS) :=
  forall i x (H : (N.to_nat i <? length or)%nat),
    x = nth_safe (N.to_nat i) or H
      <-> (x <- peek (psHeap nr) (psOffset nr); ret (snd x)) ↝ Some x.

(*
Lemma ByteStringImpl (heap : Rep HeapSpec) : FullySharpened ByteStringSpec.
Proof.
  start sharpening ADT.
  unfold ByteStringSpec; simpl.
  hone representation using ByteString_list_AbsR;
  try simplify with monad laws; simpl;
  unfold ByteString_list_AbsR in *.
  {
    refine pick val
      {| psHeap   := heap
       ; psBuffer := 0
       ; psBufLen := 0
       ; psOffset := 0
       ; psLength := 0
       ; psError  := false |}; simpl.
      finish honing.
    split; intros; inv H0.
  }
  {
    etransitivity.
      apply (refine_skip2 (dummy:=realloc (psHeap r_n) (psBuffer r_n)
                                          (psLength r_n + 1))).
    etransitivity.
      apply refine_under_bind; intros.
      refine pick val
        (if psError r_n
         then r_n
         else if 0 <? psOffset r_n
              then {| psHeap   := heap
                      ; psBuffer := psBuffer r_n
                      ; psBufLen := psBufLen r_n
                      ; psOffset := psOffset r_n - 1
                      ; psLength := psLength r_n + 1
                      ; psError  := false |}
              else if psBuffer r_n + psOffset r_n + psLength r_n + 1 <=?
                      psBuffer r_n + psBufLen r_n
                   then {| psHeap   := heap
                         ; psBuffer := psBuffer r_n
                         ; psBufLen := psBufLen r_n
                         ; psOffset := psOffset r_n
                         ; psLength := psLength r_n + 1
                         ; psError  := false |}
                   else match snd a with
                        | Some addr =>
                          {| psHeap   := fst a
                           ; psBuffer := addr
                           ; psBufLen := psLength r_n + 1
                           ; psOffset := 0
                           ; psLength := psLength r_n + 1
                           ; psError  := false |}
                        | None =>
                          {| psHeap   := fst a
                           ; psBuffer := psBuffer r_n
                           ; psBufLen := psBufLen r_n
                           ; psOffset := psOffset r_n
                           ; psLength := psLength r_n
                           ; psError  := true |}
                        end); simpl.
        simplify with monad laws.
        finish honing.
      intros.
      specialize (H0 i x).
      destruct (psError r_n); intros.
        split; intros; subst.
          eapply BindComputes.
            unfold peek.
            eapply BindComputes.
              apply PickComputes; intros.
      destruct (0 <? psOffset r_n); simpl.
        admit.
      destruct (psBuffer r_n + psOffset r_n + psLength r_n + 1 <=?
                psBuffer r_n + psBufLen r_n); simpl.
        admit.
      destruct a, o; simpl.
        admit.
      admit.
    simpl.
    finish honing.
  }
  {
    refine pick val (match r_n with
                     | nil => (r_o, None)
                     | List.cons x x0 =>
                       (Ensemble_map (first Init.Nat.pred)
                                     (Subtract _ r_o (0, x)), Some x)
                     end).
      simplify with monad laws; simpl.
      refine pick val (match r_n with
                       | nil => nil
                       | List.cons _ xs => xs
                       end).
        simplify with monad laws; simpl.
        replace
          (match r_n with
           | [] => []
           | _ :: xs => xs
           end,
           snd
             match r_n with
             | [] => (r_o, None)
             | x :: _ =>
               (Ensemble_map (first Init.Nat.pred)
                             (Subtract (nat * Word8) r_o (0, x)), Some x)
             end)
        with
        (match r_n with
           | [] => ([], None)
           | x :: xs => (xs, Some x)
           end).
          finish honing.
        induction r_n; simpl; trivial.
      {
        clear H.
        destruct r_n; simpl; split; intros.
        - apply H0 in H.
          destruct H.
          exists x0.
          exact e.
        - destruct H.
          inv x0.
        - simplify_ensembles.
          apply H0 in H1.
          destruct n; simpl in *.
            destruct H1; subst.
            contradiction H2.
            constructor.
          destruct H1.
          exists x0.
          exact e.
        - exists (S i, x).
          split.
            constructor.
              apply H0.
              destruct H.
              exists x0.
              exact e.
            unfold not; intros.
            inv H1.
          constructor.
      }
      destruct r_n; simpl in *.
        reflexivity.
      split.
        apply H0.
        exists eq_refl.
        reflexivity.
      reflexivity.
  }

  finish_SharpeningADT_WithoutDelegation.
Defined.

Definition ByteStringImpl' := Eval simpl in projT1 ByteStringImpl.
(* Print ByteStringImpl'. *)
*)

End ByteString.