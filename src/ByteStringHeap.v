Require Import
  Coq.Lists.List
  Coq.Arith.Arith
  Coq.NArith.NArith
  Fiat.ADT
  Fiat.ADTNotation
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements
  ByteString.ADTInduction
  ByteString.BindDep
  ByteString.ByteString
  ByteString.Heap
  ByteString.HeapADT
  ByteString.Nomega
  ByteString.Relations
  ByteString.Tactics
  ByteString.TupleEnsembles
  ByteString.Within.

Generalizable All Variables.

Open Scope N_scope.

(*
Lemma within_index : forall addr len i,
  (i <? len) -> within addr len (addr + i).
Proof.
  intros.
  split.
    apply N.le_add_r.
  apply N.add_lt_mono_l.
  apply N.ltb_lt.
  assumption.
Qed.
*)

Module ByteStringHeap (Mem : Memory).

Module Import BS := ByteString Mem.
Module Import Adt := HeapADT Mem.
Import Heap.

Definition HSpec := projT1 HeapSpecADT.

Definition memcpy' (r : Rep HSpec) (addr : N) (addr2 : N) (len : N) :
  Comp (Rep HSpec * unit) :=
  Eval simpl in callMeth HSpec memcpyS r addr addr2 len.

Definition realloc' (r : Rep HSpec) (addr : N) (len : N | 0 < len) :
  Comp (Rep HSpec * N) :=
  Eval simpl in callMeth HSpec reallocS r addr len.

Definition peek' (r : Rep HSpec) (addr : N) :
  Comp (Rep HSpec * Mem.Word8) :=
  Eval simpl in callMeth HSpec peekS r addr.

Definition poke' (r : Rep HSpec) (addr : N) (w : Mem.Word8) :
  Comp (Rep HSpec * unit) :=
  Eval simpl in callMeth HSpec pokeS r addr w.

Record PS := makePS {
  psHeap : Rep HSpec;

  psBuffer : N;
  psBufLen : N;

  psOffset : N;
  psLength : N
}.

Record Correct (ps : PS) : Prop := {
  _ : psOffset ps + psLength ps <= psBufLen ps;
  _ : 0 < psBufLen ps -> exists data,
        Lookup (psBuffer ps) {| memSize := psBufLen ps
                              ; memData := data |} (` (psHeap ps))
}.

Theorem Nlt_plus_1 : forall n : N, 0 < n + 1.
Proof. nomega. Qed.

Definition buffer_cons (r : PS) (d : Mem.Word8) : Comp PS :=
  ps <- If 0 <? psOffset r
        Then ret {| psHeap   := psHeap r
                  ; psBuffer := psBuffer r
                  ; psBufLen := psBufLen r
                  ; psOffset := psOffset r - 1
                  ; psLength := psLength r + 1 |}
        Else If psLength r <? psBufLen r
        Then (
          res <- memcpy' (psHeap r) (psBuffer r) (psBuffer r + 1)
                         (psLength r);
          ret {| psHeap   := fst res
               ; psBuffer := psBuffer r
               ; psBufLen := psBufLen r
               ; psOffset := 0
               ; psLength := psLength r + 1 |})
        Else (
          (* jww (2016-06-28): We could make a trade-off here by allocating
             extra bytes at the beginning in anticipation of future calls to
             [buffer_cons]. *)
          res <- realloc' (psHeap r) (psBuffer r)
                          (exist _ (psLength r + 1) (Nlt_plus_1 _));
          ret {| psHeap   := fst res
               ; psBuffer := snd res
               ; psBufLen := psLength r + 1
               ; psOffset := 0
               ; psLength := psLength r + 1 |});
  res <- poke' (psHeap ps) (psBuffer ps + psOffset ps) d;
  ret {| psHeap   := fst res
       ; psBuffer := psBuffer ps
       ; psBufLen := psBufLen ps
       ; psOffset := psOffset ps
       ; psLength := psLength ps |}.

Lemma refine_ret_eq_r : forall A (a b : A), refine (ret a) (ret b) -> a = b.
Proof.
  intros.
  specialize (H b (ReturnComputes b)).
  apply Return_inv; assumption.
Qed.

Theorem If_Then_Else_correct :
  forall b cpst cpse ps',
    (forall pst, b = true -> refine cpst (ret pst) -> Correct pst) ->
    (forall pse, b = false -> refine cpse (ret pse) -> Correct pse) ->
    refine (If b
            Then cpst
            Else cpse) (ret ps') -> Correct ps'.
Proof.
  intros.
  specialize (H1 ps' (ReturnComputes ps')).
  destruct b; simpl in *;
  [ apply H | apply H0 ]; auto;
  intros ??;
  apply Return_inv in H2; subst;
  assumption.
Qed.

Theorem poke'_correct `(_ : Correct ps) : forall offset length d ps',
  0 < length ->
  offset + length <= psBufLen ps ->
  refine (res <- poke' (psHeap ps) (psBuffer ps + offset) d;
          ret {| psHeap   := fst res
               ; psBuffer := psBuffer ps
               ; psBufLen := psBufLen ps
               ; psOffset := offset
               ; psLength := length |}) (ret ps') -> Correct ps'.
Proof.
  intros ??????.
  unfold poke', poke.
  rewrite refine_bind_dep_bind_ret; simpl.
  rewrite refine_bind_dep_ret; simpl.
  intro H1.
  apply refine_ret_eq_r in H1.
  subst; simpl.
  destruct Correct0.
  constructor; simpl; [nomega|].
  intuition; destruct_ex.
  exists (Update offset d x).
  teardown.
  exists {| memSize := psBufLen ps; memData := x |}; simpl.
  decisions; intuition; f_equal.
    f_equal; nomega.
  nomega.
Qed.

Definition buffer_uncons (r : PS) : Comp (PS * option Mem.Word8) :=
  If 0 <? psLength r
  Then (
    w <- peek' (psHeap r) (psBuffer r + psOffset r);
    ret ({| psHeap   := psHeap r
          ; psBuffer := psBuffer r
          ; psBufLen := psBufLen r
          ; psOffset := psOffset r + 1
          ; psLength := psLength r - 1 |}, Some (snd w))
  )
  Else ret (r, None).

Global Program Instance refineEquiv_bind_dep : forall A (ca : Comp A) B,
  Proper (forall_relation
            (fun x0 : A =>
               pointwise_relation (refine ca (ret x0)) refineEquiv) ==>
            (@refineEquiv B))
         (Bind_dep ca).
Obligation 1.
  intros ???.
  split; intros; intros ??;
  apply Bind_dep_inv in H0;
  destruct H0;
  exists x0;
  destruct H0;
  exists x1;
  eapply H in c; eauto.
Qed.

Lemma refineEquiv_If_Then_Else_Bind :
  forall (A B : Type) (i : bool) (t e : Comp A) (b : A -> Comp B),
    refineEquiv (a <- If i Then t Else e; b a)
                (If i Then a <- t; b a Else (a <- e; b a)).
Proof. split; intros; destruct i; reflexivity. Qed.

Theorem buffer_cons_correct `(_ : Correct ps) : forall ps' x,
  refine (buffer_cons ps x) (ret ps') -> Correct ps'.
Proof.
  unfold buffer_cons; intros.
  revert H.
  rewrite refineEquiv_If_Then_Else_Bind.
  apply If_Then_Else_correct; intros ??.
    autorewrite with monad laws; simpl.
    apply poke'_correct; trivial.
      nomega.
    destruct Correct0.
    nomega.
  rewrite refineEquiv_If_Then_Else_Bind.
  apply If_Then_Else_correct; intros ??.
    autorewrite with monad laws; simpl.
    admit.
  autorewrite with monad laws; simpl.
  admit.
Admitted.

Theorem buffer_cons_length_increase ps : forall ps' x,
  buffer_cons ps x ↝ ps' -> psLength ps' = psLength ps + 1.
Proof.
  unfold buffer_cons, peek, poke, memcpy in *.
  destruct (0 <? psOffset ps) eqn:Heqe;
  destruct (psLength ps <? psBufLen ps);
  simpl; intros; clear -H; simpl in H;
  simplify_ensembles; subst; simpl;
  reflexivity.
Qed.

(*
Theorem buffer_cons_data_retained `(_ : Correct ps) : forall ps' x,
  buffer_cons ps x ↝ ps' ->
    (x <- peek (` (psHeap ps')) (psOffset ps'); ret (snd x)) ↝ x /\
    forall i,
      refineEquiv
        (x <- peek (` (psHeap ps')) (psOffset ps' + (i + 1)); ret (snd x))
        (x <- peek (` (psHeap ps)) (psOffset ps + i); ret (snd x)).
Proof.
  unfold buffer_cons, peek, poke, memcpy in *.
  destruct (0 <? psOffset ps) eqn:Heqe;
  destruct (psLength ps <? psBufLen ps);
  simpl; intros; clear -H Heqe; simpl in H;
  simplify_ensembles; subst; simpl;
  autorewrite with monad laws;
  simplify_ensembles; subst; simpl;
  intros; reduction.
*)

Definition ByteString_list_AbsR (or : Rep ByteStringSpec) `(nr : PS) :=
     (* then the list and active region must be the same size *)
     length or = N.to_nat (psLength nr)
     (* and for every index within the list... *)
  /\ forall i, (i <? length or)%nat
     (* each byte in the list matches its corresponding byte in the buffer. *)
       -> forall x, x = nth i or x
          <-> (x <- peek (` (psHeap nr)) (psOffset nr + N.of_nat i);
               ret (snd x)) ↝ x.

Theorem buffer_cons_sound
        (r_o : list Mem.Word8) (r_n : PS)
        (AbsR : ByteString_list_AbsR r_o r_n) :
  forall x r_n' (H : buffer_cons r_n x ↝ r_n'),
    ByteString_list_AbsR (x :: r_o) r_n'.
Proof.
  intros.
  split; intros.
    apply buffer_cons_length_increase in H.
    destruct AbsR; nomega.
  split; intros.
    rewrite H1; clear H1.
    admit.
  admit.
Admitted.

Theorem buffer_uncons_sound
        (r_o : list Mem.Word8) (r_n : PS)
        (AbsR : ByteString_list_AbsR r_o r_n) :
  forall x r_n' (H : buffer_uncons r_n ↝ (r_n', x)),
    ByteString_list_AbsR (match x with
                          | None   => r_o
                          | Some _ => tl r_o
                          end) r_n'.
Proof.
  intros.
  split; intros.
    admit.
  split; intros.
    admit.
  admit.
Admitted.

Lemma ByteStringImpl (heap : Rep HSpec) : FullySharpened ByteStringSpec.
Proof.
  start sharpening ADT.
  hone representation using ByteString_list_AbsR.
  {
    simplify with monad laws.
    refine pick val
      {| psHeap   := heap
       ; psBuffer := 0
       ; psBufLen := 0
       ; psOffset := 0
       ; psLength := 0 |}.
      finish honing.
    split; intros.
      reflexivity.
    split; intros; discriminate.
  }
  {
    simplify with monad laws.
    etransitivity.
      eapply (refine_skip2 (dummy:=buffer_cons r_n d)).
    etransitivity.
      apply refine_under_bind; intros; simpl.
      refine pick val a.
        simplify with monad laws.
        finish honing.
      eapply buffer_cons_sound; eauto.
    unfold buffer_cons.
    simplify with monad laws; simpl.
    finish honing.
  }
  {
    simplify with monad laws.
    etransitivity.
      eapply (refine_skip2 (dummy:=buffer_uncons r_n)).
    etransitivity.
      apply refine_under_bind; intros; simpl.
      refine pick val (fst a).
        simplify with monad laws.
        finish honing.
      pose proof (buffer_uncons_sound H0 (snd a) (fst a)).
      rewrite <- surjective_pairing in H2.
      specialize (H2 H1).
      destruct a; simpl in *.
      simpl.
      admit.
    unfold buffer_uncons.
    admit.
  }
  finish_SharpeningADT_WithoutDelegation.
Admitted.

Fail Definition ByteStringImpl' := Eval simpl in projT1 ByteStringImpl.
(* Print ByteStringImpl'. *)

End ByteStringHeap.
