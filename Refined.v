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
  psLength : N
}.

  (* psBufInHeap : psBufLen = 0 \/ Ensembles.In _ (fst heap) (psBuffer, psBufLen); *)

  (* psBegInBlock : psBufLen = 0 \/ within psBuffer psBufLen psOffset; *)
  (* psEndInBlock : psBufLen = 0 \/ within psBuffer psBufLen (psOffset + psLength) *)

Theorem Nle_zero : forall n : N, 0 <= n.
Proof.
  destruct n.
    reflexivity.
  destruct p; discriminate.
Qed.

Theorem Nlt_plus_1 : forall n : N, 0 < n + 1.
Proof.
  destruct n.
    reflexivity.
  constructor.
Qed.

Theorem Nsucc_nat : forall n, N.pos (Pos.of_succ_nat n) = N.succ (N.of_nat n).
Proof.
  induction n.
    reflexivity.
  constructor.
Qed.

Theorem Nsub_add_succ : forall n m,
  n - 1 + N.succ (N.of_nat m) = n + N.of_nat m.
Proof.
  destruct n; intros.
    admit.
  admit.
Admitted.

Theorem Nplus_1_mismatch : forall n m, n > 0 -> n + m = n - 1 -> False.
Proof.
  destruct n; intros.
    discriminate.
Admitted.

Theorem Nlt_false : forall n, (0 <? n) = false -> n = 0.
Proof.
  destruct n; intros.
    reflexivity.
  discriminate.
Qed.

Theorem within_extended : forall addr len i,
  within (addr - 1) (len + 1) (N.succ i) -> within addr len i.
Proof.
  unfold within; intros.
  destruct H.
  split.
    admit.
  admit.
Admitted.

Definition ByteString_list_AbsR (or : Rep ByteStringSpec) (nr : PS) :=
  length or = N.to_nat (psLength nr) /\
  forall i x,
    (i <? length or)%nat
      -> within (psOffset nr) (psLength nr) (N.of_nat i)
      -> x = nth i or x <->
         (x <- peek (psHeap nr) (psOffset nr + N.of_nat i);
          ret (snd x)) ↝ Some x.

Definition buffer_cons (r : PS) (d : Word8) : Comp PS :=
  ps <- If 0 <? psOffset r
        Then ret {| psHeap   := psHeap r
                  ; psBuffer := psBuffer r
                  ; psBufLen := psBufLen r
                  ; psOffset := psOffset r - 1
                  ; psLength := psLength r + 1 |}
        Else (
          If psLength r <? psBufLen r
          Then res <- memcpy (psHeap r) (psBuffer r)
                             (psBuffer r + 1) (psLength r);
               ret {| psHeap   := fst res
                    ; psBuffer := psBuffer r
                    ; psBufLen := psBufLen r
                    ; psOffset := 0
                    ; psLength := psLength r + 1 |}
          Else (
            res <- realloc (psHeap r) (psBuffer r)
                           (exist _ (psLength r + 1)
                                    (Nlt_plus_1 _));
            ret {| psHeap   := fst res
                 ; psBuffer := snd res
                 ; psBufLen := psLength r + 1
                 ; psOffset := 0
                 ; psLength := psLength r + 1 |}));
  res <- poke (psHeap ps) (psOffset ps) d;
  ret {| psHeap   := fst res
       ; psBuffer := psBuffer ps
       ; psBufLen := psBufLen ps
       ; psOffset := psOffset ps
       ; psLength := psLength ps |}.

Ltac reduction :=
  repeat match goal with
    | [ H : Some _ = Some _ |- _ ] => inv H
    | [ H : (_, _) = (_, _) |- _ ] => inv H
    (* | [ _ : is_true (Nat.ltb 0 _) |- _ ] => *)
    (*   rewrite N.add_0_r in *; *)
    (*   try (apply Union_intror; constructor) *)
    | [ H : forall x : _, Some ?X = Some x -> _ |- _ ] =>
      specialize (H X eq_refl);
      simplify_ensembles; subst; simpl in *
    | [ |- context [N.pos (Pos.of_succ_nat _)] ] =>
      rewrite Nsucc_nat
    | [ H : context [N.pos (Pos.of_succ_nat _)] |- _ ] =>
      rewrite Nsucc_nat in H
    | [ |- context [N.succ (N.of_nat _)] ] =>
      rewrite Nsub_add_succ
    | [ H : context [N.succ (N.of_nat _)] |- _ ] =>
      rewrite Nsub_add_succ in H
    | [ H1 : is_true (Nat.ltb (S ?I) (S _)),
        _  : _ = nth ?I _ ?X,
        H2 : forall i x, is_true (Nat.ltb i _) -> _ |- _ ] =>
      specialize (H2 I X H1); clear H1
    | [ H1 : is_true (Nat.ltb (S ?I) (S _)),
        _  : In _ _ (_, ?X),
        H2 : forall i x, is_true (Nat.ltb i _) -> _ |- _ ] =>
      specialize (H2 I X H1); clear H1
    | [ H1 : _ = nth _ _ _,
        H2 : _ = nth _ _ _ <-> _ |- _ ] =>
      apply H2 in H1; clear H2;
      simplify_ensembles; subst; simpl in *
    | [ H : _ = nth _ _ _ <-> _ |- _ = nth _ _ _ ] =>
      apply H; clear H;
      autorewrite with monad laws;
      simplify_ensembles; simpl; intros
    | [ |- ~ _ ] => unfold not; intros
    end.

Theorem buffer_cons_sound
        (r_o : list Word8) (r_n : PS) (x : Word8)
        (AbsR : ByteString_list_AbsR r_o r_n) :
  forall r_n', buffer_cons r_n x ↝ r_n' ->
    ByteString_list_AbsR (x :: r_o) r_n'.
Proof.
  unfold buffer_cons, ByteString_list_AbsR,
         peek, poke, memcpy.
  simpl; intros.
  destruct AbsR.
  rewrite H0 in *; clear H0.

  split.
    destruct (0 <? psOffset r_n) eqn:Heqe;
    destruct (psLength r_n <? psBufLen r_n);
    clear -H; simpl in H;
    simplify_ensembles; subst; simpl;
    rewrite <- N2Nat.inj_succ, N.add_1_r; reflexivity.

  split; intros.
    autorewrite with monad laws.
    apply PickComputes; intros ? H4; inv H4.
    destruct (psLength r_n <? psBufLen r_n);
    (destruct (0 <? psOffset r_n) eqn:Heqe;
     [|apply Nlt_false in Heqe]);
    simplify_ensembles; subst; simpl in *; inv H4;
    (destruct i; subst;
     [apply Union_intror|apply Union_introl]);
    rewrite ?N.add_0_r, ?Heqe in *;
    try constructor;
    unfold peek in *;
    simplify_ensembles; subst; simpl in *;
    reduction.
    simpl in H;
    + inv H3.
      destruct i; subst; [apply Union_intror|apply Union_introl].
        constructor.
      specialize (H1 i x1 H0).
      apply H1 in H2; clear H1 H0.
      unfold peek in H2.
      simplify_ensembles.
        simpl in H0.
        admit.
      unfold not; intros.
      inv H2.
      admit.
    + inv H3.
      destruct i; subst; [apply Union_intror|apply Union_introl].
        rewrite N.add_0_r.
        constructor.
      specialize (H1 i x1 H0).
      apply H1 in H2; clear H1 H0.
      unfold peek in H2.
      simplify_ensembles.
        simpl in H0.
        admit.
      unfold not; intros.
      inv H2.
      admit.
    + inv H3.
      destruct i; subst; [apply Union_intror|apply Union_introl].
        constructor.
      specialize (H1 i x1 H0).
      apply H1 in H2; clear H1 H0.
      unfold peek in H2.
      simplify_ensembles.
        simpl in H0.
        admit.
      unfold not; intros.
      inv H2.
    + 
        rewrite N.ltb_lt in Heqe.
        apply N.lt_gt.
    inv H3.

  destruct i; [clear H1 H0|].
    destruct (0 <? psOffset r_n) eqn:Heqe;
    destruct (psLength r_n <? psBufLen r_n);
    simpl in H;
    simplify_ensembles; subst; simpl in *.

  (split; intros; [autorewrite with monad laws|]);
  simplify_ensembles; intro; subst; simpl in *.
      split.

      split; intros;
      unfold poke in H0.
        autorewrite with monad laws.
        destruct (0 <? psOffset r_n) eqn:Heqe;
        destruct (psLength r_n <? psBufLen r_n);
        simpl in H0;
        simplify_ensembles;
        subst; simpl in *; intros;
        repeat match goal with
          | [ H : Some _ = Some _ |- _ ] => inv H
          | [ H : (_, _) = (_, _) |- _ ] => inv H
          end.
        admit.
        admit.
        admit.
        admit.

      unfold peek in H3.
      simplify_ensembles.
      repeat match goal with
        | [ H : Some _ = Some _ |- _ ] => inv H
        | [ H : (_, _) = (_, _) |- _ ] => inv H
        end.
      simpl in *.
      specialize (H3 x H4).
      repeat match goal with
        | [ H : Some _ = Some _ |- _ ] => inv H
        | [ H : (_, _) = (_, _) |- _ ] => inv H
        end.
      destruct (0 <? psOffset r_n) eqn:Heqe;
      destruct (psLength r_n <? psBufLen r_n);
      simpl in H0;
      simplify_ensembles;
      subst; simpl in *; intros.

      destruct i; split; intros; subst;
      autorewrite with monad laws;
      simplify_ensembles;
      intros; simpl in *;
      repeat match goal with
        | [ H : Some _ = Some _ |- _ ] => inv H
        | [ H : (_, _) = (_, _) |- _ ] => inv H
        | [ _ : is_true (Nat.ltb 0 _) |- _ ] =>
          rewrite N.add_0_r in *;
          try (apply Union_intror; constructor)
        | [ H : forall x : _, Some ?X = Some x -> _ |- _ ] =>
          specialize (H X eq_refl);
          simplify_ensembles; subst; simpl in *
        | [ |- context [N.pos (Pos.of_succ_nat _)] ] =>
          rewrite Nsucc_nat
        | [ H : context [N.pos (Pos.of_succ_nat _)] |- _ ] =>
          rewrite Nsucc_nat in H
        | [ |- context [N.succ (N.of_nat _)] ] =>
          rewrite Nsub_add_succ
        | [ H : context [N.succ (N.of_nat _)] |- _ ] =>
          rewrite Nsub_add_succ in H
        | [ H1 : is_true (Nat.ltb (S ?I) (S _)),
            _  : _ = nth ?I _ ?X,
            H2 : forall i x, is_true (Nat.ltb i _) -> _ |- _ ] =>
          specialize (H2 I X H1); clear H1
        | [ H1 : is_true (Nat.ltb (S ?I) (S _)),
            _  : In _ _ (_, ?X),
            H2 : forall i x, is_true (Nat.ltb i _) -> _ |- _ ] =>
          specialize (H2 I X H1); clear H1
        | [ H1 : _ = nth _ _ _,
            H2 : _ = nth _ _ _ <-> _ |- _ ] =>
          apply H2 in H1; clear H2;
          simplify_ensembles; subst; simpl in *
        | [ H : _ = nth _ _ _ <-> _ |- _ = nth _ _ _ ] =>
          apply H; clear H;
          autorewrite with monad laws;
          simplify_ensembles; simpl; intros
        | [ |- ~ _ ] => unfold not; intros
        | [ |- In _ _ _ ] => apply Union_introl; split; intros
        end.

      - inv H1.
        apply Nplus_1_mismatch in H3.
          assumption.
        rewrite N.ltb_lt in Heqe.
        apply N.lt_gt.
        assumption.
      - assumption.
      - symmetry in H4.
        apply Nplus_1_mismatch in H4.
          contradiction.
        rewrite N.ltb_lt in Heqe.
        apply N.lt_gt.
        assumption.
      - inv H1.
        apply Nplus_1_mismatch in H3.
          assumption.
        rewrite N.ltb_lt in Heqe.
        apply N.lt_gt.
        assumption.
      - assumption.
      - symmetry in H4.
        apply Nplus_1_mismatch in H4.
          contradiction.
        rewrite N.ltb_lt in Heqe.
        apply N.lt_gt.
        assumption.
      - clear H1 H0 Heqe.
        admit.
      - inv H2.
        admit.
      - admit.
      - inv H1.
        admit.
      - contradiction H4.
        unfold Ensembles.In; simpl.
        admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
    }
    finish honing.
  }
Admitted.

Lemma ByteStringImpl (heap : Rep HeapSpec) : FullySharpened ByteStringSpec.
Proof.
  start sharpening ADT.
  unfold ByteStringSpec; simpl.
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
      apply refine_under_bind; intros.
      refine pick val a.
        simplify with monad laws.
        finish honing.
      exact (buffer_cons_sound H0 H1).
    unfold buffer_cons.
    simplify with monad laws; simpl.
    finish honing.
  }
  (*
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
  *)
  admit.

  finish_SharpeningADT_WithoutDelegation.
  simpl.
Fail Defined.

Fail Definition ByteStringImpl' := Eval simpl in projT1 ByteStringImpl.
(* Print ByteStringImpl'. *)

Fail End ByteString.
Abort All.