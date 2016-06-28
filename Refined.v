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

Generalizable All Variables.

Open Scope N_scope.

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

(* Theorem Nsub_add_succ : forall n m, *)
(*   n > 0 -> n - 1 + N.succ (N.of_nat m) = n + N.of_nat m. *)
(* Proof. *)
(*   destruct n; intros. *)
(*     admit. *)
(*   admit. *)
(* Admitted. *)

Theorem Nplus_1_mismatch : forall n m, n > 0 -> n + m = n - 1 -> False.
Proof.
  destruct n; intros.
    discriminate.
Admitted.

Theorem Nplus_mismatch : forall n m, m > 0 -> ~ (n = n + m).
Proof.
  destruct n; intros.
Admitted.

Theorem Nplus_minus : forall n m o, o <= n -> n - o + (m + o) = n + m.
Proof.
  destruct n; intros.
    apply N.le_0_r in H.
    subst.
    simpl.
    rewrite N.add_0_r.
    reflexivity.
Admitted.

Theorem Nplus_minus_one : forall n m o,
  n + m <= o -> (0 <? n) = true -> n - 1 + (m + 1) <= o.
Proof.
  intros.
  rewrite Nplus_minus.
    exact H.
  apply N.ltb_lt in H0.
  destruct n.
    discriminate.
  destruct p; discriminate.
Qed.

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

Theorem Nsucc_nat : forall n, N.pos (Pos.of_succ_nat n) = N.succ (N.of_nat n).
Proof.
  induction n.
    reflexivity.
  constructor.
Qed.

Lemma Nlt_nat_lt : forall n m, (n < N.to_nat m)%nat -> (N.of_nat n < m).
Proof.
  induction n; simpl in *; intros.
    destruct m.
      inversion H.
    destruct p; constructor.
  apply lt_pred in H.
  rewrite <- N2Nat.inj_pred in H.
  specialize (IHn _ H).
  apply N.lt_succ_lt_pred in IHn.
  simpl in IHn.
  rewrite <- Nsucc_nat in IHn.
  apply IHn.
Qed.

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

Record Correct (ps : PS) : Prop := {
  _ : 0 < psBufLen ps
        -> exists data,
             In _ (psHeap ps) {| memAddr := psBuffer ps
                               ; memSize := psBufLen ps
                               ; memData := data |};
  _ : psOffset ps + psLength ps <= psBufLen ps;
  _ : ADTInduction.fromADT HeapSpec (psHeap ps)
}.

Definition ByteString_list_AbsR (or : Rep ByteStringSpec) `(_ : Correct nr) :=
     (* then the list and active region must be the same size *)
     length or = N.to_nat (psLength nr)
     (* and for every index within the list... *)
  /\ forall i, (i <? length or)%nat
     (* each byte in the list matches its corresponding byte in the buffer. *)
       -> forall x, x = nth i or x
          <-> (x <- peek (psHeap nr) (psOffset nr + N.of_nat i);
               ret (snd x)) ↝ x.

Definition buffer_cons (r : PS) (d : Word8) : Comp PS :=
  ps <- If 0 <? psOffset r
        Then ret {| psHeap   := psHeap r
                  ; psBuffer := psBuffer r
                  ; psBufLen := psBufLen r
                  ; psOffset := psOffset r - 1
                  ; psLength := psLength r + 1 |}
        Else (
          If psLength r <? psBufLen r
          Then (
            res <- memcpy (psHeap r) (psBuffer r)
                          (psBuffer r + 1) (psLength r);
            ret {| psHeap   := fst res
                 ; psBuffer := psBuffer r
                 ; psBufLen := psBufLen r
                 ; psOffset := 0
                 ; psLength := psLength r + 1 |})
          Else (
            (* jww (2016-06-28): We could make a trade-off here by allocating
               extra bytes at the beginning in anticipation of future calls to
               [buffer_cons]. *)
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
    (* | [ |- context [N.succ (N.of_nat _)] ] => *)
    (*   rewrite Nsub_add_succ *)
    (* | [ H : context [N.succ (N.of_nat _)] |- _ ] => *)
    (*   rewrite Nsub_add_succ in H *)
    | [ H : within (_ - 1) (_ + 1) (N.succ _) |- _ ] =>
      apply within_extended in H
    | [ H1 : is_true (Nat.ltb (S ?I) (S _)),
        _  : _ = nth ?I _ ?X,
        H2 : within _ _ _,
        H3 : forall i x, is_true (Nat.ltb i _) -> within _ _ _ -> _ |- _ ] =>
      specialize (H3 I X H1 H2); clear H1 H2
    | [ H1 : is_true (Nat.ltb (S ?I) (S _)),
        _  : _ = nth ?I _ ?X,
        H2 : forall i x, is_true (Nat.ltb i _) -> _ |- _ ] =>
      specialize (H2 I X H1); clear H1
    | [ H1 : is_true (Nat.ltb (S ?I) (S _)),
        _  : In _ _ (_, ?X),
        H2 : within _ _ _,
        H3 : forall i x, is_true (Nat.ltb i _) -> within _ _ _ -> _ |- _ ] =>
      specialize (H3 I X H1 H2); clear H1 H2
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

Theorem fromADT_bind
        {sig} `{adt : ADT sig} (r : Rep adt)
        A (f : Rep adt -> Comp (Rep adt * A))
        ResultT (k : Rep adt * A -> Comp ResultT)
        (prj : ResultT -> Rep adt) :
  ADTInduction.fromADT adt r
    -> (forall r r' x,
          ADTInduction.fromADT adt r
            -> f r ↝ (r', x)
            -> ADTInduction.fromADT adt r')
    -> (forall r r' x,
          ADTInduction.fromADT adt r
            -> k (r, x) ↝ r'
            -> ADTInduction.fromADT adt (prj r'))
    -> forall r', (x <- f r; k x) ↝ r'
         -> ADTInduction.fromADT adt (prj r').
Proof.
  intros.
  simplify_ensembles.
  apply (H0 _ _ _ H) in H2.
  apply (H1 _ _ _ H2) in H3.
  exact H3.
Qed.

Theorem buffer_cons_heap_adt `(_ : Correct ps) : forall ps' x,
  buffer_cons ps x ↝ ps'
    -> ADTInduction.fromADT HeapSpec (psHeap ps').
Proof.
  unfold buffer_cons.
  destruct Correct0.
  intros.
  destruct (0 <? psOffset ps) eqn:Heqe;
  destruct (psLength ps <? psBufLen ps) eqn:Heqe2;
  simpl in H2.
  - unfold poke in H2.
    apply (@ADTInduction.fromADTMethod
             _ HeapSpec
             (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) (* poke *)
             (psHeap ps) _ H1).
    do 3 eexists.
    simplify_ensembles; reduction.
    constructor.
  - unfold poke in H2.
    apply (@ADTInduction.fromADTMethod
             _ HeapSpec
             (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) (* poke *)
             (psHeap ps) _ H1).
    do 3 eexists.
    simplify_ensembles; reduction.
    constructor.
  - revert H2.
    rewrite refineEquiv_bind_bind.
    remember (fun u => Bind _ _) as k.
    intros.
    eapply (@fromADT_bind
              _ HeapSpec (psHeap ps) unit
              (fun h => memcpy h (psBuffer ps) (psBuffer ps + 1)
                                 (psLength ps)) _ k).
    + assumption.
    + intros.
      clear -H3 H4.
      revert H4.
      unfold memcpy.
      intros.
      simplify_ensembles.
      inv H4.
      apply (@ADTInduction.fromADTMethod
               _ HeapSpec
               (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))) (* memcpy *)
               r _ H3).
      do 4 eexists.
      constructor.
    + intros.
      rewrite Heqk in H4.
      clear -H3 H4.
      revert H4.
      unfold poke.
      autorewrite with monad laws.
      simpl.
      intros.
      apply (@ADTInduction.fromADTMethod
               _ HeapSpec
               (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) (* poke *)
               r _ H3).
      do 3 eexists.
      simplify_ensembles; subst.
      constructor.
    + apply H2.
  - revert H2.
    rewrite refineEquiv_bind_bind.
    remember (fun u => Bind _ _) as k.
    intros.
    eapply (@fromADT_bind
              _ HeapSpec (psHeap ps) N
              (fun h => realloc h (psBuffer ps)
                                  (exist (N.lt 0) (psLength ps + 1)
                                         (Nlt_plus_1 (psLength ps)))) _ k).
    + assumption.
    + intros.
      clear -H3 H4.
      revert H4.
      unfold realloc.
      intros.
      simplify_ensembles.
      apply (@ADTInduction.fromADTMethod
               _ HeapSpec
               (Fin.FS (Fin.FS Fin.F1)) (* realloc *)
               r _ H3).
      do 3 eexists.
      econstructor.
      split; [ exact H | exact H0 ].
    + intros.
      rewrite Heqk in H4.
      clear -H3 H4.
      revert H4.
      unfold poke.
      autorewrite with monad laws.
      simpl.
      intros.
      apply (@ADTInduction.fromADTMethod
               _ HeapSpec
               (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) (* poke *)
               r _ H3).
      do 3 eexists.
      simplify_ensembles; subst.
      constructor.
    + apply H2.
Qed.

Theorem buffer_cons_correct `(_ : Correct ps) : forall ps' x,
  buffer_cons ps x ↝ ps' -> Correct ps'.
Proof.
  destruct Correct0.
  unfold buffer_cons, peek, poke, memcpy.
  constructor; intros;
  destruct (0 <? psOffset ps) eqn:Heqe;
  destruct (psLength ps <? psBufLen ps) eqn:Heqe2;
  simpl in H;
  simplify_ensembles; subst; simpl in *; reduction;
  simplify_ensembles; subst; simpl in *; eauto.
  - inv H2; eauto.
  - unfold realloc, Decidable.IfDec_Then_Else in H2.
    simpl in H2.
    simplify_ensembles.
    unfold If_Opt_Then_Else in *.
    destruct x0; simpl in *;
    simplify_ensembles.
      destruct (psLength ps + 1 <=? n0);
      simplify_ensembles.
        inv H4.
        unfold IF_then_else.
        intuition.
      inv H5.
      right; constructor.
    inv H5.
    right; constructor.
  - apply Nplus_minus_one; assumption.
  - apply Nplus_minus_one; assumption.
  - clear H H2 u.
    apply Nlt_false in Heqe.
    rewrite Heqe in H0; simpl in H0.
    apply N.ltb_lt in Heqe2.
    rewrite N.add_1_r.
    apply N.le_succ_l.
    assumption.
  - apply N.le_refl.
  - apply (@ADTInduction.fromADTMethod
             _ HeapSpec
             (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
             (psHeap ps) _ H1).
    eexists.
    exists x.
    exists tt.
    constructor.
  - apply (@ADTInduction.fromADTMethod
             _ HeapSpec
             (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
             (psHeap ps) _ H1).
    eexists.
    exists x.
    exists tt.
    constructor.
  - inv H2.
    eapply (@ADTInduction.fromADTMethod
              _ HeapSpec
              (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
              (psHeap ps) _ H1).
    eapply (@ADTInduction.fromADTMethod
             _ HeapSpec
             (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))
             (psHeap ps)).
    eexists.
    eexists.
    eexists.
    
    inv 
    constructor.
    exists x.
    exists tt.
    simpl.
    inv H2.
    admit.
  - apply (@ADTInduction.fromADTMethod
             _ HeapSpec
             (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
             (psHeap ps) _ H1).
    eexists; eexists; eexists.
    simpl.
Qed.

Theorem buffer_cons_length_increase `(_ : Correct ps) : forall ps' x,
  buffer_cons ps x ↝ ps' -> psLength ps' = psLength ps + 1.
Proof.
  unfold buffer_cons, peek, poke, memcpy in *.
  destruct (0 <? psOffset ps) eqn:Heqe;
  destruct (psLength ps <? psBufLen ps);
  simpl; intros; clear -H; simpl in H;
  simplify_ensembles; subst; simpl;
  reflexivity.
Qed.

Theorem buffer_cons_data_retained `(_ : Correct ps) : forall ps' x,
  buffer_cons ps x ↝ ps' ->
    (x <- peek (psHeap ps') (psOffset ps'); ret (snd x)) ↝ Some x /\
    forall i,
      refineEquiv
        (x <- peek (psHeap ps') (psOffset ps' + (i + 1)); ret (snd x))
        (x <- peek (psHeap ps) (psOffset ps + i); ret (snd x)).
Proof.
  unfold buffer_cons, peek, poke, memcpy in *.
  destruct (0 <? psOffset ps) eqn:Heqe;
  destruct (psLength ps <? psBufLen ps);
  simpl; intros; clear -H Heqe; simpl in H;
  simplify_ensembles; subst; simpl;
  autorewrite with monad laws;
  simplify_ensembles; subst; simpl;
  intros; reduction.
  (* f_equiv; unfold impl, flip; *)
  (* intros ????; subst; simpl in *; reduction. *)
Admitted.
  (* - rewrite (@Nplus_minus (psOffset ps) i 1) in H. *)
  (*     assumption. *)
  (*   apply N.ltb_lt in Heqe. *)
  (*   replace 1 with (N.succ 0); trivial. *)
  (*   apply N.le_succ_l; assumption. *)
  (* - apply Nplus_mismatch in H1. *)
  (*     contradiction. *)
  (*   admit. *)

Theorem buffer_cons_sound
        (r_o : list Word8) `(r_n : Correct ps)
        (AbsR : ByteString_list_AbsR r_o r_n) :
  forall x ps' (H : buffer_cons ps x ↝ ps'),
    ByteString_list_AbsR (x :: r_o) (buffer_cons_correct r_n H).
Proof.
  unfold ByteString_list_AbsR in *; intros.
  destruct AbsR.
  split.
    simpl.
    rewrite H0, (buffer_cons_length_increase r_n H),
            <- N2Nat.inj_succ, N.add_1_r.
    reflexivity.

  destruct (buffer_cons_data_retained r_n H).
  split; intros.
    destruct i; simpl in *.
      subst.
      clear -H2.
      rewrite N.add_0_r.
      assumption.
    destruct (H3 (N.of_nat i)); clear H3.
    unfold refine in H6.
    rewrite Nsucc_nat, <- N.add_1_r.
    apply H6, H1; eauto.

  destruct i; simpl in *.
    clear H0 H1.
    rewrite N.add_0_r in H5.
    clear -H2 H5.
    unfold peek in *.
    simplify_ensembles; reduction.
    simpl in *; subst.
    reduction.
    assert (ADTInduction.fromADT (Heap.HeapSpec Word8) (psHeap ps')).
      
      unfold ADTInduction.fromADT.
    apply (assignments_unique _ _ _ _ (conj H H2)).
  apply H1.
    exact H4.
  apply H3.
  rewrite N.add_1_r, <- Nsucc_nat.
  exact H5.
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