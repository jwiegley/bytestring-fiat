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

Theorem Nlt_plus_1 : forall n : N, 0 < n + 1.
Proof. nomega. Qed.

Corollary refine_computes_to_ret :
  forall A f (v : A), f ↝ v <-> refine f (ret v).
Proof.
  split; intros.
    apply refine_In.
    exact H.
  apply H.
  constructor.
Qed.

Lemma refineEquiv_If_Then_Else_Bind :
  forall (A B : Type) (i : bool) (t e : Comp A) (b : A -> Comp B),
    refineEquiv (a <- If i Then t Else e; b a)
                (If i Then a <- t; b a Else (a <- e; b a)).
Proof. split; intros; destruct i; reflexivity. Qed.

Theorem refine_If_Then_Else_bool :
  forall (b : bool) A cpst cpse (res : Comp A),
    (if b then refine cpst res else refine cpse res)
      <-> refine (If b Then cpst Else cpse) res.
Proof. split; intros; destruct b; auto. Qed.

Module ByteStringHeap (Mem : Memory).

Module Import BS := ByteString Mem.
Module Import Adt := HeapADT Mem.
Import Heap.

Open Scope N_scope.

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

Definition poke_at_offset (r : PS) (d : Mem.Word8) : Comp PS :=
  res <- poke' (psHeap r) (psBuffer r + psOffset r) d;
  ret {| psHeap   := fst res
       ; psBuffer := psBuffer r
       ; psBufLen := psBufLen r
       ; psOffset := psOffset r
       ; psLength := psLength r |}.

Definition simply_widen_region (r : PS) : PS :=
  {| psHeap   := psHeap r
   ; psBuffer := psBuffer r
   ; psBufLen := psBufLen r
   ; psOffset := psOffset r - 1
   ; psLength := psLength r + 1 |}.

Definition make_room_by_shifting_up (r : PS) : Comp PS :=
  res <- memcpy' (psHeap r) (psBuffer r) (psBuffer r + 1)
                 (psLength r);
  ret {| psHeap   := fst res
       ; psBuffer := psBuffer r
       ; psBufLen := psBufLen r
       ; psOffset := 0
       ; psLength := psLength r + 1 |}.

Definition make_room_by_growing_buffer (r : PS) : Comp PS :=
  (* jww (2016-06-28): We could make a trade-off here by allocating
     extra bytes at the beginning in anticipation of future calls to
     [buffer_cons]. *)
  res <- realloc' (psHeap r) (psBuffer r)
                  (exist _ (psLength r + 1) (Nlt_plus_1 _));
  ret {| psHeap   := fst res
       ; psBuffer := snd res
       ; psBufLen := psLength r + 1
       ; psOffset := 0
       ; psLength := psLength r + 1 |}.

Definition buffer_cons (r : PS) (d : Mem.Word8) : Comp PS :=
  ps <- If 0 <? psOffset r
        Then ret (simply_widen_region r)
        Else If psLength r <? psBufLen r
             Then make_room_by_shifting_up r
             Else make_room_by_growing_buffer r;
  poke_at_offset ps d.

Ltac tease_apart_binds :=
  repeat match goal with
  | [ H : _ ↝ _ |- _ ] =>
    apply Bind_inv in H;
    destruct H as [? [? H]];
    apply Return_inv in H;
    rewrite <- H; simpl
  | [ H : _ ↝ _ |- _ ] =>
    apply Bind_dep_inv in H;
    destruct H as [? [? H]];
    apply Return_inv in H;
    rewrite <- H; simpl
  end.

Lemma buffer_cons_ind : forall (R1 R2 R3 R : relation PS) ps d ps',
     (0 < psOffset ps -> R1 ps (simply_widen_region ps))
  -> (forall v,
        psOffset ps = 0
          -> psLength ps < psBufLen ps
          -> make_room_by_shifting_up ps ↝ v
          -> R2 ps v)
  -> (forall v,
        psOffset ps = 0
          -> psLength ps >= psBufLen ps
          -> make_room_by_growing_buffer ps ↝ v
          -> R3 ps v)
  -> (forall v v' v'',
        (R1 v v' \/ R2 v v' \/ R3 v v')
          -> 0 < psLength v'
          -> poke_at_offset v' d ↝ v''
          -> R v v'')
  -> buffer_cons ps d ↝ ps'
  -> R ps ps'.
Proof.
  intros R1 R2 R3 R ? ? H1 H2 H3 H4 H5 H.
  unfold buffer_cons in H.
  apply refine_computes_to_ret in H.
  rewrite refineEquiv_If_Then_Else_Bind in H.
  apply refine_If_Then_Else_bool in H.
  destruct (0 <? psOffset ps) eqn:Heqe.
    apply refine_computes_to_ret in H.
    {
      apply Bind_inv in H.
      destruct H, H.
      apply Return_inv in H.
      apply H5 with (v':=x); subst.
      - left; apply H2; nomega.
      - nomega.
      - nomega.
    }
  rewrite refineEquiv_If_Then_Else_Bind in H.
  apply refine_If_Then_Else_bool in H.
  destruct (psLength ps <? psBufLen ps) eqn:Heqe2;
  apply refine_computes_to_ret in H.
  {
    apply Bind_inv in H.
    destruct H, H.
    apply H5 with (v':=x).
    - right; left.
      apply H3; nomega.
    - tease_apart_binds; nomega.
    - assumption.
  }
  {
    apply Bind_inv in H.
    destruct H, H.
    apply H5 with (v':=x).
    - right; right.
      apply H4, H; nomega.
    - tease_apart_binds; nomega.
    - assumption.
  }
Qed.

Tactic Notation "unfold_buffer_cons" constr(R1) constr(R2) constr(R3) :=
  repeat match goal with
  | [ H : buffer_cons ?PS ?D ↝ ?PS' |- _ ] =>
    apply (buffer_cons_ind R1 R2 R3)
      with (ps:=PS) (d:=D) (ps':=PS'); intuition
  | [ H : _ ↝ _ |- _ ] => tease_apart_binds
  end.

Theorem buffer_cons_length_increase ps : forall ps' x,
  buffer_cons ps x ↝ ps' -> psLength ps' = psLength ps + 1.
Proof.
  intros;
  set (P := fun x x' => psLength x = psLength x' - 1).
  unfold_buffer_cons P P P; unfold P in *; nomega.
Qed.

Definition buffer_uncons (r : PS) : Comp (PS * option Mem.Word8) :=
  If psLength r =? 0
  Then (
    v <- { p | p = None /\ psOffset r = 0 /\ psBufLen r = 0 };
    ret (r, v)
  )
  Else (
    w <- peek' (psHeap r) (psBuffer r + psOffset r);
    ret ({| psHeap   := psHeap r
          ; psBuffer := psBuffer r
          ; psBufLen := psBufLen r
          ; psOffset := psOffset r + 1
          ; psLength := psLength r - 1 |}, Some (snd w))).

Definition list_map_rel {A} (base : N) (xs : list A) (ys : EMap N A) : Prop :=
  forall k e, Lookup k e ys <-> nth (N.to_nat (k - base)) xs e = e.

Definition ByteString_list_AbsR (or : Rep ByteStringSpec) `(nr : PS) :=
  length or = N.to_nat (psLength nr) /\
  IF psLength nr = 0
  then psBufLen nr = 0
  else exists data,
    fits (psBuffer nr) (psBufLen nr)
         (psBuffer nr + psOffset nr) (psLength nr)
      /\ Lookup (psBuffer nr) {| memSize := psBufLen nr; memData := data |}
                (` (psHeap nr))
      /\ list_map_rel (psOffset nr) or
                      (Filter (fun k _ => within (psOffset nr)
                                                 (psLength nr) k) data).

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

Theorem buffer_cons_sound
        (r_o : list Mem.Word8) (r_n : PS)
        (AbsR : ByteString_list_AbsR r_o r_n) :
  forall x r_n' (H : buffer_cons r_n x ↝ r_n'),
    ByteString_list_AbsR (x :: r_o) r_n'.
Proof.
  intros.
(*
  right.
  split; [nomega|].
  destruct AbsR.
    destruct H0, H1, H2.
    exists (Update 0 x Empty).
    split.
      revert H.
      unfold buffer_cons, make_room_by_growing_buffer, poke_at_offset.
      rewrite H1, H2, H3; simpl; clear H1 H2 H3.
      unfold realloc'.
      rewrite refine_bind_dep_bind_ret; simpl.
      rewrite refine_bind_dep_bind_ret; simpl.
      unfold poke'; simpl.
      setoid_rewrite refine_bind_dep_bind_ret; simpl.
      intros.
      apply Bind_dep_inv in H.
      destruct H, H.
      apply Bind_dep_inv in c.
      destruct c, H.
      apply Return_inv in c.
      destruct r_n';
      tsubst; simpl in *.
      inv c; simpl.
      apply Return_inv in x3; subst; simpl.
      teardown.
      exists {| memSize := 1; memData := Empty |}; simpl.
      rewrite N.add_0_r.
      assert (within (snd x0) 1 (snd x0)) by nomega.
      unfold IfDec_Then_Else; simpl.
      apply within_reflect in H; rewrite H.
      intuition.
      f_equal; f_equal.
      nomega.
      unfold poke in x3.
  destruct H0, H1.
  exists (Update (psOffset r_n') x x0).
*)
(*
  revert AbsR.
  apply
    (buffer_cons_ind
       (fun r_n r_n' =>
          r_n' = {| psHeap   := psHeap   r_n
                  ; psBuffer := psBuffer r_n
                  ; psBufLen := psBufLen r_n
                  ; psOffset := psOffset r_n - 1
                  ; psLength := psLength r_n + 1 |})
       (fun r_n r_n' =>
          exists h,
          memcpy' (psHeap r_n) (psBuffer r_n) (psBuffer r_n + 1)
                  (psLength r_n) ↝ h /\
          r_n' = {| psHeap   := fst h
                  ; psBuffer := psBuffer r_n
                  ; psBufLen := psBufLen r_n
                  ; psOffset := 0
                  ; psLength := psLength r_n + 1 |})
       (fun r_n r_n' =>
          exists h,
          realloc' (psHeap r_n) (psBuffer r_n)
                   (exist (N.lt 0) (psLength r_n + 1)
                          (Nlt_plus_1 (psLength r_n))) ↝ h /\
          r_n' = {| psHeap   := fst h
                  ; psBuffer := snd h
                  ; psBufLen := psLength r_n + 1
                  ; psOffset := 0
                  ; psLength := psLength r_n + 1 |}))
   with (ps:=r_n) (ps':=r_n') (d:=x);
  intros; trivial;
  destruct r_n; simpl in *;
  f_equal; try nomega;
  tease_apart_binds;
  simpl in *; subst.
  - remember (exist _ _ _) as E.
    exists (E, snd x1).
    split; trivial.
    rewrite HeqE.
    exists x1.
    exists x2.
    constructor.
  - remember (exist _ (fst x1) _) as E.
    exists (E, snd x1).
    split; trivial.
    rewrite HeqE.
    exists x1.
    exists x2.
    constructor.
  - destruct H0.
      subst; simpl in *.
      unfold ByteString_list_AbsR in *; simpl in *.
      left.
      destruct AbsR.
        admit.
      destruct H0, H2.
      split.
        nomega.
      rewrite H2, H3 in *; simpl.
      exists Empty.
    destruct H0.
      destruct H0, H0.
      subst; simpl in *.
      unfold ByteString_list_AbsR in *; simpl in *.
      admit.
    destruct H0, H0.
      subst; simpl in *.
      unfold ByteString_list_AbsR in *; simpl in *.
      admit.
*)
Admitted.

Lemma refine_ret_eq_r : forall A (a b : A), refine (ret a) (ret b) -> a = b.
Proof.
  intros.
  specialize (H b (ReturnComputes b)).
  apply Return_inv; assumption.
Qed.

Lemma nth_plus_one : forall A (x : A) xs e off,
  (0 < off)%nat -> nth off (x :: xs) e = nth (off - 1) xs e.
Proof.
  intros.
  destruct off.
    nomega.
  simpl.
  rewrite Nat.sub_0_r.
  reflexivity.
Qed.

Lemma list_map_rel_cons_inv : forall off len A (x : A) xs ys,
  length xs = N.to_nat len
    -> list_map_rel off (x :: xs) (Filter (fun k _ => within off len k) ys)
    -> Lookup off x ys
         /\ list_map_rel (off + 1) xs
                         (Filter (fun k _ => within (off + 1) (len - 1) k) ys).
Proof.
  unfold list_map_rel; split; intros.
    specialize (H0 off x).
    apply H0.
    replace (N.to_nat (off - off)) with 0%nat.
      reflexivity.
    nomega.
  split; intros.
    teardown.
    rewrite N.sub_add_distr, N2Nat.inj_sub.
    simpl in *.
    erewrite <- nth_plus_one.
      apply H0.
      repeat teardown.
      intuition.
      nomega.
    nomega.
  teardown.
  split.
    apply H0.
    admit.
  admit.
Admitted.

Theorem buffer_uncons_sound : forall r_o r_n a,
  ByteString_list_AbsR r_o r_n
    -> buffer_uncons r_n ↝ a
    -> ByteString_list_AbsR (match r_o with
                             | [] => r_o
                             | _ :: xs => xs
                             end) (fst a).
Proof.
  unfold buffer_uncons; intros.
  apply refine_computes_to_ret in H0.
  apply refine_If_Then_Else_bool in H0.
  destruct (psLength r_n =? 0) eqn:Heqe.
    apply refine_computes_to_ret in H0.
    apply Bind_inv in H0.
    destruct H0, H0.
    apply Pick_inv in H0.
    apply Return_inv in H1.
    destruct a; tsubst; simpl in *.
    destruct r_o; simpl in *; auto.
    destruct H, H0, H0, H1.
      destruct r_o; simpl in *; nomega.
    nomega.
  revert H0.
  unfold peek'.
  rewrite refine_bind_dep_bind_ret; simpl.
  rewrite refine_bind_dep_ignore.
  unfold peek.
  autorewrite with monad laws; simpl.
  intros.
  apply refine_computes_to_ret in H0.
  apply Bind_inv in H0.
  destruct H0, H0.
  apply Return_inv in H1.
  destruct a; tsubst; simpl in *.
  apply Pick_inv in H0.
  destruct H.
  destruct H1.
    nomega.
  destruct H1, H2, H2, H3.
  assert (within (psBuffer r_n) (psBufLen r_n) (psBuffer r_n + psOffset r_n)).
    nomega.
  specialize (H0 _ _ H3 H5); simpl in *.
  destruct r_o.
    nomega.
  f_equal.
  split; simpl.
    nomega.
  destruct r_o; simpl in *.
    left.
    split.
      nomega.
    admit.
  right.
  split.
    nomega.
  exists x0.
  split.
    nomega.
  split.
    assumption.
  apply list_map_rel_cons_inv in H4.
  destruct H4.
  assumption.
Admitted.

Theorem buffer_uncons_impl : forall r_o r_n a,
  ByteString_list_AbsR r_o r_n
    -> buffer_uncons r_n ↝ a
    -> snd a = match r_o with
               | [] => None
               | x :: _ => Some x
               end.
Proof.
  unfold buffer_uncons; intros.
  apply refine_computes_to_ret in H0.
  apply refine_If_Then_Else_bool in H0.
  destruct (psLength r_n =? 0) eqn:Heqe.
    apply refine_computes_to_ret in H0.
    apply Bind_inv in H0.
    destruct H0, H0.
    apply Pick_inv in H0.
    apply Return_inv in H1.
    destruct a; tsubst; simpl in *.
    destruct r_o; simpl in *;
    destruct H, H0, H0, H1; auto.
      destruct H0.
      rewrite H0 in H; simpl in H.
      discriminate.
    nomega.
  revert H0.
  unfold peek'.
  rewrite refine_bind_dep_bind_ret; simpl.
  rewrite refine_bind_dep_ignore.
  unfold peek.
  autorewrite with monad laws; simpl.
  intros.
  apply refine_computes_to_ret in H0.
  apply Bind_inv in H0.
  destruct H0, H0.
  apply Return_inv in H1.
  destruct a; tsubst; simpl in *.
  apply Pick_inv in H0.
  destruct H.
  destruct H1.
    nomega.
  destruct H1, H2, H2, H3.
  assert (within (psBuffer r_n) (psBufLen r_n) (psBuffer r_n + psOffset r_n)).
    nomega.
  specialize (H0 _ _ H3 H5); simpl in *.
  destruct r_o.
    nomega.
  f_equal.
  apply H0.
  replace (psBuffer r_n + psOffset r_n - psBuffer r_n)
     with (psOffset r_n); [|nomega].
  apply list_map_rel_cons_inv in H4.
    destruct H4.
    assumption.
  admit.
Admitted.

Lemma fst_match_list :
  forall A (xs : list A) B z C z'
         (f : A -> list A -> B) (f' : A -> list A -> C),
    fst match xs with
        | [] => (z, z')
        | x :: xs => (f x xs, f' x xs)
        end = match xs with
              | [] => z
              | x :: xs => f x xs
              end.
Proof. induction xs; auto. Qed.

Lemma snd_match_list :
  forall A (xs : list A) B z C z'
         (f : A -> list A -> B) (f' : A -> list A -> C),
    snd match xs with
        | [] => (z, z')
        | x :: xs => (f x xs, f' x xs)
        end = match xs with
              | [] => z'
              | x :: xs => f' x xs
              end.
Proof. induction xs; auto. Qed.

Section Refined.

Variable heap : Rep HSpec.

Lemma ByteStringHeap  : { adt : _ & refineADT ByteStringSpec adt }.
Proof.
  eexists.
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
    split.
      reflexivity.
    left; intuition.
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
    unfold buffer_cons, simply_widen_region,
           make_room_by_shifting_up, make_room_by_growing_buffer.
    simplify with monad laws; simpl.
    finish honing.
  }
  {
    simplify with monad laws.
    etransitivity.
      eapply (refine_skip2 (dummy:=buffer_uncons r_n)).
    etransitivity.
      apply refine_under_bind; intros; simpl.
      pose proof H1.
      eapply buffer_uncons_impl in H1; eauto.
      rewrite fst_match_list, snd_match_list.
      rewrite <- H1.
      refine pick val (fst a).
        simplify with monad laws.
        rewrite <- surjective_pairing.
        finish honing.
      eapply buffer_uncons_sound; eauto.
    simplify with monad laws.
    unfold buffer_uncons.
    finish honing.
  }
  apply reflexivityT.
Defined.

Definition ByteStringHeap' := Eval simpl in projT1 ByteStringHeap.
Print ByteStringHeap'.

End Refined.

End ByteStringHeap.
