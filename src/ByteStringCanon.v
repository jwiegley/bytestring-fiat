Require Import
  ByteString.Lib.Tactics
  ByteString.Lib.Nomega
  ByteString.Lib.Fiat
  ByteString.Memory
  ByteString.Heap
  ByteString.ByteString
  ByteString.ByteStringHeap
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Module ByteStringFMap (M : WSfun Ptr_as_DT).

Module Import ByteStringHeap := ByteStringHeap M.

Import HeapCanonical.
Import Heap.
Import HeapState.
Import FMapExt.

Section Refined.

Definition cHeapRep := ComputationalADT.cRep (projT1 HeapCanonical).

Variable heap  : Rep HeapSpec.
Variable heap' : cHeapRep.

Definition Heap_AbsR (or : Rep HeapSpec) (nr : cHeapRep) :=
  M.Equal (resvs or) (resvs (snd nr)) /\
  M.Equal (bytes or) (bytes (snd nr)) /\
  P.for_all (fun addr sz =>
               lebPtr (A:=Word) (plusPtr (A:=Word) addr sz) (fst nr))
            (resvs (snd nr)).

Variable heap_AbsR : Heap_AbsR heap heap'.

(* This style of computational refinement makes use of a separately refined
   heap. Another approach is to refine the heap methods directly, which would
   mean going directly to the metal (but would require replicating much of the
   proof work that is done in HeapFMap.v). *)

Lemma refine_ByteString_Heap_AbsR :
  forall heap_resvs heap_bytes buffer buflen offset length B (k : _ -> Comp B),
    refineEquiv
      (r_n' <- { r_n0 : cHeapRep * PS
               | Heap_AbsR heap (fst r_n0) /\
                 pbuffer = snd r_n0 };
       k r_n')
      (resvs' <- {resvs' : M.t Size | M.Equal (resvs heap) resvs'};
       bytes' <- {bytes' : M.t Word | M.Equal (bytes heap) bytes'};
       brk'   <- {brk'   : N
                 | P.for_all (fun addr sz =>
                                lebPtr (A:=Word) (plusPtr (A:=Word) addr sz) brk')
                             resvs' };
       k ((brk', {| resvs := resvs'; bytes := bytes' |}),
          {| psBuffer := buffer
           ; psBufLen := buflen
           ; psOffset := offset
           ; psLength := length |})).
Proof.
  split.
    intros; intros ??.
    destruct_computations.
    revert H2.
    remember (makePS _ _ _ _) as P; intros.
    refine pick val ((x1, {| resvs := x; bytes := x0 |}), P).
      apply computes_to_refine.
      simplify with monad laws.
      apply refine_computes_to.
      assumption.
    rewrite HeqP.
    firstorder.
  intros; intros ??.
  destruct_computations.
  destruct H, x; simpl in *.
  subst.
  remember (makePS _ _ _ _) as P; intros.
  apply computes_to_refine.
  refine pick val (resvs (snd c)).
    simplify with monad laws.
    refine pick val (bytes (snd c)).
      simplify with monad laws.
      refine pick val (fst c).
        simplify with monad laws.
        assert ({| resvs := resvs (snd c); bytes := bytes (snd c) |} = snd c).
          destruct c; simpl.
          destruct h; reflexivity.
        rewrite H1, <- surjective_pairing.
        apply refine_computes_to; assumption.
      destruct H; intuition.
    destruct H; intuition.
  destruct H; intuition.
Qed.

Lemma refine_ByteString_Heap_AbsR' :
  forall heap_resvs heap_bytes buffer buflen offset length,
    refineEquiv
      { r_n0 : cHeapRep * PS
      | Heap_AbsR {| resvs := heap_resvs
                   ; bytes := heap_bytes |} (fst r_n0) /\
        {| psBuffer := buffer
         ; psBufLen := buflen
         ; psOffset := offset
         ; psLength := length |} = snd r_n0 }
      (resvs' <- {resvs' : M.t Size | M.Equal heap_resvs resvs'};
       bytes' <- {bytes' : M.t Word | M.Equal heap_bytes bytes'};
       brk'   <- {brk'   : N
                 | P.for_all (fun addr sz =>
                                lebPtr (A:=Word) (plusPtr (A:=Word) addr sz) brk')
                             resvs' };
       ret ((brk', {| resvs := resvs'; bytes := bytes' |}),
            {| psBuffer := buffer
             ; psBufLen := buflen
             ; psOffset := offset
             ; psLength := length |})).
Proof.
  split.
    intros; intros ??.
    destruct_computations.
    remember (makePS _ _ _ _) as P.
    apply computes_to_refine.
    refine pick val ((x1, {| resvs := x; bytes := x0 |}), P).
      apply refine_computes_to.
      constructor.
    rewrite HeqP.
    firstorder.
  intros; intros ??.
  destruct_computations.
  destruct H, v; simpl in *.
  subst.
  remember (makePS _ _ _ _) as P; intros.
  apply computes_to_refine.
  refine pick val (resvs (snd c)).
    simplify with monad laws.
    refine pick val (bytes (snd c)).
      simplify with monad laws.
      refine pick val (fst c).
        simplify with monad laws.
        assert ({| resvs := resvs (snd c); bytes := bytes (snd c) |} = snd c).
          destruct c; simpl.
          destruct h; reflexivity.
        rewrite H0, <- surjective_pairing.
        apply refine_computes_to.
        constructor.
      destruct H; intuition.
    destruct H; intuition.
  destruct H; intuition.
Qed.

Ltac apply_ByteString_Heap_AbsR :=
  match goal with
    | [ H : Heap_AbsR (fst ?O) (fst ?N) /\ snd ?X = snd ?Y |- _ ] =>
      destruct H as
          [ [ resvs_match0 [ bytes_match0 for_all_matches0 ] ] match0 ],
          O as [ [ resvs_o bytes_o ] ps_o ];
      simpl in *;
      rewrite ?match0
  end.

Tactic Notation "refine" "using" "ByteString_Heap_AbsR" :=
  match goal with
  | [ resvs_o : M.t Size, bytes_o : M.t Word |- _ ] =>
    match goal with
    | [ resvs_match0 : M.Equal resvs_o _
      , bytes_match0 : M.Equal bytes_o _ |- _ ] =>
      repeat (
        try simplify with monad laws; simpl;
        unfold find_free_block, allocate_buffer;
        match goal with
        | [ |- refine (x <- ret _; _) _ ] =>
          simplify with monad laws; simpl
        | [ |- refine (x <- { X : cHeapRep * PS
                            | Heap_AbsR _ (fst X) /\ _ = snd X }; _) _ ] =>
          rewrite refine_ByteString_Heap_AbsR
        | [ |- refine { X : cHeapRep * PS
                      | Heap_AbsR _ (fst X) /\ _ = snd X } _ ] =>
          rewrite refine_ByteString_Heap_AbsR'
        | [ |- refine (If ?B Then ?T Else ?E) _ ] =>
          apply refine_If_Then_Else
        | [ |- refine (x <- If ?B Then ?T Else ?E; _) _ ] =>
          rewrite refineEquiv_If_Then_Else_Bind
        | [ |- refine (x <- { X : M.t Size | M.Equal _ X }; _) _ ] =>
          try setoid_rewrite resvs_match0;
          refine pick val _
        | [ |- refine (x <- { X : M.t Word | M.Equal _ X }; _) _ ] =>
          try setoid_rewrite bytes_match0;
          refine pick val _
        end);
      try simplify with monad laws; simpl; eauto;
      try match goal with
      | [ |- M.Equal _ _ ] => reflexivity
      end
    end
  end.

Theorem ByteStringCanonical : FullySharpened (projT1 (ByteStringHeap heap)).
Proof.
  start sharpening ADT.

  hone representation using
       (fun (or : Comp (Rep HeapSpec) * PS) (nr : cHeapRep * PS) =>
          exists oh, fst or ↝ oh ->
            Heap_AbsR oh (fst nr) /\ snd or = snd nr).

  (* refine method ByteString.emptyS. *)
  {
    simplify with monad laws.
    refine pick val (heap', {| psBuffer := 0
                             ; psBufLen := 0
                             ; psOffset := 0
                             ; psLength := 0 |}).
      finish honing.
    firstorder.
  }

  (* refine method ByteString.consS. *)
  {
    admit.
(*
    apply_ByteString_Heap_AbsR.
    simplify_with_applied_monad_laws.
    fracture H; unfold find_free_block;
    refine using ByteString_Heap_AbsR;
    refine pick val (fst (fst r_n)); eauto;
    try simplify with monad laws;
    try finish honing;
    refine using ByteString_Heap_AbsR.

    - refine pick val (plusPtr (A:=Word) (fst (fst r_n))
                               (psLength (snd r_n) + alloc_quantum)); eauto.
        simplify with monad laws.
        finish honing.

      rewrite <- remove_add.
      apply for_all_remove; relational.
        rewrite H; reflexivity.
      apply for_all_add_true; relational; try nomega.
        simplify_maps.
      split; [|nomega].
      apply for_all_remove; relational; try nomega.
      eapply for_all_impl; auto;
      relational; eauto; nomega.

    - rewrite resvs_match0.
      eapply for_all_impl; eauto;
      relational; nomega.

    - refine pick val (plusPtr (A:=Word) (fst (fst r_n)) alloc_quantum); eauto.
        simplify with monad laws.
        finish honing.

      rewrite <- remove_add.
      apply for_all_add_true; relational; try nomega.
        simplify_maps.
      split; [|nomega].
      apply for_all_remove; relational; try nomega.
      eapply for_all_impl; auto;
      relational; eauto; nomega.

    - rewrite resvs_match0.
      eapply for_all_impl; eauto;
      relational; nomega.
*)
  }

  (* refine method ByteString.unconsS. *)
  {
    admit.
(*
    unfold buffer_uncons;
    apply_ByteString_Heap_AbsR;
    fracture H.
    refine using ByteString_Heap_AbsR.

    - refine pick val (Ifopt M.find (plusPtr (A:=Word) (psBuffer (snd r_n))
                                             (psOffset (snd r_n)))
                                    (bytes (snd (fst r_n))) as v
                       Then v
                       Else Zero).
        simplify with monad laws.
        refine using ByteString_Heap_AbsR.
        refine pick val (fst (fst r_n)); eauto.
        simplify with monad laws.
        finish honing.

      intros.
      destruct (M.find _ _) eqn:Heqe; simpl.
        normalize.
        rewrite bytes_match0.
        left; assumption.
      right; split; trivial.
      apply HeapState.F.not_find_in_iff.
      rewrite bytes_match0.
      assumption.

    - refine pick val r_n; eauto.
        simplify with monad laws.
        finish honing.
      split; trivial.
      constructor; auto.
*)
  }

  (* refine method ByteString.appendS. *)
  {
    unfold buffer_append, alloc, Bind2, find_free_block; simpl.

    admit.
(*
    rewrite !refine_IfDep_Then_Else_Bind,
            !refineEquiv_strip_IfDep_Then_Else.
    refine pick val (plusPtr (A:=Word) (fst (fst r_n)) 1).
      autorewrite with monad laws; simpl.
      etransitivity.
        apply refine_If_Then_Else; intros.
          rewrite refine_If_Then_Else_Bind.
          apply refine_If_Then_Else; intros.
            simplify with monad laws; simpl.
            destruct H0, H1.
            rewrite e, e0; clear e e0.
            destruct h, H1, h0, H4.
            refine pick val
              ((plusPtr (A:=Word) (fst (fst r_n))
                        (psLength (snd r_n) + psLength (snd r_n0) + 1),
                {| resvs := M.add (plusPtr (A:=Word) (fst (fst r_n)) 1)
                                  (psLength (snd r_n) + psLength (snd r_n0))
                                  (resvs (snd (fst r_n)))
                 ; bytes :=
                     copy_bytes (A:=Word)
                       (plusPtr (A:=Word) (psBuffer (snd r_n0))
                                (psOffset (snd r_n0)))
                       (plusPtr (A:=Word) (fst (fst r_n))
                                (psLength (snd r_n) + 1))
                       (psLength (snd r_n0))
                       (bytes (snd (fst r_n0)))
                       (copy_bytes (A:=Word)
                                   (plusPtr (A:=Word) (psBuffer (snd r_n))
                                            (psOffset (snd r_n)))
                                   (plusPtr (A:=Word) (fst (fst r_n)) 1)
                                   (psLength (snd r_n))
                                   (bytes (snd (fst r_n)))
                                   (bytes (snd (fst r_n)))) |}),
               {| psBuffer := plusPtr (A:=Word) (fst (fst r_n)) 1
                ; psBufLen := psLength (snd r_n) + psLength (snd r_n0)
                ; psOffset := 0
                ; psLength := psLength (snd r_n) + psLength (snd r_n0) |}).
              finish honing.
            intuition.
            rewrite_ptr.
            rewrite !N.add_comm with (n:=1).
            constructor; simpl.
              rewrite H0.
              reflexivity.
            split.
              rewrite H1, H4.
              reflexivity.
            clear -H2.
            apply for_all_add_true; relational; try nomega.
              destruct 1.
              apply_for_all; relational.
              nomega.
            split.
              remember (fun _ _ => _) as P.
              remember (fun _ _ =>
                          lebPtr (A:=Word) _ (plusPtr (A:=Word) _ (_ + _))) as P'.
              apply for_all_impl with (P:=P) (P':=P'); relational; nomega.
            nomega.
          simplify with monad laws; simpl.
          refine pick val r_n.
            finish honing.
          assumption.
        refine pick val r_n0.
          finish honing.
        assumption.
      intuition.
      rewrite !H3, !H4.
      rewrite !refine_If_Then_Else_ret.
      finish honing.
    intuition.
    rewrite H3, H4.
    destruct H2.
    rewrite H1.
    intuition.
    clear -H6.
    remember (fun _ _ => _) as P.
    remember (fun _ _ => negb _) as P'.
    apply for_all_impl with (P:=P) (P':=P'); relational; nomega.
*)
  }

  (** Apply some common functional optimizations, such as common subexpression
      elimination. *)

  hone representation using eq.

  (* refine method ByteString.emptyS. *)
  {
    simplify with monad laws.
    finish honing.
  }

  (* refine method ByteString.consS. *)
  {
    rewrite !refine_If_Then_Else_ret.
    simplify with monad laws.
    refine pick eq.
    rewrite !H0.
    finish honing.
  }

  (* refine method ByteString.unconsS. *)
  {
    rewrite refine_If_Then_Else_ret.
    simplify with monad laws.
    refine pick eq.
    simplify with monad laws.
    admit.
(*
    rewrite !If_Then_Else_fst, !If_Then_Else_snd; simpl.
    rewrite If_Then_Else_pair.
    subst; finish honing.
*)
  }

  (* refine method ByteString.appendS. *)
  {
    rewrite H0, H1.
    finish honing.
  }

  finish_SharpeningADT_WithoutDelegation.
Admitted.
(* Defined. *)

End Refined.

End ByteStringFMap.
