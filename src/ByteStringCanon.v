Require Import
  ByteString.Tactics
  ByteString.Memory
  ByteString.Nomega
  ByteString.Heap
  ByteString.ByteString
  ByteString.ByteStringHeap
  ByteString.Fiat
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Generalizable All Variables.

Module ByteStringFMap (M : WSfun N_as_DT).

Module Import ByteStringHeap := ByteStringHeap M.

Import HeapCanonical.
Import HeapADT.
Import Heap.
Import HeapState.
Import FMapExt.

Section Refined.

Definition cHeapRep := ComputationalADT.cRep (projT1 HeapCanonical).

Variable heap  : Rep HeapSpec.
Variable heap' : cHeapRep.

Definition Heap_AbsR (or : Rep HeapSpec) nr :=
  M.Equal (resvs or) (resvs (snd nr)) /\
  M.Equal (bytes or) (bytes (snd nr)) /\
  P.for_all (fun addr sz => addr + sz <=? fst nr) (resvs (snd nr)).

Variable heap_AbsR : Heap_AbsR heap heap'.

(* This style of computational refinement makes use of a separately refined
   heap. Another approach is to refine the heap methods directly, which would
   mean going directly to the metal (but would require replicating much of the
   proof word that is done in HeapFMap.v). *)

Record PS' := {
  ps'Heap : cHeapRep;

  ps'Buffer : N;
  ps'BufLen : N;

  ps'Offset : N;
  ps'Length : N
}.

Require Import ByteString.FromADT.

Record ByteString_Heap_AbsR or nr := {
  heap_match   : Heap_AbsR (psHeap or) (ps'Heap nr);
  buffer_match : psBuffer or = ps'Buffer nr;
  buflen_match : psBufLen or = ps'BufLen nr;
  offset_match : psOffset or = ps'Offset nr;
  length_match : psLength or = ps'Length nr
}.

Lemma refine_ByteString_Heap_AbsR :
  forall heap_resvs heap_bytes buffer buflen offset length B (k : _ -> Comp B),
    refine
      (r_n' <- { r_n0 : PS'
               | ByteString_Heap_AbsR
                   {| psHeap := {| resvs := heap_resvs
                                 ; bytes := heap_bytes |}
                    ; psBuffer := buffer
                    ; psBufLen := buflen
                    ; psOffset := offset
                    ; psLength := length |} r_n0 };
       k r_n')
      (resvs' <- {resvs' : M.t Size | M.Equal heap_resvs resvs'};
       bytes' <- {bytes' : M.t Word | M.Equal heap_bytes bytes'};
       brk'   <- {brk'   : N
                 | P.for_all (fun addr sz => addr + sz <=? brk') resvs' };
       k {| ps'Heap   := (brk', {| resvs := resvs'; bytes := bytes' |})
          ; ps'Buffer := buffer
          ; ps'BufLen := buflen
          ; ps'Offset := offset
          ; ps'Length := length |}).
Proof.
  intros; intros ??.
  destruct_computations.
  revert H2.
  remember (Build_PS' _ _ _ _ _) as P; intros.
  refine pick val P.
    apply computes_to_refine.
    simplify with monad laws.
    apply refine_computes_to.
    assumption.
  rewrite HeqP.
  firstorder.
Qed.

Ltac apply_ByteString_Heap_AbsR :=
  match goal with
    | [ H : ByteString_Heap_AbsR ?O ?N |- _ ] =>
      destruct H as
          [ [ resvs_match0 [ bytes_match0 for_all_matches0 ] ]
            buffer_match0 buflen_match0 offset_match0 length_match0 ],
          O as [ [ resvs_o bytes_o ]
                 psBuffer0 psBufLen0 psOffset0 psLength0 ];
      simpl in *;
      rewrite ?buffer_match0, ?buflen_match0, ?offset_match0, ?length_match0
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
        | [ |- refine (x <- { X : PS' | ByteString_Heap_AbsR _ X }; _) _ ] =>
          rewrite refine_ByteString_Heap_AbsR
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

Ltac fracture H :=
  repeat (
    try simplify with monad laws; simpl;
    match goal with
    | [ |- refine (If ?B Then ?T Else ?E) _ ] =>
      apply refine_If_Then_Else; [ fracture H | fracture H ]
    | [ |- refine (If ?B Then ?T Else ?E) _ ] =>
      subst H; apply refine_If_Then_Else; [ fracture H | fracture H ]
    | [ |- refine (x <- If ?B Then ?T Else ?E; _) _ ] =>
      rewrite refineEquiv_If_Then_Else_Bind
    | [ |- _ ] => idtac
    end).

Theorem ByteStringCanonical : FullySharpened (projT1 (ByteStringHeap heap)).
Proof.
  start sharpening ADT.

  hone representation using ByteString_Heap_AbsR.

  refine method ByteString.emptyS.
  {
    simplify with monad laws.
    refine pick val {| ps'Heap   := heap'
                     ; ps'Buffer := 0
                     ; ps'BufLen := 0
                     ; ps'Offset := 0
                     ; ps'Length := 0 |}.
      finish honing.
    firstorder.
  }

  refine method ByteString.consS.
  {
    apply_ByteString_Heap_AbsR.
    fracture H; unfold find_free_block.
    refine using ByteString_Heap_AbsR;
    refine pick val (fst (ps'Heap r_n)); eauto;
    try simplify with monad laws;
    try finish honing;
    refine using ByteString_Heap_AbsR.

    - refine pick val (fst (ps'Heap r_n) +
                       (ps'Length r_n + alloc_quantum)); eauto.
        simplify with monad laws.
        finish honing.

      rewrite <- remove_add.
      apply for_all_remove; relational.
      apply for_all_add_true; relational.
        simplify_maps.
      split; [|nomega].
      apply for_all_remove; relational.
      eapply for_all_impl; auto;
      relational; eauto; nomega.

    - rewrite resvs_match0.
      eapply for_all_impl; eauto;
      relational; nomega.

    - refine pick val (fst (ps'Heap r_n) + alloc_quantum); eauto.
        simplify with monad laws.
        finish honing.

      rewrite <- remove_add.
      apply for_all_add_true; relational.
        simplify_maps.
      split; [|nomega].
      apply for_all_remove; relational.
      eapply for_all_impl; auto;
      relational; eauto; nomega.

    - rewrite resvs_match0.
      eapply for_all_impl; eauto;
      relational; nomega.
  }

  refine method ByteString.unconsS.
  {
    apply_ByteString_Heap_AbsR.
    fracture H; refine using ByteString_Heap_AbsR.

    - refine pick val (Ifopt M.find (ps'Buffer r_n + ps'Offset r_n)
                                    (bytes (snd (ps'Heap r_n))) as v
                       Then v
                       Else Zero).
        simplify with monad laws.
        refine using ByteString_Heap_AbsR.
        refine pick val (fst (ps'Heap r_n)); eauto.
        simplify with monad laws.
        finish honing.

      intros.
      destruct (M.find _ _) eqn:Heqe; simpl.
        normalize.
        rewrite bytes_match0 in H.
        eapply F.MapsTo_fun; eauto.
      apply F.find_mapsto_iff in H.
      congruence.

    - refine pick val (fst (ps'Heap r_n)); eauto.
      simplify with monad laws.
      finish honing.
  }

  (** Apply some common functional optimizations. *)

  hone representation using eq.

  refine method ByteString.emptyS.
  {
    simplify with monad laws.
    finish honing.
  }

  refine method ByteString.consS.
  {
    rewrite !refine_If_Then_Else_ret.
    simplify with monad laws.
    refine pick eq.
    simplify with monad laws.
    rewrite !If_Then_Else_fst, !If_Then_Else_snd; simpl.

    replace (If 0 <? ps'Offset r_o
             Then ()
             Else (If ps'Length r_o + 1 <=? ps'BufLen r_o
                   Then ()
                   Else (If 0 <? ps'BufLen r_o
                         Then ()
                         Else ()))) with ().
      subst; finish honing.

    destruct (0 <? _); trivial; simpl.
    destruct (_ + 1 <=? _); trivial; simpl.
    destruct (0 <? _); trivial.
  }

  refine method ByteString.unconsS.
  {
    rewrite refine_If_Then_Else_ret.
    simplify with monad laws.
    refine pick eq.
    simplify with monad laws.
    rewrite !If_Then_Else_fst, !If_Then_Else_snd; simpl.
    rewrite If_Then_Else_pair.
    subst; finish honing.
  }

  finish_SharpeningADT_WithoutDelegation.
Defined.

End Refined.

End ByteStringFMap.
