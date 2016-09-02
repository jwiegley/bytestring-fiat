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
  ByteString.ByteStringHeap
  ByteString.Heap
  ByteString.HeapADT
  ByteString.HeapFMap
  ByteString.Nomega
  ByteString.Relations
  ByteString.Tactics
  ByteString.TupleEnsembles
  ByteString.Same_set
  ByteString.Within
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Generalizable All Variables.

Module ByteStringFMap (M : WSfun N_as_DT).

Module Import HF := HeapFMap M.

Import Within.
Import Within.Block.

Section Refined.

Variable heap : Rep HSpec.

(* This style of computational refinement makes use of a separately refined
   heap. Another approach is to refine the heap methods directly, which would
   mean going directly to the metal (but would require replicating much of the
   proof word that is done in HeapFMap.v). *)

Record PS' := {
  ps'Heap : Rep HeapSpec;

  ps'Buffer : N;
  ps'BufLen : N;

  ps'Offset : N;
  ps'Length : N
}.

(* Strip away the proofy bits. *)
Lemma ByteStringStrip :
  { adt : _ & refineADT (projT1 (ByteStringHeap heap)) adt }.
Proof.
  eexists.
  hone representation using
       (fun (or : PS) (nr : PS') =>
          ` (psHeap or) = ps'Heap nr /\
          psBuffer or = ps'Buffer nr /\
          psBufLen or = ps'BufLen nr /\
          psOffset or = ps'Offset nr /\
          psLength or = ps'Length nr);
  try simplify with monad laws; simpl.
  {
    refine pick val {| ps'Heap   := ` heap
                     ; ps'Buffer := 0
                     ; ps'BufLen := 0
                     ; ps'Offset := 0
                     ; ps'Length := 0 |}.
      finish honing.
    simpl; intuition.
  }
  {
    repeat match goal with
      [ H : _ /\ _ |- _ ] => destruct H
    end; subst.
    rewrite H1, H2, H3, H4.
    rewrite refineEquiv_If_Then_Else_Bind.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.
      unfold poke'; simpl.
      remove_dependency; simpl.
      rewrite H0.
      etransitivity.
        apply refine_under_bind; intros.
        refine pick val {| ps'Heap   := fst a
                         ; ps'Buffer := ps'Buffer r_n
                         ; ps'BufLen := ps'BufLen r_n
                         ; ps'Offset := ps'Offset r_n - 1
                         ; ps'Length := ps'Length r_n + 1 |}.
          simplify with monad laws.
          finish honing.
        intuition.
      simpl.
      finish honing.
    rewrite refineEquiv_If_Then_Else_Bind.
    subst H.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.
      unfold memcpy', poke'; simpl.
      remove_dependency; simpl.
      setoid_rewrite refine_bind_dep_bind_ret; simpl.
      do 2 setoid_rewrite refine_bind_dep_ignore.
      etransitivity.
        apply refine_under_bind; intros.
        etransitivity.
          apply refine_under_bind; intros.
          refine pick val {| ps'Heap   := fst a0
                           ; ps'Buffer := ps'Buffer r_n
                           ; ps'BufLen := ps'BufLen r_n
                           ; ps'Offset := 0
                           ; ps'Length := ps'Length r_n + 1 |}.
            simplify with monad laws.
            finish honing.
          intuition.
        simpl.
        finish honing.
      simpl.
      rewrite H0.
      finish honing.
    rewrite refineEquiv_If_Then_Else_Bind.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.
      unfold alloc', memcpy', poke'.
      remove_dependency; simpl.
      do 3 setoid_rewrite refine_bind_dep_bind_ret.
      simpl; remove_dependency.
      do 3 setoid_rewrite refine_bind_dep_ignore.
      unfold ByteStringHeap.buffer_cons_obligation_2.
      rewrite H0.
      etransitivity.
        apply refine_under_bind; intros.
        etransitivity.
          apply refine_under_bind; intros.
          etransitivity.
            apply refine_under_bind; intros.
            etransitivity.
              apply refine_under_bind; intros.
              refine pick val {| ps'Heap   := fst a2
                               ; ps'Buffer := snd a
                               ; ps'BufLen := ps'Length r_n +1
                               ; ps'Offset := 0
                               ; ps'Length := ps'Length r_n + 1 |}.
                simplify with monad laws.
                finish honing.
              intuition.
            simpl; finish honing.
          simpl; finish honing.
        simpl; finish honing.
      simpl; finish honing.
    unfold allocate_buffer, alloc', poke'.
    simplify with monad laws; simpl.
    remove_dependency; simpl.
    setoid_rewrite refine_bind_dep_ret.
    autorewrite with monad laws; simpl.
    remove_dependency.
    rewrite H0.
    unfold ByteStringHeap.buffer_cons_obligation_3.
    etransitivity.
      apply refine_under_bind; intros.
      remember (Map _ _) as M.
      refine pick val {| ps'Heap   := M
                       ; ps'Buffer := snd a
                       ; ps'BufLen := 1
                       ; ps'Offset := 0
                       ; ps'Length := 1 |}.
        simplify with monad laws.
        rewrite HeqM.
        finish honing.
      intuition.
    simpl.
    finish honing.
  }
  {
    repeat match goal with
      [ H : _ /\ _ |- _ ] => destruct H
    end; subst.
    rewrite H1, H2, H3, H4.
    rewrite refineEquiv_If_Then_Else_Bind.
    subst H.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.
      unfold peek'.
      remove_dependency.
      rewrite H0.
      etransitivity.
        apply refine_under_bind; intros.
        refine pick val {| ps'Heap   := ps'Heap r_n
                         ; ps'Buffer := ps'Buffer r_n
                         ; ps'BufLen := ps'BufLen r_n
                         ; ps'Offset := if ps'Length r_n =? 1
                                        then 0
                                        else ps'Offset r_n + 1
                         ; ps'Length := ps'Length r_n - 1 |}.
          simplify with monad laws.
          finish honing.
        intuition.
      simpl.
      finish honing.
    simplify with monad laws; simpl.
    rewrite H0.
    refine pick val r_n.
      simplify with monad laws; simpl.
      finish honing.
    intuition.
  }
  apply reflexivityT.
Defined.

Record CPS := {
  cpsHeap : ComputationalADT.cRep (projT1 HeapImpl);

  cpsBuffer : N;
  cpsBufLen : N;

  cpsOffset : N;
  cpsLength : N
}.

Variable cheap : ComputationalADT.cRep (projT1 HeapImpl).
Variable AbsR : Heap_AbsR (` heap) cheap.

(*
Lemma refine_pick_PS' : forall P a b c d,
  refine {r_n0 : PS' | P (ps'Heap r_n0) /\
                       a = ps'Buffer r_n0 /\
                       b = ps'BufLen r_n0 /\
                       c = ps'Offset r_n0 /\
                       d = ps'Length r_n0}
         (r_n' <- {r_n0 : N * M.t MemoryBlockC | P r_n0};
          {r_n0 : PS' | r_n' = ps'Heap   r_n0 /\
                        a = ps'Buffer r_n0 /\
                        b = ps'BufLen r_n0 /\
                        c = ps'Offset r_n0 /\
                        d = ps'Length r_n0}).
Proof.
Admitted.
*)

Lemma ByteStringFMap :
  { adt : _ & refineADT (projT1 ByteStringStrip) adt }.
Proof.
  eexists.
  hone representation using
       (fun (or : PS') (nr : CPS) =>
          Heap_AbsR (ps'Heap or) (cpsHeap nr) /\
          ps'Buffer or = cpsBuffer nr /\
          ps'BufLen or = cpsBufLen nr /\
          ps'Offset or = cpsOffset nr /\
          ps'Length or = cpsLength nr);
  try simplify with monad laws; simpl.
  {
    refine pick val {| cpsHeap   := cheap
                     ; cpsBuffer := 0
                     ; cpsBufLen := 0
                     ; cpsOffset := 0
                     ; cpsLength := 0 |}.
      finish honing.
    intuition.
  }
  {
    repeat match goal with
      [ H : _ /\ _ |- _ ] => destruct H
    end; subst.
    rewrite H1, H2, H3, H4.
    rewrite refineEquiv_If_Then_Else_Bind.
    apply refine_If_Then_Else.
      admit.
    rewrite refineEquiv_If_Then_Else_Bind.
    subst H.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.
      admit.
    rewrite refineEquiv_If_Then_Else_Bind.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.
      admit.
    simplify with monad laws; simpl.
    admit.
  }
  {
    repeat match goal with
      [ H : _ /\ _ |- _ ] => destruct H
    end; subst.
    rewrite H1, H2, H3, H4.
    rewrite refineEquiv_If_Then_Else_Bind.
    subst H.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.
      admit.
    simplify with monad laws; simpl.
    refine pick val r_n.
      simplify with monad laws; simpl.
      finish honing.
    intuition.
  }
  apply reflexivityT.
Admitted.

End Refined.

End ByteStringFMap.
