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
  ps'Heap : ComputationalADT.cRep (projT1 HeapImpl);

  ps'Buffer : N;
  ps'BufLen : N;

  ps'Offset : N;
  ps'Length : N
}.

Variable heap' : ComputationalADT.cRep (projT1 HeapImpl).
Variable AbsR : Heap_AbsR (` heap) heap'.

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

(* Strip away the proofy bits. *)
Lemma ByteStringStrip :
  { adt : _ & refineADT (projT1 (ByteStringHeap heap)) adt }.
Proof.
  eexists.
  hone representation using
       (fun (or : PS) (nr : PS') =>
          Heap_AbsR (` (psHeap or)) (ps'Heap nr) /\
          psBuffer or = ps'Buffer nr /\
          psBufLen or = ps'BufLen nr /\
          psOffset or = ps'Offset nr /\
          psLength or = ps'Length nr);
  try simplify with monad laws; simpl.
  {
    refine pick val {| ps'Heap   := heap'
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
    rewrite H1; clear H1.
    rewrite H2; clear H2.
    rewrite H3; clear H3.
    rewrite H4; clear H4.
    rewrite refineEquiv_If_Then_Else_Bind.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.
      unfold poke'; simpl.
      remove_dependency; simpl.
      etransitivity.
        apply refine_under_bind; intros.
        rewrite refine_pick_PS'.
        simplify with monad laws.
        finish honing.
      simpl.
      rewrite
        (Heap_refine_poke
           H0 _ _
           (fun u =>
              r_n' <- { r_n0 : PS' |
                        fst u             = ps'Heap   r_n0 /\
                        ps'Buffer r_n     = ps'Buffer r_n0 /\
                        ps'BufLen r_n     = ps'BufLen r_n0 /\
                        ps'Offset r_n - 1 = ps'Offset r_n0 /\
                        ps'Length r_n + 1 = ps'Length r_n0 };
              ret (r_n', ()))).
        remember (M.mapi _ _) as M.
        refine pick val
          {| ps'Heap   := (fst (ps'Heap r_n), M)
           ; ps'Buffer := ps'Buffer r_n
           ; ps'BufLen := ps'BufLen r_n
           ; ps'Offset := ps'Offset r_n - 1
           ; ps'Length := ps'Length r_n + 1 |}.
          simplify with monad laws.
          rewrite HeqM.
          finish honing.
        simpl; intuition.
      exact (proj2_sig (psHeap r_o)).
    rewrite refineEquiv_If_Then_Else_Bind.
    subst H.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.
      unfold memcpy', poke'; simpl.
      remove_dependency; simpl.
      setoid_rewrite refine_bind_dep_bind_ret; simpl.
      do 2 setoid_rewrite refine_bind_dep_ignore.
      setoid_rewrite refine_pick_PS'.
      etransitivity.
        apply refine_under_bind; intros.
        etransitivity.
          apply refine_under_bind; intros.
          simplify with monad laws.
          finish honing.
        simpl.
        finish honing.
      simpl.
      rewrite N.add_0_r.
(*
      rewrite
        (Heap_refine_poke
           _ _ _
           (fun u =>
              r_n' <- {r_n0 : PS' |
                       fst u             = ps'Heap   r_n0 /\
                       ps'Buffer r_n     = ps'Buffer r_n0 /\
                       ps'BufLen r_n     = ps'BufLen r_n0 /\
                       0                 = ps'Offset r_n0 /\
                       ps'Length r_n + 1 = ps'Length r_n0};
              ret (r_n', ()))).

        rewrite Heap_refine_poke.
      setoid_rewrite refine_bind_dep_ret; simpl.
      remove_dependency.
      simplify with monad laws; simpl.
*)
      admit.
    rewrite refineEquiv_If_Then_Else_Bind.
    apply refine_If_Then_Else.
      simplify with monad laws; simpl.
      unfold alloc', memcpy', poke'.
      remove_dependency.
      do 3 setoid_rewrite refine_bind_dep_bind_ret.
      simpl; remove_dependency.
      do 3 setoid_rewrite refine_bind_dep_ignore.
      unfold ByteStringHeap.buffer_cons_obligation_2.
      erewrite Heap_refine_alloc'; eauto.
        admit.
      exact (proj2_sig (psHeap r_o)).
    unfold allocate_buffer, alloc', poke'.
    simplify with monad laws; simpl.
    remove_dependency.
    setoid_rewrite refine_bind_dep_ret.
    autorewrite with monad laws; simpl.
    remove_dependency.
    unfold ByteStringHeap.buffer_cons_obligation_3.
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
      unfold peek'.
      remove_dependency.
      destruct (psHeap r_o); simpl in *; subst.
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
