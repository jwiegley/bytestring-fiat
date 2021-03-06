Require Import
  ByteString.Lib.Tactics
  ByteString.Lib.Nomega
  ByteString.Lib.Fiat
  ByteString.Lib.TupleEnsembles
  ByteString.Lib.FunMaps
  ByteString.Lib.FromADT
  ByteString.Lib.HList
  ByteString.Memory
  ByteString.Heap
  ByteString.FFI.CompileFFI
  ByteString.ByteString
  ByteString.ByteStringHeap
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx
  Coq.Strings.String
  Hask.Data.Functor
  Hask.Control.Monad
  Hask.Control.Monad.Trans.FiatState
  Hask.Control.Monad.Free.

(****************************************************************************
 * Compile [buffer_cons] into a [ClientDSL] term
 ****************************************************************************)

Module ByteStringFFI (M : WSfun N_as_DT).

Module Import ByteStringHeap := ByteStringHeap M.
Module Import FunMaps := FunMaps N_as_DT M.

Import HeapCanonical.
Import Heap.

Definition buffer_empty :=
  ret {| psBuffer := nullPtr
       ; psBufLen := 0
       ; psOffset := 0
       ; psLength := 0 |}.

Hint Unfold buffer_empty.

Check "Compiling emptyDSL...".
Definition emptyDSL : reflect_ADT_DSL_computation HeapSpec buffer_empty.
Proof.
  Time compile_term.
Defined.

Corollary emptyDSL_correct :
  refine buffer_empty (denote HeapSpec (projT1 emptyDSL)).
Proof. intros; apply denote_refineEquiv. Qed.

Hint Unfold id.
Hint Unfold bind.
Hint Unfold Bind2.
Hint Unfold allocate_buffer.
Hint Unfold HeapState.find_free_block.
Hint Unfold ByteStringHeap.buffer_pack_obligation_1.
Hint Unfold buffer_pack.

Check "Compiling packDSL...".
Definition packDSL h xs:
  reflect_ADT_DSL_computation HeapSpec (buffer_pack xs h).
Proof.
  Local Opaque alloc.
  Local Opaque write.
  Time compile_term.
  Local Transparent alloc.
  Local Transparent write.
Defined.

Corollary packDSL_correct : forall (h : Rep HeapSpec) xs,
  refine (buffer_pack xs h)
         (denote HeapSpec (projT1 (packDSL h xs))).
Proof. intros; apply denote_refineEquiv. Qed.

Hint Unfold buffer_unpack.

Check "Compiling unpackDSL...".
Definition unpackDSL h bs:
  reflect_ADT_DSL_computation HeapSpec (buffer_unpack bs h).
Proof.
  Local Opaque read.
  Time compile_term.
  Local Transparent read.
Defined.

Corollary unpackDSL_correct : forall (h : Rep HeapSpec) bs,
  refine (buffer_unpack bs h)
         (denote HeapSpec (projT1 (unpackDSL h bs))).
Proof. intros; apply denote_refineEquiv. Qed.

Hint Unfold make_room_by_growing_buffer.
Hint Unfold make_room_by_shifting_up.
Hint Unfold ByteStringHeap.buffer_cons_obligation_2.
Hint Unfold poke_at_offset.
Hint Unfold buffer_cons.

Check "Compiling consDSL...".
Definition consDSL h ps w :
  reflect_ADT_DSL_computation HeapSpec (buffer_cons ps w h).
Proof.
  Local Opaque poke.
  Local Opaque alloc.
  Local Opaque peek.
  Local Opaque memcpy.
  Time compile_term.
  Local Transparent poke.
  Local Transparent alloc.
  Local Transparent peek.
  Local Transparent memcpy.
Defined.

Corollary consDSL_correct : forall (h : Rep HeapSpec) (bs : PS) w,
  refine (buffer_cons bs w h)
         (denote HeapSpec (projT1 (consDSL h bs w))).
Proof. intros; apply denote_refineEquiv. Qed.

Hint Unfold buffer_uncons.

Check "Compiling unconsDSL...".
Definition unconsDSL h ps:
  reflect_ADT_DSL_computation HeapSpec (buffer_uncons ps h).
Proof.
  Local Opaque poke.
  Local Opaque alloc.
  Local Opaque peek.
  Local Opaque memcpy.
  Time compile_term.
  Local Transparent poke.
  Local Transparent alloc.
  Local Transparent peek.
  Local Transparent memcpy.
Defined.

Corollary unconsDSL_correct : forall (h : Rep HeapSpec) (bs : PS),
  refine (buffer_uncons bs h)
         (denote HeapSpec (projT1 (unconsDSL h bs))).
Proof. intros; apply denote_refineEquiv. Qed.

Hint Unfold ByteStringHeap.buffer_append_obligation_1.
Hint Unfold buffer_append.

Definition reflect_ADT_DSL_computation_Pick :
  forall sig (adt : ADT sig) (P : Prop) A (k : () -> Comp A),
    P -> reflect_ADT_DSL_computation adt (k tt)
      -> reflect_ADT_DSL_computation adt (H <- { x : () | P }; k H).
Proof.
  intros.
  eapply reflect_ADT_DSL_computation_simplify; eauto.
  split; intros.
    refine pick val tt.
      simplify with monad laws.
      reflexivity.
    assumption.
  intros ??.
  destruct_computations.
  destruct x.
  assumption.
Defined.

Check "Compiling appendDSL...".
Definition appendDSL h ps1 ps2:
  reflect_ADT_DSL_computation HeapSpec (buffer_append ps1 ps2 h).
Proof.
  Local Opaque poke.
  Local Opaque alloc.
  Local Opaque peek.
  Local Opaque memcpy.
  Time compile_term.
  Local Transparent poke.
  Local Transparent alloc.
  Local Transparent peek.
  Local Transparent memcpy.
Defined.

Corollary appendDSL_correct : forall (h : Rep HeapSpec) (bs1 bs2 : PS),
  refine (buffer_append bs1 bs2 h)
         (denote HeapSpec (projT1 (appendDSL h bs1 bs2))).
Proof. intros; apply denote_refineEquiv. Qed.

End ByteStringFFI.
