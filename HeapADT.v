Require Import
  Coq.Sets.Ensembles
  Coq.NArith.NArith
  Fiat.ADT
  Fiat.ADTNotation
  Fiat.ADTInduction
  Here.FromADT
  Here.Heap.

Section HeapADT.

Variable Word8 : Type.
Variable Zero  : Word8.

Definition MemoryBlock := MemoryBlock Word8.
Definition HeapSpec    := @HeapSpec Word8.

Lemma empty_fromADT r :
  refine (callCons HeapSpec emptyS) (ret r) -> fromADT HeapSpec r.
Proof. check constructor (fromCons HeapSpec emptyS r). Qed.

Open Scope N_scope.

Lemma alloc_fromADT r :
  fromADT HeapSpec r
    -> forall (len : N | 0 < len) v,
         refine (callMeth HeapSpec allocS r len) (ret v)
    -> fromADT HeapSpec (fst v).
Proof. intros; check method (fromMeth HeapSpec allocS r (fst v)). Qed.

Lemma free_fromADT r :
  fromADT HeapSpec r
    -> forall (addr : N) v,
         refine (callMeth HeapSpec freeS r addr) (ret v)
    -> fromADT HeapSpec (fst v).
Proof. intros; check method (fromMeth HeapSpec freeS r (fst v)). Qed.

Lemma realloc_fromADT r :
  fromADT HeapSpec r
    -> forall (addr : N) (len : N | 0 < len) v,
         refine (callMeth HeapSpec reallocS r addr len) (ret v)
    -> fromADT HeapSpec (fst v).
Proof. intros; check method (fromMeth HeapSpec reallocS r (fst v)). Qed.

Lemma peek_fromADT r :
  fromADT HeapSpec r
    -> forall (addr : N) v,
         refine (callMeth HeapSpec peekS r addr) (ret v)
    -> fromADT HeapSpec (fst v).
Proof. intros; check method (fromMeth HeapSpec peekS r (fst v)). Qed.

Lemma poke_fromADT r :
  fromADT HeapSpec r
    -> forall (addr : N) w v,
         refine (callMeth HeapSpec pokeS r addr w) (ret v)
    -> fromADT HeapSpec (fst v).
Proof. intros; check method (fromMeth HeapSpec pokeS r (fst v)). Qed.

Lemma memcpy_fromADT r :
  fromADT HeapSpec r
    -> forall (addr : N) (addr2 : N) (len : N | 0 < len) v,
         refine (callMeth HeapSpec memcpyS r addr addr2 len) (ret v)
    -> fromADT HeapSpec (fst v).
Proof. intros; check method (fromMeth HeapSpec memcpyS r (fst v)). Qed.

Lemma memset_fromADT r :
  fromADT HeapSpec r
    -> forall (addr : N) (len : N | 0 < len) (w : Word8) v,
         refine (callMeth HeapSpec memsetS r addr len w) (ret v)
    -> fromADT HeapSpec (fst v).
Proof. intros; check method (fromMeth HeapSpec memsetS r (fst v)). Qed.

Require Import
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Theorem HeapSpecADT : { adt : _ & refineADT HeapSpec adt }.
Proof.
  eexists.
  hone representation using
    (fun (or : Rep HeapSpec)
         (nr : { r : Rep HeapSpec | fromADT HeapSpec r }) => or = ` nr).
  resolve_constructor (@empty Word8) empty_fromADT.
  resolve_method r_n (@alloc Word8 (` r_n) d)
                     (@alloc_fromADT _ (proj2_sig r_n) d).
  resolve_method r_n (@free Word8 (` r_n) d)
                     (@free_fromADT _ (proj2_sig r_n) d).
  resolve_method r_n (@realloc Word8 (` r_n) d d0)
                     (@realloc_fromADT _ (proj2_sig r_n) d d0).
  resolve_method r_n (@peek Word8 (` r_n) d)
                     (@peek_fromADT _ (proj2_sig r_n) d).
  resolve_method r_n (@poke Word8 (` r_n) d d0)
                     (@poke_fromADT _ (proj2_sig r_n) d d0).
  resolve_method r_n (@memcpy Word8 (` r_n) d d0 d1)
                     (@memcpy_fromADT _ (proj2_sig r_n) d d0 d1).
  resolve_method r_n (@memset Word8 (` r_n) d d0 d1)
                     (@memset_fromADT _ (proj2_sig r_n) d d0 d1).
  apply reflexivityT.
Defined.

End HeapADT.
