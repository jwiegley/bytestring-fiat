Require Import
  ByteString.Tactics
  ByteString.Nomega
  ByteString.Memory
  ByteString.FMapExt
  ByteString.Fiat
  ByteString.FromADT
  ByteString.Heap
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Generalizable All Variables.

Module HeapADT (M : WSfun N_as_DT).

Module Import Heap := Heap M.

Open Scope N_scope.

Lemma empty_fromADT r :
  callCons HeapSpec emptyS ↝ r -> fromADT HeapSpec r.
Proof. check constructor (fromCons HeapSpec emptyS r). Qed.

Lemma alloc_fromADT r :
  fromADT HeapSpec r
    -> forall (len : Size | 0 < len) v,
         callMeth HeapSpec allocS r len ↝ v
    -> fromADT HeapSpec (fst v).
Proof. intros; check method (fromMeth HeapSpec allocS r (fst v)). Qed.

Lemma free_fromADT r :
  fromADT HeapSpec r
    -> forall (addr : Ptr) v,
         callMeth HeapSpec freeS r addr ↝ v
    -> fromADT HeapSpec (fst v).
Proof. intros; check method (fromMeth HeapSpec freeS r (fst v)). Qed.

Lemma realloc_fromADT r :
  fromADT HeapSpec r
    -> forall (addr : Ptr) (len : Size | 0 < len) v,
         callMeth HeapSpec reallocS r addr len ↝ v
    -> fromADT HeapSpec (fst v).
Proof. intros; check method (fromMeth HeapSpec reallocS r (fst v)). Qed.

Lemma peek_fromADT r :
  fromADT HeapSpec r
    -> forall (addr : Ptr) v,
         callMeth HeapSpec peekS r addr ↝ v
    -> fromADT HeapSpec (fst v).
Proof. intros; check method (fromMeth HeapSpec peekS r (fst v)). Qed.

Lemma poke_fromADT r :
  fromADT HeapSpec r
    -> forall (addr : Ptr) w v,
         callMeth HeapSpec pokeS r addr w ↝ v
    -> fromADT HeapSpec (fst v).
Proof. intros; check method (fromMeth HeapSpec pokeS r (fst v)). Qed.

Lemma memcpy_fromADT r :
  fromADT HeapSpec r
    -> forall (addr : Ptr) (addr2 : Ptr) (len : Size) v,
         callMeth HeapSpec memcpyS r addr addr2 len ↝ v
    -> fromADT HeapSpec (fst v).
Proof. intros; check method (fromMeth HeapSpec memcpyS r (fst v)). Qed.

Lemma memset_fromADT r :
  fromADT HeapSpec r
    -> forall (addr : Ptr) (len : Size) (w : Word) v,
         callMeth HeapSpec memsetS r addr len w ↝ v
    -> fromADT HeapSpec (fst v).
Proof. intros; check method (fromMeth HeapSpec memsetS r (fst v)). Qed.

Theorem HeapSpecADT : { adt : _ & refineADT HeapSpec adt }.
Proof.
  eexists.
  hone representation using
    (fun (or : Rep HeapSpec)
         (nr : { r : Rep HeapSpec | fromADT HeapSpec r }) => or = ` nr).
  resolve_constructor empty empty_fromADT.
  resolve_method r_n (alloc (` r_n) d)
                     (@alloc_fromADT _ (proj2_sig r_n) d).
  resolve_method r_n (free (` r_n) d)
                     (@free_fromADT _ (proj2_sig r_n) d).
  resolve_method r_n (realloc (` r_n) d d0)
                     (@realloc_fromADT _ (proj2_sig r_n) d d0).
  resolve_method r_n (peek (` r_n) d)
                     (@peek_fromADT _ (proj2_sig r_n) d).
  resolve_method r_n (poke (` r_n) d d0)
                     (@poke_fromADT _ (proj2_sig r_n) d d0).
  resolve_method r_n (memcpy (` r_n) d d0 d1)
                     (@memcpy_fromADT _ (proj2_sig r_n) d d0 d1).
  resolve_method r_n (memset (` r_n) d d0 d1)
                     (@memset_fromADT _ (proj2_sig r_n) d d0 d1).
  apply reflexivityT.
Defined.

End HeapADT.
