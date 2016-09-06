Require Import
  ByteString.Fiat
  ByteString.FromADT
  ByteString.Heap
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Module HeapADT (M : WSfun N_as_DT).

Module Import Heap := Heap M.

Theorem HeapSpecADT : { adt : _ & refineADT HeapSpec adt }.
Proof.
  eexists.
  hone representation using
    (fun (or : Rep HeapSpec)
         (nr : { r : Rep HeapSpec | fromADT HeapSpec r }) => or = ` nr).
  resolve constructor (HeapSpec@@emptyS).
  resolve method (HeapSpec@allocS).
  resolve method (HeapSpec@freeS).
  resolve method (HeapSpec@reallocS).
  resolve method (HeapSpec@peekS).
  resolve method (HeapSpec@pokeS).
  resolve method (HeapSpec@memcpyS).
  resolve method (HeapSpec@memsetS).
  apply reflexivityT.
Defined.

End HeapADT.
