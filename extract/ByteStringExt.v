Require Import
  ByteString.Lib.Fiat
  ByteString.Lib.Nomega
  ByteString.Memory
  ByteString.Heap
  ByteString.ByteString
  ByteString.ByteStringHeap
  (* ByteString.ByteStringCanon *)
  ByteString.FFI.ByteStringFFI
  ByteString.FFI.HaskellFFI
  Coq.Strings.Ascii
  Coq.Strings.String
  Coq.FSets.FMapList
  Coq.Structures.OrderedTypeEx.

Module Import M  := FMapList.Make(N_as_OT).
Module Import BM := ByteStringHeap M.

Import HeapCanonical.
Import Heap.
Import HeapState.

Definition impl := Eval simpl in projT1 HeapCanonical.

Definition crep := ComputationalADT.cRep impl.

Open Scope N_scope.

Definition emptyHeap   : crep :=
  Eval compute in CallMethod impl emptyS.
Definition allocHeap (r : crep) (len : Size | 0 < len) : crep * Ptr Word :=
  Eval compute in CallMethod impl allocS r len.
Definition freeHeap (r : crep) (addr : Ptr Word) : crep :=
  Eval compute in CallMethod impl freeS r addr.
Definition reallocHeap (r : crep) (addr : Ptr Word) (len : Size | 0 < len) :
  crep * Ptr Word :=
  Eval compute in CallMethod impl reallocS r addr len.
Definition peekHeap (r : crep) (addr : Ptr Word) (off : Size) : crep * Word :=
  Eval compute in CallMethod impl peekS r addr off.
Definition pokeHeap (r : crep) (addr : Ptr Word) (off : Size) (w : Word) : crep :=
  Eval compute in CallMethod impl pokeS r addr off w.
Definition memcpyHeap (r : crep) (addr1 : Ptr Word) (off1 : Size)
           (addr2 : Ptr Word) (off2 : Size) (len : Size) :
  crep :=
  Eval compute in CallMethod impl memcpyS r addr1 off1 addr2 off2 len.
Definition memsetHeap (r : crep) (addr : Ptr Word) (off : Size) (len : Size)
           (w : Word) : crep :=
  Eval compute in CallMethod impl memsetS r addr off len w.

Section ByteStringExt.

Variable heap  : Rep HeapSpec.
Variable heap' : ComputationalADT.cRep (projT1 HeapCanonical).

(* Variable heap_AbsR : Heap_AbsR heap heap'. *)

(* Axiom one_Haskell_heap : forall h1 h2 : Rep HeapSpec, h1 = h2. *)

(* Definition BSimpl' := *)
(*   projT1 (@ByteStringCanonical heap heap' heap_AbsR one_Haskell_heap). *)
(* Definition BSimpl := Eval simpl in BSimpl'. *)

(* Definition BScrep := ComputationalADT.cRep BSimpl. *)

Open Scope N_scope.

(* Definition emptyBS   : BScrep := *)
(*   Eval compute in CallMethod BSimpl emptyS. *)
(* Definition packBS (xs : list Word) : BScrep := *)
(*   Eval compute in CallMethod BSimpl packS xs. *)
(* Definition unpackBS (r : BScrep) : BScrep * list Word := *)
(*   Eval compute in CallMethod BSimpl unpackS r. *)
(* Definition consBS (r : BScrep) (w : Word) : BScrep := *)
(*   Eval compute in CallMethod BSimpl consS r w. *)
(* Definition unconsBS (r : BScrep) : BScrep * option Word := *)
(*   Eval compute in CallMethod BSimpl unconsS r. *)
(* Definition appendBS (r1 r2 : BScrep) : BScrep := *)
(*   Eval compute in CallMethod BSimpl appendS r1 r2. *)

End ByteStringExt.

(** Eq *)

Extraction Implicit eq_rect   [ x y ].
Extraction Implicit eq_rect_r [ x y ].
Extraction Implicit eq_rec    [ x y ].
Extraction Implicit eq_rec_r  [ x y ].

Extract Inlined Constant eq_rect   => "".
Extract Inlined Constant eq_rect_r => "".
Extract Inlined Constant eq_rec    => "".
Extract Inlined Constant eq_rec_r  => "".

(** Ord *)

Extract Inductive comparison =>
  "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].

(** Int *)

Extract Inductive Datatypes.nat => "Prelude.Int"
  ["(0 :: Prelude.Int)" "HString.nsucc"]
  "(\fO fS n -> if n Prelude.<= 0 then fO () else fS (Prelude.pred n))".

Extract Inlined Constant EqNat.beq_nat         =>
  "((Prelude.==) :: Prelude.Int -> Prelude.Int -> Prelude.Bool)".
Extract Inlined Constant Compare_dec.le_lt_dec =>
  "((Prelude.<=) :: Prelude.Int -> Prelude.Int -> Prelude.Bool)".
Extract Inlined Constant Compare_dec.le_gt_dec => "(Prelude.>)".
Extract Inlined Constant Compare_dec.le_dec    =>
  "((Prelude.<=) :: Prelude.Int -> Prelude.Int -> Prelude.Bool)".
Extract Inlined Constant Compare_dec.lt_dec    => "(Prelude.<)".
Extract Inlined Constant Compare_dec.leb       =>
  "((Prelude.<=) :: Prelude.Int -> Prelude.Int -> Prelude.Bool)".

Extract Inlined Constant plus  => "(Prelude.+)".
Extract Inlined Constant minus => "(Prelude.-)".
Extract Inlined Constant mult  => "(Prelude.* )".
Extract Inlined Constant pred  =>
  "(Prelude.pred :: Prelude.Int -> Prelude.Int)".
Extract Inlined Constant min   => "Prelude.min".
Extract Inlined Constant max   =>
  "(Prelude.max :: Prelude.Int -> Prelude.Int -> Prelude.Int)".

(** Z, positive, Q *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.

Extract Inductive positive => "Prelude.Int" [
  "(\x -> 2 Prelude.* x Prelude.+ 1)"
  "(\x -> 2 Prelude.* x)"
  "1" ]
  "(\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))".

Extract Inductive Z => "Prelude.Int" [ "0" "(\x -> x)" "Prelude.negate" ]
  "(\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))".

Extract Inlined Constant Z.add       => "(Prelude.+)".
Extract Inlined Constant Z.sub       => "(Prelude.-)".
Extract Inlined Constant Z.mul       => "(Prelude.*)".
Extract Inlined Constant Z.max       => "Prelude.max".
Extract Inlined Constant Z.min       => "Prelude.min".
Extract Inlined Constant Z_ge_lt_dec => "(Prelude.>=)".
Extract Inlined Constant Z_gt_le_dec => "(Prelude.>)".

Extract Constant Z.div =>
  "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
Extract Constant Z.modulo =>
  "(\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)".

Extract Inductive N => "Prelude.Int" [ "0" "(\x -> x)" ]
  "(\fO fP n -> if n Prelude.== 0 then fO () else fP n)".

Extract Inlined Constant N.add       => "(Prelude.+)".
Extract Inlined Constant N.sub       => "(Prelude.-)".
Extract Inlined Constant N.mul       => "(Prelude.*)".
Extract Inlined Constant N.max       => "Prelude.max".
Extract Inlined Constant N.min       => "Prelude.min".
Extract Inlined Constant N.ltb       => "(Prelude.<)".
Extract Inlined Constant N.leb       => "(Prelude.<=)".
Extract Inlined Constant N.of_nat    => "".

Extract Inductive Q => "(GHC.Real.Ratio Prelude.Int)" [ "(GHC.Real.:%)" ].

Extract Inlined Constant Qplus  => "(Prelude.+)".
Extract Inlined Constant Qminus => "(Prelude.-)".
Extract Inlined Constant Qmult  => "(Prelude.*)".

Extract Constant Qdiv =>
  "(\n m -> if m Prelude.== 0 then 0 else n Prelude./ m)".

(** Bool *)

Extract Inductive bool    => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].

(* Extract Inlined Constant Equality.bool_beq => *)
(*   "((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool)". *)
Extract Inlined Constant Bool.bool_dec     =>
  "((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool)".

Extract Inlined Constant Sumbool.sumbool_of_bool => "".

Extract Inlined Constant negb => "Prelude.not".
Extract Inlined Constant orb  => "(Prelude.||)".
Extract Inlined Constant andb => "(Prelude.&&)".

(** Maybe *)

Extract Inductive option => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive sumor  => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].

(** Either *)

Extract Inductive sum => "Prelude.Either" ["Prelude.Left" "Prelude.Right"].

(** List *)

Extract Inductive list => "[]" ["[]" "(:)"].

Extract Inlined Constant app             => "(Prelude.++)".
Extract Inlined Constant List.map        => "Prelude.map".
Extract         Constant List.fold_left  => "\f l z -> Data.List.foldl f z l".
Extract Inlined Constant List.fold_right => "Data.List.foldr".
Extract Inlined Constant List.find       => "Data.List.find".
Extract Inlined Constant List.length     =>
  "(Data.List.length :: [a] -> Prelude.Int)".

(** Tuple *)

Extract Inductive prod => "(,)" ["(,)"].
Extract Inductive sigT => "(,)" ["(,)"].

Extract Inlined Constant fst    => "Prelude.fst".
Extract Inlined Constant snd    => "Prelude.snd".
Extract Inlined Constant projT1 => "Prelude.fst".
Extract Inlined Constant projT2 => "Prelude.snd".

Extract Inlined Constant proj1_sig => "".

(** Unit *)

Extract Inductive unit => "()" ["()"].

(** Vector *)

Require Import Coq.Vectors.Vector.

Extract Inductive Vector.t =>
  "HString.Vector" ["HString.Nil" "HString.Cons"].
Extract Inductive VectorDef.t =>
  "HString.Vector" ["HString.Nil" "HString.Cons"].

(**************************************************************************)
(* The following extraction constants are only valid for Coq 8.4, and     *)
(* are needed there to workaround an incorrect use of [unsafeCoerce],     *)
(* which results in a core dump when attempting to evaluate a certain     *)
(* thunk.                                                                 *)
(*                                                                        *)
(* These are not only not needed in 8.5, but will actually cause          *)
(* compilation errors there, because the [unsafeCoerce] statements are    *)
(* no longer used, resulting in type mismatches with the [()] type that   *)
(* is used here.                                                          *)
(**************************************************************************)
(* COQ 8.4 START HERE                                                     *)
(**************************************************************************)

(*
Extract Constant ilist.ilist "a" "b" => "()".

Extract Constant ilist.icons    =>
  "\_ _ _ x xs -> unsafeCoerce (x:unsafeCoerce xs)".
Extract Constant ilist.inil     => "unsafeCoerce []".
Extract Constant ilist.ilist_hd =>
  "\_ _ -> unsafeCoerce Prelude.. Prelude.head Prelude.. unsafeCoerce".
Extract Constant ilist.ilist_tl =>
  "\_ _ -> unsafeCoerce Prelude.. Prelude.tail Prelude.. unsafeCoerce".

Extract Constant ilist.ith =>
  "Data.Function.fix Prelude.$ \f _ _ v n ->
  case unsafeCoerce v of
    Build_prim_prod x xs ->
      case n of F1 _    -> x
                FS _ n' -> f __ __ xs n'".

Extract Constant ilist2.ilist2 "a" "b" => "()".

Extract Constant ilist2.icons2    =>
  "\_ _ _ x xs -> unsafeCoerce (x:unsafeCoerce xs)".
Extract Constant ilist2.inil2     => "unsafeCoerce []".
Extract Constant ilist2.ilist2_hd =>
  "\_ _ -> unsafeCoerce Prelude.. Prelude.head Prelude.. unsafeCoerce".
Extract Constant ilist2.ilist2_tl =>
  "\_ _ -> unsafeCoerce Prelude.. Prelude.tail Prelude.. unsafeCoerce".

Extract Constant ilist2.ith2 =>
  "Data.Function.fix Prelude.$ \f _ _ v n ->
  case n of F1 _    -> (unsafeCoerce v) Prelude.!! 0
            FS _ n' -> case unsafeCoerce v of
                         []     -> __
                         (x:xs) -> f __ __ (unsafeCoerce xs) n'".
*)

(**************************************************************************)
(* COQ 8.4 END HERE                                                       *)
(**************************************************************************)

(** String *)

Extract Inductive string => "Prelude.String" ["[]" "(:)"].
Extract Inductive ascii  => "Prelude.Char" ["HString.asciiToChar"]
  "HString.foldChar".

Extract Inlined Constant ascii_of_nat => "Data.Char.chr".
Extract Inlined Constant nat_of_ascii => "Data.Char.ord".
Extract Inlined Constant ascii_of_N   => "Data.Char.chr".
Extract Inlined Constant ascii_of_pos => "Data.Char.chr".

(** Haskell IO *)

Module Import BS  := ByteStringFFI M.
Module Import FFI := HaskellFFI M.

(** Fiat *)

Extract Inlined Constant FFI.Let_                => "(Data.Function.&)".
Extract Inlined Constant Common.If_Then_Else     => "(\c t e -> if c then t else e)".
Extract Inlined Constant Common.If_Opt_Then_Else => "(\c t e -> Data.Maybe.maybe e t c)".

Extract Constant Word => "Data.Word.Word8".

Extract Inlined Constant Zero => "0".

Extract Constant IO  "a" => "Prelude.IO a".
Extract Constant Ptr "a" => "Foreign.ForeignPtr.ForeignPtr a".

Extract Inlined Constant unsafeDupablePerformIO =>
  "System.IO.Unsafe.unsafeDupablePerformIO".

Extract Inlined Constant fmapIO   => "Prelude.fmap".
Extract Inlined Constant bindIO   => "(GHC.Base.>>=)".
Extract Inlined Constant returnIO => "Prelude.return".
Extract Inlined Constant malloc   => "GHC.ForeignPtr.mallocPlainForeignPtrBytes".
(* Extract Inlined Constant free     => "Prelude.undefined". *)
(* Extract Inlined Constant realloc  => "Prelude.undefined". *)
Extract Inlined Constant peek     =>
  "(\p off -> Foreign.ForeignPtr.withForeignPtr p (\ptr -> Foreign.Storable.peekByteOff ptr off))".
Extract Inlined Constant poke     =>
  "(\p off w -> Foreign.ForeignPtr.withForeignPtr p (\ptr -> Foreign.Storable.pokeByteOff ptr off w))".
Extract Inlined Constant memcpy   =>
  "(\p1 o1 p2 o2 sz -> Foreign.ForeignPtr.withForeignPtr p1 (\ptr1 -> Foreign.ForeignPtr.withForeignPtr p2 (\ptr2 -> Foreign.Marshal.Utils.copyBytes (Foreign.Ptr.plusPtr ptr2 o2) (Foreign.Ptr.plusPtr ptr1 o1) sz)))".
Extract Inlined Constant memset   =>
  "(\p off len w -> Foreign.ForeignPtr.withForeignPtr p (\ptr -> Foreign.Marshal.Utils.fillBytes (Foreign.Ptr.plusPtr ptr off) len w))".
Extract Inlined Constant read     =>
  "(\p off len -> Foreign.ForeignPtr.withForeignPtr p (\ptr -> Foreign.Marshal.Array.peekArray len (Foreign.Ptr.plusPtr ptr off)))".
Extract Inlined Constant write    =>
  "(\p off xs -> Foreign.ForeignPtr.withForeignPtr p (\ptr -> HString.pokeArray' (Foreign.Ptr.plusPtr ptr off) xs))".

Extract Inlined Constant nullPtr  =>
  "(System.IO.Unsafe.unsafePerformIO (Foreign.ForeignPtr.newForeignPtr_ Foreign.Ptr.nullPtr))".
Extract Inlined Constant plusPtr  => "Foreign.Ptr.plusPtr".
Extract Inlined Constant minusPtr => "Foreign.Ptr.minusPtr".

Extract Inlined Constant eqbPtr   => "(Prelude.==)".
Extract Inlined Constant eqdecPtr => "(Prelude.==)".
Extract Inlined Constant ltbPtr   => "(Prelude.<)".
Extract Inlined Constant lebPtr   => "(Prelude.<=)".

(** Final extraction *)

Extraction Language Haskell.

Unset Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction Optimize.
Set Extraction AccessOpaque.

Extraction "Internal.hs"
  emptyHeap

  (* emptyBS *)
  (* packBS *)
  (* unpackBS *)
  (* consBS *)
  (* unconsBS *)
  (* appendBS *)

  ghcEmptyDSL'
  ghcPackDSL'
  ghcUnpackDSL'
  ghcConsDSL'
  ghcUnconsDSL'
  ghcAppendDSL'.
