Require Import
  Fiat.ADT
  Fiat.ADTNotation
  ByteString.Heap.

Module ByteString (Mem : Memory).

(************************************************************************
 ** Semantics of the core Haskell ByteString data type in Fiat.        **
 ************************************************************************)

Definition emptyS  := "empty".
Definition consS   := "cons".
Definition unconsS := "uncons".

Definition ByteStringSpec := Def ADT {
  rep := list Mem.Word8,

  Def Constructor0 emptyS : rep := ret []%list,,

  Def Method1 consS (r : rep) (w : Mem.Word8) : rep * unit :=
    ret (cons w r, tt),
  Def Method0 unconsS (r : rep) : rep * (option Mem.Word8) :=
    match r with
    | nil => ret (r, None)
    | cons x xs => ret (xs, Some x)
    end

}%ADTParsing.

Definition ByteString := Rep ByteStringSpec.

Definition empty : Comp ByteString :=
  Eval simpl in callCons ByteStringSpec emptyS.

Definition cons (w : Mem.Word8) (bs : ByteString) : Comp ByteString :=
  Eval simpl in (p <- callMeth ByteStringSpec consS bs w; ret (fst p)).

Definition uncons (bs : ByteString) : Comp (ByteString * option Mem.Word8) :=
  Eval simpl in callMeth ByteStringSpec unconsS bs.

End ByteString.
