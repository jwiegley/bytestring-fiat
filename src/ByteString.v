Require Import
  Fiat.ADT
  Fiat.ADTNotation
  ByteString.Memory.

(************************************************************************
 ** Semantics of the core Haskell ByteString data type in Fiat.        **
 ************************************************************************)

Open Scope string_scope.

Definition emptyS  := "empty".
Definition consS   := "cons".
Definition unconsS := "uncons".

Definition ByteStringSpec := Def ADT {
  rep := list Word,

  Def Constructor0 emptyS : rep := ret []%list,,

  Def Method1 consS (r : rep) (w : Word) : rep * unit :=
    ret (cons w r, tt),

  Def Method0 unconsS (r : rep) : rep * (option Word) :=
    ret (match r with
         | nil => (r, None)
         | cons x xs => (xs, Some x)
         end)

}%ADTParsing.

Definition ByteString := Rep ByteStringSpec.

Definition empty : Comp ByteString :=
  Eval simpl in callCons ByteStringSpec emptyS.

Definition cons (w : Word) (bs : ByteString) : Comp ByteString :=
  Eval simpl in (p <- callMeth ByteStringSpec consS bs w; ret (fst p)).

Definition uncons (bs : ByteString) : Comp (ByteString * option Word) :=
  Eval simpl in callMeth ByteStringSpec unconsS bs.
