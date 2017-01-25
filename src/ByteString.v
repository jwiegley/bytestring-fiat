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
Definition appendS := "append".

Definition ByteStringSpec := Def ADT {
  rep := list Word,

  Def Constructor0 emptyS : rep := ret []%list,

  Def Method1 consS (r : rep) (w : Word) : rep :=
    ret (cons w r),

  Def Method0 unconsS (r : rep) : rep * (option Word) :=
    ret (match r with
         | nil => (r, None)
         | cons x xs => (xs, Some x)
         end),

  Def Binary Method0 appendS (r1 : rep) (r2 : rep) : rep :=
    ret (r1 ++ r2)%list

}%ADTParsing.

Definition ByteString := Rep ByteStringSpec.

Definition empty : Comp ByteString :=
  Eval simpl in callMeth ByteStringSpec emptyS.

Definition cons (w : Word) (bs : ByteString) : Comp ByteString :=
  Eval simpl in (callMeth ByteStringSpec consS bs w).

Definition uncons (bs : ByteString) : Comp (ByteString * option Word) :=
  Eval simpl in callMeth ByteStringSpec unconsS bs.

Definition append (bs1 bs2 : ByteString) : Comp ByteString :=
  Eval simpl in callMeth ByteStringSpec appendS bs1 bs2.
