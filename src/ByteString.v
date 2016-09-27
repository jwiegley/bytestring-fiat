Require Import
  Fiat.ADT
  Fiat.ADTNotation
  ByteString.Memory
  Hask.Control.Applicative.

(************************************************************************
 ** Semantics of the core Haskell ByteString data type in Fiat.        **
 ************************************************************************)

Open Scope string_scope.

Definition emptyS  := "empty".
Definition consS   := "cons".
Definition unconsS := "uncons".

Section ByteString.

Context `{Alternative m}.

Definition ByteStringSpec := Def ADT {
  rep := list Word,

  Def Constructor0 emptyS : rep := ret []%list,,

  Def Method1 consS (r : rep) (w : Word) : rep * m unit :=
    u <- { u : m unit | True };
    ret (cons w r, u),
  Def Method0 unconsS (r : rep) : rep * m (option Word) :=
    u <- { u : m unit | True };
    ret (match r with
         | nil => (r, u *> pure None)
         | cons x xs => (xs, u *> pure (Some x))
         end)

}%ADTParsing.

Definition ByteString := Rep ByteStringSpec.

Definition empty : Comp ByteString :=
  Eval simpl in callCons ByteStringSpec emptyS.

Definition cons (w : Word) (bs : ByteString) : Comp (ByteString * m unit) :=
  Eval simpl in callMeth ByteStringSpec consS bs w.

Definition uncons (bs : ByteString) : Comp (ByteString * m (option Word)) :=
  Eval simpl in callMeth ByteStringSpec unconsS bs.

End ByteString.