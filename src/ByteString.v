Require Import
  Fiat.ADT
  Fiat.ADTNotation
  ByteString.Lib.Fiat
  ByteString.Memory
  Hask.Data.Functor
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
Context `{Computable m}.

Definition ByteStringSpec := Def ADT {
  rep := list Word,

  Def Constructor0 emptyS : rep := ret []%list,,

  Def Method1 consS (r : rep) (w : Word) : rep * m unit :=
    mu <- { mu : m unit | True };
    ret (if m_computes_to mu then cons w r else r, mu),

  Def Method0 unconsS (r : rep) : rep * m (option Word) :=
    mu <- { mu : m unit | True };
    ret (if m_computes_to mu
         then (match r with
               | nil => (r, None <$ mu)
               | cons x xs => (xs, Some x <$ mu)
               end)
         else (r, None <$ mu))

}%ADTParsing.

Definition ByteString := Rep ByteStringSpec.

Definition empty : Comp ByteString :=
  Eval simpl in callCons ByteStringSpec emptyS.

Definition cons (w : Word) (bs : ByteString) : Comp (ByteString * m unit) :=
  Eval simpl in callMeth ByteStringSpec consS bs w.

Definition uncons (bs : ByteString) : Comp (ByteString * m (option Word)) :=
  Eval simpl in callMeth ByteStringSpec unconsS bs.

End ByteString.