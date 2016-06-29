Require Import
  Fiat.ADT
  Fiat.ADTNotation
  Fiat.ADTInduction.

Require Import
  Coq.Lists.List
  Coq.NArith.NArith.

Section ByteString.

(************************************************************************
 ** Semantics of the core Haskell ByteString data type in Fiat.        **
 ************************************************************************)

Variable Word8 : Type.

Open Scope string_scope.

Definition emptyS  := "empty".
Definition consS   := "cons".
Definition unconsS := "uncons".

Definition ByteStringSpec := Def ADT {
  rep := list Word8,

  (* Introduction *)

  Def Constructor0 emptyS : rep := ret [],,

  Def Method1 consS (r : rep) (w : Word8) : rep * unit :=
    ret (cons w r, tt),

  (* Elimination *)

  Def Method0 unconsS (r : rep) : rep * (option Word8) :=
    match r with
    | nil => ret (r, None)
    | cons x xs => ret (xs, Some x)
    end

}%ADTParsing.

Definition ByteString := Rep ByteStringSpec.

Definition empty : Comp ByteString :=
  Eval simpl in callCons ByteStringSpec emptyS.

Definition cons (w : Word8) (bs : ByteString) : Comp ByteString :=
  Eval simpl in (p <- callMeth ByteStringSpec consS bs w; ret (fst p)).

Definition uncons (bs : ByteString) : Comp (ByteString * option Word8) :=
  Eval simpl in callMeth ByteStringSpec unconsS bs.

End ByteString.
