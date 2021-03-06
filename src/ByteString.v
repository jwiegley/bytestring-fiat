Require Import
  Fiat.ADT
  Fiat.ADTNotation
  ByteString.Memory.

(************************************************************************
 ** Semantics of the core Haskell ByteString data type in Fiat.        **
 ************************************************************************)

Open Scope string_scope.

Definition emptyS  := "empty".
Definition packS   := "pack".
Definition unpackS := "unpack".
Definition consS   := "cons".
Definition unconsS := "uncons".
Definition appendS := "append".

Definition ByteStringSpec := Def ADT {
  rep := list Word,

  Def Constructor0 emptyS : rep := ret []%list,

  (* Def Constructor1 packS (xs : list Word) : rep := ret xs, *)
  (Build_methDef _
     {| methID    := packS
      ; methArity := 0
      ; methDom   := [_]%list
      ; methCod   := None|}
     (fun xs => ret xs)),

  Def Method0 unpackS (r : rep) : rep * (list Word) :=
    ret (r, r),

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

Definition pack (xs : list Word) : Comp ByteString :=
  Eval simpl in callMeth ByteStringSpec packS xs.

Definition unpack (bs : ByteString) : Comp (ByteString * list Word) :=
  Eval simpl in callMeth ByteStringSpec unpackS bs.

Definition cons (w : Word) (bs : ByteString) : Comp ByteString :=
  Eval simpl in (callMeth ByteStringSpec consS bs w).

Definition uncons (bs : ByteString) : Comp (ByteString * option Word) :=
  Eval simpl in callMeth ByteStringSpec unconsS bs.

Definition append (bs1 bs2 : ByteString) : Comp ByteString :=
  Eval simpl in callMeth ByteStringSpec appendS bs1 bs2.

(* Definition fold {A : Type} (bs : ByteString) (f : Word -> A -> A) (z : A) : Comp A :=. *)
