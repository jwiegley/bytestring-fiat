Require Import
  Fiat.ADT
  Fiat.ADTNotation
  Fiat.Computation.FixComp
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

Import LeastFixedPointFun.

Inductive Foo (A : Type) : Type := MkFoo : list (Foo A) -> Foo A.

Fixpoint mapM {A B} (f : A -> Comp B) (l : list A) :
  Comp (list B) :=
  match l with
  | nil => ret nil
  | List.cons x xs =>
    x' <- f x;
    xs' <- mapM f xs;
    ret (List.cons x' xs')
  end.

Definition map' {A B : Type} (f : Foo A -> Foo B) (bs : Foo A) : Comp (Foo B) :=
  LeastFixedPoint (fDom := [Foo A : Type])
    (fun rec (bs : Foo A) =>
       match bs with
       | MkFoo xs =>
         res <- mapM (fun x => rec x) xs;
         ret (MkFoo res)
       end) bs.

Definition foldr {A : Type} (bs : ByteString) (f : Word -> A -> A) (z : A) :
  Comp A :=
  LeastFixedPoint (fDom := [ByteString; A])
    (fun rec (bs : ByteString) (rest : A) =>
       `(bs', mw) <- uncons bs;
       match mw with
       | None   => ret rest
       | Some w =>
         res <- rec bs' rest;
         ret (f w res)
       end) bs z.
