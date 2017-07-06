Require Import
  ByteString.Lib.Nomega
  Coq.NArith.NArith
  Coq.Strings.Ascii
  Coq.Structures.DecidableTypeEx
  Coq.Structures.OrderedType
  Coq.Structures.OrderedTypeEx.

Generalizable All Variables.

Definition Ptr (A : Type) := N.
Definition Size := N.
Definition Word := Ascii.ascii.
Definition Zero := Ascii.zero.

Definition nullPtr {A} : Ptr A := 0%N.

Definition eqPtr {A} (x y : Ptr A) := x = y.
Hint Unfold eqPtr.
Definition neqPtr {A} (x y : Ptr A) := x <> y.
Hint Unfold neqPtr.
Definition eqbPtr {A} (x y : Ptr A) := N.eqb x y.
Hint Unfold eqbPtr.
Definition eqdecPtr {A} (x y : Ptr A) := N.eq_dec x y.
Hint Unfold eqdecPtr.

Definition ltPtr {A} (ptr1 ptr2 : Ptr A) : Prop := N.lt ptr1 ptr2.
Hint Unfold ltPtr.
Definition lePtr {A} (ptr1 ptr2 : Ptr A) : Prop := N.le ptr1 ptr2.
Hint Unfold lePtr.
Definition gtPtr {A} (ptr1 ptr2 : Ptr A) : Prop := N.gt ptr1 ptr2.
Hint Unfold gtPtr.
Definition gePtr {A} (ptr1 ptr2 : Ptr A) : Prop := N.ge ptr1 ptr2.
Hint Unfold gePtr.

Definition ltbPtr {A} (ptr1 ptr2 : Ptr A) : bool := N.ltb ptr1 ptr2.
Hint Unfold ltbPtr.
Definition lebPtr {A} (ptr1 ptr2 : Ptr A) : bool := N.leb ptr1 ptr2.
Hint Unfold lebPtr.

Delimit Scope Ptr_scope with Ptr.
Bind Scope Ptr_scope with Ptr.

Infix "<=" := lePtr : Ptr_scope.
Infix "<"  := ltPtr : Ptr_scope.
Infix ">=" := gePtr : Ptr_scope.
Infix ">"  := gtPtr : Ptr_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z)%Ptr : Ptr_scope.
Notation "x <= y <  z" := (x <= y /\ y <  z)%Ptr : Ptr_scope.
Notation "x <  y <  z" := (x <  y /\ y <  z)%Ptr : Ptr_scope.
Notation "x <  y <= z" := (x <  y /\ y <= z)%Ptr : Ptr_scope.

Infix "=?"  := eqbPtr (at level 70, no associativity) : Ptr_scope.
Infix "<=?" := lebPtr (at level 70, no associativity) : Ptr_scope.
Infix "<?"  := ltbPtr (at level 70, no associativity) : Ptr_scope.

Definition plusPtr  `(ptr : Ptr A) (n : Size) := (ptr + n)%N.
Hint Unfold plusPtr.
Definition minusPtr {A} (ptr1 ptr2 : Ptr A) := (ptr1 - ptr2)%N.
Hint Unfold minusPtr.

Module Ptr_as_OT <: UsualOrderedType.
  Definition t:=Ptr Word.
  Definition eq:=eqPtr (A:=Word).

  Definition eq_refl  := @eq_refl t.
  Definition eq_sym   := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition lt := ltPtr (A:=Word).
  Definition lt_trans := N.lt_trans.
  Definition lt_not_eq := N.lt_neq.

  Definition compare x y : Compare (ltPtr (A:=Word)) (eqPtr (A:=Word)) x y.
  Proof.
  case_eq (x ?= y)%N; intro.
  - apply EQ. now apply N.compare_eq.
  - apply LT. assumption.
  - apply GT. now apply N.gt_lt.
  Defined.

  Definition eq_dec := eqdecPtr (A:=Word).
End Ptr_as_OT.

Module Ptr_as_DT <: UsualDecidableType := Ptr_as_OT.

Local Open Scope N_scope.

Corollary succ_sub_one : forall n,
  N.succ n - 1 = n.
Proof. nomega. Qed.

Corollary succ_one_sub : forall n,
  N.succ n - n = 1.
Proof. intros; rewrite N.sub_succ_l; nomega. Qed.

Corollary plusPtr_zero : forall A (addr : Ptr A),
  plusPtr addr 0 = addr.
Proof. intros; nomega. Qed.

Corollary plusPtr_add : forall A (addr : Ptr A) n m,
  plusPtr (A:=A) (plusPtr addr n) m = plusPtr addr (n + m).
Proof. intros; nomega. Qed.

Corollary plusPtr_succ : forall A (addr : Ptr A) n,
  plusPtr (A:=A) (plusPtr addr n) 1 = plusPtr addr (N.succ n).
Proof. intros; nomega. Qed.

Corollary plusPtr_comm : forall A (addr : Ptr A) n m,
  plusPtr (A:=A) (plusPtr addr n) m = plusPtr (A:=A) (plusPtr addr m) n.
Proof. intros; nomega. Qed.

Corollary minusPtr_plusPtr_plusPtr : forall A (addr : Ptr A) n m,
  minusPtr (A:=A) (plusPtr addr n) (plusPtr addr m) = n - m.
Proof. intros; nomega. Qed.

Corollary minusPtr_plusPtr : forall A (addr : Ptr A) n,
  minusPtr (A:=A) (plusPtr addr n) addr = n.
Proof. intros; nomega. Qed.

Hint Rewrite N.add_0_r : ptr.
Hint Rewrite N.add_sub : ptr.
Hint Rewrite N.add_succ_l : ptr.
Hint Rewrite N.sub_diag : ptr.
Hint Rewrite N.sub_succ : ptr.
Hint Rewrite N.peano_rec_succ : ptr.
Hint Rewrite succ_sub_one : ptr.
Hint Rewrite succ_one_sub : ptr.
Hint Rewrite plusPtr_zero : ptr.
Hint Rewrite plusPtr_add : ptr.
Hint Rewrite plusPtr_succ : ptr.
Hint Rewrite minusPtr_plusPtr_plusPtr : ptr.
Hint Rewrite minusPtr_plusPtr : ptr.

Ltac rewrite_ptr :=
  repeat (
    autorewrite with ptr; try nomega;
    repeat match goal with
    | [ |- context[N.succ _ - _] ] =>
      rewrite N.sub_succ_l; [|nomega]
    | [ |- context[N.peano_rec _ _ _ (_ + 1)] ] =>
      rewrite N.add_1_r
    end);
  first [ auto | discriminate | congruence | nomega | idtac ].
