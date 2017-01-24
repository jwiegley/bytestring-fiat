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

Definition plusPtr `(ptr : Ptr A) (n : Size) := (ptr + n)%N.
Definition minusPtr `(ptr : Ptr A) (n : Size) := (ptr - n)%N.

Module Ptr_as_OT <: UsualOrderedType.
  Definition t:=Ptr Word.
  Definition eq:=@eq (Ptr Word).
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition lt := N.lt.
  Definition lt_trans := N.lt_trans.
  Definition lt_not_eq := N.lt_neq.

  Definition compare x y : Compare lt eq x y.
  Proof.
  case_eq (x ?= y)%N; intro.
  - apply EQ. now apply N.compare_eq.
  - apply LT. assumption.
  - apply GT. now apply N.gt_lt.
  Defined.

  Definition eq_dec := N.eq_dec.
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

Corollary plusPtr_sub : forall A (addr : Ptr A) n m,
  m <= n -> minusPtr (A:=A) (plusPtr addr n) m = plusPtr addr (n - m).
Proof. intros; symmetry; apply N.add_sub_assoc; nomega. Qed.

Corollary plusPtr_sub_r : forall A (addr : Ptr A) n m,
  n <= addr -> n <= m
    -> plusPtr (A:=A) (minusPtr addr n) m = plusPtr addr (m - n).
Proof. intros; nomega. Qed.

Corollary plusPtr_comm : forall A (addr : Ptr A) n m,
  plusPtr (A:=A) (plusPtr addr n) m = plusPtr (A:=A) (plusPtr addr m) n.
Proof. intros; nomega. Qed.

Corollary minusPtr_add : forall A (addr : Ptr A) n m,
  minusPtr (A:=A) (minusPtr addr n) m = minusPtr addr (n + m).
Proof. intros; nomega. Qed.

Corollary minusPtr_zero : forall A (addr : Ptr A),
  minusPtr addr 0 = addr.
Proof. intros; nomega. Qed.

Corollary minusPtr_succ : forall A (addr : Ptr A) n,
  n <= addr -> minusPtr (A:=A) (minusPtr addr 1) n = minusPtr addr (N.succ n).
Proof. intros; nomega. Qed.

Corollary minusPtr_sub : forall A (addr : Ptr A) n m,
  m <= n -> minusPtr (A:=A) (plusPtr addr m) n = minusPtr addr (n - m).
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
Hint Rewrite plusPtr_sub : ptr.
Hint Rewrite plusPtr_succ : ptr.
Hint Rewrite minusPtr_zero : ptr.
Hint Rewrite minusPtr_add : ptr.
Hint Rewrite minusPtr_sub : ptr.
Hint Rewrite minusPtr_succ : ptr.

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
