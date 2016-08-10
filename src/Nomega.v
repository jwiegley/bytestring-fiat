Require Export
  Coq.Arith.Arith
  Coq.omega.Omega
  Coq.NArith.NArith
  Here.Decidable.

Open Scope N_scope.

Hint Rewrite
  Nplus_0_r
  nat_of_Nsucc
  nat_of_Nplus
  nat_of_Nminus
  N_of_nat_of_N
  nat_of_N_of_nat
  nat_of_P_o_P_of_succ_nat_eq_succ
  nat_of_P_succ_morphism : N.

Corollary sumbool_split : forall P Q : Prop,
  {P} + {~P} -> {Q} + {~Q} -> {P /\ Q} + {~ (P /\ Q)}.
Proof. intros; intuition. Qed.

Section N_theory.

Variables n m : N.

Theorem Neq_in : nat_of_N n = nat_of_N m -> n = m.
Proof.
  intros H; apply (f_equal N_of_nat) in H;
  autorewrite with N in *; assumption.
Qed.

Theorem Neq_out : n = m -> nat_of_N n = nat_of_N m.
Proof.
  intros H; apply (f_equal N.to_nat) in H;
  autorewrite with N in *; assumption.
Qed.

Corollary Nneq_in : nat_of_N n <> nat_of_N m -> n <> m.
Proof. congruence. Qed.

Theorem Nneq_out : n <> m -> nat_of_N n <> nat_of_N m.
Proof. intuition; apply Neq_in in H0; tauto. Qed.

Theorem Nlt_in : (nat_of_N n < nat_of_N m)%nat -> n < m.
Proof.
  unfold Nlt; intros.
  rewrite nat_of_Ncompare.
  apply (proj1 (nat_compare_lt _ _)); assumption.
Qed.

Theorem Nlt_out : n < m -> (nat_of_N n < nat_of_N m)%nat.
Proof.
  unfold Nlt; intros.
  rewrite nat_of_Ncompare in H.
  apply nat_compare_Lt_lt; assumption.
Qed.

Theorem Nle_in : (nat_of_N n <= nat_of_N m)%nat -> n <= m.
Proof.
  unfold Nle; intros.
  rewrite nat_of_Ncompare.
  apply (proj1 (nat_compare_le _ _)); assumption.
Qed.

Theorem Nle_out : n <= m -> (nat_of_N n <= nat_of_N m)%nat.
Proof.
  unfold Nle; intros.
  rewrite nat_of_Ncompare in H.
  apply nat_compare_le; assumption.
Qed.

Theorem Ngt_out : n > m -> (nat_of_N n > nat_of_N m)%nat.
Proof.
  unfold Ngt; intros.
  rewrite nat_of_Ncompare in H.
  apply nat_compare_gt; assumption.
Qed.

Theorem Ngt_in : (nat_of_N n > nat_of_N m)%nat -> n > m.
Proof.
  unfold Ngt; intros.
  rewrite nat_of_Ncompare.
  apply nat_compare_gt; assumption.
Qed.

Theorem Nge_out : n >= m -> (nat_of_N n >= nat_of_N m)%nat.
Proof.
  unfold Nge; intros.
  rewrite nat_of_Ncompare in H.
  apply nat_compare_ge; assumption.
Qed.

Theorem Nge_in : (nat_of_N n >= nat_of_N m)%nat -> n >= m.
Proof.
  unfold Nge; intros.
  rewrite nat_of_Ncompare.
  apply nat_compare_ge; assumption.
Qed.

Theorem Nle_add_plus : forall o, 0 < o -> n <= m -> n <= m + o.
Proof.
  intros.
  rewrite <- (N.add_0_r n).
  apply N.add_le_mono; congruence.
Qed.

Lemma Nsub_eq : forall o, o <= n -> o <= m -> n - o = m - o -> n = m.
Proof.
  intros.
  apply N2Z.inj_iff in H1.
  rewrite !N2Z.inj_sub in H1; auto.
  rewrite N2Z.inj_le in H, H0.
  apply N2Z.inj_iff.
  omega.
Qed.

Corollary Neq_impl_eq : n = m <-> n = m.
Proof. split; intros; assumption. Qed.

Hint Resolve Neq_impl_eq.

Corollary Nneq_impl_neq : n <> m <-> n <> m.
Proof. split; intros; assumption. Qed.

Hint Resolve Nneq_impl_neq.

Lemma Nlt_dec : {n < m} + {~ n < m}.
Proof.
  destruct (N.compare n m) eqn:Heqe.
  - right; congruence.
  - left; congruence.
  - right; congruence.
Qed.

Lemma Nle_dec : {n <= m} + {~ n <= m}.
Proof.
  destruct (N.compare n m) eqn:Heqe.
  - left; congruence.
  - left; congruence.
  - right; congruence.
Qed.

Lemma Ngt_dec : {n > m} + {~ n > m}.
Proof.
  destruct (N.compare n m) eqn:Heqe.
  - right; congruence.
  - right; congruence.
  - left; congruence.
Qed.

Lemma Nge_dec : {n >= m} + {~ n >= m}.
Proof.
  destruct (N.compare n m) eqn:Heqe.
  - left; congruence.
  - right; congruence.
  - left; congruence.
Qed.

End N_theory.

Theorem Nle_impossible : forall n m, 0 < m -> n + m <= n -> False.
Proof.
  intros.
  rewrite <- (N.add_0_r n) in H0 at 2.
  apply N.add_le_mono_l in H0.
  apply Nlt_out in H.
  apply Nle_out in H0.
  omega.
Qed.

Theorem Nadd_minus : forall n m, n <= m -> n + (m - n) = m.
Proof.
  intros.
  apply Nle_out in H.
  apply Neq_in.
  autorewrite with N.
  omega.
Qed.

(*** definitions ***)

Definition within (addr : N) (len : N) (a : N) : Prop :=
  addr <= a < addr + len.

Definition fits (addr1 len1 addr2 len2 : N) : Prop :=
  within addr1 len1 addr2 /\ within addr1 len1 (addr2 + len2).

Definition overlaps (addr len addr2 len2 : N) : Prop :=
  addr < addr2 + len2 /\ addr2 < addr + len.

(*** tactics ***)

Ltac nsimp :=
  simpl; repeat progress (autorewrite with N; simpl).

Ltac nsimp_H H :=
  simpl in H; repeat progress (autorewrite with N in H; simpl in H).

Hint Extern 3 (Decidable.decidable (_ = _)) => apply N.eq_decidable.
Hint Extern 3 (Decidable.decidable (_ < _)) => apply N.lt_decidable.
Hint Extern 3 (Decidable.decidable (_ <= _)) => apply N.le_decidable.

Ltac norm_N_step :=
  match goal with
  | [ |- ~ _ ] => unfold not; intros

  | [ H : is_true (_ <? _)  |- _ ] => apply N.ltb_lt in H
  | [ H : (_ <? _) = true   |- _ ] => apply N.ltb_lt in H
  | [ H : (_ <? _) = false  |- _ ] => apply N.ltb_ge in H
  | [ H : is_true (_ <=? _) |- _ ] => apply N.leb_le in H
  | [ H : (_ <=? _) = true  |- _ ] => apply N.leb_le in H
  | [ H : (_ <=? _) = false |- _ ] => apply N.leb_gt in H
  | [ H : is_true (_ =? _)  |- _ ] => apply N.eqb_eq in H; subst
  | [ H : (_ =? _) = true   |- _ ] => apply N.eqb_eq in H; subst
  | [ H : (_ =? _) = false  |- _ ] => apply N.eqb_neq in H

  | [ |- is_true (_ <? _)  ] => apply N.ltb_lt
  | [ |- (_ <? _) = true   ] => apply N.ltb_lt
  | [ |- (_ <? _) = false  ] => apply N.ltb_ge
  | [ |- is_true (_ <=? _) ] => apply N.leb_le
  | [ |- (_ <=? _) = true  ] => apply N.leb_le
  | [ |- (_ <=? _) = false ] => apply N.leb_gt
  | [ |- is_true (_ =? _)  ] => apply N.eqb_eq
  | [ |- (_ =? _) = true   ] => apply N.eqb_eq
  | [ |- (_ =? _) = false  ] => apply N.eqb_neq

  | [ H : _ /\ _ |- _ ] => destruct H

  | [ H : is_true ((_ && _)%bool) |- _ ] =>
    apply Bool.andb_true_iff in H; destruct H
  | [ H : (_ && _)%bool = true |- _ ] =>
    apply Bool.andb_true_iff in H; destruct H
  | [ H : (_ && _)%bool = false |- _ ] =>
    apply Bool.andb_false_iff in H; destruct H

  | [ |- is_true ((_ && _)%bool)  ] => apply Bool.andb_true_iff; split
  | [ |- (_ && _)%bool = true  ] => apply Bool.andb_true_iff; split
  | [ |- (_ && _)%bool = false ] => apply Bool.andb_false_iff

  | [ H : { _ : N | _ } |- _ ] => destruct H; simpl in *

  | [ |- {?P /\ ?Q} + {~ (?P /\ ?Q)} ] => apply sumbool_split
  | [ |- {?n =  ?m} + {?n <> ?m} ] => apply N.eq_dec
  | [ |- {?n <  ?m} + {~ (?n <  ?m)} ] => apply Nlt_dec
  | [ |- {?n <= ?m} + {~ (?n <= ?m)} ] => apply Nle_dec
  | [ |- {?n >  ?m} + {~ (?n >  ?m)} ] => apply Ngt_dec
  | [ |- {?n >= ?m} + {~ (?n >= ?m)} ] => apply Nge_dec

  | [ H : ~ _ < _  |- _ ] => apply N.nlt_ge in H
  | [ H : ~ _ <= _ |- _ ] => apply N.nle_gt in H

  | [ H : _ <  _ <  _ |- _ ] => destruct H
  | [ H : _ <= _ <  _ |- _ ] => destruct H
  | [ H : _ <  _ <= _ |- _ ] => destruct H
  | [ H : _ <= _ <= _ |- _ ] => destruct H

  | [ H : ~ (?x <  ?y <  ?z) |- _ ] => apply Decidable.not_and in H
  | [ H : ~ (?x <= ?y <  ?z) |- _ ] => apply Decidable.not_and in H
  | [ H : ~ (?x <  ?y <= ?z) |- _ ] => apply Decidable.not_and in H
  | [ H : ~ (?x <= ?y <= ?z) |- _ ] => apply Decidable.not_and in H

  | [ |- ~ (?x <  ?y <  ?z) ] => apply Decidable.not_and
  | [ |- ~ (?x <= ?y <  ?z) ] => apply Decidable.not_and
  | [ |- ~ (?x <  ?y <= ?z) ] => apply Decidable.not_and
  | [ |- ~ (?x <= ?y <= ?z) ] => apply Decidable.not_and

  | [ H : ~ (?x <  ?y /\ ?w <  ?z) |- _ ] => apply Decidable.not_and in H
  | [ H : ~ (?x <= ?y /\ ?w <  ?z) |- _ ] => apply Decidable.not_and in H
  | [ H : ~ (?x <  ?y /\ ?w <= ?z) |- _ ] => apply Decidable.not_and in H
  | [ H : ~ (?x <= ?y /\ ?w <= ?z) |- _ ] => apply Decidable.not_and in H

  | [ |- ~ (?x <  ?y /\ ?w <  ?z) ] =>
    apply LogicFacts.not_and_implication; intros
  | [ |- ~ (?x <= ?y /\ ?w <  ?z) ] =>
    apply LogicFacts.not_and_implication; intros
  | [ |- ~ (?x <  ?y /\ ?w <= ?z) ] =>
    apply LogicFacts.not_and_implication; intros
  | [ |- ~ (?x <= ?y /\ ?w <= ?z) ] =>
    apply LogicFacts.not_and_implication; intros

  | [ |- _ <  _ <  _ ] => split
  | [ |- _ <= _ <  _ ] => split
  | [ |- _ <  _ <= _ ] => split
  | [ |- _ <= _ <= _ ] => split

  | [ H : ?n < ?m |- ?n < ?m + ?o ] => apply (N.lt_lt_add_r _ _ _ H)
  | [ H : 0 < ?m  |- ?n < ?n + ?m ] => apply (N.lt_add_pos_r _ _ H)

  | [ H : _ = _ |- _ ] => subst
  end.

Ltac norm_N := repeat progress (norm_N_step; auto).

Ltac pre_nomega :=
  unfold within, fits, overlaps in *;
  nsimp; intros; norm_N; nsimp;
  repeat
    match goal with
    | [ H : _ = _          |- _ ] => apply Neq_out in H; nsimp_H H
    | [ H : _ <> _         |- _ ] => apply Nneq_out in H; nsimp_H H
    | [ H : _ = _ -> False |- _ ] => apply Nneq_out in H; nsimp_H H
    | [ H : _ < _          |- _ ] => apply Nlt_out in H; nsimp_H H
    | [ H : _ <= _         |- _ ] => apply Nle_out in H; nsimp_H H
    | [ H : _ > _          |- _ ] => apply Ngt_out in H; nsimp_H H
    | [ H : _ >= _         |- _ ] => apply Nge_out in H; nsimp_H H

    | [ |- _ = _  ] => apply Neq_in; nsimp
    | [ |- _ < _  ] => apply Nlt_in; nsimp
    | [ |- _ <= _ ] => apply Nle_in; nsimp
    | [ |- _ > _  ] => apply Ngt_in; nsimp
    | [ |- _ >= _ ] => apply Nge_in; nsimp
    end.

Ltac nomega' :=
  pre_nomega;
  repeat progress match goal with
  | _ => omega || (unfold nat_of_P in *; simpl in *; omega)
  | [ H : _ \/ _ |- _ ] => destruct H; nomega'
  | [ |- _ /\ _ ] => split; intros; nomega'
  | [ |- _ <-> _ ] => split; intros; nomega'
  | [ |- _ \/ _ ] => first [ solve [ left; nomega' ]
                           | solve [ right; nomega' ] ]
  end.

Ltac nomega := solve [ nomega' ].

Ltac decisions :=
  repeat
    match goal with
    | [ H : context [if ?B then _ else _] |- _ ] =>
      let Heqe := fresh "Heqe" in destruct B eqn:Heqe
    | [ |- context [if ?B then _ else _] ] =>
      let Heqe := fresh "Heqe" in destruct B eqn:Heqe

    | [ H : context[@IfDec_Then_Else _ _ _ _ _] |- _ ] =>
      unfold IfDec_Then_Else in H; simpl in H
    | [ |- context[@IfDec_Then_Else _ _ _ _ _] ] =>
      unfold IfDec_Then_Else; simpl
    end.

(*** within ***)

Lemma within_refl : forall addr len,
  0 < len -> within addr len addr.
Proof. nomega. Qed.

Lemma within_reflect : forall x y a,
  within x y a <-> ((x <=? a) && (a <? x + y) = true)%bool.
Proof. nomega. Qed.

Lemma not_within_reflect : forall x y a,
  ~ within x y a <-> ((x <=? a) && (a <? x + y) = false)%bool.
Proof. nomega. Qed.

Lemma within_dec : forall a l x,
  {within a l x} + {~ within a l x}.
Proof. nomega. Qed.

(*** fits ***)

(*** overlaps ***)

Lemma overlaps_sym : forall addr1 len1 addr2 len2,
  overlaps addr1 len1 addr2 len2 <-> overlaps addr2 len2 addr1 len1.
Proof. nomega. Qed.

Lemma overlaps_trans : forall a b x y z,
  y < z -> overlaps a b x y -> overlaps a b x z.
Proof. nomega. Qed.

Lemma not_overlaps_sym : forall addr1 len1 addr2 len2,
  ~ overlaps addr1 len1 addr2 len2 <-> ~ overlaps addr2 len2 addr1 len1.
Proof. nomega. Qed.

Corollary not_overlaps_trans : forall a b x y z,
  z < y -> ~ overlaps a b x y -> ~ overlaps a b x z.
Proof. nomega. Qed.

Lemma overlaps_irr : forall addr len1 len2,
  0 < len1 -> 0 < len2 -> overlaps addr len1 addr len2.
Proof. nomega. Qed.

Lemma overlaps_within : forall addr1 len1 addr2 len2,
  0 < len1 -> overlaps addr1 len1 addr2 len2
                <-> IfDec addr1 < addr2
                    Then within addr1 len1 addr2
                    Else within addr2 len2 addr1.
Proof. intros; decisions; nomega. Qed.

Corollary not_overlaps_within : forall addr1 len1 addr2 len2,
  0 < len1
    -> ~ overlaps addr1 len1 addr2 len2
         <-> IfDec addr1 < addr2
             Then ~ within addr1 len1 addr2
             Else ~ within addr2 len2 addr1.
Proof.
  split; intros.
    decisions;
    unfold not; intros;
    apply H0, overlaps_within; trivial;
    decisions; firstorder.
  unfold not; intros;
  apply overlaps_within in H1; trivial;
  decisions; firstorder.
Qed.
