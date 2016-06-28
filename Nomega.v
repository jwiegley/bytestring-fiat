Require Import
  Fiat.ADT
  Fiat.ADTNotation.

Require Export
  Coq.NArith.NArith
  Omega.

Require Export
  Here.Decidable.

Open Scope N_scope.

Definition within (addr : N) (len : N) (a : N) : Prop :=
  addr <= a < addr + len.

Definition within_le (addr : N) (len : N) (a : N) : Prop :=
  addr <= a <= addr + len.

Lemma within_refl : forall addr len,
  0 < len -> within addr len addr.
Proof.
  split; intros.
    apply N.le_refl.
  apply N.lt_add_pos_r.
  assumption.
Qed.

Definition fits (addr1 len1 addr2 len2 : N) : Prop :=
  within addr1 len1 addr2 /\ within addr1 len1 (addr2 + len2).

Definition overlaps (addr len addr2 len2 : N) : Prop :=
  addr < addr2 + len2 /\ addr2 < addr + len.

Lemma overlaps_sym : forall addr1 len1 addr2 len2,
  overlaps addr1 len1 addr2 len2 <-> overlaps addr2 len2 addr1 len1.
Proof.
  split; intros;
  destruct H; split; assumption.
Qed.

Lemma overlaps_irr : forall addr len1 len2,
  0 < len1 -> 0 < len2 -> overlaps addr len1 addr len2.
Proof.
  split; intros;
  apply N.lt_add_pos_r; assumption.
Qed.

Ltac decisions :=
  repeat
    match goal with
    | [ H : context [if ?B then _ else _] |- _ ] =>
      let Heqe := fresh "Heqe" in
      destruct B eqn:Heqe
    | [ |- context [if ?B then _ else _] ] =>
      let Heqe := fresh "Heqe" in
      destruct B eqn:Heqe

    | [ H : context[@IfDec_Then_Else _ _ _ _ _] |- _ ] =>
      unfold IfDec_Then_Else in H; simpl in H
    | [ |- context[@IfDec_Then_Else _ _ _ _ _] ] =>
      unfold IfDec_Then_Else; simpl
    end.

Ltac undecide :=
  repeat
    match goal with
    | [ H : (_ <? _)  = true  |- _ ] => apply N.ltb_lt in H
    | [ H : (_ <? _)  = false |- _ ] => apply N.ltb_ge in H
    | [ H : (_ <=? _) = true  |- _ ] => apply N.leb_le in H
    | [ H : (_ <=? _) = false |- _ ] => apply N.leb_gt in H
    | [ H : (_ =? _)  = true  |- _ ] => apply N.eqb_eq in H; subst
    | [ H : (_ =? _)  = false |- _ ] => apply N.eqb_neq in H

    | [ |- (_ <? _)  = true  ] => apply N.ltb_lt
    | [ |- (_ <? _)  = false ] => apply N.ltb_ge
    | [ |- (_ <=? _) = true  ] => apply N.leb_le
    | [ |- (_ <=? _) = false ] => apply N.leb_gt
    | [ |- (_ =? _)  = true  ] => apply N.eqb_eq
    | [ |- (_ =? _)  = false ] => apply N.eqb_neq
    end.

Ltac nomega_reduce :=
  repeat (
    match goal with
    | [ H : (_ && _)%bool = true |- _ ] =>
      apply Bool.andb_true_iff in H; destruct H
    | [ H : (_ && _)%bool = false |- _ ] =>
      apply Bool.andb_false_iff in H; destruct H

    | [ H : _ <  _ <  _ |- _ ] => destruct H
    | [ H : _ <= _ <  _ |- _ ] => destruct H
    | [ H : _ <  _ <= _ |- _ ] => destruct H
    | [ H : _ <= _ <= _ |- _ ] => destruct H

    | [ |- _ <  _ <  _ ] => split
    | [ |- _ <= _ <  _ ] => split
    | [ |- _ <  _ <= _ ] => split
    | [ |- _ <= _ <= _ ] => split

    | [ H : ?N < ?M |- ?N < ?M + ?O ] => apply (N.lt_lt_add_r _ _ _ H)
    | [ H : 0 < ?M  |- ?N < ?N + ?M ] => apply (N.lt_add_pos_r _ _ H)

    | [ H : context[Z.of_N (_ + _)] |- _ ] => rewrite N2Z.inj_add in H
    | [ H : context[Z.of_N (_ - _)] |- _ ] => rewrite N2Z.inj_sub in H; trivial

    | [ |- context[Z.of_N (_ + _)] ] => rewrite N2Z.inj_add
    | [ |- context[Z.of_N (_ - _)] ] => rewrite N2Z.inj_sub

    | [ H : _ = _ |- _ ] => subst

    | [ H : context[_ < _]  |- _ ] => rewrite N2Z.inj_lt in H
    (* | [ H : context[_ = _]  |- _ ] => apply N2Z.inj_iff in H *)
    (* | [ H : context[_ <> _] |- _ ] => apply N2Z.inj_iff in H *)

    (* We need to give _ <= _ alone a chance to be used by N2Z.inj_sub. *)
    | [ H : context[_     <= _ + _] |- _ ] => rewrite N2Z.inj_le in H
    | [ H : context[_ + _ <= _    ] |- _ ] => rewrite N2Z.inj_le in H
    | [ H : context[_ + _ <= _ + _] |- _ ] => rewrite N2Z.inj_le in H
    | [ H : context[_     <= _    ] |- _ ] => rewrite N2Z.inj_le in H

    | [ |- context[_ < _]  ] => rewrite N2Z.inj_lt
    | [ |- context[_ <= _] ] => rewrite N2Z.inj_le
    | [ |- context[_ = _]  ] => apply N2Z.inj_iff
    | [ |- context[_ <> _] ] => apply N2Z.inj_iff
    end; undecide).

Ltac nomega := solve [ nomega_reduce; abstract omega ].

Lemma overlaps_within : forall addr1 len1 addr2 len2,
  0 < len1 -> overlaps addr1 len1 addr2 len2
                <-> IfDec addr1 < addr2
                    Then within addr1 len1 addr2
                    Else within addr2 len2 addr1.
Proof.
  unfold overlaps, within.
  split; intros.
    destruct H0.
    decisions; nomega.
  decisions;
  destruct H0.
    nomega.
  split; trivial.
  undecide.
  apply N.lt_eq_cases in Heqe.
  destruct Heqe; nomega.
Qed.

Corollary not_overlaps_within : forall addr1 len1 addr2 len2,
  0 < len1 -> ~ overlaps addr1 len1 addr2 len2
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

Theorem Nle_add_plus : forall n m o, 0 < o -> n <= m -> n <= m + o.
Proof.
  intros.
  rewrite <- (N.add_0_r n).
  apply N.add_le_mono; nomega.
Qed.

Theorem Nle_impossible : forall n m, 0 < m -> n + m <= n -> False.
Proof.
  intros.
  rewrite <- (N.add_0_r n) in H0 at 2.
  apply N.add_le_mono_l in H0.
  nomega.
Qed.

Lemma within_reflect : forall x y a,
  within x y a <-> ((x <=? a) && (a <? x + y) = true)%bool.
Proof.
  intros.
  unfold within.
  split; intros; try nomega.
  apply Bool.andb_true_iff; split; nomega.
Qed.
