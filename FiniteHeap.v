Require Import
  Fiat.ADT
  Fiat.ADTNotation
  Here.Nomega
  Here.Decidable
  Here.BindDep
  Here.FunRelation
  Here.FinRelation
  Here.Tactics
  Here.ADTInduction
  Here.Heap.

Require Import
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Generalizable All Variables.

Section FiniteHeap.

Variable Word8 : Type.
Variable Zero : Word8.

Definition MemoryBlock := MemoryBlock Word8.
Definition HeapSpec := @HeapSpec Word8.

Tactic Notation "locate" "set" "as" ident(s)  :=
  match goal with
  | [ |- context [ {r_n : {r : FunRel N MemoryBlock | FinRel r}
                   | ?S = ` r_n} ] ] =>
    remember S as s
  end.

Lemma Bool_FinRel {A B} (a : bool) `(_ : FinRel r1) `(_ : FinRel r2) :
  @FinRel A B (if a then r1 else r2).
Proof. destruct a; assumption. Defined.

Lemma Option_Option_FinRel {A B C D E F}
      (a : option (C * D)) (b : option (E * F)) `(_ : FinRel r)
      (f : C -> D -> E -> F -> FunRel A B) :
  (forall (c : C) (d : D) (e : E) (g : F), FinRel (f c d e g)) ->
    @FinRel A B (match a, b with Some (x, y), Some (z, w) => f x y z w | _, _ => r end).
Proof.
  destruct a, b; intros; auto.
    destruct p, p0; auto.
  destruct p; auto.
Defined.

Ltac prep H :=
  intros ? H; simplify_ensembles; simpl in *;
  decisions; simplify_ensembles; simpl in *.

Ltac fin :=
  match goal with
  | [ H0 : All _ _, H1 : In _ _ _     |- _ ] => exact (H0 _ H1)
  | [ H0 : All _ _, H1 : Lookup _ _ _ |- _ ] => exact (H0 _ H1)
  | [ H0 : All _ _, H1 : forall m, Lookup _ m _ |- _ ] => exact (H0 _ (H1 _))
  end.

Ltac complete :=
  let H := fresh "H" in prep H; fin || inversion H.

Theorem Finite_Heap : { adt : ADT _ & refineADT HeapSpec adt }.
Proof.
  eexists.
  hone representation using
    (fun (or : FunRel N MemoryBlock) (nr : FunRel N MemoryBlock) =>
       or = nr /\ FinRel nr /\ All (fun p => FinRel (memData (snd p))) nr);
  try simplify with monad laws; try destruct H0 as [H0 H1 H2]; subst; simpl.
  {
    refine pick val (Empty _ _).
      finish honing.
    intuition.
      apply Empty_FinRel.
    intros ??.
    inversion H0.
  }
  {
    subst H.
    apply refine_under_bind; intros.
    refine pick val (Update a _ _).
      simplify with monad laws.
      finish honing.
    intuition.
      apply Update_FinRel; assumption.
    complete.
  }
  {
    unfold free_block.
    refine pick val (Remove d _).
      simplify with monad laws.
      finish honing.
    intuition.
      apply Remove_FinRel; assumption.
    complete.
  }
  {
    subst H.
    apply refine_bind_pick; intros.
    apply refine_under_bind; intros.
    unfold fit_to_length, shift_address.
    refine pick val (If a
                     Then Modify a0 _ (Move d a0 _)
                     Else Update a0 _ _).
      simplify with monad laws.
      finish honing.
    intuition.
      apply Bool_FinRel.
        apply Modify_FinRel, Move_FinRel; assumption.
      apply Update_FinRel; assumption.
    prep H4; destruct a; simplify_ensembles; simpl in *; fin.
  }
  {
    subst H.
    apply refine_bind_pick; intros.
    refine pick val r_n.
      simplify with monad laws.
      finish honing.
    intuition.
  }
  {
    unfold set_address.
    refine pick val (Map _ _).
      simplify with monad laws.
      finish honing.
    intuition.
      apply Map_FinRel; assumption.
    prep H3.
      apply Update_FinRel; fin.
    fin.
  }
  {
    subst H.
    apply refine_bind_pick; intros.
    apply refine_bind_pick; intros.
    refine pick val (match a, a0 with
                     | Some (saddr, sblk), Some (daddr, dblk) =>
                       Update daddr _ _
                     | _, _ => r_n
                     end).
      simplify with monad laws.
      finish honing.
    intuition.
      destruct a, a0; trivial.
        destruct p, p0.
        apply Update_FinRel; assumption.
      destruct p; assumption.
    prep H4.
    destruct a, a0; try fin.
      destruct p, p0.
      simplify_ensembles.
        fin.
      apply Overlay_FinRel.
        destruct (H0 n m1 eq_refl), H4; fin.
      destruct (H n0 m0 eq_refl), H4; fin.
    destruct p; fin.
  }
  {
    unfold set_memory.
    refine pick val (Map _ _).
      simplify with monad laws.
      finish honing.
    intuition.
      apply Map_FinRel; assumption.
    prep H3; try fin.
    apply Define_FinRel; fin.
  }
  apply reflexivityT.
Defined.

End FiniteHeap.
