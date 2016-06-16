Require Import Fiat.ADT Fiat.ADTNotation.

Require Import Coq.Sets.Ensembles.

Require Import
  Here.ByteString
  Here.LibExt
  Here.Same_set.

Section Canonical.

Variable Word8 : Type.

Definition ByteStringSpec := ByteStringSpec Word8.
Definition ByteString     := ByteString Word8.

Inductive ByteStringT :=
  | BS_empty : ByteStringT
  | BS_cons : forall (r : ByteStringT), Word8 -> ByteStringT.

Fixpoint bsDenote (bs : ByteStringT) : ByteString :=
  match bs with
  | BS_empty    => Empty_set _
  | BS_cons r w => Ensembles.Add _ (Ensemble_map (first S) (bsDenote r)) (0, w)
  end.

Require Import
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Lemma ByteString_canonical : FullySharpened ByteStringSpec.
Proof.
  start sharpening ADT.
  hone representation using (fun or (nr : ByteStringT) =>
                               Same_set _ or (bsDenote nr)).
  {
    simplify with monad laws.
    subst H.
    apply refine_pick_val with (a:=BS_empty).
    simplify_ensembles.
  }
  {
    simplify with monad laws; simpl.
    setoid_rewrite H0; clear H0; simpl.
    refine pick val (BS_cons r_n d).
      simplify with monad laws.
      finish honing.
    reflexivity.
  }
  {
    refine pick val match r_n with
                    | BS_empty    => (bsDenote r_n, None)
                    | BS_cons r x => (bsDenote r, Some x)
                    end.
      simplify with monad laws; simpl.
      refine pick val match r_n with
                      | BS_empty => r_n
                      | BS_cons r _ => r
                      end.
        simplify with monad laws.
        finish honing.
      destruct r_n; reflexivity.
    destruct r_n; simpl in *.
      symmetry.
      exact H0.
    simplify_ensembles.
      inv H0.
      apply H2.
      apply Union_intror.
      constructor.
    rewrite H0.
    rewrite Ensemble_Add_Subtract.
      clear.
      rewrite Ensemble_map_comp.
      unfold Ensemble_map, first; simpl.
      split; intros z H.
        exists z.
        split.
          exact H.
        rewrite <- surjective_pairing.
        constructor.
      inv H.
      destruct H0.
      inv H0.
      rewrite <- surjective_pairing.
      exact H.
    unfold not; intros.
    inv H0.
    destruct H1.
    destruct H0.
    inv H1.
  }
  finish_SharpeningADT_WithoutDelegation.
Defined.

Definition ByteString_canonical' := Eval simpl in projT1 ByteString_canonical.
(* Print ByteString_canonical'. *)

(* Theorem ByteString_canonicity says that for any concrete refinement of
   [ByteStringSpec], there exists an isomorphism with [ByteString_canonical].
   This should follow trivially from their having, by definition, the same
   semantics. *)

End Canonical.