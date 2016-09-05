Require Import Fiat.ADT Fiat.ADTNotation.

Require Import Coq.Sets.Ensembles.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.

Require Import
  ByteString.ByteString
  ByteString.ByteStringLib
  ByteString.Refined
  ByteString.Same_set.

Import LeastFixedPointFun.

Require Import
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Section ByteStringLib.

Variable Word8 : Type.

Definition ByteStringSpec := ByteStringSpec Word8.
Definition ByteString     := ByteString Word8.

(** Refine [singleton] into something optimized in terms of the internal set
    representation. *)
Lemma singleton_Impl_Ensemble :
  { Impl : _ & forall w : Word8, refine (@singleton_Spec Word8 w) (Impl w) }.
Proof.
  exists (fun w : Word8 => ret (Singleton _ (0, w))).
  intro w.
  simplify with monad laws; simpl.
  apply Same_set_ret.
  unfold Ensembles.Add.
  rewrite Ensemble_map_Empty_set, Empty_set_zero.
  reflexivity.
Defined.

Lemma singleton_Impl_List :
  { Impl : _
  & forall w : Word8,
      refine (o <- @singleton_Spec Word8 w;
              { n : list Word8 | ByteString_list_AbsR o n })
             (ret (Impl w)) }.
Proof.
  exists (fun w : Word8 => [w]).
  intro w.
  simplify with monad laws; simpl.
  refine pick val [w].
    reflexivity.
  unfold ByteString_list_AbsR; intros.
  unfold Ensembles.Add.
  split; intros;
  rewrite Ensemble_map_Empty_set, Empty_set_zero in *.
    inv H.
    exists eq_refl.
    reflexivity.
  destruct H.
  simpl in x0.
  destruct i.
    simpl in e; subst.
    constructor.
  discriminate.
Defined.

Definition singleton := Eval simpl in projT1 singleton_Impl_List.
(* Print singleton. *)

Definition partially_refine
           {oldRep newRep fDom fCod}
           (AbsR : oldRep -> newRep -> Prop)
           (fDef : funType (oldRep :: fDom) (oldRep * fCod)) :=
  { Impl : _ & refineFun_AbsR AbsR fDef Impl }.

Definition fully_refine
           {oldRep newRep fDom fCod}
           (AbsR : oldRep -> newRep -> Prop)
           (fDef : funType (oldRep :: fDom) (oldRep * fCod)) :=
  { Impl : _ & refineFun_AbsR AbsR fDef (Lift_cfunType _ _ Impl) }.

Definition fully_refine_List
           {fDom fCod}
           (fDef : funType (ByteString :: fDom) (ByteString * fCod)) :=
  fully_refine (@ByteString_list_AbsR Word8) fDef.

Lemma match_list_fst : forall A (xs : list A) B C (x : B) (y : C) f g,
  fst match xs with
      | [] => (x, y)
      | x :: xs => (f x xs, g x xs)
      end = match xs with
            | [] => x
            | x :: xs => f x xs
            end.
Proof. destruct xs; trivial. Qed.

Lemma match_list_snd : forall A (xs : list A) B C (x : B) (y : C) f g,
  snd match xs with
      | [] => (x, y)
      | x :: xs => (f x xs, g x xs)
      end = match xs with
            | [] => y
            | x :: xs => g x xs
            end.
Proof. destruct xs; trivial. Qed.

Lemma If_Opt_Then_Else_fst :
  forall A b B (x : B) C (y : C) f g,
    fst (If_Opt_Then_Else b (fun p : A => (f p, g p)) (x, y))
      = If_Opt_Then_Else b f x.
Proof. intros; destruct b; reflexivity. Qed.

Lemma If_Opt_Then_Else_snd :
  forall A b B (x : B) C (y : C) f g,
    snd (If_Opt_Then_Else b (fun p : A => (f p, g p)) (x, y))
      = If_Opt_Then_Else b g y.
Proof. intros; destruct b; reflexivity. Qed.

Lemma If_Opt_match_list : forall A (xs : list A) B (y : B) f (g : A -> B),
  (Ifopt match xs with
         | [] => None
         | x :: xs => Some (f x xs)
         end as p Then g p Else y) = match xs with
                                   | [] => y
                                   | x :: xs => g (f x xs)
                                   end.
Proof. destruct xs; trivial. Qed.

Lemma match_list_pair : forall A (xs : list A) B (z : B) C (w : C) f g,
  (match xs with
   | [] => z
   | x :: xs => f x xs
   end, match xs with
        | [] => w
        | x :: xs => g x xs
        end) = match xs with
               | [] => (z, w)
               | x :: xs => (f x xs, g x xs)
               end.
Proof. destruct xs; trivial. Qed.

(*
Definition tail_Impl_Ensemble :
  partially_refine eq (fDom:=[]) (@tail_Spec Word8).
Proof.
  eexists.
  unfold refineFun_AbsR; simpl; intros; subst.
  simplify with monad laws; unfold uncons; simpl.
    setoid_rewrite If_Opt_Then_Else_fst.
    setoid_rewrite If_Opt_Then_Else_snd.
*)

Definition tail_Impl_List : fully_refine_List (fDom:=[]) (@tail_Spec Word8).
Proof.
  exists (fun bs => match bs with
                    | nil => (nil, false)
                    | List.cons x xs => (xs, true)
                    end).
  unfold refineFun_AbsR, ByteString_list_AbsR.
  simpl; intros.
  simplify with monad laws.
  unfold uncons.
  refine pick val match r_n with
                  | nil => (r_o, None)
                  | List.cons x xs =>
                    (Ensemble_map (first Init.Nat.pred)
                                  (Subtract (nat * Word8) r_o (0, x)), Some x)
                  end.
    simplify with monad laws; simpl.
    rewrite match_list_fst, match_list_snd.
    rewrite If_Opt_Then_Else_fst, If_Opt_Then_Else_snd.
    refine pick val match r_n with
                    | nil => nil
                    | List.cons x xs => xs
                    end.
      simplify with monad laws; simpl.
      rewrite If_Opt_match_list.
      rewrite match_list_pair.
      finish honing.
    {
    split; intros;
    destruct r_n; simpl in *.
    - apply H in H0.
      destruct H0.
      inv x0.
    - simplify_ensembles.
      apply H in H1.
      destruct n; simpl in *.
        contradiction H2.
        destruct H1; subst.
        constructor.
      apply H1.
    - apply H; assumption.
    - apply H in H0.
      unfold Ensemble_map, first.
      exists (S i, x).
      split.
        constructor.
          exact H0.
        unfold not; intros.
        inv H1.
      simpl.
      constructor.
    }
  destruct r_n; simpl in *.
    reflexivity.
  split.
    apply H.
    exists eq_refl.
    reflexivity.
  reflexivity.
Defined.

Definition tail := Eval simpl in projT1 tail_Impl_List.
(* Print tail. *)

End ByteStringLib.