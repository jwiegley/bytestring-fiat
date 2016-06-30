Require Import
  Coq.Sets.Ensembles.

Require Import
  Fiat.ADT
  Fiat.ADTNotation.

Require Import
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Generalizable All Variables.

Lemma refine_In `(H : In A ca a) : refine ca (ret a).
Proof.
  intros ??.
  destruct H0.
  exact H.
Defined.

Definition Bind_dep {A B : Type} (ca : Comp A)
           (k : forall v : A, refine ca (ret v) -> Comp B) : Comp B :=
  fun b : B =>
    exists a : A, { H : In A ca a & In B (k a (refine_In H)) b }.

Arguments Bind_dep {A B} ca k _.

Global Opaque Bind_dep.

Notation "`( a | H ) <- c ; k" :=
  (Bind_dep c (fun a H => k))
    (at level 81, right associativity,
     format "'[v' `( a | H )  <-  c ; '/' k ']'") : comp_scope.

Lemma refine_reveal_dep : forall A (c : Comp A) B (k : A -> Comp B),
  refine (x <- c; k x) (`(x | H) <- c; k x).
Proof.
  intros.
  intros x?.
  destruct H.
  exists x0.
  destruct H.
  split; trivial.
Qed.

Lemma refine_bind_dep_ret :
  forall A a B (k : forall x : A, refine (ret a) (ret x) -> Comp B),
  refine (`(x | H) <- ret a; k x H)
         (k a (refine_In (ReturnComputes a))).
Proof.
  intros.
  intros x?.
  Local Transparent Bind_dep.
  unfold Bind_dep.
  exists a.
  exists (ReturnComputes a).
  exact H.
Qed.

Lemma refine_bind_dep_bind_ret :
  forall A (c : Comp A) B (f : forall x : A, refine c (ret x) -> B)
         C (k : B -> Comp C),
    refine
      (r_o' <- `(x|H) <- c;
               ret (f x H);
       k r_o')
       (`(x|H) <- c;
       k (f x H)).
Proof.
  intros.
  intros ??.
  destruct H.
  destruct H.
  eapply BindComputes.
    Focus 2.
    apply i.
  eexists.
  exists x0.
  constructor.
Qed.

Lemma refine_bind_dep_ignore {A} (c : Comp A) B (k : A -> Comp B) :
  refine (`(x | _) <- c; k x) (x <- c; k x).
Proof.
  intros ??.
  destruct H.
  destruct H.
  exists x.
  exists H.
  exact H0.
Qed.

Ltac remove_dependency :=
  repeat
    match goal with
      | [ |- refine (_ <- `(_|_) <- ret _;
                          ret _;
                     _) _ ] =>
        rewrite refine_bind_dep_ret
      | [ |- refine (_ <- `(_|_) <- _;
                          ret _;
                     _) _ ] =>
        rewrite refine_bind_dep_bind_ret; simpl
      | [ |- refine (`(_|_) <- _;
                     _) _ ] =>
        rewrite refine_bind_dep_ignore
    end.
