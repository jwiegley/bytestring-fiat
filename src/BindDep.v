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

Lemma Bind_dep_inv :
  forall (A B : Type) (ca : Comp A)
         (f : forall v : A, refine ca (ret v) -> Comp B) (v : B),
    (`(x | H) <- ca; f x H) ↝ v -> exists a' : A,
      { H : ca ↝ a' & f a' (refine_In H) ↝ v }.
Proof.
  intros.
  destruct H, H.
  exists x.
  exists x0.
  exact i.
Qed.

Global Program Instance refine_bind_dep :
  Proper (forall_relation (fun ca : Comp A =>
            ((forall_relation (fun v : A => pointwise_relation _ (@refine B)))
               ==> (@refine B))%signature)) (@Bind_dep A B).
Obligation 1.
  intros ??????.
  apply Bind_dep_inv in H0.
  destruct H0.
  exists x0.
  destruct H0.
  exists x1.
  eapply H in c; eauto.
Qed.

Global Program Instance refine_bind_dep_flip :
  Proper (forall_relation (fun ca : Comp A =>
            ((forall_relation
                (fun v : A =>
                   pointwise_relation _ (Basics.flip (@refine B))))
               ==> Basics.flip (@refine B))%signature)) (@Bind_dep A B).
Obligation 1.
  intros ??????.
  apply Bind_dep_inv in H0.
  destruct H0.
  exists x0.
  destruct H0.
  exists x1.
  eapply H in c; eauto.
Qed.

Global Program Instance refineEquiv_bind_dep :
  Proper (forall_relation (fun ca : Comp A =>
            ((forall_relation
                (fun v : A =>
                   pointwise_relation _ (@refineEquiv B)))
               ==> (@refineEquiv B))%signature)) (@Bind_dep A B).
Obligation 1.
  intros ????.
  split; intros; intros ??;
  apply Bind_dep_inv in H0;
  destruct H0;
  exists x0;
  destruct H0;
  exists x1;
  eapply H in c; eauto.
Qed.

Lemma refine_reveal_dep : forall A (c : Comp A) B (k : A -> Comp B),
  refineEquiv (x <- c; k x) (`(x | H) <- c; k x).
Proof.
  split; intros;
  intros x?;
  destruct H;
  exists x0;
  destruct H;
  split; trivial.
Qed.

Lemma refine_bind_dep_ret :
  forall A a B (k : forall x : A, refine (ret a) (ret x) -> Comp B),
  refineEquiv (`(x | H) <- ret a; k x H)
              (k a (refine_In (In_singleton _ a))).
Proof.
  Local Transparent Bind_dep.
  split; intros;
  intros x ?.
  unfold Bind_dep;
    exists a.
    exists (In_singleton _ a).
    exact H.
  apply Bind_dep_inv in H.
  destruct H, H.
  destruct x1.
  exact c.
Qed.

Lemma refine_bind_dep_bind_ret :
  forall A (c : Comp A) B (f : forall x : A, refine c (ret x) -> B)
         C (k : B -> Comp C),
    refineEquiv
      (r_o' <- `(x|H) <- c;
               ret (f x H);
       k r_o')
       (`(x|H) <- c;
       k (f x H)).
Proof.
  split; intros;
  intros ??;
  destruct H;
  destruct H.
    eapply BindComputes.
      Focus 2.
      apply i.
    eexists.
    exists x0.
    constructor.
  apply Bind_dep_inv in H.
  destruct H, H.
  exists x0.
  exists x1.
  apply Return_inv in c0.
  subst.
  exact H0.
Qed.

Lemma refine_bind_dep_ignore {A} (c : Comp A) B (k : A -> Comp B) :
  refineEquiv (`(x | _) <- c; k x) (x <- c; k x).
Proof.
  split; intros;
  intros ??;
  destruct H;
  destruct H;
  exists x.
    exists H.
    exact H0.
  intuition.
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
