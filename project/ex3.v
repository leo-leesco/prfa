From Stdlib Require Import List.
Import ListNotations.

From project Require Import ex1 ex2.

Inductive cf : list form -> form -> Prop :=
  | impintro (A : list form) (s t : form) : cf (s :: A) t -> cf A (s → t)
  | elim (A : list form) (s : form) : ae A s -> cf A s

with ae : list form -> form -> Prop :=
  | impelim (A : list form) (s t : form) : ae A (s → t) -> cf A s -> ae A t
  | ass (A : list form) (s : form) : In s A -> ae A s.

Notation "A ⊢ae s" := (ae A s) (at level 70).
Notation "A ⊢cf s" := (cf A s) (at level 70).

Scheme cf_ind_mut := Induction for cf Sort Prop
with ae_ind_mut := Induction for ae Sort Prop.
Combined Scheme cf_ae_ind from cf_ind_mut, ae_ind_mut.
Check cf_ae_ind.

Lemma WeakeningCF A B s :
  incl A B -> A ⊢cf s -> B ⊢cf s
with WeakeningAE A B s :
  incl A B -> A ⊢ae s -> B ⊢ae s.
Proof.
  all: intros sub H; induction H.
  - apply impintro.
    apply WeakeningCF with (A := (s :: A)); auto with datatypes.
  - apply elim.
    eapply WeakeningAE; eauto.
  - eapply impelim; eauto.
  - apply ass.
    auto with datatypes.
Qed.

#[refine] Instance syntactic_model : WModel := {|
  W := list form;
  rel := @incl form ;
  abs := fun A => A ⊢cf bot;
  interp := fun A s => A ⊢cf s;
|}.
Proof.
  - unfold incl in *. auto.
  - unfold incl in *. auto.
  - intros. eapply WeakeningCF; eauto.
  - intros. eapply WeakeningCF; eauto.
Defined.

Lemma correctness A s :
  (winterp syntactic_model A s -> A ⊢cf s) /\ (A ⊢ae s -> winterp syntactic_model A s).
Proof.
  revert A.
  induction s.
  - split.
    + auto.
    + apply elim.
  - split.
    + auto.
    + apply elim.
  - simpl in *. split.
    + intros.
      apply impintro.
      apply IHs2.
      apply H.
      split.
      * auto with datatypes.
      * apply IHs1.
        apply ass.
        auto with datatypes.
    + intros.
      apply IHs2.
      apply impelim with (s := s1).
      * eapply WeakeningAE; eauto. tauto.
      * apply IHs1. tauto.
Qed.

Lemma Weak_ctx_syntactic A:
   ctx_winterp syntactic_model A A.
Proof.
  induction A.
  - constructor.
  - simpl.
    split.
    + apply correctness.
      apply ass.
      auto with datatypes.
    + apply ctx_monotonicity with (w := A).
      * simpl. auto with datatypes.
      * assumption.
Qed.

Theorem Cut_elimination A s:
  (forall M w, ctx_winterp M w A -> winterp M w s) -> A ⊢cf s.
Proof.
  intros.
  apply correctness.
  apply H.
  apply Weak_ctx_syntactic.
Qed.

Lemma absurd_ae s:
  ~ [] ⊢ae s.
Proof.
  intro.
  remember [] as A.
  induction H.
  - auto.
  - rewrite HeqA in H. auto with datatypes.
Qed.

Fixpoint ctx_implies A s : form :=
  match A with
  | [] => s
  | t :: A => t → (ctx_implies A s)
  end.

Notation "A --> s" := (ctx_implies A s) (at level 60).

Lemma absurd_dne_ae A:
  ~ [neg (neg (var 0))] ⊢ae A --> var 0.
Proof.
  remember (var 0) as s.
  intro.
  induction 1.
  - assumption.
  - destruct A.
