From Stdlib Require Import List.
Import ListNotations.

From project Require Import ex1 ex2.

(* 4.1.a *)
Inductive hil {A : list form} : form -> Prop :=
  | ass s : In s A -> hil s
  | impelim s t : hil (s → t) -> hil s -> hil t
  | Konstant s t : hil (s → t → s)
  | Substitution s t u : hil ((s → t → u) → (s → t) → s → u).

Notation "A ⊢H s" := (@hil A s) (at level 70).

(* 4.1.b *)
Lemma hil_ndm A s :
  A ⊢H s -> A ⊢m s.
Proof.
  intro H.
  induction H.
  - apply ex2.ass.
    assumption.
  - eapply ex2.impelim; eauto.
  - repeat apply ex2.impintro.
    auto with mddb datatypes.
  - repeat apply ex2.impintro.
apply ex2.impelim with (s := t).
    + apply ex2.impelim with (s := s); auto with mddb datatypes.
    + eapply ex2.impelim; eauto with mddb datatypes.
Qed.

(* 4.1.c.1 *)
Lemma eta A s t:
  A ⊢H s -> A ⊢H t → s.
Proof.
  intro.
  apply impelim with (s := s).
  - apply Konstant.
  - assumption.
Qed.

(* 4.1.c.2 *)
Lemma compose A s t u:
  A ⊢H s → t → u -> A ⊢H s → t -> A ⊢H s → u.
Proof.
  intros.
  apply impelim with (s := (s → t)).
  - apply impelim with (s := (s → t → u)).
    + apply Substitution.
    + assumption.
  - assumption.
Qed.

(* 4.1.c.3 *)
Lemma tautology A s:
  A ⊢H s → s.
Proof.
  eapply impelim.
  - eapply impelim.
    + apply Substitution.
    + apply Konstant.
  - apply Konstant.
  Unshelve.
  assumption.
Qed.

(* 4.1.d : we need `A` as a parameter because that allows us to use the first rule. *)
Lemma impintro A s t:
  s :: A ⊢H t -> A ⊢H s → t.
Proof.
  intro.
  induction H.
  - destruct H.
    + subst.
      apply tautology.
    + apply eta.
      apply ass.
      auto with datatypes.
  - eapply compose; eassumption.
  - apply eta.
    apply Konstant.
  - apply eta.
    apply Substitution.
Qed.

(* 4.1.e *)
Fact ndm_hil A s:
  A ⊢m s -> A ⊢H s.
Proof.
  induction 1.
  - apply ass.
    assumption.
  - apply impintro.
    assumption.
  - eapply impelim; eassumption.
Qed.

From Stdlib Require Import Lia ZArith List.

Section ARS.
  Context {A : Type} (R : A -> A -> Prop).

  (* 4.2.a *)
  Inductive SN_on : A -> Prop :=
    | SNon x : (forall y, R x y -> SN_on y) -> SN_on x.

  (* 4.2.b *)
  Inductive rtc : A -> A -> Prop :=
    | refl : forall x, rtc x x
    | cons : forall x y, R x y -> rtc x y
    | trans : forall x y z, rtc x y -> rtc y z -> rtc x z.

  (* 4.2.c *)
  Lemma SN_on_rtc x y:
    SN_on x -> rtc x y -> SN_on y.
  Proof.
    intros SNx xy.
    induction xy.
    - assumption.
    - induction SNx as [x H0 H1].
      apply H0.
      assumption.
    - auto.
  Qed.

  (* 4.2.d *)
  Variables T V : A -> Prop.

  Variable Hpres : forall x y, T x -> R x y -> T y.
  Variable Hprog : forall x, T x -> (exists y, R x y) \/ V x.

  Lemma SN_to_WN x :
    T x -> SN_on x -> exists v, rtc x v /\ T v /\ V v.
  Proof.
    intros Tx SNx.
    induction SNx as [x H0 H1].
    destruct (Hprog x Tx) as [[y Rxy] | Vx].
    - specialize (Hpres x y Tx Rxy) as Ty.
      specialize (H1 y Rxy Ty) as (v & yv & Tv & Vv).
      exists v.
      split.
      eapply trans.
      + apply cons.
        eassumption.
      + assumption.
      + auto.
    - exists x.
      split.
      + apply refl.
      + auto.
  Qed.
End ARS.

(* 4.2.e *)
Lemma SN_on_double_ind [A B : Type] [R1 : A -> A -> Prop] [R2 : B -> B -> Prop] (P : A -> B -> Prop) :
  (forall (a : A) (b : B),
    (forall (a' : A), R1 a a' -> SN_on R1 a') ->
    (forall (a' : A), R1 a a' -> P a' b) ->
    (forall (b' : B), R2 b b' -> SN_on R2 b') ->
    (forall (b' : B), R2 b b' -> P a b') ->
    P a b) ->
  forall (x : A) (y : B), SN_on R1 x -> SN_on R2 y -> P x y.
Proof.
  intros IH x y sn1x sn2y.
  revert y sn2y.
  induction sn1x as [x Hx0 Hx1].
  intros.
  induction sn2y as [y Hy0 Hy1].
  apply IH.
  - assumption.
  - intros.
    apply Hx1.
    + assumption.
    + apply SNon.
      assumption.
  - assumption.
  - intros.
    apply Hy1.
    assumption.
Qed.

Inductive term :=
| S | K | V (n : nat) | app (e1 e2 : term).

Coercion app : term >-> Funclass.

Section typing.

  Variable A : list form.

  Reserved Notation "⊢ e : s" (at level 60, e at next level).

  (* 4.3.a *)
  Inductive typing : term -> form -> Prop :=
    | val n s : nth_error A n = Some s -> typing (V n) s
    | comp e1 e2 s t : typing e1 (s → t) -> typing e2 s -> typing (e1 e2) t
    | konstant s t : typing K (s → t → s)
    | substitution s t u : typing S ((s → t → u) → (s → t) → s → u).

  Notation "⊢ e : s" := (typing e s) (at level 60, e at next level).

  (* 4.3.b *)
  Lemma hil_equiv s:
    A ⊢H s <-> exists e, ⊢ e : s.
  Proof.
    split.
    - induction 1.
      + destruct (In_nth_error A s H) as [n eq].
        exists (V n).
        apply val.
        assumption.
      + destruct IHhil1 as [f feq].
        destruct IHhil2 as [x xeq].
        eexists.
        eapply comp; eassumption.
      + exists K.
        apply konstant.
      + exists S.
        apply substitution.
    - intro H. destruct H as [e deriv].
      induction deriv.
      + apply ass.
        eapply nth_error_In.
        eassumption.
      + eapply impelim;
        eassumption.
      + apply Konstant.
      + apply Substitution.
  Qed.

  (* 4.3.c *)
  Inductive red : term -> term -> Prop :=
    | Kproj e1 e2 : red (K e1 e2) e1
    | SubApp e1 e2 e3 : red (S e1 e2 e3) (e1 e3 (e2 e3))
    | LeftRed e1 e1' e2 : red e1 e1' -> red (e1 e2) (e1' e2)
    | RightRed (e1 : term) e2 e2' : red e2 e2' -> red (e1 e2) (e1 e2').

  Notation "e1 » e2" := (red e1 e2) (at level 60).

  (* 4.3.d *)
  Lemma preservation e1 e2 s:
    ⊢ e1 : s -> e1 » e2 -> ⊢ e2 : s.
  Proof.
    intros te1 re1e2.
    revert te1.
    revert s.
    induction re1e2; intros; inversion te1; subst.
    - inversion H1; subst.
      inversion H2; subst.
      assumption.
    - inversion H1; subst.
      inversion H2; subst.
      inversion H4; subst.
      eapply comp; eapply comp; eassumption.
    - eapply comp; eauto.
    - eapply comp; eauto.
  Qed.

  (* 4.3.e *)
  Definition reds :=
    rtc red.

  Notation "e1 »* e2" := (reds e1 e2) (at level 60).

  Lemma app_red e1 e1' e2 :
    e1 »* e1' -> e1 e2 »* e1' e2.
  Proof.
    intro rstar.
    induction rstar.
    - apply refl.
    - apply cons.
      apply LeftRed.
      assumption.
    - eapply trans; eassumption.
  Qed.

  (* 4.3.f *)
  Lemma subject_reduction e1 e2 s:
    ⊢ e1 : s -> e1 »* e2 -> ⊢ e2 : s.
  Proof.
    induction 2.
    - assumption.
    - eapply preservation; eassumption.
    - auto.
  Qed.
End typing.

(* 4.3.g *)
Notation "A ⊢ e : s" := (typing A e s) (at level 60, e at next level).

Notation "t1 » t2" := (red t1 t2) (at level 60).
Notation "t1 »* t2" := (reds t1 t2) (at level 60).

Definition SN (e : term) := SN_on red e.

Lemma SN_app (e1 : term) e2 :
  SN (e1 e2) -> SN e1.
Proof.
  intro.
  remember (e1 e2) as e1e2 eqn:e.
  revert e.
  revert e1 e2.
  induction H.
  constructor.
  intros.
  eapply H0.
  + subst.
    constructor.
    eassumption.
  + constructor.
Qed.

(* 4.3.h *)
Definition neutral (e : term) :=
  match e with
  | app K _ | K | app (app S _ ) _ | S | app S _ => False
  | _ => True
  end.

Lemma neutral_app e1 e2 :
  neutral e1 -> neutral (e1 e2).
Proof.
  intro.
  revert e2.
  induction e1; intro; simpl; try assumption.
  destruct e1_1; try split.
  simpl in *.
  auto.
Qed.

(* 4.3.i *)
Lemma progress e s:
  ([] ⊢ e : s) -> (exists e', red e e') \/ ~ neutral e.
Proof.
  induction 1.
  - rewrite nth_error_nil in H.
    discriminate.
  - destruct IHtyping1, IHtyping2.
    + left. destruct H1 as (e1' & r1), H2 as (e2' & r2).
      eexists.
      constructor.
      eassumption.
    + destruct H1 as [e1' r1].
      left.
      exists (e1' e2).
      constructor.
      assumption.
    + destruct H2 as [e2' r2].
      left.
      exists (e1 e2').
      constructor.
      assumption.
    + induction e1; auto.
      * induction e1_1; simpl; auto; left.
        ** econstructor.
           apply Kproj.
        ** destruct e1_1_1; eexists; constructor.
           *** econstructor.
           *** simpl in H1.
               contradiction.
           *** simpl in H1.
               contradiction.
  - auto.
  - auto.
    Unshelve.
    all: assumption.
Qed.

(* 4.4 *)
Fixpoint sem_typing (e : term) (s : form) :=
  match s with
  | bot | var _ => SN e
  | s → t => forall e1, sem_typing e1 s -> sem_typing (e e1) t
  end.

Notation "⊨ e : s" := (sem_typing e s) (at level 60, e at next level).

Theorem logical_facts e s :
  (⊨ e : s -> SN e) /\
  (⊨ e : s -> forall e', e »* e' -> ⊨ e' : s) /\
  (neutral e -> (forall e', e » e' -> ⊨ e' : s) -> ⊨ e : s).
Proof.
  revert e.
  induction s; intro.
  1,2:
      split;
      simpl;
      split.
