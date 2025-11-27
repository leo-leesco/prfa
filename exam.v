From Stdlib Require Import Utf8.
From Stdlib Require Import List.
Import ListNotations.

Fixpoint nat_ind : ∀(P : nat → Prop), P 0 → (∀n, P n → P (S n)) →∀n, P n :=
  fun P P0 rec n =>
  match n with
  | 0 => P0
  | S n => rec n (nat_ind P P0 rec n)
  end.

Inductive Exists {A : Type}(P : A → Prop) : list A → Prop :=
| Exists_base : ∀(x : A) (l : list A), P x → Exists P (x :: l)
| Exists_cons : ∀(x : A) (l : list A), Exists P l → Exists P (x :: l).

Definition Exists_rec {A : Type} (P0 : A -> Prop) :=
  forall (P : forall l, Exists P0 l -> Prop),
  (forall x l0 Px, P (x :: l0) (Exists_base P0 x l0 Px)) ->
  (forall x l0 Pl, P l0 Pl -> P (x :: l0) (Exists_cons P0 x l0 Pl)) ->
  forall l Pl, P l Pl.

Definition Exists_recprop {A : Type} (P0 : A -> Prop) :=
  forall (P : list A -> Prop),
  (forall x l, P0 x -> P (x :: l)) ->
  (forall x l, P l -> Exists P0 l -> P (x :: l)) ->
  forall l, Exists P0 l -> P l.

Goal forall (A : Type), False -> A.
Proof.
  intros.
  contradiction.
  Show Proof.
Qed.

Definition test (A : Type) : False -> A :=
  fun f => match f with end.

Inductive ex (A : Type) (P : A → Prop) : Prop :=
| ex_intro (a : A) (p : P a).

Notation "∃ x, P" := (ex _ (fun x => P)).

Inductive sig (A : Type) (P : A → Prop) : Type :=
| exist (a : A) (p : P a).

Notation "{ x | P }" := (sig _ (fun x => P)).

Goal forall A (P : A -> Prop),  { x |P x } -> (ex _ (fun x => P x)).
Proof.
  intros.
  destruct X.
Abort.
Goal nat + (bool → bool).
Proof.
  constructor ; intro x.
(* constructor. intro x. *)
Abort.
