(** Exercise session 2 — Inductive types

  Part 2

  Similar to last week, when you see REPLACE_ME, replace it with the relevant
  value. Again try to solve the exercises without looking at the live coding
  file. Even if it seems easy when you see us doing it, it might not be so easy
  to do on your own, so try to do it!

  Exercises all start with "EXERCISE".
  When it is written before a lemma, just prove it. :)

**)

Set Default Goal Selector "!".

Axiom REPLACE_ME : forall {A : Type}, A.

From Stdlib Require Import Nat List.
Import ListNotations.

Fixpoint iter {A : Type} (f : A -> A) (n : nat) (x : A) : A :=
  match n with
  | 0 => x
  | S n' => f (iter f n' x)
  end.

(** EXERCISE

  As you can guess, x^n is a notation for x to the power of n.
  You can use
  Locate "^".
  to see what the notation unfold to (here pow) and then
  Print pow.
  to see the definition.

**)
Fact iter_pow n x :
  x^n = iter (mul x) n 1.
Proof.
  induction n.
  - reflexivity.
  - simpl. f_equal. assumption.
Qed.

(** EXERCISE

  Hint: The rewrite tactic can be used to rewrite an equality in the opposite
  direction using rewrite <- e. When e : u = v, it will replace v in the goal
  by u.

**)
Fact iter_shift A (f : A -> A) n x :
  iter f (S n) x = iter f n (f x).
Proof.
  induction n.
  - reflexivity.
  - simpl. f_equal. assumption.
Qed.

Inductive le' : nat -> nat -> Prop :=
| leO' n : le' 0 n
| leS' n m : le' n m -> le' (S n) (S m).

(** EXERCISE

  Spell out the induction principle of le' without checking it.
  Notice that it's *not* the same definition as in the live coding.

  ⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️
  Do not forget this one.

   ind : ∀ P : nat -> nat -> Prop
   -> ∀ n : nat, P 0 n
   -> ∀ n m : nat, le' n m -> P n m -> P (S n) (S m)
   -> ∀ n m : le' n m -> P n m

**)
Check le'_ind.

(** EXERCISE

  Prove the following and lemmas that you need by induction.
  Do not use the standard library or lia!

**)
Lemma le_zero n : le 0 n.
Proof.
  induction n.
  - reflexivity.
  - apply le_S. assumption.
Qed.

Lemma le_succ n m : le n m -> le (S n) (S m).
Proof.
  intro nlem.
  induction nlem.
  - reflexivity.
  - apply le_S. assumption.
Qed.

Lemma le'_succ n m : le' n m -> le' n (S m).
Proof.
  intro nlem. induction nlem.
  - apply leO'.
  - apply leS'. assumption.
Qed.

Lemma le_equiv n m :
  le' n m <-> le n m.
Proof.
  split.
  - revert m. induction n.
    + intros m _. apply le_zero.
    + intros m l'. inversion l'. subst. apply le_succ. apply IHn. assumption.
  - intro nlm. induction nlm.
    + induction n.
      * apply leO'.
      * apply leS'. assumption.
    + apply le'_succ. assumption.
Qed.

(** EXERCISE **)
Fixpoint leb (n m : nat) : bool :=
  match n , m with
  | 0, _ => true
  | S _, 0 => false
  | S n, S m => leb n m
  end.

(** EXERCISE **)

(* Lemma le'b_spec n m : *)
(*   leb n m = true <-> le' n m. *)
(* Proof. *)
(*   split. *)
(*   - intro nlm. *)
(*     induction n. *)
(*     + apply leO'. *)
(*     + destruct m. *)
(*       * simpl in nlm. discriminate. *)
(*       * simpl in nlm. apply leS'. *)
(* Admitted. *)

Lemma leb_spec n m :
  leb n m = true <-> le n m.
Proof.
  induction n as [ | n IH ] in m |- *.
  - simpl. split.
    + intro tr. induction m.
      * constructor.
      * apply le_S. assumption.
    + trivial.
  - split.
    + intro lebsnm. induction m.
      * simpl in lebsnm. discriminate.
      * simpl in lebsnm. apply le_succ. apply IH. assumption.
    + intro snm. simpl. destruct m.
      * inversion snm.
      * apply IH. apply le_equiv in snm. inversion snm. apply le_equiv. assumption.
Qed.

Definition even1 n :=
  exists m, n = 2 * m.

Fixpoint even2 (n : nat) :=
  match n with
  | 0 => true
  | 1 => false
  | S (S n) => even2 n
  end.

(** EXERCISE

  Define an even predicate similar to how you would define a boolean predicate
  but using propositions instead.

**)
Fixpoint even3 (n : nat) : Prop :=
  match n with
  | 0 => True
  | 1 => False
  | S (S n) => even3 n
  end.

Inductive even4 : nat -> Prop :=
| evenO : even4 0
| evenS n : even4 n -> even4 (S (S n)).

(** EXERCISE

  Spell out the induction principle of even4 without checking it.

  ⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️
  Do not forget this one.

   forall P : nat -> Prop, P 0
   -> forall n : nat, even4 n -> P n -> P (S (S n))
   -> forall n : even4 n, P n

**)
Check even4_ind.

(** We now allow you to use [lia]. **)
Require Import Lia.

(** EXERCISE **)
Lemma strong_nat_ind :
  forall (P : nat -> Prop),
    (forall n, (forall m, m < n -> P m) -> P n) ->
    forall n, P n.
Proof.
  intros P SI.
  induction n.
  - specialize (SI 0). apply SI. intros m ineq. inversion ineq.
  - specialize (SI (S n)). apply SI. intros m ineq. inversion ineq.
    + assumption.
    + assert (leq : le (S m) (S n)). {
      apply ineq.
    }

(** EXERCISE

  Hint: If you want to assert an equality (e : a = b) and then use
  rewrite e, then you can also make use of the replace tactic.
  [replace a with b] will replace [a] with [b] in the goal and ask you to prove
  the equality between the two.

**)
Lemma even1_to_even2 n :
  even1 n ->
  even2 n = true.
Proof.
Admitted.

(** EXERCISE **)
Lemma even2_iff_even3 n :
  even2 n = true <-> even3 n.
Proof.
Admitted.

(** EXERCISE

  Hint: The tactic [contradiction] is useful if you have an obviously false
  hypothesis.

**)
Lemma even3_to_even4 n :
  even3 n ->
  even4 n.
Proof.
Admitted.

(** EXERCISE **)
Lemma even4_to_even1 n :
  even4 n ->
  even1 n.
Proof.
Admitted.

(** Membership in a list **)
Fixpoint In {A} (x : A) (l : list A) : Prop :=
  match l with
  | nil => False
  | y :: m => y = x \/ In x m
  end.

(** EXERCISE

  Propose an inductive definition of membership
  (add the missing constructor(s)).

**)
Inductive In_i {A} : A -> list A -> Prop := . (* REPLACE ME *)

(** EXERCISE **)
Lemma In_iff A (x : A) l :
  In x l <-> In_i x l.
Proof.
Admitted.

(** ADVANCED EXERCISES

  Make sure you manage to do the previous exercices before.
  Do not hesitate to ask for help.

**)

(** EXERCISE

  Define the factorial function in two ways:
  - once using Fixpoint
  - and once using iter

  Prove that both yield the same value for all arguments.

  ⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️
  Do not forget this one.
  We have not stated the lemmas this time.

**)

Module Fib_Iter.

  (** EXERCISE

    Define the Fibonnaci function, using only iter (no recursive definition).
    As a reminder fib 0 = 0, fib 1 = 1 and fib (n+2) = fib (n+1) + fib n.

  **)
  Definition fib (n : nat) : nat :=
    REPLACE_ME.

  (** EXERCISE **)
  Lemma fib_eq0 :
    fib 0 = 0.
  Proof.
  Admitted.

  (** EXERCISE **)
  Lemma fib_eq1 :
    fib 1 = 1.
  Proof.
  Admitted.

  (** EXERCISE **)
  Lemma fib_eq3 :
    forall n,
      fib (S (S n)) = fib n + fib (S n).
  Proof.
  Admitted.

End Fib_Iter.

Inductive rtclos {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| refl x : rtclos R x x
| incl x y : R x y -> rtclos R x y
| trans x y z : rtclos R x y -> rtclos R y z -> rtclos R x z.

Inductive rtclos' {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| refl' x : rtclos' R x x
| trans' x y z : R x y -> rtclos' R y z -> rtclos' R x z.

(** EXERCISE

  Hint: You can use [apply f with u] to provide [u] as argument to [f] when
  Rocq can't guess it on its own.

**)
Lemma rtclos'_trans :
  forall A (R : A -> A -> Prop) x y z,
    rtclos' R x y ->
    rtclos' R y z ->
    rtclos' R x z.
Proof.
Admitted.

(** EXERCISE **)
Lemma rtclos_iff :
  forall A (R : A -> A -> Prop) x y,
    rtclos R x y <-> rtclos' R x y.
Proof.
Admitted.

(** Implementation of the Cantor pairing and its inverse function

  We build a bijection between nat * nat and nat.

*)

Require Import PeanoNat.

(** Cantor pairing [to_nat] *)

Fixpoint to_nat' n :=
  match n with
  | 0 => 0
  | S i => S i + to_nat' i
  end.

(** Note the following notation '(x,y) is performing pattern matching
  implicitly.
**)
Definition to_nat '(x, y) : nat :=
  y + to_nat' (y + x).

(** Cantor pairing inverse [of_nat] *)

Fixpoint of_nat (n : nat) : nat * nat :=
  match n with
  | 0 => (0,0)
  | S i =>
    let '(x,y) := of_nat i in
    match x with
    | 0 => (S y, 0)
    | S x => (x, S y)
    end
  end.

(** EXERCISE

  Show that of_nat is a left inverse for to_nat.

**)
Lemma cancel_of_to :
  forall p,
    of_nat (to_nat p) = p.
Proof.
  assert (H : forall n p, to_nat p = n -> of_nat n = p).
  { admit. }
Admitted.

(** EXERCISE

  Show to_nat is injective.

**)
Corollary to_nat_inj :
  forall p q,
    to_nat p = to_nat q ->
    p = q.
Proof.
Admitted.

(** EXERCISE

  Show to_nat is a left inverse for of_nat.

**)
Lemma cancel_to_of :
  forall n,
    to_nat (of_nat n) = n.
Proof.
Admitted.

(** EXERCISE

  Show of_nat is injective.

**)
Corollary of_nat_inj :
  forall n m,
    of_nat n = of_nat m ->
    n = m.
Proof.
Admitted.

(** Church encodings

  It is possible to encode natural numbers (and other data types) using
  so-called Church encodings that you might have seen in a λ-calculus class.
  Below, num is the definition of Church numerals.

**)

Definition num :=
  forall (X : Prop) (s : X -> X) (z : X), X.

Definition zero : num :=
  fun X s z => z.

Definition succ : num -> num :=
  fun n X s z => s (n X s z).

Fixpoint from_nat n : num :=
  match n with
  | 0 => zero
  | S n => succ (from_nat n)
  end.

Definition add : num -> num -> num :=
  fun n m X s z => n X s (m X s z).

Compute (add (from_nat 3) (from_nat 2)).

(** EXERCISE **)
Lemma add_from_nat :
  forall n m,
    add (from_nat n) (from_nat m) = from_nat (n + m).
Proof.
Admitted.

(** EXERCISE **)
Definition mul : num -> num -> num :=
  REPLACE_ME.

(** EXERCISE **)
Lemma mul_from_nat :
  forall n m,
    mul (from_nat n) (from_nat m) = from_nat (n * m).
Proof.
Admitted.

(** EXERCISE

  Define the power function (check out the next exercise to make sure you
  see what it should give).

**)
Definition exp : num -> num -> num :=
  REPLACE_ME.

(** EXERCISE **)
Lemma exp_from_nat n m :
  exp (from_nat n) (from_nat m) = from_nat (n ^ m).
Proof.
Admitted.

(** EXERCISE

  Define a predecessor function.

**)
Definition pred : num -> num :=
  REPLACE_ME.

(** EXERCISE **)
Lemma pred_from_nat n :
  pred (from_nat n) = from_nat (Nat.pred n).
Proof.
Admitted.
