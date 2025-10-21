(** * MPRI PRFA — Exercise session 5 **)

From Stdlib Require Import RelationClasses Arith Lia List.
Import ListNotations.

(** ** Sorts ***)

(** Elimination restrictions **)

(** EXERCISE

  Define a copy of Booleans called prop_bool that lives in Prop.
  Show that you can go from bool to prop_bool.
  Can you do the converse? Why?
  What does a surjective function from prop_bool to bool would mean for
  proof irrelevance? (We want to see a proof.)

**)

Inductive prop_bool : Prop :=
  | prop_true
  | prop_false.

Definition b2pb (b:bool) : prop_bool :=
  if b then prop_true else prop_false.

Fail Definition pb2b (pb : prop_bool) : bool :=
  match pb with
  | prop_true => true
  | prop_false => false
  end.

Definition PI :=
  forall (P : Prop) (p q: P), p = q.

Lemma notPI (f : prop_bool -> bool) : (exists pb, f pb = true) /\ (exists pb, f pb = false) -> not PI.
Proof.
  intros [pbt pbf].
  intro PI.
  destruct pbt as [pbt ft].
  destruct pbf as [pbf ff].
  specialize (PI prop_bool pbt pbf).
  rewrite PI in ft.
  rewrite ft in ff.
  discriminate.
Qed.

(** EXERCISE

  Prove that for all p : prop_bool, there exists some b : bool such that
  its mapping to prop_bool is equal to p.

**)

Goal forall (p : prop_bool), exists (b:bool), b2pb b = p.
Proof.
  intros. destruct p.
  - exists true. trivial.
  - exists false. trivial.
Qed.

(** EXERCISE

  exists (x : A), P x and { x : A | P x } are two very similar types but the
  former lives in Prop. Show how one implies the other.
  Why is the other implication not provable?

**)

Goal forall (A:Type) (P : A -> Prop), (exists (x: A), P x) -> {x : A | P x}.
Proof.
  intros ? ? H. Fail destruct H as [x Px].
Abort. (* not provable because we have a Type instead of Prop which is not impredicative *)

Goal forall (A:Type) (P : A -> Prop), {x : A | P x} -> (exists (x: A), P x).
Proof.
  intros ? ? X. destruct X as [x Px].
  eauto.
Qed.

(** EXERCISE

  Similarly, P \/ Q and A + B are similar types. The first you know as
  disjunction of propositions, the other one is relevant data that either
  contains either a value of type A, or a value of type B.

  Prove that P + Q -> P \/ Q both with a proof script and a proof term.

  Why is the other implication not provable?

**)

Goal forall (A B : Prop), A + B -> A \/ B.
Proof.
  intros.
  destruct H; auto.
  Show Proof.
Qed.

Locate "+".
Print sum.

(** EXERCISE

  We can't show that (exists x, P x) -> { x : A | P x } in general, but we can
  when A is bool and when P x is of the form f x = true. Show it.

**)

Goal forall (f : bool -> bool), (exists (x: bool), f x = true) -> {x : bool | f x = true}.
Proof.
  intros f H.
  destruct (f true) eqn:htrue.
  - now exists true.
  - destruct (f false) eqn:hfalse.
    + now exists false.
    + exfalso. destruct H as [[] fx].
      * rewrite fx in htrue. discriminate.
      * rewrite fx in hfalse. discriminate.
Qed.

(** ** Singleton elimination **)

(** EXERCISE

  Write a term that goes from False to any A : Type.

**)

Goal forall (A:Type), False -> A.
Proof.
  intros.
  exfalso. assumption.
Qed.

(** EXERCISE

  We have seen above that disjunction did not satisfy the subsingleton
  criterion. What about conjunction?
  Either give a proof script that fails because conjunction does not satisfy
  the subsingleton criterion, or give a proof script that works because it does.

**)

Goal forall {A B}, A /\ B -> A * B.
Proof.
  intros. split; destruct H; assumption.
Qed.

(** EXERCISE

  Propose a version of [le] that is a singleton.
  You can use the goal below with le (<=) and with your le'.
  It should only work with le'.
  Is it satisfying? If not you can try and think if you can't define one
  (perhaps not with the Inductive keyword) that works better.

**)

Goal forall n m, n <= m -> nat.
Proof.
  intros n m h.
  Fail destruct h.
Abort.

(** ** Induction principles ***)

(** EXERCISE

  Define an inductive type bintree for binary trees.

  As for every inductive type, Rocq generates induction principles corresponding
  to the various sorts:
  - bintree_ind for Prop
  - bintree_rect for Type
  - bintree_rec for Set (but you can ignore it and use bintree_rect)

  Write down both type and term for bintree_rect manually.

**)

Inductive bintree (A:Type) :=
  | leaf (x : A)
  | node (left : bintree A) (right : bintree A).

(** EXERCISE

  Define a map function for it, and show mapping with the identity results in
  the identity on binary trees.

**)

(** EXERCISE

  Define an inductive type tree of trees taking a list of children.
  - Show that all binary trees can be seen as trees.
  - Define a map function for tree.
  - Show that turning a binary tree into a tree then mapping is the same as
    mapping first then turning into a tree.

**)

(** EXERCISE

  Now if you want to show that mapping with the identity on tree results in
  the identity function, you will be in trouble because
  tree_ind (use Check or About to see its type)
  does not carry any induction hypothesis.

  Taking inspiration from tree_ind, implement some good_tree_ind that has an
  induction hypothesis for the list of children.
  Hint: You may use the Forall P l which says that P x holds for every x in l.

  To do the proof, you can use the tactic fix like
  fix ind 1
  to perform recursion on the first argument in the goal and call
  ind the recursive call.
  You will need to do to nested fixpoints, one for the tree and one for the list
  of children.

  This is hard to get right, so you can also admit it and move on.

**)

(** EXERCISE

  Use induction using good_tree_ind to prove that mapping with the identity
  function on tree results in the identity function.

**)

(** EXERCISE Strong induction on natural numbers

  We have seen it already, but show it again and use it to prove the following
  lemma that corresponds to induction on natural numbers with access to the
  two previous cases.

**)

Lemma nat_ind_2 :
  forall (P : nat -> Prop),
    P 0 ->
    P 1 ->
    (forall n, P n -> P (S n) -> P (S (S n))) ->
    forall n, P n.
Proof.
Admitted.

(** EXERCISE

  Use the induction tactic with nat_ind_2 to prove that the fibonacci sequence
  is always above its index (n <= fib n).

**)

Fixpoint fib n :=
  match n with
  | 0 => 1
  | 1 => 1
  | S (S n as m) => fib n + fib m
  end.

(** ** Well-founded induction **)

(** EXERCISE

  We're going to show that from (exists n, f n = true) one can exhibit a
  natural number n for which f n = true in the form of { n | f n = true },
  in a different way than in the lecture.

  Prove the admitted lemmas below.

*)

Section ConstructiveIndefiniteGroundDescription_Acc.

Context (P : nat -> Prop).

Hypothesis P_decidable : forall (n : nat), {P n} + {~ P n}.

Let R (x y : nat) : Prop := x = S y /\ ~ P y.

Local Notation acc x := (Acc R x).

Lemma P_implies_acc : forall x : nat, P x -> acc x.
Proof.
Admitted.

Lemma P_eventually_implies_acc : forall (x : nat) (n : nat), P (n + x) -> acc x.
Proof.
Admitted.

Corollary P_eventually_implies_acc_ex : (exists n : nat, P n) -> acc 0.
Proof.
Admitted.

Theorem acc_implies_P_eventually : acc 0 -> {n : nat | P n}.
Proof.
intros Acc_0. pattern 0.
induction Acc_0 as [x H IH].
(* now use decidability of P *)
Admitted.

Theorem constructive_indefinite_ground_description_nat_Acc :
  (exists n : nat, P n) -> {n : nat | P n}.
Proof.
Admitted.

End ConstructiveIndefiniteGroundDescription_Acc.

(** Defining functions by well-founded recursion.

  We have seen well-founded induction, but sometimes we also want to define
  functions like that. The standard library comes with a helpful function for
  doing that called Fix_F. It performs induction on accessibilty like we have
  been doing.

**)

About Fix_F.

(** EXERCISE

  Implement a merge function on lists such that if l and r are individually
  sorted, then merge l r should be sorted too.
  This function is the main ingredient for the merge sort algorithm.

  We give you the version one would write in OCaml and you have to adapt it into
  a function accepted by Rocq.
  We're using lists of natural numbers to make it simpler but it could be
  generalised of course.

  Hint: You may have to pack arguments together to make it work.

  Next, prove a specification for merge that ensures it preserves sortedness
  and that the result is a permutation of the original lists. You can use a
  weak version of permutation that doesn't account for multiplicity.

  We give you some lemmas about sorted and wpermut that you may or may not use.
  This is so you don't waste too much time on those. We expect you to begin
  by admitting them, but you should be able to prove them.

  Hint: If you want to do induction on Acc, you should prove a better induction
  principle for it because the generated one isn't enough.

**)

Fail Fixpoint merge (l r : list nat) : list nat :=
  match l, r with
  | [], r => r
  | l, [] => l
  | x :: l, y :: r =>
    if x <? y
    then x :: merge l (y :: r)
    else y :: merge (x :: l) r
  end.

Inductive sorted : list nat -> Prop :=
| sorted_nil : sorted []
| sorted_cons : forall x l, sorted l -> Forall (le x) l -> sorted (x :: l).

Definition wpermut (l r : list nat) : Prop :=
  forall x, In x l <-> In x r.

#[export] Instance wpermut_refl : Reflexive wpermut.
Proof.
Admitted.

#[export] Instance wpermut_sym : Symmetric wpermut.
Proof.
Admitted.

#[export] Instance wpermut_trans : Transitive wpermut.
Proof.
Admitted.

Add Parametric Relation : (list nat) wpermut as wpermut_rel.

Lemma Forall_wpermut :
  forall P l r,
    wpermut l r ->
    Forall P r ->
    Forall P l.
Proof.
Admitted.

Lemma wpermut_cons :
  forall x l r,
    wpermut l r ->
    wpermut (x :: l) (x :: r).
Proof.
Admitted.

Lemma wpermut_app :
  forall l r,
    wpermut (l ++ r) (r ++ l).
Proof.
Admitted.

Lemma sorted_cons_inv :
  forall x l,
    sorted (x :: l) ->
    sorted l /\ Forall (le x) l.
Proof.
Admitted.

(** ** ADVANCED EXERCISES ***)

(** Axiom of choice

  We're going to show the Bishop-Diaconescu-Myhill-Goodman theorem.
  It shows that the axiom of choice implies excluded middle with sufficient
  extensionality.

  There are several versions of the axiom of choice.
  One is Hilbert's epsilon operator which takes a property on a type, and
  returns an element of that type that verifies the property if such an element
  exists. To avoid inconsistencies, we have to restrict this operator to
  inhabited types.

**)

Section Hilbert.

  (**
    inhabited A is just a proposition from which you cannot extract the
    witness.
  **)
  Context (epsilon : forall A, inhabited A -> (A -> Prop) -> A).

  (**
    If there is an element verifying the property, then the one epsilon gave
    us also verifies it.
  **)
  Context (epsilon_spec :
    forall A i P,
      (exists x, P x) ->
      P (epsilon A i P)).

  (**
    We also need some extensionality to tell us that the choice does not
    depend on how the property was formulated.
  **)
  Context (epsilon_ext :
    forall A i P Q,
      (forall x, P x <-> Q x) ->
      epsilon A i P = epsilon A i Q
  ).

  (** EXERCISE

    Prove the law of excluded middle 

    Hint: You can use epsilon with some property like x = true \/ P and same
    with false.

  **)

End Hilbert.

(** From relation to function

  Another version of the axiom of choice says that from an entire relation,
  one can extract a function. It's a form of inversion of quantifiers.

**)

Definition fun_choice :=
  forall A B (R : A -> B -> Prop),
    (forall x, exists y, R x y) ->
    exists (f : A -> B),
      forall x, R x (f x).

(** EXERCISE

  Show that fun_choice implies LEM under the assumption of proposition and function extensionality.

  The proof should share some ideas with the one above and could involve some
  function from { p : bool -> Prop | p = B \/ p = C } -> bool
  with carefully chosen B and C.

**)

Definition FunExt :=
  forall A B (f g : A -> B),
    (forall x, f x = g x) ->
    f = g.

Definition PropExt :=
  forall (P Q : Prop), P <-> Q -> P = Q.

(** ADVANCED ADVANCED EXERCISE

  PI (forall P : Prop, forall h1 h2 : P, h1 = h2) suffices to prove that choice
  implies ELEM := forall A : Type, forall a b : A, a = b \/ ~ (a = b)

*)

(** ADVANCED ADVANCED ADVANCED EXERCISE

  Read the documentation of SProp and see whether you can prove that choice for
  SProp implies LEM for SProp (without any additional assumption).

*)
