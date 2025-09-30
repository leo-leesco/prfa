(*|
============================
MPRI PRFA — Proof Assistants
============================

`Go back to the course homepage.`_

.. _Go back to the course homepage.: ..

------------------------
Inductive types — part 1
------------------------

This week, we will talk about inductive types. At their basis, inductive
types are similar to algebraic data types from OCaml or Haskell. In Rocq, they
are however more expressive, and can for instance also be used to express
certain logical predicates.
|*)

(*| We first make sure that the use of bullets is enforced: |*)
Set Default Goal Selector "!".

(*|
Inductive types can be defined using the ``Inductive`` keyword.

Below, we give the definition of natural numbers ``nat``. They are exactly the
same as the ones from the standard library which we have seen in the first
lecture.

The type ``nat`` is made of two *constructors*: ``O`` and ``S``.
We have ``O : nat`` and ``S n : nat`` if ``n : nat``.
(Notice how this is ``O`` and not ``0`` as names cannot start with a numeral.
The use of ``0`` is allowed thanks to a notation mechanism.)
Rocq uses BNF (Backus-Naur-form) notation for inductive types:
|*)
Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Check nat.
Check O.
Check S.

(*|
If you look carefully, you will see that Rocq says that ``nat`` is of type
``Set`` when we wrote ``nat : Type``. This is mostly for historical reasons and
you can roughly conflate the two. We encourage you to use ``Type`` though.
|*)

(*| Elements of the type ``nat`` now consist exactly of ``O, S O, S (S O)``, and so on: |*)
Check (S O).
Check (S (S O)).

(*|
The ``Inductive`` command allows syntactic flexibility.
We could also have written the following:

``Inductive nat := | O : nat | S (n : nat) : nat.``

or

``Inductive nat := O | S (n : nat).``
|*)

(*|
In practice you get to pick the variant that suits you the most as they are
anyway equivalent: they merely differ in how you write them, but produce the
same definition.
|*)

(*| As the word inductive type hints, one can do proofs by induction about them.
Mathematically, an inductive type is the *smallest* type closed under the type's
constructors. You are already familiar with induction on natural numbers from
week 1. However, make sure that you are also familiar with the exact formulation
of the induction principle: |*)
Check nat_ind.

(*|
As you have seen in `week 1 <https://mpri-prfa.github.io/render/lesson1.html#defining-functions>`__,
one can define recursive functions operating on inductive arguments with the
``Fixpoint`` keyword:
|*)
Fixpoint add (n m : nat) {struct n} :=
  match n with
  | O => m
  | S n => S (add n m)
  end.

(*| Rocq ensures that recursive functions are terminating, for reasons we will
discuss later.

To ensure termination, recursion has to be performed on a structurally smaller
argument. In the case of ``double`` from last week, there was only one argument
so it was obvious which one had to decrease. This time, there is an ambiguity:
it could be either ``n`` or ``m``. The ``{struct n}`` annotation above tells
Rocq that ``n`` is the one that is structurally decreasing.

Of course, it won't blindly trust us, there is a complex termination checker
(sometimes called guard checker) which will make sure this is indeed the case.
For instance, if you were to suggest that ``m`` was structurally decreasing,
Rocq would rightfully complain: |*)

Fail Fixpoint add' (n m : nat) {struct m} :=
  match n with
  | O => m
  | S n => S (add' n m)
  end.

(*|
The important bit of the error message is the one saying:

    Recursive call to add' has principal argument equal to "m" instead of a
    subterm of "m".

In other words it's complaining about the recursive call being performed on
``m`` again.
|*)

(*|
Note that there are other ways to define functions using more complex
recursion patterns — you will learn about them soon.
|*)

(*|
^^^^^^^^^^^^^^^^^^^^
Evaluating functions
^^^^^^^^^^^^^^^^^^^^

It is possible to evaluate a function, such as the ``add`` function above by
using the ``Eval`` command.

Note how the following evaluates to ``fun m => m`` (the identity function):
|*)

Eval simpl in (fun m => add O m).

(*| However, the following expression cannot be simplified using computation. |*)
Eval simpl in (fun n => add n O).

(*| Instead, we can prove this equation: |*)
Lemma add_0 n :
  add n O = n.
Proof.
  induction n as [| n IHn].
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(*| We can introduce infix notations as follows: |*)
Infix "+" := add.

(*| See how Rocq *prints* the lemma statement using ``+`` now! |*)
Check add_0.

(*| Now, even if we still use ``add``, Rocq will print the goal using ``+``. |*)
Lemma add_S n m :
  add n (S m) = S (add n m).
Proof.
  induction n as [| n IHn].
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(*| We define (truncating) subtraction on natural numbers: |*)
Fixpoint sub (n m : nat) : nat :=
  match n, m with
  | O, _  => O
  | S n', O => n
  | S n', S m' => sub n' m'
  end.

(*|
Note that we did not provide a ``{struct _}`` argument here because Rocq
can infer it automatically.
On paper, we will however often ask you to tell us which argument is
structurally decreasing, so it is good to think for yourself about which
argument decreases when writing a function.
|*)

(*|
Instead of using ``Infix`` to give a notation to ``sub`` we can also use the
``Notation`` command. It asks for more information and is sometimes tricky to
use but it is very powerful.
We will see more examples over the course of the lecture so don't worry too much
about it.
|*)

Notation "n - m" := (sub n m).

(*|
An alternative to ``Eval simpl in e`` is ``Compute e``.
See what it does to the following two expressions.
|*)

Compute (S (S O) - S O). (* 2 - 1 = 1 *)
Compute (S O - S (S O)). (* 1 - 2 = 0 *)

(*|
We can now prove a lemma involving addition and subtraction that we just
defined.
|*)

Lemma add_sub n m :
  (n + m) - n = m.
Proof.
  induction n.
  - simpl. destruct m. all: reflexivity.
  - assumption.
Qed.

(*|
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Predicates, propositions and injectivity of constructors
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In Rocq, everything is computational, including propositions.

We can define the following Boolean predicate testing whether a natural number
is ``0`` or not.
|*)
Definition is_zerob (n : nat) : bool :=
  match n with
  | O => true
  | S n => false
  end.

(*|
But we can also produce directly a proposition asserting asserting whether
the natural number is ``0`` or not.
Pay attention to the use of ``Prop`` instead of ``bool`` and of capital ``True``
and ``False``.
|*)
Definition is_zero (n : nat) : Prop :=
  match n with
  | O => True
  | S n => False
  end.

(*|
Of course, a proposition stating that ``n`` is ``0`` could equivalently be
written as ``n = 0`` as we have seen already.
Similarly, we can express what it means to be different from ``0`` by writing
``n <> 0``, which is Rocq's way of writing ``n ≠ 0`` (in fact, if you use
Unicode with Rocq you can also write ``n ≠ 0`` directly, it is mostly a matter
of taste and getting used to, see our
`FAQ <https://mpri-prfa.github.io/rocq-faq.html#does-rocq-support-unicode>`__ to
know more).
This notation is nothing more than the negation of ``n = 0``, in other words it
unfolds to ``(n = 0) -> False``.

We can use this to prove the fact that, in general, constructors are distinct.
For ``nat`` this means that ``0`` and ``S n`` can always be distinguished.
|*)

Lemma S_O n :
  S n <> O.
Proof.
  (*| This can be proved manually |*)
  intros E.
(*|
We use the ``change`` tactic to change the goal to something equivalent w.r.t.
computation.
|*)
  change (is_zero (S n)).
(*|
We can simplify again to get the old goal.
This is in fact the reason why ``change`` succeeded in the first place.
|*)
  simpl.
  change (is_zero (S n)).
(*|
Now that our goal is ``is_zero (S n)`` we want to use our hypothesis
``E : S n = 0`` to get ``is_zero 0`` instead. We can do this using the
``rewrite`` tactic which will replace occurrence of ``S n`` in the goal by the
right-hand side of the equation, namely ``0``.
|*)
  rewrite E.
(*|
Computation is now handy again, because ``is_zero 0`` is much easier to prove
than ``False``. We simplify and then conclude.
|*)
  simpl.
  split.
Qed.

(*|
There is also a tactic to automatically discharge such goals: ``discriminate``.
|*)
Lemma S_0' n :
  S n <> O.
Proof.
  discriminate.
Qed.

(*|
Say now we want to prove that ``S`` is injective. We can achieve this by
using an auxiliary function ``pred`` such that ``pred (S n) = n``
(in other words, it is a left inverse to ``S``).
By congruence (``f_equal``) we can thus go from ``S n = S m`` to
``pred (S n) = pred (S m)`` which is then the same as ``n = m``.

You can see here that it doesn't matter what value we choose for ``pred 0``.
We're just going to pick ``0``.
|*)

Definition pred n :=
  match n with
  | O => O
  | S n => n
  end.

(*|
We can now prove that ``S`` is injective. It is in fact true for all
constructors.
|*)

Lemma S_inj n m :
  S n = S m -> n = m.
Proof.
  intros E.
  change (pred (S n) = m).
  rewrite E.
  reflexivity.
Qed.

(*| We could in fact do it without ``pred``. |*)
Lemma S_inj_2 n m :
  S n = S m -> n = m.
Proof.
  intros E.
  change (match S n with O => True | S k => k = m end).
  rewrite E.
  reflexivity.
Qed.

(*| We can also use the ``f_equal`` lemma (not the tactic!). |*)
Lemma S_inj_3 n m :
  S n = S m -> n = m.
Proof.
  Check f_equal.
  intros E.
  apply (f_equal pred) in E.
  assumption.
Qed.

(*|
Finally, we have tactics that do this automatically such as ``inversion``.
|*)
Lemma S_inj_4 n m :
  S n = S m -> n = m.
Proof.
  intros E.
  inversion E.
  reflexivity.
Qed.

(*|
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Generalising induction hypotheses
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Let us now try and prove things about functions operating on inductive types.
We're going to start by defining a function for deciding equality between
natural numbers.
|*)

Fixpoint eq_nat x y : bool :=
  match x, y with
  | O, O => true
  | O, S _ => false
  | S _, O => false
  | S x', S y' => eq_nat x' y'
  end.

(*|
We're going to prove that it indeed decides equality of natural numbers.
Below, we make use of the notation ``P <-> Q`` which corresponds to logical
equivalence, in other words the conjunction of ``P -> Q`` and ``Q -> P``.
|*)
Lemma eq_nat_spec n m :
  eq_nat n m = true <-> n = m.
Proof.
  induction n as [ | n' IH]. all: simpl.
(*|
In case you are wondering, we made use of ``all: simpl.`` here to apply the
``simpl`` tactic to all subgoals, before even focusing them. ``all`` is called
a *goal selector* and can be useful in certain situations.
|*)
  - destruct m. all: simpl.
    + split. all: reflexivity.
(*| Notice ``reflexivity`` is able to conclude ``A -> 0 = 0`` for any ``A``. |*)
    + split. all: intros E. all: discriminate E.
(*|
Here we provided ``E`` to ``discriminate`` to tell it which assumption was
inconsistent (equating two distinct constructors).
|*)
  - destruct m.
    + split. all: discriminate.
    +
(*|
We are now stuck. The IH talks about ``S m``, but we need it for ``m``.
Note that this always happens when a recursive function changes other arguments
apart from its structural argument.
|*)
Abort.

(*|
The proper way to deal with this is by generalising the induction hypothesis.
We have to do this before we start perfoming induction.
The reason we have to do this is because Rocq is trying to infer the property
we prove by induction on its own: we only say we want to perform induction on
``n`` and it then tries to infer the property from the goal.
Fortunately, the ``induction`` tactic also supports generalisation with the
keyword ``in``, as follows.
|*)
Lemma eq_nat_spec n m :
  eq_nat n m = true <-> n = m.
Proof.
  induction n as [ | n' IH] in m |- *.
(*|
The syntax is bit heavy: ``m |- *`` represents which information should Rocq
take into account when generating the induction hypothesis. The turnstile ``|-``
is supposed to represent the whole proof goal, with the hypotheses on the left,
and the proposition to prove on the right. We use ``*`` to indicate that we want
to include the goal (which you always will want to do) and ``m`` on the left to
indicate we generalise over it, and nothing else.
|*)
  - destruct m. all: simpl.
    + split. all: reflexivity.
    + split. all: discriminate.
  - (*| See how the IH is quantified for all ``m``. |*)
    destruct m. all: simpl.
    + split. all: discriminate.
    + split. all: intros E.
      * apply IH in E. rewrite E. reflexivity.
      * apply IH. inversion E. reflexivity.
Qed.

(*|
^^^^^^^^
Booleans
^^^^^^^^

Booleans are even simpler.
|*)

Inductive bool := true | false.

Check true.
Check bool.

(*|
Since ``bool`` is not recursive, the induction principle is a lot simpler.
In this case, it makes sense to talk about case anlysis instead.
|*)
Check bool_ind.

(*| Again, since it's an inductive type, the constructors are disjoint. |*)
Lemma true_false :
  true <> false.
Proof.
  discriminate.
Qed.

(*|
^^^^^^^^^^^^^^^^^
Cartesian product
^^^^^^^^^^^^^^^^^

We can define more types, such as the cartesian product.
|*)

(*|
We define product types inductively with one constructor taking two arguments.
|*)
Inductive prod X Y :=
| pair (x : X) (y : Y).

(*| Note how the constructor ``pair`` takes *4* arguments: |*)
Check pair.
(*|
Namely types ``X`` and ``Y``, and elements ``x : X`` and ``y : Y``.

The first two arguments are real arguments that can be passed explicitly:
types are first-class in Rocq.
|*)
Check pair nat.

(*|
Furthermore, types can appear at any position in arguments, unlike OCaml
where the quantification is necessarily prenex.
|*)
Definition pair' X (x : X) Y (y : Y) :=
  pair X Y x y.

Check pair'.

(*| Also, the type arguments *have to* be passed. |*)
Fail Check pair' 0 0.

(*|
However, we can declare arguments as *implicit* using the ``Arguments``
command by marking implicit arguments with braces ``{}``
(sometimes called squigly brackets).
|*)
Arguments pair' {X} x {Y} y.

(*|
When an argument is implicit, Rocq tries to infer what it has to be, based
on the other passed arguments.
If we build the pair ``(O,O)`` then both types *have to be* ``nat`` and Rocq is
able to figure it out.
|*)
Check pair' O O.

(*|
We can use the following command to force Rocq to print implicit arguments.
|*)
Set Printing Implicit.

(*|
There we can see the ``nat`` that have been inferred.
|*)
Check pair' O O.

(*| We go back to not printing implicit arguments. |*)
Unset Printing Implicit.

(*| We can define the first projection by pattern matching. |*)
(*| Note that we mark arguments as implicit directly. |*)
Definition fst {X Y} (p : prod X Y) : X :=
  match p with
  | pair _ _ x y => x
  end.

(*|
**Remark:**
In the pattern matching above, we had to also talk about the
type parameters of ``pair`` even though they are not necessary.
By making them implicit in the constructor ``pair``, we can write nicer
pattern matching.
|*)

Arguments pair {X Y} x y.

Definition snd {X Y} (p : prod X Y) : Y :=
  match p with
  | pair x y => y
  end.

(*|
^^^^^
Lists
^^^^^
|*)

  (*| The type of list is both recursive and has a type parameter. |*)
Inductive list (A : Type) :=
| nil : list A
| cons : A -> list A -> list A.

(*|
We declare arguments as implicit. Note here we can specify a prefix if we want.
|*)
Arguments nil {A}.
Arguments cons {A}.

Set Printing Implicit.
Compute (cons 5 nil).
Unset Printing Implicit.

(*|
Check now the induction principle we get for lists.
It's saying that to prove ``P l`` for some list ``l``, you only need to prove

  * ``P nil``
  * ``P (cons a l')`` for any ``a`` and ``l'`` such that ``P l'``

Have a look at its type:
|*)
Check list_ind.

(*|
^^^^^^^^^^^^^^^^^^^
Proofs by induction
^^^^^^^^^^^^^^^^^^^

We reimport all these datatypes from Rocq, to be able to use functions from the
standard library.
|*)

From Stdlib  Require Import Datatypes List.
Open Scope nat.

(*|
Like for ``nat``, ``list`` in the standard library comes with nice notations
to be able to write ``x :: l`` or ``[ a ; b ; c ; d ]``.
We can load them as follows.
|*)
Import ListNotations.

(*| Below we check the types of concatenation and reversal of lists. |*)
About app.
About rev.

(*|
Lemmas about lists we typically proven by induction as we did for natural
numbers.
|*)
Lemma app_nil_r A (l : list A) :
  l ++ nil = l.
Proof.
  induction l. all: simpl.
  - reflexivity.
  - f_equal. assumption.
Qed.

Lemma rev_app_distr {A} (l1 l2 : list A) :
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  induction l1 as [| a l IHl]. all: simpl.
  - rewrite app_nil_r. reflexivity.
  - (*| For ``rewrite`` we can separate two lemmas to rewrite by a comma. |*)
    rewrite IHl, app_assoc. reflexivity.
Qed.

Lemma rev_rev {A} (l : list A) :
  rev (rev l) = l.
Proof.
  induction l. all: simpl.
  - reflexivity.
  - rewrite rev_app_distr. simpl. rewrite IHl. reflexivity.
Qed.

(*|
The ``rev`` defined above is not very smart because it uses concatenation
on the right which is expensive. However, it works as a specification for a
smarter version using an accumulator.
|*)
Fixpoint fast_rev {A} (l : list A) (acc : list A) :=
  match l with
  | [] => acc
  | x :: l => fast_rev l (x :: acc)
  end.

(*| We can show the two behave the same. |*)
Lemma fast_rev_eq {A} (l : list A) :
  fast_rev l nil = rev l.
Proof.
  induction l. all: simpl.
  - reflexivity.
  - (*| We are stuck again, because the ``acc`` argument is changed. |*)
Abort.

Lemma fast_rev_eq {A} (l : list A) :
  fast_rev l nil = rev l.
Proof.
(*|
We prove a more general lemma locally.
We're using ``forall`` here to introduce a parameter.
|*)
  assert (H : forall acc, fast_rev l acc = rev l ++ acc).
  { induction l as [| a l IHl]. all: simpl. all: intros acc.
    - reflexivity.
    - rewrite IHl. rewrite <- app_assoc. reflexivity.
  }
  rewrite H. Search app nil. rewrite app_nil_r. reflexivity.
Qed.

(*| We can prove things in a different way. |*)
Lemma fast_rev_eq_alt {A} (l : list A) :
  fast_rev l nil = rev l.
Proof.
(*|
We are going to generalise the empty list to any ``acc``.
We write ``@nil A`` to provide the type argument ``A`` explicitly.
|*)
  rewrite <- app_nil_r. generalize (@nil A) as acc.
  induction l as [| a l IHl]. all: simpl. all: intros acc.
  - reflexivity.
  - rewrite IHl. rewrite <- app_assoc. reflexivity.
Qed.
