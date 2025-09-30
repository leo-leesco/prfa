(*|
============================
MPRI PRFA — Proof Assistants
============================

`Go back to the course homepage.`_

.. _Go back to the course homepage.: ..

------------------------
Inductive types — part 2
------------------------

We continue after `part 1 <lesson2_part1.html>`__, still looking at
inductive types.
|*)

From Stdlib  Require Import List.
Import ListNotations.

Set Default Goal Selector "!".

(*|
^^^^^^^^^^^^^^^
Dependent pairs
^^^^^^^^^^^^^^^

We define the type of dependent pairs, where the second component can
depend on the first. We often call those Σ-types (hence the name ``sigT``).
|*)
Inductive sigT {A} (B : A -> Type) :=
| existT (a : A) (b : B a) : sigT B.

Arguments existT {A B}.

(*|
For instance, we can create a type of pairs, where the first component
is always a boolean ``b``, but the second is of type ``nat`` when ``b`` is
``true`` and of type ``list nat`` otherwise.
|*)
Definition T := sigT (fun (b : bool) => if b then nat else list nat).

(*|
We can then create two elements of type ``T``, a pair ``(true, 17)`` and a
pair ``(false, [ 90 ; 4 ; 8 ])``. This is something you could not do without
dependent types (so for instance, not in OCaml).
|*)

Definition pair1 : T :=
  existT true 17.

Definition pair2 : T :=
  existT false [ 90 ; 4 ; 8 ].

(*|
Important, you should have a look at the induction principle for dependent
pairs.
|*)

Check sigT_ind.

(*|
**Remark.**
In the standard library, you have a notation for ``sigT``: you can write
``{ x : A & B x }`` for ``sigT B``. This looks like the usual subset notation.
|*)

(*|
Similar to how a function of type ``A * B -> C`` is the same as ``A -> B -> C``
(which we call currying), we can turn a function of type ``sigT {A} B -> C`` to
a (dependent) function of type ``forall (x : A), B x -> C``.

Notice that ``forall`` can work for dependent functions and not just for
propositions.
|*)
Definition cur {A} {B : A -> Type} {C} (f : sigT B -> C) :
  forall (x : A), B x -> C :=
  fun a b => f (existT a b).

(*| We can perform the opposite transformation. |*)
Definition car {A} {B : A -> Type} {C} (f : forall x, B x -> C) :
  sigT B -> C :=
  fun p =>
    match p with
    | existT a b => f a b
    end.

(*| And now we can prove that they are indeed inverse of each other. |*)
Lemma car_cur A (B : A -> Type) C (f : sigT B -> C) p :
  car (cur f) p = f p.
Proof.
  destruct p as [a b]. reflexivity.
Qed.

(*|
The other direction is even simpler, there is nothing to destruct so the proof
is direct by reflexivity.
|*)
Lemma cur_car A (B : A -> Type) C (f : forall (x : A), B x -> C) a b :
  cur (car f) a b = f a b.
Proof.
  reflexivity.
Qed.

(*|
^^^^^^^^^^^^^^^^^^^^^
Polymorphic iteration
^^^^^^^^^^^^^^^^^^^^^

We will now have a look at ``iter``, a function such that ``iter f n x``
applies ``n`` times the function ``f``, starting with the argument ``x``.
For instance ``iter f 2 x`` is ``f (f x)``.
|*)

Fixpoint iter {A : Type} (f : A -> A) (n : nat) (x : A) : A :=
  match n with
  | 0 => x
  | S n' => f (iter f n' x)
  end.

(*|
We can show that iterating the successor ``n`` times is the same as adding
``n``.
|*)
Lemma iter_add n x :
  n + x = iter S n x.
Proof.
  induction n as [|n IH]. all: simpl.
  - reflexivity.
  - f_equal. assumption.
Qed.

(*| Similarly, multiplication is iterated addition. |*)
Lemma iter_mul n x :
  n * x = iter (Nat.add x) n 0.
Proof.
  induction n as [|n IH]. all: simpl.
  - reflexivity.
  - f_equal. assumption.
Qed.

(*|
^^^^^^^^^^^^^^^^^^^^^^^
Indexed inductive types
^^^^^^^^^^^^^^^^^^^^^^^
|*)

(*| We can define predicates using the ``Inductive`` keyword as well. |*)
Inductive even : nat -> Prop :=
| evenO : even 0
| evenS n : even n -> even (S (S n)).

(*|
Being inductive, their proofs can be constructed using the ``constructor``
tactic.

Note: The ``Goal`` command is similar to ``Lemma`` except it doesn't require a
name for a lemma which is useful when just checking things that are not
useful later such as the fact the ``4`` is even…
|*)
Goal even 4.
Proof.
  constructor. constructor. constructor.
Qed.

(*| Case analysis works using ``inversion``. |*)
Goal ~ even 3.
Proof.
  intros h.
  inversion h.
(*|
Here we learnt from ``even 3`` that to build it we must have had ``even 1``
first.
|*)
  inversion H0.
(*|
But there is no rule (neither ``evenO`` nor ``evenS``) that can *unify* with
``even 1`` so there is no goal left, we are done!
|*)
Qed.

(*|
``inversion`` is useful but it is hard to predict its behaviour and to
name the resulting hyoptheses. So we might want to use regular case analysis
instead, ie. use ``destruct``.
|*)
Goal ~ even 3.
Proof.
  intro h.
  destruct h.
(*|
Here this quite terrible because ``destruct`` completely forgets about
the fact we had ``3`` so we are left with an unprovable goal.
|*)
Abort.

(*|
There is a way to recover this information by telling Rocq to remember it
as an equality using the ``remember`` tactic.
|*)
Goal ~ even 3.
Proof.
  intro h.
  remember 3 as n eqn: e.
  destruct h.
  -
(*|
See that ``n`` has been replaced by ``0`` but since we also kept the
equality ``e`` we know this case is impossible.
|*)
    discriminate.
  -
(*| In the other branch, we have that ``3`` must be ``2 + n`` for some even ``n``
which is also impossible but requires noticing that ``n`` must be ``1``.
``inversion`` on the equality will give us that.
|*)
    inversion e.
(*| We can then use ``subst`` to automatically substitute ``n`` by ``1``. |*)
    subst.
(*| We can now rely on ``inversion`` again to discharge the goal. |*)
    inversion h.
Qed.

(*|
Rather than an inductive predicate, we can also define a Boolean function
that checks whether its argument is even.
|*)
Fixpoint evenb n :=
  match n with
  | 0 => true
  | 1 => false
  | S (S n) => evenb n
  end.

(*| We can show that the two are equivalent. |*)
Lemma even_to_evenb n :
  even n ->
  evenb n = true.
Proof.
  intros h.
  (*| We can perform induction on the proof! |*)
  induction h.
  - reflexivity.
  - simpl. assumption.
Qed.

(*| And now the other direction. |*)
Lemma evenb_to_even n :
  evenb n = true ->
  even n.
Proof.
  intros h.
(*| This time we have to perform the induction on ``n``. |*)
  induction n as [ | n ih].
  - constructor.
  - destruct n.
    + simpl in h. discriminate.
    + constructor.
(*|
Note how we are stuck here: The inductive hypothesis talks about ``S n``
instead of ``n``. But this we cannot generalise.
|*)
Abort.

(*|
The solution is to use a stronger form of induction that lets you conclude
about any smaller argument.
We'll require ``Lia`` which provides the ``lia`` tactic
(for linear integer arithmetic) to help us deal with some arithmetic goals.
|*)

From Stdlib Require Import Lia.

(*|
In the induction principle below we use ``forall`` which is used to quantify
over anything from natural numbers to propositions.
We can use ``intros`` to introduce those variables, the same way we do it for
implication.

The strong induction principle is as you'd expect: to prove some property ``P``
about ``n``, you can assume it holds for all natural numbers that are smaller.
|*)

Lemma strong_nat_ind :
  forall (P : nat -> Prop),
    (forall n, (forall m, m < n -> P m) -> P n) ->
    forall n, P n.
Proof.
  intros P h n.
(*|
We'll show a stronger property by induction, that ``P`` is valid for ``n`` and
everything below.
|*)
  assert (hn : forall m, m <= n -> P m).
  { induction n as [| n ih].
    - intros m hm. inversion hm.
      apply h. intros k hk. lia.
(*|
``lia`` knows there can't be ``k < 0`` so it solves the goal for us.
It is implictly using a proof of ``~ k < 0`` together with ``False``
elimination.
|*)
    - intros m hm. inversion hm.
      + apply h. intros k hk. apply ih. lia.
      + apply ih. lia.
  }
  apply hn. lia.
Qed.

(*|
Back to ``even``.
We can now use our stronger induction principle thanks to the ``using`` clause
of the ``induction`` tactic. Indeed, the tactic can use anything that *looks
like* an induction principle (which is admittedly a vague notion) which can be
very handy!
|*)
Lemma evenb_to_even n :
  evenb n = true -> even n.
Proof.
  intros h.
  induction n as [n ih] using strong_nat_ind.
(*|
As opposed to regular induction, we only have one case to consider: an arbitrary
``n`` but for which we have an induction hypothesis.
We still need to perform case analysis, so we'll do it manually.
We have to consider the cases ``0``, ``1`` and ``S (S n)``.
We could perform ``destruct n`` once to get cases `0` and `S n` and then in
the second branch do ``destruct`` again, but we can do it all at once by using
square brackets within square brackets.
|*)
  destruct n as [| [| n]].
  - constructor.
  - simpl in h. discriminate.
  - simpl in h. constructor.
    apply ih.
    + lia.
    + assumption.
Qed.

(*|
The "less than" predicate ``<=`` we have used above is defined as follows.

The idea is that ``n ≤ n`` always holds, and if ``n ≤ m`` then ``n ≤ S m``.
In other words, if you can remove successors ``S`` from ``m`` and reach ``n``
then ``n ≤ m``.
|*)
Inductive le : nat -> nat -> Prop :=
| leO n : le n n
| leS n m : le n m -> le n (S m).

(*|
We build the proof as hinted above, by removing ``S`` from ``5`` until we reach
``3`` which takes only two steps.
|*)
Goal le 3 5.
Proof.
  constructor. constructor. constructor.
Qed.

(*| To show that ``1`` is *not* below ``0`` we can use ``inversion`` again. |*)
Goal ~ le 1 0.
Proof.
  intros h. inversion h.
Qed.

(*| As for ``even`` we can also do it more manually. |*)
Goal ~ le 1 0.
Proof.
  intros h. remember 1 as n1 eqn: e1. remember 0 as n0 eqn: e0.
  destruct h.
  - subst. discriminate.
  - subst. discriminate.
Qed.

(*|
As a sanity check, we can verify the following property.

Below ``exists (x : A), P x`` is very similar to ``sigT P`` except that ``P x``
is a proposition. We can prove ``exists x, P x`` by *e.g.,* using ``exists 0``
and then proving ``P 0``.
|*)
Lemma le_iff n m :
  le n m <-> exists k, k + n = m.
Proof.
  split.
  - intros h. induction h as [n | n m h ih].
    + exists 0. reflexivity.
    + destruct ih as [k ih]. subst.
      exists (S k). simpl. reflexivity.
  -
(*|
Instead of doing ``intro x`` and then ``destruct x as [a b]`` we can do
``intros [a b]``.
|*)
    intros [k h]. subst.
    induction k as [| k ih].
    + simpl. constructor.
    + simpl. constructor. assumption.
Qed.

(*| We can also show transitivity. |*)
Lemma le_trans n m k :
  le n m ->
  le m k ->
  le n k.
Proof.
  intros hnm hmk. induction hmk as [ m | m k hmk ih ].
  - assumption.
  - constructor. apply ih. assumption.
Qed.

(*|
We can also define the notion of reflexive transitive closure of a relation
``R : A -> A -> Prop`` on ``A`` like so.
|*)
Inductive rtclos {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| refl x : rtclos R x x
| incl x y : R x y -> rtclos R x y
| trans x y z : rtclos R x y -> rtclos R y z -> rtclos R x z.

Arguments trans {A R}.

(*| Then ``le`` is just the closure of being the successor. |*)
Lemma le_rtclos n m :
  le n m <-> rtclos (fun n m => m = S n) n m.
Proof.
  split.
  - intros h. induction h as [ n | n m h ih ].
    + constructor.
    +
(*|
If we just apply ``constructor`` then it's going to pick ``incl``
which is not what we want. What we want is to use ``trans``:
|*)
      apply (trans _ m _). 1: assumption.
(*| We just applied ``assumption`` to the first goal this way. |*)
(*| It can be nicer than having many levels of nested bullets. |*)
      constructor. reflexivity.
  - intros h. induction h as [ n | n m h | n m k hnm ihnm hmk ihmk ].
    + constructor.
    + subst. constructor. constructor.
    + apply (le_trans _ m _). all: assumption.
Qed.
