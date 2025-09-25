(*|
============================
MPRI PRFA — Proof Assistants
============================

`Go back to the course homepage.`_

.. _Go back to the course homepage.: ..

-------------------------------
Introduction to the Rocq Prover
-------------------------------

This course teaches you how to use one proof assistant (Rocq), with the goal to

- be able to use Rocq in other courses,
- use Rocq in an internship,
- learn other proof assistants or become an expert user of Rocq via self study,
- ultimately use or study proof assistants as part of a PhD.

In particular, we believe that taking this course will allow you to learn other proof assistants, e.g. `Agda`_, `Isabelle`_, or `Lean`_, via self study, very quickly. Note that the `MPRI HOTT`_ course teaches Agda in more detail, relying on you having learnt about proof assistants in this course.

.. _MPRI HOTT: https://mpri-master.ens.fr/doku.php?id=cours:hott

.. _Agda: https://agda.readthedocs.io/en/latest/getting-started/what-is-agda.html

.. _Isabelle: https://isabelle.in.tum.de/

.. _Lean: https://lean-lang.org/

You should have installed Rocq before attending, but in case you haven't, please consult `our page about installing Rocq`_.

.. _our page about installing Rocq: ../installrocq.html

In this first lecture, we will introduce fundamentals of Rocq and proof assistants in general:

* propositional logic
* proofs by case analysis
* proofs by induction

.. raw:: html

  <hr>

.. raw:: html

  Note that this document is being interpreted from Rocq files by
  <a href="https://github.com/cpitclaudel/alectryon/">Alectryon</a>.
  Bubbles (<span class="alectryon-bubble"></span>) indicate interactive
  fragments: hover for details, click to reveal contents.
  Use <kbd>Ctrl+↑</kbd> and <kbd>Ctrl+↓</kbd> to navigate,
  <kbd>Ctrl+🖱️</kbd> to focus.
  On macOS, use <kbd>⌘</kbd> instead of <kbd>Ctrl</kbd>.

.. raw:: html

  <hr>

Let's get started with proving a first simple fact about propositional logic: If ``P`` holds, then ``P`` holds, i.e., an implication.

Implications are written ``->`` in Rocq.

To prove a fact, one writes ``Lemma name : statement.`` Lemmas can be parameterized, our first lemma is parametric in an arbitrary proposition ``P``. We denote this by writing ``(P : Prop)``.

|*)

Lemma P_imp_P (P : Prop) : P -> P.
Proof.
  (*| If you interpret this script live, you will see the so-called goal: ``P -> P``. Verbally: ``P`` implies ``P``. *)
  (*| To prove it, we can assume we have a proof of ``P``, we call it ``h``. |*)
  intro h.
  (*| The command ``intro`` is called a *tactic*. |*)
(*|
The goal is now ``P``, but notice we have some extra assumption
``h : P``.
To use an assumption, one can use the ``apply`` tactic:
|*)
  apply h.
  (*| Proof finished! All that's left to do is to type ``Qed``. |*)
Qed.

(*|
Try to see what happens if one types ``Qed`` before the proof is finished.
|*)

(*|
We now have a new fact that can be used in other proofs:
``P_imp_P`` which is a proof of ``P -> P``.

You can check this fact using the ``Check`` command.
|*)
Check P_imp_P.

(*| We can also write conjunction (``/\``) and disjunction (``\/``) |*)

Lemma and_comm (P Q : Prop) : P /\ Q -> Q /\ P.
Proof.
  (*| We have an implication so we use ``intro``. |*)
  intro h.
  (*|
We now have ``h : P /\ Q`` as assumption and we need to prove ``Q /\ P``.

First we need to have a look at ``P /\ Q``, we would like to turn it into
two different hyoptheses: one for ``P`` and one for ``Q``.
If you have taken a course in logic, you would have said that we need to apply the elimination rule for conjunctions.
We can use elimination rules in general using the ``destruct`` tactic to decompose an hypothesis into all
possible proofs of it. In the case of ``P /\ Q``, there is just one:
|*)
  destruct h as [hP hQ].
(*| The ``as`` clause above is used to give a name to the resulting
hypotheses. Here we name ``hP : P`` and ``hQ : Q``.
|*)
  (*|
To prove a conjunction we can use the ``split`` tactic to get two goals:
|*)
  split.
(*|
In logical terms, this corresponds to applying the introduction rule for conjuctions.

Notice we now have two goals, ``P`` and ``Q``.
We use bullets to focus on the goals one by one.
|*)
  - (*| Now proving ``Q`` is easy. |*)
    apply hQ.
  - apply hP.
Qed.

(*| Let us look at a slightly different example: disjunction. |*)

Lemma or_comm (P Q : Prop) : P \/ Q -> Q \/ P.
Proof.
  intro h.
  (*|
Now we first need to do a case analysis on whether ``P`` or ``Q`` holds.
This is done using the ``destruct`` tactic again, doing a case analysis
on all possible proofs of ``P \/ Q``. There are two:
|*)
  destruct h as [hP | hQ].
  (*| Notice how we used a pipe to separate the two cases. |*)
  -
    (*|
Now we have ``P`` and we want to prove ``Q \/ P``.
We can use the tactic ``right`` to say we want to prove the right case.
|*)
    right.
    apply hP.
  - (*| Unsurprisingly, the dual tactic is called ``left``. |*)
    left.
    apply hQ.
Qed.

(*|
We also have the usual ⊤ and ⊥ which in Rocq are called ``True`` and
``False``.
|*)

Lemma truetrue : True.
Proof.
  (*|
To prove it, you can also use ``split``!
It's like the nullary conjunction.
``split`` will work with all logical constructions that only have one introduction rule.
|*)
  split.
Qed.

Lemma falsefalse : False.
Proof.
(*|
Of course, one cannot prove ``False`` without assumptions.
So we give up:
|*)
Abort.

(*| Rocq will now not add ``falsefalse`` to the environment, and thus the ``Check`` command will fail: |*)
Fail Check falsefalse.

(*|
However, ``False`` implies anything: *ex falso quodlibet*.
|*)

Lemma anything_goes P : False -> P.
Proof.
  intro bot.
  (*|
The ``exfalso`` tactic concludes anything as long as you can prove
``False``.
|*)
  exfalso.
  apply bot.
Qed.

(*| Let's do the proof again, with an alternative approach. |*)
Lemma anything_goes_again P : False -> P.
Proof.
  (*|
Namely, we can do case analysis on all possible proofs of ``False``
directly — of which there are none.
|*)
  intro bot.
  destruct bot.
Qed.

(*|
Let us have a look at negation now.
``~ P`` is a notation for the negation of ``P``.
In fact it is defined as ``P -> False``, so we can use intro to prove a
negation.
|*)

Lemma nofalse : ~ False.
Proof.
  intro contra. apply contra.
Qed.

(*|
^^^^^^^^^^^^^^^^^^^^^^^^^^^
Case analysis and induction
^^^^^^^^^^^^^^^^^^^^^^^^^^^

Let us consider the type of Booleans, with elements ``true`` and ``false``.
We also refer to the ``negb`` function from the standard library which sends
``true`` to ``false`` and vice versa.
|*)
Lemma negb_true :
  negb true = false.
Proof.
  (*| Here we have computation, so we can ask Rocq to simplify things. |*)
  simpl.
  (*| Equality is then proven with the following tactic which solves goals
of the form ``x = x``.
  |*)
  reflexivity.
Qed.

(*| We show that boolean negation is involutive. |*)

Lemma negb_invol (b : bool) :
  negb (negb b) = b.
Proof.
  (*|
Similar to how ``destruct`` can be used to do case analysis on hypotheses,
it can be used to do case analysis on booleans. There are two cases:
|*)
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(*| We now turn to boolean conjunction. |*)

Lemma andb_comm b1 b2 :
  andb b1 b2 = andb b2 b1.
Proof.
  destruct b1.
  - simpl. destruct b2.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - simpl. destruct b2.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Lemma andb_comm' b1 b2 :
  andb b1 b2 = andb b2 b1.
Proof.
  (*| We can also ask Rocq to do two case analyses at the same time. |*)
  destruct b1, b2.
  -
    (*|
No need to use ``simpl`` every time, ``reflexivity`` does it on its own.
|*)
    reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(*| Let us switch to natural numbers. |*)

Lemma calc_12_3 : 12 + 3 = 15.
Proof.
  (*| Here we have computation again, so we can ask Rocq to simplify things. |*)
  simpl.
  (*|
Now we have to prove ``15 = 15``, the is true by reflexivity of equality.
|*)
  reflexivity.
Qed.

Lemma double_eq n : n + n = 2 * n.
Proof.
  (*| Functions in Rocq have computation rules. |*)
  simpl.
  (*|
The ``+ 0`` at the end might seem surprising.
This has to do with the definition of multiplication:

    0 * m := 0

    (n + 1) * m := m + n * m

So ``2 * m = m + 1 * m = m + (m + (0 * m)) = m + (m + 0)``.

Note that ``n + 0`` also does not simplify by computation, because the defining rules are:

    0 + m := m

    (n + 1) + m := (n + m) + 1

However, we can prove that ``n + 0 = n``. We do so with a lemma first.

|*)
Abort.

Lemma plus_zero n : n = n + 0.
Proof.
(*|
Case analysis is no longer sufficient to prove such a result, instead we're
going to perform induction on natural numbers. We do so with the following
tactic.
|*)
  induction n.
  (*|
We have two cases to prove, the case ``n = 0`` and the case ``n + 1``.
In Rocq, the successor of ``n`` is written ``S n``, like in Peano
arithmetic.
|*)
  - (*| Now, ``0 + 0`` computes to ``0``: *)
    simpl. reflexivity.
  - simpl.
    (*| We have ``S`` on both sides. We can use the ``f_equal`` tactic to prove that ``f x = f y`` if ``x = y``. |*)
    f_equal.
    (*|
Here we can apply our induction hypothesis.
Since we did not chose its name, we can use a different tactic
that finds a matching hypothesis on its own:
|*)
    assumption.
Qed.

(*|
The lemma we wanted to prove earlier is now easy, we just have to make use of
``plus_zero`` we just proved.
|*)

Lemma double_eq n : n + n = 2 * n.
Proof.
  simpl. f_equal. apply plus_zero.
Qed.

(*|
^^^^^^^^^^^^^^^^^^
Defining functions
^^^^^^^^^^^^^^^^^^

One last thing: in Rocq you can also write your own definitions and they can
be recursive. In models a recursive function corresponds to a fixed point so
such functions are introduced with the keyword ``Fixpoint``. It corresponds
roughly to OCaml's ``let rec`` syntax, but compared to OCaml, functions must
be total (defined on all inputs) so in particular, they must be terminating.

Here, we define a function ``double`` which doubles its argument by dupplicating
all occurrences of ``S`` in it. For instance, ``double (S (S 0))`` will compute
to ``S (S (double (S 0)))`` and then to ``S (S (S (S (double 0))))`` which is
``S (S (S (S 0)))``. In other words ``double 2 = 4``.
|*)

Fixpoint double (n : nat) :=
  match n with
  | 0 => 0
  | S n => S (S (double n))
  end.

(*|
Note that the definition contains the ``match`` construct which performs
pattern matching, or case analysis. If you know OCaml then it is the same syntax
with the exception that a ``match`` block has to end with the keyword ``end``.
This makes it easier to parse for both humans and machines, in particular when
several ``match`` are nested.

We can now prove by a simple induction that ``double n`` is the same as
``n * 2``.
|*)

Lemma double_eq2 n : double n = n * 2.
Proof.
  induction n as [ | m IHm].
(*|
This time we decided to give names to the extra hypotheses produced by the
``induction`` tactic. As with ``destruct`` before, there is a pipe (`|`)
separating the two cases (``0`` and ``S m``).
In the first case, there is no induction hypothesis so we do not need to
introduce any name.
In the successor case, we need to provide a name for the induction hypothesis
``IHm`` but also for the natural number that appears below ``S``, here we chose
``m``.
|*)
  - simpl. reflexivity.
  - simpl. rewrite IHm. reflexivity.
Qed.

(*|
This concludes our first lesson.
Try to do the exercises and ask for help if needed.

`Go back to the course homepage.`_
|*)
