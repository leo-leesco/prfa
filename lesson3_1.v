(*|
============================
MPRI PRFA — Proof Assistants
============================

`🏠 Go back to the course homepage. <..>`__

------------------------------------
Proof terms and meta-theory — Part 1
------------------------------------

For this class we will look a bit more at the theory behind Agda, Lean and Rocq:
dependent type theory.
We will see how this underlying theory comes into play when proving theorems
and defining functions.
Knowing this isn't strictly necessary to use Lean or Rocq (for Agda this is
a different story), but it will certainly help, for instance to understand
error messages a bit more. And sometimes it makes proving easier.
It's also relevant if you want to work in the area of proof assistants later.
|*)

From Stdlib Require Import List.
Import ListNotations.

(*|
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Dependent functions and type universes
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

So what makes depentent type theory *dependent*?
In simple type theory, variants of which are used in OCaml for instance, types
can depend on other types, as exemplified by ``list A``.
Dependent types can additionally depend on terms. This allows types to include
computation or even be computations themselves.

See for instance the ``if`` in the type of the function below.
|*)
Definition dependent (b : bool) : if b then nat else bool :=
  match b with true => 0 | false => true end.

(*|
We already used such ``if`` statements when showcasing Σ types in the previous
lecture so it shouldn't be too surprising.

The thing which allows us to include computation in types is that terms and
types are not actually separated. In particular, types have a type, often
``Type``, and ``Type`` itself has a type!
This bring us to the notion of *universe*.

Essentially ``Type`` and ``Prop`` are universes. They contain respectively the
types and propositions (as the names suggest).
|*)

Check Type.

(*|
Above you see that ``Type`` itself has type ``Type``. It makes sense, after all
``Type`` is indeed a ``Type``. However, assuming ``Type : Type`` actually leads to
inconistencies (proofs of ``False``) so instead, we have a *hierarchy* of
universes: basically ``Type₀ : Type₁ : Type₂ …``

You can ask Rocq to show you universe levels by using the following command.
|*)

Set Printing Universes.
Check Type.
Unset Printing Universes.

(*|
This is not very easy to read but essentially it says that ``Typeᵢ`` lives
in ``Typeᵢ₊₁``.

The fact that the universe levels are not displayed and inferred by the
system is sometimes called *typical ambiguity*.

Even while hidden they still play an important role.
If for instance we alias ``Type`` under some name ``T``, we will run into an
issue with the following definition because it will pick a specific universe
level (the index ``i`` in ``Typeᵢ``).
|*)

Definition T := Type.
Fail Check (forall (X : T), X) : T.

(*|
**Note.** Here we used the ``Fail`` command which can be used in front of
commands that result in errors to turn them into successes.

Here you get what is called a "universe inconsistency" because you cannot
quantify over a universe and stay within it essentially.

Compare however with the following, seemingly equivalent, presentation.
|*)

Check (forall (X : Type), X) : Type.

(*|
This time it works because the ``Type`` on the right has a higher level that
the one on the left so that it is able to contain it.
You don't need to worry too much about universes at this point but know that
they exist to forbid inconsistencies and that sometimes you will get
universes inconsistencies that will require to look more closely at the
definitions.

We will also have examples about this later, so stay tuned. 😎

Back to ``Prop`` now.
|*)

Check Prop.

(*|
``Prop`` is of type ``Type`` and actually ``Prop`` doens't have any hidden universe
levels. It however has one interesting property which is that to create a
proposition you can quantify over *anything*. This includes ``Prop`` itself.
This propery is called *impredicativity* and is not present in Agda for
instance.
|*)

Check (forall (P : Prop), P) : Prop.

(*|
^^^^^^^^^^^
Proof terms
^^^^^^^^^^^

Let us consider again the ``even`` predicate from the previous lesson.
|*)

Inductive even : nat -> Prop :=
| evenO : even 0
| evenS : forall n, even n -> even (S (S n)).

(*|
As we showed you, ``constructor`` is actually applying the correct constructor
between ``evenO`` and ``evenS``. So when proving ``even 4`` we can actually be
explicit like below:
|*)

Lemma even_four : even 4.
Proof.
  apply evenS. apply evenS. apply evenO.
Qed.

(*| Now let us use ``Print`` to see what the proof is to Rocq. |*)

Print even_four.

(*|
You see two uses of ``evenS`` followed by ``evenO``.
We also see that the numbers ``2`` and ``0`` are there because they appear as
arguments to ``evenS`` but they're not really necessary so we can mark them as
implicit so they don't bother us.
|*)

Arguments evenS {n}.

(*| Now the proof of ``even 4`` we write directly as follows: |*)

Definition even_four' :=
  evenS (evenS evenO).

(*|
^^^^^^^^^^^^^^^^^^^
Forall, implication
^^^^^^^^^^^^^^^^^^^

For now you saw what to do with ``forall`` and ``->`` interactively, and it was
very similar: you use ``intro`` or ``intros`` to prove them, and ``apply`` to use
them.

When we prove something using tactics we can ask Rocq to show how it built it
with the command ``Show Proof``. Let's see on an example.
|*)

Goal forall P Q, P -> (P -> Q) -> Q.
Proof.
  intros P Q x f.
  apply f.
  apply x.
  Show Proof.
Qed.

(*|
We get what is called a proof term: it's a definition whose type is exactly
the proposition we wanted to prove.
We can use it directly to prove our lemma.
|*)

Goal forall P Q, P -> (P -> Q) -> Q.
Proof.
  apply (fun P Q x f => f x).
Qed.

(*|
Coming up a with a proof term by hand is hard, and Rocq can also help us write
it using the ``refine`` tactic which accepts a partial term with some
underscores (``_``) and then you can fill them interactively.
|*)

Goal forall P Q, P -> (P -> Q) -> Q.
Proof.
  refine (fun P Q x f => _). (*| Basically here we do ``intros P Q x f`` |*)
  refine (f _). (*| Now ``apply f`` |*)
  refine x. (*| Now ``apply x`` |*)
Qed.

(*|
The proof in essence hasn't changed. All it comes down to is the typing
rules of the theory. If you know the Curry-Howard correspondance for simple
type theory this shouldn't be surprising.
Let us recap the idea quickly.
Proving ``A → B`` is the same as defining a function from ``A`` to ``B``.
The introduction rule corresponds to λ-abstraction:

.. math::

  \fbox{Natural deduction}

  \frac{\Gamma, A \vdash B}{\Gamma \vdash A \to B}


  \fbox{Simple type theory}

  \frac{\Gamma, x: A \vdash t : B}{\Gamma \vdash \lambda (x : A).\ t : A \to B}


If you don't know λ-calculus, then think of ``λ x. t`` as a function taking an
argument ``x`` and returning ``t`` where ``t`` might mention ``x``.

The elimination rule for implication then corresponds to application:

.. math::

  \fbox{Natural deduction}

  \frac{\Gamma \vdash A \to B \qquad \Gamma \vdash A}{\Gamma \vdash B}

  \fbox{Simple type theory}

  \frac{\Gamma \vdash f : A \to B \qquad \Gamma \vdash u : A}{\Gamma \vdash f\ u : B}


We mentioned before that we have dependent types, that lets us write
things such as ``forall (x : A), B``.
This generalises the rules above to quantifiers:

.. math::

  \fbox{Dependent type theory}

  \frac{\Gamma, x : A \vdash t : B}{\Gamma \vdash \lambda (x : A).\ t : \forall (x : A).\ B}

  \frac{\Gamma \vdash f : \forall (x : A). B \qquad \Gamma \vdash u : A}{\Gamma \vdash f\ u : B[x := u]}


Notice how ``x`` may appear in ``B`` and thus needs to be replaced by ``u``,
which is what the :math:`B[x := u]` represents.
Let us see how it works in practice:
|*)

Goal forall (f : forall n, even n), even 1.
Proof.
  refine (fun f => f 1).
  (*| ``f 1`` has type ``even 1``, the ``n`` was substitued by ``1``. |*)
Qed.

(*| Let us see again proof terms in action and how it compares to tactics. |*)

Lemma even_plus_four :
  forall (n : nat) (H : even n), even (4 + n).
Proof.
  intros n H.
  apply evenS.
  apply evenS.
  apply H.
Qed.

Lemma even_plus_four_refine :
  forall (n : nat) (H : even n), even (4 + n).
Proof.
  refine (fun n H => evenS (evenS _)).
  refine H.
Qed.

(*| We can just do it in direct style. |*)

Definition even_plus_four_term :
  forall (n : nat), even n -> even (4 + n)
:= fun n H => evenS (evenS H).

(*|
^^^^^^^^^^^^^^^
And, or, exists
^^^^^^^^^^^^^^^
|*)

(*|
First, we'll have a look at the definitions of various logical connectives
and propositions we've used over the course of the lecture.

**Note.** We create a module so that the definitions are local and do not
replace the ones from the standard library, but you won't be needing to do that
yourself in this course.
|*)

Module Show_Definitions.

(*|
First, ``False`` can be seen as the empty type, so we define it as an inductive
type with absolutely no constructor.
We write this as below, with an odd syntax that really just lists all—meaning
0—the constructors.
|*)

  Inductive False := .

(*|
``True`` on the other hand is like the unit type: it has exactly one constructor
which happens to be called ``I``.
|*)

  Inductive True := I.

(*|
``~ P`` is a notation for ``not P`` which unfolds to ``P -> False``.
|*)

  Definition not (P : Prop) := P -> False.

  Notation "~ P" := (not P).

(*|
Conjunction ``A /\ B`` is a notation for ``and A B`` which is defined in a very
similar way to cartesian product ``A * B``, except that ``A`` and ``B``, as well
as ``A /\ B`` are propositions (they live in the ``Prop`` universe).

**Remark.** The universe annotations are in fact the *only* differences between
the two inductive types! Rocq is currently evolving so that the two are actually
unified.
|*)

  Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.

(*|
Disjunction ``P \/ Q`` is a notation for ``or P Q`` and has two constructors:
one saying ``P`` is enough to prove ``P \/ Q`` and one saying ``Q`` is enough.
|*)

  Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

End Show_Definitions.

(*|
You can also use the ``Print`` command to see the definitions above.
Note how you can use quotation marks around a notation to print it as well,
which can be quite handy when you don't know what it represents.
|*)
Print False.
Print True.
Print "~".
Print and.
Print "/\".
Print or.
Print "\/".

(*|
To eliminate a proof of ``False``, one can just match on it and provide the
exactly zero cases that are needed.
|*)
Definition elim_False : forall (Z : Prop), False -> Z :=
  fun Z a =>
    match a with end.

(*| The rest should be easier to understand. |*)

Definition elim_and :
  forall (X Y Z : Prop), X /\ Y -> (X -> Y -> Z) -> Z
:= fun X Y Z a e =>
    match a with
    | conj x y => e x y
    end.

Definition elim_or :
  forall (X Y Z : Prop), X \/ Y -> (X -> Z) -> (Y -> Z) -> Z
:= fun X Y Z a e1 e2 =>
    match a with
    | or_introl x => e1 x
    | or_intror y => e2 y
    end.
