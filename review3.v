(*|
============================
MPRI PRFA — Proof Assistants
============================

`🏠 Go back to the course homepage. <..>`__

-------------------
Reviewing session 3
-------------------

^^^^^^^^^^^^^^^^^^^^^^^^
Proving with proof terms
^^^^^^^^^^^^^^^^^^^^^^^^

If you find it hard, it's perfectly normal!
It takes some time to get used to it, but it is worth it.
Now when programming you can use proof-theoretic intuition, and when proving
you can use programmer's intuition, this is a very powerful tool!

Let us look again at ``Russel`` for the exercises.
We'll do it step by step.
|*)

Definition Russel X : ~ (X <-> ~ X).
Proof.
(*| We want to prove a negation, that's just a function to ``False`` |*)
  refine (fun h => _).
(*| Now we have ``X <-> ~ X`` which is a conjunction, so we ``match`` on it. |*)
  refine (match h with conj f g => _ end).
(*|
What can we do now? To prove ``False``, there is not much else we can do
besides applying ``f`` since ``f _`` is of type ``~ X`` which is ``X -> False``.
In other words ``f _ _`` is of type ``False``.
What does ``f`` expect as two arguments?
In both cases ``X``, so we might as well just prove it once with a ``let``.
|*)
  refine (let x := _ in f x x).
(*| Again, we don't really have a choice but to apply ``g``. |*)
  refine (g _).
(*| We know the drill. |*)
  refine (fun x => _).
(*|
It might seem like we're back where we started, but not really…
We have ``x : X`` now!
|*)
  refine (f x x).
Abort.

(*| If we combine all of that, we get |*)
Definition Russel X : ~ (X <-> ~ X) :=
  fun h =>
    let 'conj f g := h in
    let x : X := g (fun x => f x x) in
    f x x.

(*|
**Remark.**
The ``X`` in the definition above is on the left of the colon ``:`` so it needs
not be introduced (with ``fun X => _``) in the body of the definition.
|*)

(*|
^^^^^^^^^^^^^^^^^^
Implicit arguments
^^^^^^^^^^^^^^^^^^

When writing proof terms, implicit arguments become all the more important.
Let's look at one of the very first exercises.
|*)

Inductive lt (n : nat) : nat -> Prop :=
| lt_B : lt n (S n)
| lt_S m : lt n m -> lt n (S m).

Definition lt_plus_4 n m : lt n m -> lt n (4 + m) :=
  fun h => lt_S _ _ (lt_S _ _ (lt_S _ _ (lt_S _ _ h))).

(*| Now we make ``lt_S`` easier to use by making ``n, m`` implicit |*)
Arguments lt_S {n m}.

Definition lt_plus_4' n m : lt n m -> lt n (4 + m) :=
  fun h => lt_S (lt_S (lt_S (lt_S h))).

(*|
^^^^^^^^^^^^^^^^^^^^^^^
Impredicative encodings
^^^^^^^^^^^^^^^^^^^^^^^

Before there were inductive types, logical connectives were defined using
so-called impredicative encodings.

Note: Even datatypes were defined this way, in the advanced exercises, this
was the case of the Church encoding of natural numbers.

Impredicative encodings essentially define a type as their eliminator.
In other words, think about how you use it.

For ``False``, elimination states that you can prove any other proposition from
it, hence the following definition:
|*)

Definition iFalse :=
  forall (P : Prop), P.

(*| Notice the similarity with ``False_ind``. |*)

Check False_ind.

(*| For conjunction, it's the same idea. |*)

Definition iAnd (A B : Prop) :=
  forall (P : Prop), (A -> B -> P) -> P.

Check and_ind.

(*| Now ``apply`` plays the role of ``destruct`` for such a proof. |*)

Lemma iAnd_and :
  forall A B,
    iAnd A B ->
    A /\ B.
Proof.
  intros A B h.
(*| With ``A /\ B`` the following would be ``destruct h as [hA hB]``. |*)
  apply h. intros hA hB.
  split. all: assumption.
Qed.

(*| Now for ``exists x, P x``. |*)

Check ex_ind.

Definition iEx A (P : A -> Prop) :=
  forall (Q : Prop),
    (forall x, P x -> Q) ->
    Q.

Lemma iEx_ex :
  forall A P,
    iEx A P ->
    exists x, P x.
Proof.
  intros A P h.
  apply h. intros x hx.
  exists x. assumption.
Qed.

(*|
--------------------
SELF-EVALUATION TIME
--------------------

We'll do again some paper proving.
|*)

Inductive even : nat -> Prop :=
| evenO : even 0
| evenS n : even n -> even (S (S n)).

(*|
^^^^^^^^
EXERCISE
^^^^^^^^

Write down the induction principle for ``even``.
|*)

Definition even_indp (P : nat -> Prop) := 
  (P 0) ->
  (forall n, even n -> P n -> P (S (S n))) ->
  (forall n, even n -> P n).

Definition even_indp' (P : forall n, even n -> Prop) := 
   (P 0 evenO) ->
   (forall n en, P n en -> P (S (S n)) (evenS n en)) ->
   (forall n en, P n en).

(*|
^^^^^^^^
REMINDER
^^^^^^^^

  Inductive or (A B : Prop) : Prop :=
  | or_introl : A -> A \/ B
  | or_intror : B -> A \/ B.

  Notation ``"A \/ B" := (or A B)``.
|*)

(*|
^^^^^^^^
EXERCISE
^^^^^^^^

What is a proof term of the following type?
|*)

Definition or_imp :
  forall (P Q R : Prop), (P -> R) -> (Q -> R) -> P \/ Q -> R :=
  fun P Q R pr qr pq => match pq with
                        | or_introl p => pr p
                        | or_intror q => qr q
                        end.

(*|
^^^^^^^^
EXERCISE
^^^^^^^^

What is the goal after the following script?
|*)

Lemma true_false :
  true <> false.
Proof.
  intro e.
  change (if true then False else True).
  rewrite e.
  (*| if false then False else True |*)
  (*| pourquoi True ? Il y a forcément un calcul ici |*)
Abort.

(*|
^^^^^^^^
EXERCISE
^^^^^^^^

  Inductive le (n : nat) : nat -> Prop :=
  | le_n : n <= n
  | le_S : forall m, n <= m -> n <= S m.
|*)

Definition le_indp :=
  forall P : nat -> nat -> Prop,
  (forall n, P n n) ->
  (forall n m, le n m -> P n m -> P n (S m)) ->
  (forall n m, le n m -> P n m).

Definition le_indp' (P : forall n m, le n m -> Prop) :=
  (forall n lenn, P n n lenn) ->
  (forall n m lenm, P n m lenm -> P n (S m) (le_S n m lenm)) ->
  (forall n m lenm, P n m lenm).

(*|
^^^^^^^^
EXERCISE
^^^^^^^^

What is the goal after the following script?
|*)

Lemma le_n_S :
  forall n m,
    n <= m ->
    S n <= S m.
Proof.
  intros n m h.
  induction h.
  - constructor.
  - (*| h : n <= m
        IH : S n <= S m
        ---
        S n <= S (S m)
    |*)
Abort.
