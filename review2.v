(*|
============================
MPRI PRFA — Proof Assistants
============================

`🏠 Go back to the course homepage. <..>`__

-------------------
Reviewing session 2
-------------------

^^^^^^^^^^^^^^^^^^^^^^
Think before you prove
^^^^^^^^^^^^^^^^^^^^^^

We all jump right in the proof and it can be quite fun, but sometimes just
thinking a little will save some trouble.

Let us look at the ``add_sub`` example from the exercise session.
It might be tempting to prove things by induction on ``n``, after all it's the
first variable we have in the context, but it's actually must better to perform
induction on ``m``.
|*)

Lemma add_sub :
  forall n m,
    (n + m) - m = n.
Proof.
  intros n m. induction m as [| m ih].
  - rewrite <- plus_n_O. destruct n. all: reflexivity.
  - rewrite <- plus_n_Sm. simpl. assumption.
Qed.

(*|
^^^^^^^^^
Shadowing
^^^^^^^^^

We have several ways to write the definition of subtraction, depending on
whether we reuse the name of the argument or not in the pattern matching.
If we reuse the name, the original name is then *shadowed* which is fine as long
as we don't want to mention it again. Sometimes, it is useful to mention it.
|*)

Fixpoint sub_1 (n m : nat) :=
  match n, m with
  | 0, m => m
  | S n, 0 => S n
  | S n, S m => sub_1 n m
  end.

Fixpoint sub_2 (n m : nat) :=
  match n, m with
  | 0, _ => m
  | S _, 0 => n
  | S n, S m => sub_2 n m
  end.

(*|
^^^^^^^^^^^^^^^^^^^^^^
Discriminating by hand
^^^^^^^^^^^^^^^^^^^^^^

We write instructions in the document in the form of comments, please follow
them! This includes writing the induction principle, or not using certain
tactics or libraries, so that you can learn. 🧑‍🎓
When we told you to prove true ≠ false, we were expecting the following.
|*)

Lemma true_neq_false : true <> false.
Proof.
  intros e.
  change (if true then False else True).
  rewrite e. split.
Qed.

(*|
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Using custom induction principles
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

When you prove an induction principle, you can use it directly with the
induction tactic. Much nicer than applying it by hand.
|*)

Lemma strong_nat_ind :
  forall (P : nat -> Prop),
    (forall n, (forall m, m < n -> P m) -> P n) ->
    forall n, P n.
Admitted.

From Stdlib Require Import Lia.

Fixpoint even3 (n : nat) : Prop :=
  match n with
  | 0 => True
  | 1 => False
  | S (S n) => even3 n
  end.

Inductive even4 : nat -> Prop :=
| evenO : even4 0
| evenS n : even4 n -> even4 (S (S n)).

Lemma even3_to_even4 : forall n, even3 n -> even4 n.
Proof.
  intros n h.
  induction n as [n ih] using strong_nat_ind.
  destruct n as [| [| n]].
  - constructor.
  - simpl in h. contradiction.
  - constructor. apply ih.
    + lia.
    + assumption.
Qed.

(*|
--------------------
SELF-EVALUATION TIME
--------------------

Finally, we would like you to try to do the following on paper, that is
without using Rocq on your computer to tell you the answer!
|*)

(*|
^^^^^^^^
EXERCISE
^^^^^^^^

Write down the induction principle for ``list``.
   Definition ind_list {A : Type} (P : list A -> Prop) :=
   (P []) ->
   (forall a l, P l -> P (a :: l)) ->
   (forall l, P l)
|*)

About list_rec.

(*|
^^^^^^^^
EXERCISE
^^^^^^^^

What is the goal after the following script?
|*)

Goal forall P Q, P \/ Q -> Q \/ P.
Proof.
  intros P Q h.
  destruct h as [h | h].
  - left. (*| Q |*)
Abort.

(*|
^^^^^^^^
EXERCISE
^^^^^^^^

Prove 0 ≠ 1 without automation.
|*)

Goal 0 <> 1.
Proof.
  intro.
  change (match 0 with 0 => False | _ => True end).
  rewrite H.
  split.
Qed.
