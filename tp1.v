(** Exercise session 1

  Try and solve the following exercises by using the tactics shown in class:
    intro, apply, destruct, split, left, right, exfalso, simpl, reflexivity,
    f_equal, induction, assumption.

  Lemmas currently end with the keyword Admitted which means the lemma is
  accepted and can be used without a proof.
  Replace Admitted with Qed once you have completed the proofs.

  There are more exercises than what can be done in the exercise session during
  the lecture.
  Proving is like programming: You will have to practice at home.
  It is fine not to do all the exercises, but you should feel like you *could*
  do the exercises. We will help you with this assessment at the start of every
  lecture.

  Please send us this file with your (partial) solutions by email before the
  next lecture:
  yannick.forster@inria.fr, theo.winterhalter@inria.fr

  We will begin with the exercises you have seen already.

 **)

Lemma P_imp_P (P : Prop) : P -> P.
Proof.
  intro h.
  exact h.
Qed.

Lemma and_comm (P Q : Prop) : P /\ Q -> Q /\ P.
Proof.
  intro h.
  destruct h as [h1 h2].
  split.
  - exact h2.
  - assumption. (*- exact h1*)
Qed.

Lemma or_comm (P Q : Prop) : P \/ Q -> Q \/ P.
Proof.
  intro h.
  destruct h as [h1 | h2].
  - right. assumption.
  - left. assumption.
Qed.

Lemma truetrue : True.
split.
Qed.

Lemma anything_goes (P : Prop) : False -> P.
Proof.
  intro f.
  exfalso.
  assumption.
Qed.

Lemma nofalse : ~ False.
Proof.
  intro f.
  assumption.
Qed.

(** Now some new exercises about propositional logic *)

Lemma imp_trans (P Q R : Prop) : (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros f g x.
  apply g.
  apply f.
  exact x.
Qed.

Lemma to_not_not (P : Prop) : P -> ~~ P.
Proof.
  intro p.
  intro np.
  apply np.
  exact p.
Qed.

(** For this one, note that if you already separated a case distinction
      with dashes (-) then you can use + at the next level.
      The following level is marked with *.
 **)

Lemma distr (P Q R : Prop) : (P \/ Q) /\ R -> (P /\ R) \/ (Q /\ R).
Proof.
  intro poqer.
  destruct poqer as [pq r].
  destruct pq as [p | q].
  - left. split.
    + assumption.
    + assumption.
  - right. split. assumption. assumption.
Qed.

Lemma contrad (P : Prop) : P /\ ~ P -> False.
Proof.
  intro pnp.
  destruct pnp as [p np].
  apply np.
  exact p.
Qed.

Lemma lem_pl (P Q : Prop) : P \/ ~ P -> ((P -> Q) -> P) -> P.
Proof.
  intros pnp f.
  destruct pnp as [p | np].
  - exact p.
  - apply f. intro p. cut False.
    + intro f'. exfalso. apply np. assumption.
    + apply np. assumption.
Qed.

Lemma lem_dns (P : Prop) : P \/ ~ P -> ~~ P -> P.
Proof.
  intros [p | np] nnp.
  - exact p.
  - cut False.
    + intro f. exfalso. exact f.
    + apply nnp. assumption.
Qed.


(** To introduce several variables at once, you can use the intros tactic *)

Lemma dn_functorial P Q : (P -> Q) -> ~~ P -> ~~ Q.
Proof.
  intros hPQ hnnP.
  intro nq.
  apply hnnP.
  intro p.
  apply nq.
  apply hPQ.
  assumption.
Qed.

(** Let us switch to booleans again *)

Lemma andb_orb_distr (b1 b2 b3 : bool) :
  andb b1 (orb b2 b3) = orb (andb b1 b2) (andb b1 b3).
Proof.
  induction b1.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma de_morgan (b1 b2 : bool) :
  negb (andb b1 b2) = orb (negb b1) (negb b2).
Proof.
  induction b1.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(** Let us switch to natural numbers. *)

Lemma calc_12_3 : 12 + 3 = 15.
Proof.
  simpl. reflexivity.
Qed.

(** Let us make a lemma out of the n + 0 = n property.

    You can then apply this lemma by using [apply n_plus_0] like for hyoptheses!
 **)
Lemma n_plus_0 (n : nat) : n + 0 = n.
Proof.
  induction n as [ | m IH].
  - reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Lemma double_eq (n : nat) : n + n = 2 * n.
Proof.
  induction n as [ | n' IH].
  - simpl. reflexivity.
  - simpl. f_equal. f_equal. f_equal. apply eq_sym. apply n_plus_0.
Qed.

Lemma plus_S (n m : nat) : n + S m = S n + m.
Proof.
  induction n as [ | n IH].
  - simpl. reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Lemma plus_comm (n m : nat) : n + m = m + n.
Proof.
  induction n.
  - simpl.
    About n_plus_0.
    rewrite n_plus_0.
    reflexivity.
 - apply eq_sym. simpl. rewrite plus_S. simpl. f_equal. apply eq_sym. apply IHn.
Qed.

(** Show associativity of additon **)

Lemma plus_assoc (k n m : nat) : k + n + m = k + (n + m).
Proof.
  induction k as [ | k IH].
  - simpl. reflexivity.
  - simpl. f_equal. apply IH.
Qed.

(** TODO : We can also show commutativity of multiplication.

    Try to come up with the lemmas yourself.

    Note that you can also use rewrite in the opposite direction by using
    rewrite <- n_plus_0
    for instance.
    You can also use rewrite with hypotheses you have.

    If you ever find yourself with x = y to prove, when you think you can
    prove y = x, you can also use the symmetry tactic.
 **)

(** Fill in the cases for the following function.

  We use a placeholder REPLACE_ME that you need to replace.

 **)
Definition REPLACE_ME := 123.

Fixpoint min (n m : nat) :=
  match n, m with
  | 0, _ => 0
  | _, 0 => 0
  | S n, S m => S (min n m)
  end.

Lemma min_comm : forall n m, min n m = min m n.
Proof.
  intro n.
  (* Hint: start the induction before introducing m *)
  induction n.
  - simpl. intro m. induction m.
    + reflexivity.
    + simpl. reflexivity.
  - intro m. induction m.
    + simpl. reflexivity.
    + simpl. f_equal. apply IHn.
Qed.

(** ADVANCED EXERCISES

  If you have already used Coq before or you are done with the exercises,
  give the advanced exercises a try.
  They hopefully teach you thinks you have not seen before.

 **)

Section Advanced.

  Context (P Q R : Prop).

  (** We introduce a new notation P <-> Q meaning P is equivalent to Q.

      It is essentially a notation for P -> Q /\ Q -> P so you can use the
      tactics split and destruct to prove it and use it.

      Here is a trivial example to understand it.
   **)

  Lemma P_iff_P : P <-> P.
  Proof.
    split.
    - intro. assumption.
    - intro. assumption.
  Qed.

  (** And here is a new tactic that is going to be useful: assert

    When you write assert (h : P) you are telling Coq that you want to prove P
    and that then you are going to use this as an hypothesis named h.
    This is sometimes called forward reasoning.

    See how it works below.
   **)

  Lemma or_imp : (Q -> P) /\ (R -> P) -> Q \/ R  -> ~~ P.
  Proof.
    intros h1 h2.
    assert (hP : P).
    { destruct h1 as [hQP hRP].
      destruct h2 as [hQ | hR].
      - apply hQP. apply hQ.
      - apply hRP. apply hR.
    }
    apply to_not_not. apply hP.
  Qed.

  Lemma Russel : ~ (P <-> ~ P).
  Proof.
    intro pnp.
    destruct pnp as [pinp npip].
    assert (p:P). {
      apply npip.
      intro hP.
      exact ((pinp hP) hP).
    }
    exact ((pinp p) p).
  Qed.

End Advanced.

(** For even more advanced stuff we are going to use quantifiers
    on propositions too. Its basically the same as with natural numbers.

    If you have some hypothesis of the form
    h : forall x, P x
    then know that you can use
    specialize (h y) to obtain h : P y.
    See the following example.
 **)

Lemma forall_False : (forall (P : Prop), P) -> False.
Proof.
  intro h.
  specialize (h False).
  assumption.
Qed.

(** Note that it would work with apply directly in this case. **)

Lemma forall_False' : (forall (P : Prop), P) -> False.
Proof.
  intro h.
  apply h.
Qed.

(** Prove the converse now **)

Lemma False_forall : False -> (forall (P : Prop), P).
Proof.
  intro f.
  intro p.
  exfalso.
  exact f.
Qed.

(**

Rocq is, at its basis, as system that has nothing but elimination and introduction rules for disjunctions:
   P        Q       P \/ Q  P -> R  Q -> R
-------  -------   ------------------------
P \/ Q    P \/ Q              R

In particular, these rules do not allow proving

P \/  ~P

In other words, Rocq implements intuitionistic logic. This allows

- assuming classical laws of reasoning like the law of excluded middle and doing classical math
- not assuming the law of excluded middle, thus being able to have interesting proofs of the form A -> LEM for a statement A. We will do prove A <-> LEM for two statements now:

**)

Definition theLEM := forall P:Prop, P \/ ~ P.
Definition theDNS := forall P:Prop, ~~ P -> P. (* double negation shift *)
Definition thePL := forall P Q:Prop, ((P -> Q) -> P) -> P. (* Peirce's law *)

(** We can now prove the other direction from before. **)

Lemma lem_dns_general : theLEM -> theDNS.
Proof.
  intro lem.
  intro p.
  intro nnp.
  specialize (lem p).
  destruct lem as [p' | np].
  - exact p'.
  - exfalso. apply nnp. exact np.
Qed.

Lemma lem_pl_general : theLEM -> thePL.
Proof.
  intro lem.
  intros P Q.
  intro f.
  destruct (lem P) as [p | np].
  - exact p.
  - apply f. intro p. exfalso. exact (np p).
Qed.

Lemma dns_lem : theDNS -> theLEM.
Proof.
  intro dns.
  intro P.
  apply (dns (P \/ not P)).
  intro npnnp.
  assert (h:(not P /\ (not (not P)))). {
    split.
    - intro p. apply npnnp. left. assumption. 
    - intro np. apply npnnp. right. assumption.
  }
  destruct h as [np nnp].
  exact (nnp np).
Qed.

Lemma pl_lem : thePL -> theLEM.
Proof.
  intro pl.
  intro P.
  assert (premise: (not (P \/ not P)) -> (P \/ not P)). {
    intro npnp. right. intro p. apply npnp. left. exact p.
}
  apply (pl (P \/ not P) False).
  exact premise.
Qed.

(** An example of commuting forall and \/ **)

Lemma forall_or :
  forall P Q,
    (Q \/ ~ Q) ->
    (forall (x : nat), P x \/ Q) ->
    (forall x, P x) \/ Q.
Proof.
  intros P Q lem.
  intro PxQ.
  destruct lem as [q | nq].
  - right. assumption.
  - left. intro x. specialize (PxQ x). destruct PxQ as [Px | q].
    + assumption.
    + exfalso. apply nq. exact q.
Qed.

(** More classical reasoning. **)

Lemma classical_or_contra_r :
  theLEM ->
  forall (P Q : Prop),
    (~ Q -> P) ->
    P \/ Q.
Proof.
  intros lem P Q nqip.
  specialize (lem Q) as [q | nq].
  - right. assumption.
  - left. apply nqip. exact nq.
Qed.

(* For the following do you need LEM for both directions? *)

Lemma classical_impl :
  theLEM ->
  forall (P Q : Prop),
    (P -> Q) <-> (~ P \/ Q).
Proof.
  intros lem P Q.
  split.
  - intro piq. specialize (lem P) as [p | np].
    + right. apply piq. exact p.
    + left. assumption.
  - intro npq. intro p. destruct npq as [np | q].
    + exfalso. apply np. exact p.
    + assumption.
Qed.

Lemma contrapositive :
  theLEM ->
  forall (P Q : Prop),
    (~ Q -> ~ P) ->
    P -> Q.
Proof.
  intros lem P Q nqnp.
  destruct (classical_impl lem P Q) as [_ disj].
  apply disj.
  destruct (classical_impl lem (not Q) (not P)) as [imp _].
  assert (dns_in_or : (not (not Q)) \/ (not P) -> (not P) \/ Q). {
    intro nnqnp.
    destruct nnqnp as [nnq | np].
    - right. exact (((lem_dns_general lem) Q) nnq).
    - left. assumption.
  }
  apply dns_in_or.
  apply imp.
  exact nqnp.
Qed.

(** Note: if you want to use specialize on a hyothesis twice, you
    can use specialize (h x) as hx to create a new hypothesis instead of
    replacing h.
 **)

Lemma twice :
  theLEM ->
  forall (P Q : Prop),
    ((P -> Q) -> Q) ->
    ((Q -> P) -> P).
Proof.
Admitted.

(** More natural numbers.

  Sometimes you will need to generalise a goal before calling the induction
  tactic. To that end you can use the revert tactic that works as the opposite
  of intro.

  For instance if you have goal

  n, m, k : nat
  -------------
  something

  then you can type

  revert m.

  and obtain goal

  n, k : nat
  -------------------
  forall m, something

 **)

Lemma mult_distr :
  forall n m k,
    k * (n + m) = k * n + k * m.
Proof.
Admitted.

(** If you thought this kind of proof is extremely annoying,
    rest assured, most would agree and in practice you don't have to do them by
    hand. We torture you so you understand better how things work.

    In practice Coq users will use the lia tactic to solve a lot of integer
    arithmetic problems.
 **)

From Stdlib Require Import Lia.

Lemma mult_distr_lia :
  forall n m k,
    k * (n + m) = k * n + k * m.
Proof.
  lia. (* See? Much better. :) *)
Qed.
