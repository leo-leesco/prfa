(** * MPRI PRFA (2-7-2) — Session 8 — Dependent functional programming **)

From Coq Require Import Arith List Lia.
From Equations Require Import Equations.
Import ListNotations.

Set Default Goal Selector "!".

Axiom REPLACE_ME : forall {A}, A.

Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A 0
| vcons (a : A) (n : nat) (v : vec A n) : vec A (S n).

Arguments vnil {A}.
Arguments vcons {A} a {n}.

Inductive fin : nat -> Type :=
| fin0 n : fin (S n)
| finS n (x : fin n) : fin (S n).

Arguments fin0 {n}.
Arguments finS {n}.

Equations vnth {A n} (v : vec A n) (x : fin n) : A :=
  vnth (vcons a v) fin0 := a ;
  vnth (vcons a v) (finS x) := vnth v x.

(** EXERCISE

  Define the head and tail functions on vectors manually by filling the gaps
  in the following programs.
  You have to use the [return] clause and the [vnil] branch explicitly.

**)

Definition hd {A n} (v : vec A (S n)) : A :=
  match v in vec _ m return
    match m with
    | 0 => True
    | S m => A
    end
  with
  | vnil => I
  | vcons a v => a
  end.

Fixpoint tl {A n} (v : vec A (S n)) {struct v} : vec A n :=
  match v in vec _ m return
    match m with
    | 0 => True (* we want to prove something trivial for a never occurring case *)
    | S m => vec _ m
    end
  with
  | vnil => I
  | vcons _ v => v
  end.

Equations last {A n} (v : vec A (S n)) : A
  by wf n lt :=
  (* last vnil := I; *)
  last (vcons a vnil) := a;
  last (vcons _ v) := last v.

(** EXERCISE

  Do the same thing for the [zip] function.
  Hint: Your [match] on the first vector will need to return a function that
  expects the other vector as argument.

  You may also use [hd] and [tl] on the second vector.

**)

Fixpoint zip {A B n} (v : vec A n) (w : vec B n) : vec (A * B) n :=
  match v in vec _ n return
    vec B n -> vec (A * B) n
  with
  | vnil => vnil
  | vcons a v => _
  end.

(** EXERCISE

  We will now start using Equations.

  Define [repeat] such that [repeat a n] is a vector of length [n] with all
  elements equal to [a].

  Give and prove its functional elimination principle.
  Then use it to prove the associated lemma.
  You can compare with the proof using [funelim].

**)

Equations repeat {A} (a : A) (n : nat) : vec A n :=
  repeat a n := REPLACE_ME.

Lemma repeat_ind :
  REPLACE_ME.
Proof.
Admitted.

Lemma vnth_repeat :
  forall A (a : A) n m,
    vnth (repeat a n) m = a.
Proof.
Admitted.

(** EXERCISE

  Same thing with a map function for vectors. Define it on vectors and prove
  that [vnth (vmap f v) n] is equal to something not mentioning [vmap].

  State and prove the functional elimination principle for [vmap].

**)

Fail REPLACE_ME.

(** EXERCISE

  Can you fix the definition of [rev_acc] below that is supposed to reverse a
  vector by using an accumulator?

  It should work when removing the [Fail].

  Hint: You can use underscores [_] to tell Equations to try and solve a missing
  goal automatically, if doesn't solve it it will produce an obligation to solve
  interactively.
  This works a bit like [refine].

**)

Definition transport {A} {P : A -> Type} {u v} (e : u = v) : P u -> P v :=
  match e with
  | eq_refl => fun x => x
  end.

Fail Equations rev_acc {A n m} (v : vec A n) (acc : vec A m) : vec A (n + m) :=
  rev_acc vnil acc := acc ;
  rev_acc (vcons a v) acc := rev_acc v (vcons a acc).

(** EXERCISE

  To practice dependent elimination a bit more, we give you a new definition of
  terms of the simply typed λ-calculus, but this time with a dichotomy between
  normal terms that are values and those that are "stuck".

  Show that a normal term of type [tunit ~> tunit] in the empty environment is
  necessarily a λ, meaning some [nlam].

  Hint: It might be useful to first show that there is no stuck term in the
  empty environment.

**)

Inductive type := tunit | tarrow (a b : type).

Notation "A ~> B" := (tarrow A B) (at level 20, right associativity).

Definition env := vec type.

Inductive normal {n} (E : env n) : type -> Type :=
| nstar : normal E tunit
| nlam (A : type) B (b : normal (vcons A E) B) : normal E (A ~> B)
| nstuck A (s : stuck E A) :> normal E A

with stuck {n} (E : env n) : type -> Type :=
| svar (x : fin n) : stuck E (vnth E x)
| sapp A B (f : stuck E (A ~> B)) (u : normal E A) : stuck E B.

Arguments svar {n E}.
Arguments nstar {n E}.
Arguments nlam {n E} A {B}.
Arguments sapp {n E A B}.
Arguments nstuck {n E A}.

Derive NoConfusion for type.

Lemma lam_inv :
  REPLACE_ME.
Proof.
Admitted.

(** EXERCISE

  We could also define vectors by using subset types, as we show below.
  Define the head and tail functions again for [ilist].

**)

Definition ilist (A : Type) (n : nat) :=
  { l : list A | length l = n }.

(** Some notation so that it's nicer **)
Notation "⟨ u | v ⟩" := (exist _ u v) (at level 0).
Notation "⟨ u ⟩" := (⟨ u | _ ⟩) (at level 0, only parsing).

Fail REPLACE_ME.

(** EXERCISE Convoy pattern

  Sometimes it is useful to remember an expression that we "destruct".
  For instance, if we have the following goal.
  Can you do the same using only [match]?

**)

Fixpoint eq_nat (n m : nat) : bool :=
  match n, m with
  | 0, 0 => true
  | S n, S m => eq_nat n m
  | _, _ => false
  end.

Lemma eq_nat_eq {n m} :
  eq_nat n m = true -> n = m.
Proof.
Admitted.

Lemma neq_nat_neq {n m} :
  eq_nat n m = false -> n <> m.
Proof.
Admitted.

Lemma eq_dec :
  forall (n m : nat), { n = m } + { n <> m }.
Proof.
  intros n m.
  destruct (eq_nat n m) eqn: e.
  - left. apply eq_nat_eq. assumption.
  - right. apply neq_nat_neq. assumption.
Qed.

Definition eq_dec_term (n m : nat) : { n = m } + { n <> m } :=
  REPLACE_ME.

(** * ADVANCED EXERCISES **)

(** EXERCISE

  Show that [ilist A n] and [vec A n] are equivalent.

  You may use the [K] axiom to prove lemma [ilist_eq] but it is not strictly
  necessary.

**)

Axiom K : forall A (u : A) (e : u = u), e = eq_refl.

Lemma ilist_eq :
  forall A n (l l' : ilist A n),
    proj1_sig l = proj1_sig l' ->
    l = l'.
Proof.
Admitted.

Record equiv (A B : Type) := {
  l_to_r : A -> B ;
  r_to_l : B -> A ;
  l_to_l : forall a, r_to_l (l_to_r a) = a ;
  r_to_r : forall b, l_to_r (r_to_l b) = b
}.

Lemma transportK :
  forall A (u : A) (e : u = u) (P : A -> Type) (t : P u),
    transport e t = t.
Proof.
Admitted.

Lemma transport_vcons :
  forall A n m e e' a (v : vec A n),
    transport e (vcons a v) = vcons a (n := m) (transport e' v).
Proof.
Admitted.

Lemma equiv_ilist :
  forall A n,
    equiv (vec A n) (ilist A n).
Proof.
Admitted.

(** EXERCISE

  Back to λ-calculus. This time we're going to see how we can go from the [term]
  representation of the live coding to the [normal] we showed above.
  This method is called Normalisation by Evaluation (NbE).

  We give you some stuff about renaming, which are remappings of variables.

**)

Set Equations Transparent.

Inductive term {n} (E : env n) : type -> Type :=
| tvar (x : fin n) : term E (vnth E x)
| tstar : term E tunit
| tlam (A : type) B (b : term (vcons A E) B) : term E (A ~> B)
| tapp A B (f : term E (A ~> B)) (u : term E A) : term E B.

Arguments tvar {n E}.
Arguments tstar {n E}.
Arguments tlam {n E} A {B}.
Arguments tapp {n E A B}.

(** Renaming **)
Definition ren {n m} (E : env n) (F : env m) :=
  { f : fin n -> fin m | forall x, vnth E x = vnth F (f x) }.

Equations? xren {n m E F} A (r : @ren n m E F) : ren (vcons A E) (vcons A F) :=
  xren A ⟨ r ⟩ := ⟨ fun x => _ ⟩.
Proof.
  - dependent elimination x.
    + apply fin0.
    + apply finS, r, x.
  - dependent elimination x.
    + cbn. simp vnth. reflexivity.
    + cbn. simp vnth.
Defined.

Equations idren {n E} : ren (n := n) E E :=
  idren := ⟨ fun x => x ⟩.

Equations? rencomp {n m k E F G} (r : @ren n m E F) (r' : ren (m := k) F G) : ren E G :=
  rencomp ⟨ r | h ⟩ ⟨ r' | h' ⟩ := ⟨ fun x => r' (r x) ⟩.
Proof.
  rewrite h, h'. reflexivity.
Defined.

Equations weak {n E A} : ren (n := n) E (vcons A E) :=
  weak := ⟨ fun x => finS x ⟩.

Equations nren {A n m E F} (r : @ren n m E F) (s : normal E A) : normal F A by struct s := {
  nren r nstar := nstar ;
  nren r (nlam A b) := nlam A (nren (xren _ r) b) ;
  nren r (nstuck s) := sren r s
}
where sren {A n m E F} (r : @ren n m E F) (s : stuck E A) : stuck F A by struct s := {
  sren ⟨ r | h ⟩ (svar x) := transport _ (svar (r x)) ;
  sren r (sapp f u) := sapp (sren r f) (nren r u)
}.

Equations sem {n} (E : env n) (A : type) : Type :=
  sem E tunit := normal E tunit ;
  sem E (A ~> B) := forall m F (r : ren (m := m) E F), sem F A -> sem F B.

(** Semantic valuation **)
Definition sval {n m} (E : env n) (F : env m) :=
  forall x, sem F (vnth E x).

Equations semren {n m E F A} (r : @ren n m E F) (s : sem E A) : sem F A :=
  semren s := REPLACE_ME.

Equations renval {n m k E F G} (rho : @sval n m E F) (r : ren (m := k) F G) : sval E G :=
  renval rho r x := REPLACE_ME.

Equations extend {n m A} {E : env n} {F : env m} (rho : sval E F) (a : sem F A) : sval (vcons A E) F :=
  extend rho a x := REPLACE_ME.

Equations eval {n m A} {E : env n} {F : env m} (t : term E A) (rho : sval E F) : sem F A :=
  eval t rho := REPLACE_ME.

Equations reify {n A} {E : env n} (s : sem E A) : normal E A := {
  reify (A := tunit) s := s ;
  reify (A := A ~> B) f := nlam A (reify (f _ _ weak (reflect (svar fin0))))
}
where reflect {n A} {E : env n} (s : stuck E A) : sem E A := {
  reflect (A := tunit) s := nstuck s ;
  reflect (A := A ~> B) s := fun m G r a => reflect (sapp (sren r s) (reify a))
}.

Equations idval {n E} : sval (n := n) E E :=
  idval x := REPLACE_ME.

Equations nbe {n E A} (t : @term n E A) : normal E A :=
  nbe t := reify (eval t idval).

Example test A B : term vnil _ :=
  tlam (A ~> B) (
    tlam A (
      tapp (tvar (E := vcons _ (vcons _ _)) (finS fin0)) (tvar fin0)
    )
  ).

Example tid A : term vnil (A ~> A) :=
  tlam A (tvar (E := vcons _ vnil) fin0).

(** Test on those **)
(* Compute nbe (test tunit tunit).
Compute nbe (tapp (test tunit tunit) (tid tunit)).
Compute nbe (tapp (tapp (test tunit tunit) (tid tunit)) tstar). *)
