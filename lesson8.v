(** * MPRI PRFA (2-7-2) — Live coding session 8

  For this final lecture, we're going to have a look at dependently typed
  programming in Coq. On the way we'll also explore the Equations package
  and all the nice features it provides to make your lives easier.

**)

From Coq Require Import Arith List Lia.
Import ListNotations.

Set Default Goal Selector "!".

(**

  If you remember merge sort, it involves a merge function that takes in two
  sorted lists, and produces a new one.

  Unfortunately, if we write it as follows, Coq will not accept the definition
  as terminating.

**)

Fail Fixpoint merge (l1 l2 : list nat) :=
  match l1, l2 with
  | x :: l1, y :: l2 =>
    if x <=? y then
      x :: merge l1 (y :: l2)
    else
      y :: merge (x :: l1) l2
  | l1, [] => l1
  | [], l2 => l2
  end.

(** We are going to load Equations to help deal with it nicely. **)

From Equations Require Import Equations.

Equations? merge (l1 l2 : list nat) : list nat by wf (length l1 + length l2) lt :=
  merge l1 [] := l1 ;
  merge [] l2 => l2 ;
  merge (x :: l1) (y :: l2) with le_dec x y := {
  | left _ => x :: merge l1 (y :: l2)
  | right _ => y :: merge (x :: l1) l2
  }.
Proof.
  lia.
Qed.

(**

  Ok so many things happen at once here.
  For once, you can see that the syntax differs from the usual definitions.
  Instead we use the keyword [Equations?] which tells Coq to use the Equations
  package to produce the definition.
  Then we have the keyword [by] which is telling Equations why the function is
  terminating, here by saying that the quantity [length l1 + length l2]
  decreases according to order [lt] on [nat].

  Then the branches are given in Haskell/Agda-like syntax by giving patterns for
  the whole `merge l1 l2` expression.
  The keyword `with` let us perform a case analysis on an expression.

  Finally, Equations will try to indeed verify that the recursive calls have
  smaller weight, in one case it doesn't figure it out on its own so we help it
  with [lia].

**)

(** ** EXTRACTION

  It is possible to extract the [merge] function to OCaml using the following
  command.

  This is very useful and this feature was actually one of the main motivations
  behind Coq. CompCert for instance is a compiler exracted from Coq code.

**)

Require Import ExtrOcamlBasic.
Extraction merge.

(** ** Reasoning principles

  Equations actually proves more stuff for us when defining new functions.
  For instance it gives us useful functional induction principles.

**)

Lemma merge_In x l1 l2 :
  In x (merge l1 l2) <-> In x l1 \/ In x l2.
Proof.
  eapply merge_elim.
  all: firstorder congruence.
Qed.

(** Let us look at a simpler example to see what it does.

  NOTE: There is no question mark here because there is nothing to prove like
  termination above.

**)

Equations neg (b : bool) : bool :=
  neg true := false ;
  neg false := true.

(** See all the things it generated about [neg]. **)
Search neg.

(**

  For instance, it generates a functional elimination principle.
  For [neg] it says that to prove [P b (neg b)] you only need to consider the
  two cases in the definitions, meaning you only need to prove
  [P true false] and [P false true].

**)
About neg_elim.

(** Say we want to prove that [neg] is involutive, we have several options. **)
(** The first one is to use [destruct] as before. **)
Lemma neg_inv :
  forall b,
    neg (neg b) = b.
Proof.
  intros [].
  - simp neg. reflexivity. (* Watch out: it's not [simpl] but [simp]! *)
  - simp neg. reflexivity.
Abort.

(** Note that Equations definitions are opaque by default, meaning
  [cbn], [simpl] and friends do not unfold it by default.
  We can change that locally.
**)
Lemma neg_inv :
  forall b,
    neg (neg b) = b.
Proof.
  Transparent neg. (* To tell Coq it's ok to unfold it. *)
  (* Without it [cbn] below does nothing. *)
  intros []. all: cbn. all: reflexivity.
Abort.

(** Or globally by using

  [Set Equations Transparent]

  which will affect all *future* definitions.

**)

(** We can also use [neg_elim]! **)
Lemma neg_inv :
  forall b,
    neg (neg b) = b.
Proof.
  intro b. pattern b, (neg b).
  apply neg_elim.
  - simp neg. reflexivity.
  - reflexivity. (* Actually [reflexivity] works *)
Abort.

(** Even easier, we use the [funelim] tactic which applies [neg_elim] on its
  own, a bit like [induction] applies an induction principle.
**)
Lemma neg_inv :
  forall b,
    neg (neg b) = b.
Proof.
  intros b.
  funelim (neg b).
  all: reflexivity.
Qed.

(** Equations syntax is quite permissive and allows us to use notations. **)

Reserved Notation "x +++ y" (at level 60, right associativity).

Equations app {A} (l l' : list A) : list A := {
  [] +++ l' := l' ;
  (a :: l) +++ l' := a :: (l +++ l')
}
where "x +++ y" := (app x y).

(** ** Functional elimination and recursion

  The [app] definition above is recursive, and Equations can deal with that too.
  We'll do it by hand first: with functional elimination the predicate is always
  going to conclude about the output of the function, but also its inputs.
  This is important because often we want to relate the output with the inputs.

**)

Lemma app_ind :
  forall A (P : list A -> list A -> list A -> Prop),
    (forall l', P [] l' l') ->
    (forall a l l', P l l' (l +++ l') -> P (a :: l) l' (a :: (l +++ l'))) ->
    forall l l', P l l' (l +++ l').
Proof.
  intros A P hnil hcons l l'.
  induction l as [| a l ih] in l' |- *.
  - apply hnil.
  - eapply hcons. eapply ih.
Qed.

(** The one Equations generated is very similar. **)
About app_elim.

(** Once again we apply it using [funelim]. **)
Lemma app_assoc {A} (x y z : list A) :
  x +++ y +++ z = (x +++ y) +++ z.
Proof.
  funelim (x +++ y). 1: auto.
  simp app. rewrite H. (* [H] is the induction hypothesis *)
  reflexivity.
Qed.

Lemma app_nil_r {A} (l : list A) :
 l +++ [] = l.
Proof.
  funelim (l +++ []).
  - reflexivity.
  - simp app. rewrite H. reflexivity.
Qed.

(** ** Matching expressions

  We have already seen it but it is possible to match on expressions that are
  not direct arguments of the function we define using Equations.
  This is done with the `with` keyword.
  Subsequently, Equations takes this branching into account e.g. for [funelim].

**)

Equations filter {A} (l : list A) (p : A -> bool) : list A :=
  filter [] p := [] ;
  filter (a :: l) p with p a => {
  | true => a :: filter l p ;
  | false => filter l p
  }.

Lemma filter_true {A} (l : list A) :
  filter l (fun x => true) = l.
Proof.
  funelim (filter l (fun _ => true)).
  - (* [l = []] *) reflexivity.
  - (* [l = (a :: l)] and [(fun x => true) a = true] *)
    simp filter. rewrite H. reflexivity.
  - (* [l = (a :: l)] and [(fun x => true) a = false] *)
    discriminate.
Qed.

(** * Dependent types

  Equations is able to handle dependent types as well of course.
  Let us look at the following function deciding equality of natural numbers.
  Given [n] and [m] it returns either a proof that [n = m] or a proof that
  [n <> m].

  At the same time we're going to see that if one does not add the question mark
  to [Equations] ([Equations?]), then any missing proof is going to be asked as
  a so-called "proof obligation".

  Before obligations are given to the user to prove, Coq will try to use some
  automation to discharge them automatically.

  WARNING: VSCoq Legacy doesn't tell you about obligations so be careful to
  check that you don't have unresolved obligations. The easiest way is to use
  [Equations?] alaways.

**)

Equations equal (n m : nat) : { n = m } + { n <> m } :=
  equal O O := left eq_refl ;
  equal (S n) (S m) with equal n m := {
    equal (S n) (S ?(n)) (left eq_refl) := left eq_refl ;
    equal (S n) (S m) (right p) := right _
  } ;
  equal x y := right _.

Extraction equal.

(** We can tell Coq what it should do with obligations, here: nothing! **)
#[local] Obligation Tactic := idtac.

Equations split_two {A : Type} (l : list A) : list (A * A) by wf (length l) lt :=
  split_two [] := [] ;
  split_two [a] := [] ;
  split_two (a :: b :: l) := (a, b) :: split_two l.
Next Obligation. (* This is how we focus on obligations. *)
  cbn. lia.
Qed.

(** ** Inacessible branches

  A popular dependent type is the following type of vectors, or length-indexed
  lists. [vec A n] is the type of lists containing exactly [n] elements of type
  [A]. It is defined below.

**)

Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A 0
| vcons (a : A) (n : nat) (v : vec A n) : vec A (S n).

Arguments vnil {A}.
Arguments vcons {A} a {n}.

(**

  We can thus write type-safe head and tail functions by stating that the list
  is of length [S n] for some [n], in other words that it is not empty.
  Coq actually figures out that the [vnil] case is impossible on its own.

**)

Definition head {A n} (v : vec A (S n)) : A :=
  match v with
  | vcons a v => a
  end.

Definition tail {A n} (v : vec A (S n)) : vec A n :=
  match v with
  | vcons a v => v
  end.

(** Well if you print the terms you will see the trick. **)
Print head.

(** Let's do it by hand because it's a good exercise **)

Definition head' {A n} (v : vec A (S n)) : A :=
  match v in vec _ m return
    match m with
    | 0 => unit
    | S k => A
    end
  with
  | vnil => tt
  | vcons a v => a
  end.

Definition tail' {A n} (v : vec A (S n)) : vec A n :=
  match v in vec _ m return
    match m with
    | 0 => unit
    | S k => vec A k
    end
  with
  | vnil => tt
  | vcons a v => v
  end.

(**

  Coq is not always smart enough to see that some patterns are impossible.
  Consider the following [zip] function that it doesn't let you define.

**)

Fail Fixpoint zip {A B n} (v : vec A n) (v' : vec B n) : vec (A * B) n :=
  match v, v' with
  | vnil, vnil => vnil
  | vcons a v, vcons b v' => vcons (a, b) (zip v v')
  end.

(** Thankfully, Equations knows how to do it! **)

Equations zip {A B n} (v : vec A n) (v' : vec B n) : vec (A * B) n :=
  zip vnil vnil := vnil ;
  zip (vcons a v) (vcons b v') := vcons (a, b) (zip v v').

Print zip. (* Quite complicated, it's nice we didn't have to write it ourselves. *)

(**

  Another useful dependent type is that of bounded natural numbers.
  [fin n] represents the natural numbers below [n] (excluding [n]).
  Its name comes from the fact that [fin n] is the archetypical type with
  exactly [n] elements.

**)

Inductive fin : nat -> Type :=
| fin0 n : fin (S n)
| finS n (x : fin n) : fin (S n).

Arguments fin0 {n}.
Arguments finS {n}.

(**

  This allows us to take an index in a vector that is guaranteed to be within
  bounds by typing.

**)

Equations vnth {A n} (v : vec A n) (x : fin n) : A :=
  vnth (vcons a v) fin0 := a ;
  vnth (vcons a v) (finS x) := vnth v x.

(** We now have tools to reason about such dependent types. **)

Lemma vec_expand :
  forall A n (v : vec A (S n)),
    v = vcons (head v) (tail v).
Proof.
  intros A n v.
  (* This tactic is like [induction] by it takes into account the index! *)
  dependent elimination v.
  reflexivity.
Qed.

(** With the following we can help Equations do more things

  [NoConfusion] and [NoConfusionHom] will teach Equations to discriminate
  values of the type automatically and thus derive that more branches are
  inaccessible.

 **)
Derive Signature NoConfusion NoConfusionHom for fin.
Derive NoConfusion for vec.

Lemma zip_vnth :
  forall A B n (v : vec A n) (v' : vec B n) (x : fin n),
    vnth (zip v v') x = (vnth v x, vnth v' x).
Proof.
  intros A B n v v' x.
  funelim (vnth v x). (* Notice how both v and x are destructed at once. *)
  - funelim (vnth v' _).
    simp zip vnth. reflexivity.
  - funelim (vnth v' _).
    simp zip vnth. (* Sometimes [simp] will also solve the goal. *)
Qed.

(** ** Intrinsically typed syntax

  One more thing we can do with dependent types is define simply typed
  λ-calculus (STLC) where the terms are well typed by construction.

  We first define the types.

**)

Inductive type := tunit | tarrow (a b : type).

Notation "A ~> B" := (tarrow A B) (at level 20, right associativity).

(**

  Open terms can have variables in them so we store their types in an
  environment.
  We store them in vectors so it's easy to keep track of variables.
  We could have used lists as well.

**)
Definition env := vec type.

(**

  We now define terms, indexed over the environment of variables they are
  allowed to mention. [n] is letting us keep track of the length of said
  environment so that we make sure variables are bound by placing them in
  [fin n].

  [term E T] reprensents terms of type [T] with variables in [E].
  Notice how [tlam] represents λ and thus binds a variable in the environment
  of its body.

**)
Inductive term {n} (E : env n) : type -> Type :=
| tvar (x : fin n) : term E (vnth E x)
| tstar : term E tunit
| tlam (A : type) B (b : term (vcons A E) B) : term E (A ~> B)
| tapp A B (f : term E (A ~> B)) (u : term E A) : term E B.

Arguments tvar {n E}.
Arguments tstar {n E}.
Arguments tlam {n E} A {B}.
Arguments tapp {n E A B}.

Example test A B : term vnil _ :=
  tlam (A ~> B) (
    tlam A (
      tapp (tvar (E := vcons _ (vcons _ _)) (finS fin0)) (tvar fin0)
    )
  ).

(** Sadly the annotation for [E] is necessary… **)

Check test. (* The type has been computed for us! *)

(** We cannot write examples that do not type in STLC like self-application. **)
Fail Example test' : term vnil _ :=
  tapp tstar tstar.

(** We map STLC types to Coq types **)
Fixpoint interp_type (t : type) : Type :=
  match t with
  | tunit => unit
  | A ~> B => interp_type A -> interp_type B
  end.

(** We also define the concept of valuation of an environment **)
Definition valuation {n} (E : env n) :=
  forall x, interp_type (vnth E x).

(** The empty valuation **)
Definition rho0 : valuation vnil :=
  fun x => match x with end.

(**

  We'll tell Equations to produce transparent constants, meaning [simpl] and co
  will be able to unfold them.

**)
Set Equations Transparent.

(** Extension of a valuation with a new value. **)
Equations extend {n E A} (ρ : valuation (n := n) E) (a : interp_type A) : valuation (vcons A E) :=
  extend ρ a fin0 := a ;
  extend ρ a (finS x) := ρ x.

(** We are now ready to interpret terms! **)
Equations interp {n E A} (t : term (n := n) E A) (rho : valuation E) : interp_type A :=
  interp (tvar x) rho := rho x ;
  interp  tstar rho := tt ;
  interp (tlam A (B := B) b) rho := fun x => interp b (extend rho x) ;
  interp (tapp u v) rho := (interp u rho) (interp v rho).

(** We can test on a few examples and see them get normalised. **)

Eval compute in interp (test tunit tunit) rho0.

Eval compute in interp (tapp (test _ _) (test tunit tunit)) rho0.
