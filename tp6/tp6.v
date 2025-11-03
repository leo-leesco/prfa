(** MPRI — Exercise session 6 — Meta-programming **)

From Stdlib Require Import Nat List String.

Set Default Goal Selector "!".

Axiom REPLACE_ME : forall {A : Type}, A.

(** REMINDER — Syntax of [match goal] **)

Ltac my_assumption :=
  match goal with
  | H : ?A |- ?A => apply H
  end.

Goal forall P Q R, P -> Q -> R -> P.
Proof.
  intros.
  my_assumption.
Qed.

(** EXERCISE

  Define a tactic to perform [split] repeatedly on goals of the shape [A * B]
  but not on any other kinds of goals (for instance it should not solve [True]).

  For instance, on [(nat * bool) * (unit * bool)] it should yield 4 subgoals.

  Hint: You will need [split] and [match goal] or [lazymatch goal] and [idtac].

**)

Ltac splits :=
  repeat match goal with
  | |- ?A * ?B => split
  end.

(** Try it on these goals. **)

Goal nat * bool.
Proof.
  splits. (* 2 goals *)
Abort.

Goal nat * (bool * unit) * (unit * nat * bool) * unit.
Proof.
  splits. (* 7 goals *)
Abort.

(** NEW TACTIC — [clear]

  It is possible to *forget* about hypotheses using the [clear] tactic as
  follows.

  It is sometimes useful before applying the [induction] tactic to get rid of
  something in the generated induction hypothesis.

**)

Goal forall P Q R, P -> Q -> R -> P.
Proof.
  intros P Q R p q r.
  clear Q p q.
  Fail clear P. (* Cannot get rid of something used elsewhere. *)
  clear. (* Without arguments it clears everything it can *)
  exfalso.
  clear.
Abort.

(** EXERCISE

  Prove the following by induction on [n].
  In particular, don't use [lia], we want you to use the induction hypothesis.

**)
Goal forall n, n mod 14 = 7 -> n - n = 0.
Proof.
  intros. clear H.
  induction n.
  - reflexivity.
  - simpl. assumption.
Qed.

(** Matching on the type of an expression

  The same way we can match on the goal, we can match the type of an expression
  using the [type of] construct.

**)

Ltac handle_hyp h :=
  lazymatch type of h with
  | (?A * ?B)%type => destruct h
  | nat => induction h
  | _ => idtac
  end.

Goal forall (n : nat * nat), fst n = snd n.
Proof.
  intro n.
  handle_hyp n. (*@%!*)
  handle_hyp n.
Abort.

(** NEW TACTIC — [fresh]

  Not all tactics operate on goals, some are used to produce values, or even
  names (as in variable names).

  This is the case of the [fresh] tactic which you can use to get a *fresh*
  name (as in not used in the currrent context) to give to a newly introduced
  variable.

**)

Goal forall n m k, n + m - k = m + n - k.
Proof.
  let N := fresh in
  intro N. (* Here it chooses [H], not very cool, we can guide naming a bit *)
  let N := fresh "n" in
  intro N. (* We suggested [n] and it stick with it. *)
  let N := fresh "n" in
  intro N. (* This time, [n] was already taken, so it chose [n0] instead *)
  let na := fresh H in
  destruct H as [| na]. (* This time we suggested to use the name of [H] *)
  (* It picked [H0] *)
Abort.

(** EXERCISE — Forward reasoning

  A very useful tactic that should be part of the standard library, but is not,
  is the [fwd] tactic.
  Given [H : P -> Q], [fwd H] will yield two goals:
  - one where [P] must be proven
  - and one where [H] has been replaced by [H : Q]

  Note that there shouldn't be anything else appearing in the goal.

**)

Ltac fwd h :=
  match type of h with
  | ?P -> ?Q => let p := fresh "p" in assert (p : P); [| specialize (h p); clear p]
  end.

(** Try on the following goal.
  Do not use [apply], only [intros], [fwd] and [assumption]
**)
Goal forall P Q R, (P -> Q -> R) -> (P -> Q) -> P -> R.
Proof.
  intros P Q R pqr pq p.
  fwd pqr.
  - assumption.
  - fwd pqr.
    + fwd pq; assumption.
    + assumption.
Qed.

(** EXERCISE (Harder)

  Try to generalise the code for [fwd] so that you can also provide a tactic.
  If [H : P -> Q] then [forward_gen H tac ] will also apply [tac] to try and
  solve the goal [P] first.

**)

Ltac forward_gen h tac :=
  fwd h; [tac |].

(** We define handy notations **)
Tactic Notation "forward" constr(H) := fwd H.
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.

Goal forall P Q R, (P -> Q -> R) -> (P -> Q) -> P -> R.
Proof.
  intros P Q R h1 h2 h3.
  forward h2 by assumption.
  do 2 forward h1 by assumption.
  assumption.
Qed.

From PRFA Require Import MetaRocqPrelude.

(** Print Assumptions

  In Coq, you have a very useful command which can tell you on which axiom a
  given lemma depends.

  See how it works below.

**)

Axiom LEM : forall (P : Prop), P \/ ~ P.
Axiom funext : forall A B (f g : A -> B), (forall x, f x = g x) -> f = g.

Lemma foo :
  (fun n => n + 0) = (fun n => n).
Proof.
  apply funext. intro. rewrite <- plus_n_O. reflexivity.
Qed.

Print Assumptions foo. (* Only [funext] is listed. *)

(** We will now try to implement our own [Print Assumptions] using MetaRocq.

  For this, we need to be able to manipulate not only the term but also its
  environment to be able to check its dependencies.
  For instance, if we inspect [foo] above, we need to know that [funext] is
  indeed referring to an axiom, and this information is not contained within
  [foo] itself.

  We can use [$quote_rec] to get both the term and its dependencies as follows:

**)

Definition q_foo := $quote_rec foo.

Check q_foo. (* global_env × term *)

(**

  We can for instance querry the environment to see whether it contains
  some constant such as [plus_n_O] or [funext].

**)

Definition foo_env :=
  let (env, _) := q_foo in env.

Compute lookup_constant foo_env (MPfile ["Peano"; "Init"; "Coq"], "plus_n_O").

(**

  We get [Some] and then a big record with a [cst_type] and [cst_body] which
  is also of the form [Some _].
  The presence of this [cst_body] means that this is a [Definition] and not an
  [Axiom].

  Indeed check out what it returns for [funext].

  Warning: You have to change [tp6] into the name of your file, here this
  assumes you didn't rename it and it is [tp6.v].

**)

Compute lookup_constant foo_env (MPfile ["tp6"; "PRFA"], "funext").

(** This time, [cst_body := None]. It's an axiom. **)

(**

  To give you inspiration for the rest here is the (deep) identity function on
  [term].

**)

Fixpoint identity (t : term) :=
  match t with
  | tRel n => tRel n
  | tVar id => tVar id
  | tEvar ev args => tEvar ev (map identity args)
  | tSort s => tSort s
  | tCast t kind v => tCast (identity t) kind (identity v)
  | tProd na ty body => tProd na (identity ty) (identity body)
  | tLambda na ty body => tLambda na (identity ty) (identity body)
  | tLetIn na def def_ty body => tLetIn na (identity def) (identity def_ty) (identity body)
  | tApp f args => tApp (identity f) (map identity args)
  | tConst c u => tConst c u
  | tInd ind u => tInd ind u
  | tConstruct ind idx u => tConstruct ind idx u
  | tCase ind p discr brs =>
      let p' := map_predicate id identity identity p in
      let brs' := map_branches identity brs in
      tCase ind p' (identity discr) brs'
  | tProj proj t => tProj proj (identity t)
  | tFix mfix idx => tFix (map (map_def identity identity) mfix) idx
  | tCoFix mfix idx => tCoFix (map (map_def identity identity) mfix) idx
  | tInt i => tInt i
  | tFloat f => tFloat f
  | tArray u arr def ty => tArray u (map identity arr) (identity def) (identity ty)
  | tString s => tString s
  end.

(** EXERCISE

  Define a Coq function [assumptions : global_env × term -> list kername]
  such that [Compute assumptions ($quote_rec f)] returns the list of
  assumptions (axioms) that [f] depends on, including recursively.

  Note: You cannot convince Coq that it is terminating, so we'll deactivate
  termination checking. That's ok when meta-programming.

  Hint: You may use the [flat_map] function too.

**)

Unset Guard Checking.
Section assums.

  Context (env : global_env).

  Fixpoint assms (t : term) : list kername :=
    let _ := lookup_constant env in (* This function might be useful *)
    REPLACE_ME.

End assums.
Set Guard Checking.

Definition assumptions p :=
  assms p.1 p.2.

Compute assumptions ($quote_rec 0).

Compute assumptions ($quote_rec foo).

Definition bar : nat :=
  let x := foo in
  139.

Compute assumptions ($quote_rec bar).

Module test.

  Require Import Classical.

  Lemma DNE P : ~~ P -> P.
  Proof.
    tauto.
  Qed.

End test.

Compute assumptions ($quote_rec test.DNE).

(** EXERCISE

  Define a function which replaces any subterm of the form [a * b + c] with
  [muladd a b c] defined below.

  Hint: You can use [u == v] to check whether [u] and [v] are equal terms
  (it returns a boolean).

**)

Definition muladd a b c :=
  a * b + c.

Fixpoint fold_muladd (t : term) : term :=
  REPLACE_ME.

(** Remove the [Fail] here **)

Fail Check $unquote (fold_muladd ($quote (3 * 2 + 5))).

Fail Check $unquote (fold_muladd ($quote (1 + (3 * 2 + 5)))).

Fail Check $unquote (fold_muladd ($quote ((9 * 2 + 0) * (1 + (3 * 2 + 5)) + 1 + (3 * 2 + 5)))).

(** EXERCISE

  Now that you suffered through this definition, we'll give you a handy
  combinator we call [transform].
  [transform] takes [h : tm_handler] and transforms [t : term] into another
  [term].
  The handler is typically of the form [fun t k => ...] where [t] is the subterm
  to inspect/transform and [k] is a continuation. Calling [k] on a subterm
  (or on [t]) itself, gives control back to [transform] which will decompose
  the subterm once, and then call the handler again on the subsequent subterms.

  Now define [fold_muladd] again using this technique.

  Note: If you want, you can also do the same for [assumptions] by using
  [tm_fold] which is similar but implements a fold instead.

**)

(** Let's go back to Ltac for a bit **)

(** EXERCISE

  Expand the [my_tauto] tactic below so that it solves the following goals.

**)

Ltac my_tauto :=
  lazymatch goal with
  | |- True => constructor
  end.

Section Tauto.

  Variables (P Q R : Prop).

  Goal P -> True /\ True.
  Proof.
    Fail my_tauto.
  Admitted.

  Goal P -> P.
  Proof.
    Fail my_tauto.
  Admitted.

  Goal P -> (P -> R) -> R.
  Proof.
    Fail my_tauto.
  Admitted.

  Goal False \/ True.
  Proof.
    Fail my_tauto.
  Admitted.

  Goal (P \/ Q \/ False) /\ (P -> Q) -> True /\ (R \/ Q).
  Proof.
    Fail my_tauto.
  Admitted.

End Tauto.

(** Some more MetaRocq **)

(** EXERCISE

  Write a command [reify] that turns a Coq expression of type [nat] into an
  expression of the following datatype.
  Expressions that do not start with [+] or [*] are reified as constants.

**)

Inductive arith :=
| aPlus : arith -> arith -> arith
| aTimes : arith -> arith -> arith
| aConst : nat -> arith.

Fixpoint reify (t : term) : term :=
  REPLACE_ME.

Goal 4 * (9 + 12) + (3 + 1 * 7) = 2.
Proof.
  Fail match goal with
  | [ |- ?L = _ ] =>
    let x := eval cbv in $unquote (reify ($quote L)) in
    pose x
  end.
Abort.

(** ADVANCED EXERCISE

  Write a meta-program that takes a definition potentially using an axioms and
  a proof of said axiom to produce a new definition, equal to the original one
  expcet that uses of the axioms are replaced by the proof.

  The axiom to be replaced is going to be given as a [kername], like those
  collected by [assumptions].
  You don't actually have to verify that the constant is indeed an axiom.

  Hint: You will need [eq_constant].

**)

Definition instantiate_axiom (ax : kername) (prf : term) : term -> term :=
  REPLACE_ME.

Axiom mystery : nat.

Definition what :=
  mystery * 3.

Fail Compute $unquote (instantiate_axiom ($name mystery) ($quote 10) ($Quote what)).

(** ADVANCED EXERCISE

  A slightly harder version would be to turn a definition using axioms to one
  assuming these axioms with an implication.

  For instance, for the [foo] defined above which uses [funext], we would expect
  something of the following type.
  [
    (forall A B (f g : A -> B), (forall x, f x = g x) -> f = g) ->
    (fun n => n + 0) = (fun n => n)
  ]

  Hint: You can use [assumptions] and [lookup_constant] to get the type of a
  constant, and [lift0 1 t] to weaken [t] by adding one new variable in the
  context.

  You can also use a variant of [transform] called [transform_nb] which also
  tracks the number of introduced variables (to know how much to lift by).

**)

Definition unaxiom (p : global_env * term) : term :=
  REPLACE_ME.

Fail Eval simpl in $unquote (unaxiom ($Quote_rec what)).

Axiom unkown : bool.
Axiom random : nat -> nat.

Definition test f :=
  if unkown then what else random (f 9).

Fail Eval simpl in $unquote (unaxiom ($Quote_rec test)).

(** ADVANCED EXERCISE — Deriving (hard)

  We promised MetaRocq could be used to derive automatically certain things.
  Let's see how this can be done by automatically deriving update functions for
  a record.

  We assume that there is no dependency between the fields, otherwise it's
  unclear what an update function should do.

  This exercise is hard, so it makes sense to make some assumptions first
  such as the absence of parameters (like in [triple] below) or of local
  definitions (like in [trap] below).
  Don't hesitate to ask questions if you are stuck.

  We'll start with a few record definitions, together with one example of an
  update function, don't hesitate to write your own and quote them to understand
  what you need to write.

**)

Record point3D := {
  px : nat ;
  py : nat ;
  pz : nat
}.

Record Zalt := {
  num : nat ;
  positive : bool
}.

Record triple A B C := {
  p1 : A ;
  p2 : B ;
  p3 : C
}.

Record trap := {
  v1 : nat ;
  v2 := 10 ^ v1 ;
  v3 : nat
}.

(** We write an update for [num] by hand. **)
Definition upd_num (f : nat -> nat) (x : Zalt) :=
  match x with
  | Build_Zalt num positive => Build_Zalt (f num) positive
  end.

(** NOTE

  There are other ways to write it, but this one might be the easiest to
  automate.

**)

(** Now we can look at how it is quoted.

  We use [$Quote] rather than [$quote] to unfold the constant [upd_num] when
  quoting it. Otherwise we would get some [tConst] which is not as informative.

**)

Definition q_upd_num := $Quote upd_num.
Print q_upd_num.

(** Below is a meta-program that gives you the definition of an inductive.

  Hint: It may be useful to you later, perhaps no as-is, but with some
  modification to also get the argument of [tInd].

**)
Definition get_inductive {A} (ind : A) :=
  t <- tmQuote ind ;;
  match t with
  | tInd ind _ =>
    let kn := ind.(inductive_mind) in
    tmQuoteInductive kn
  | _ => tmFail "Not an inductive type"
  end.

(** We use it like this to define [Zalt_def] to inspect at our leisure. **)
MetaRocq Run (
  mib <- get_inductive Zalt ;;
  tmDefinition "Zalt_def" mib
).

(** This now contains the definition of [Zalt].

  You may compare the information you see in here with what appeared in
  [q_upd_num]. It might be useful to copy paste them to better compare.

**)
Print Zalt_def.

(** SOME TOOLS

  To help you build the [derive_updates] meta-program, we'll give you some
  useful tools.

  Also check out the following useful constructs:
  - [tmMkDefinition] takes a [string] and a [term] and produces a definition
    using that name (if fresh, otherwise it fails) and unquoting the given term.
  - [tmFreshName] takes a [string] and will return a new string that is fresh in
    the current environment, based on the given one (typically by adding a
    number at the end).

  If you plan to handle parameters:
  - [it_mkLambda_or_LetIn] takes [c : context] and [t : term] and produces
    a new λ-abstraction with body [t] and quantifying over [c].
    Basically it does the right thing by inserting as many [tLam] as necessary.
  - [subst l 0 t] will substitute the variables of [t] using the terms provided
    in [l]. For this exercise, you can provide garbage (just some random
    [tRel k] will suffice), what matters is the number of terms you provide.
    Providing [3] will reduce [tRel 5] to [tRel 2].

**)

(** Handy concatenation notation. **)
Notation "a # b" := (String.append a b).

(** To debug we recommend you use the following in place of [tmMkDefinition] **)
Definition tmDebugDefinition na (t : term) :=
  t <- tmEval all t ;;
  tmDefinition na t.

(** [mkr 3 2] will produce [[ tRel 4 ; tRel 3 ; tRel 2 ]] **)
Fixpoint mkr i off :=
  match i with
  | 0 => []
  | S i => tRel (off + i) :: mkr i off
  end.

(** Extract the name from [aname] or use [d] as default. **)
Definition get_name (a : aname) d :=
  match a.(binder_name) with
  | nNamed na => na
  | nAnon => d
  end.

Definition derive_updates {A} (ind : A) : TemplateMonad unit :=
  REPLACE_ME.

(** SUGGESTION

  Use the same as [derive_updates] with [tmDebugDefinition] instead of
  [tmMkDefinition]. It will help debug because I don't expect the error messages
  to be very useful.

**)
Definition debug_derive_updates {A} (ind : A) : TemplateMonad unit :=
  REPLACE_ME.

(** Below, one of them should always fail **)
Fail MetaRocq Run (derive_updates point3D).
Fail MetaRocq Run (derive_updates Zalt).
Fail MetaRocq Run (derive_updates nat).
Fail MetaRocq Run (derive_updates triple).
Fail MetaRocq Run (derive_updates trap).

(** Probably out meta-program doesn't do it for us. **)
Fail Arguments upd_p1 {A B C}.
Fail Arguments upd_p2 {A B C}.
Fail Arguments upd_p3 {A B C}.

(** Test that it works

  If you manage to execute those lines, it's very likely that it does, but
  better safe than sorry.

**)

Fail Compute upd_p2 S {| p1 := "hello" ; p2 := 23 ; p3 := true |}.
Fail Compute upd_v3 (fun n => 23 + n) {| v1 := 78 ; v3 := 12 |}.
