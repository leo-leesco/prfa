(** MPRI PRFA — Exercise session 7 — Equality **)

From Stdlib Require Import List.
Import ListNotations.

Set Default Goal Selector "!".

Axiom REPLACE_ME : forall {A}, A.

Module Leibniz.

  Definition leib_eq {A} (u v : A) :=
    forall (P : A -> Prop), P u -> P v.

  Notation "u == v" := (leib_eq u v) (at level 80).

  (** EXERCISE *)
  Definition refl {A} (a : A) : a == a :=
    fun P Pu => Pu.

  (** EXERCISE
     On veut [forall P, Pv -> Pu], et on peut donner à [e] ce qu'on veut
     
     e (P := fun a => P a -> P u) v
  *)
  Definition sym {A} (u v : A) (e : u == v) : v == u :=
    fun P Pv => e (fun a => P a -> P u) (fun x => x) Pv.

  (** EXERCISE *)
  Definition trans {A} (u v w : A) (e : u == v) (e' : v == w) : u == w :=
    fun P Pu =>
      let Pv := e P Pu in
    e' P Pv.

  Definition trans' {A} (u v w : A) (e : u == v) (e' : v == w) : u == w :=
    e' (leib_eq u) e.

  (** EXERCISE *)
  Definition f_equal {A B} (f : A -> B) {u v} (e : u == v) : f u == f v :=
    fun P Pfu =>
    e (fun a => P (f a)) Pfu.

  (** EXERCISE *)
  Lemma n_plus_0 : forall n, n + 0 == n.
  Proof.
    induction n; simpl.
    - apply refl.
    - apply f_equal.
      assumption.
  Qed.

  (** EXERCISE *)
  Lemma nat_discr : forall n, S n == 0 -> False.
  Proof.
  Admitted.

  Print eq.
  About eq_rect.

  (** EXERCISE

    Show equivalence between Leibniz equality and eq using eq_rect not rewrite
    or destruct.
    You can use refine if it helps.

  **)

End Leibniz.

(* Now we're only going to use eq from the standard library. *)

(* Similar to eq_rect but for propositions. *)
About eq_ind.

(** EXERCISE

  Show symmetry, transitivty and congruence (f_equal) for eq, once using
  eq_ind / eq_rect and once using pattern matching on equality.

**)

(** EXERCISE

  Identify the parameters (uniform and non-uniform) and indices of eq.
  Then consider the following definition of equality eq_ts with rules for
  transitivity and symmetry. What are the parameters (unifrom and non-unfirom)
  and indices? Could the definition be changed (only syntactically) to have
  more parameters?

  Show that eq and eq_ts are equivalent.

*)

Inductive eq_ts {X} : X -> X -> Prop :=
| refl_eq x : eq_ts x x
| sym_eq x y : eq_ts x y -> eq_ts y x
| trans_eq x y z : eq_ts x y -> eq_ts y z -> eq_ts x z.

(** EXERCISE

  Show a lemma similar to f_equal but for dependent functions, ie functions of
  type forall (x : A), B x.

  Hint: You can for instance use eq_rect to state the lemma.

**)

(** EXERCISE

  Define the inductive predicate for even natural numbers we already saw several
  times (try to do it without having to look it up).

  Then prove that even (S (S n)) implies even n.
  Try to do it both using tactics (for instance using the remember tactic,
  but ideally without using inversion directly on even) and by writing a
  proof term directly.

  Do the same to prove that even 1 is false.

  Finally, show that n cannot be even at the same time as S n.
  (This time you can just do it using tactics.)

**)

(** EXERCISE

  Define the map function on lists.

  Show that map (fun x => x) l is the same as l.
  Can you prove that map (fun x => x) is equal to the identity function?

**)

(* Equality principles *)

(** EXERCISE

  We give some equality principles below. You may assume some of them when
  solving the exercises below. Try to assume only what you need.

  Show that map (fun x => x) is equal to the identity function.

  Show that inhabited propositions are equal to True.
  Similarly, show that uninhabited propositions are equal to False.

  Show that two predicates are equal as soon as they are logically equivalent:
  ie. as soon as forall x, P x <-> Q x.

  Show that proof irrelevance follows from proposition extensionality.

  Show that UIP follows from proof irrelevance.

  Show that UIP and K are equivalent.

**)

Definition FunExt :=
  forall A B (f g : A -> B), (forall x, f x = g x) -> f = g.

Definition PropExt :=
  forall (P Q : Prop), (P <-> Q) -> P = Q.

Definition ProofIrrelevance :=
  forall (P : Prop) (p q : P), p = q.

Definition UIP :=
  forall A (u v : A) (p q : u = v), p = q.

Definition K :=
  forall A (u : A) (e : u = u), e = eq_refl.

(** EXERCISE

  Define Boolean equality for natural numbers, ie some
  eq_nat : nat -> nat -> bool.
  (You may have already done it, but try to do it again.)

  Show that when eq_nat n m is true, then n = m.
  Show that when it is false, then n <> m.

  Deduce that equality of natural numbers is decidable.
  This is typically achieved by defining
  eq_dec : forall n m, { n = m } + { n <> m }.
  You can first do it with tactics but try to do it with a proof term.

  To know more about the {} + {} type, execute the following commands.
  Locate can tell you what is the name of an object or notation.
  Print for an inductive will tell you the name and type of its constructors.

**)

Locate "{ _ } + { _ }".
Print sumbool.

(** EXERCISE

  Show extensionality of existential types.
  In other words to prove that exist _ x hx = exist _ y hy, it is enough to
  show x = y.

  Hint: once again you may require an axiom to do it.
  It's fine to assume it and keep going.

**)

(** Equivalence

  There are many ways to define equivalence in Rocq. We will choose one using
  some notion of unique existence, defined below.

  We will say that a function is an equivalence when there exists a unique
  antecedent to each point.

**)

Print unique.

Notation "{ ! x | P }" := (sig (unique (fun x => P))) : type_scope.
Notation "{ ! x : A | P }" := (sig (A := A) (unique (fun x => P))) : type_scope.

Definition isEquiv {X Y} (f : X -> Y) :=
  forall y, { ! x | y = f x }.

Definition equivalence X Y :=
  { f : X -> Y & isEquiv f }.

(** EXERCISE

  Show that equivalences form an equivalence relation, that is that they are
  reflexive, symmetric and transitive.

  Next, show that nat is equivalent to nat*, ie nonzero natural numbers.
  Hint: You can define this as a subset type (using {}) or nat.
  Hint: You may need one extra axiom to complete the proof.

**)

(** Discriminating types **)

(** EXERCISE

  Define a predicate on types that says that a type has exactly one inhabitant.

  Deduce that unit is different from bool.

  Next, show that nat is different from bool.

**)

(*** ADVANCED EXERCISES ***)

(** EXERCISE

  Until now, the equalities we considred have been *homogenous*, meaning
  [u = v] requires both [u] and [v] to have the same type.
  You even have a notation to give the common type [u = v :> A].

  In some cases, it makes sense to compare two objects of a priori different
  types. We can say that [u : A] and [v : B] are *heterogenously* equal when,
  first [A = B] and then [u = v] up to a transport from [A] to [B].

  We can also define it inductively. Show that the two versions are equivalent.

**)

Definition cast {A B} (e : A = B) (t : A) : B :=
  REPLACE_ME.

Definition heq {A B} (u : A) (v : B) :=
  { e : A = B & cast e u = v }.

Inductive Heq {A} (u : A) : forall {B}, B -> Prop :=
| heq_refl : Heq u u.

Lemma heq_Heq A B (u : A) (v : B) :
  heq u v -> Heq u v.
Proof.
Admitted.

Lemma Heq_heq A B (u : A) (v : B) :
  Heq u v -> heq u v.
Proof.
Admitted.

(** EXERCISE

  Does heterogneous equality imply homogenous equality?
  In other words can you prove the following?
  [forall A (u v : A), Heq u v -> u = v]

  Hint: Maybe it requires an axiom?

**)

(** EXERCISE

  Show that nat is equivalent to even natural numbers.

**)

(** EXERCISE

  Cantor theorem for bool:
  Show that there are no surjections from X to X -> bool.
  In other words there are no f : X -> (X -> bool) such that
  for all p there exists x such that f x = p.

  Cantor theorem:
  Show that there are no surjections from X to X -> Prop.

  Now prove the following theorem:

**)

Theorem Lawvere X Y :
  forall (f : X -> (X -> Y)),
    (forall g, exists x, f x = g) ->
    forall (g : Y -> Y), exists y, g y = y.
Proof.
Admitted.

(** EXERCISE

  Can you get a simpler proof of the Cantor theorem for bool now?

**)

(** J eliminator

  We have seen eq_rect / eq_ind, but equality actually enjoys a stronger
  induction principle called the J eliminator.
  Instead of considering a predicate on an element, we also consider that the
  predicate depends on an equality and that we only need to show it when the
  equality is reflexivity to get it for all equalities.

  Its type is the following. Show that you can indeed derive it.

**)

Definition J :
  forall {A} {u : A} (P : forall z, u = z -> Prop) {v : A} (t : P u eq_refl) (e : u = v),
    P v e.
Proof.
Admitted.

(** EXERCISE

  We are now going to show that J is equivalent to singletons being
  contractible, ie that singletons have a exactly one element.
  For this we are going back to the world of Leibniz equality which does not
  enjoy J.

  You have to fill a few REPLACE_MEs but you should have solved them already
  so you can easily copy paste your definitions, and all_equal should be
  safely removed.

  You can then prove the equivalence at the end of the module Leibniz2.

**)

Module Leibniz2.

  Definition leib_eq {A} (u v : A) :=
    forall (P : A -> Prop), P u -> P v.

  Notation "u == v" := (leib_eq u v) (at level 80).

  Definition refl {A} (a : A) : a == a :=
    REPLACE_ME.

  Definition sym {A} (u v : A) (e : u == v) : v == u :=
    REPLACE_ME.

  Definition trans {A} (u v w : A) (e : u == v) (e' : v == w) : u == w :=
    REPLACE_ME.

  Definition J_prop :=
    forall A (u : A) (P : forall z, u == z -> Prop) v (t : P u (refl u)) (e : u == v),
      P v e.

  Definition singleton {A} (x : A) := { y | x == y }.

  Definition incl {A} (x : A) : singleton x :=
    exist _ x (refl x).

  Definition all_equal (A : Type) : Prop :=
    REPLACE_ME.

  Lemma all_equal_implies_J :
    (forall A (x : A), all_equal (singleton x)) ->
    J_prop.
  Proof.
  Admitted.

  Lemma J_implies_all_equal :
    J_prop ->
    (forall A (x : A), all_equal (singleton x)).
  Proof.
  Admitted.

End Leibniz2.

(** EXERCISE

  Uniqueness of identity proofs (UIP) is not provable in general but it still
  holds for specific types, namely types with a decidable equality.
  This fact is known as Hedberg's theorem.

  We thus state UIP_for, so that UIP_for X means UIP holds for type X.

  We're going first to prove UIP holds for nat.

**)

Definition UIP_for X :=
  forall (u v : X) (p q : u = v), p = q.

Lemma nat_eqdec_eq x :
  PeanoNat.Nat.eq_dec x x = left eq_refl.
Proof.
Admitted.

Lemma UIP_nat' (x y: nat) :
  forall (e : x = y),
    match PeanoNat.Nat.eq_dec x y with
    | left e' => eq_ind _ _ eq_refl _ e' = e
    | _ => True
    end.
Proof.
Admitted.

Fact UIP_refl_nat (x: nat) :
  forall (e : x = x), e = eq_refl.
Proof.
Admitted.

Lemma UIP_for_nat : UIP_for nat.
Proof.
Admitted.

(** EXERCISE

  We are now going to prove the general case.
  Prove Hedberg's theorem as follows.

**)

Definition HF X (f : forall (x y : X), x = y -> x = y) :=
  forall x y (e e' : x = y), f x y e = f x y e'.

Lemma Hedberg' X :
  ex (HF X) -> UIP_for X.
Proof.
Admitted.

Theorem Hedberg X :
  (forall x y: X, x = y \/ x <> y) -> UIP_for X.
Proof.
Admitted.

(** EXERCISE

  Using FunExt, we can show that two functions of type nat -> bool are equal if
  and only if they are not not equal. Prove it.

**)

Definition stable (P : Prop) :=
  ~~P -> P.

Fact FE_stable_HF X :
  FunExt ->
  (forall (x y : X), stable (x = y)) ->
  sig (HF X).
Proof.
Admitted.

Fact FE_test_eq_stable :
  FunExt ->
  forall (f g : nat -> bool), stable (f = g).
Proof.
Admitted.

(** EXERCISE

  You may or may not have heard of homotopy type theory and univalent
  foundations. This is a relatively recent development in which equality of
  types corresponds to equivalences. This essentially justifies the informal
  mathematical practice of considering isomorphic objects to be the same.

  Define a term to_equiv that inhabits equivalence X Y from X = Y.

  Univalence is then stated as this function being itself being an equivalence.

**)

Definition to_equiv X Y : X = Y -> equivalence X Y :=
  REPLACE_ME.

Definition Univalence :=
  forall (X Y : Type), isEquiv (to_equiv X Y).

(** EXERCISE

  Show that assuming univalence, equivalent types are equal.

**)

(** EXERCISE

  Univalence is incompatible with UIP. One way is to show that
  [equivalence A B = (A = B)] and that there are two equivalences between
  [bool] and itself, which negates UIP.

**)

Lemma Univalence_neg_UIP :
  Univalence -> ~ UIP.
Proof.
Admitted.
