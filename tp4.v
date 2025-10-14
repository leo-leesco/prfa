(** * MPRI PRFA / 2025 / Exercise session 4 **)

From Coq Require Import Lia List ZArith.
Import ListNotations.

Axiom REPLACE_ME : forall {A}, A.

(** Actually products that are defined using an inductive type,
    can also be defined as records. For this we use parameters to records.
    They work like inductive parameters.

    In fact, records are syntactic sugar over inductive types with one
    constructor that takes all the fields as arguments, and we can even give
    a name to that constructor.
**)

Record prod' (A B : Type) := mkpair {
  fst' : A ;
  snd' : B
}.

Definition some_pair := mkpair _ _ 12 bool.
Print some_pair.

(** Actually it's annoying to have the underscores in mkpair _ _ 12 bool
    we're going to change that with the Arguments command.
**)

Arguments mkpair {A B}.

Definition some_other_pair := mkpair false true.

(** You can also use do pattern matching using this constructor. **)

Definition to_prod {A B} (p : prod' A B) : A * B :=
  match p with
  | mkpair a b => (a, b)
  end.

(** Since there is only one constructor, we can also use let **)

Definition to_prod_alt {A B} (p : prod' A B) : A * B :=
  let 'mkpair a b := p in (a, b).

(** We can also use a more generic notation that doesn't require remembering
    the name of mkpair. It's maybe not as explicit so it's up to you to decide
    which version you prefer.
**)

Definition to_prod_alt2 {A B} (p : prod' A B) : A * B :=
  let (a, b) := p in (a, b).

(** Generally, one uses the projections directly.
    They take the parameters as arguments so for convenience we declare them
    as implicit.
**)

Arguments fst' {A B}.
Arguments snd' {A B}.

Definition to_prod_alt3 {A B} (p : prod' A B) : A * B :=
  (fst' p, snd' p).

(** EXERCISE

  Show that to_prod and to_prod_alt3 produce the same result.

**)

Lemma to_prod_equiv {A B} (p:prod' A B) : to_prod p = to_prod_alt3 p.
Proof.
  destruct p as [a b]. reflexivity.
Qed.


(** We can use records to represent more complex mathematical structures
    by also taking types as fields. See for instance the following record
    representing monoids.
**)

Record monoid := {
  m_ty : Type ;
  m_ne : m_ty ;
  m_op : m_ty -> m_ty -> m_ty ;
  m_l_ne : forall x, m_op m_ne x = x ;
  m_r_ne : forall x, m_op x m_ne = x ;
  m_assoc : forall x y z, m_op (m_op x y) z = m_op x (m_op y z)
}.

(** EXERCISE

  Define a record for groups.

**)

Record group := {
  g_ty : Type ;
  g_ne : g_ty ;
  g_op : g_ty -> g_ty -> g_ty ;
  g_l_ne : forall x, g_op g_ne x = x ;
  g_r_ne : forall x, g_op x g_ne = x ;
  g_assoc : forall x y z, g_op (g_op x y) z = g_op x (g_op y z) ;
  g_inverse : forall x, exists y, g_op x y = g_ne /\ g_op y x = g_ne ;
}.

(** EXERCISE

  Give an instance of monoid for nat.

**)

Definition nat_monoid : monoid.
Proof.
  refine {|
    m_ty := nat ;
    m_ne := 0 ;
    m_op m n := m + n;
  |}.
  all: lia.
Defined.

Compute nat_monoid.(m_ne). (* Notation for m_neu nat_monoid *)
Check nat_monoid.(m_op).

(** We can prove things generically about monoids. **)

Notation "a ** b" := (m_op _ a b) (at level 11, left associativity).

(** EXERCISE

  Prove the following fact on monoids.

**)

Lemma monoid_fact :
  forall (M : monoid) (x y : M.(m_ty)),
    x ** M.(m_ne) ** y = x ** y.
Proof.
  intros.
  replace (x ** M.(m_ne)) with x.
  - reflexivity.
  - apply eq_sym. apply m_r_ne.
Qed.

(** EXERCISE

  Prove the following lemma using monoid_fact.

**)

Lemma nat_fact :
  forall (x y : nat),
    x + 0 + y = x + y.
Proof.
  specialize (monoid_fact nat_monoid).
  intro. assumption.
Qed.

(** EXERCISE

  Show that lists form a monoid using ++ as operation.
  How does monoid_fact translate to lists?
  Note that, unlike ** or +, ++ is associated to the right,
  meaning x ++ y ++ z stands for x ++ (y ++ z).

**)

Definition list_monoid {A : Type}: monoid.
Proof.
  refine {|
    m_ty := list A;
    m_ne := [];
    m_op l m := l ++ m;
  |}.
  - reflexivity.
  - intro l. induction l as [| x l IH].
    + reflexivity.
    + simpl. rewrite IH. trivial.
  - intros. apply eq_sym. apply app_assoc.
Defined.

(** EXERCISE

  Products of monoids also yields a monoid. Prove it.

**)

Definition product_monoid (M N : monoid): monoid.
Proof.
  refine {|
    m_ty := M.(m_ty) * N.(m_ty);
    m_ne := (M.(m_ne),N.(m_ne));
    m_op '(a,x) '(b,y) := (a ** b, x ** y);
  |}.
  - intros [a x]. f_equal; apply m_l_ne.
  - intros [a x]. f_equal; apply m_r_ne.
  - intros [a x] [b y] [c z]. f_equal; apply m_assoc.
Defined.

(** Classes **)

Class Monoid (A : Type) (neu : A) (op : A -> A -> A) := {
  mon_left_neutral : forall x, op neu x = x ;
  mon_right_neutral : forall x, op x neu = x ;
  mon_assoc : forall x y z, op (op x y) z = op x (op y z)
}.

(** EXERCISE

  Instance is a a special command for definitions that register them as things
  Coq will use automatically if it has to find a value for Monoid nat 0 plus.

  Don't worry too much about the export thing. This is called an attribute
  and it just means that if someone imports the file, then the instance will
  still be available. We could instead use #[local] to restrict the instance
  to the module. It does not matter for the course.

  Complete the following instance.

**)
#[export] Instance MonoidNat : Monoid nat 0 plus.
Proof.
  split; lia.
Qed.

(** EXERCISE

  Some lemmas we can prove using only the monoid structure on (ℕ,0,+).
  See how Coq infers which proofs we are talking about.

  Prove the following using only monoid laws.

**)
Lemma test_nat :
  forall k n m, k + n + m + 0 = k + (n + m).
Proof.
  intros.
  rewrite mon_right_neutral.
  apply mon_assoc.
Qed.

(** EXERCISE

  Prove the previous statement on monoids in general.
  Then use it to reprove it for nat.

  Hint: If asked for an instance of Monoid, you can always write
  exact _.
  It will trigger class resolution and find it automatically (if you have a
  corresponding instance).

**)

Lemma test_monoid {A : Type} {e : A} {op : A -> A -> A} (M : Monoid A e op):
  forall a b c, op (op (op a b) c) e = op a (op b c).
Proof.
  intros.
  rewrite mon_right_neutral.
  apply mon_assoc.
Qed.

(** EXERCISE

  Define an instance for lists and apply test_monoid to it.

**)

#[export] Instance MonoidList {A : Type}: Monoid (list A) [] (@app A).
Proof.
  split.
  - trivial.
  - apply app_nil_r.
  (* - intro l. induction l as [| x l IH]. *)
  (*   + trivial. *)
  (*   + simpl. rewrite IH. trivial. *)
  - intros. apply eq_sym. apply app_assoc.
Qed.
(** EXERCISE

  Complete the product instance.

**)

#[export] Instance MonoidProd :
  forall A B na nb opa opb,
    Monoid A na opa ->
    Monoid B nb opb ->
    Monoid (A * B) (na,nb) (fun '(xa,xb) '(ya,yb) => (opa xa ya, opb xb yb)).
Proof.
  split.
  - intros [a b]. f_equal; apply mon_left_neutral.
  - intros [a b]. f_equal; apply mon_right_neutral.
  - intros [a b] [a' b'] [a'' b'']. f_equal; apply mon_assoc.
Qed.

(** Now you can see that Coq can infer complex monoid structures on its own! **)
Definition foo : Monoid (nat * nat * nat) _ _ := _.
Print foo.

(** If you defined an instance for list, then the following should succeed
    (remove the Fail).
**)
(*Fail*) Definition bar : Monoid (list bool * nat * list nat) _ _ := _.

(** Here is another example of class: decidable equality. **)

Class Eq A := {
  eqb : A -> A -> bool ;
  eqb_iff : forall x y, eqb x y = true <-> x = y
}.

(** EXERCISE

  Complete the following function that tests whether an element is inside a
  list. Thanks to classes, we can define this function for all types with a
  decidable equality.

  Give it a specification using the In predicate and show it correct with
  respect to it.

  Note: The special tick before {Eq A} is so that we don't have to give it a
  name. Indeed we don't care about the name of the instance because we don't
  need to refer to it explicitly, Coq finds it on its own.
**)

Fixpoint memb {A} `{Eq A} (x : A) (l : list A) : bool :=
  match l with
  | [] => false
  | a :: l => orb (eqb x a) (memb x l)
  end.

(** EXERCISE

  Give an instance of Eq for nat and test memb on some lists.

  You can use already proven lemmas from past weeks or from the standard
  library.
  Tip: Use the Search command as follows.
**)

Search (nat -> nat -> bool).

(** Another useful tool is the refine attribute that also lets us give only
    partial instances.
**)

#[export, refine] Instance Eq_nat : Eq nat := {|
  eqb := REPLACE_ME
|}.
Proof.
  apply REPLACE_ME.
Defined. (* We still need to use Defined though. *)

Compute (eqb 0 1).
Compute (eqb 12 12).

Compute (memb 1 [ 3 ; 5 ; 1 ]).
Compute (memb 12 [ 3 ; 5 ; 1 ]).

(** EXERCISE

  Define a class of groups and show uniqueness of neutral and inverse for all
  groups.

  Apply this result to a group of your choosing (you will have to provide an
  instance). To apply a lemma, sometimes apply is not enough.
  In this case you can use eapply which is more permissive. It creates
  existential variables (starting with a question mark) corresponding to values
  it couldn't guess. They are typically resolved as you prove the various
  goals.

  Can you show that every group forms a monoid (again, provide a generic
  instance)?

**)

(** AUTOMATION

  Classes are one form of automation. There are others in Coq. The main one
  being tactics. Indeed they can be used to derive properties automatically.
  We will start by looking again at the In predicate.

  We'll start by proving some easy lemmas.

**)

(** EXERCISE

  Prove the following lemmas using auto to conclude.

**)

Lemma In_hd :
  forall A (x : A) l,
    In x (x :: l).
Proof.
Admitted.

Lemma In_tl :
  forall A (x y : A) l,
    In x l ->
    In x (y :: l).
Proof.
Admitted.

(** EXERCISE

  Now we would like auto to deal with In without the need to use simpl.
  It should also be able to deal with more complex examples like the
  following.

  Prove it by hand first.

**)

Lemma In_4 :
  forall A (x a b c d : A) l,
    In x l ->
    In x (a :: b :: c :: d :: l).
Proof.
Admitted.

(** Applying the lemma by hand is not very nice, and rather tedious.
    We're going to declare hints so that auto knows how to use them.

    In fact, we're first going to declare a new database of hints dedicated
    to In. We call it indb, because why not?
**)

Create HintDb indb.

(** We then add hints to the database using the Hint Resolve command.
    Like for instances, we need to specify a locality. It doesn't matter so
    we're going to go with export as before.
    We then give it the name of a definition (or lemma etc.) and after the
    colon the databases to which we want to add the hint.
**)

#[export] Hint Resolve In_hd : indb.

(** EXERCISE

  Prove the following lemma with auto.
  Remember you have to give the database to it.

**)

Lemma In_hd' :
  forall A (x : A) l,
    In x (x :: l).
Proof.
Admitted.

(** EXERCISE

  Expand the database so that auto with indb is enough to solve the following
  goals.

  Note: Goal is like Lemma but it doesn't require a name. You won't be able to
  reuse the proven goal afterwards, but it's useful to test things.

**)

Goal forall A (x a b c d : A) l,
  In x l ->
  In x (a :: b :: c :: d :: l).
Proof.
Admitted.

Goal forall A (x a b c d : A) l,
  In x (a :: b :: x :: c :: d :: l).
Proof.
Admitted.

(** EXERCISE

  Show that In x l implies In x (l ++ r) and that In x r implies In x (l ++ r).

**)

(** EXERCISE

  Now add both lemmas to indb, for the first time we are introducing a choice
  for auto: presented with the goal In x (l ++ r) it has to choose whether to
  go left or right. It has no way to know in advance which one is better so it
  will pick one and backtrack if it doesn't work.

  Use it to solve the two following goals.

**)

Goal forall A (x a b c d : A) l l',
  In x l ->
  In x ([ a ; b ; c ] ++ l' ++ d :: l).
Proof.
Admitted.

Goal forall A (x a b c d : A) l l',
  In x l ->
  In x (l ++ [ a ; b ; c ] ++ l' ++ [ d ]).
Proof.
Admitted.

(** EXERCISE

  What if the element in my list is not syntactically what I'm looking for
  but only equal to it?

  Prove a lemma for this particular case and add a hint for it.
  It should solve the following goal.

**)

Goal forall A (x y a b c d : A) l l',
  x = y ->
  In x ([ a ; b ; c ] ++ l' ++ d :: y :: l).
Proof.
Admitted.

(** EXERCISE

  This equality is not always going to be an assumption in the context.
  But it could be handled by some more automation.
  There is for instance the arith database that can deal with arithmetic.

  You can give two (or more) databases to auto. Check that it indeed succeeds
  in the following goal with arith but not without.

**)

Goal forall (a b c d : nat) l l',
  In (a + b) ([ b ; c ] ++ l' ++ d :: (b + a) :: l).
Proof.
Admitted.

(** EXERCISE

  Sadly, it has its limits, check that it isn't sufficient for the following
  goal even though you should be able to prove it (do it).

  Hint: lia is stronger than auto with arith on that one.

**)

Goal forall (a b c d : nat) l l',
  In (a + b + c) ([ a ; b ; c ] ++ l' ++ d :: (c + 0 + a + b) :: l).
Proof.
Admitted.

(** ADVANCED EXERCISE (But more regular exercises afterwards.)

  There is a way to use lia with auto actually. For this we have to provide
  a different kind of hint.
  Using the command Hint Extern we can tell Coq what tactic to try when
  encountering a goal of the form n = m where n, m : nat.

  Below what we do is say that when the goal is of the shape @eq nat _ _
  then we apply lia. We add this to indb.
  The 3 is something called cost. auto is acutally cost-based and each action
  it takes has a cost attached to it. auto will start by picking the actions
  with the lowest cost when it has a choice. When it runs out of money, it
  gives up.

  Check that you can solve the previous goal using auto with indb.
  Can you also make it so that the other goal works?

**)

#[export] Hint Extern 3 (@eq nat _ _) => lia : indb.

Goal forall (a b c d : nat) l l',
  In (a + b + c) ([ a ; b ; c ] ++ l' ++ d :: (c + 0 + a + b) :: l).
Proof.
  auto with indb.
Admitted.

Goal forall (a b c d : Z) l l',
  In (a + b + c)%Z ([ a ; b ; c ] ++ l' ++ d :: (c + d + 0 + a - d + b) :: l)%Z.
Proof.
  auto with indb.
Admitted.

(** Existential variables

  We have hinted at eapply already. But many tactics come with an e version.
  One such example is the eexists tactic that is very convenient. See below.

**)

Goal forall n, n = 0 \/ exists m, n = S m.
Proof.
  intro n.
  destruct n.
  - auto.
  - right. eexists. reflexivity.
  (* We're going to show the proof to see what auto picked for a value *)
  Show Proof.
Qed.

(** EXERCISE

  Solve the following goal without using any lemma or variable in the context
  explicitly.

**)

Goal forall A (x : A) l l',
  exists y, In y (l ++ x :: l').
Proof.
Admitted.

(** auto also has an eauto variant. You can use it to deal with quantifiers.
    It is generally slower than auto so you can use it when auto fails.
**)

Goal forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  P 4 2 ->
  (forall x y, P x y -> Q x) ->
  Q 4.
Proof.
  intros P Q hP h.
  apply h with (y := 2). assumption.
Restart.
  intros P Q hP h.
  eapply h.
  eassumption. (* Notice how we need the e here too! *)
Restart.
  eauto.
Qed.

(** EXERCISE

  Solve the following goal.

**)

Goal forall A (P : A -> A -> Prop) (Q : A -> Prop),
  (forall x, exists y, P x y) ->
  (forall x y, P x y -> Q x) ->
  (forall x, Q x).
Proof.
Admitted.

(** ADVANCED: SETOID REWRITE

  Another interesting feature of Coq is the ability to rewrite on other things
  rather than just equality.

  For instance, we can use rewrite for logical equivalences.
  Let us go through it step by step.

**)

(** EXERCISE

  To begin, prove the following logical equivalences.

**)

Lemma and_AA :
  forall A, A /\ A <-> A.
Proof.
Admitted.

Lemma or_AA :
  forall A, A \/ A <-> A.
Proof.
Admitted.

Lemma and_com :
  forall A B,
    A /\ B <-> B /\ A.
Proof.
Admitted.

Lemma or_com :
  forall A B,
    A \/ B <-> B \/ A.
Proof.
Admitted.

Lemma and_assoc :
  forall A B C,
    (A /\ B) /\ C <-> A /\ B /\ C.
Proof.
Admitted.

(** EXERCISE

  Now you can solve the following goals just by using rewrite on equivalences.
  No more need for split!

  Note that you can also use reflexivity, symmetry and transitivity on those.
  Under the hood, this is using class resolution to find the proper instances.
  For iff (logical equivalence) they are already registered so we can freely
  use them.

**)

Goal forall (A B C D : Prop),
  A /\ (B /\ B) /\ (C -> D) /\ (C -> D) <-> A /\ B /\ (C -> D).
Proof.
Admitted.

Goal forall (A B : Prop),
  (B /\ A /\ B) \/ (A /\ B) <-> B /\ A.
Proof.
Admitted.

(** EXERCISE

  Ok, this is getting old. We're going to switch to another relation which isn't
  already registered in the standard library.
  First we're going to introduce a relation on lists that relates two lists
  if they have the same elements (regardless of how many times they appear),
  ie if they represent the same set.

  Complete the following definition.

**)

Definition list_set_eq {A} (u v : list A) : Prop :=
  REPLACE_ME.

Notation "u ~ v" := (list_set_eq u v) (at level 70).

(** EXERCISE

  We first need to show that the relation is reflexive, symmetric and
  transitive. We do so by instantiating the right classes so that we can use
  the corresponding tactics (as for iff).

  Check it works with the provided goal.

**)

From Coq Require Import Setoid.

#[export] Instance list_set_eq_refl :
  forall A, Reflexive (list_set_eq (A := A)).
Proof.
Admitted.

#[export] Instance list_set_eq_sym :
  forall A, Symmetric (list_set_eq (A := A)).
Proof.
Admitted.

#[export] Instance list_set_eq_trans :
  forall A, Transitive (list_set_eq (A := A)).
Proof.
Admitted.

Goal forall A (u v w : list A),
  v ~ u ->
  (u ~ u -> v ~ w) ->
  u ~ w.
Proof.
Admitted.

(** EXERCISE

  We will use the following command to register this relation to use with
  rewrite. Coq will find the instances of equivalence relation we provided
  above. Otherwise we could provide them manually.
  Look up the documentation if you want to do that:
  https://coq.inria.fr/refman/addendum/generalized-rewriting.html

  On the left of the colon we give the list of parameters, here there is only
  one which is the type of values. We call it A and we can refer to it after
  the colon.
  The next argument is the type of elements we compare with the relation:
  list A.
  Then we give the relation itself: list_seq_eq.
  Finally we give a name to the setoid relation. This is for Coq internal use.

  Prove the following goal using rewrite. This is just transitivity again but
  this is to show you how it works on a simple example.

**)

Add Parametric Relation A : (list A) list_set_eq as list_set_rel.

Goal forall A (u v w : list A),
  u ~ v ->
  v ~ w ->
  u ~ w.
Proof.
Admitted.

(** EXERCISE

  Prove that u ++ v ~ v ++ u.

**)

(** EXERCISE

  In order to rewrite this relation inside, eg., In, we have to first show that
  In is invariant by ~. In other words that u ~ v implies In x u <-> In x v.
  We can use the following command to declare it. This will in turn let us
  rewrite inside In.

  Prove that we indeed have a morpshim.
  Prove the given goals using rewrite.

**)

Add Parametric Morphism A (x : A) : (In x)
  with signature list_set_eq ==> iff
  as In_morph.
Proof.
Admitted.

Goal forall A (x : A) u v,
  In x (u ++ v) ->
  In x (v ++ u).
Proof.
Admitted.

Goal forall A (x a b c : A) u v,
  In x (u ++ [ a ; b ; c ] ++ x :: v).
Proof.
Admitted.

(** EXERCISE

  Look up the Forall predicate. Show that it is a morphism for list_set_eq.
  Proceed to solve the following goal.

**)

Goal forall u v w,
  let P n := exists m, n = 2 * m in
  Forall P (w ++ u ++ v) ->
  Forall P (u ++ v ++ w).
Proof.
Admitted.
