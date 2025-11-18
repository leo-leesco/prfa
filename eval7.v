Axiom REPLACE_ME : forall {A}, A.
From Stdlib Require Import List.
Import ListNotations.

(*
  For the following inductive types, list the
  - uniform parameters : A
  - non-uniform parameters : x
  - indices : y l false/true
*)

Inductive blurb (A : Type) (x : A) : list A -> bool -> Prop :=
| foo : blurb A x nil false
| bar y l : blurb A y l false -> blurb A x (x :: l) true
| baz y l : blurb A x l true -> blurb A x (y :: l) false.

(*
  Give a proof term for transitivity of Leibniz equality.
*)

Definition lbeq {A} (u v : A) :=
  forall (P : A -> Prop), P u -> P v.

Notation "u == v" := (lbeq u v) (at level 80).

Definition lb_trans {A} {u v w : A} : u == v -> v == w -> u == w :=
  fun uv vw P Pu =>
  vw P (uv P Pu).


(*
  Prove the following.
*)

Definition distinct A := exists (x : A) (y : A), x <> y.

Goal list False <> list nat.
Proof.
  assert (dist : distinct (list nat)). {
    exists [], [0].
    intro.
    change (match [0] with
            | [0] => False
            | _ => True
            end).
            rewrite <- H.
            split.
  }
  assert (notdist : ~ distinct (list False)). {
    intro.
    destruct H as (x & y & neq).
    apply neq.
    destruct x.
    - destruct y.
      + reflexivity.
      + contradiction.
    - contradiction.
  }

  intro.
  apply notdist.
  rewrite H.
  assumption.
Qed.

(*
  Show that PropExt implies proof irrelevance.
*)

Definition PropExt :=
  forall (P Q : Prop), (P <-> Q) -> P = Q.

Definition ProofIrrelevance :=
  forall (P : Prop) (p q : P), p = q.

Set Printing Universes.

Goal PropExt -> ProofIrrelevance.
Proof.
  repeat intro.
  assert (h : P = True). {
    apply H.
    split.
    - split.
    - intro. assumption.
  }
  subst.
  destruct p.
  destruct q.
  reflexivity.
Qed.
