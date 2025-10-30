From Stdlib Require Import List.
Import ListNotations.

From project Require Import ex1.

(* 2.1.a *)
Inductive ndm : list form -> form -> Prop :=
  | assm (A : list form) (s : form) : In s A -> ndm A s
  | impintrom (A : list form) (s t : form) : ndm (s :: A) t -> ndm A (s → t)
  | impelimm (A : list form) (s t : form) : ndm A (s → t) -> ndm A s -> ndm A t.

Notation "A ⊢m s" := (ndm A s) (at level 70).

(* 2.1.b *)
Lemma Weakm A B s :
  A ⊢m s -> incl A B -> B ⊢m s.
Proof.
  intro As. revert B.
  induction As as [ A s H | A s t sAt IH | A s t Ast As IHst IHs]; intros B sub.
  - apply assm. apply sub. assumption.
  - apply impintrom. auto with datatypes.
  - apply impelimm with s; auto.
Qed.

(* 2.1.c *)
Lemma Implication A s :
  A ⊢m s -> A ⊢c s.
Proof.
  induction 1 as [ | | A s t Amst Acst Ams Acs].
  - auto with nddb.
  - auto with nddb.
  - apply (impelim A s t Acst Acs).
Qed.

(* 2.1.d *)
Fixpoint trans s t :=
  match s with
  | bot => t
  | var x => (var x → t) → t
  | s0 → t0 => trans s0 t → trans t0 t
  end.

(* 2.1.e *)
Lemma DNE_Friedman A s t :
A ⊢m (( trans t s ∼> t)∼> t)∼> (trans t s).
