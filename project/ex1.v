From Stdlib Require Import List.
Import ListNotations.

Inductive form : Type :=
  | var (x : nat)
  | bot
  | imp (s t : form).

Print In.
Print incl.

Notation "s → t" := (imp s t) (at level 51, right associativity).
Notation neg s := (imp s bot).
Reserved Notation "A ⊢c s" (at level 70).

(* 1.1.a *)
Inductive ndc : list form -> form -> Prop :=
  | ass (A : list form) (s : form) : In s A -> ndc A s
  | impintro (A : list form) (s t : form) : ndc (s :: A) t -> ndc A (s → t)
  | impelim (A : list form) (s t : form) : ndc A (s → t) -> ndc A s -> ndc A t
  | contr (A : list form) (s : form) : ndc (neg s :: A) bot -> ndc A s.

Notation "A ⊢c s" := (ndc A s).

Create HintDb nddb.
#[export] Hint Constructors ndc : nddb.

Create HintDb listdb.

Lemma In_hd {A : Type} (x : A) (l : list A):
    In x (x :: l).
Proof.
  intros. simpl. auto.
Qed.

#[export] Hint Resolve In_hd : listdb.

(* 1.1.b.1 *)
Lemma imp_tauto (A : list form) (s : form) : A ⊢c s → s.
Proof.
  apply impintro.
  apply ass.
  auto with listdb.
  (* firstorder. (* would have also worked *) *)
Qed.

#[export] Hint Resolve imp_tauto : nddb.

Lemma In_tl :
  forall A (x y : A) l,
    In x l ->
    In x (y :: l).
Proof.
  intros. simpl. auto.
Qed.

#[export] Hint Resolve In_tl : listdb.

(* 1.1.b.2 *)
Lemma neg_sat (A : list form) (s : form) : s :: A ⊢c neg (neg s).
Proof.
  apply impintro.
  apply impelim with s; auto with listdb nddb.
Qed.

(* 1.1.b.3 : by structural induction on the goal, we can only apply :
   - assumption
     we cannot apply assumption because the hypothesis is not satisfied
   - implication elimination
   if we try to use implication elimination, we end up proving 
   - contradiction



*)
Lemma dne_simpl : [neg (neg bot)] ⊢c bot.
Proof.
  apply contr. 
