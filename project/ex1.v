From Stdlib Require Import List.
Import ListNotations.

(* 1.1 *)
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

Create HintDb datatypes.

Lemma In_hd {A : Type} (x : A) (l : list A):
    In x (x :: l).
Proof.
  intros. simpl. auto.
Qed.

(* 1.1.b.1 *)
Lemma imp_tauto (A : list form) (s : form) : A ⊢c s → s.
Proof.
  apply impintro.
  apply ass.
  auto with datatypes.
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


(* 1.1.b.2 *)
Lemma neg_sat (A : list form) (s : form) : s :: A ⊢c neg (neg s).
Proof.
  apply impintro.
  apply impelim with s; auto with datatypes nddb.
Qed.

(* 1.1.b.3 *)
Lemma dne_simpl : [neg (neg bot)] ⊢c bot.
Proof.
  apply contr.
  apply impelim with (s := neg bot) (t:= bot); auto with datatypes nddb.
Restart.
  apply impelim with (s := neg bot) (t := bot).
  - auto with datatypes nddb.
  - apply imp_tauto.
Qed.

(* 1.1.b.4 *)
Lemma dne (A : list form) (s : form) : A ⊢c (neg (neg s)) → s.
Proof.
  apply impintro.
  apply contr.
  apply impelim with (s := neg s); auto with datatypes nddb.
Qed.

Lemma empty_subset {T : Type} (A : list T) : incl A [] <-> A = [].
Proof.
  split; intros.
  - induction A as [| x A IH].
    + reflexivity.
    + unfold incl in *.
      simpl in *.
      exfalso.
      apply H with x.
      auto.
  - rewrite H. unfold incl. auto.
Qed.

Lemma concat_sub {T : Type} (A B : list T) (x : T) : incl A B -> incl (x :: A) (x :: B).
Proof.
  intro inAB.
  unfold incl.
  intros a H. destruct H.
  + rewrite H. auto with datatypes.
  + auto with datatypes.
Qed.

(* 1.1.c *)
Fact Weakc A B s :
  A ⊢c s -> incl A B -> B ⊢c s.
Proof.
  intros H AsubB.
  induction B.
  - apply empty_subset in AsubB.
    rewrite AsubB in H. assumption.
  - unfold incl in *.
Restart.
  intro As. revert B.
  induction As as [ A s H | A s t sAt IH | A s t Ast As IHst IHs | A s As IH]; intros B sub.
  - apply ass. apply sub. assumption.
  - apply impintro. auto with datatypes.
  - apply impelim with s; auto.
  - apply contr. auto with datatypes.
Qed.

(* 1.1.d *)
Fixpoint ground s : Prop :=
  match s with
  | var x => False
  | s → t => ground s /\ ground t
  | bot => True
  end.

(* 1.2 *)

Definition Model := nat -> Prop.

(* 1.2.a *)
Fixpoint interp (M : Model) (s : form) : Prop :=
  match s with
  | bot => False
  | s → t => interp M s -> interp M t
  | var x => M x
  end.

(* 1.2.b *)
Fixpoint ctx_interp (M : Model) (A : list form) : Prop :=
  match A with
  | [] => True
  | s :: A => interp M s /\ ctx_interp M A
  end.

Lemma soundness M A (s : form) :
(forall P, (not (not P)) -> P) ->
A ⊢c s -> ctx_interp M A -> interp M s.
Proof.
  intros dne As MA.
  induction As as [ A s H | A s t sAt IH | A s t Ast As IHst IHs | A s As IH].
  - 
