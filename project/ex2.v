From Stdlib Require Import List.
Import ListNotations.

From project Require Import ex1.

(* 2.1.a *)
Inductive ndm : list form -> form -> Prop :=
  | ass (A : list form) (s : form) : In s A -> ndm A s
  | impintro (A : list form) (s t : form) : ndm (s :: A) t -> ndm A (s → t)
  | impelim (A : list form) (s t : form) : ndm A (s → t) -> ndm A s -> ndm A t.

Notation "A ⊢m s" := (ndm A s) (at level 70).

Create HintDb mddb.
#[export] Hint Constructors ndm : mddb.

(* 2.1.b *)
Lemma Weakm A B s :
  A ⊢m s -> incl A B -> B ⊢m s.
Proof.
  intro As. revert B.
  induction As as [ A s H | A s t sAt IH | A s t Ast As IHst IHs]; intros B sub.
  - apply ass. apply sub. assumption.
  - apply impintro. auto with datatypes.
  - apply impelim with s; auto.
Qed.

#[export] Hint Resolve Weakm : mddb.

(* 2.1.c *)
Lemma Implication A s :
  A ⊢m s -> A ⊢c s.
Proof.
  induction 1 as [ | | A s t Amst Acst Ams Acs].
  - auto with nddb.
  - auto with nddb.
  - apply (ex1.impelim A s t Acst Acs).
Qed.

#[export] Hint Resolve Implication : mddb.

(* 2.1.d *)
Fixpoint trans t s :=
  match s with
  | bot => t
  | var x => (var x → t) → t
  | s0 → t0 => trans t s0 → trans t t0
  end.

(* 2.1.e *)
Lemma DNE_Friedman A s t :
  A ⊢m ((trans t s → t) → t) → (trans t s).
Proof.
  revert t A. induction s as [| | s0 IHs t0 IHt]; intros; simpl.
  - repeat apply impintro.
    apply impelim with (s := (((var x → t) → t) → t)).
    + auto with mddb datatypes.
    + repeat apply impintro.
      apply impelim with (s := (var x → t)); auto with mddb datatypes.
  - repeat apply impintro.
    apply impelim with (s := t → t); auto with mddb datatypes.
  - repeat apply impintro.
    apply impelim with (s := (trans t t0 → t) → t).
    + apply IHt.
    + apply impintro. apply impelim with (s := ((trans t s0 → trans t t0) → t)).
      * auto with mddb datatypes.
      * apply impintro.
        apply impelim with (s := trans t t0).
        ** auto with mddb datatypes.
        ** apply impelim with (s := trans t s0); auto with mddb datatypes.
(* Restart. *)
  (* revert t A. *)
  (* induction s as [| | s0 IHs t0 IHt] *)
  (* ; intros *)
  (* ; simpl *)
  (* ; repeat apply impintro *)
  (* ; eapply impelim *)
  (* ; eauto with mddb datatypes. *)
  (* - apply impelim with (s := (((var x → t) → t) → t)). *)
  (*   + auto with mddb datatypes. *)
  (*   + repeat apply impintro. *)
  (*     eapply impelim; eauto with mddb datatypes. *)
  (* - repeat apply impintro. *)
  (*   apply impelim with (s := (trans t t0 → t) → t). *)
  (*   + apply IHt. *)
  (*   + apply impintro. apply impelim with (s := ((trans t s0 → trans t t0) → t)). *)
  (*     * auto with mddb datatypes. *)
  (*     * apply impintro. *)
  (*       apply impelim with (s := trans t t0). *)
  (*       ** auto with mddb datatypes. *)
  (*       ** apply impelim with (s := trans t s0); auto with mddb datatypes. *)
Qed.

(* 2.1.f *)
Lemma Friedman A s t :
  A ⊢c s -> map (trans t) A ⊢m trans t s.
Proof.
  intro H.
  induction H as [| A s s0 H IH | A s s0 Hss0 IHss0 Hs IHs |]; simpl in *.
  - induction A as [| u A IH].
    + simpl in H. exfalso. assumption.
    + destruct H.
      * rewrite H. simpl. auto with mddb datatypes.
      * specialize (IH H). simpl.
        apply Weakm with (A := map (trans t) A) (B := map (trans t) (u :: A))
        ; auto with mddb datatypes.
  - apply impintro. auto with mddb datatypes.
  - apply impelim with (s := trans t s)
    ; auto with mddb datatypes.
  - apply impelim with (s := (trans t s → t) → t).
    + apply DNE_Friedman.
    + auto with mddb datatypes.
Qed.

(* 2.1.g *)
Lemma ground_truths s :
  ground s -> ([] ⊢m s <-> [] ⊢c s).
Proof.
  intro grnd. split.
  - apply Implication.
  - assert (grd : trans bot s = s). {
    induction s as [| | s1 IHs1 s2 IHs2].
    - inversion grnd.
    - reflexivity.
    - simpl in *. f_equal; tauto.
  }
  intro.
  rewrite <- grd.
  apply Friedman with (A := []).
  assumption.
Qed.

Lemma consistence_equiv :
  [] ⊢m bot <-> [] ⊢c bot.
Proof.
  apply ground_truths.
  split.
Qed.

Definition dne s := ((s → bot) → bot) → s.

Lemma consistency_of_dne s :
  ~([] ⊢m dne s → bot).
Proof.
  intro H.
  apply Implication in H.
  apply constructive_consistency.
  apply ex1.impelim with (s := dne s) in H.
  - assumption.
  - unfold dne.
    apply ex1.dne.
Qed.
