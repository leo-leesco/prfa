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

(* 2.1.h *)
Lemma consistence_equiv :
  [] ⊢m bot <-> [] ⊢c bot.
Proof.
  apply ground_truths.
  split.
Qed.

(* 2.1.i *)
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

(* 2.2.a *)
Class WModel := {
  W : Type ;
  rel : W -> W -> Prop ;
  interp : W -> form -> Prop ;
  abs : W -> Prop ;

  reflexive : forall w, rel w w ;
  transitive : forall w1 w2 w3, rel w1 w2 -> rel w2 w3 -> rel w1 w3 ;
  abs_higher : forall w w', rel w w' -> abs w -> abs w' ;
  var_higher : forall w w' s, rel w w' -> interp w s -> interp w' s ;
}.

Notation "w '<=(' M ) w'" := (@rel M w w') (at level 40, w' at next level).

(* 2.2.b *)
Fixpoint winterp : forall M : WModel, W -> form -> Prop :=
  fun M w s => match s with
             | var _ => interp w s
             | bot => abs w
             | s → t => forall w', w <=(M) w' /\ winterp M w' s -> winterp M w' t
             end.

(* Fixpoint winterp : forall M : WModel, W -> form -> Prop. *)
(* Proof. *)
(*   intros ? w s. *)
(*   destruct s as [ x | | s t]. *)
(*   - exact (interp w (var x)). *)
(*   - exact (abs w). *)
(*   - exact (forall w', w <=(M) w' /\ winterp M w' s -> winterp M w' t). *)
(* Defined. *)

(* 2.2.c *)
Fixpoint ctx_winterp : forall M : WModel, W -> list form -> Prop :=
  fun M w A => match A with
               | [] => True
               | s :: A => winterp M w s /\ ctx_winterp M w A
               end.

(* 2.2.d *)
Lemma monotonicity M s w w':
  w <=(M) w' -> winterp M w s -> winterp M w' s.
Proof.
  intros wsubw' Mws.
  induction s as [| | s IHs t IHt]; simpl in *.
  - eapply var_higher; eauto.
  - eapply abs_higher; eauto.
  - intros w0 [ wsubw0 Mw0s].
    apply Mws. split.
    + apply transitive with (w2 := w'); auto.
    + auto.
Qed.

(* 2.2.e *)
Lemma ctx_monotonicity M A w w':
  w <=(M) w' -> ctx_winterp M w A -> ctx_winterp M w' A.
Proof.
  intros. induction A.
  - trivial.
  - simpl in *.
    intuition.
    eapply monotonicity; eauto.
Qed.

(* 2.2.f *)
Lemma wsoundness M A s:
  A ⊢m s -> forall w, ctx_winterp M w A -> winterp M w s.
Proof.
  intros As.
  induction As as [ A s H | A s t sAt IH | A s t Ast As IHst IHs ]
      ; intros w MA.
  - induction A as [| t A IH].
    + simpl in H. tauto.
    + destruct H; simpl in MA.
      * rewrite H in MA. tauto.
      * apply IH.
        ** assumption.
        ** tauto.
  - simpl. intros w' [ww' Ms].
    apply IH. split.
    + assumption.
    + eapply ctx_monotonicity.
      * apply ww'.
      * assumption.
  - simpl in *.
    eapply As; eauto.
    split.
    + apply reflexive.
    + auto.
Qed.

(* 2.2.g *)
#[refine] Instance consistency_model : WModel := {|
  W := unit;
  rel := fun w w' => w = w';
  abs := fun w => False;
  interp := fun w s => True;
|}.
Proof.
  - trivial.
  - intuition. rewrite H. assumption.
  - trivial.
  - trivial.
Defined.

(* 2.2.h *)
Lemma consistency :
  ~([] ⊢m bot).
Proof.
  intro H.
  apply wsoundness with (M := consistency_model) (w := tt) in H.
  - assumption.
  - split.
Qed.

(* 2.2.i *)
#[export, refine] Instance notdne_model : WModel := {|
  W := bool;
  rel := Bool.le;
  abs := fun w => False;
  interp := fun w s => is_true w;
|}.
Proof.
  - destruct w; simpl; reflexivity.
  - intros. destruct w3; simpl in *.
    + destruct w1; reflexivity.
    + destruct w2; simpl in *.
      * discriminate.
      * assumption.
  - trivial.
  - intros. destruct w'.
    + reflexivity.
    + simpl in *. destruct w; simpl in *; assumption.
Defined.

Goal false <=(notdne_model) true.
Proof.
  simpl.
  auto.
Qed.

Lemma true_false : ~ is_true false.
Proof.
  intro.
  unfold is_true in *.
  discriminate.
Qed.

Lemma true_true : is_true true.
Proof.
  reflexivity.
Qed.

(* 2.2.j *)
Lemma dne_independent :
  ~(forall s, [] ⊢m dne s).
Proof.
  intro H.
  apply wsoundness with (M := notdne_model) (w := false) (s := dne (var 0)) in H; simpl in *.
  - apply true_false.
    apply (H false).
    split.
    + constructor.
    + intros w' [l imp].
      * apply (imp true).
        split.
        ** destruct w'; reflexivity.
        ** reflexivity.
  - constructor.
Qed.

(* 2.3.a *)
#[export, refine] Instance syntactic_model : WModel := {|
  W := list form;
  rel := @incl form ;
  abs := fun A => A ⊢m bot;
  interp := fun A s => A ⊢m s;
|}.
Proof.
  - unfold incl in *. auto.
  - unfold incl in *. auto.
  - intros. eapply Weakm; eauto.
  - intros. eapply Weakm; eauto.
Defined.

(* 2.3.b *)
Lemma correctness A s :
  winterp syntactic_model A s <-> A ⊢m s.
Proof.
  revert A. induction s; split; simpl in *; auto.
  - intros.
    apply impintro.
    apply IHs2.
    apply H.
    split.
    + auto with datatypes.
    + apply IHs1.
      auto with mddb datatypes.
  - intros.
    destruct H0 as [Asubw' w's1].
    apply IHs2.
    apply impelim with (s := s1).
    + apply Weakm with (A := A); assumption.
    + apply IHs1. assumption.
Qed.

(* thanks to Virgile Marionneau on this one, I did not think that was the way to go, but he pushed me in the correct direction + gave me some advice on how to solve the goal *)
Lemma Weak_ctx_syntactic A:
   ctx_winterp syntactic_model A A.
Proof.
  induction A.
  - constructor.
  - simpl.
    split.
    + apply correctness.
      auto with mddb datatypes.
    + apply ctx_monotonicity with (w := A).
      * simpl. auto with datatypes.
      * assumption.
Qed.

(* 2.3.c *)
Lemma completeness A s :
  (forall M w, ctx_winterp M w A -> winterp M w s) -> A ⊢m s.
Proof.
  induction A; intros; simpl.
  - apply correctness.
    apply H.
    simpl.
    split.
  - apply correctness.
    apply H.
    split.
    + apply correctness.
      auto with mddb datatypes.
    + apply ctx_monotonicity with (w := A).
      * simpl. auto with datatypes.
      * apply Weak_ctx_syntactic.
Qed.
