(** * Self-evaluation week 1  *)

(* Write down the goal at the annotated points.
   Goals have the shape

   h1 : P1
   h2 : P2
   ...
   ---------
   G

*)

Lemma test1 (P Q : Prop) : P \/ Q -> Q \/ P.
Proof.
  intros h.
  destruct h as [h | h].
  - left.
    (*
       h : P
       ---
       Q
     *)
Abort.

Lemma test2 (P Q : Prop) : ~~ P -> (P -> ~ Q) -> ~ Q.
Proof.
  intros h1 h2 h3.
  apply h1. intros h4.
  (*
     h1 : ~ ~ P
     h2 : P -> ~ Q
     h3 : Q
     h4 : P
     ---
     False

   *)
Abort.

Lemma test3 (n : nat) : n = 42.
Proof.
  induction n as [ | n' IH].
  - (*
       ---
       0 = 42
    *)
  - (*
       n' : nat
       IH : n' = 42
       ---
       S n' = 42
     *)
Abort.

(* Ex 5: what tactics solve test2? [tauto] *)
