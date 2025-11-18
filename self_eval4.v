(* Self-evaluation

1) Define a product type prod' : Type -> Type -> Type using records.
2) Prove that forall A B, prod' A B -> A * B and forall A B, A * B -> prod' A B using a proof script or a proof term.
3) Give the type of an induction principle for prod'
4) Prove the induction principle with a proof script or a proof term.

*)

Record prod' A B: Type :=
  {
    fst' : A ;
    snd' : B
  }.

Goal forall A B, prod' A B -> prod A B.
Proof.
  intros ?? [a b].
  split; assumption.
Defined.

Goal forall A B, prod A B -> prod' A B.
Proof.
  intros ?? [a b].
  split; assumption.
Defined.

Definition prod'_ind :
  forall A B, forall P : prod' A B -> Prop,
  (forall a b, P {| fst' := a; snd' := b |}) ->
  forall p, P p.
Proof.
  intros.
  destruct p.
  apply H.
Qed.
