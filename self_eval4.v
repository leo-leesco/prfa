(* Self-evaluation

1) Define a product type prod' : Type -> Type -> Type using records.
2) Prove that forall A B, prod' A B -> A * B and forall A B, A * B -> prod' A B using a proof script or a proof term.
3) Give the type of an induction principle for prod'
4) Prove the induction principle with a proof script or a proof term.

*)

Record prod' A B := pair'
  {
    fst' : A ;
    snd' : B
  }.

Goal forall A B, prod' A B -> prod A B.
Proof.
  exact (fun A B '{| fst' := a ; snd' := b |} => (a, b)).
Defined.

Goal forall A B, prod A B -> prod' A B.
Proof.
  intros A B []. split; assumption.
Defined.

Definition prod'_ind :
  forall A B (P : prod' A B -> Prop),
    (forall a b, P (pair' A B a b)) ->
    forall x : prod' A B, P x.
Proof.
  refine (fun A B P H '(pair' _ _ a b) => H a b).
Qed.
