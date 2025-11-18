Lemma O_neq_1 : O <> 1.
Proof.
  intro.
  change (match 0 with
          | 0 => False
          | _ => True
          end).
          rewrite H.
          split.
Qed.

Definition ptoor (A : Prop) (B : Prop) : A + B -> A \/ B := fun ab =>
  match ab with
  | inl a => or_introl a
  | inr b => or_intror b
  end.

Fail Definition ortop (A : Prop) (B : Prop) : A \/ B -> A + B := fun ab =>
  match ab with
  | or_introl a => inl a
  | or_intror b => inr b
  end. (* not possible because A \/ B does not respect the subsingleton criterion : we cannot destruct the proof of [A \/ B]

          it does not respect the subsingleton criterion because it has two constructors, even though all non-parameter arguments are proofs (because they are in [Prop]).
        *)

Inductive Forall {A : Type} (P : A -> Prop) : list A -> Prop :=
  | Forall_nil : Forall P nil
  | Forall_cons : forall (x : A) (l : list A), P x -> Forall P l -> Forall P (x :: l).

Definition Forall_indp :=
  forall A (P0 : A -> Prop),
  forall P : forall l, Forall P0 l -> Prop,
  (P nil (Forall_nil P0)) ->
  (forall x l px fpl, P l fpl -> P (cons x l) (Forall_cons P0 x l px fpl)) ->
  forall l fpl, P l fpl.

Inductive bintree A :=
  | bt_leaf (a : A)
  | bt_node (a : A) (l r : bintree A).

Fixpoint bt_map {A B} (f : A -> B) (t : bintree A) : bintree B :=
  match t with
    | bt_leaf _ a => bt_leaf _ (f a)
    | bt_node _ a l r => bt_node _ (f a) (bt_map f l) (bt_map f r)
  end.

Lemma bt_map_id A (t : bintree A) :
  bt_map (fun x => x) t = t.
Proof.
induction t as [ a | a l ihl r ihr].
- reflexivity.
- cbn. rewrite ihl.
  (* Goal = assumption + conclusion
     A : Type
     a : A
     l : bintree A
     r : bintree A
     ihl : bt_map (fun x => x) l = l
     ihr : bt_map (fun x => x) r = r
     ---
     bt_node _ (id a) (bt_map id l) (bt_map id r) = bt_node _ a l r
     cbn => bt_node _ a (bt_map id l) (bt_map id r) = bt_node _ a l r
     rewrite ihl => bt_node _ a l (bt_map id r) = bt_node _ a l r
   *)

Abort.

Goal forall A B : Prop, A \/ B -> ((A /\ True) \/ B) \/ False.
exact (
  fun A B ab =>
  or_introl (match ab with
             | or_introl a => or_introl (conj a I)
             | or_intror b => or_intror b
             end)
).
Qed.
