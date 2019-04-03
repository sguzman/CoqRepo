(* Inductive nat : Set := 0 : nat | S : nat -> nat. *)


Fixpoint add (a b : nat) : nat :=
  match a with
    | 0 => b
    | S n => S (add n b)
  end.


Theorem add_assoc : forall (a b c : nat),
  (add a (add b c)) = (add (add a b) c).

Proof.
intros a b c.
induction a. simpl. reflexivity.
simpl. rewrite -> IHa. reflexivity.
Qed.

Print add_assoc.