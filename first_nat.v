Module Test1.

Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat
.

Check Nat.

Definition suc (n : Nat) : Nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Check suc.
Check (S (S (S (S O)))).

Fixpoint add (n : Nat) (m : Nat) : Nat :=
  match n with
    | O => m
    | S n' => S (add n' m)
  end.

Eval compute in (add (S (S (S O))) (S (S O))).

Fixpoint EvenQ (n : Nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => EvenQ n'
  end.

Eval compute in (add (S (S (S O))) (S (S O))).
Eval compute in (EvenQ (S (S O))).
Eval compute in (EvenQ (S (S (S O)))).

End Test1.