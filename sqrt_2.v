Require Import Arith.Even.
Require Import Omega.

Check Nat.even.

Lemma two_times_x_is_even : forall x : nat,
  Nat.even (2 * x) = true.
Proof.
  simpl.
  induction x.
  - simpl.
    reflexivity.
  - rewrite Nat.add_0_r.
    rewrite Nat.add_0_r in IHx.
    replace (S x + S x) with (S (S (x + x))).
    + simpl.
      apply IHx.
    + simpl.
      rewrite (Nat.add_comm x (S x)).
      simpl.
      reflexivity.
Qed.

Lemma square_even_is_even: forall x: nat,
  Nat.even (x * x) = true -> Nat.even x = true.
Proof.
  simpl.

Theorem sqrt2_is_irrational : forall p q : nat,
  p * p <> 2 * q * q.

Proof.
  intros.
  unfold not.
  intros eq.
  assert (Nat.even (p * p) = true).
  {
    rewrite -> eq.
    rewrite <- Nat.mul_assoc.
    apply two_times_x_is_even.
  }

  Set Printing All.