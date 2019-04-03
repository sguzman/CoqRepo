(* Theorem is (A -> B) -> (A -> B) *)

Theorem implies_reflex : (forall A B : Prop, (A -> B) -> (A -> B)).
Proof.
  intros A.
  intros B.
  intros A_implies_B.
  exact A_implies_B.
Qed.