Goal forall X Y : Prop, X -> Y -> X.

Proof.
  intros X Y.
  exact (fun A B => A).
Qed.

Goal forall X Y Z : Prop,
  (X -> Y) -> (Y -> Z) -> (X -> Z).
Proof.
  exact (fun X Y Z A B C => B (A C)).
Qed.