Require Import Arith String.

(* This is a comment *)

Inductive exp : Set :=
  | Constant : nat -> exp
  | Plus : exp -> exp -> exp
  | Times : exp -> exp -> exp.

Fixpoint eval (e : exp) : nat :=
  match e with
    | Constant n => n
    | Plus e1 e2 => eval e1 + eval e2
    | Times e1 e2 => eval e1 + eval e2
  end.

Fixpoint commuter (e : exp) : exp :=
  match e with
   | Constant _ => e
   | Plus e1 e2 => Plus (commuter e2) (commuter e1)
   | Times e1 e2 => Times (commuter e2) (commuter e1)
  end.

Inductive natural : Set :=
  | Zero : natural
  | Succ : natural -> natural.

Fixpoint add (n m : natural) : natural :=
  match n with
   | Zero => m
   | Succ n' => Succ (add n' m)
  end.

Theorem add_assoc : forall n m o,
  add (add n m) o = add n (add m o).
Proof.
  induction n.
  intros.
  simpl.
  reflexivity.

  intros.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Lemma add_Zero : forall n,
  add n Zero = n.
Proof.
  induction n; simpl.
  reflexivity.

  rewrite IHn.
  reflexivity.
Qed.

Lemma add_Succ  : forall n m,
  add n (Succ m) = Succ (add n m).
Proof.
  induction n; simpl; intros.
  reflexivity.

  rewrite IHn.
  reflexivity.
Qed.

Theorem add_comm : forall n m,
  add n m = add m n.
Proof.
  induction n; intros; simpl.

  rewrite add_Zero.
  reflexivity.
  rewrite IHn.
  rewrite add_Succ.
  reflexivity.
Qed.

Theorem eval_commuter : forall e,
  eval (commuter e) = eval e.
Proof.
  induction e; simpl.
  reflexivity.
  rewrite IHe1, IHe2.
  ring.

  rewrite IHe1, IHe2.
  ring.
Qed.