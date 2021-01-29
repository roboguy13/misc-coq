Require Import Lia.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Wf_nat.

Inductive Parity := Even | Odd.

Inductive EvenOdd : nat -> Parity -> Type :=
| EvenOdd_Z : EvenOdd 0 Even
| EvenOdd_Even : forall n, EvenOdd n Odd -> EvenOdd (S n) Even
| EvenOdd_Odd : forall n, EvenOdd n Even -> EvenOdd (S n) Odd.

Inductive Divides : nat -> nat -> Type :=
| Divides_Refl : forall n, Divides n n
| Divides_Step : forall n n',
    Divides n n' -> Divides n (n' + n).

Inductive Gcd' : nat -> nat -> nat -> Type :=
| Gcd_refl : forall a, Gcd' a a a
| Gcd_gt : forall a b x, a > b -> Gcd' (a - b) b x -> Gcd' a b x
| Gcd_lt : forall a b x, a < b -> Gcd' a (b - a) x -> Gcd' a b x.

Definition Gcd a b x :=
  ((a > 0) * (b > 0) * Gcd' a b x)%type.

Ltac solve_Gcd :=
  let prf1 := fresh "prf1"
  in
  let prf2 := fresh "prf2"
  in
  unfold Gcd; split; try split; try lia;
  repeat (((apply Gcd_lt; [> lia | idtac]; simpl) || (apply Gcd_gt; [> lia | idtac]; simpl)));
  apply Gcd_refl.

Example Gcd_ex1 : Gcd 8 12 4.
Proof. solve_Gcd. Defined.

Lemma Gcd_pos : forall x y z,
  Gcd x y z -> z > 0.
Proof.
  induction x using (well_founded_induction lt_wf).
  intros. destruct x.
  destruct H0. destruct p. lia.

  inversion H0; subst. destruct H1.
  l


  induction x; intros.
  destruct H. destruct p. lia.
  destruct H. inversion g; subst.
  lia.
  destruct p. inversion H0; subst; try lia.
  apply (IHx y).

Theorem Gcd_is_fn : forall x y z z',
  x > 0 -> y > 0 ->
  Gcd x y z ->
  Gcd x y z' ->
  z = z'.
Proof.
  destruct z. intros.


  induction z using (well_founded_induction lt_wf); intros.

  destruct z. destruct z'. easy.
  pose (P := H _ _ _ H0 H1 H2 H3).


  induction z; intros.
  destruct (H2 H H0).
  pose (P := H1 H H). inversion P; subst; try lia.
  pose (P := H1 H H0). inversion P; subst; try lia.
  destruct x. easy.
  inversion g0. subst.
  replace (a - (a - b)) with b in H8 by lia. subst.
  inversion H4; subst; try lia.
  destruct g0; try lia.



Inductive Totient' : nat -> nat -> nat -> Type :=
| Totient'_One : Totient' 1 1 1
| Totient'_Gcd1 : forall d n t,
    Gcd (S d) n 1 -> Totient' d n t -> Totient' (S d) n (S t)
| Totient'_NotGcd1 : forall d n t,
    notT (Gcd (S d) n 1) -> Totient' d n t -> Totient' (S d) n t.

Definition Totient n t := Totient' n n t.


Example Totient_9 : Totient 9 6.
Proof.
  apply Totient'_NotGcd1. intro.
  apply Totient'_Gcd1. solve_Gcd.
  apply Totient 
Defined.


Lemma Totient_
