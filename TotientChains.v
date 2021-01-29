Require Import Lia.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Arith.Compare_dec.

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
  unfold Gcd; split; [> split | idtac]; try lia;
  repeat (((apply Gcd_lt; [> lia | idtac]; simpl) || (apply Gcd_gt; [> lia | idtac]; simpl)));
  apply Gcd_refl.

(*
Ltac solve_notGcd :=
  let H := fresh "H"
  in
  let G := fresh "G"
  in
  intro H; destruct H as (_ & G); inversion G; subst; lia.
*)

Ltac solve_notGcd :=
  let H := fresh "H"
  in
  let H' := fresh "H'"
  in
  let H'' := fresh "H''"
  in
  intro H; destruct H as (_&H');
  repeat (inversion H' as [ | ? ? ? ? H'' | ? ? ? ? H'' ]; subst; try lia; clear H'; rename H'' into H').


Example Gcd_ex1 : Gcd 8 12 4.
Proof. solve_Gcd. Defined.

Lemma Gcd'_sym : forall {x y z},
  Gcd' x y z -> Gcd' y x z.
Proof.
  intros.
  induction H; try (now constructor || easy).
Defined.

Lemma Gcd_sym : forall {x y z},
  Gcd x y z -> Gcd y x z.
Proof.
  intros.
  destruct H. destruct p.
  split; try split; try lia.

  apply Gcd'_sym. assumption.
Defined.

Lemma Gcd_pos : forall {x y z},
  Gcd x y z -> z > 0.
Proof.
  intros.
  destruct H. intuition.
  induction g; try easy.
  apply IHg; lia.
  apply IHg; lia.
Defined.

Theorem Gcd_is_fn : forall x y z z',
  x > 0 -> y > 0 ->
  Gcd x y z ->
  Gcd x y z' ->
  z = z'.
Proof.
  intros.
  destruct H1, H2. intuition.
  dependent induction g0; intros.
  inversion g; subst. reflexivity. lia. lia.
  apply IHg0; try lia.
  destruct g; try lia. assumption.

  apply IHg0; try lia.
  destruct g; try lia. assumption.
Defined.


Inductive Totient' : nat -> nat -> nat -> Type :=
| Totient'_One : forall x, Totient' 1 x 1
| Totient'_Gcd1 : forall d n t,
    Gcd (S d) n 1 -> Totient' d n t -> Totient' (S d) n (S t)
| Totient'_NotGcd1 : forall d n t,
    notT (Gcd (S d) n 1) -> Totient' d n t -> Totient' (S d) n t.

Definition Totient n t := Totient' n n t.


Ltac solveTotient :=
  repeat
    (((apply Totient'_One)
      ||
     (apply Totient'_NotGcd1; [> solve_notGcd | solveTotient])
      ||
     (apply Totient'_Gcd1; [> solve_Gcd | solveTotient]))).


Example Totient_9 : Totient 9 6.
Proof. solveTotient.
(* solveTotient. *)
  apply Totient'_NotGcd1; [> solve_notGcd | idtac].
  apply Totient'_Gcd1; [> solve_Gcd | idtac].
  apply Totient'_Gcd1; [> solve_Gcd | idtac].
  apply Totient'_NotGcd1; [> solve_notGcd | idtac].
  apply Totient'_Gcd1; [> solve_Gcd | idtac].
  apply Totient'_Gcd1; [> solve_Gcd | idtac].
  apply Totient'_NotGcd1; [> solve_notGcd | idtac].
  apply Totient'_Gcd1; [> solve_Gcd | idtac].
  apply Totient'_One.
  apply Totient'_Gcd1; [> solve_Gcd | idtac].

Defined.


Lemma Totient_
