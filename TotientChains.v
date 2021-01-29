Require Import Lia.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Program.Wf.

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

Theorem Gcd_is_fn : forall {x y z z'},
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

(*Inductive Gcd' : nat -> nat -> nat -> Type :=
| Gcd_refl : forall a, Gcd' a a a
| Gcd_gt : forall a b x, a > b -> Gcd' (a - b) b x -> Gcd' a b x
| Gcd_lt : forall a b x, a < b -> Gcd' a (b - a) x -> Gcd' a b x.*)

Program Fixpoint Gcd'_exists x y {measure (x+y)} :
  ({z & Gcd' x y z} + (x = 0) + (y = 0)) :=
  match x, y with
  | O, _ => _
  | _, O => _
  | S x', S y' => _
  end.
Next Obligation. left. right. reflexivity. Defined.
Next Obligation. right. reflexivity. Defined.
Next Obligation.
  destruct (lt_dec (S x') (S y')).
  - destruct (Gcd'_exists (S x') (S y' - S x')); try lia.
    destruct s; try lia. destruct s.
    left. left.
    exists x.
    apply Gcd_lt. assumption. assumption.

  - destruct (Nat.eq_dec (S x') (S y')). left. left. rewrite e. exists (S y'). constructor.

    destruct (Gcd'_exists (S x' - S y') (S y')); try lia.
    destruct s. destruct s. left. left.
    exists x. apply Gcd_gt; try lia. assumption.

    lia.
Defined.

Theorem Gcd_exists : forall x y,
  x > 0 -> y > 0 ->
  {z & Gcd x y z}.
Proof.
  intros.
  destruct (Gcd'_exists x y).
  destruct s. destruct s. exists x0.
  split; try split; try assumption. lia. lia.
Defined.

Theorem Gcd1_dec : forall x y,
  (Gcd x y 1) + notT (Gcd x y 1).
Proof.
  intros.
  destruct x, y; try (right; intro; destruct H; intuition; lia).
  destruct (Gcd_exists (S x) (S y)); try lia.
  destruct (Nat.eq_dec x0 1).
  left. subst. assumption.
  right. intro.
  assert (A0 : S x > 0). lia.
  assert (A1 : S y > 0). lia.
  pose (P := Gcd_is_fn A0 A1 g H).
  lia.
Defined.


Inductive Totient' : nat -> nat -> nat -> Type :=
| Totient'_One : forall x, Totient' 1 x 1
| Totient'_Gcd1 : forall d n t,
    Gcd (S d) n 1 -> Totient' d n t -> Totient' (S d) n (S t)
| Totient'_NotGcd1 : forall d n t,
    notT (Gcd (S d) n 1) -> Totient' d n t -> Totient' (S d) n t.

Definition Totient n t := Totient' n n t.

(*
Fixpoint totient (d n : nat) : nat.
Proof.
  Check wf.
*)

(*
Ltac solveTotient :=
  repeat
    ((apply Totient'_NotGcd1; [> solve_notGcd | idtac])
      ||
     (apply Totient'_Gcd1; [> solve_Gcd | idtac])); apply Totient'_One.
*)

Ltac contradictT H := unfold notT in H; contradict H.

Ltac solveTotient :=
  let H := fresh "H"
  in
  match goal with
  | [ |- Totient ?X ?Y ] =>
      destruct (Gcd1_dec X Y) as [H |];
        [> try (apply Totient'_Gcd1; [> (try solve_Gcd; try (contradictT H; solve_notGcd)) | idtac])
         | try (apply Totient'_NotGcd1; [> (try solve_notGcd; try (contradictT H; solve_Gcd)) | idtac])]
  end.

Example Totient_9 : Totient 9 6.
Proof. solveTotient. contradict H. solve_notGcd.  solveTotient.
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
Defined.


Lemma Totient_
