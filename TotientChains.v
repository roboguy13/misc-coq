Require Import Lia.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Program.Wf.
Require Import Ring.
Require Import NArithRing.
Require Import NArith.
Require ArithRing.

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
| Totient'_One : forall x, Totient' 1 (S x) 1
| Totient'_Gcd1 : forall d n t,
    Gcd (S d) n 1 -> Totient' d n t -> Totient' (S d) n (S t)
| Totient'_NotGcd1 : forall d n t,
    notT (Gcd (S d) n 1) -> Totient' d n t -> Totient' (S d) n t.

Definition Totient n t := Totient' n n t.

Ltac contradictT H := unfold notT in H; contradict H.

Ltac solveTotient :=
  repeat ((apply Totient'_One) ||
          (apply Totient'_Gcd1; [> solve_Gcd | idtac]) ||
          (apply Totient'_NotGcd1; [> solve_notGcd | idtac])).

Example Totient_9 : Totient 9 6.
Proof. solveTotient. Defined.

Lemma Totient_pos : forall {x y z}, Totient' x y z -> z > 0.
Proof.
  intros.
  induction H; lia.
Defined.

Lemma Totient_unique : forall s s' x y z,
  Totient' (S s) x y -> Totient' (S s') x z -> z = y.
Proof.
  dependent induction s using (well_founded_induction lt_wf); intros.
  destruct s.
  inversion H1; subst. inversion H0; subst; try easy.

  inversion H0; subst; try easy.


  pose (P := H _ _ _ _ _ _ H0 H1).



  induction s, s'; intros.

  inversion H; subst.


  dependent induction s' using (well_founded_induction lt_wf); intros.
  destruct s'. inversion H1.

  inversion H0; subst.
  inversion H1; subst; try easy.
  assert (A0 : s' < S s'). lia.
  pose (P := H _ A0 _ _ _ H0 H4).




  dependent induction s using (well_founded_induction lt_wf); intros.
  destruct s. inversion H0.

  inversion H0; subst.
  destruct s'. inversion H1.
  pose (P := H _ _ _ _ _ _ H1 H0).

  inversion H0; subst.
  inversion H1; subst; try easy.

  inversion H1; subst. inversion H4.
  assert (A0 : x < S x). lia.
  pose (P := H x A0 (S x) t0).


Lemma Totient_exists : forall x, x > 0 -> { y & Totient x y }.
Proof.
  intros.

  induction x using (well_founded_induction lt_wf).
  dependent induction x. lia.


  assert (A0 : forall y, y < x -> y > 0 -> {y0 & Totient y y0}). intros. apply H0; lia.

  destruct x.

  exists 1. solveTotient.

  destruct IHx; try easy. lia.

  destruct (Gcd1_dec (S x) (S (S x))).
  exists (S x0).
  apply Totient'_NotGcd1. solve_notGcd.
  apply Totient'_Gcd1. assumption.

  destruct (H0 (S x)); try lia.




  destruct t.
  inversion t; subst.





  induction x.
  exists 1. constructor.

  destruct IHx. lia.
  inversion t; subst.
  exists 1. solveTotient.

  destruct (Gcd1_dec x (S (S x))).
  exists 









  exists (S (S t0)).

  assert (A0 : x = 0). destruct H1. inversion g; subst; lia.
  subst. inversion H2.

  exists x0.
  unfold Totient.
  apply Totient'_NotGcd1. intro. destruct H0. inversion g; subst; lia.

  destruct x0. inversion H2; subst.

  pose (P := Totient_pos t). lia.

  assert (A0 : x > 0).
    destruct x. contradictT H1. constructor. intuition. constructor. intuition.

  destruct (Gcd1_dec ((S x)) ((S (S x)))).
  apply Totient'_Gcd1. assumption.

  inversion H2; subst.


  inversion t; subst; try lia; try now intuition.






  destruct t.
  destruct x1. constructor.

  inversion H2; subst.




  destruct (Gcd1_dec (S (S x1)) (S (S (S x1)))).
  apply Totient'_Gcd1. assumption.
  
(*
  assert (A1 : x < 3).
    induction x; try lia.
    inversion H2; subst; try lia.
    pose (P := Totient_pos H6); lia.
    destruct x. inversion H4.
    destruct x. lia.

    assert (A1 : S (S x) > 0). lia.
    pose (P := IHx H4 A1).
    assert (A2 : x = 0). lia.
    subst.
    destruct x1.
    contradictT H3. solve_Gcd.

    dependent destruction H4.
    pose (Totient_pos H4); lia.

*)



    inversion H2; subst. intuition.
    inversion H6; subst. intuition.
    inversion H8; subst.






    contradict 
    inversion H6; subst. pose (Totient_pos H10); lia.



    generalize H3.
    dependent induction x1 using (well_founded_induction lt_wf).




 pose (Gcd_sym g). intuition.
    inversion H4; subst. pose (Totient_pos H8). lia.
    destruct H6.

    induction H2; try lia.
    assert (A1' : S x > 0). lia.
    pose (P := IHx H4 A1'). lia.
    



 inversion H2; subst. lia.
    pose (P := Totient_pos H6). lia. inversion H3; subst; try lia.
    pose (P := Totient_pos H8). lia.
    inversion H5; subst; try lia. inversion H3; subst; try lia.
    pose (P := Totient_pos H10). lia.

  apply .


  destruct (Gcd1_dec x1 (S x1)).
  apply Totient'_Gcd1.



  destruct (Gcd1_dec (S x) (S (S x))).
  apply Totient'_Gcd1. assumption.
  destruct H2.
  

  inversion H2; subst.
  inversion t; subst; try lia.



  inversion H2; subst. 

  inversion t; subst; try now inversion H2.

  destruct (Gcd1_dec (S x) (S (S x))).
  apply Totient'_Gcd1. assumption.
(*  inversion t; subst; try now inversion H2. *)
