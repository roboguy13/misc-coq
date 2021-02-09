Require Import Lia.

Definition optionS (n : option nat) : option nat :=
  match n with
  | None => Some O
  | Some n => Some (n+1)
  end.

Inductive Env' : nat -> Type :=
| Env_One : bool -> Env' 1
| Env_Cons : forall n, bool -> Env' n -> Env' (S n).

Definition Env x : Type := (x = 0) + (Env' x).


Inductive Lookup : forall x y, (y <= x) -> Env x -> bool -> Prop :=
| Lookup_Here : forall x (prf : S x <= S x) e b, Lookup (S x) (S x) prf (inr (Env_Cons x b e)) b
| Lookup_There : forall x y prf1 prf2 e b b',
    Lookup x y prf1 (inr e) b ->
    Lookup (S x) y prf2 (inr (Env_Cons _ b' e)) b.

(* | Lookup_There : forall x y prf1 prf2 (e : Env (S x)) b b',
    Lookup x y prf1 e b ->
    Lookup (S (S x)) y prf2 (Env_Cons (S (S x)) b' e) b. *)

Inductive SatProp : nat -> Type :=
| SatProp_Lit : bool -> SatProp 0
| SatProp_Var : forall n, SatProp (S n)
| SatProp_And : forall a b, SatProp a -> SatProp b -> SatProp (max a b)
| SatProp_Or : forall a b, SatProp a -> SatProp b -> SatProp (max a b)
| SatProp_Not : forall n, SatProp n -> SatProp n.

Lemma max_le : forall {y1 y2 x},
  y1 <= x ->
  y2 <= x ->
  Nat.max y1 y2 <= x.
Proof. lia. Defined.

Inductive Eval : forall x y, (y <= x) -> Env x -> SatProp y -> bool -> Prop :=
| Eval_Lit : forall x prf e b, Eval x 0 prf e (SatProp_Lit b) b

| Eval_Var : forall x y prf1 prf2 e b, Lookup x _ prf1 e b -> Eval (S x) (S y) prf2 e (SatProp_Var y) b

| Eval_And : forall x y1 y2 prf1 prf2 e b1 b2 p q,
    Eval x y1 prf1 e p b1 ->
    Eval x y2 prf2 e q b2 ->
    Eval x (max y1 y2) (max_le prf1 prf2) e (SatProp_And _ _ p q) (andb b1 b2)

| Eval_Or : forall x y1 y2 prf1 prf2 e b1 b2 p q,
    Eval x y1 prf1 e p b1 ->
    Eval x y2 prf2 e q b2 ->
    Eval x (max y1 y2) (max_le prf1 prf2) e (SatProp_Or _ _ p q) (orb b1 b2)

| Eval_Not : forall x y prf e b p,
    Eval x y prf e p b ->
    Eval x y prf e (SatProp_Not _ p) (negb b).

Theorem Lookup_exists : forall x y e prf, {b & Lookup x y prf e b}.
Proof.
  dependent induction e; intros.
  destruct (Nat.eq_dec (S x) y).
  subst.
  exists b.
  apply Lookup_Here.
  exists b.
  destruct x.
  apply Lookup_There.



Theorem Eval_exists : forall x y (prf : y <= x) e p,
  {b : bool & Eval x y prf e p b}.
Proof.
  intros.
  induction p eqn:E.
  - exists b. constructor.
  - 
