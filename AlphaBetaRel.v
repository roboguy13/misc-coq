(* Based on "\u03b1\u03b2-Relations and the Actual Meaning of \u03b1-Renaming" by Michele Basaldella (2021) *)

Require Import Coq.Program.Equality.

Parameter Name : Type.

Parameter Name_eq_dec : forall (a b : Name), {a = b} + {a <> b}.

Inductive Expr : Type :=
| Var : Name -> Expr
| App : Expr -> Expr -> Expr
| Lam : Name -> Expr -> Expr.

Lemma Expr_eq_dec : forall (a b : Expr), {a = b} + {a <> b}.
Proof. decide equality; apply Name_eq_dec. Defined.

(* Inductive Cofinite : Type := *)

Inductive Beta : Expr -> Expr -> Type :=
| Beta_refl : forall e, Beta e e
| Beta_sym  : forall e1 e2, Beta e1 e2 -> Beta e2 e1
| Beta_trans : forall e1 e2 e3, Beta e1 e2 -> Beta e2 e3 -> Beta e1 e3
| Beta_Lam : forall x a b, Beta (Lam x a) (Lam x b)
| Beta_App : forall a b c d, Beta a b -> Beta c d -> Beta (App a c) (App b d)

| Beta_id : forall x d, Beta (App (Lam x (Var x)) d) d
| Beta_const : forall x y d, x <> y -> Beta (App (Lam x (Var y)) d) (Var y)
| Beta_App_distr : forall x a b d,
    Beta (App (Lam x (App a b)) d)
         (App (App (Lam x a) d) (App (Lam x b) d))
| Beta_dup : forall x a d, Beta (App (Lam x (Lam x a)) d) (Lam x a)
| Beta_Lam_swap : forall x y a d,
    x <> y ->
    Beta (App (Lam y d) (Var x)) d ->
    Beta (App (Lam x (Lam y a)) d)
         (Lam y (App (Lam x a) d)).

Definition Beta_rel (R : Expr -> Expr -> Type) :=
  forall a b,
    Beta a b -> R a b.

Definition Inconsistent_Beta : Expr -> Expr -> Type := fun _ _ => True.

Lemma Inconsistent_Beta_rel : Beta_rel Inconsistent_Beta.
Proof. easy. Defined.

Inductive Subst : Expr -> Name -> Expr -> Expr -> Type :=
| Subst_id : forall d x, Subst d x (Var x) d
| Subst_const : forall d x y, x <> y -> Subst d x (Var y) (Var y)
| Subst_App : forall d x a b rA rB,
    Subst d x a rA ->
    Subst d x b rB ->
    Subst d x (App a b) (App rA rB)
| Subst_Lam1 : forall d x a, Subst d x (Lam x a) (Lam x a)
| Subst_Lam2 : forall d x y a r,
    x <> y ->
    Subst (Var x) y d d ->
    Subst d x a r ->
    Subst d x (Lam y a) r.

Lemma Subst_unique : forall {e d x e' e''},
  Subst d x e e' ->
  Subst d x e e'' ->
  e' = e''.
Proof.
  intro e.
  induction e; intros.
  - case_eq (Name_eq_dec x n); intros.
    + subst.
      inversion X0; inversion X; subst; easy.
    + inversion X0; inversion X; subst; easy.
  - inversion X0; inversion X; subst.
    pose (P := IHe1 d x rA0 rA X3 X1).
    pose (Q := IHe2 d x rB0 rB X4 X2).
    rewrite P. rewrite Q. reflexivity.
  - inversion X0; inversion X; subst; try easy.
    apply (IHe _ _ _ _ X4). assumption.
Defined.

Lemma Subst_dec : forall d x e e',
  ( Subst d x e e' ) + ( notT (Subst d x e e') ).
Proof.
  intros.

  assert (A1 : forall q r, App q r <> q).
    induction q; intros; try easy.
    intro. injection H; intros. subst.
    pose (Q1 := IHq1 q2). easy.

  assert (A2 : forall q r, App r q <> q).
    induction q; intros; try easy.
    intro. injection H; intros. subst.
    pose (Q1 := IHq2 q1). easy. 

  induction e.
  - case_eq (Name_eq_dec x n); intros.

    + subst.
      case_eq (Expr_eq_dec e' d); intros.
      * subst. left. constructor.
      * right. intro X. inversion X; subst; easy.

    + case_eq (Expr_eq_dec e' (Var n)); intros.
      * subst. left. constructor. assumption.
      * right. intro X. inversion X; subst; easy.

  - induction IHe1, IHe2.
    + right. intro X. inversion X; subst.
      pose (P := Subst_unique s X1).
      apply (A2 rB rA). assumption.

    + right. intro X. inversion X; subst.
      pose (P := Subst_unique a X0).

      apply (A1 rA rB). assumption.

    + right. intro X. inversion X; subst.
      pose (P := Subst_unique s X1).
      apply (A2 rB rA). assumption.

    + clear b n. induction e'.
      * right. easy.
      * destruct IHe'1, IHe'2.
        right. intro X.
        inversion X; subst.
        pose (P := Subst_unique X s0).
        pose (Q := A2 e'2 e'1). easy.

        right. intro X.
        inversion X; subst.


Fixpoint Subst_exists d x e {struct e} :
  { e' & Subst d x e e' }.
Proof.
  intros.

  induction e.

  - case_eq (Name_eq_dec x n); intros.
    + subst.
      exists d. constructor.
    + exists (Var n). constructor. assumption.

  - destruct IHe1. destruct IHe2.
    exists (App x0 x1).
    constructor; assumption.

  - destruct IHe.
    case_eq (Name_eq_dec x n); intros.
    + subst.
      exists (Lam n e).
      constructor.

    + exists x0. constructor. assumption.
      destruct (Subst_exists (Var x) n d).

