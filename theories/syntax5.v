From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure fsbigop numfun lebesgue_integral kernel.
Require Import prob_lang.

Set Implicit Arguments.
Implicit Types V : Set.
Unset Strict Implicit.
Set Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Require Import String ZArith.
Local Open Scope string.

Import Notations.


Section test.
Variables (R : realType).
Goal ret (R := R) (@measurable_fun_id _ mbool _) true [set: bool] = 1.
Proof.
by rewrite retE diracE in_setT.
Qed.

End test.

Section ttype.
Variables (R : realType).
Inductive ttype : Type := D | P.

Definition ttype_denote (t : ttype) :=
  match t with
  | D => forall dA dB (A : measurableType dA) (B : measurableType dB), {f : A -> B | measurable_fun setT f}
  | P => forall dA dB (A : measurableType dA) (B : measurableType dB), R.-sfker A ~> B
  end.

End ttype.

Section type.
Inductive type : Type :=
| Real | Bool | Unit
.

Definition type_eqb (t t' : type) : bool :=
match t, t' with
| _, _ => true
end.

Definition type_eqb_dec (t t' : type) : {is_true (type_eqb t t')} + {~ is_true (type_eqb t t')}.
destruct (type_eqb t t').
by left. 
by right.
Defined.

(* Variables (R : realType). *)
Fixpoint type_denote {R : realType} (t : type) : Type :=
  match t with
  | Real => R
  | Bool => bool
  | Unit => unit
  end.

End type.

Section expr.
Variables (R : realType).
Variables var : type -> Type.

Inductive expr : type -> Type :=
| Num : R -> expr Real
| Bol : bool -> expr Bool
| TT : expr Unit
| Var : forall t, var t -> expr t
.

Inductive exprP : type -> Type :=
| Ret : forall t t1, expr t -> expr t1
.

End expr.

Section expr_denote.
Variable (R : realType).

Fixpoint expr_denote (t : type) (e : expr R type_denote t) : type_denote t :=
  match e in (expr _ _ t) return (type_denote t) with
  | Num r => r
  | Bol b => b
  | TT => tt
  | Var _ x => x
  | Ret _ _ t => expr_denote t
  end.

End expr_denote.

