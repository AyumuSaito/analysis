From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure fsbigop numfun lebesgue_integral kernel prob_lang.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Require Import String ZArith.
Local Open Scope string.

Section simple_lang.
Variable (R : realType).

Inductive term : Type :=
| Letin : string -> term -> term -> term
with rterm : Type :=
| Real : R -> rterm
| Plus : rterm -> rterm -> rterm
with bterm : Type :=
| Bool : bool -> bterm
.

Fixpoint eval_r (env : list R) (t : rterm) : R :=
  match t with
  | Real r => r
  | Plus t1 t2 => eval_r env t1 + eval_r env t2
  (* | Letin x t1 t2 => eval [:: (x, t1)] t2 *)
  end.

Fixpoint eval_b (env : list R) (t : bterm) : bool :=
  match t with 
  | Bool b => b
  end.

Fixpoint beval (env : list (string * term)%type) (t : bterm) : bool :=
  match t with
  | Bool b => b
  end.
(* 
Lemma _1 : eval [::] (Plus (Real 1) (Real 2)) = 3.
Proof. rewrite //. Qed.

Lemma _2 : eval [::] (Letin "x" (Real 1) (Plus (Real 1) (Real 2))) = 3.
Proof. rewrite //. Qed. *)

End simple_lang.

Section v1.
Variable (R : realType).

Let mR := Real_sort__canonical__measure_Measurable R.
Let munit := Datatypes_unit__canonical__measure_Measurable.
Let mbool := Datatypes_bool__canonical__measure_Measurable.

Inductive type :=
| ty_real
.

Definition interp_type (ty : type) :=
  match ty with
  | ty_real => R
  end.

Inductive exp : Type :=
(* | exp_var : string -> exp *)
(* | exp_letin : string -> exp -> exp -> exp *)
(* | exp_aexp : aexp -> exp
| exp_bexp : bexp -> exp
| exp_pexp : pexp -> exp
| exp_kexp : kexp -> exp *)
with aexp :=
| aexp_real : R -> aexp
| aexp_plus : aexp -> aexp -> aexp
| aexp_minus : aexp -> aexp -> aexp
| aexp_times : aexp -> aexp -> aexp
| aexp_var : string -> aexp
| aexp_letin : string -> aexp -> aexp -> aexp
with bexp :=
| bexp_true 
| bexp_false
| bexp_eq : aexp -> aexp -> bexp
(* | bexp_le : aexp -> aexp -> bexp *)
| bexp_not : bexp -> bexp
| bexp_letin : string -> bexp -> bexp -> bexp
with pexp :=
| pexp_bernoulli : R -> pexp
| pexp_letin : string -> pexp -> pexp -> pexp
(* | pexp_normal : _ -> pexp *)
with kexp :=
| kexp_sample : pexp -> kexp
| kexp_letin : string -> kexp -> kexp -> kexp
.

(* Coercion exp_aexp : aexp >-> exp. *)
(* 
Fixpoint interp_exp (env : list (string * exp)%type) (exp : exp) : R :=
  match exp with
  (* | exp_var x => *)
  | exp_letin x e1 e2 => interp_exp ((x, e1) :: env) e2
  (* | exp_aexp e => interp_exp e
  | exp_bexp e => "x"
  | exp_pexp e => "x"
  | exp_kexp e => "x" *)
  end. *)

Fixpoint search (x : string) (env : list (string * aexp)%type) :=
  match env with
  | [::] => aexp_real 0
  | h :: t => if string_dec x h.1 then h.2 else search x t
  end.

Require Import Program.Wf.
Program Fixpoint interp_aexp (env : list (string * aexp)%type) (exp : aexp) {measure _}: R :=
  match exp with
  | aexp_real r => r
  | aexp_plus e1 e2 => interp_aexp env e1 + interp_aexp env e2
  | aexp_minus e1 e2 => interp_aexp env e1 - interp_aexp env e2
  | aexp_times e1 e2 => interp_aexp env e1 * interp_aexp env e2
  | aexp_var x => interp_aexp env (aexp_real 2)
  | aexp_letin x e1 e2 => interp_aexp ((x, e1) :: env) e2 
  end.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Example pgm1 := aexp_letin "x" (aexp_real 2) (aexp_var "x").
Lemma interp1 : interp_aexp [::] pgm1 = 2.
Proof. rewrite //. Qed.

Fixpoint interp_bexp (exp : bexp) : mbool :=
  match exp with
  | bexp_true => true
  | bexp_false => false
  | bexp_eq e1 e2 => interp_aexp env e1 == interp_aexp env e2
  (* | bexp_le e1 e2 => interp_aexp env e1 < interp_aexp env e2 *)
  | bexp_not e => ~~ (interp_bexp e)
  end.

Definition interp_pexp (exp : pexp) : probability _ R :=
  match exp with
  | pexp_bernoulli r => [the probability _ R of bernoulli27 R]
  end.

Definition pgm1 := aexp_plus (aexp_real 1) (aexp_real 2).
Lemma interp1 : interp_aexp env pgm1 = 3.
Proof. by []. Qed.

Definition pgm2 := aexp_minus (aexp_real 1) (aexp_real 2).
Lemma interp2 : interp_aexp env pgm2 = -1 :> R.
Proof. rewrite /= (* natrB *). Admitted.

Lemma __ : (2 * 3)%R = 6 :> R.
Proof. rewrite -natrM //. Qed.

Definition pgm3 := aexp_times (aexp_real 2) (aexp_real 3).
Lemma interp3 : interp_aexp env pgm3 = 6 :> R.
Proof. by rewrite /= -natrM. Qed.

Definition pgm4 := 
  bexp_eq (aexp_plus (aexp_real 1) (aexp_real 2)) (aexp_real 3).
Lemma interp4 : interp_bexp pgm4 = true.
Proof. apply/idP/eqP => //. Qed.

Definition interp_kexp (exp : kexp) : R.-sfker munit ~> _ :=
  match exp with
  | kexp_sample p => sample _ (interp_pexp p)
  end.
Definition pgm0 := kexp_sample (pexp_bernoulli (2 / 7)).
Lemma interp0 : interp_kexp pgm0 = sample _ [the probability _ _ of bernoulli27 R].
Proof. by []. Qed.

End v1.