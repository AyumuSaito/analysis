From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure fsbigop numfun lebesgue_integral kernel prob_lang.

Set Implicit Arguments.
Implicit Types V : Set.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Require Import String ZArith.
Local Open Scope string.

Import Notations.

Section type_checking.
Variable (R : realType).
Section expression.

Definition variable := string.
Inductive Z := D | P.

Inductive exp : Z -> Type :=
| exp_var  : variable -> exp D
| exp_unit : exp D
| exp_bool : bool -> exp D
| exp_real : R -> exp D
| exp_pair : exp D -> exp D -> exp D
(* | val_unif : val *)
| exp_bernoulli : {nonneg R} -> exp D
| exp_poisson : nat -> exp D -> exp D
(* | exp_if : forall z, exp D -> exp z -> exp z -> exp z *)
| exp_if : exp D -> exp P -> exp P -> exp P
| exp_letin : variable -> exp P -> exp P -> exp P
| exp_sample : exp D -> exp P
| exp_score : exp D -> exp P
| exp_return : exp D -> exp P
| exp_norm : exp P -> exp D
.

End expression.

(* Arguments exp R. *)

Section context.

Definition context := seq (string * Type)%type.

Definition context' := seq (string * forall d, measurableType d)%type.

End context.

(* Variable (R : realType). *)
Variables (d : _) (T : measurableType d).

Inductive type_checkD : context -> exp D -> Type -> Prop :=
| tc_unit G : type_checkD G exp_unit unit
| tc_bool G b : type_checkD G (exp_bool b) bool
| tc_real G r : type_checkD G (exp_real r) R
| tc_pair G e1 e2 A B : type_checkD G e1 A -> 
  type_checkD G e2 B -> type_checkD G (exp_pair e1 e2) (A * B)%type
| tc_bernoulli G r : type_checkD G (exp_bernoulli r) (probability mbool R)
| tc_poisson G k e : type_checkD G (exp_poisson k e) R
| tc_norm G e d (A : measurableType d) : 
  type_checkP G e A ->
  type_checkD G (exp_norm e) (probability A R)

| tc_var G v G' A : type_checkD (G ++ (v, A) :: G')%SEQ (exp_var v) A

with type_checkP : context -> exp P -> Type -> Prop :=
| tc_sample G e d (A : measurableType d) : type_checkD G e (probability A R) ->
  type_checkP G (exp_sample e) A
| tc_return G e A : type_checkD G e A -> type_checkP G (exp_return e) A
| tc_score G e : type_checkD G e R -> type_checkP G (exp_score e) unit

| tc_if G e1 e2 e3 A : type_checkD G e1 bool -> 
  type_checkP G e2 A -> type_checkP G e3 A -> type_checkP G (exp_if e1 e2 e3) A 
| tc_letin G v e1 e2 A B : type_checkP G e1 A -> type_checkP ((v, A) :: G) e2 B ->
  type_checkP G (exp_letin v e1 e2) B
.

Local Open Scope ring_scope.

Definition pgm1 := exp_sample (exp_bernoulli (2 / 7%:R)%:nng).

Example tc_1 : type_checkP [::] pgm1 bool.
Proof. apply/tc_sample /tc_bernoulli. Qed.

Definition pgm2 := exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng)) (exp_return (exp_var "x")).

Example tc_2 : type_checkP [::] pgm2 bool.
Proof. 
apply/(@tc_letin _ _ _ _ bool).
apply/tc_sample /tc_bernoulli.
apply/tc_return /(@tc_var [::] "x").
Qed.

Example pgm3 := exp_norm (
  exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng)) (
  exp_letin "r" (exp_if (exp_var "x") (exp_return (exp_real 3%:R)) (exp_return (exp_real 10%:R))) (
  exp_letin "_" (exp_score (exp_poisson 4 (exp_var "r"))) (
  exp_return (exp_var "x"))))).

Example tc_3 : type_checkD [::] pgm3 (probability mbool R).
Proof.
apply/tc_norm.
apply/(@tc_letin _ _ _ _ mbool).
apply/tc_sample /tc_bernoulli.
apply/tc_letin.
apply/tc_if.
apply/(@tc_var [::] "x").
apply/tc_return /tc_real.
apply/tc_return /tc_real.
apply/tc_letin.
apply/tc_score /tc_poisson.
apply/tc_return /(@tc_var [:: _; _] "x").
Qed.

End type_checking.
