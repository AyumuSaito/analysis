From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure fsbigop numfun lebesgue_integral kernel.
Require Import prob_lang.

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

Section operators.
Variable (R : realType).

Import Notations.

Lemma check_ret : @ret _ _ _ _ R (cst true) (kb true) tt [set true] = 1%E.
Proof.
rewrite /ret; unlock.
by rewrite /= diracE mem_set.
Abort.

Lemma check_ret : @ret _ _ _ (mR R) R _ (kr 1) tt [set 1%R] = 1%E.
Proof.
rewrite /ret; unlock; rewrite /=.
by rewrite diracE mem_set.
Abort.

Lemma check_ret : @ret _ _ _ (mR R) R _ (kr 1) true [set: R] = 1.
Proof.
rewrite /ret; unlock.
by rewrite /= diracE in_setT.
Abort.

Local Open Scope ring_scope.
Lemma test_samele : @sample _ _ _ _ R (cst (bernoulli p27)) (measurable_fun_cst (bernoulli p27 : pprobability _ _)) tt [set true]= (2 / 7)%:E.
Proof.
rewrite /sample; unlock; rewrite /=.
rewrite /mbernoulli /= /measure_add /msum 2!big_ord_recr/= big_ord0 add0e /=.
rewrite /mscale/= diracE mem_set //= mule1 diracE.
rewrite memNset //= mule0 adde0 //.
Abort.

Lemma test_score : @score R _ (mR R) (fun x => x) (@measurable_fun_id _ (mR R) setT) 1 [set tt] = 1%:E.
Proof.
rewrite /score /= /mscale/= diracE mem_set //= mule1.
rewrite normr1.
Abort.

Lemma test_score : @score R _ _ (cst 3) (kr 3) tt [set tt] = 3%:E.
Proof.
rewrite /score/= /mscale/= diracE mem_set//= mule1 normr_nat.
Abort.

Axiom measurable_fun_add1 : measurable_fun setT (fun x : R => x + 1).

Lemma test_score : @score R _ _ (fun x : R => x + 1) measurable_fun_add1 2%:R [set tt] = 3%:E.
Proof.
rewrite /score/= /mscale/= diracE mem_set//= mule1.
rewrite addrC.
have -> : (`|1 + 2| = 1 + 2).
move=> ?.
apply gtr0_norm => //.
rewrite //.
Abort.

Check letin.

Definition k1 : R.-sfker munit ~> mbool := 
  @sample _ _ _ _ R (cst (bernoulli p27)) 
  (measurable_fun_cst (bernoulli p27 : pprobability _ _)).

Definition k2 : 
  R.-sfker [the measurableType _ of (munit * mbool)%type] ~> mbool :=
  @ret _ _ _ _ R _ var2of2.

Check letin (letin k1 k2) k2.

Check k2 (tt, true) [set true].

Lemma test_integral : (\int[k1 tt]_y (k2 (tt, y) [set true]))%E = (2 / 7%:R)%:E.
Proof.
rewrite -letinE.
rewrite letinE.
under eq_integral do rewrite retE.
rewrite integral_indic ?setIT//=.
rewrite /sample; unlock.
rewrite /= /mbernoulli /measure_add /msum/= 2!big_ord_recr/=.
rewrite big_ord0 add0e /=.
rewrite /mscale/= diracE mem_set //= mule1 diracE.
by rewrite memNset //= mule0 adde0.
Abort.

Lemma test_letin : 
  @letin R _ _ _ munit mbool _ k1 k2 tt [set true] = (2 / 7%:R)%:E.
Proof.
(* letin_kret *)
rewrite letinE.
under eq_integral do rewrite retE.
rewrite integral_indic ?setIT//=.
(* test_sample *)
rewrite /sample; unlock.
rewrite /= /mbernoulli /measure_add /msum/= 2!big_ord_recr/=.
rewrite big_ord0 add0e /=.
rewrite /mscale/= diracE mem_set //= mule1 diracE.
by rewrite memNset //= mule0 adde0.
Abort.

Check (fun (x : munit) => k1 tt) : munit -> {measure set mbool -> \bar R}.
Check (fun (x : munit) => k1 tt) tt : {measure set mbool -> \bar R}.
Check [the R.-ker munit ~> mbool of (fun x => k1 x)] : R.-ker _ ~> _.
Fail Check [the R.-sfker munit ~> mbool of (fun x => k1 x)] : R.-sfker _ ~> _.

End operators.