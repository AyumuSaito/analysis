From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure fsbigop numfun lebesgue_integral kernel.
Require Import prob_lang.

Section bernoulli.
Variable (R : realType) (p : {nonneg R}%R) (p1 : (p%:num <= 1)%R).

Lemma b10 : bernoulli p1 [set 0] = (`1-(p%:num))%:E.
Proof.
rewrite /bernoulli/= /measure_add/= /msum.
rewrite 2!big_ord_recr/= big_ord0 add0e.
rewrite /mscale/= !diracE memNset// mem_set//= mule1 mule0 add0e //.
Qed.

Lemma b11 : bernoulli p1 [set 1] = p%:num%:E.
Proof.
rewrite /bernoulli/= /measure_add/= /msum.
rewrite 2!big_ord_recr/= big_ord0 add0e.
rewrite /mscale/= !diracE mem_set// memNset//= mule1 mule0 adde0 //.
Qed.

End bernoulli.
Section binomial.
Local Open Scope ring_scope.
Variables (R : realType).

(* Compute p%:num%:E.
Compute p%:num%R ^+ 2. *)

Definition binomial2 (p : {nonneg R}) (p1 : p%:num <= 1) :=
  measure_add
    (mscale (p%:num ^+ 2)%:nng (dirac 2%N))
    (measure_add
    (mscale (2 * p%:num * (onem_nonneg p1)%:num)%:nng (dirac 1%N))
    (mscale ((onem_nonneg p1)%:num ^+ 2)%:nng (dirac 0%N))).

Lemma b20 p p1 : binomial2 p p1 [set 2%N] = (p%:num ^+ 2)%:E.
Proof.
rewrite /binomial2/= /measure_add/= /msum !big_ord_recr/= big_ord0 add0e.
rewrite /msum !big_ord_recr/= big_ord0 add0e.
rewrite /mscale/= !diracE mem_set//= memNset// memNset// mule1 mule0 mule0 add0e adde0//.
Qed.

End binomial.

Local Open Scope ring_scope.
Import Order.TTheory GRing.Theory Num.Def Num.ExtraDef Num.Theory.

Section example.
Variables (R : realType).

Goal binomial2 R (1 / 2)%:nng p12 [set 2%N] = (1 / 4)%:E.
Proof.
rewrite b20 /= expr2.
by rewrite mulf_div -natrM [in LHS]mul1r.
Qed.

(* Lemma measurable_fun_bernoulli (U : set _) :
  measurable U ->
  measurable_fun setT (@bernoulli R p).
Proof.
move=> mU.
by apply: ge0_emeasurable_fun_sum => // n; exact/measurable_kernel.
Qed. *)

HB.instance Definition _ :=
  isKernel.Build _ _ _ _ _ (bernoulli p1) measurable_fun_kseries.

Check letin bernoulli.

Check p27.

