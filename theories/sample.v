
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
Require Import reals ereal classical_sets numfun.
Require Import measure kernel lebesgue_integral signed.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section sample.
Variables (R : realType) (d : measure_display) (T : measurableType d).

Lemma __ : true \in [set true].
rewrite inE //.
Qed.

Lemma _k x (s : set T) : kernel_from_dirac x s = dirac x s :> \bar R.
Proof. by []. Qed.

Check kernel_from_dirac : T -> measure R T. (* T ^^> T *)

Lemma _k1 : kernel_from_dirac true [set true] = 1 :> \bar R.
Proof. rewrite /= diracE __ //. Qed.

Lemma _k2 : kernel_from_dirac false [set: bool] = 1 :> \bar R.
Proof. rewrite /= diracE in_setT //. Qed.

(* bernoulli *)
Check bernoulli27 R : measure _ _.
Check sample_bernoulli27 R : kernel R _ _.

Lemma _k3 : sample_bernoulli27 R tt set0 = 0.
Proof. by rewrite measure0. Qed.

Lemma _k4 (s : set bool) : sample_bernoulli27 R tt s = bernoulli27 R s.
Proof. by []. Qed.

(* star *)
Check Return R : kernel R _ _.

Lemma _s (b : bool) : 
  star (Return R) (sample_bernoulli27 R) tt [set (tt, b)] =
  bernoulli27 R [set b].
Proof.
rewrite /star /=.
rewrite ge0_integral_measure_sum// 2!big_ord_recl/= big_ord0 adde0/=.
rewrite !ge0_integral_mscale//=.
rewrite !integral_dirac//=.
rewrite 2!indicE 2!in_setT 2!mul1e.
rewrite /msum 2!big_ord_recl/= big_ord0 adde0/= /mscale /=.
admit.
Abort.


End sample.
