From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure fsbigop numfun lebesgue_integral kernel.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Definition onem (R : numDomainType) (p : R) := (1 - p)%R.

Lemma onem1 (R : numDomainType) (p : R) : (p + onem p = 1)%R.
Proof. by rewrite /onem addrCA subrr addr0. Qed.

Lemma onem_nonneg_proof (R : numDomainType) (p : {nonneg R}) (p1 : (p%:num <= 1)%R) :
  (0 <= onem p%:num)%R.
Proof. by rewrite /onem/= subr_ge0. Qed.

Definition onem_nonneg (R : numDomainType) (p : {nonneg R}) (p1 : (p%:num <= 1)%R) :=
  NngNum (onem_nonneg_proof p1).

Section bernoulli.
Variables (R : realType) (p : {nonneg R}) (p1 : (p%:num <= 1)%R).
Local Open Scope ring_scope.

Definition bernoulli : set _ -> \bar R :=
  measure_add
    [the measure _ _ of mscale p [the measure _ _ of dirac true]]
    [the measure _ _ of mscale (onem_nonneg p1) [the measure _ _ of dirac false]].

HB.instance Definition _ := Measure.on bernoulli.

Example bernoulli_set0 : bernoulli set0 = 0%:E.
Proof. by []. Qed.
Example bernoulli_setT : bernoulli setT = 1%:E.
Proof. 
rewrite /bernoulli/= /measure_add/= /msum 2!big_ord_recr/= big_ord0 add0e/=.
by rewrite /mscale/= !diracE !in_setT !mule1 -EFinD onem1.
Qed.

HB.instance Definition _ := @isProbability.Build _ _ R bernoulli bernoulli_setT.

End bernoulli.

Section score.
Variables (R : realType) (d : _) (T : measurableType d).
Variables (r : T -> R).

Definition score (t : T) (U : set unit) : \bar R :=
  if U == set0 then 0 else `| (r t)%:E |.

Let score0 t : score t (set0 : set unit) = 0 :> \bar R.
Proof. by rewrite /score eqxx. Qed.

Let score_ge0 t U : 0 <= score t U.
Proof. by rewrite /score; case: ifP. Qed.

Let score_sigma_additive t : semi_sigma_additive (score t).
Proof.
move=> /= F mF tF mUF; rewrite /score; case: ifPn => [/eqP/bigcup0P F0|].
  rewrite (_ : (fun _ => _) = cst 0); first exact: cvg_cst.
  apply/funext => k.
  under eq_bigr do rewrite F0// eqxx.
  by rewrite big1.
move=> /eqP/bigcup0P/existsNP[k /not_implyP[_ /eqP Fk0]].
rewrite -(cvg_shiftn k.+1)/=.
rewrite (_ : (fun _ => _) = cst `|(r t)%:E|); first exact: cvg_cst.
apply/funext => n.
rewrite big_mkord (bigD1 (widen_ord (leq_addl n _) (Ordinal (ltnSn k))))//=.
rewrite (negbTE Fk0) big1 ?adde0// => i/= ik; rewrite ifT//.
have [/eqP//|Fitt] := set_unit (F i).
move/trivIsetP : tF => /(_ i k Logic.I Logic.I ik).
by rewrite Fitt setTI => /eqP; rewrite (negbTE Fk0).
Qed.

HB.instance Definition _ (t : T) := isMeasure.Build _ _ _
  (score t) (score0 t) (score_ge0 t) (@score_sigma_additive t).

Definition k_ (i : nat) 

End score.