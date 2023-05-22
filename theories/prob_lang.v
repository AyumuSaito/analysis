(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import rat.
From mathcomp.classical Require Import mathcomp_extra boolp classical_sets.
From mathcomp.classical Require Import functions cardinality fsbigop.
Require Import reals ereal signed topology normedtype sequences esum measure.
Require Import lebesgue_measure  numfun lebesgue_integral exp kernel.

(******************************************************************************)
(*  Semantics of a probabilistic programming language using s-finite kernels  *)
(*                                                                            *)
(*       bernoulli r1 == Bernoulli probability with r1 a proof that           *)
(*                       r : {nonneg R} is smaller than 1                     *)
(*                                                                            *)
(*           sample P == sample according to the probability P                *)
(*          letin l k == execute l, augment the context, and execute k        *)
(*             ret mf == access the context with f and return the result      *)
(*           score mf == observe t from d, where f is the density of d and    *)
(*                       t occurs in f                                        *)
(*                       e.g., score (r e^(-r * t)) = observe t from exp(r)   *)
(*     pnormalize k P == normalize the kernel k into a probability kernel,    *)
(*                       P is a default probability in case normalization is  *)
(*                       not possible                                         *)
(*       ite mf k1 k2 == access the context with the boolean function f and   *)
(*                       behaves as k1 or k2 according to the result          *)
(*                                                                            *)
(*            poisson == Poisson distribution function                        *)
(*        exp_density == density function for exponential distribution        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.ExtraDef Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(* TODO: PR *)
Lemma onem1' (R : numDomainType) (p : R) : (p + `1- p = 1)%R.
Proof. by rewrite /onem addrCA subrr addr0. Qed.

Lemma onem_nonneg_proof (R : numDomainType) (p : {nonneg R}) :
  (p%:num <= 1 -> 0 <= `1-(p%:num))%R.
Proof. by rewrite /onem/= subr_ge0. Qed.

Definition onem_nonneg (R : numDomainType) (p : {nonneg R})
   (p1 : (p%:num <= 1)%R) :=
  NngNum (onem_nonneg_proof p1).
(* /TODO: PR *)

Section bernoulli.
Variables (R : realType) (p : {nonneg R}) (p1 : (p%:num <= 1)%R).
Local Open Scope ring_scope.

Definition bernoulli : set _ -> \bar R :=
  measure_add
    [the measure _ _ of mscale p [the measure _ _ of dirac true]]
    [the measure _ _ of mscale (onem_nonneg p1) [the measure _ _ of dirac false]].

HB.instance Definition _ := Measure.on bernoulli.

Local Close Scope ring_scope.

Let bernoulli_setT : bernoulli [set: _] = 1.
Proof.
rewrite /bernoulli/= /measure_add/= /msum 2!big_ord_recr/= big_ord0 add0e/=.
by rewrite /mscale/= !diracT !mule1 -EFinD onem1'.
Qed.

HB.instance Definition _ := @Measure_isProbability.Build _ _ R bernoulli bernoulli_setT.

End bernoulli.

Section mscore.
Context d (T : measurableType d) (R : realType).
Variable f : T -> R.

Definition mscore t : {measure set _ -> \bar R} :=
  let p := NngNum (normr_ge0 (f t)) in
  [the measure _ _ of mscale p [the measure _ _ of dirac tt]].

Lemma mscoreE t U : mscore t U = if U == set0 then 0 else `| (f t)%:E |.
Proof.
rewrite /mscore/= /mscale/=; have [->|->] := set_unit U.
  by rewrite eqxx dirac0 mule0.
by rewrite diracT mule1 (negbTE setT0).
Qed.

Lemma measurable_fun_mscore U : measurable_fun setT f ->
  measurable_fun setT (mscore ^~ U).
Proof.
move=> mr; under eq_fun do rewrite mscoreE/=.
have [U0|U0] := eqVneq U set0; first exact: measurable_cst.
by apply: measurableT_comp => //; exact: measurableT_comp.
Qed.

End mscore.

(* decomposition of score into finite kernels *)
Module SCORE.
Section score.
Context d (T : measurableType d) (R : realType).
Variable f : T -> R.

Definition k (mf : measurable_fun setT f) i t U :=
    if i%:R%:E <= mscore f t U < i.+1%:R%:E then
      mscore f t U
    else
      0.

Hypothesis mf : measurable_fun setT f.

Lemma k0 i t : k mf i t (set0 : set unit) = 0 :> \bar R.
Proof. by rewrite /k measure0; case: ifP. Qed.

Lemma k_ge0 i t B : 0 <= k mf i t B.
Proof. by rewrite /k; case: ifP. Qed.

Lemma k_sigma_additive i t : semi_sigma_additive (k mf i t).
Proof.
move=> /= F mF tF mUF; rewrite /k /=.
have [F0|UF0] := eqVneq (\bigcup_n F n) set0.
  rewrite F0 measure0 (_ : (fun _ => _) = cst 0).
    by case: ifPn => _; exact: cvg_cst.
  apply/funext => k; rewrite big1// => n _.
  by move: F0 => /bigcup0P -> //; rewrite measure0; case: ifPn.
move: (UF0) => /eqP/bigcup0P/existsNP[m /not_implyP[_ /eqP Fm0]].
rewrite [in X in _ --> X]mscoreE (negbTE UF0).
rewrite -(cvg_shiftn m.+1)/=.
case: ifPn => ir.
  rewrite (_ : (fun _ => _) = cst `|(f t)%:E|); first exact: cvg_cst.
  apply/funext => n.
  rewrite big_mkord (bigD1 (widen_ord (leq_addl n _) (Ordinal (ltnSn m))))//=.
  rewrite [in X in X + _]mscoreE (negbTE Fm0) ir big1 ?adde0// => /= j jk.
  rewrite mscoreE; have /eqP -> : F j == set0.
    have [/eqP//|Fjtt] := set_unit (F j).
    move/trivIsetP : tF => /(_ j m Logic.I Logic.I jk).
    by rewrite Fjtt setTI => /eqP; rewrite (negbTE Fm0).
  by rewrite eqxx; case: ifP.
rewrite (_ : (fun _ => _) = cst 0); first exact: cvg_cst.
apply/funext => n.
rewrite big_mkord (bigD1 (widen_ord (leq_addl n _) (Ordinal (ltnSn m))))//=.
rewrite [in X in if X then _ else _]mscoreE (negbTE Fm0) (negbTE ir) add0e.
rewrite big1//= => j jm; rewrite mscoreE; have /eqP -> : F j == set0.
  have [/eqP//|Fjtt] := set_unit (F j).
  move/trivIsetP : tF => /(_ j m Logic.I Logic.I jm).
  by rewrite Fjtt setTI => /eqP; rewrite (negbTE Fm0).
by rewrite eqxx; case: ifP.
Qed.

HB.instance Definition _ i t := isMeasure.Build _ _ _
  (k mf i t) (k0 i t) (k_ge0 i t) (@k_sigma_additive i t).

Lemma measurable_fun_k i U : measurable U -> measurable_fun setT (k mf i ^~ U).
Proof.
move=> /= mU; rewrite /k /= (_ : (fun x => _) =
  (fun x => if i%:R%:E <= x < i.+1%:R%:E then x else 0) \o (mscore f ^~ U)) //.
apply: measurableT_comp => /=; last exact/measurable_fun_mscore.
rewrite (_ : (fun x => _) = (fun x => x *
    (\1_(`[i%:R%:E, i.+1%:R%:E [%classic : set _) x)%:E)); last first.
  apply/funext => x; case: ifPn => ix; first by rewrite indicE/= mem_set ?mule1.
  by rewrite indicE/= memNset ?mule0// /= in_itv/=; exact/negP.
apply: emeasurable_funM => //=; apply/EFin_measurable_fun.
by rewrite (_ : \1__ = mindic R (emeasurable_itv `[(i%:R)%:E, (i.+1%:R)%:E[)).
Qed.

Definition mk i t := [the measure _ _ of k mf i t].

HB.instance Definition _ i :=
  isKernel.Build _ _ _ _ _ (mk i) (measurable_fun_k i).

Lemma mk_uub i : measure_fam_uub (mk i).
Proof.
exists i.+1%:R => /= t; rewrite /k mscoreE setT_unit.
by case: ifPn => //; case: ifPn => // _ /andP[].
Qed.

HB.instance Definition _ i :=
  Kernel_isFinite.Build _ _ _ _ _ (mk i) (mk_uub i).

End score.
End SCORE.

Section kscore.
Context d (T : measurableType d) (R : realType).
Variable f : T -> R.

Definition kscore (mf : measurable_fun setT f)
    : T -> {measure set _ -> \bar R} :=
  mscore f.

Variable mf : measurable_fun setT f.

Let measurable_fun_kscore U : measurable U ->
  measurable_fun setT (kscore mf ^~ U).
Proof. by move=> /= _; exact: measurable_fun_mscore. Qed.

HB.instance Definition _ := isKernel.Build _ _ T _ R
  (kscore mf) measurable_fun_kscore.

Import SCORE.

Let sfinite_kscore : exists k : (R.-fker T ~> _)^nat,
  forall x U, measurable U ->
    kscore mf x U = mseries (k ^~ x) 0 U.
Proof.
rewrite /=; exists (fun i => [the R.-fker _ ~> _ of mk mf i]) => /= t U mU.
rewrite /mseries /kscore/= mscoreE; case: ifPn => [/eqP U0|U0].
  by apply/esym/eseries0 => i _; rewrite U0 measure0.
rewrite /mk /= /k /= mscoreE (negbTE U0).
apply/esym/cvg_lim => //.
rewrite -(cvg_shiftn `|floor (fine `|(f t)%:E|)|%N.+1)/=.
rewrite (_ : (fun _ => _) = cst `|(f t)%:E|); first exact: cvg_cst.
apply/funext => n.
pose floor_f := widen_ord (leq_addl n `|floor `|f t| |.+1)
                          (Ordinal (ltnSn `|floor `|f t| |)).
rewrite big_mkord (bigD1 floor_f)//= ifT; last first.
  rewrite lee_fin lte_fin; apply/andP; split.
    by rewrite natr_absz (@ger0_norm _ (floor `|f t|)) ?floor_ge0 ?floor_le.
  rewrite -addn1 natrD natr_absz.
  by rewrite (@ger0_norm _ (floor `|f t|)) ?floor_ge0 ?lt_succ_floor.
rewrite big1 ?adde0//= => j jk.
rewrite ifF// lte_fin lee_fin.
move: jk; rewrite neq_ltn/= => /orP[|] jr.
- suff : (j.+1%:R <= `|f t|)%R by rewrite leNgt => /negbTE ->; rewrite andbF.
  rewrite (_ : j.+1%:R = j.+1%:~R)// floor_ge_int.
  move: jr; rewrite -lez_nat => /le_trans; apply.
  by rewrite -[leRHS](@ger0_norm _ (floor `|f t|)) ?floor_ge0.
- suff : (`|f t| < j%:R)%R by rewrite ltNge => /negbTE ->.
  move: jr; rewrite -ltz_nat -(@ltr_int R) (@gez0_abs (floor `|f t|)) ?floor_ge0//.
  by rewrite ltr_int -floor_lt_int.
Qed.

HB.instance Definition _ :=
  @Kernel_isSFinite.Build _ _ _ _ _ (kscore mf) sfinite_kscore.

End kscore.

(* decomposition of ite into s-finite kernels *)
Module ITE.
Section ite.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).

Section kiteT.
Variable k : R.-ker X ~> Y.

Definition kiteT : X * bool -> {measure set Y -> \bar R} :=
  fun xb => if xb.2 then k xb.1 else [the measure _ _ of mzero].

Let measurable_fun_kiteT U : measurable U -> measurable_fun setT (kiteT ^~ U).
Proof.
move=> /= mcU; rewrite /kiteT.
rewrite (_ : (fun _ => _) =
    (fun x => if x.2 then k x.1 U else mzero U)); last first.
  by apply/funext => -[t b]/=; case: ifPn.
apply: (@measurable_fun_if_pair _ _ _ _ (k ^~ U) (fun=> mzero U)) => //.
exact/measurable_kernel.
Qed.

#[export]
HB.instance Definition _ := isKernel.Build _ _ _ _ _
  kiteT measurable_fun_kiteT.
End kiteT.

Section sfkiteT.
Variable k : R.-sfker X ~> Y.

Let sfinite_kiteT : exists2 k_ : (R.-ker _ ~> _)^nat,
  forall n, measure_fam_uub (k_ n) &
  forall x U, measurable U -> kiteT k x U = mseries (k_ ^~ x) 0 U.
Proof.
have [k_ hk /=] := sfinite_kernel k.
exists (fun n => [the _.-ker _ ~> _ of kiteT (k_ n)]) => /=.
  move=> n; have /measure_fam_uubP[r k_r] := measure_uub (k_ n).
  by exists r%:num => /= -[x []]; rewrite /kiteT//= /mzero//.
move=> [x b] U mU; rewrite /kiteT; case: ifPn => hb; first by rewrite hk.
by rewrite /mseries eseries0.
Qed.

#[export]
HB.instance Definition _ t := @Kernel_isSFinite_subdef.Build _ _ _ _ _
  (kiteT k) sfinite_kiteT.
End sfkiteT.

Section fkiteT.
Variable k : R.-fker X ~> Y.

Let kiteT_uub : measure_fam_uub (kiteT k).
Proof.
have /measure_fam_uubP[M hM] := measure_uub k.
exists M%:num => /= -[]; rewrite /kiteT => t [|]/=; first exact: hM.
by rewrite /= /mzero.
Qed.

#[export]
HB.instance Definition _ t := Kernel_isFinite.Build _ _ _ _ _
  (kiteT k) kiteT_uub.
End fkiteT.

Section kiteF.
Variable k : R.-ker X ~> Y.

Definition kiteF : X * bool -> {measure set Y -> \bar R} :=
  fun xb => if ~~ xb.2 then k xb.1 else [the measure _ _ of mzero].

Let measurable_fun_kiteF U : measurable U -> measurable_fun setT (kiteF ^~ U).
Proof.
move=> /= mcU; rewrite /kiteF.
rewrite (_ : (fun x => _) =
    (fun x => if x.2 then mzero U else k x.1 U)); last first.
  by apply/funext => -[t b]/=; rewrite if_neg//; case: ifPn.
apply: (@measurable_fun_if_pair _ _ _ _ (fun=> mzero U) (k ^~ U)) => //.
exact/measurable_kernel.
Qed.

#[export]
HB.instance Definition _ := isKernel.Build _ _ _ _ _
  kiteF measurable_fun_kiteF.

End kiteF.

Section sfkiteF.
Variable k : R.-sfker X ~> Y.

Let sfinite_kiteF : exists2 k_ : (R.-ker _ ~> _)^nat,
  forall n, measure_fam_uub (k_ n) &
  forall x U, measurable U -> kiteF k x U = mseries (k_ ^~ x) 0 U.
Proof.
have [k_ hk /=] := sfinite_kernel k.
exists (fun n => [the _.-ker _ ~> _ of kiteF (k_ n)]) => /=.
  move=> n; have /measure_fam_uubP[r k_r] := measure_uub (k_ n).
  by exists r%:num => /= -[x []]; rewrite /kiteF//= /mzero//.
move=> [x b] U mU; rewrite /kiteF; case: ifPn => hb; first by rewrite hk.
by rewrite /mseries eseries0.
Qed.

#[export]
HB.instance Definition _ := @Kernel_isSFinite_subdef.Build _ _ _ _ _
  (kiteF k) sfinite_kiteF.

End sfkiteF.

Section fkiteF.
Variable k : R.-fker X ~> Y.

Let kiteF_uub : measure_fam_uub (kiteF k).
Proof.
have /measure_fam_uubP[M hM] := measure_uub k.
by exists M%:num => /= -[]; rewrite /kiteF/= => t; case => //=; rewrite /mzero.
Qed.

#[export]
HB.instance Definition _ := Kernel_isFinite.Build _ _ _ _ _
  (kiteF k) kiteF_uub.

End fkiteF.
End ite.
End ITE.

Section ite.
Context d d' (T : measurableType d) (T' : measurableType d') (R : realType).
Variables (f : T -> bool) (u1 u2 : R.-sfker T ~> T').

Definition mite (mf : measurable_fun setT f) : T -> set T' -> \bar R :=
  fun t => if f t then u1 t else u2 t.

Variables mf : measurable_fun setT f.

Let mite0 t : mite mf t set0 = 0.
Proof. by rewrite /mite; case: ifPn. Qed.

Let mite_ge0 t U : 0 <= mite mf t U.
Proof. by rewrite /mite; case: ifPn. Qed.

Let mite_sigma_additive t : semi_sigma_additive (mite mf t).
Proof.
by rewrite /mite; case: ifPn => ft; exact: measure_semi_sigma_additive.
Qed.

HB.instance Definition _ t := isMeasure.Build _ _ _ (mite mf t)
  (mite0 t) (mite_ge0 t) (@mite_sigma_additive t).

Import ITE.

(*
Definition kite : R.-sfker T ~> T' :=
  kdirac mf \; kadd (kiteT u1) (kiteF u2).
*)
Definition kite :=
  [the R.-sfker _ ~> _ of kdirac mf] \;
  [the R.-sfker _ ~> _ of kadd
    [the R.-sfker _ ~> T' of kiteT u1]
    [the R.-sfker _ ~> T' of kiteF u2] ].

End ite.

Section insn2.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).

Definition ret (f : X -> Y) (mf : measurable_fun setT f)
  : R.-pker X ~> Y := [the R.-pker _ ~> _ of kdirac mf].

Definition sample (P : pprobability Y R) : R.-pker X ~> Y :=
  [the R.-pker _ ~> _ of kprobability (measurable_cst P)].

Definition normalize (k : R.-sfker X ~> Y) P : X -> probability Y R :=
  fun x => [the probability _ _ of mnormalize k P x].

Definition ite (f : X -> bool) (mf : measurable_fun setT f)
    (k1 k2 : R.-sfker X ~> Y) : R.-sfker X ~> Y :=
  locked [the R.-sfker X ~> Y of kite k1 k2 mf].

End insn2.
Arguments ret {d d' X Y R f} mf.
Arguments sample {d d' X Y R}.

Section insn2_lemmas.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).

Lemma retE (f : X -> Y) (mf : measurable_fun setT f) x :
  ret mf x = \d_(f x) :> (_ -> \bar R).
Proof. by []. Qed.

Lemma sampleE (P : probability Y R) (x : X) : sample P x = P.
Proof. by []. Qed.

Lemma normalizeE (f : R.-sfker X ~> Y) P x U :
  normalize f P x U =
  if (f x [set: Y] == 0) || (f x [set: Y] == +oo) then P U
  else f x U * ((fine (f x [set: Y]))^-1)%:E.
Proof. by rewrite /normalize /= /mnormalize; case: ifPn. Qed.

Lemma iteE (f : X -> bool) (mf : measurable_fun setT f)
    (k1 k2 : R.-sfker X ~> Y) x :
  ite mf k1 k2 x = if f x then k1 x else k2 x.
Proof.
apply/eq_measure/funext => U.
rewrite /ite; unlock => /=.
rewrite /kcomp/= integral_dirac//=.
rewrite indicT mul1e.
rewrite -/(measure_add (ITE.kiteT k1 (x, f x)) (ITE.kiteF k2 (x, f x))).
rewrite measure_addE.
rewrite /ITE.kiteT /ITE.kiteF/=.
by case: ifPn => fx /=; rewrite /mzero ?(adde0,add0e).
Qed.

End insn2_lemmas.

Section insn3.
Context d d' d3 (X : measurableType d) (Y : measurableType d')
  (Z : measurableType d3) (R : realType).

Definition letin (l : R.-sfker X ~> Y) (k : R.-sfker [the measurableType _ of (X * Y)%type] ~> Z)
   : R.-sfker X ~> Z :=
  [the R.-sfker X ~> Z of l \; k].

End insn3.

Section insn3_lemmas.
Context d d' d3 (X : measurableType d) (Y : measurableType d')
  (Z : measurableType d3) (R : realType).

Lemma letinE (l : R.-sfker X ~> Y) (k : R.-sfker [the measurableType _ of (X * Y)%type] ~> Z) x U :
  letin l k x U = \int[l x]_y k (x, y) U.
Proof. by []. Qed.

End insn3_lemmas.

(* rewriting laws *)
Section letin_return.
Context d d' d3 (X : measurableType d) (Y : measurableType d')
  (Z : measurableType d3) (R : realType).

Lemma letin_kret (k : R.-sfker X ~> Y)
  (f : X * Y -> Z) (mf : measurable_fun setT f) x U :
  measurable U ->
  letin k (ret mf) x U = k x (curry f x @^-1` U).
Proof.
move=> mU; rewrite letinE.
under eq_integral do rewrite retE.
rewrite integral_indic ?setIT// -[X in measurable X]setTI.
exact: (measurableT_comp mf).
Qed.

Lemma letin_retk
  (f : X -> Y) (mf : measurable_fun setT f)
  (k : R.-sfker [the measurableType _ of (X * Y)%type] ~> Z)
  x U : measurable U ->
  letin (ret mf) k x U = k (x, f x) U.
Proof.
move=> mU; rewrite letinE retE integral_dirac ?indicT ?mul1e//.
exact: (measurableT_comp (measurable_kernel k _ mU)).
Qed.

End letin_return.

Section insn1.
Context d (X : measurableType d) (R : realType).

Definition score (f : X -> R) (mf : measurable_fun setT f)
    : R.-sfker X ~> _ :=
  [the R.-sfker X ~> _ of kscore mf].

End insn1.

Section hard_constraint.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).

Definition fail :=
  letin (score (@measurable_cst _ _ X _ setT (0%R : R)))
        (ret (@measurable_cst _ _ _ Y setT point)).

Lemma failE x U : fail x U = 0.
Proof. by rewrite /fail letinE ge0_integral_mscale//= normr0 mul0e. Qed.

End hard_constraint.
Arguments fail {d d' X Y R}.

Module Notations.

(*Notation var1of2 := (@measurable_fst _ _ _ _).
Notation var2of2 := (@measurable_snd _ _ _ _).
Notation var1of3 := (measurableT_comp (@measurable_fst _ _ _ _)
                                         (@measurable_fst _ _ _ _)).
Notation var2of3 := (measurableT_comp (@measurable_snd _ _ _ _)
                                         (@measurable_fst _ _ _ _)).
Notation var3of3 := (@measurable_snd _ _ _ _).*)

Notation mR := Real_sort__canonical__measure_Measurable.
Notation munit := Datatypes_unit__canonical__measure_Measurable.
Notation mbool := Datatypes_bool__canonical__measure_Measurable.

End Notations.

Section cst_fun.
Context d (T : measurableType d) (R : realType).

Definition kr (r : R) := @measurable_cst _ _ T _ setT r.
Definition k3 : measurable_fun _ _ := kr 3%:R.
Definition k10 : measurable_fun _ _ := kr 10%:R.
Definition ktt := @measurable_cst _ _ T _ setT tt.
Definition kb (b : bool) := @measurable_cst _ _ T _ setT b.

End cst_fun.
Arguments kr {d T R}.
Arguments k3 {d T R}.
Arguments k10 {d T R}.
Arguments ktt {d T}.
Arguments kb {d T}.

Section type_syntax.
Import Notations.
Variables (R : realType).

Fixpoint iter_mprod (l : list {d & measurableType d})
    : {d & measurableType d} :=
  match l with
  | [::] => existT measurableType _ munit
  | h :: t => let t' := iter_mprod t in
    existT _ _ [the measurableType (projT1 h, projT1 t').-prod of (projT2 h * projT2 t')%type]
  end.

Inductive stype :=
| sunit : stype
| sbool : stype
| sreal : stype
| spair : stype -> stype -> stype
| sprob : stype -> stype
| slist : list stype -> stype
| sconst : {d & measurableType d} -> stype.

(* Canonical stype_eqType := Equality.Pack (@gen_eqMixin stype). *)

Fixpoint typei (t : stype) : {d & measurableType d} :=
  match t with
  | sunit => existT _ _ munit
  | sbool => existT _ _ mbool
  | sreal => existT _ _ (mR R)
  | spair A B => existT _ _
      [the measurableType (projT1 (typei A), projT1 (typei B)).-prod%mdisp of
      (projT2 (typei A) * projT2 (typei B))%type]
  | sprob A => existT _ _ (pprobability (projT2 (typei A)) R)
  | slist l => iter_mprod (map typei l)
  | sconst T => T
  end.

Definition typei2 t := projT2 (typei t).

End type_syntax.

Arguments typei {R}.
Arguments typei2 {R}.

Section acc.
Context {R : realType}.

Fixpoint acc (l : seq stype) (i : nat) :
  typei2 (slist l) -> @typei2 R (nth sunit l i) :=
  match l return (typei2 (slist l) -> typei2 (nth sunit l i)) with
  | [::] => match i with | O => id | j.+1 => id end
  | _ :: _ => match i with
               | O => fst
               | j.+1 => fun H => acc j H.2
               end
  end.

Lemma macc (l : seq stype) (i : nat) : measurable_fun setT (@acc l i).
Proof. by elim: l i => //= h t ih [|j] //; exact: (measurableT_comp (ih _)). Qed.
End acc.
Arguments acc {R} l i.
Arguments macc {R} l i.

Section rpair_pairA.
Context d0 d1 d2 (T0 : measurableType d0) (T1 : measurableType d1)
  (T2 : measurableType d2).

Definition rpair d (T : measurableType d) t :
    ([the measurableType _ of T0] -> [the measurableType _ of T0 * T])%type :=
  fun x => (x, t).

Lemma mrpair d (T : measurableType d) t : measurable_fun setT (@rpair _ T t).
Proof. exact: measurable_fun_prod. Qed.

Definition pairA : ([the measurableType _ of T0 * T1 * T2] ->
                    [the measurableType _ of T0 * (T1 * T2)])%type :=
  fun x => (x.1.1, (x.1.2, x.2)).

Definition mpairA : measurable_fun setT pairA.
Proof.
apply: measurable_fun_prod => /=; first exact: measurableT_comp.
by apply: measurable_fun_prod => //=; exact: measurableT_comp.
Qed.

Definition pairAi : ([the measurableType _ of T0 * (T1 * T2)] ->
                    [the measurableType _ of T0 * T1 * T2])%type :=
  fun x => (x.1, x.2.1, x.2.2).

Definition mpairAi : measurable_fun setT pairAi.
Proof.
apply: measurable_fun_prod => //=; last exact: measurableT_comp.
apply: measurable_fun_prod => //=; exact: measurableT_comp.
Qed.

End rpair_pairA.
Arguments rpair {d0 T0 d} T.
#[global] Hint Extern 0 (measurable_fun _ (rpair _ _)) =>
  solve [apply: mrpair] : core.
Arguments pairA {d0 d1 d2 T0 T1 T2}.
#[global] Hint Extern 0 (measurable_fun _ pairA) =>
  solve [apply: mpairA] : core.
Arguments pairAi {d0 d1 d2 T0 T1 T2}.
#[global] Hint Extern 0 (measurable_fun _ pairAi) =>
  solve [apply: mpairAi] : core.

Section rpair_pairA_comp.
Import Notations.
Context d0 d1 d2 d3 (T0 : measurableType d0) (T1 : measurableType d1)
  (T2 : measurableType d2) (T3 : measurableType d3) (R : realType).

Definition pairAr d (T : measurableType d) t :
    ([the measurableType _ of T0 * T1] ->
     [the measurableType _ of T0 * (T1 * T)])%type :=
  pairA \o rpair T t.
Arguments pairAr {d} T.

Lemma mpairAr d (T : measurableType d) t : measurable_fun setT (pairAr T t).
Proof. exact: measurableT_comp. Qed.

Definition pairAAr : ([the measurableType _ of T0 * T1 * T2] ->
                      [the measurableType _ of T0 * (T1 * (T2 * munit))])%type :=
  pairA \o pairA \o rpair munit tt.

Lemma mpairAAr : measurable_fun setT pairAAr.
Proof. by do 2 apply: measurableT_comp => //. Qed.

Definition pairAArAi : ([the measurableType _ of T0 * (T1 * T2)] ->
                        [the measurableType _ of T0 * (T1 * (T2 * munit))])%type :=
  pairAAr \o pairAi.

Lemma mpairAArAi : measurable_fun setT pairAArAi.
Proof. by apply: measurableT_comp => //=; exact: mpairAAr. Qed.

Definition pairAAArAAi : ([the measurableType _ of T3 * (T0 * (T1 * T2))] ->
                     [the measurableType _ of T3 * (T0 * (T1 * (T2 * munit)))])%type :=
  pairA \o pairA \o pairA \o rpair munit tt \o pairAi \o pairAi.

Lemma mpairAAARAAAi : measurable_fun setT pairAAArAAi.
Proof. by do 5 apply: measurableT_comp => //=. Qed.

End rpair_pairA_comp.
Arguments pairAr {d0 d1 T0 T1 d} T.
Arguments pairAAr {d0 d1 d2 T0 T1 T2}.
Arguments pairAArAi {d0 d1 d2 T0 T1 T2}.
Arguments pairAAArAAi {d0 d1 d2 d3 T0 T1 T2 T3}.

Section accessor_funcions.
Import Notations.
Context d0 d1 d2 d3 (T0 : measurableType d0) (T1 : measurableType d1)
  (T2 : measurableType d2) (T3 : measurableType d3) (R : realType).

Definition Of2 := [:: sconst (existT _ _ T0); sconst (existT _ _ T1)].

Definition acc0of2 : [the measurableType _ of (T0 * T1)%type] -> T0 :=
  @acc R Of2 0 \o pairAr munit tt.

Lemma macc0of2 : measurable_fun setT acc0of2.
Proof. by apply: measurableT_comp; [exact: (macc Of2 0)|exact: mpairAr]. Qed.

Definition acc1of2 : [the measurableType _ of (T0 * T1)%type] -> T1 :=
  @acc R Of2 1 \o pairAr munit tt.

Lemma macc1of2 : measurable_fun setT acc1of2.
Proof. by apply: measurableT_comp; [exact: (macc Of2 1)|exact: mpairAr]. Qed.

Definition Of3 := [:: sconst (existT _ _ T0); sconst (existT _ _ T1); sconst (existT _ d2 T2)].

Definition acc1of3 : [the measurableType _ of (T0 * T1 * T2)%type] -> T1 :=
  @acc R Of3 1 \o pairAAr.

Lemma macc1of3 : measurable_fun setT acc1of3.
Proof. by apply: measurableT_comp; [exact: (macc Of3 1)|exact: mpairAAr]. Qed.

Definition acc2of3 : [the measurableType _ of (T0 * T1 * T2)%type] -> T2 :=
  @acc R Of3 2 \o pairAAr.

Lemma macc2of3 : measurable_fun setT acc2of3.
Proof. by apply: measurableT_comp; [exact: (macc Of3 2)|exact: mpairAAr]. Qed.

Definition acc0of3' : [the measurableType _ of (T0 * (T1 * T2))%type] -> T0 :=
  @acc R Of3 0 \o pairAArAi.

Lemma macc0of3' : measurable_fun setT acc0of3'.
Proof. by apply: measurableT_comp; [exact: (macc Of3 0)|exact: mpairAArAi]. Qed.

Definition acc1of3' : [the measurableType _ of (T0 * (T1 * T2))%type] -> T1 :=
  @acc R Of3 1 \o pairAArAi.

Lemma macc1of3' : measurable_fun setT acc1of3'.
Proof. by apply: measurableT_comp; [exact: (macc Of3 1)|exact: mpairAArAi]. Qed.

Definition acc2of3' : [the measurableType _ of (T0 * (T1 * T2))%type] -> T2 :=
  @acc R Of3 2 \o pairAArAi.

Lemma macc2of3' : measurable_fun setT acc2of3'.
Proof. by apply: measurableT_comp; [exact: (macc Of3 2)|exact: mpairAArAi]. Qed.

Definition Of4 := [:: sconst (existT _ _ T0); sconst (existT _ _ T1); sconst (existT _ d2 T2); sconst (existT _ d3 T3)].

Definition acc2of4' : [the measurableType _ of (T0 * (T1 * (T2 * T3)))%type] -> T2 :=
  @acc R Of4 2 \o pairAAArAAi.

Lemma macc2of4' : measurable_fun setT acc2of4'.
Proof. by apply: measurableT_comp; [exact: (macc Of4 2)|exact: mpairAAARAAAi]. Qed.

End accessor_funcions.

Section insn1_lemmas.
Import Notations.
Context d (T : measurableType d) (R : realType).

Let kcomp_scoreE d1 d2 (T1 : measurableType d1) (T2 : measurableType d2)
  (g : R.-sfker [the measurableType _ of (T1 * unit)%type] ~> T2)
  f (mf : measurable_fun setT f) r U :
  (score mf \; g) r U = `|f r|%:E * g (r, tt) U.
Proof.
rewrite /= /kcomp /kscore /= ge0_integral_mscale//=.
by rewrite integral_dirac// indicT mul1e.
Qed.

Goal @typei2 R (slist [:: spair (sconst (existT _ _ mbool)) (sconst (existT _ _ munit)); sreal]) =
     ((bool * unit) * (R * unit))%type.
done.
Abort.

Lemma scoreE d' (T' : measurableType d') (x : T * T') (U : set T') (f : R -> R)
    (r : R) (r0 : (0 <= r)%R)
    (f0 : (forall r, 0 <= r -> 0 <= f r)%R) (mf : measurable_fun setT f) :
  score (measurableT_comp mf (macc1of2 R))
    (x, r) (curry (snd \o fst) x @^-1` U) =
  (f r)%:E * \d_x.2 U.
Proof.
by rewrite /score/= /mscale/= ger0_norm//= f0.
Qed.

(* Lemma scoreE d' (T' : measurableType d') (x : T * T') (U : set T') (f : R -> R)
    (r : R) (r0 : (0 <= r)%R)
    (f0 : (forall r, 0 <= r -> 0 <= f r)%R) (mf : measurable_fun setT f) :
  score (measurable_funT_comp mf var2of2)
    (x, r) (curry (snd \o fst) x @^-1` U) =
  (f r)%:E * \d_x.2 U.
Proof. by rewrite /score/= /mscale/= ger0_norm// f0. Qed. *)

Lemma score_score (f : R -> R) (g : R * unit -> R)
    (mf : measurable_fun setT f)
    (mg : measurable_fun setT g) :
  letin (score mf) (score mg) =
  score (measurable_funM mf (measurableT_comp mg (measurable_pair2 tt))).
Proof.
apply/eq_sfkernel => x U.
rewrite {1}/letin; unlock.
by rewrite kcomp_scoreE/= /mscale/= diracE normrM muleA EFinM.
Qed.

(* hard constraints to express score below 1 *)
Lemma score_fail (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
  score (kr r%:num) =
  letin (sample [the probability _ _ of bernoulli r1] : R.-pker T ~> _)
        (ite (macc1of2 R) (ret ktt) fail).
Proof.
apply/eq_sfkernel => x U.
rewrite letinE/= /sample; unlock.
rewrite integral_measure_add//= ge0_integral_mscale//= ge0_integral_mscale//=.
rewrite integral_dirac//= integral_dirac//= !indicT/= !mul1e.
by rewrite /mscale/= iteE//= iteE//= failE mule0 adde0 ger0_norm.
Qed.

End insn1_lemmas.

Section letin_ite.
Context d d2 d3 (T : measurableType d) (T2 : measurableType d2)
  (Z : measurableType d3) (R : realType).
Variables  (k1 k2 : R.-sfker T ~> Z) (u : R.-sfker [the measurableType _ of (T * Z)%type] ~> T2)
  (f : T -> bool) (mf : measurable_fun setT f)
  (t : T) (U : set T2).

Lemma letin_iteT : f t -> letin (ite mf k1 k2) u t U = letin k1 u t U.
Proof.
move=> ftT.
rewrite !letinE/=.
apply: eq_measure_integral => V mV _.
by rewrite iteE ftT.
Qed.

Lemma letin_iteF : ~~ f t -> letin (ite mf k1 k2) u t U = letin k2 u t U.
Proof.
move=> ftF.
rewrite !letinE/=.
apply: eq_measure_integral => V mV _.
by rewrite iteE (negbTE ftF).
Qed.

End letin_ite.

Section letinA.
Context d d' d1 d2 d3 (X : measurableType d) (Y : measurableType d')
  (T1 : measurableType d1) (T2 : measurableType d2) (T3 : measurableType d3)
  (R : realType).
Import Notations.
Variables (t : R.-sfker X ~> T1)
          (u : R.-sfker [the measurableType _ of (X * T1)%type] ~> T2)
          (v : R.-sfker [the measurableType _ of (X * T2)%type] ~> Y)
          (v' : R.-sfker [the measurableType _ of (X * T1 * T2)%type] ~> Y)
          (vv' : forall y, v =1 fun xz => v' (xz.1, y, xz.2)).

Lemma letinA x A : measurable A ->
  letin t (letin u v') x A
  =
  (letin (letin t u) v) x A.
Proof.
move=> mA.
rewrite !letinE.
under eq_integral do rewrite letinE.
rewrite integral_kcomp; [|by []|].
- apply: eq_integral => y _.
  apply: eq_integral => z _.
  by rewrite (vv' y).
exact: (measurableT_comp (measurable_kernel v _ mA)).
Qed.

End letinA.

Section letinC.
Context d d1 d' (X : measurableType d) (Y : measurableType d1)
  (Z : measurableType d') (R : realType).

Import Notations.

Variables (t : R.-sfker Z ~> X)
          (t' : R.-sfker [the measurableType _ of (Z * Y)%type] ~> X)
          (tt' : forall y, t =1 fun z => t' (z, y))
          (u : R.-sfker Z ~> Y)
          (u' : R.-sfker [the measurableType _ of (Z * X)%type] ~> Y)
          (uu' : forall x, u =1 fun z => u' (z, x)).

Definition T z : set X -> \bar R := t z.
Let T0 z : (T z) set0 = 0. Proof. by []. Qed.
Let T_ge0 z x : 0 <= (T z) x. Proof. by []. Qed.
Let T_semi_sigma_additive z : semi_sigma_additive (T z).
Proof. exact: measure_semi_sigma_additive. Qed.
HB.instance Definition _ z := @isMeasure.Build _ R X (T z) (T0 z) (T_ge0 z)
  (@T_semi_sigma_additive z).

Let sfinT z : sfinite_measure (T z). Proof. exact: sfinite_kernel_measure. Qed.
HB.instance Definition _ z := @Measure_isSFinite_subdef.Build _ X R
  (T z) (sfinT z).

Definition U z : set Y -> \bar R := u z.
Let U0 z : (U z) set0 = 0. Proof. by []. Qed.
Let U_ge0 z x : 0 <= (U z) x. Proof. by []. Qed.
Let U_semi_sigma_additive z : semi_sigma_additive (U z).
Proof. exact: measure_semi_sigma_additive. Qed.
HB.instance Definition _ z := @isMeasure.Build _ R Y (U z) (U0 z) (U_ge0 z)
  (@U_semi_sigma_additive z).

Let sfinU z : sfinite_measure (U z). Proof. exact: sfinite_kernel_measure. Qed.
HB.instance Definition _ z := @Measure_isSFinite_subdef.Build _ Y R
  (U z) (sfinU z).

Lemma letinC z A : measurable A ->
  letin t
  (letin u'
  (ret (measurable_fun_prod (macc1of3 R) (macc2of3 R)))) z A =
  letin u
  (letin t'
  (ret (measurable_fun_prod (macc2of3 R) (macc1of3 R)))) z A.
Proof.
move=> mA.
rewrite !letinE.
under eq_integral.
  move=> x _.
  rewrite letinE -uu'.
  under eq_integral do rewrite retE /=.
  over.
rewrite (sfinite_Fubini
  [the {sfinite_measure set X -> \bar R} of T z]
  [the {sfinite_measure set Y -> \bar R} of U z]
  (fun x => \d_(x.1, x.2) A ))//; last first.
  apply/EFin_measurable_fun => /=; rewrite (_ : (fun x => _) = mindic R mA)//.
  by apply/funext => -[].
rewrite /=.
apply: eq_integral => y _.
by rewrite letinE/= -tt'; apply: eq_integral => // x _; rewrite retE.
Qed.

End letinC.

(* sample programs *)

Section constants.
Variable R : realType.
Local Open Scope ring_scope.

Lemma onem1S n : `1- (1 / n.+1%:R) = (n%:R / n.+1%:R)%:nng%:num :> R.
Proof.
by rewrite /onem/= -{1}(@divrr _ n.+1%:R) ?unitfE// -mulrBl -natr1 addrK.
Qed.

Lemma p1S n : (1 / n.+1%:R)%:nng%:num <= 1 :> R.
Proof. by rewrite ler_pdivr_mulr//= mul1r ler1n. Qed.

Lemma p12 : (1 / 2%:R)%:nng%:num <= 1 :> R. Proof. by rewrite p1S. Qed.

Lemma p14 : (1 / 4%:R)%:nng%:num <= 1 :> R. Proof. by rewrite p1S. Qed.

Lemma onem27 : `1- (2 / 7%:R) = (5%:R / 7%:R)%:nng%:num :> R.
Proof. by apply/eqP; rewrite subr_eq/= -mulrDl -natrD divrr// unitfE. Qed.

Lemma p27 : (2 / 7%:R)%:nng%:num <= 1 :> R.
Proof. by rewrite /= lter_pdivr_mulr// mul1r ler_nat. Qed.

End constants.
Arguments p12 {R}.
Arguments p14 {R}.
Arguments p27 {R}.

Section poisson.
Variable R : realType.
Local Open Scope ring_scope.

(* density function for Poisson *)
Definition poisson k r : R := r ^+ k / k`!%:R^-1 * expR (- r).

Lemma poisson_ge0 k r : 0 <= r -> 0 <= poisson k r.
Proof.
move=> r0; rewrite /poisson mulr_ge0 ?expR_ge0//.
by rewrite mulr_ge0// exprn_ge0.
Qed.

Lemma poisson_gt0 k r : 0 < r -> 0 < poisson k.+1 r.
Proof.
move=> r0; rewrite /poisson mulr_gt0 ?expR_gt0//.
by rewrite divr_gt0// ?exprn_gt0// invr_gt0 ltr0n fact_gt0.
Qed.

Lemma mpoisson k : measurable_fun setT (poisson k).
Proof.
by apply: measurable_funM => /=; [exact: measurable_funM|exact: measurableT_comp].
Qed.

Definition poisson3 := poisson 4 3%:R. (* 0.168 *)
Definition poisson10 := poisson 4 10%:R. (* 0.019 *)

End poisson.

Section exponential.
Variable R : realType.
Local Open Scope ring_scope.

(* density function for exponential *)
Definition exp_density x r : R := r * expR (- r * x).

Lemma exp_density_gt0 x r : 0 < r -> 0 < exp_density x r.
Proof. by move=> r0; rewrite /exp_density mulr_gt0// expR_gt0. Qed.

Lemma exp_density_ge0 x r : 0 <= r -> 0 <= exp_density x r.
Proof. by move=> r0; rewrite /exp_density mulr_ge0// expR_ge0. Qed.

Lemma mexp_density x : measurable_fun setT (exp_density x).
Proof.
apply: measurable_funM => //=; apply: measurableT_comp => //.
exact: measurable_funM.
Qed.

End exponential.

Lemma letin_sample_bernoulli d d' (T : measurableType d)
    (T' : measurableType d') (R : realType)(r : {nonneg R}) (r1 : (r%:num <= 1)%R)
    (u : R.-sfker [the measurableType _ of (T * bool)%type] ~> T') x y :
  letin (sample [the probability _ _ of bernoulli r1]) u x y =
  r%:num%:E * u (x, true) y + (`1- (r%:num))%:E * u (x, false) y.
Proof.
rewrite letinE/=.
rewrite ge0_integral_measure_sum// 2!big_ord_recl/= big_ord0 adde0/=.
by rewrite !ge0_integral_mscale//= !integral_dirac//= indicT 2!mul1e.
Qed.

Section sample_and_return.
Import Notations.
Context d (T : measurableType d) (R : realType).

Definition sample_and_return : R.-sfker T ~> _ :=
  letin
    (sample [the probability _ _ of bernoulli p27]) (* T -> B *)
    (ret (macc1of2 R)) (* T * B -> B *).

Lemma sample_and_returnE t U : sample_and_return t U =
  (2 / 7%:R)%:E * \d_true U + (5%:R / 7%:R)%:E * \d_false U.
Proof.
by rewrite /sample_and_return letin_sample_bernoulli !retE onem27.
Qed.

End sample_and_return.

(* trivial example *)
Section sample_and_branch.
Import Notations.
Context d (T : measurableType d) (R : realType).

(* let x = sample (bernoulli (2/7)) in
   let r = case x of {(1, _) => return (k3()), (2, _) => return (k10())} in
   return r *)

Definition sample_and_branch : R.-sfker T ~> mR R :=
  letin
    (sample [the probability _ _ of bernoulli p27]) (* T -> B *)
    (ite (macc1of2 R) (ret k3) (ret k10)).

Lemma sample_and_branchE t U : sample_and_branch t U =
  (2 / 7%:R)%:E * \d_(3%:R : R) U +
  (5%:R / 7%:R)%:E * \d_(10%:R : R) U.
Proof.
by rewrite /sample_and_branch letin_sample_bernoulli/= !iteE !retE onem27.
Qed.

End sample_and_branch.

Section bernoulli_and.
Context d (T : measurableType d) (R : realType).
Import Notations.

Definition mand (x y : T * mbool * mbool -> mbool)
  (t : T * mbool * mbool) : mbool := x t && y t.

Lemma measurable_fun_mand (x y : T * mbool * mbool -> mbool) :
  measurable_fun setT x -> measurable_fun setT y ->
  measurable_fun setT (mand x y).
Proof.
move=> /= mx my; apply: (measurable_fun_bool true).
rewrite [X in measurable X](_ : _ =
    (x @^-1` [set true]) `&` (y @^-1` [set true])); last first.
  by rewrite /mand; apply/seteqP; split => z/= /andP.
apply: measurableI.
- by rewrite -[X in measurable X]setTI; exact: mx.
- by rewrite -[X in measurable X]setTI; exact: my.
Qed.

Definition bernoulli_and : R.-sfker T ~> mbool :=
    (letin (sample [the probability _ _ of bernoulli p12])
     (letin (sample [the probability _ _ of bernoulli p12])
        (ret (measurable_fun_mand (macc1of3 R) (macc2of3 R))))).

Lemma bernoulli_andE t U :
  bernoulli_and t U =
  sample [the probability _ _ of bernoulli p14] t U.
Proof.
rewrite /bernoulli_and 3!letin_sample_bernoulli/= /mand/= muleDr//= -muleDl//.
rewrite !muleA -addeA -muleDl// -!EFinM !onem1S/= -splitr mulr1.
have -> : (1 / 2 * (1 / 2) = 1 / 4%:R :> R)%R by rewrite mulf_div mulr1// -natrM.
rewrite /bernoulli/= measure_addE/= /mscale/= -!EFinM; congr( _ + (_ * _)%:E).
have -> : (1 / 2 = 2 / 4%:R :> R)%R.
  by apply/eqP; rewrite eqr_div// ?pnatr_eq0// mul1r -natrM.
by rewrite onem1S// -mulrDl.
Qed.

End bernoulli_and.

Section staton_bus.
Import Notations.
Context d (T : measurableType d) (R : realType) (h : R -> R).
Hypothesis mh : measurable_fun setT h.
Definition kstaton_bus : R.-sfker T ~> mbool :=
  letin (sample [the probability _ _ of bernoulli p27])
  (letin
    (letin (ite (macc1of2 R) (ret k3) (ret k10))
      (score (measurableT_comp mh (macc2of3 R))))
    (ret (macc1of3 R))).

Definition staton_bus := normalize kstaton_bus.

End staton_bus.

(* let x = sample (bernoulli (2/7)) in
   let r = case x of {(1, _) => return (k3()), (2, _) => return (k10())} in
   let _ = score (1/4! r^4 e^-r) in
   return x *)
Section staton_bus_poisson.
Import Notations.
Context d (T : measurableType d) (R : realType).
Let poisson4 := @poisson R 4%N.
Let mpoisson4 := @mpoisson R 4%N.

Definition kstaton_bus_poisson : R.-sfker (mR R) ~> mbool :=
  kstaton_bus _ mpoisson4.

Let kstaton_bus_poissonE t U : kstaton_bus_poisson t U =
  (2 / 7%:R)%:E * (poisson4 3%:R)%:E * \d_true U +
  (5%:R / 7%:R)%:E * (poisson4 10%:R)%:E * \d_false U.
Proof.
rewrite /kstaton_bus.
rewrite letin_sample_bernoulli.
rewrite -!muleA; congr (_ * _ + _ * _).
- rewrite letin_kret//.
  rewrite letin_iteT//.
  rewrite letin_retk//.
  by rewrite scoreE//= => r r0; exact: poisson_ge0.
- by rewrite onem27.
  rewrite letin_kret//.
  rewrite letin_iteF//.
  rewrite letin_retk//.
  by rewrite scoreE//= => r r0; exact: poisson_ge0.
Qed.

(* true -> 2/7 * 0.168 = 2/7 * 3^4 e^-3 / 4! *)
(* false -> 5/7 * 0.019 = 5/7 * 10^4 e^-10 / 4! *)

Lemma staton_busE P (t : R) U :
  let N := ((2 / 7%:R) * poisson4 3%:R +
            (5%:R / 7%:R) * poisson4 10%:R)%R in
  staton_bus mpoisson4 P t U =
  ((2 / 7%:R)%:E * (poisson4 3%:R)%:E * \d_true U +
   (5%:R / 7%:R)%:E * (poisson4 10%:R)%:E * \d_false U) * N^-1%:E.
Proof.
rewrite /staton_bus normalizeE /= !kstaton_bus_poissonE !diracT !mule1 ifF //.
apply/negbTE; rewrite gt_eqF// lte_fin.
by rewrite addr_gt0// mulr_gt0//= ?divr_gt0// ?ltr0n// poisson_gt0// ltr0n.
Qed.

End staton_bus_poisson.

(* let x = sample (bernoulli (2/7)) in
   let r = case x of {(1, _) => return (k3()), (2, _) => return (k10())} in
   let _ = score (r e^-(15/60 r)) in
   return x *)
Section staton_bus_exponential.
Import Notations.
Context d (T : measurableType d) (R : realType).
Let exp1560 := @exp_density R (ratr (15%:Q / 60%:Q)).
Let mexp1560 := @mexp_density R (ratr (15%:Q / 60%:Q)).

(* 15/60 = 0.25 *)

Definition kstaton_bus_exponential : R.-sfker (mR R) ~> mbool :=
  kstaton_bus _ mexp1560.

Let kstaton_bus_exponentialE t U : kstaton_bus_exponential t U =
  (2 / 7%:R)%:E * (exp1560 3%:R)%:E * \d_true U +
  (5%:R / 7%:R)%:E * (exp1560 10%:R)%:E * \d_false U.
Proof.
rewrite /kstaton_bus.
rewrite letin_sample_bernoulli.
rewrite -!muleA; congr (_ * _ + _ * _).
- rewrite letin_kret//.
  rewrite letin_iteT//.
  rewrite letin_retk//.
  rewrite scoreE//= => r r0; exact: exp_density_ge0.
- by rewrite onem27.
  rewrite letin_kret//.
  rewrite letin_iteF//.
  rewrite letin_retk//.
  by rewrite scoreE//= => r r0; exact: exp_density_ge0.
Qed.

(* true -> 5/7 * 0.019 = 5/7 * 10^4 e^-10 / 4! *)
(* false -> 2/7 * 0.168 = 2/7 * 3^4 e^-3 / 4! *)

Lemma staton_bus_exponentialE P (t : R) U :
  let N := ((2 / 7%:R) * exp1560 3%:R +
            (5%:R / 7%:R) * exp1560 10%:R)%R in
  staton_bus mexp1560 P t U =
  ((2 / 7%:R)%:E * (exp1560 3%:R)%:E * \d_true U +
   (5%:R / 7%:R)%:E * (exp1560 10%:R)%:E * \d_false U) * N^-1%:E.
Proof.
rewrite /staton_bus.
rewrite normalizeE /= !kstaton_bus_exponentialE !diracT !mule1 ifF //.
apply/negbTE; rewrite gt_eqF// lte_fin.
by rewrite addr_gt0// mulr_gt0//= ?divr_gt0// ?ltr0n// exp_density_gt0 ?ltr0n.
Qed.

End staton_bus_exponential.

Section mswap.
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3) (R : realType).
Variable k : R.-ker [the measurableType _ of (Y * X)%type] ~> Z.

Definition mswap xy U := k (swap xy) U.

Let mswap0 xy : mswap xy set0 = 0.
Proof. done. Qed.

Let mswap_ge0 x U : 0 <= mswap x U.
Proof. done. Qed.

Let mswap_sigma_additive x : semi_sigma_additive (mswap x).
Proof. exact: measure_semi_sigma_additive. Qed.

HB.instance Definition _ x := isMeasure.Build _ R _
  (mswap x) (mswap0 x) (mswap_ge0 x) (@mswap_sigma_additive x).

Definition mkswap : _ -> {measure set Z -> \bar R} :=
  fun x => [the measure _ _ of mswap x].

Let measurable_fun_kswap U :
  measurable U -> measurable_fun setT (mkswap ^~ U).
Proof.
move=> mU.
rewrite [X in measurable_fun _ X](_ : _ = ((fun xy => k xy U) \o (@swap _ _)))//.
apply measurableT_comp => //=.
  exact/measurable_kernel.
exact: measurable_swap.
Qed.

HB.instance Definition _ :=
  isKernel.Build _ _ [the measurableType _ of (X * Y)%type] Z R mkswap measurable_fun_kswap.

End mswap.

Section mswap_sfinite_kernel.
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3) (R : realType).
Variable k : R.-sfker [the measurableType _ of (Y * X)%type] ~> Z.

(* Import KSWAP_FINITE_KERNEL. *)

Let mkswap_sfinite :
  exists2 k_ : (R.-ker [the measurableType _ of (X * Y)%type] ~> Z)^nat,
  forall n, measure_fam_uub (k_ n) &
  forall x U, measurable U -> mkswap k x U = kseries k_ x U.
Proof.
have [k_ /= kE] := sfinite_kernel k.
exists (fun n => [the R.-ker _ ~> _ of mkswap (k_  n)]).
  move=> n.
  have /measure_fam_uubP[M hM] := measure_uub (k_ n).
  by exists M%:num => x/=; exact: hM.
move=> xy U mU.
by rewrite /mswap/= kE.
Qed.

HB.instance Definition _ :=
  Kernel_isSFinite_subdef.Build _ _ _ Z R (mkswap k) mkswap_sfinite.

End mswap_sfinite_kernel.

(* Module KSWAP_FINITE_KERNEL. *)

Section kswap_finite_kernel_finite.
Context d d' d3 (X : measurableType d) (Y : measurableType d')
  (Z : measurableType d3) (R : realType)
  (k : R.-fker [the measurableType _ of (Y * X)%type] ~> Z).

Let mkswap_finite : measure_fam_uub (mkswap k).
Proof.
have /measure_fam_uubP[r hr] := measure_uub k.
apply/measure_fam_uubP; exists (PosNum [gt0 of r%:num%R]) => x /=.
exact: hr.
Qed.

HB.instance Definition _ :=
  Kernel_isFinite.Build _ _ _ Z R (mkswap k) mkswap_finite.

End kswap_finite_kernel_finite.
(* End KSWAP_FINITE_KERNEL. *)

(* Module MSWAP_SFINITE_KERNEL. *)

Reserved Notation "f .; g" (at level 60, right associativity,
  format "f  .; '/ '  g").

Notation "l .; k" := (mkcomp l [the _.-ker _ ~> _ of mkswap k]) : ereal_scope.

(* TODO: move to kernel.v *)

Section letin'.
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3) (R : realType).

Definition letin' (l : R.-sfker X ~> Y)
    (k : R.-sfker [the measurableType (d', d).-prod of (Y * X)%type] ~> Z) :=
  locked [the R.-sfker X ~> Z of l .; k].

Lemma letin'E (l : R.-sfker X ~> Y)
    (k : R.-sfker [the measurableType (d', d).-prod of (Y * X)%type] ~> Z) x U :
  letin' l k x U = \int[l x]_y k (y, x) U.
Proof. by rewrite /letin'; unlock. Qed.

End letin'.

Section letin'A.
Context d d' d1 d2 d3 (X : measurableType d) (Y : measurableType d')
  (T1 : measurableType d1) (T2 : measurableType d2) (T3 : measurableType d3)
  (R : realType).
Import Notations.
Variables (t : R.-sfker X ~> T1)
          (u : R.-sfker [the measurableType _ of (T1 * X)%type] ~> T2)
          (v : R.-sfker [the measurableType _ of (T2 * X)%type] ~> Y)
          (v' : R.-sfker [the measurableType _ of (T2 * (T1 * X))%type] ~> Y)
          (vv' : forall y, v =1 fun xz => v' (xz.1, (y, xz.2))).

Lemma letin'A x A : measurable A ->
  letin' t (letin' u v') x A
  =
  (letin' (letin' t u) v) x A.
Proof.
move=> mA.
rewrite !letin'E.
under eq_integral do rewrite letin'E.
rewrite /letin'; unlock.
rewrite integral_kcomp; [|by []|].
  apply: eq_integral => z _.
  apply: eq_integral => y _.
  by rewrite (vv' z).
exact: measurableT_comp (@measurable_kernel _ _ _ _ _ v _ mA) _.
Qed.

End letin'A.

Section letin'C.
Context d d1 d' (X : measurableType d) (Y : measurableType d1)
  (Z : measurableType d') (R : realType).

Import Notations.

Lemma letin'C12 z A : measurable A ->
  @letin' _ _ _ _ _ _ R (ret (kr 1)) (letin' (ret (kb true)) (ret (measurable_fun_prod (@macc R [:: sbool; sreal] 1) (@macc R [:: sbool; sreal] 0)))) z A =
  letin' (ret (kb true)) (letin' (ret (kr 1)) (ret (measurable_fun_prod (@macc R [:: sreal; sbool] 0) (@macc R [:: sreal; sbool] 1)))) z A.
Proof.
move=> mA.
have : acc [:: sbool; sreal] 1 = acc [:: sbool; sreal] 1.
rewrite /acc /=.
(* rewrite !letin'E. *)
Admitted.

Variables (t : R.-sfker Z ~> X)
          (u' : R.-sfker [the measurableType _ of (X * Z)%type] ~> Y)
          (u : R.-sfker Z ~> Y)
          (t' : R.-sfker [the measurableType _ of (Y * Z)%type] ~> X)
          (tt' : forall y, t =1 fun z => t' (y, z))
          (uu' : forall x, u =1 fun z => u' (x, z)).

Definition T' z : set X -> \bar R := t z.
Let T0 z : (T' z) set0 = 0. Proof. by []. Qed.
Let T_ge0 z x : 0 <= (T' z) x. Proof. by []. Qed.
Let T_semi_sigma_additive z : semi_sigma_additive (T' z).
Proof. exact: measure_semi_sigma_additive. Qed.
HB.instance Definition _ z := @isMeasure.Build _ R X (T' z) (T0 z) (T_ge0 z)
  (@T_semi_sigma_additive z).

Let sfinT z : sfinite_measure (T' z). Proof. exact: sfinite_kernel_measure. Qed.
HB.instance Definition _ z := @Measure_isSFinite_subdef.Build _ X R
  (T' z) (sfinT z).

Definition U' z : set Y -> \bar R := u z.
Let U0 z : (U' z) set0 = 0. Proof. by []. Qed.
Let U_ge0 z x : 0 <= (U' z) x. Proof. by []. Qed.
Let U_semi_sigma_additive z : semi_sigma_additive (U' z).
Proof. exact: measure_semi_sigma_additive. Qed.
HB.instance Definition _ z := @isMeasure.Build _ R Y (U' z) (U0 z) (U_ge0 z)
  (@U_semi_sigma_additive z).

Let sfinU z : sfinite_measure (U' z). Proof. exact: sfinite_kernel_measure. Qed.
HB.instance Definition _ z := @Measure_isSFinite_subdef.Build _ Y R
  (U' z) (sfinU z).

Check (ret (measurable_fun_prod (macc (R := R) [:: sconst (existT _ _ Y); sconst (existT _ _ X); sconst (existT _ _ Z)] 1) (macc (R := R) [:: sconst (existT _ _ Y); sconst (existT _ _ X); sconst (existT _ _ Z)] 0))).

Check (ret (kr 1)) : R.-sfker munit ~> mR R.

Lemma letin'C z A : measurable A ->
  letin' t
  (letin' u'
  (ret (measurable_fun_prod (macc1of3' R) (macc0of3' R)))) z A =
  letin' u
  (letin' t'
  (ret (measurable_fun_prod (macc0of3' R) (macc1of3' R)))) z A.
Proof.
move=> mA.
rewrite !letin'E.
under eq_integral.
  move=> x _.
  rewrite letin'E -uu'.
  under eq_integral do rewrite retE /=.
  over.
rewrite (sfinite_Fubini
  [the {sfinite_measure set X -> \bar R} of T' z]
  [the {sfinite_measure set Y -> \bar R} of U' z]
  (fun x => \d_(x.1, x.2) A ))//; last first.
  apply/EFin_measurable_fun => /=; rewrite (_ : (fun x => _) = mindic R mA)//.
  by apply/funext => -[].
rewrite /=.
apply: eq_integral => y _.
by rewrite letin'E/= -tt'; apply: eq_integral => // x _; rewrite retE.
Qed.

End letin'C.

Arguments letin'C {d d1 d' X Y Z R} _ _ _ _.
