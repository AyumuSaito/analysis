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

Notation var1of3' := (@measurable_fun_fst _ _ _ _).
Notation var2of3' := (measurable_fun_comp (@measurable_fun_fst _ _ _ _) (@measurable_fun_snd _ _ _ _)).
Notation var3of3' := (measurable_fun_comp (@measurable_fun_fst _ _ _ _) (measurable_fun_comp (@measurable_fun_snd _ _ _ _) (@measurable_fun_snd _ _ _ _))).

Notation var1of4' := (@measurable_fun_fst _ _ _ _).
Notation var2of4' := (measurable_fun_comp (@measurable_fun_fst _ _ _ _) (@measurable_fun_snd _ _ _ _)).
Notation var3of4' := (measurable_fun_comp (@measurable_fun_fst _ _ _ _) (measurable_fun_comp (@measurable_fun_snd _ _ _ _) (@measurable_fun_snd _ _ _ _))).
Notation var4of4' := (measurable_fun_comp (@measurable_fun_fst _ _ _ _) (measurable_fun_comp (@measurable_fun_snd _ _ _ _) (measurable_fun_comp (@measurable_fun_snd _ _ _ _) (@measurable_fun_snd _ _ _ _)))).

Section kcomp'_def.
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3) (R : realType).
Variable l : X -> {measure set Y -> \bar R}.
Variable k : (Y * X)%type -> {measure set Z -> \bar R}.

Definition kcomp' x U := \int[l x]_y k (y, x) U.

End kcomp'_def.

Section kcomp_is_measure.
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3) (R : realType).
Variable l : R.-ker X ~> Y.
Variable k : R.-ker [the measurableType _ of (Y * X)%type] ~> Z.

Local Notation "l \; k" := (kcomp' l k).

Let kcomp0 x : (l \; k) x set0 = 0.
Proof.
by rewrite /kcomp' (eq_integral (cst 0)) ?integral0// => y _; rewrite measure0.
Qed.

Let kcomp_ge0 x U : 0 <= (l \; k) x U. Proof. exact: integral_ge0. Qed.

Let kcomp_sigma_additive x : semi_sigma_additive ((l \; k) x).
Proof.
move=> U mU tU mUU; rewrite [X in _ --> X](_ : _ =
  \int[l x]_y (\sum_(n <oo) k (y, x) (U n))); last first.
  apply: eq_integral => V _.
  by apply/esym/cvg_lim => //; exact/measure_semi_sigma_additive.
apply/cvg_closeP; split.
  by apply: is_cvg_nneseries => n _; exact: integral_ge0.
rewrite closeE // integral_nneseries// => n.
by have /measurable_fun_prod2 := measurable_kernel k _ (mU n).
Qed.

HB.instance Definition _ x := isMeasure.Build _ R _
  ((l \; k) x) (kcomp0 x) (kcomp_ge0 x) (@kcomp_sigma_additive x).

Definition mkcomp' : X -> {measure set Z -> \bar R} :=
  fun x => [the measure _ _ of (l \; k) x].

End kcomp_is_measure.

Notation "l \; k" := (mkcomp' l k) : ereal_scope.

Module KCOMP_FINITE_KERNEL.

Section measurable_fun_xsection_finite_kernel.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d')
          (R : realType).
Variables (k : R.-fker X ~> Y).
Implicit Types A : set (Y * X).

Let phi A := fun x => k x (ysection A x).
Let XY := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma measurable_fun_ysection_finite_kernel A :
  A \in measurable -> measurable_fun setT (phi A).
Admitted.

End measurable_fun_xsection_finite_kernel.

Section measurable_fun_integral_finite_sfinite.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d')
  (R : realType).
Variable k : Y * X -> \bar R.

Lemma measurable_fun_ysection_integral
    (l : X -> {measure set Y -> \bar R})
    (k_ : ({nnsfun [the measurableType _ of (Y * X)%type] >-> R})^nat)
    (ndk_ : nondecreasing_seq (k_ : (Y * X -> R)^nat))
    (k_k : forall z, EFin \o (k_ ^~ z) --> k z) :
  (forall n r, measurable_fun setT (fun x => l x (ysection (k_ n @^-1` [set r]) x))) ->
  measurable_fun setT (fun x => \int[l x]_y k (y, x)).
Admitted.

Lemma measurable_fun_integral_finite_kernel (l : R.-fker X ~> Y)
    (k0 : forall z, 0 <= k z) (mk : measurable_fun setT k) :
  measurable_fun setT (fun x => \int[l x]_y k (y, x)).
Proof.
have [k_ [ndk_ k_k]] := approximation measurableT mk (fun x _ => k0 x).
apply: (measurable_fun_ysection_integral ndk_ (k_k ^~ Logic.I)) => n r.
have [l_ hl_] := measure_uub l.
by apply: measurable_fun_ysection_finite_kernel => // /[!inE].
Qed.

Lemma measurable_fun_integral_sfinite_kernel (l : R.-sfker X ~> Y)
    (k0 : forall t, 0 <= k t) (mk : measurable_fun setT k) :
  measurable_fun setT (fun x => \int[l x]_y k (y, x)).
Proof.
have [k_ [ndk_ k_k]] := approximation measurableT mk (fun xy _ => k0 xy).
apply: (measurable_fun_ysection_integral ndk_ (k_k ^~ Logic.I)) => n r.
have [l_ hl_] := sfinite l.
rewrite (_ : (fun x => _) =
    (fun x => mseries (l_ ^~ x) 0 (ysection (k_ n @^-1` [set r]) x))); last first.
  by apply/funext => x; rewrite hl_//; exact/measurable_ysection.
apply: ge0_emeasurable_fun_sum => // m.
by apply: measurable_fun_ysection_finite_kernel => // /[!inE].
Qed.

End measurable_fun_integral_finite_sfinite.

Arguments measurable_fun_ysection_integral {_ _ _ _ _} k l.
Arguments measurable_fun_integral_finite_kernel {_ _ _ _ _} k l.
Arguments measurable_fun_integral_sfinite_kernel {_ _ _ _ _} k l.

Section kcomp_finite_kernel_kernel.
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3) (R : realType).
Variables (l : R.-fker X ~> Y)
          (k : R.-ker [the measurableType _ of (Y * X)%type] ~> Z).

Lemma measurable_fun_kcomp_finite U :
  measurable U -> measurable_fun setT ((l \; k) ^~ U).
Proof.
move=> mU; apply: (measurable_fun_integral_finite_kernel (k ^~ U)) => //.
exact/measurable_kernel.
Qed.

HB.instance Definition _ :=
  isKernel.Build _ _ X Z R (l \; k) measurable_fun_kcomp_finite.

End kcomp_finite_kernel_kernel.

Section kcomp_finite_kernel_finite.
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3) (R : realType).
Variable l : R.-fker X ~> Y.
Variable k : R.-fker [the measurableType _ of (Y * X)%type] ~> Z.

Import Order.TTheory.

Let mkcomp_finite : measure_fam_uub (l \; k).
Proof.
have /measure_fam_uubP[r hr] := measure_uub k.
have /measure_fam_uubP[s hs] := measure_uub l.
apply/measure_fam_uubP; exists (PosNum [gt0 of (r%:num * s%:num)%R]) => x /=.
apply: (@le_lt_trans _ _ (\int[l x]__ r%:num%:E)).
  apply: ge0_le_integral => //.
  - have /measurable_fun_prod2 := measurable_kernel k _ measurableT.
    exact.
  - exact/measurable_fun_cst.
  - by move=> y _; exact/ltW/hr.
by rewrite integral_cst//= EFinM lte_pmul2l.
Qed.

HB.instance Definition _ :=
  Kernel_isFinite.Build _ _ X Z R (l \; k) mkcomp_finite.

End kcomp_finite_kernel_finite.
End KCOMP_FINITE_KERNEL.

Section kcomp_sfinite_kernel.
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3) (R : realType).
Variable l : R.-sfker X ~> Y.
Variable k : R.-sfker [the measurableType _ of (Y * X)%type] ~> Z.

Import KCOMP_FINITE_KERNEL.

Lemma mkcomp_sfinite : exists k_ : (R.-fker X ~> Z)^nat, forall x U, measurable U ->
  (l \; k) x U = kseries k_ x U.
Proof.
have [k_ hk_] := sfinite k; have [l_ hl_] := sfinite l.
have [kl hkl] : exists kl : (R.-fker X ~> Z) ^nat, forall x U,
    \esum_(i in setT) (l_ i.2 \; k_ i.1) x U = \sum_(i <oo) kl i x U.
  have /ppcard_eqP[f] : ([set: nat] #= [set: nat * nat])%card.
    by rewrite card_eq_sym; exact: card_nat2.
  exists (fun i => [the _.-fker _ ~> _ of l_ (f i).2 \; k_ (f i).1]) => x U.
  by rewrite (reindex_esum [set: nat] _ f)// nneseries_esum// fun_true.
exists kl => x U mU.
transitivity (([the _.-ker _ ~> _ of kseries l_] \;
               [the _.-ker _ ~> _ of kseries k_]) x U).
  rewrite /= /kcomp' [in RHS](eq_measure_integral (l x)); last first.
    by move=> *; rewrite hl_.
  by apply: eq_integral => y _; rewrite hk_.
rewrite /= /kcomp'/= integral_nneseries//=; last first.
  by move=> n; have /measurable_fun_prod2 := measurable_kernel (k_ n) _ mU; exact.
transitivity (\sum_(i <oo) \sum_(j <oo) (l_ j \; k_ i) x U).
  apply: eq_eseries => i _; rewrite integral_kseries//.
  by have /measurable_fun_prod2 := measurable_kernel (k_ i) _ mU; exact.
rewrite /mseries -hkl/=.
rewrite (_ : setT = setT `*`` (fun=> setT)); last by apply/seteqP; split.
rewrite -(@esum_esum _ _ _ _ _ (fun i j => (l_ j \; k_ i) x U))//.
rewrite nneseries_esum; last by move=> n _; exact: nneseries_ge0.
by rewrite fun_true; apply: eq_esum => /= i _; rewrite nneseries_esum// fun_true.
Qed.

Lemma measurable_fun_mkcomp_sfinite U : measurable U ->
  measurable_fun setT ((l \; k) ^~ U).
Proof.
move=> mU; apply: (measurable_fun_integral_sfinite_kernel (k ^~ U)) => //.
exact/measurable_kernel.
Qed.

End kcomp_sfinite_kernel.

Module KCOMP_SFINITE_KERNEL.

Section kcomp_sfinite_kernel.
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3) (R : realType).
Variable l : R.-sfker X ~> Y.
Variable k : R.-sfker [the measurableType _ of (Y * X)%type] ~> Z.

HB.instance Definition _ :=
  isKernel.Build _ _ X Z R (l \; k) (measurable_fun_mkcomp_sfinite l k).

#[export]
HB.instance Definition _ :=
  Kernel_isSFinite.Build _ _ X Z R (l \; k) (mkcomp_sfinite l k).

End kcomp_sfinite_kernel.
End KCOMP_SFINITE_KERNEL.
HB.export KCOMP_SFINITE_KERNEL.

Section letin'.
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3) (R : realType).
Definition letin' (l : R.-sfker X ~> Y)
    (k : R.-sfker [the measurableType (d', d).-prod of (Y * X)%type] ~> Z) :=
  locked [the R.-sfker X ~> Z of l \; k].

Lemma letin'E (l : R.-sfker X ~> Y)
    (k : R.-sfker [the measurableType (d', d).-prod of (Y * X)%type] ~> Z) x U :
  letin' l k x U = \int[l x]_y k (y, x) U.
Proof. by rewrite /letin'; unlock. Qed.

End letin'.

Section type_syntax.
Variables (R : realType).


Section string_eq.

Definition string_eqMixin := @EqMixin string eqb eqb_spec.
Canonical string_eqType := EqType string string_eqMixin.

End string_eq.

Local Obligation Tactic := idtac.
Program Fixpoint prod_meas (l : list {d & measurableType d}) : {d & measurableType d} :=
  match l with
  | [::] => existT measurableType _ munit 
  | h :: t =>
    let t' := prod_meas t in
    existT _ _ _
  end.
Next Obligation.
move=> ? l h t htl t'.
exact: (measure_prod_display (projT1 h, projT1 t')).
Defined.
Next Obligation.
move=> ? l h t htl t'.
simpl.
exact: [the measurableType _ of (projT2 h * projT2 t')%type].
Defined.

Inductive types :=
| units : types
| bools : types
| reals : types
| pairs : types -> types -> types
| probs : types -> types
| prods : list types -> types.

Fixpoint typei (t : types) : {d & measurableType d} :=
  match t with
  | units => existT _ _ munit
  | bools => existT _ _ mbool
  | reals => existT _ _ (mR R)
  | pairs A B => existT _ _
      [the measurableType ((projT1 (typei A),projT1 (typei B)).-prod)%mdisp of (projT2 (typei A) * projT2 (typei B))%type]
  | probs A => existT _ _ (pprobability (projT2 (typei A)) R)
  | prods l => prod_meas (map typei l) 
  end.

Definition typei2 (t : types) := projT2 (typei t).

End type_syntax.

Arguments typei {R}.
Arguments typei2 {R}.

Section context.
Definition context := seq (string * types)%type.
End context.

Section expr.
Variables (R : realType).
Inductive expD : types -> Type :=
| exp_unit : expD units
| exp_bool : bool -> expD bools
| exp_real : R -> expD reals
| exp_pair : forall t1 t2, expD t1 -> expD t2 -> expD (pairs t1 t2)
| exp_var  : forall l (x : string),
    x \in map fst l ->
    (* i = seq.index x (map fst l) -> *)
    expD (nth units (map snd l) (seq.index x (map fst l)))
(* | exp_var (x : string) :  x \in (map fst l) -> expD (nth units (map snd l) (seq.index x (map fst l))) *)
(* | exp_plus : expD -> expD -> expD *)
(* | val_unif : val *)
| exp_bernoulli {r : {nonneg R}} {r1 : (r%:num <= 1)%R} : expD (probs  bools)
| exp_poisson : nat -> expD reals -> expD reals
| exp_norm : forall t, expP t -> expD (probs t)
(* | exp_if : forall z, expD -> exp z -> exp z -> exp z *)
with expP : types -> Type :=
| exp_if : forall t, expD bools -> expP t -> expP t -> expP t
| exp_letin : forall t1 t2 (x : string), expP t1 -> expP t2 -> expP t2
| exp_sample : forall t, expD (probs t) -> expP t
| exp_score : expD reals -> expP units
| exp_return : forall t, expD t -> expP t
.

End expr.

Arguments expD {R}.
Arguments expP {R}.
Arguments exp_unit {R}.
Arguments exp_bool {R}.
Arguments exp_real {R}.
Arguments exp_pair {R _ _}.
Arguments exp_var {R _}.
Arguments exp_bernoulli {R}.
Arguments exp_poisson {R}.
Arguments exp_norm {R _}.
Arguments exp_if {R _}.
Arguments exp_letin {R _ _}.
Arguments exp_sample {R _}.
Arguments exp_score {R}.
Arguments exp_return {R _}.

Section eval.
Variables (R : realType).

Definition varof2 (l : context) (i : nat) (li : (i < size l)%nat) :
  projT2 (@typei R (prods (map snd l))) ->
  projT2 (@typei R (nth units (map snd l : seq types) i)).
  (* projT2 (nth (existT _ _ munit) (map (typei \o snd) l) i). *)
revert l i li.
fix H 1.
destruct l.
  by destruct i.
destruct i.
simpl => _.
intro K.
exact: K.1.
simpl.
move=> il.
move=> K.
refine (H _ _ _ K.2).
exact il.
Defined.

Definition varof3 (l l0 : context) (x : string) (lx : x \in map fst l) (lx0 : x \in map fst l0) :
  projT2 (@typei R (prods (map snd l0))) ->
  projT2 (@typei R (nth units (map snd l : seq types) (seq.index x (map fst l)))).
Admitted.

Lemma false_index_size2 (x : string) (l : context) (H : x \in (map fst l)) :
	(seq.index x (map fst l) < size l)%nat.
Proof. by rewrite -(size_map fst) index_mem. Qed.

Lemma mvarof2 (l : context) (i : nat) (li : (i < size l)%nat) :
  measurable_fun setT (@varof2 l i li).
Proof.
revert l i li.
induction l.
  by destruct i.
destruct i.
simpl => _.
intro K.
exact: measurable_fun_fst.
move=> il K.
apply: (measurable_fun_comp (IHl _ _) (@measurable_fun_snd _ _ _ _)).
apply: K.
Qed.

Lemma mvarof3 (l l0 : context) (x : string) (lx : x \in map fst l) (lx0 : x \in map fst l0) :
  measurable_fun setT (@varof3 l l0 x lx lx0).
Proof.
Admitted.

Lemma measurable_fun_knormalize d d' (X : measurableType d) (Y : measurableType d') (k : R.-sfker X ~> Y) U :
  measurable U -> measurable_fun setT (knormalize k ^~ U).
Proof.
apply: measurable_kernel.
Qed.

Lemma measurable_fun_normalize d d' (X : measurableType d) (Y : measurableType d') (k : R.-sfker X ~> Y) :
  measurable_fun setT (normalize k : X -> pprobability Y R).
Proof.
move=> mX U mU.
rewrite setTI.
(* 
apply: measurability.
reflexivity.
move=> B [Z [r r01]] [Z0 mZ0 <-{Z}] <-{B}.
rewrite /normalize.
rewrite /mnormalize.
rewrite setTI.
rewrite [X in measurable X](_ : _ = (fun x : X =>
   
                            if (k x [set: Y] == 0) || (k x [set: Y] == +oo)
                            then fun U : set Y =>point U
                            else fun U : set Y => k x U * ((fine (k x [set: Y]))^-1)%:E) @^-1`
   [set mu | mu Z0 < r%:E]); last first.
  apply/funext => x/=.
  rewrite /mset/= /mnormalize.
  admit.
 apply: measurable_fun_if.
  reflex
  
  ivity.
  done.



simpl.
rewe
move=> _ B.
rewrite /pset/= => hB.



 => _ /= -[_ [r ->] <-].
(* apply: (measurability (ErealGenInftyO.measurableE R)). *)
apply: measurability => //.
apply: measurableI => //.
apply: measurable_fun_knormalize.
have := measurable_kernel [the kernel _ _ _ of (normalize k : X -> pprobability Y R)]. *)
(* rewrite preimage. *)
Admitted.

(* Fixpoint denoteType (t : types) (e : @expD t) :=
  match e with
  | exp_unit => units
  | exp_bool _ => bools
  | exp_real R _ => reals
  | exp_pair _ _ e1 e2 => pairs (denoteType e1) (denoteType e2)
  | exp_var l x => nth units (map snd l) (seq.index x (map fst l))
  end. *)

(* Fixpoint execD (l : context) (t : types) (e : expD t) 
  : {f : @typei2 R (prods (map snd l)) -> typei2 (denoteType e) & measurable_fun _ f} :=
  match e return {f : @typei2 R (prods (map snd l)) -> typei2 (denoteType e) & measurable_fun _ f} with
  | exp_unit => existT _ (cst tt) ktt
  | exp_bool b => existT _ (cst b) (kb b)
  | exp_real r => existT _ (cst r) (kr r)
  | exp_pair _ _ e1 e2 => 
    existT _ _ (@measurable_fun_pair _ _ _ _ _ _ _ _ (projT2 (execD l e1)) (projT2 (execD l e2)))
  | exp_var l x => forall (H : x \in (map fst l)),
    existT _ (@varof2 l (seq.index x (map fst l)) (false_index_size2 H)) (@mvarof2 l (seq.index x (map fst l)) (false_index_size2 H))
  end. *)

Inductive evalD : forall (l : context) 
(* (G := prod_meas (map snd l)) *)
    (T : types) (e : @expD R T) 
    (* (el : (freevarsD e <= size l)%nat) *)
    (f : projT2 (typei (prods (map (snd) l))) -> projT2 (typei T)), measurable_fun setT f -> Prop :=
| E_unit : forall l, 
  @evalD l units exp_unit (cst tt) ktt

| E_bool : forall l b, 
  @evalD l bools (exp_bool b) (cst b) (kb b)

| E_real : forall l r, 
  @evalD l reals (exp_real r) (cst r) (kr r)

| E_pair : forall l (G := prods (map (snd) l)) A B e1 f1 mf1 e2 f2 mf2,
  @evalD l A e1 (f1 : projT2 (typei G) -> projT2 (typei A)) mf1 ->
  @evalD l B e2 (f2 : projT2 (typei G) -> projT2 (typei B)) mf2 ->
  @evalD l (pairs A B) (exp_pair e1 e2)
    ((fun x : projT2 (typei G) => (f1 x, f2 x)) : projT2 (typei G) -> projT2 (typei (pairs A B))) 
    (@measurable_fun_pair _ _ _ (projT2 (typei G)) (projT2 (typei A)) (projT2 (typei B)) f1 f2 mf1 mf2)

| E_var : forall (l : context) (x : string) (H : x \in (map fst l)),
  let i := seq.index x (map fst l) in
  (* @evalD _ [the measurableType _ of (T1 * T2)%type] l _ _ (exp_var x) (proj1_sig (var_i_of2 i.+1)) (proj2_sig (var_i_of2 i.+1)) *)
  @evalD l _ (exp_var x H) (@varof3 l l x H H)
  (@mvarof3 l l x H H)

| E_bernoulli : forall l (r : {nonneg R}) (r1 : (r%:num <= 1)%R),
  @evalD l (probs bools) (exp_bernoulli r r1) (cst [the probability _ _ of bernoulli r1]) (measurable_fun_cst _)

| E_poisson : forall l k e f mf,
  @evalD l reals e f mf ->
  @evalD l reals (exp_poisson k e) (poisson k \o f) 
  (measurable_fun_comp (mpoisson k) mf)

| E_norm : forall l (T : types) (e : expP T) (k : R.-sfker _ ~> projT2 (typei T)),
  @evalP l T e k ->
  @evalD l (probs T) (exp_norm e)
  (normalize k : _ -> pprobability _ _) 
  (measurable_fun_normalize k)

with evalP : forall (l : context) (T : types),
  expP T ->
  R.-sfker (projT2 (typei (prods (map (snd) l)))) ~> projT2 (typei T) ->
  Prop :=
| E_sample : forall l (T : types) (e : expD (probs T)) (p : pprobability (projT2 (typei T)) R),
  @evalD l (probs T) e (cst p) (measurable_fun_cst p) ->
  @evalP l T (exp_sample e) (sample p)

| E_ifP : forall l T e1 f1 mf e2 k2 e3 k3,
  @evalD l bools e1 f1 mf ->
  @evalP l T e2 k2 ->
  @evalP l T e3 k3 ->
  @evalP l T (exp_if e1 e2 e3) (ite mf k2 k3)

| E_score : forall l (G := prods (map snd l)) e (f : projT2 (typei G) -> R)
(mf : measurable_fun _ f),
  @evalD l reals e f mf ->
  @evalP l units (exp_score e) [the R.-sfker _ ~> _ of kscore mf]

| E_return : forall l T e (f : _ -> _) (mf : measurable_fun _ f),
  @evalD l _ e f mf ->
  @evalP l T (exp_return e) (ret mf)

| E_letin : forall (l : context) (G := prods (map snd l)) (Y Z : types) (x : string) (e1 : expP Y) (e2 : expP Z)
  (k1 : R.-sfker projT2 (typei G) ~> projT2 (typei Y))
  (k2 : R.-sfker (typei2 (pairs Y G)) ~> projT2 (typei Z)) ,
  @evalP l Y e1 k1 ->
  (* l' = ((x, Y) :: l) -> *)
  @evalP ((x,Y)::l)%SEQ Z e2 k2 ->
  @evalP l Z (exp_letin x e1 e2) (letin' k1 k2)
.

End eval.

Section inj_f.
Lemma inj_f A B (f g : A -> B) x : f = g -> f x = g x.
Proof. by move=> ->. Qed.

(* Variable (_A _B : Type) (a b : _A). *)
Lemma inj_cst (A : pointedType) B b1 b2 : (@cst A B b1) = cst b2 -> b1 = b2.
Proof. by move/(congr1 (fun f => f point)). Qed.

End inj_f.

Section eval_prop.
Variables (R : realType).

Ltac inj H := apply Classical_Prop.EqdepTheory.inj_pair2 in H.

Scheme evalD_mut_ind := Induction for evalD Sort Prop
with evalP_mut_ind := Induction for evalP Sort Prop.

Scheme expD_mut_ind := Induction for expD Sort Prop
with expP_mut_ind := Induction for expP Sort Prop.

Lemma evalD_uniq (l : context) (G := prods (map (snd) l)) (T : types) (e : expD T) (u v : projT2 (typei G) -> projT2 (typei T)) (mu : measurable_fun _ u) (mv : measurable_fun _ v) :
  @evalD R l T e u mu -> evalD e mv -> u = v.
Proof.
move=> hu.
apply: (@evalD_mut_ind R
  (fun (l : _) (G := prods (map snd l)) (T : types) (e : expD T) (f : projT2 (typei G) -> projT2 (typei T)) (mf : measurable_fun setT f) (h1 : evalD e mf) =>
    forall (v : projT2 (typei G) -> projT2 (typei T)) (mv : measurable_fun setT v), evalD e mv -> f = v)
  (fun (l : _) (G := prods (map snd l)) (T : types) (e : expP T) (u : R.-sfker projT2 (typei G) ~> projT2 (typei T)) (h1 : evalP e u) =>
    forall (v : R.-sfker projT2 (typei G) ~> projT2 (typei T)), evalP e v -> u = v)
  _ _ _ _ _ _ _ _ _ _ _ _ _ l T e); last exact: hu.
- 
move=> l' {}v {}mv.
inversion 1.
by do 2 inj H3.
-
move=> l' b {}v {}mv.
inversion 1.
by do 2 inj H3.
-
move=> l' r {}v {}mv.
inversion 1.
subst.
by do 2 inj H3.
- (* pair *)
move=> l' G0 A B e1 f1 mf1 e2 f2 mf2 ev1 IH1 ev2 IH2 {}v {}mv H.
simple inversion H => //.
injection H3 => ? ?; subst A0 B0 l0.
inj H4.
injection H4 => He1 He2. 
inj He1.
inj He2.
subst e0 e3.
do 2 inj H5.
move=> e1f0 e2f3.
by rewrite (IH1 _ _ e1f0) (IH2 _ _ e2f3).
- (* var *)
move=> l' x H n {}v {}mv.
inversion 1.
do 2 inj H9.
by have -> : (H = H7) by exact: Prop_irrelevance.
- (* bernoulli *)
move=> l' r r1 {}v {}mv.
inversion 1.
subst.
do 2 inj H3.
subst.
by have -> : (r1 = r3) by exact: Prop_irrelevance.
- (* poisson *)
move=> l' k e0 f mf ev IH {}v {}mv.
inversion 1.
subst.
do 2 inj H4; clear H5.
subst.
by rewrite (IH _ _ H3).
- (* norm *)
move=> l' A e0 k ev IH {}v {}mv.
inversion 1.
inj H2.
do 2 inj H4.
subst.
by rewrite (IH _ H3).
- (* sample *)
move=> l' A e0 p ev IH k.
inversion 1.
inj H0.
do 2 inj H3.
subst.
have cstp := IH _ _ H4.
by rewrite (inj_cst cstp).
- (* if *)
move=> l' G0 e0 f1 mf1 e2 k2 e3 k3 ev1 IH1 ev2 IH2 ev3 IH3 k.
inversion 1.
inj H1.
inj H2.
subst.
do 2 inj H5.
have ? := IH1 _ _ H6.
subst f1.
have -> : (mf1 = mf) by exact: Prop_irrelevance.
by rewrite (IH2 _ H7) (IH3 _ H8).
- (* score *)
move=> l' G0 e0 f mf ev IH k H.
simple inversion H => // ev0.
subst.
do 2 inj H4.
inj H3.
injection H3 => H5.
subst.
have ? := IH _ _ ev0.
subst f0.
by have -> : (mf = mf0) by exact: Prop_irrelevance.
- (* return *)
move=> l' A e0 f mf ev IH k.
inversion 1.
subst.
inj H5.
do 2 inj H7.
subst.
have ? := IH _ _ H3.
subst f1.
by have -> : (mf = mf1) by exact: Prop_irrelevance.
- (* letin *)
move=> l' G0 A B x e1 e2 k1 k2 ev1 IH1 ev2 IH2 k.
inversion 1.
subst.
inj H5.
inj H6.
do 2 inj H8.
subst.
by rewrite (IH1 _ H4) (IH2 _ H9).
Qed.

(* Lemma eval_uniqP (l : context) (T : types) (e : expP T l) 
  (u v : R.-sfker typei2 (prods (map snd l)) ~> typei2 T) :
  evalP e u -> evalP e v -> u = v.
Proof.
move=> hu.
apply: (@evalP_mut_ind R
  (fun (l : _) (G := prods (map snd l)) (T : types) (e : expD T l) (f : projT2 (typei G) -> projT2 (typei T)) (mf : measurable_fun setT f) (h1 : evalD e mf) =>
    forall (v : projT2 (typei G) -> projT2 (typei T)) (mv : measurable_fun setT v), evalD e mv -> f = v)
  (fun (l : _) (G := prods (map snd l)) (T : types) (e : expP T l) (u : R.-sfker projT2 (typei G) ~> projT2 (typei T)) (h1 : evalP e u) =>
    forall (v : R.-sfker projT2 (typei G) ~> projT2 (typei T)), evalP e v -> u = v)
  _ _ _ _ _ _ _ _ _ _ _ _ _ l T e); last exact: hu.
- 
move=> l' {}v {}mv.
inversion 1.
by do 2 inj H3.
-
move=> l' b {}v {}mv.
inversion 1.
by do 2 inj H3.
-
move=> l' r {}v {}mv.
inversion 1.
subst.
by do 2 inj H3.
- (* pair *)
move=> l' G0 A B e1 f1 mf1 e2 f2 mf2 ev1 IH1 ev2 IH2 {}v {}mv H.
simple inversion H => //.
injection H3 => ? ?; subst A0 B0 l0.
inj H4.
injection H4 => He1 He2. 
do 2 inj He1.
do 2 inj He2.
subst e0 e3.
do 2 inj H5.
move=> e1f0 e2f3.
by rewrite (IH1 _ _ e1f0) (IH2 _ _ e2f3).
- (* var *)
move=> l' x H n {}v {}mv.
inversion 1.
do 2 inj H8.
by have -> : (H = H1) by exact: Prop_irrelevance.
- (* bernoulli *)
move=> l' r r1 {}v {}mv.
inversion 1.
subst.
do 2 inj H3.
subst.
by have -> : (r1 = r3) by exact: Prop_irrelevance.
- (* poisson *)
move=> l' k e0 f mf ev IH {}v {}mv.
inversion 1.
subst.
inj H2.
do 2 inj H4; clear H5.
subst.
by rewrite (IH _ _ H3).
- (* norm *)
move=> l' A e0 k ev IH {}v {}mv.
inversion 1.
do 2 inj H2.
do 2 inj H4.
subst.
by rewrite (IH _ H3).
- (* sample *)
move=> l' A e0 p ev IH k.
inversion 1.
do 2 inj H0.
do 2 inj H3.
subst.
have cstp := IH _ _ H4.
by rewrite (inj_cst cstp).
- (* if *)
move=> l' G0 e0 f1 mf1 e2 k2 e3 k3 ev1 IH1 ev2 IH2 ev3 IH3 k.
inversion 1.
inj H0.
do 2 inj H1.
do 2 inj H2.
subst.
do 2 inj H5.
have ? := IH1 _ _ H6.
subst f1.
have -> : (mf1 = mf) by exact: Prop_irrelevance.
by rewrite (IH2 _ H7) (IH3 _ H8).
- (* score *)
move=> l' G0 e0 f mf ev IH k H.
simple inversion H => // ev0.
subst.
do 2 inj H4.
do 2 inj H3.
injection H3 => H5.
inj H5.
subst.
have ? := IH _ _ ev0.
subst f0.
by have -> : (mf = mf0) by exact: Prop_irrelevance.
- (* return *)
move=> l' A e0 f mf ev IH k.
inversion 1.
subst.
do 2 inj H5.
do 2 inj H7.
subst.
have ? := IH _ _ H3.
subst f1.
by have -> : (mf = mf1) by exact: Prop_irrelevance.
- (* letin *)
move=> l' G0 A B x e1 e2 k1 k2 ev1 IH1 ev2 IH2 k.
inversion 1.
subst.
do 2 inj H10.
(* inj H5.
inj H6. *)
do 2 inj H7.
do 4 inj H8.
subst.
by rewrite (IH1 _ H4) (IH2 _ H11).
Qed. *)

Axiom largest_var_in_expD : forall (t : types) (l : context) (e : @expD R t), nat.
Axiom H : forall x (l : context), x \in (map fst l).

Local Open Scope seq_scope.
Fixpoint free_varsD T (e : @expD R T) : seq _ :=
  match e with
  | exp_var R x _ => [:: x]
  | exp_poisson _ e => free_varsD e
  | exp_pair _ _ e1 e2 => free_varsD e1 ++ free_varsD e2
  | exp_unit => [::]
  | exp_bool _ => [::]
  | exp_real _ => [::]
  | exp_bernoulli _ _ => [::]
  | exp_norm _ e => free_varsP e
  (* | _ => [::] *)
  end
with free_varsP T (e : expP T) : seq _ :=
  match e with
  | exp_if R e1 e2 e3 => free_varsD e1 ++ free_varsP e2 ++ free_varsP e3
  | exp_letin R _ x e1 e2 => free_varsP e1 ++ rem x (free_varsP e2)
  | exp_sample R e => free_varsD e
  | exp_score e => free_varsD e
  | exp_return R e => free_varsD e
  end.

Lemma evalD_full (T : types) :
  forall e l, 
  {subset (free_varsD e) <= map fst l} ->
  exists f (mf : measurable_fun _ f), @evalD R l T e f mf.
Proof.
move=> e.
apply: (@expD_mut_ind R
  (fun (t : types) (e : expD t) =>
    forall l, {subset (free_varsD e) <= map fst l} ->
    exists f (mf : measurable_fun _ f), evalD e mf)
  (fun (t : types) (e : expP t) =>
    forall l, {subset (free_varsP e) <= map fst l} ->
    exists k, evalP e k)
  _ _ _ _ _ _ _ _ _ _ _ _ _ T e).
do 2 eexists; apply: E_unit.
do 2 eexists; apply: E_bool.
do 2 eexists; apply: E_real.
- (* pair *)
move=> t1 t2 e1 H1 e2 H2 l el.
have h1 : {subset free_varsD e1 <= [seq i.1 | i <- l]}.
  move=> x xe1.
  apply: el => /=.
  by rewrite mem_cat xe1.
have h2 : {subset free_varsD e2 <= [seq i.1 | i <- l]}.
  move=> x xe2.
  apply: el => /=.
  by rewrite mem_cat xe2 orbT.
move: H1 => /(_ _ h1) => H1.
move: H2 => /(_ _ h2) => H2.
destruct H1 as [f1 [mf1 ev1]].
destruct H2 as [f2 [mf2 ev2]].
do 2 eexists.
by apply: (E_pair ev1 ev2).
- (* var *)
move=> l x xl l0 xl0.
have xl0' : (x \in map fst l0) by admit.
(* have -> : (l0 = l) by admit. *)
exists (@varof3 R l l0 x xl xl0').
(* eexists. *)
exists (@mvarof3 R l l0 x xl xl0').
(* apply/E_var. *)
admit.
move=> r r1.
do 2 eexists; exact: E_bernoulli.
move=> k e0 H.
destruct H as [f [mf ev]].
exists (poisson k \o f).
exists (measurable_fun_comp (mpoisson k) mf).
apply/E_poisson /ev.
move=> t e0 H.
destruct H as [k ev].
exists (normalize k).
exists (measurable_fun_normalize k).
exact: E_norm.
move=> t e1 H1 e2 H2 e3 H3.
destruct H1 as [f [mf ev1]].
destruct H2 as [k2 ev2].
destruct H3 as [k3 ev3].
exists (ite mf k2 k3).
exact: E_ifP.
move=> t1 t2 x e1 H1 e2 H2.
destruct (H1) as [k1 ev1].
destruct (H2) as [k2 ev2].
(* exists (letin' k1 k2). *)
(* exact: E_letin. *)
admit.
move=> t e0 H.
destruct H as [f [mf ev]].
have : (f = (cst _)).
admit.
move=> Hf.
have s : typei2 (probs t).
admit.
exists (sample (s R)).
apply: E_sample.
(*
syntax -> 制限する
*)
admit.
move=> e0 H.
destruct H as [f [mf H]].
exists (score mf).
exact: E_score.
move=> t e0 H.
destruct H as [f [mf H]].
exists (ret mf).
exact: E_return.
Admitted.


Variables (A B C : types).
Definition X := @typei2 R A.
Definition Y := @typei2 R B.
Definition Z := @typei2 R C.

Definition execP T :
  @expP R T -> R.-sfker X ~> Y.
Proof.
move=> e.
(* have /cid h := eval_full [::]. *)
(* exact: (proj1_sig h). *)
(* Defined. *)
Admitted.

Lemma letin1 v1 v2 t M :
  let x := "x" in
  let y := "y" in
  measurable M ->
  @evalP R [::] (pairs reals reals) (exp_letin x (exp_return (exp_real 1)) (exp_letin y (exp_return (exp_real 2)) (exp_return (exp_pair (exp_var x) (exp_var y))))) v1 ->
  evalP (exp_letin y (exp_return (exp_real 2)) (exp_letin x (exp_return (exp_real 1)) (exp_return (exp_pair (exp_var x) (exp_var y))))) v2 ->
  v1 t M = v2 t M.
Proof.
move=> x y mM ev1 ev2.
pose vx : R.-sfker munit ~> mR R := @execP reals [::] (exp_return (exp_real 1)).
pose vy : R.-sfker [the measurableType _ of (mR R * munit)%type] ~> mR R := @execP reals [:: (x, reals)] (exp_return (exp_real 2)).
(* move=> ev1 ev2. *)
have -> : v1 = letin' vx (letin' vy (ret (measurable_fun_pair var2of3' var1of3'))).
apply: (evalP_uniq ev1).
apply/E_letin /E_letin.
have -> : (vx = ret (kr 1)).
  rewrite /vx /execP /ssr_have /sval.
  case: cid => ? h.
  apply: esym.
  apply: evalP_uniq h.
  apply/E_return /E_real.
apply/E_return /E_real.
have -> : (vy = ret (kr 2)).
  rewrite /vy /execP /ssr_have /sval.
  case: cid => ? h.
  apply: esym.
  apply: evalP_uniq h.
  apply/E_return /E_real.
apply/E_return /E_real.
apply/E_return /E_pair.
have -> : (var2of3' = (@mvarof R [:: (y, reals); (x, reals)] 1 (false_index_size (_ : (x \in map fst [:: (y, reals); (x, reals)]))))) by [].
apply/(@E_var R [:: (y, reals); (x, reals)] x).
have -> : (var1of4' = (@mvarof R [:: (y, reals); (x, reals)] 0 (false_index_size (_ : (y \in map fst [:: (y, reals); (x, reals)]))))) by [].
apply/(@E_var R [:: (y, reals); (x, reals)] y is_true_true).
pose vy' : R.-sfker munit ~> mR R := @execP reals [::] (exp_return (exp_real 2)).
pose vx' : R.-sfker [the measurableType _ of (mR R * munit)%type] ~> mR R := @execP reals [:: (y, reals)] (exp_return (exp_real 1)).
have -> : v2 = letin' vy' (letin' vx' (ret (measurable_fun_pair var1of3' var2of3'))).
apply: (evalP_uniq ev2).
apply/E_letin /E_letin.
have -> : (vy' = ret (kr 2)).
  rewrite /vy' /execP /ssr_have /sval.
  case: cid => ? h.
  apply: esym.
  apply: evalP_uniq h.
  apply/E_return /E_real.
apply/E_return /E_real.
have -> : (vx' = ret (kr 1)).
  rewrite /vx' /execP /ssr_have /sval.
  case: cid => ? h.
  apply: esym.
  apply: evalP_uniq h.
  apply/E_return /E_real.
apply/E_return /E_real.
apply/E_return /E_pair.
have -> : (var1of3' = (@mvarof R [:: (x, reals); (y, reals)] 0 (false_index_size (_ : (x \in map fst [:: (x, reals); (y, reals)]))))) by [].
apply/(@E_var R [:: (x, reals); (y, reals)] x is_true_true).
have -> : (var2of3' = (@mvarof R [:: (x, reals); (y, reals)] 1 (false_index_size (_ : (y \in map fst [:: (x, reals); (y, reals)]))))) by [].
apply/(@E_var R [:: (x, reals); (y, reals)] y is_true_true).
rewrite !letin'E.
under eq_integral.
  move=> x0 _.
  rewrite letin'E /=.
  have -> : (vy (x0, t) = vy' t).
  rewrite /vy /vy' /execP /ssr_have /sval.
  case: cid => x1.
  case: cid => x2.
  move=> H1 H2.
  have := (evalP_uniq H1 H2). /(_ (ret (kr 1))).
  move=> /[apply].
  rewrite -(@tt' reals reals vy').
  over.
apply esym.
under eq_integral.
  move=> x0 _.
  rewrite letin'E /=.
  rewrite -(@tt' reals reals vx).
  over.
rewrite (sfinite_fubini _ _ (fun t => \d_(t.1, t.2) M))//; last 3 first.
exact: sfinite_kernel_measure.
exact: sfinite_kernel_measure.
apply/EFin_measurable_fun => /=.
rewrite (_ : (fun x => _) = @mindic _ [the measurableType _ of (mR R * mR R)%type] R _ mM).
admit.
by apply/funext => -[].
Admitted.

Lemma letinC (t : expP A) (u : expP _) 
  (vt : R.-sfker munit ~> X) (vu : R.-sfker munit ~> Y) 
  (vt' : R.-sfker _ ~> _) (vu' : R.-sfker [the measurableType _ of (X * munit)%type] ~> Y) z M :
  let x := "x" in let y := "y" in
  (* measurable M -> *)
  @evalP R [::] A t vt ->
  @evalP R [::] B u vu ->
  letin' vt
  (letin' vu'
  (@ret _ _ _ _ (measurable_fun_pair var3of3' var2of3'))) z M =
  letin' vu
  (letin' vt
  (ret (measurable_fun_pair var3of3 var2of3))) z M.

Lemma tt' t (t' : R.-sfker @typei2 R (pairs B units) ~> @typei2 R A) : forall x, t =1 fun z => t' (x, z).
Admitted.

Lemma uu' u (u' : R.-sfker @typei2 R (pairs A units) ~> @typei2 R B) : forall y, u =1 fun z => u' (y, z).
Admitted.

Lemma letinC' (t : expP B [::]) (u : expP A (("x", B) :: [::]))(v1 v2 : R.-sfker _ ~> _) z M :
  let x := "x" in let y := "y" in
  measurable M ->
  @evalP R [::] (pairs B A)
  (@exp_letin R _ _ [::] x t (@exp_letin R _ _ [:: (x, B)] y u
    (exp_return (exp_pair (exp_var x) (exp_var y))))) v1 ->
  @evalP R [::] (pairs B A)
  (@exp_letin R _ _ [:: (x, B)] y u (@exp_letin R _ _ [:: (y, A); (x, B)] x t
    (exp_return (exp_pair (exp_var x) (exp_var y))))) v2 ->
  v1 z M = v2 z M.


End eval_prop.

Section example.

Local Open Scope ring_scope.
Variables (R : realType).

Example pgm1 : expD (probs bools) [::] := exp_norm (
  exp_letin "x" (exp_sample (@exp_bernoulli R (2 / 7%:R)%:nng p27 [::])) (
  exp_letin "r" (exp_if (@exp_var R [:: ("x", bools)] "x") 
    (exp_return (exp_real 3%:R)) (exp_return (exp_real 10%:R))) (
  exp_letin "_" (exp_score 
  (exp_poisson 4 (@exp_var R [:: ("r", reals); ("x", bools)] "r"))) 
    (exp_return 
      (@exp_var R [:: ("_", units); ("r", reals); ("x", bools)] "x"))))).

Definition sample_bern : R.-sfker munit ~> mbool := 
  sample [the probability _ _ of bernoulli p27].
Definition ite_3_10 : 
  R.-sfker [the measurableType _ of (mbool * munit)%type] ~> (mR R) :=
  ite var1of4' (ret k3) (ret k10).
Definition score_poi :
  R.-sfker [the measurableType _ of ((mR R) * (mbool * munit)%type)%type] ~> munit :=
  score (measurable_fun_comp (mpoisson 4) var1of4').

Local Definition kstaton_bus'' := 
  letin' sample_bern 
    (letin' ite_3_10 
      (letin' score_poi (ret var3of4'))).

Example ev1 : @evalD R [::] _ pgm1 _ (measurable_fun_normalize kstaton_bus'').
Proof.
apply/E_norm /E_letin /E_letin /E_letin.
apply/E_sample /E_bernoulli.
apply/E_ifP.
have -> : (var1of4' = (@mvarof2 R [:: ("x", bools)] 0 (false_index_size2 (_ : "x" \in map fst [:: ("x", bools)])))) by done.
exact: (@E_var R [:: ("x", bools)] "x").
apply/E_return /E_real.
apply/E_return /E_real.
apply/E_score /E_poisson.
have -> : (var1of4' = (@mvarof2 R [:: ("r", reals); ("x", bools)] 0 (false_index_size2 (_ : "r" \in map fst [:: ("r", reals); ("x", bools)])))) by done.
exact: (@E_var R [:: ("r", reals); ("x", bools)] "r").
apply/E_return.
have -> : (var3of4' = (@mvarof2 R [:: ("_", units); ("r", reals); ("x", bools)] 2 (false_index_size2 (_ : "x" \in map fst [:: ("_", units); ("r", reals); ("x", bools)])))) by done.
exact: (@E_var R [:: ("_", units); ("r", reals); ("x", bools)] "x").
Qed.

End example.