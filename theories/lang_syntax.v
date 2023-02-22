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
Notation var2of3' := (measurable_funT_comp (@measurable_fun_fst _ _ _ _) (@measurable_fun_snd _ _ _ _)).
Notation var3of3' := (measurable_funT_comp (@measurable_fun_fst _ _ _ _) (measurable_funT_comp (@measurable_fun_snd _ _ _ _) (@measurable_fun_snd _ _ _ _))).

Notation var1of4' := (@measurable_fun_fst _ _ _ _).
Notation var2of4' := (measurable_funT_comp (@measurable_fun_fst _ _ _ _) (@measurable_fun_snd _ _ _ _)).
Notation var3of4' := (measurable_funT_comp (@measurable_fun_fst _ _ _ _) (measurable_funT_comp (@measurable_fun_snd _ _ _ _) (@measurable_fun_snd _ _ _ _))).
Notation var4of4' := (measurable_funT_comp (@measurable_fun_fst _ _ _ _) (measurable_funT_comp (@measurable_fun_snd _ _ _ _) (measurable_funT_comp (@measurable_fun_snd _ _ _ _) (@measurable_fun_snd _ _ _ _)))).

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

Inductive stype :=
| sunit : stype
| sbool : stype
| sreal : stype
| spair : stype -> stype -> stype
| sprob : stype -> stype
| sprod : list stype -> stype.

Fixpoint typei (t : stype) : {d & measurableType d} :=
  match t with
  | sunit => existT _ _ munit
  | sbool => existT _ _ mbool
  | sreal => existT _ _ (mR R)
  | spair A B => existT _ _
      [the measurableType ((projT1 (typei A),projT1 (typei B)).-prod)%mdisp of (projT2 (typei A) * projT2 (typei B))%type]
  | sprob A => existT _ _ (pprobability (projT2 (typei A)) R)
  | sprod l => prod_meas (map typei l) 
  end.

Definition typei2 (t : stype) := projT2 (typei t).

End type_syntax.

Arguments typei {R}.
Arguments typei2 {R}.

Section context.
Definition context := seq (string * stype)%type.
End context.

Section expr.
Variables (R : realType).
Inductive expD : context -> stype -> Type :=
| exp_unit l : expD l sunit
| exp_bool l : bool -> expD l sbool
| exp_real l : R -> expD l sreal
| exp_pair l t1 t2 : expD l t1 -> expD l t2 -> expD l (spair t1 t2)
| exp_var l x t : t = nth sunit (map snd l) (seq.index x (map fst l)) ->
    expD l t
| exp_bernoulli l (r : {nonneg R}) (r1 : (r%:num <= 1)%R) : 
    expD l (sprob sbool)
| exp_poisson l : nat -> expD l sreal -> expD l sreal
| exp_norm l t : expP l t -> expD l (sprob t)

with expP : context -> stype -> Type :=
| exp_if l t : expD l sbool -> expP l t -> expP l t -> expP l t
| exp_letin l l' t1 t2 (x : string) : l' = (x, t1) :: l ->
    expP l t1 -> expP l' t2 -> expP l t2
(* | exp_sample : forall t l, expD (sprob t) l -> expP t l *)
| exp_sample_bern l (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
    expP l sbool
| exp_score l : expD l sreal -> expP l sunit
| exp_return l t : expD l t -> expP l t
.

End expr.

Arguments expD {R}.
Arguments expP {R}.
Arguments exp_unit {R l}.
Arguments exp_bool {R l}.
Arguments exp_real {R l}.
Arguments exp_pair {R l _ _}.
Arguments exp_var {R _}.
Arguments exp_bernoulli {R l}.
Arguments exp_poisson {R l}.
Arguments exp_norm {R l _}.
Arguments exp_if {R l _}.
Arguments exp_letin {R l _ _}.
Arguments exp_sample_bern {R} l r.
Arguments exp_score {R l}.
Arguments exp_return {R l _}.

Section eval.
Variables (R : realType).

Definition varof (l : context) (i : nat) (li : (i < size l)%nat) :
  projT2 (@typei R (sprod (map snd l))) ->
  projT2 (@typei R (nth sunit (map snd l) i)).
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

Lemma false_index_size (x : string) (l : context) (H : x \in (map fst l)) :
	(seq.index x (map fst l) < size l)%nat.
Proof. by rewrite -(size_map fst) index_mem. Qed.

Lemma mvarof (l : context) (i : nat) (li : (i < size l)%nat) :
  measurable_fun setT (@varof l i li).
Proof.
revert l i li.
induction l.
  by destruct i.
destruct i.
simpl => _.
intro K.
exact: measurable_fun_fst.
move=> il K.
apply: (measurable_funT_comp (IHl _ _) (@measurable_fun_snd _ _ _ _)).
apply: K.
Qed.

Lemma measurable_fun_normalize d d' (X : measurableType d) (Y : measurableType d') (k : R.-sfker X ~> Y) :
  measurable_fun setT (normalize k point : X -> pprobability Y R).
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
  reflexivity.
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

(* Fixpoint denoteType (t : stype) (e : @expD t) :=
  match e with
  | exp_unit => sunit
  | exp_bool _ => sbool
  | exp_real R _ => sreal
  | exp_pair _ _ e1 e2 => spair (denoteType e1) (denoteType e2)
  | exp_var l x => nth sunit (map snd l) (seq.index x (map fst l))
  end. *)

(* Fixpoint execD (l : context) (t : stype) (e : expD t) 
  : {f : @typei2 R (sprod (map snd l)) -> typei2 (denoteType e) & measurable_fun _ f} :=
  match e return {f : @typei2 R (sprod (map snd l)) -> typei2 (denoteType e) & measurable_fun _ f} with
  | exp_unit => existT _ (cst tt) ktt
  | exp_bool b => existT _ (cst b) (kb b)
  | exp_real r => existT _ (cst r) (kr r)
  | exp_pair _ _ e1 e2 => 
    existT _ _ (@measurable_fun_pair _ _ _ _ _ _ _ _ (projT2 (execD l e1)) (projT2 (execD l e2)))
  | exp_var l x => forall (H : x \in (map fst l)),
    existT _ (@varof l (seq.index x (map fst l)) (false_index_size H)) (@mvarof l (seq.index x (map fst l)) (false_index_size H))
  end. *)

Reserved Notation "l |- e -D-> v # mv" (at level 50).
Reserved Notation "l |- e -P-> v" (at level 50).

Inductive evalD : forall (l : context) (T : stype) (e : @expD R l T) 
  (f : projT2 (typei (sprod (map (snd) l))) -> projT2 (typei T)),
  measurable_fun setT f -> Prop :=
| E_unit l :
  l |- exp_unit -D-> cst tt # ktt

| E_bool l b :
  l |- exp_bool b -D-> cst b # kb b

| E_real l r :
  l |- exp_real r -D-> cst r # kr r

| E_pair l (G := sprod (map (snd) l)) A B e1 f1 mf1 e2 f2 mf2 :
  l |- e1 -D-> f1 # mf1 -> (* (f1 : projT2 (typei G) -> projT2 (typei A)) *)
  l |- e2 -D-> f2 # mf2 -> (* (f2 : projT2 (typei G) -> projT2 (typei B)) *)

  l |- exp_pair e1 e2 -D-> fun x => (f1 x, f2 x) # 
  (@measurable_fun_pair _ _ _ (projT2 (typei G)) (projT2 (typei A)) 
  (projT2 (typei B)) f1 f2 mf1 mf2)
  (* 
  ((fun x : projT2 (typei G) => (f1 x, f2 x)) 
    : projT2 (typei G) -> projT2 (typei (spair A B))) 
  *)

| E_var (l : context) (x : string) (H : x \in map fst l) :
  let i := seq.index x (map fst l) in
  l |- exp_var x _ erefl -D-> @varof l i (false_index_size H) #
  @mvarof l i (false_index_size H)

| E_bernoulli l (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
  l |- exp_bernoulli r r1 -D->
  cst [the probability _ _ of bernoulli r1] # measurable_fun_cst _
  (* sprob sbool *)

| E_poisson l k e f mf :
  l |- e -D-> f # mf ->
  l |- exp_poisson k e -D-> poisson k \o f #
  measurable_funT_comp (mpoisson k) mf

| E_norm l (t : stype) (e : expP l t) (k : R.-sfker _ ~> projT2 (typei t)) :
  l |- e -P-> k ->
  l |- exp_norm e -D-> (normalize k point : _ -> pprobability _ _) #
  measurable_fun_normalize k

where "l |- e -D-> v # mv" := (@evalD l _ e v mv)

with evalP : forall (l : context) (T : stype),
  expP l T ->
  R.-sfker (projT2 (typei (sprod (map (snd) l)))) ~> projT2 (typei T) -> Prop :=
| E_sample l (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
  (* @evalD l (sprob T) e (cst p) (measurable_fun_cst p) -> *)
  l |- @exp_sample_bern R _ r r1 -P->
  sample [the probability _ _ of bernoulli r1]

| E_ifP l T e1 f1 mf e2 k2 e3 k3 :
  l |- e1 -D-> f1 # mf ->
  l |- e2 -P-> k2 ->
  l |- e3 -P-> k3 ->
  l |- exp_if e1 e2 e3 : expP l T -P-> ite mf k2 k3

| E_score l (G := sprod (map snd l)) e (f : projT2 (typei G) -> R)
  (mf : measurable_fun _ f) :
  l |- e : expD l sreal -D-> f # mf ->
  l |- exp_score e -P-> [the R.-sfker _ ~> _ of kscore mf]

| E_return l T e (f : _ -> _) (mf : measurable_fun _ f) :
  l |- e -D-> f # mf ->
  l |- exp_return e : expP l T -P-> ret mf

| E_letin (l : context) (G := sprod (map snd l)) (t1 t2 : stype) 
  (x : string) (e1 : expP l t1) (e2 : expP ((x, t1) :: l) t2)
  (k1 : R.-sfker projT2 (typei G) ~> projT2 (typei t1))
  (k2 : R.-sfker (typei2 (spair t1 G)) ~> projT2 (typei t2)) :
  l |- e1 -P-> k1 ->
  ((x, t1)::l)%SEQ |- e2 -P-> k2 ->
  l |- exp_letin _ x erefl e1 e2 -P-> letin' k1 k2
where "l |- e -P-> v" := (@evalP l _ e v).

End eval.

Section eval_prop.
Variables (R : realType).

Ltac inj H := apply Classical_Prop.EqdepTheory.inj_pair2 in H.

Scheme evalD_mut_ind := Induction for evalD Sort Prop
with evalP_mut_ind := Induction for evalP Sort Prop.

Scheme expD_mut_ind := Induction for expD Sort Prop
with expP_mut_ind := Induction for expP Sort Prop.

Lemma evalD_uniq (l : context) (G := sprod (map snd l)) (t : stype) 
  (e : expD l t) (u v : projT2 (typei G) -> projT2 (typei t)) 
  (mu : measurable_fun _ u) (mv : measurable_fun _ v) :
  @evalD R l t e u mu -> evalD e mv -> u = v.
Proof.
move=> hu.
apply: (@evalD_mut_ind R
  (fun (l : _) (G := sprod (map snd l)) (t : stype) (e : expD l t) 
  (f : projT2 (typei G) -> projT2 (typei t)) (mf : measurable_fun setT f) 
  (h1 : evalD e mf) => forall (v : projT2 (typei G) -> projT2 (typei t)) (mv : measurable_fun setT v), evalD e mv -> f = v)
  (fun (l : _) (G := sprod (map snd l)) (t : stype) (e : expP l t) 
  (u : R.-sfker projT2 (typei G) ~> projT2 (typei t)) (h1 : evalP e u) =>
  forall (v : R.-sfker projT2 (typei G) ~> projT2 (typei t)), 
  evalP e v -> u = v) _ _ _ _ _ _ _ _ _ _ _ _ _ l t e); last exact: hu.
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
do 2 inj H4.
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
move=> l' r r1 p.
inversion 1.
(* do 2 inj H0. *)
do 2 inj H3.
subst.
by have -> : (r1 = r3) by apply: Prop_irrelevance.
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
do 2 inj H13.
do 2 inj H11.
subst.
by rewrite (IH1 _ H4) (IH2 _ H14).
Qed.

(* TODO: factorize proof *)
Lemma evalP_uniq (l : context) (t : stype) (e : expP l t) 
  (u v : R.-sfker typei2 (sprod (map snd l)) ~> typei2 t) :
  evalP e u -> evalP e v -> u = v.
Proof.
move=> hu.
apply: (@evalP_mut_ind R
  (fun (l : _) (G := sprod (map snd l)) (t : stype) (e : expD l t) (f : projT2 (typei G) -> projT2 (typei t)) (mf : measurable_fun setT f) (h1 : evalD e mf) =>
    forall (v : projT2 (typei G) -> projT2 (typei t)) (mv : measurable_fun setT v), evalD e mv -> f = v)
  (fun (l : _) (G := sprod (map snd l)) (t : stype) (e : expP l t) (u : R.-sfker projT2 (typei G) ~> projT2 (typei t)) (h1 : evalP e u) =>
    forall (v : R.-sfker projT2 (typei G) ~> projT2 (typei t)), evalP e v -> u = v)
  _ _ _ _ _ _ _ _ _ _ _ _ _ l t e); last exact: hu.
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
move=> l' r r1 ev.
inversion 1.
(* do 2 inj H0. *)
do 2 inj H3.
subst.
by have -> : (r1 = r3) by exact: Prop_irrelevance.
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
do 2 inj H11.
do 2 inj H13.
(* do 2 inj H7.
do 4 inj H8. *)
subst.
by rewrite (IH1 _ H4) (IH2 _ H14).
Qed.

Fixpoint free_varsD l t (e : @expD R l t) : seq string :=
  match e with
  | exp_var _ x _ _             => [:: x]
  | exp_poisson _ _ e       => free_varsD e
  | exp_pair _ _ _ e1 e2    => free_varsD e1 ++ free_varsD e2
  | exp_unit _              => [::]
  | exp_bool _ _            => [::]
  | exp_real _ _            => [::]
  | exp_bernoulli _ _ _     => [::]
  | exp_norm _ _ e          => free_varsP e
  end
with free_varsP T l (e : expP T l) : seq _ :=
  match e with
  | exp_if _ _ e1 e2 e3     => free_varsD e1 ++ free_varsP e2 ++ free_varsP e3
  | exp_letin _ _ _ _ x _ e1 e2 => free_varsP e1 ++ rem x (free_varsP e2)
  | exp_sample_bern _ _ _   => [::]
  | exp_score _ e           => free_varsD e
  | exp_return _ _ e        => free_varsD e
  end.

Lemma evalD_full (l : context) (t : stype) :
  forall e, {subset (free_varsD e) <= map fst l} ->
  exists f (mf : measurable_fun _ f), @evalD R l t e f mf.
Proof.
move=> e.
apply: (@expD_mut_ind R
  (fun (l : context) (t : stype) (e : expD l t) =>
    {subset (free_varsD e) <= map fst l} ->
    exists f (mf : measurable_fun _ f), evalD e mf)
  (fun (l : context) (t : stype) (e : expP l t) =>
    {subset (free_varsP e) <= map fst l} ->
    exists k, evalP e k) _ _ _ _ _ _ _ _ _ _ _ _ _ l t e).
do 2 eexists; apply/E_unit.
do 2 eexists; apply/E_bool.
do 2 eexists; apply/E_real.
move=> l0 t1 t2 e1 H1 e2 H2 el.
have h1 : {subset free_varsD e1 <= [seq i.1 | i <- l0]}.
  move=> x xe1.
  apply: el => /=.
  by rewrite mem_cat xe1.
have h2 : {subset free_varsD e2 <= [seq i.1 | i <- l0]}.
  move=> x xe2.
  apply: el => /=.
  by rewrite mem_cat xe2 orbT.
move: H1 => /(_ h1) => H1.
move: H2 => /(_ h2) => H2.
destruct H1 as [f1 [mf1]].
destruct H2 as [f2 [mf2]].
exists (fun x => (f1 x, f2 x)).
eexists; exact: E_pair.
move=> l0 x t0 t0E H.
subst t0.
have xl0 : x \in map fst l0.
apply: H.
by rewrite /= inE.
(* exists (@varof R l0 (seq.index x (map fst l0)) (false_index_size xl0)). *)
(* exists (@mvarof R l0 (seq.index x (map fst l0)) (false_index_size xl0)). *)
do 2 eexists.
by apply/E_var.
move=> r r1.
eexists.
eexists.
exact: E_bernoulli.
move=> l0 k e0 H el.
have h : {subset free_varsD e0 <= [seq i.1 | i <- l0]}.
  move=> x xe0.
  by apply: el => /=.
move: H => /(_ h) => H.
destruct H as [f [mf]].
exists (poisson k \o f).
exists (measurable_funT_comp (mpoisson k) mf).
exact: E_poisson.
move=> l0 t0 e0 H el.
have h : {subset free_varsP e0 <= map fst l0}.
  move=> x xe0.
  by apply: el => /=.
move: H => /(_ h) => H.
destruct H as [k].
exists (normalize k point).
exists (measurable_fun_normalize k).
exact: E_norm.
move=> l0 t0 e1 H1 e2 H2 e3 H3 el.
have h1 : {subset free_varsD e1 <= map fst l0}.
  move=> x xe1.
  apply: el => /=.
  by rewrite mem_cat xe1.
have h2 : {subset free_varsP e2 <= map fst l0}.
  move=> x xe2.
  apply: el => /=.
  by rewrite 2!mem_cat xe2 orbT.
have h3 : {subset free_varsP e3 <= map fst l0}.
  move=> x xe3.
  apply: el => /=.
  by rewrite 2!mem_cat xe3 2!orbT.
move: H1 => /(_ h1) => H1.
move: H2 => /(_ h2) => H2.
move: H3 => /(_ h3) => H3.
destruct H1 as [f [mf]].
destruct H2 as [k2].
destruct H3 as [k3].
exists (ite mf k2 k3).
exact: E_ifP.
move=> l0 l1 t1 t2 x l1l0 e1 H1 e2 H2 el.
have h1 : {subset free_varsP e1 <= map fst l0}.
  move=> y ye1.
  apply: el => /=.
  by rewrite mem_cat ye1.
have h2 : {subset free_varsP e2 <= map fst ((x, t1) :: l0)}.
  move=> y ye2.
  rewrite /= inE.
  have [//|/= xy] := eqVneq x y.
  apply: el => /=.
  rewrite mem_cat.
  apply/orP.
  right.
  move: ye2 xy.
  move: (free_varsP e2).
  (* TODO: extract lemma *)
  elim=> // h tl ih /=; rewrite inE => /orP[/eqP <-|yt xy].
    by move/negbTE; rewrite eq_sym => ->; rewrite mem_head.
  by case: ifPn => // hx; rewrite inE ih ?orbT.
subst l1.
move: H1 => /(_ h1) => H1.
move: H2 => /(_ h2) => H2.
destruct H1 as [k1 ev1].
destruct H2 as [k2 ev2].
exists (letin' k1 k2).
exact: E_letin.
move=> l0 r r1 el.
exists (sample [the pprobability _ _ of bernoulli r1]).
exact: E_sample.
move=> l0 e0 H el.
have h : {subset free_varsD e0 <= [seq i.1 | i <- l0]}.
  move=> x xe0.
  by apply: el => /=.
move: H => /(_ h) => H.
destruct H as [f [mf]].
exists (score mf).
exact: E_score.
move=> l0 t0 e0 H el.
have h : {subset free_varsD e0 <= [seq i.1 | i <- l0]}.
  move=> x xe0.
  by apply: el => /=.
move: H => /(_ h) => H.
destruct H as [f [mf]].
exists (ret mf).
exact: E_return.
Qed.

Lemma evalP_full (l : context) (t : stype) :
  forall e, {subset (free_varsP e) <= map fst l} ->
  exists (k : R.-sfker _ ~> _), @evalP R l t e k.
Proof.
move=> e.
apply: (@expP_mut_ind R
  (fun (l : context) (t : stype) (e : expD l t) =>
    {subset (free_varsD e) <= map fst l} ->
    exists f (mf : measurable_fun _ f), evalD e mf)
  (fun (l : context) (t : stype) (e : expP l t) =>
    {subset (free_varsP e) <= map fst l} ->
    exists k, evalP e k) _ _ _ _ _ _ _ _ _ _ _ _ _ l t e).
do 2 eexists; apply/E_unit.
do 2 eexists; apply/E_bool.
do 2 eexists; apply/E_real.
move=> l0 t1 t2 e1 H1 e2 H2 el.
have h1 : {subset free_varsD e1 <= [seq i.1 | i <- l0]}.
  move=> x xe1.
  apply: el => /=.
  by rewrite mem_cat xe1.
have h2 : {subset free_varsD e2 <= [seq i.1 | i <- l0]}.
  move=> x xe2.
  apply: el => /=.
  by rewrite mem_cat xe2 orbT.
move: H1 => /(_ h1) => H1.
move: H2 => /(_ h2) => H2.
destruct H1 as [f1 [mf1]].
destruct H2 as [f2 [mf2]].
exists (fun x => (f1 x, f2 x)).
eexists; exact: E_pair.
move=> l0 x t0 t0E H.
subst t0.
have xl0 : x \in map fst l0.
apply: H.
by rewrite /= inE.
do 2 eexists.
by apply/E_var.
move=> r r1.
eexists.
eexists.
exact: E_bernoulli.
move=> l0 k e0 H el.
have h : {subset free_varsD e0 <= [seq i.1 | i <- l0]}.
  move=> x xe0.
  by apply: el => /=.
move: H => /(_ h) => H.
destruct H as [f [mf]].
exists (poisson k \o f).
exists (measurable_funT_comp (mpoisson k) mf).
exact: E_poisson.
move=> l0 t0 e0 H el.
have h : {subset free_varsP e0 <= map fst l0}.
  move=> x xe0.
  by apply: el => /=.
move: H => /(_ h) => H.
destruct H as [k].
exists (normalize k point).
exists (measurable_fun_normalize k).
exact: E_norm.
move=> l0 t0 e1 H1 e2 H2 e3 H3 el.
have h1 : {subset free_varsD e1 <= map fst l0}.
  move=> x xe1.
  apply: el => /=.
  by rewrite mem_cat xe1.
have h2 : {subset free_varsP e2 <= map fst l0}.
  move=> x xe2.
  apply: el => /=.
  by rewrite 2!mem_cat xe2 orbT.
have h3 : {subset free_varsP e3 <= map fst l0}.
  move=> x xe3.
  apply: el => /=.
  by rewrite 2!mem_cat xe3 2!orbT.
move: H1 => /(_ h1) => H1.
move: H2 => /(_ h2) => H2.
move: H3 => /(_ h3) => H3.
destruct H1 as [f [mf]].
destruct H2 as [k2].
destruct H3 as [k3].
exists (ite mf k2 k3).
exact: E_ifP.
move=> l0 l1 t1 t2 x l1l0 e1 H1 e2 H2 el.
have h1 : {subset free_varsP e1 <= map fst l0}.
  move=> y ye1.
  apply: el => /=.
  by rewrite mem_cat ye1.
have h2 : {subset free_varsP e2 <= map fst ((x, t1) :: l0)}.
  move=> y ye2.
  rewrite /= inE.
  have [//|/= xy] := eqVneq x y.
  apply: el => /=.
  rewrite mem_cat.
  apply/orP.
  right.
  move: ye2 xy.
  move: (free_varsP e2).
  (* TODO: extract lemma *)
  elim=> // h tl ih /=; rewrite inE => /orP[/eqP <-|yt xy].
    by move/negbTE; rewrite eq_sym => ->; rewrite mem_head.
  by case: ifPn => // hx; rewrite inE ih ?orbT.
subst l1.
move: H1 => /(_ h1) => H1.
move: H2 => /(_ h2) => H2.
destruct H1 as [k1 ev1].
destruct H2 as [k2 ev2].
exists (letin' k1 k2).
exact: E_letin.
move=> l0 r r1 el.
exists (sample [the pprobability _ _ of bernoulli r1]).
exact: E_sample.
move=> l0 e0 H el.
have h : {subset free_varsD e0 <= [seq i.1 | i <- l0]}.
  move=> x xe0.
  by apply: el => /=.
move: H => /(_ h) => H.
destruct H as [f [mf]].
exists (score mf).
exact: E_score.
move=> l0 t0 e0 H el.
have h : {subset free_varsD e0 <= [seq i.1 | i <- l0]}.
  move=> x xe0.
  by apply: el => /=.
move: H => /(_ h) => H.
destruct H as [f [mf]].
exists (ret mf).
exact: E_return.
Qed.

(* Variables (A B C : stype).
Definition X := @typei2 R A.
Definition Y := @typei2 R B.
Definition Z := @typei2 R C. *)

Definition execP l t (e : @expP R l t) (H : {subset free_varsP e <= map fst l}):
  R.-sfker (@typei2 R (sprod (map snd l))) ~> @typei2 R t.
Proof.
have /cid h := @evalP_full l t e H.
exact: (proj1_sig h).
Defined.

Definition execP_cst (l l' : context) (r : R) :
  R.-sfker (@typei2 R (sprod (map (@snd string stype) l'))) ~> @typei2 R sreal.
Proof.
have H0 : {subset free_varsP (exp_return (exp_real r) : expP [::] _) <= map (@fst string stype) l'}.
  by move=> x /=.
have /cid h := @evalP_full l' _ (exp_return (exp_real r)) H0.
exact: (proj1_sig h).
Defined.

Scheme expD_mut_rec := Induction for expD Sort Type
with expP_mut_rec := Induction for expP Sort Type.

Definition rem_context l t (e : @expP R l t) (H : free_varsP e = [::]) : @expP R [::] t.
move: H.
apply: (@expP_mut_rec R
  (fun (l : context) (t : stype) (e : expD l t) =>
    free_varsD e = [::] -> expD [::] t)
  (fun (l : context) (t : stype) (e : expP l t) =>
    free_varsP e = [::] -> expP [::] t)
  _ _ _ _ _ _ _ _ _ _ _ _ _ l t e).
move=> ? ?; exact: exp_unit.
move=> ? b ?; exact: (exp_bool b).
move=> ? r ?; exact: (exp_real r).
move=> t1 t2 ? e1 t1nil e2 t2nil H.
rewrite /= in H.
apply: exp_pair.
apply: t1nil.
by destruct (free_varsD e1).
apply: t2nil.
destruct (free_varsD e2).
reflexivity.
move/(congr1 size) : H.
by rewrite size_cat/= addnS.
done.
move=> ? r r1 H.
apply: exp_bernoulli.
exact: r1.
rewrite /=.
move=> ? n e1 h H.
apply: (exp_poisson n).
exact: h.
rewrite /=.
move=> ? ? e1 h H.
apply: exp_norm.
exact: h.
move=> ? ? e1 h1 e2 h2 e3 h3 /= H.
apply: exp_if.
apply: h1.
by destruct (free_varsD e1).
apply: h2.
move: H.
destruct (free_varsP e2) => //=.
move=>/(congr1 size).
by rewrite !size_cat/= addnS.
apply: h3.
destruct (free_varsP e3) => //=.
move/(congr1 size) : H.
by rewrite !size_cat/= !addnS.
rewrite /=.
move=> ? t1 t2 x e1 h1 e2 h2 H.
Abort.

(* Variables (dT : measure_display) (T : measurableType dT).
(* Definition m := fun A => (_ : {measure set (@typei2 R A) -> \bar R}). *)

Axiom same_expP : forall (l l' : context) (T : stype) (e : @expP R T l)
  (e' : @expP R T l'), Prop. *)

Lemma evalP_uni_new x r
  (u : R.-sfker munit ~> mR R)
  (v : R.-sfker prod_meas_obligation_2 prod_meas
                (existT [eta measurableType] default_measure_display (mR R))
                [::] ~> mR R) :
  evalP (exp_return (exp_real r) : expP [::] sreal) u ->
  evalP (exp_return (exp_real r) : expP [:: (x, sreal)] sreal) v ->
  forall x0 t, v (x0, t) = u t.
Proof.
move=> H1 H2.
have -> : u = ret (kr r).
have := @evalP_uniq [::] sreal (exp_return (exp_real r)) u (ret (kr r)) H1.
apply.
apply/E_return /E_real.
suff : v = ret (kr r) by move=> ->.
have := @evalP_uniq [:: (x, sreal)] sreal (exp_return (exp_real r)) v (ret (kr r)) H2.
apply.
exact/E_return/E_real.
Qed.

Definition vx : R.-sfker munit ~> mR R := execP_cst [:: ("x", sreal)] [::] 1.
Definition VX z : set (mR R) -> \bar R := vx z.
Let VX0 z : (VX z) set0 = 0. Proof. by []. Qed.
Let VX_ge0 z x : 0 <= (VX z) x. Proof. by []. Qed.
Let VX_semi_sigma_additive z : semi_sigma_additive (VX z).
Proof. exact: measure_semi_sigma_additive. Qed.
HB.instance Definition _ z := @isMeasure.Build _ R (mR R) (VX z) (VX0 z) 
  (VX_ge0 z) (@VX_semi_sigma_additive z).
Let sfinVX z : sfinite_measure_def (VX z). Proof. exact: sfinite_kernel_measure. Qed.
HB.instance Definition _ z := @Measure_isSFinite_subdef.Build _ (mR R) R
  (VX z) (sfinVX z).

Definition vy' : R.-sfker munit ~> mR R := execP_cst  [::] [::] 2.
Definition VY z : set (mR R) -> \bar R := vy' z.
Let VY0 z : (VY z) set0 = 0. Proof. by []. Qed.
Let VY_ge0 z x : 0 <= (VY z) x. Proof. by []. Qed.
Let VY_semi_sigma_additive z : semi_sigma_additive (VY z).
Proof. exact: measure_semi_sigma_additive. Qed.
HB.instance Definition _ z := @isMeasure.Build _ R (mR R) (VY z) (VY0 z) 
  (VY_ge0 z) (@VY_semi_sigma_additive z).
Let sfinVY z : sfinite_measure_def (VY z). Proof. exact: sfinite_kernel_measure. Qed.
HB.instance Definition _ z := @Measure_isSFinite_subdef.Build _ (mR R) R
  (VY z) (sfinVY z).

Lemma letinC12 v1 v2 t M :
  let x := "x" in
  let y := "y" in
  measurable M ->
  @evalP R [::] (spair sreal sreal) (exp_letin _ x erefl (exp_return (exp_real 1)) (exp_letin _ y erefl (exp_return (exp_real 2)) (exp_return (exp_pair (exp_var x _ erefl) (exp_var y _ erefl))))) v1 ->
  evalP (exp_letin _ y erefl (exp_return (exp_real 2)) (exp_letin _ x erefl (exp_return (exp_real 1)) (exp_return (exp_pair (exp_var x _ erefl) (exp_var y _ erefl))))) v2 ->
  v1 t M = v2 t M.
Proof.
move=> x y mM ev1 ev2.
pose vx : R.-sfker munit ~> mR R := execP_cst [:: (x, sreal)] [::] 1.
pose vy : R.-sfker [the measurableType _ of (mR R * munit)%type] ~> mR R := execP_cst [:: (x, sreal)] [:: (x, sreal)] 2.
(* move=> ev1 ev2. *)
have -> : v1 = letin' (vx) (letin' (vy) (ret (measurable_fun_pair var2of3' var1of3'))).
(*move=> H0 H1.*)
apply: (evalP_uniq ev1).
apply/E_letin /E_letin.
rewrite /vx /execP_cst /ssr_have /sval/=.
by case: cid => // ? h.
rewrite /vy /execP_cst /ssr_have /sval/=.
by case: cid => // ? h.
(*have -> : (vx H0 = ret (kr 1)).
  rewrite /vx /execP /ssr_have /sval.
  case: cid => ? h.
  apply: esym.
  apply: evalP_uniq h.
  apply/E_return /E_real.
apply/E_return /E_real.
have -> : (vy H1 = ret (kr 2)).
  rewrite /vy /execP /ssr_have /sval.
  case: cid => ? h.
  apply: esym.
  apply: evalP_uniq h.
  apply/E_return /E_real.
apply/E_return /E_real.*)
apply/E_return /E_pair.
have -> : (var2of3' = (@mvarof R [:: (y, sreal); (x, sreal)] 1 (false_index_size (_ : (x \in map fst [:: (y, sreal); (x, sreal)]))))) by [].
apply/(@E_var R [:: (y, sreal); (x, sreal)] x).
have -> : (var1of4' = (@mvarof R [:: (y, sreal); (x, sreal)] 0 (false_index_size (_ : (y \in map fst [:: (y, sreal); (x, sreal)]))))) by [].
apply/(@E_var R [:: (y, sreal); (x, sreal)] y is_true_true).
(*  by [].
  by []. *)
pose vy' : R.-sfker munit ~> mR R := execP_cst  [::] [::] 2.
pose vx' : R.-sfker [the measurableType _ of (mR R * munit)%type] ~> mR R :=    execP_cst [:: (y, sreal)] [:: (y, sreal)] 1.
have -> : v2 = letin' (vy') (letin' (vx') (ret (measurable_fun_pair var1of3' var2of3'))).
(*move=> H2 H3.*)
apply: (evalP_uniq ev2).
apply/E_letin /E_letin.
rewrite /vy' /execP_cst /ssr_have /sval/=.
case: cid => //.
rewrite /vx' /execP_cst /ssr_have /sval/=.
case: cid => //.
(*
have -> : (vy' H2 = ret (kr 2)).
  rewrite /vy' /execP /ssr_have /sval.
  case: cid => ? h.
  apply: esym.
  apply: evalP_uniq h.
  apply/E_return /E_real.
apply/E_return /E_real.
have -> : (vx' H3 = ret (kr 1)).
  rewrite /vx' /execP /ssr_have /sval.
  case: cid => ? h.
  apply: esym.
  apply: evalP_uniq h.
  apply/E_return /E_real.
apply/E_return /E_real.*)
apply/E_return /E_pair.
have -> : (var1of3' = (@mvarof R [:: (x, sreal); (y, sreal)] 0 (false_index_size (_ : (x \in map fst [:: (x, sreal); (y, sreal)]))))) by [].
apply/(@E_var R [:: (x, sreal); (y, sreal)] x is_true_true).
have -> : (var2of3' = (@mvarof R [:: (x, sreal); (y, sreal)] 1 (false_index_size (_ : (y \in map fst [:: (x, sreal); (y, sreal)]))))) by [].
apply/(@E_var R [:: (x, sreal); (y, sreal)] y is_true_true).
(*  by []. by [].*)
(*move=> H0 H1 H2 H3.*)
rewrite !letin'E.
under eq_integral.
  move=> x0 _.
  rewrite letin'E /=.
  have -> : vy (x0, t) = vy' t.
  rewrite /vy /vy' /execP /ssr_have /sval.
  rewrite /execP_cst /ssr_have /sval/=.
  case: cid => sy.
  case: cid => sy'.
  move=> er1 er2.
  apply: evalP_uni_new.
  exact: er1.
  exact: er2.
  over.
apply esym.
under eq_integral.
  move=> x0 _.
  rewrite letin'E /=.
  (* have := @evalP_uni_new x vx vx'. *)
  rewrite (@evalP_uni_new y 1 vx vx'); last 2 first.
  (* rewrite -(@tt' sreal sreal (vx H0)). *)
  rewrite /vx /execP_cst /ssr_have /sval/=.
  by case: cid.
  rewrite /vx' /execP_cst /ssr_have /sval/=.
  by case: cid.
  over.
rewrite /=.
rewrite (sfinite_fubini
  [the {sfinite_measure set (mR R) -> \bar R} of VX t]
  [the {sfinite_measure set (mR R) -> \bar R} of VY t]
  (fun t => \d_(t.1, t.2) M)) //; last first.
apply/EFin_measurable_fun => /=.
rewrite (_ : (fun x => _) = @mindic _ [the measurableType _ of (mR R * mR R)%type] R _ mM).
by apply: measurable_fun_indic.
by apply/funext => -[].
Qed.

End eval_prop.

Section example.

Local Open Scope ring_scope.
Variables (R : realType).

Notation "r '%:r'" := (exp_real r) (at level 2, left associativity).
Notation "% x" := (exp_var x _ erefl) (at level 4).
Notation Ret := exp_return.
Notation If := exp_if.
Notation "'Let' x <= e1 'In' e2" := (exp_letin _ x erefl e1 e2) (at level 40, x, e1, e2 at next level).

Example pgm1 : expD [::] (sprob sbool) := exp_norm (
  Let "x" <= exp_sample_bern [::] (2 / 7%:R)%:nng p27 In 
  Let "r" <= If (@exp_var R [:: ("x", sbool)] "x" _ erefl) 
    (Ret 3%:r) (Ret 10%:r) In
  Let "_" <= exp_score 
  (exp_poisson 4 (@exp_var R [:: ("r", sreal); ("x", sbool)] "r" _ erefl)) In Ret %"x"). 

Print pgm1.

Definition sample_bern : R.-sfker munit ~> mbool := 
  sample [the probability _ _ of bernoulli p27].
Definition ite_3_10 : 
  R.-sfker [the measurableType _ of (mbool * munit)%type] ~> (mR R) :=
  ite var1of4' (ret k3) (ret k10).
Definition score_poi :
  R.-sfker [the measurableType _ of ((mR R) * (mbool * munit)%type)%type] ~> munit :=
  score (measurable_funT_comp (mpoisson 4) var1of4').

Local Definition kstaton_bus'' := 
  letin' sample_bern 
    (letin' ite_3_10 
      (letin' score_poi (ret var3of4'))).

Example ev1 : @evalD R [::] _ pgm1 _ (measurable_fun_normalize kstaton_bus'').
Proof.
apply/E_norm /E_letin /E_letin /E_letin.
apply/E_sample.
apply/E_ifP.
have -> : (var1of4' = (@mvarof R [:: ("x", sbool)] 0 (false_index_size (_ : "x" \in map fst [:: ("x", sbool)])))) by done.
exact: (@E_var R [:: ("x", sbool)] "x").
apply/E_return /E_real.
apply/E_return /E_real.
apply/E_score /E_poisson.
have -> : (var1of4' = (@mvarof R [:: ("r", sreal); ("x", sbool)] 0 (false_index_size (_ : "r" \in map fst [:: ("r", sreal); ("x", sbool)])))) by done.
exact: (@E_var R [:: ("r", sreal); ("x", sbool)] "r").
apply/E_return.
have -> : (var3of4' = (@mvarof R [:: ("_", sunit); ("r", sreal); ("x", sbool)] 2 (false_index_size (_ : "x" \in map fst [:: ("_", sunit); ("r", sreal); ("x", sbool)])))) by done.
exact: (@E_var R [:: ("_", sunit); ("r", sreal); ("x", sbool)] "x").
Qed.

End example.