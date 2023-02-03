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

(* 
define letin': 
change type of domain of k to (Y * X) from (X * Y)
*)

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

(* new notation with letin' *)
Notation var1of3' := (@measurable_fun_fst _ _ _ _).
Notation var2of3' := (measurable_fun_comp (@measurable_fun_fst _ _ _ _) (@measurable_fun_snd _ _ _ _)).
Notation var3of3' := (measurable_fun_comp (@measurable_fun_fst _ _ _ _) (measurable_fun_comp (@measurable_fun_snd _ _ _ _) (@measurable_fun_snd _ _ _ _))).

Notation var1of4' := (@measurable_fun_fst _ _ _ _).
Notation var2of4' := (measurable_fun_comp (@measurable_fun_fst _ _ _ _) (@measurable_fun_snd _ _ _ _)).
Notation var3of4' := (measurable_fun_comp (@measurable_fun_fst _ _ _ _) (measurable_fun_comp (@measurable_fun_snd _ _ _ _) (@measurable_fun_snd _ _ _ _))).
Notation var4of4' := (measurable_fun_comp (@measurable_fun_fst _ _ _ _) (measurable_fun_comp (@measurable_fun_snd _ _ _ _) (measurable_fun_comp (@measurable_fun_snd _ _ _ _) (@measurable_fun_snd _ _ _ _)))).

Section string_eq.

Definition string_eqMixin := @EqMixin string eqb eqb_spec.
Canonical string_eqType := EqType string string_eqMixin.

End string_eq.

Section expression.
Variable (R : realType).

Inductive expD : Type :=
| exp_var  : string -> expD
| exp_unit : expD
| exp_bool : bool -> expD
| exp_real : R -> expD
| exp_pair : expD -> expD -> expD
(* | exp_plus : expD -> expD -> expD *)
(* | val_unif : val *)
| exp_bernoulli : {nonneg R} -> expD
| exp_poisson : nat -> expD -> expD
| exp_norm : expP -> expD
(* | exp_if : forall z, expD -> exp z -> exp z -> exp z *)
with expP :=
| exp_if : expD -> expP -> expP -> expP
| exp_letin : string -> expP -> expP -> expP
| exp_sample : expD -> expP
| exp_score : expD -> expP
| exp_return : expD -> expP.

Local Open Scope ring_scope.

Definition pgm1 : expP := exp_sample (exp_bernoulli (2 / 7%:R)%:nng).
Definition pgm2 : expP := exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng)) (exp_return (exp_var "x")).
Example pgm3 : expD := exp_norm (
  exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng)) (
  exp_letin "r" (exp_if (exp_var "x") (exp_return (exp_real 3%:R)) (exp_return (exp_real 10%:R))) (
  exp_letin "_" (exp_score (exp_poisson 4 (exp_var  "r"))) (
  exp_return (exp_var "x"))))).

End expression.

Arguments exp_unit {R}.
Arguments exp_bool {R}.
Arguments exp_var {R}.

Section context.

Definition context := seq (string * Type)%type.

Definition context' := seq (string * sigT measurableType)%type.

End context.

Import Notations.

Section typeof.
Variable (R : realType).

Check kernel _ _ _ : Type.

Fixpoint typeofD (G : context') (e : expD R) : Type :=
  match e with
  | exp_unit => munit
  | exp_bool b => mbool
  | exp_real r => mR R
  | exp_pair e1 e2 => (typeofD G e1 * typeofD G e2)%type
  | exp_bernoulli nng => munit -> mbool
  | exp_poisson n e => munit -> (mR R)
  | _ => munit
  end
with typeofP (G : context') (e : expP R) : Type :=
  match e with
  | exp_if _ e _ => typeofP G e
  | exp_letin _ e1 e2 => munit
  | exp_sample e => R.-sfker munit ~> mbool
  | exp_score e => R.-sfker munit ~> (mR R)
  | exp_return e => R.-sfker munit ~> munit
  end.

Example typeofpgm1 : typeofP [::] (pgm1 R) = R.-sfker munit ~> mbool.
Proof. done. Qed.

End typeof.

Section size.
Variable (R : realType).

Fixpoint sizeD (e : expD R) : nat :=
  match e with
  | exp_pair e1 e2 => sizeD e1 + sizeD e2 + 1
  | exp_poisson _ e => sizeD e + 1
  | exp_norm e => sizeP e + 1
  | _ => 1
  end
with sizeP (e : expP R) :=
  match e with
  | exp_if e1 e2 e3 => sizeD e1 + sizeP e2 + sizeP e3 + 1
  | exp_letin _ e1 e2 => sizeP e1 + sizeP e2 + 1
  | exp_sample e => sizeD e + 1
  | exp_score e => sizeD e + 1
  | exp_return e => sizeD e + 1
end.

End size.


Section free_variables.
Variable (R : realType).

Local Open Scope seq_scope.
Fixpoint free_varsD (e : expD R) : seq _ :=
  match e with
  | exp_var x => [:: x]
  | exp_poisson _ e => free_varsD e
  | _ => [::]
  end
with free_varsP (e : expP R) : seq _ :=
  match e with
  | exp_if e1 e2 e3 => free_varsD e1 ++ free_varsP e2 ++ free_varsP e3
  | exp_letin x e1 e2 => free_varsP e1 ++ rem x (free_varsP e2)
  | exp_sample e => free_varsD e
  | exp_score e => free_varsD e
  | exp_return e => free_varsD e
  end.

Example fv1 : free_varsP (pgm1 R) = [::].
Proof. done. Qed.
Example fv2 : free_varsP (pgm2 R) = [::].
Proof. done. Qed.
Example fv3 : free_varsD (pgm3 R) = [::].
Proof. done. Qed.

Example fv4 : free_varsP (exp_letin "x" (exp_return (exp_var "y")) (exp_return (exp_var "x"))) = [:: "y"].
Proof. done. Qed.

Local Open Scope nat_scope.
Lemma fv_sizeD (e : expD R) : size (free_varsD e) <= sizeD e.
Proof.
elim: e => //= n e IH.
apply: (leq_trans IH (leq_addr 1 _)).
Qed.

Lemma fv_sizeP (e : expP R) : size (free_varsP e) <= sizeP e.
Proof.
elim: e => //=.
move=> e e0 IH0 e1 IH1.
rewrite !size_cat.
have -> : sizeP (exp_if e e0 e1) = sizeD e + sizeP e0 + sizeP e1 + 1.
by done.
have H : size (free_varsD e) <= sizeD e by rewrite fv_sizeD.
apply: (leq_trans _ (leq_addr 1 _)).
rewrite addnA.
apply: leq_add => //.
apply: leq_add => //.
move=> s e IH e0 IH0.
have H : size (rem s (free_varsP e ++ free_varsP e0)) <= size (free_varsP e ++ free_varsP e0).
case sin : (s \in free_varsP e ++ free_varsP e0).
by rewrite (size_rem sin) leq_pred.
rewrite rem_id //.
by rewrite sin.
admit.
(* apply: (leq_trans H). *)
(* rewrite size_cat. *)
(* apply: (leq_trans (leq_add IH IH0) (leq_addr 1 _)). *)
move=> e; apply /(leq_trans (fv_sizeD e)) /leq_addr.
move=> e; apply /(leq_trans (fv_sizeD e)) /leq_addr.
move=> e; apply /(leq_trans (fv_sizeD e)) /leq_addr.
Admitted.

End free_variables.

Section type_checking.
Variable (R : realType).

Variables (d : _) (T : measurableType d).

Inductive type_checkD : context -> expD R -> Type -> Prop :=
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

with type_checkP : context -> expP R -> Type -> Prop :=
| tc_sample G e d (A : measurableType d) : type_checkD G e (probability A R) ->
  type_checkP G (exp_sample e) A
| tc_return G e A : type_checkD G e A -> type_checkP G (exp_return e) A
| tc_score G e : type_checkD G e R -> type_checkP G (exp_score e) unit

| tc_if G e1 e2 e3 A : type_checkD G e1 bool ->
  type_checkP G e2 A -> type_checkP G e3 A -> type_checkP G (exp_if e1 e2 e3) A
| tc_letin G v e1 e2 A B : type_checkP G e1 A -> type_checkP ((v, A) :: G) e2 B ->
  type_checkP G (exp_letin v e1 e2) B.

Example tc_1 : type_checkP [::] (pgm1 R) bool.
Proof. apply/tc_sample /tc_bernoulli. Qed.

Example tc_2 : type_checkP [::] (pgm2 R) bool.
Proof.
apply/(@tc_letin _ _ _ _ bool).
apply/tc_sample /tc_bernoulli.
apply/tc_return /(@tc_var [::] "x").
Qed.

Example tc_3 : type_checkD [::] (pgm3 R) (probability mbool R).
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

Section eval.

(* TODO: use ordinal *)
Definition typ2 {d1 d2} (T1 : measurableType d1) (T2 : measurableType d2)
(i : nat) : {d & measurableType d} :=
  if i == O then existT _ d1 T1 else existT _ d2 T2.

Definition var_i_of2 {dA dB} {A : measurableType dA} {B : measurableType dB} (i : nat)
    : {f : [the measurableType _ of (A * B)%type] -> projT2 (typ2 A B i) | measurable_fun setT f} :=
  match i with
  | 0 => exist (fun x => measurable_fun setT x) (_ : A * B -> A) var1of2
  | _ => exist (fun x => measurable_fun setT x) (snd : A * B -> B) var2of2
  end.

Definition typ3 {d1 d2 d3} (T1 : measurableType d1) (T2 : measurableType d2) (T3 : measurableType d3) (i : nat)
    : {d & measurableType d} :=
  match i with
  | 0 => existT _ d1 T1
  | 1 => existT _ d2 T2
  | _ => existT _ d3 T3
  end.

Definition var_i_of3 {dA dB dC} {A : measurableType dA} {B : measurableType dB} {C : measurableType dC} (i : nat)
  : {f : [the measurableType _ of (A * B * C)%type] -> projT2 (typ3 A B C i)
| measurable_fun setT f} :=
  match i with
  | 0 => exist (fun x => measurable_fun setT x) (_ : A * B * C -> A) var1of3
  | 1 => exist (fun x => measurable_fun setT x) (_ : A * B * C -> B) var2of3
  | _ => exist (fun x => measurable_fun setT x) (_ : A * B * C -> C) var3of3
  end.

Definition typ4 {d1 d2 d3 d4} (T1 : measurableType d1) (T2 : measurableType d2) (T3 : measurableType d3) (T4 : measurableType d4) i
    : {d & measurableType d} :=
  match i with
  | 0 => existT _ d1 T1
  | 1 => existT _ d2 T2
  | 2 => existT _ d3 T3
  | _ => existT _ d4 T4
  end.

(* 'I_(size t).+1 *)
Definition typn (h : {d & measurableType d}) (t : seq {d & measurableType d}) (i : nat) : {d & measurableType d} :=
  match i with
  | 0 => h
  | n.+1 => nth h t n
  end.

Fixpoint prod_type (l : list Type): Type :=
  match l with
  | [::] => unit
  | h :: t => (h * prod_type t)%type
  end.

Fixpoint prod_disp (l : list measure_display) : measure_display :=
  match l with
  | [::] => default_measure_display
  | h :: t => measure_prod_display (h, (prod_disp t))
  end.

Fixpoint prod_meas1 (l : list {d & measurableType d}) : measure_display :=
  match l with
  | [::] => default_measure_display
  | h :: t => measure_prod_display (projT1 h, (prod_meas1 t))
  end.

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

(* Eval vm_compute in prod_meas (existT _ _ munit :: [::]). *)

Lemma prod_meas_1 : prod_meas (existT _ _ munit :: [::]) = existT _ _ [the measurableType _ of (munit * munit)%type].
Proof. done. Qed.

Lemma prod_meas_2 : prod_meas (existT _ _ mbool :: existT _ _ munit :: [::]) = existT _ _ [the measurableType _ of (mbool * (munit * munit))%type].
Proof. done. Qed.

Eval vm_compute in size (existT _ _ munit :: [::]).

Lemma prod_meas_size_1 (l : list {d & measurableType d}) : size l = 1%N ->
  exists d (T : measurableType d), prod_meas l = existT _ _ [the measurableType _ of (T * munit)%type].
Proof.
destruct l => //.
destruct l => //.
destruct s => /= _.
by exists x, t.
Qed.

Lemma prod_meas_size_2 (l : list {d & measurableType d}) : size l = 2%N ->
  exists d (T : measurableType d) d' (T' : measurableType d'), prod_meas l = existT _ _ [the measurableType _ of (T * (T' * munit))%type].
Proof.
destruct l => //.
destruct l => //.
destruct l => //.
destruct s.
destruct s0 => /= _.
by exists x, t, x0, t0.
Qed.

(*
value ::= measurable function (evalD)
        | kernel (evalP)
        | probability (eval) (-> into measurable fun.?)
*)

Lemma measurable_fun_normalize (R : realType) dX (X : measurableType dX)
   dY (Y : measurableType dY) (k : R.-sfker X ~> Y) (P : probability Y R) :
  measurable_fun setT (normalize k : X -> pprobability Y R).
Proof.
Admitted.

Variable R : realType.

Definition same_kernel d1 d2 d3 (A : measurableType d1)
  (A' : measurableType d2) (B : measurableType d3) (k : R.-sfker A ~> B) (k' : R.-sfker A' ~> B) : Prop.
  Abort.

(* 
Fixpoint exec (l : context') (G := prod_meas (map snd l)) dT (T : measurableType dT) (e : expD R) : {f : projT2 G -> T | measurable_fun setT f} :=
  match e with
  | exp_var x => forall (H : x \in (map fst l)), let i := seq.index x (map fst l) in 
  existT _ _
  (* (@varof l i (false_index_size H)) *)
  (@mvarof l i (false_index_size H))

  | exp_unit => existT _ (cst tt) ktt
  | exp_bool b => existT _ (cst b) (kb b)
  | exp_real r => existT _ (cst r) (kr r)
  | exp_pair e1 e2 => existT _ _ (@measurable_fun_pair _ _ _ (projT2 G) _ _ (projT1 (exec e1)) (projT1 (exec e2)) (projT2 (exec e1)) (projT2 (exec e2)))
  | exp_poisson k e => (poisson k \o (projT1 (exec e))) 
  (measurable_fun_comp (mpoisson k) (projT2 (exec e)))

  (* | _ => existT _ (cst tt) ktt *)
  end. *)

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

Definition context'' := seq (string * types)%type.

Definition varof2 (l : context'') (i : nat) (li : (i < size l)%nat) :
  projT2 (typei (prods (map snd l))) ->
  projT2 (typei (nth units (map snd l : seq types) i)).
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

Lemma false_index_size2 (x : string) (l : context'') (H : x \in (map fst l)) :
	(seq.index x (map fst l) < size l)%nat.
Proof. by rewrite -(size_map fst) index_mem. Qed.

Lemma mvarof2 (l : context'') (i : nat) (li : (i < size l)%nat) :
  measurable_fun setT (@varof2 l i li).
Proof.
destruct l => //.
destruct i.
exact: (@measurable_fun_fst _ _ _ _).
destruct l => //.
destruct i.
exact: (measurable_fun_comp (@measurable_fun_fst _ _ _ _) (@measurable_fun_snd _ _ _ _)).
destruct l => //.
destruct i.
(* exact: (measurable_fun_comp (measurable_fun_comp (@measurable_fun_fst _ _ _ _) (@measurable_fun_snd _ _ _ _)) (@measurable_fun_snd _ _ _ _)). *)
exact: (measurable_fun_comp (@measurable_fun_fst _ _ _ _) (measurable_fun_comp (@measurable_fun_snd _ _ _ _) (@measurable_fun_snd _ _ _ _))). (* var3of3 *)
destruct l => //.
destruct i.
exact: var4of4'.
(* ??? *)
Admitted.

(* Fixpoint type_denote (e : expD') : types :=
  match e with
  | _exp_unit => units
  | _exp_bool b => bools
  | _exp_real r => reals
  | _exp_pair e1 e2 => pairs (type_denote e1) (type_denote e2)
  end. *)

(* projT2 (typei (prods (map snd l))) *)
(* Program Fixpoint execD (l : context'') (T : types) (e : expD') :=
  match e 
  return {f : projT2 (typei (prods (map snd l))) -> projT2 (typei (type_denote e)) & measurable_fun _ f} 
  (* return measurable_fun setT (_ : projT2 (typei (prods (map snd l))) -> projT2 (typei (type_denote e))) *)
  with
  | _exp_unit => existT _ _ ktt
  | _exp_bool b => existT _ _ (kb b)
  | _exp_real r => existT _ _ (kr r)
  | _exp_pair e1 e2 =>
      let G := (prods (map snd l)) in
      let A := type_denote e1 in
      let B := type_denote e2 in
      let f1 := projT1 (execD l _ e1) in
      let f2 := projT1 (execD l _ e2) in
      let mf1 := projT2 (execD l _ e1) in
      let mf2 := projT2 (execD l _ e2) in
      existT _
      ((fun x : projT2 (typei G) => (f1 x, f2 x))) 
      (@measurable_fun_pair _ _ _ (projT2 (typei G)) (projT2 (typei A)) (projT2 (typei B)) f1 f2 mf1 mf2)
    (* @measurable_fun_pair 
    _ _ _ _ _ _ _ _ _ _ _ _ _ *)
    (* (_ : projT2 (typei (prods (map snd l))) -> projT2 (typei (type_denote e1))) (_ : projT2 (typei (prods (map snd l))) -> projT2 (typei (type_denote e2))) (execD l (type_denote e1) e1) (execD l (type_denote e2) e2) *)
  end. *)


Definition innertype (Y : types) dZ (Z : measurableType dZ) G (k2 : R.-sfker projT2 (typei (pairs Y G)) ~> Z) := Y.

Inductive evalD : forall (l : context'') 
(* (G := prod_meas (map snd l)) *)
    (T : types) (e : expD R) 
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

| E_var : forall (l : context'') (T : types) (x : string) (H : x \in (map fst l)),
  let i := seq.index x (map fst l) in
  (* @evalD _ [the measurableType _ of (T1 * T2)%type] l _ _ (exp_var x) (proj1_sig (var_i_of2 i.+1)) (proj2_sig (var_i_of2 i.+1)) *)
  @evalD l _ (exp_var x) (@varof2 l i (false_index_size2 H))
  (@mvarof2 l i (false_index_size2 H))

| E_bernoulli : forall l (r : {nonneg R}) (r1 : (r%:num <= 1)%R),
  @evalD l (probs bools) (exp_bernoulli r) (cst [the probability _ _ of bernoulli r1]) (measurable_fun_cst _)

| E_poisson : forall l k e f mf,
  @evalD l reals e f mf ->
  @evalD l reals (exp_poisson k e) (poisson k \o f) 
  (measurable_fun_comp (mpoisson k) mf)

| E_norm : forall l e (T : types) (k : R.-sfker _ ~> projT2 (typei T)),
  @evalP l T e k ->
  @evalD l (probs T) (exp_norm e)
  (normalize k : _ -> pprobability _ _) 
  (measurable_fun_normalize k point)

with evalP : forall (l : context'') (T : types),
  expP R ->
  R.-sfker (projT2 (typei (prods (map (snd) l)))) ~> projT2 (typei T) ->
  Prop :=
| E_sample : forall l (T : types) (e : expD R) (p : pprobability (projT2 (typei T)) R),
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

| E_letin : forall (l : context'') (G := prods (map snd l)) (Y Z : types) (x : string) e1 e2
  (k1 : R.-sfker projT2 (typei G) ~> projT2 (typei Y))
  (k2 : R.-sfker (typei2 (pairs Y G)) ~> projT2 (typei Z)) ,
  @evalP l Y e1 k1 ->
  (* l' = ((x, Y) :: l) -> *)
  @evalP ((x,Y)::l)%SEQ Z e2 k2 ->
  @evalP l Z (exp_letin x e1 e2) (letin' k1 k2)
.
E_var
End eval.

Ltac inj H := apply Classical_Prop.EqdepTheory.inj_pair2 in H.

Scheme evalD_mut_ind := Induction for evalD Sort Prop
with evalP_mut_ind := Induction for evalP Sort Prop.

Scheme expD_mut_ind := Induction for expD Sort Prop
with expP_mut_ind := Induction for expP Sort Prop.

Section inj_f.
Lemma inj_f A B (f g : A -> B) x : f = g -> f x = g x.
Proof. by move=> ->. Qed.

(* Variable (_A _B : Type) (a b : _A). *)
Lemma inj_cst A B b1 b2 : (@cst A B b1) = cst b2 -> b1 = b2.
Proof.
move=> H.
have : (forall (a1 a2 : A), (cst b1) a1 = (cst b2) a2).
move=> a1 a2.
by rewrite (@inj_f _ _ (cst b1) _ _ H).
(* by rewrite /= => ->.
Qed. *)
Admitted.

End inj_f.

Section eval_properties.
Variables (R : realType).

Lemma inv_evalP_exp_letin (l : context'') (G := prods (map snd l)) (Y Z : types) (x : string) e1 e2
  (k: R.-sfker projT2 (typei R (prods [seq i.2 | i <- l])) ~> 
projT2 (typei R Z)) :
  (* (k1 : R.-sfker projT2 (typei R G) ~> projT2 (typei R Y))
  (k2 : R.-sfker projT2 (typei R (pairs Y G)) ~> 
  projT2 (typei R Z)) : *)
  @evalP R l Z (exp_letin x e1 e2) k ->
  forall k1 : R.-sfker projT2 (typei R G) ~> projT2 (typei R Y),
  forall k2 : R.-sfker projT2 (typei R (pairs Y G)) ~> projT2 (typei R Z), 
  @evalP R l Y e1 k1 ->
  @evalP R ((x,Y)::l)%SEQ Z e2 k2 ->
  k = letin' k1 k2.
Proof.
(* induction 1 => //. *)
inversion 1.
subst.
do 2 inj H7.
clear G1 G2.
move=> k0 k3.
Admitted.

Lemma evalD_uniq (l : context'') (G := prods (map (snd) l)) (T : types) (e : expD R) (u v : projT2 (typei R G) -> projT2 (typei R T)) (mu : measurable_fun _ u) (mv : measurable_fun _ v) :
  evalD e mu -> evalD e mv -> u = v.
Proof.
move=> hu.
apply: (@evalD_mut_ind R
  (fun (l : _) (G := prods (map snd l)) (T : types) (e : expD R) (f : projT2 (typei R G) -> projT2 (typei R T)) (mf : measurable_fun setT f) (h1 : evalD e mf) =>
    forall (v : projT2 (typei R G) -> projT2 (typei R T)) (mv : measurable_fun setT v), evalD e mv -> f = v)
  (fun (l : _) (G := prods (map snd l)) (T : types) (e : expP R) (u : R.-sfker projT2 (typei R G) ~> projT2 (typei R T)) (h1 : evalP e u) =>
    forall (v : R.-sfker projT2 (typei R G) ~> projT2 (typei R T)), evalP e v -> u = v)
  _ _ _ _ _ _ _ _ _ _ _ _ _ l T e); last exact: hu.
- 
move=> l' G0 {}mv.
inversion 1.
by do 2 inj H3.
-
move=> l' x G0 {}mv.
inversion 1.
by do 2 inj H3.
-
move=> l' r G0 {}mv.
inversion 1.
by do 2 inj H3.
- (* pair *)
move=> l' G0 A B e1 f1 mf1 e2 f2 mf2 ev1 IH1 ev2 IH2 f {}mv H.
simple inversion H => //.
injection H3 => ? ?; subst A0 B0.
injection H4 => ? ?; subst e0 e3.
subst l0.
do 2 inj H5.
move=> e1f0 e2f3.
have -> := IH1 _ _ e1f0.
by have -> := IH2 _ _ e2f3.
- (* var *)
move=> l' A x H n f mf.
inversion 1.
do 2 inj H7.
by have -> : (H = H1) by exact: Prop_irrelevance.
- (* bernoulli *)
move=> l' r r1 f mf.
inversion 1.
subst.
do 2 inj H3.
by have -> : (r1 = r2) by exact: Prop_irrelevance.
- (* poisson *)
move=> l' k e0 f mf ev IH g mg.
inversion 1.
subst.
do 2 inj H4; clear H5.
by have -> := IH _ _ H3.
- (* norm *)
move=> l' e0 A k ev IH f mf.
inversion 1.
do 2 inj H4.
by have -> := IH _ H3.
- (* sample *)
move=> l' A e0 p ev IH k H.
inversion H.
do 2 inj H3.
have cstp := IH _ _ H4.
by rewrite (inj_cst cstp).
- (* if *)
move=> l' G0 e0 f1 mf1 e2 k2 e3 k3 ev1 IH1 ev2 IH2 ev3 IH3 k.
inversion 1.
do 2 inj H5.
have ? := IH1 _ _ H6.
subst f1.
have -> : (mf1 = mf) by exact: Prop_irrelevance.
have -> := IH2 _ H7.
by have -> := IH3 _ H8.
- (* score *)
move=> l' G0 e0 f mf ev IH k H.
simple inversion H => // ev0.
subst.
do 2 inj H4.
injection H3 => ?.
subst.
have ? := IH _ _ ev0.
subst f0.
by have -> : (mf = mf0) by exact: Prop_irrelevance.
- (* return *)
move=> l' A e0 f mf ev IH k.
inversion 1.
subst.
do 2 inj H5.
have ? := IH _ _ H4.
subst f1.
by have -> : (mf = mf1) by exact: Prop_irrelevance.
- (* letin *)
move=> l' G0 A B x e1 e2 k1 k2 ev1 IH1 ev2 IH2 k H.
inversion H.
have := (@IH1 k1).
rewrite /=.
have Hk := (@inv_evalP_exp_letin l' A B x e1 e2 k H).
(* by apply/esym /Hk. *)
(* subst k.

move=> k.
inversion 1.

 Ainner.
inversion H.
rewrite /innertype in H9.
subst.
do 2 inj H5.
have ? : (A = Y) by admit.
subst.
have ? : (k0 = k1).


simple inversion H => // ev3 ev4.
subst.
do 2 inj H5.
injection H4 => ???; subst e3 e0 x0.
subst.
have ? : (k0 = k1).
have ? : (A = Y).
rewrite //.
have := IH1 _ ev1. *)
Admitted.

Lemma eval_uniqP (l : context'') (G := prods (map snd l)) (T : types) (e : expP R) (u v : R.-sfker projT2 (typei R G) ~> projT2 (typei R T)) :
  evalP e u -> evalP e v -> u = v.
Proof.
move=> hu.
apply: (@evalP_mut_ind R
  (fun (l : _) (G := prods (map snd l)) (T : types) (e : expD R) (f : projT2 (typei R G) -> projT2 (typei R T)) (mf : measurable_fun setT f) (h1 : evalD e mf) =>
    forall (v : projT2 (typei R G) -> projT2 (typei R T)) (mv : measurable_fun setT v), evalD e mv -> f = v)
  (fun (l : _) (G := prods (map snd l)) (T : types) (e : expP R) (u : R.-sfker projT2 (typei R G) ~> projT2 (typei R T)) (h1 : evalP e u) =>
    forall (v : R.-sfker projT2 (typei R G) ~> projT2 (typei R T)), evalP e v -> u = v)
  _ _ _ _ _ _ _ _ _ _ _ _ _ l T e); last exact: hu.
- 
move=> l' G0 {}mv.
inversion 1.
by do 2 inj H3.
-
move=> l' x G0 {}mv.
inversion 1.
by do 2 inj H3.
-
move=> l' r G0 {}mv.
inversion 1.
by do 2 inj H3.
- (* pair *)
move=> l' G0 A B e1 f1 mf1 e2 f2 mf2 ev1 IH1 ev2 IH2 f {}mv H.
simple inversion H => //.
injection H3 => ? ?; subst A0 B0.
injection H4 => ? ?; subst e0 e3.
subst l0.
do 2 inj H5.
move=> e1f0 e2f3.
have -> := IH1 _ _ e1f0.
by have -> := IH2 _ _ e2f3.
- (* var *)
move=> l' A x H n f mf.
inversion 1.
do 2 inj H7.
by have -> : (H = H1) by exact: Prop_irrelevance.
- (* bernoulli *)
move=> l' r r1 f mf.
inversion 1.
subst.
do 2 inj H3.
by have -> : (r1 = r2) by exact: Prop_irrelevance.
- (* poisson *)
move=> l' k e0 f mf ev IH g mg.
inversion 1.
subst.
do 2 inj H4; clear H5.
by have -> := IH _ _ H3.
- (* norm *)
move=> l' e0 A k ev IH f mf.
inversion 1.
do 2 inj H4.
by have -> := IH _ H3.
- (* sample *)
move=> l' A e0 p ev IH k H.
inversion H.
do 2 inj H3.
have cstp := IH _ _ H4.
by rewrite (inj_cst cstp).
- (* if *)
move=> l' G0 e0 f1 mf1 e2 k2 e3 k3 ev1 IH1 ev2 IH2 ev3 IH3 k.
inversion 1.
do 2 inj H5.
have ? := IH1 _ _ H6.
subst f1.
have -> : (mf1 = mf) by exact: Prop_irrelevance.
have -> := IH2 _ H7.
by have -> := IH3 _ H8.
- (* score *)
move=> l' G0 e0 f mf ev IH k H.
simple inversion H => // ev0.
subst.
do 2 inj H4.
injection H3 => ?.
subst.
have ? := IH _ _ ev0.
subst f0.
by have -> : (mf = mf0) by exact: Prop_irrelevance.
- (* return *)
move=> l' A e0 f mf ev IH k.
inversion 1.
subst.
do 2 inj H5.
have ? := IH _ _ H4.
subst f1.
by have -> : (mf = mf1) by exact: Prop_irrelevance.
- (* letin *)
move=> l' G0 A B x e1 e2 k1 k2 ev1 IH1 ev2 IH2 k H.
rewrite /=.
have Hk := (@inv_evalP_exp_letin l' A B x e1 e2 k H).
by apply/esym /Hk.
Qed.

Axiom largest_var_in_expD : forall e : expD R, nat.

Lemma eval_full dA (A : measurableType dA) l s :
  prod_meas s = existT _ _ A ->
  forall e, (largest_var_in_expD e <= size s)%nat ->
    exists (B : types) f (mf : measurable_fun _ f), @evalD R l B e f mf.
Proof.
move=> Hs e He.
induction e.
admit.
exists units.
exists (cst tt).
exists ktt.
apply: E_unit.
exists bools.
exists (cst b).
exists (kb b).
apply: E_bool.
exists reals.
exists (cst s0).
exists (kr s0).
apply: E_real.
destruct IHe1.
admit.
destruct IHe2.
admit.
destruct H.
destruct H0.
destruct H.
destruct H0.
exists (pairs x x0).
exists (fun x => (x1 x, x2 x)).
eexists.
apply/E_pair /H0 /H.
exists (probs bools).
eexists.
eexists.
apply: E_bernoulli.
admit.
destruct IHe.
admit.
destruct H.
destruct H.
exists reals.
eexists.
eexists.
apply: E_poisson.
apply: (measurable_fun_comp (mpoisson n)).
admit.
move=> Hyp0.
admit.
eexists.
eexists.
eexists.
apply: E_norm.
Admitted.

Definition execD (dA dB : measure_display) (A : measurableType dA) (B : measurableType dB) :
  expD R -> {f : A -> B & measurable_fun setT f}.
Proof.
move=> e.
have h := eval_full [::].
exact: (proj1_sig h).
(* Defined. *)
Admitted.

Definition execP (dA dB : measure_display) (A : measurableType dA) (B : measurableType dB) :
  expP R -> R.-sfker A ~> B.
Proof.
move=> e.
have h := eval_full [::].
(* exact: (proj1_sig h). *)
(* Defined. *)
Admitted.

End eval_properties.

Section letinC.
Variables (dG : _) (G : measurableType dG) (dT : _) (T : measurableType dT)
  (dU : _) (U : measurableType dU) (R : realType).
Variables (A B : types).

Lemma tt' t (t' : R.-sfker typei2 R (pairs B units) ~> typei2 R A) : forall x, t =1 fun z => t' (x, z).
Admitted.

Lemma uu' u (u' : R.-sfker typei2 R (pairs A units) ~> typei2 R B) : forall y, u =1 fun z => u' (y, z).
Admitted.

(* Lemma __ : @evalD R
  [:: ("y", existT _ _ U);
          ("x", existT _ _ T)] _ _
  (exp_var "y") fst var1of2.
Proof.
have -> : (var1of4' = (@mvarof R [:: ("y", existT _ _ U); ("x", existT _ _ T)] 0 (false_index_size (_ : ("y" \in map fst [:: ("y", existT _ _ U); ("x", existT _ _ T)]))))) by done.
exact: (@E_var R [:: ("y", existT _ _ U); ("x", existT _ _ T)] _ _ _ _ "y").
Qed. *)


Lemma letinC' (t u : expP R) (v1 v2 : R.-sfker _ ~> _) z M :
  let x := "x" in let y := "y" in
  measurable M ->
  @evalP R [::] (pairs B A)
  (exp_letin x t (exp_letin y u
    (exp_return (exp_pair (exp_var x) (exp_var y))))) v1 ->
  @evalP R [::] (pairs B A)
  (exp_letin y u (exp_letin x t
    (exp_return (exp_pair (exp_var x) (exp_var y))))) v2 ->
  v1 z M = v2 z M.
Proof.
move=> x y mM.
pose vt : R.-sfker typei2 R units ~> typei2 R A := execP munit (typei2 R A) t.
pose vu : R.-sfker typei2 R (pairs A units) ~> typei2 R B := execP _ _ u.
move=> evalv1 evalv2.
have -> : v2 = (letin' vt (letin' vu (ret (measurable_fun_pair var1of3' var2of3')))).
apply: (eval_uniqP evalv2).
apply /E_letin /E_letin.
admit. admit.
apply /E_return /E_pair.
have -> : (var1of4' = (@mvarof2 R [:: (x, B); (y, A)] 0 (false_index_size2 (_ : (x \in map fst [:: (x, B); (y, A)]))))) by done.
apply: (@E_var R [:: (x, B); (y, A)] _ x) => //.
have -> : (var2of4' = (@mvarof2 R [:: (x, B); (y, A)] 1 (false_index_size2 (_ : (y \in map fst [:: (x, B); (y, A)]))))) by done.
apply: (@E_var R [:: (x, B); (y, A)] _ y) => //.
pose vt' : R.-sfker typei2 R (pairs B units) ~> typei2 R A := execP _ _ t.
pose vu' : R.-sfker munit ~> typei2 R B := execP _ _ u.
have -> : v1 = (letin' vu' (letin' vt' (ret (measurable_fun_pair var2of3' var1of3')))).
apply: (eval_uniqP evalv1).
apply/E_letin /E_letin.
admit. admit.
apply/E_return /E_pair.
have -> : (var2of4' = (@mvarof2 R [:: (y, A); (x, B)] 1 (false_index_size2 (_ : (x \in map fst [:: (y, A); (x, B)]))))) by done.
apply: (@E_var R [:: (y, A); (x, B)] _ x) => //.
have -> : (var1of4' = (@mvarof2 R [:: (y, A); (x, B)] 0 (false_index_size2 (_ : (y \in map fst [:: (y, A); (x, B)]))))) by done.
apply: (@E_var R [:: (y, A); (x, B)] _ y) => //.
rewrite !letin'E.
under eq_integral.
  move=> x0 _.
  rewrite letin'E /=.
  rewrite -(tt' vt).
  (* under eq_integral do rewrite retE /=. *)
  over.
rewrite (sfinite_fubini _ _ (fun x => \d_(x.1, x.2) M))//; last 3 first.
exact: sfinite_kernel_measure.
exact: sfinite_kernel_measure.
apply/EFin_measurable_fun => /=.
rewrite (_ : (fun x => _) = @mindic _ (typei2 R (pairs B A)) R _ mM).
admit.
by apply/funext => -[].
apply eq_integral => /= x0 _.
rewrite letin'E/= -(uu' vu').
by apply eq_integral => /= y0 _.
Admitted.

Lemma letinC'' (t u : expP R) :
  (exp_letin "x" t (exp_letin "y" u (exp_return (exp_var "x")))) =
  (exp_letin "y" u (exp_letin "x" t (exp_return (exp_var "x")))).
Proof.
Admitted.

End letinC.
