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

Section association_list.

Fixpoint assoc_get {A : eqType} {B : Type} (a : A) (l : seq (A * B)) : option B :=
  match l with
  | nil => None
  | h :: t => if h.1 == a then Some h.2 else assoc_get a t
  end.

Lemma __ : assoc_get "b" [:: ("a", 1%nat); ("b", 2%nat)] = Some 2%nat.
Proof. rewrite //. Abort.

End association_list.

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

(*
Inductive type :=
| ty_unit
| ty_bool
| ty_real.

Definition interp_mtype (ty : type) :=
  match ty with
  | ty_unit => munit
  | ty_bool => mbool
  | ty_real => mR R
  end.

Definition typ_of_exp (l : seq (string * type)%type) (e : expD) :=
  match e with
  (* | exp_var v => if assoc_get v l is Some t then interp_mtype t else munit *)
  | exp_real r => mR R
  | exp_bool b => mbool
  | exp_unit => munit
  (* | exp_bernoulli r => mR R *)
  end.

Set Printing All.
Definition execD (l : seq (string * type)%type) (e : expD) : forall d (A : measurableType d), {f : A -> (typ_of_exp l e) | measurable_fun setT f} :=
  match e in expD
  return forall d (A : measurableType d), {f : A -> (typ_of_exp l e) | measurable_fun setT f}
  with
  | exp_var v => fun d A => @exist _ _ _ var1of2
  | exp_real r => fun d A => @exist _ _ (@cst A (mR R) r) (kr r)
  | exp_bool b => fun d A => @exist _ _ (@cst A mbool b) (kb b)
  | exp_unit => fun _ _ => @exist _ _ _ ktt
  (* | _ => fun=> ktt *)
  end.
*)

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
(* 
(* Idea *)
Inductive Env :=
| Env2 : forall dA, measurableType dA ->
         forall dB, measurableType dB -> Env
| Env3 : forall dA, measurableType dA ->
         forall dB, measurableType dB ->
         forall dC, measurableType dC -> Env.

Inductive hlist : (list Set) -> Type :=
| HNil : hlist nil
| HCons : forall (x:Set) (ls:list Set), x -> hlist ls -> hlist (x::ls).
 *)

Check existT measurableType default_measure_display munit =
      existT measurableType ((default_measure_display,default_measure_display).-prod)%mdisp [the measurableType _ of (munit * munit)%type].

Definition varof (l : context') (i : nat) (li : (i < size l)%nat) :
  projT2 (prod_meas (map snd l)) ->
  projT2 (nth (existT measurableType default_measure_display munit) (map snd l) i).
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

Example varof_0 : (@varof (("x", existT measurableType _ munit)::nil) O erefl) = fst :> _ -> munit.
Proof. done. Abort.

Check (@varof (("x", existT measurableType _ munit)::("y", existT measurableType _ mbool)::nil) 1 erefl) : _ -> mbool.

Example varof_1 : (@varof (("x", existT measurableType _ munit)::("y", existT measurableType _ mbool)::nil) 1 erefl) = (fst \o snd : _ -> mbool).
Proof. done. Abort.

Eval compute in (@varof (("x", existT measurableType _ munit)::nil) O erefl).
Eval compute in (@varof (("x", existT measurableType _ munit)::("y", existT measurableType _ mbool)::nil) O erefl).
Check  (@varof (("x", existT measurableType _ munit)::("y", existT measurableType _ mbool)::nil) 1 erefl)
: _ -> mbool.

Fixpoint freevarsD (e : expD R) : nat := 
  match e with
  | exp_norm e => freevarsP e
  | _ => 0
  end 
with freevarsP (e : expP R) : nat :=
  match e with
  | exp_sample e => freevarsD e
  | exp_letin x e1 e2 => freevarsP e1 + freevarsP e2 + 1
  | _ => 0
  end.

Compute freevarsP (exp_sample (pgm3 R)).

Lemma mvarof (l : context') (i : nat) (li : (i < size l)%nat) :
  measurable_fun setT (@varof l i li).
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

Definition same_kernel d1 d2 d3 (A : measurableType d1)
  (A' : measurableType d2) (B : measurableType d3) (k : R.-sfker A ~> B) (k' : R.-sfker A' ~> B) : Prop.
  Abort.


Lemma false_index_size (x : string) (l : context') (H : x \in (map fst l)) :
	(seq.index x (map fst l) < size l)%nat.
Proof. by rewrite -(size_map fst) index_mem. Qed.

Definition get_dom_kernel d d' (X : measurableType d) (Y : measurableType d')
  (l : R.-sfker X ~> Y) := X.
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

Inductive mytype :=
| mybase : forall dT (T : measurableType dT), mytype
| myprod : forall dT (T : measurableType dT) (t : mytype), mytype.

Fixpoint mytype_eval (t : mytype) : seq {d & measurableType d} := 
  match t with mybase d T => [:: existT _ d T] | myprod d T T2 => existT _ d T :: mytype_eval T2 end.

Inductive evalD : forall (l : context') 
(* (G := prod_meas (map snd l)) *)
    dT (T : measurableType dT) (e : expD R) 
    (* (el : (freevarsD e <= size l)%nat) *)
    (f : projT2 (prod_meas (map snd l)) -> T), measurable_fun setT f -> Prop :=
| E_unit : forall l, 
  @evalD l _ munit exp_unit (cst tt) ktt

| E_bool : forall l b, 
  @evalD l _ mbool (exp_bool b) (cst b) (kb b)

| E_real : forall l (G := prod_meas (map snd l)) r, 
  @evalD l _ (mR R) (exp_real r) (cst r) (kr r)

| E_pair : forall l (G := prod_meas (map snd l)) dA dB A B e1 f1 mf1 e2 f2 mf2,
  @evalD l dA A e1 (f1 : projT2 G -> A) mf1 ->
  @evalD l dB B e2 (f2 : projT2 G -> B) mf2 ->
  @evalD l _ [the measurableType _ of (A * B)%type] (exp_pair e1 e2)
    (_ : projT2 G -> Datatypes_prod__canonical__measure_Measurable A B) (@measurable_fun_pair _ _ _ (projT2 G) A B f1 f2 mf1 mf2)

(* apply index_mem? *)
| E_var : forall l (G := prod_meas (map snd l)) d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (x : string) (H : x \in (map fst l)),
  let i := seq.index x (map fst l) in
  (* @evalD _ [the measurableType _ of (T1 * T2)%type] l _ _ (exp_var x) (proj1_sig (var_i_of2 i.+1)) (proj2_sig (var_i_of2 i.+1)) *)
  @evalD l _ _ (exp_var x) (@varof l i (false_index_size H))
  (@mvarof l i (false_index_size H))

| E_bernoulli : forall l (G := prod_meas (map snd l)) (r : {nonneg R}) (r1 : (r%:num <= 1)%R),
  @evalD l _ (pprobability mbool R) (exp_bernoulli r) (cst [the probability _ _ of bernoulli r1]) (measurable_fun_cst _)

| E_poisson : forall l k e f mf,
  @evalD l _ (mR R) e f mf ->
  @evalD l _ _ (exp_poisson k e) (poisson k \o f) 
  (measurable_fun_comp (mpoisson k) mf)

| E_norm : forall l e dT (T : measurableType dT) (k : R.-sfker _ ~> T),
  @evalP l _ T e k ->
  @evalD l _ (pprobability T R) (exp_norm e)
  (normalize k : _ -> pprobability _ _) 
  (measurable_fun_normalize k point)

with evalP : forall (l : context')
  dT (T : measurableType dT),
  expP R ->
  R.-sfker (projT2 (prod_meas (map snd l))) ~> T ->
  Prop :=
| E_sample : forall l (G := prod_meas (map snd l)) dT (T : measurableType dT) (e : expD R) (p : pprobability T R),
  @evalD l _ (pprobability T R) e (cst p) (measurable_fun_cst p) ->
  @evalP l _ T (exp_sample e) (sample p)

| E_ifP : forall l dT T e1 f1 mf e2 k2 e3 k3,
  @evalD l _ _ e1 f1 mf ->
  @evalP l dT T e2 k2 ->
  @evalP l dT T e3 k3 ->
  @evalP l dT T (exp_if e1 e2 e3) (ite mf k2 k3)

| E_score : forall l (G := prod_meas (map snd l)) e (f : projT2 G -> R)
(mf : measurable_fun _ f),
  @evalD l _ _ e f mf ->
  @evalP l _ munit (exp_score e) [the R.-sfker _ ~> _ of kscore mf]

| E_return : forall l dT T e (f : _ -> _) (mf : measurable_fun _ f),
  @evalD l _ _ e f mf ->
  @evalP l dT T (exp_return e) (ret mf)

| E_letin : forall l (G := prod_meas (map snd l)) dy (Y : measurableType dy)
dz (Z : measurableType dz) e1 e2
  (k1 : R.-sfker projT2 G ~> Y)
  (k2 : R.-sfker [the measurableType (dy, projT1 G).-prod of (Y * projT2 G)%type] ~> Z) 
  (x : string),
  @evalP l _ Y e1 k1 ->
  @evalP ((x, existT _ dy Y) :: l)%SEQ _ Z e2 k2 ->
  @evalP l _ Z (exp_letin x e1 e2) (letin' k1 k2)
.

(* Compute vars (exp_letin "x" (exp_var "x") (exp_var "x")). *)

(* Compute vars (exp_letin "x" (exp_var "y") (exp_letin "z" (exp_var "x") (exp_var "z"))). *)

(* Compute vars (exp_letin "x" (exp_return (exp_var "z")) (exp_letin "y" (exp_return (exp_real 2)) (exp_return (exp_pair (exp_var "x") (exp_var  "y"))))). *)

End eval.

Scheme evalD_mut_ind := Induction for evalD Sort Prop
with evalP_mut_ind := Induction for evalP Sort Prop.

Scheme expD_mut_ind := Induction for expD Sort Prop
with expP_mut_ind := Induction for expP Sort Prop.

Section example.
Variables (d : _) (G : measurableType d) (R : realType).

Example ex_real : @evalD R [::] _ _ (exp_real 3%:R) (@cst _ R 3%:R) (kr 3%:R).
Proof. apply/E_real. Qed.

Example ex_bool : @evalD R [::] _ _ (exp_bool true) (cst true)
(@measurable_fun_cst _ _ _ mbool setT _).
Proof. apply/E_bool. Qed.

Example ex_pair : @evalD R [::] _ _ (exp_pair (exp_real 1) (exp_real 2)) _
(@measurable_fun_pair _ _ _ _ _ _ (@cst _ R 1%R) (@cst _ R 2) (kr 1) (kr 2)).
Proof.
apply/E_pair /E_real /E_real.
Qed.

Example ex_ifP : @evalP R [::] _ (mR R)
  (exp_if (exp_bool true) (exp_return (exp_real 3%:R)) (exp_return (exp_real 10%:R)))
  (ite (@measurable_fun_cst _ _ _ mbool setT true) (ret k3) (ret k10)).
Proof. apply/E_ifP /E_return /E_real /E_return /E_real /E_bool. Qed.

Example ex_iteT : @ite _ _ _ (mR R) R _
(@measurable_fun_cst _ _ _ mbool setT true) (ret k3) (ret k10) tt = ret k3 tt.
Proof. by rewrite iteE. Qed.

Example ex_iteF : @ite _ _ _ (mR R) R _
(@measurable_fun_cst _ _ _ mbool setT false) (ret k3) (ret k10) tt =
ret k10 tt.
Proof. by rewrite iteE. Qed.

Local Open Scope ring_scope.

Example sample1 :
  @evalP R [::] _ _
    (exp_sample (exp_bernoulli (2 / 7%:R)%:nng))
    (sample [the probability _ _ of bernoulli p27]).
Proof.
exact/E_sample/E_bernoulli.
Qed.

Example sampler (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
  @evalP R [::] _ _
    (exp_sample (exp_bernoulli r))
    (sample [the probability _ _ of bernoulli r1]).
Proof. exact/E_sample/E_bernoulli. Qed.

Example score1 :
  @evalP R [::] _ _ (exp_score (exp_real 1)) (score (kr 1)).
Proof. apply/E_score /E_real. Qed.

Example score2 :
  @evalP R [::] _ _
    (exp_score (exp_poisson 4 (exp_real 3%:R)))
    (score (measurable_fun_comp (mpoisson 4) (kr 3%:R))).
Proof. apply/E_score /E_poisson /E_real. Qed.

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

Local Definition context1 := ("x", existT _ _ mbool) :: [::].
Local Definition context2 := ("r", existT _ _ (mR R)) :: context1.
Local Definition context3 := ("_", existT _ _ munit) :: context2.

Example ex_var :
  @evalP R [::] _ _ (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng)) (exp_return (exp_var "x"))) (letin' sample_bern (ret var1of2)).
Proof. 
apply/E_letin.
apply/E_sample.
apply/E_bernoulli.
apply/E_return.
have -> : (var1of2 = (@mvarof R [:: ("x", existT _ _ mbool)] 0 (false_index_size (_ : ("x" \in map fst context1))))) by done.
exact: (@E_var R [:: ("x", existT _ _ mbool)] _ _ _ _ "x").
Qed.

(* to be failed *)
Example ex_var_fail :
  @evalP R [::] _ _
    (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng))
      (exp_letin "r" (exp_if (exp_var "x") (exp_return (exp_real 3%:R)) (exp_return (exp_real 10%:R)))
        (exp_letin "y" (exp_score (exp_poisson 4 (exp_var "r")))
          (exp_return (exp_var "y")))))
    (kstaton_bus' _ (mpoisson 4)).
Proof.
rewrite /kstaton_bus'.
(* apply/E_letin /E_letin /E_letin => /=.
apply/E_sample /E_bernoulli. admit.
apply/E_ifP /E_return. admit. admit. *)
Admitted.

Example eval5 :
  @evalP R [::] _ _
    (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng))
      (exp_letin "r" (exp_if (exp_var "x") (exp_return (exp_real 3%:R)) (exp_return (exp_real 10%:R)))
        (exp_letin "_" (exp_score (exp_poisson 4 (exp_var "r")))
          (exp_return (exp_var "x")))))
    kstaton_bus''.
Proof.
apply/E_letin /E_letin /E_letin => /=.
apply/E_sample /E_bernoulli.
rewrite /prod_meas_obligation_2 //=.
apply/E_ifP /E_return.
have -> : (var1of4' = (@mvarof R context1 0 (false_index_size (_ : "x" \in map fst context1)))) by done.
exact: (@E_var R  [:: ("x", existT _ _ mbool)] _ _ _ _ "x").
apply/E_return.
apply/E_real.
apply/E_real.
apply/E_score.
apply/E_poisson.
have -> : (var1of4' = (@mvarof R context2 0 (false_index_size (_ : "r" \in map fst context2)))) by done.
exact: (@E_var R context2 _ _ _ _ "r").
apply/E_return.
have -> : (var3of4' = (@mvarof R context3 2 (false_index_size (_ : "x" \in map fst context3)))) by done.
exact: (@E_var R context3 _ _ _ _ "x").
Qed.

Example eval6 :
  @evalD R [::] _ _
    (exp_norm
      (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng))
        (exp_letin "r"
          (exp_if (exp_var "x") (exp_return (exp_real 3%:R))
                                (exp_return (exp_real 10%:R)))
          (exp_letin "_" (exp_score (exp_poisson 4 (exp_var "r")))
            (exp_return (exp_var "x"))))))
    _ (measurable_fun_normalize (R := R) kstaton_bus'' point).
    (* (@normalize _ _ munit mbool R (kstaton_bus' _ (mpoisson 4)) P). *)
Proof. apply/E_norm /eval5. Qed.

Example eval7 :
  @evalD R [::] _ _
    (exp_norm (exp_sample (exp_bernoulli (2 / 7%:R)%:nng)))
    _
    (* (@normalize _ _ _ _ R (sample _ (measurable_fun_cst (bernoulli p27 : pprobability _ _)))) *)
    (measurable_fun_normalize (R := R) (sample [the probability _ _ of bernoulli p27]) point).
Proof. apply/E_norm /E_sample /E_bernoulli. Qed.

(* Example eval7_2 :
  @evalD R [::] _ _
    (exp_norm (exp_sample (exp_norm (exp_sample (exp_bernoulli (2 / 7%:R)%:nng)))))
    _
    (* (@normalize _ _ _ _ R
      (sample _ (measurable_fun_normalize (sample _ (@mbernoulli_density_function R _ _ (2 / 7%:R))) P)) P : _ -> pprobability _ _) *)
    (measurable_fun_normalize 
      (sample (measurable_fun_normalize (R := R) (sample [the probability _ _ of bernoulli p27]) point)) point).
Proof.
apply/E_norm /E_sample.
apply/E_norm /E_sample /E_bernoulli.
Qed. *)

Example exp_staton_bus' : expD R :=
  (exp_norm
    (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng))
      (exp_letin "r"
        (exp_letin "_"
          (exp_if (exp_var "x") (exp_return (exp_real 3))
                                (exp_return (exp_real 10)))
          (exp_score (exp_poisson 4 (exp_var "r"))))
        (exp_return (exp_var "x"))))).

Example exp_staton_bus : expD R :=
  (exp_norm
    (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng))
      (exp_letin "r"
        (exp_if (exp_var "x") (exp_return (exp_real 3))
                              (exp_return (exp_real 10)))
        (exp_letin "_" (exp_score (exp_poisson 4 (exp_var "r")))
          (exp_return (exp_var "x")))))).

(* Lemma eq_statonbus (t u : expP) v1 v2 mv1 mv2 :
  @evalD _ munit [::] _ (pprobability _ _) exp_staton_bus v1 mv1 ->
  @evalD _ munit [::] _ _ exp_staton_bus' v2 mv2 ->
  v1 = v2.
Proof.
have -> : v1 = staton_bus (mpoisson 4) (bernoulli p27).
admit.
have -> : v2 = staton_bus' (mpoisson 4) (bernoulli p27) tt.
admit.
move=> h1 h2.
by rewrite staton_busE staton_busE'.
Admitted.
*)

End example.

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

Section eval_prop.

Variable (R : realType).
Fixpoint execD_type (e : expD R) : {d & measurableType d} :=
  match e with
  | exp_real r => existT _ _ (mR R)
  | exp_bool b => existT _ _ mbool
  | exp_unit => existT _ _ munit
  (* | exp_pair e1 e2 => existT _ _ [the measurableType _ of (projT2 (execD_type e1) * projT2 (execD_type e2))%type] *)
  | _ => existT _ _ munit
  end.

Fixpoint execD (e : expD R) : {f : munit -> projT2 (execD_type e) & measurable_fun _ f} :=
  match e return {f : munit -> projT2 (execD_type e) & measurable_fun _ f} with
  (* | exp_var v => fun=> @measurable_fun_id _ _ _ *)
  | exp_real r => existT _ (cst r) (kr r)
  | exp_bool b => existT _ (cst b) (kb b)
  | exp_unit => existT _ (cst tt) ktt
  | _ => existT _ (cst tt) ktt
  end.

  (* | exp_var v => @measurable_fun _ _ [the measurableType _ of (A * B)%type] A setT (@fst A B)
  | exp_real r => measurable_fun setT (@cst (mR R) _ r)
  | exp_bool b => measurable_fun setT (@cst mbool _ b)
  | exp_unit => measurable_fun setT (@cst munit _ tt)
  | exp_pair e1 e2 => execD e1
  | exp_bernoulli r => forall (r1 : (r%:num <= 1)%R), measurable_fun setT (@cst (mR R) _ r%:num)
  (* | exp_poisson k e => execD e *)
  | _ => measurable_fun setT (@cst munit _ tt) *)
  (* end. *)

Check execD.

(* Fixpoint execP_type (e : expP R) : Type :=
  match e with
  | exp_if e1 e2 e3 => execP_type e2
  | exp_sample _ => R.-sfker A ~> mbool
  | exp_return e1 => R.-sfker A ~> mR R
  | _ => R.-sfker A ~> B
  end. *)

(* Fixpoint execP (e : expP) : execP_type e :=
  match e with
  | exp_if e1 e2 e3 => ite _ (execP e2) (execP e3)
  | exp_sample e => sample (bernoulli p27)
  | exp_return e => ret (kr 1)
  end. *)


Require Import Coq.Program.Equality.

Ltac inj H := apply Classical_Prop.EqdepTheory.inj_pair2 in H.

Lemma pair_equal_spec :
  forall (A B : Type) (a1 a2 : A) (b1 b2 : B),
    (a1, b1) = (a2, b2) <-> a1 = a2 /\ b1 = b2.
Proof.
intros. split; intro H; inversion H; subst; eauto.
Abort.

Lemma mdisp_pair_equal_spec (dA dB dA' dB' : measure_display) :
  (dA, dB).-prod%mdisp = (dA', dB').-prod%mdisp <-> dA = dA' /\ dB = dB'.
Proof.
split; intro H; inversion H; subst; eauto.
Qed.

Lemma prod_equal_spec (A B A' B' : Type) :
  (A * B)%type = (A' * B')%type <-> A = A' /\ B = B'.
Proof.
Admitted.


Lemma evalD_unit (l : context') (G1 : projT2 (prod_meas (map snd l)) -> munit) (mv : measurable_fun (T:=projT2 (prod_meas [seq i.2 | i <- l])) (U:=munit) [set: projT2 (prod_meas [seq i.2 | i <- l])] G1) : 
  @evalD R l _ munit exp_unit _ mv -> cst tt = G1.
Proof.
inversion 1.
inj H1.
inj H1.
inj H1.
done.
Qed.

Lemma prodType_Datatypes dA dB (A A0 : measurableType dA) (B B0 : measurableType dB) : (A * B)%type = (A0 * B0)%type -> Datatypes_prod__canonical__measure_Measurable A B = Datatypes_prod__canonical__measure_Measurable A0 B0.
Proof. move=> H. Admitted.

Lemma evalD_uniq (l : context') (G := prod_meas (map snd l)) dT (T : measurableType dT) (e : expD R) (u v : projT2 G -> T) (mu : measurable_fun _ u) (mv : measurable_fun _ v) :
  evalD e mu -> evalD e mv -> u = v.
Proof.
move=> hu.
apply: (@evalD_mut_ind R
  (fun (l : _) (G := prod_meas (map snd l)) dT (T : measurableType dT) (e : expD R) (f : projT2 G -> T) (mf : measurable_fun setT f) (h1 : evalD e mf) =>
    forall (v : projT2 G -> T) (mv : measurable_fun setT v), evalD e mv -> f = v)
  (fun (l : _) (G := prod_meas (map snd l)) dT (T : measurableType dT) (e : expP R) (u : R.-sfker projT2 G ~> T) (h1 : evalP e u) =>
    forall (v : R.-sfker projT2 G ~> T), evalP e v -> u = v)
  _ _ _ _ _ _ _ _ _ _ _ _ _ l dT T e); last exact: hu.
- 
move=> l' G0 {}mv.
inversion 1.
by do 3 inj H2.
-
move=> l' x G0 {}mv.
inversion 1.
by do 3 inj H2.
-
move=> l' r G0 {}mv.
inversion 1.
by do 3 inj H2.
- (* pair *)
move=> l' G0 dA dB A B e1 f1 mf1 e2 f2 mf2 ev1 IH1 ev2 IH2 f {}mv H.
inversion H.
subst.
have Hd : dA0 = dA /\ dB0 = dB.
by apply/mdisp_pair_equal_spec /H0.
destruct Hd as [HA HB].
subst.
have PP0 : (Datatypes_prod__canonical__measure_Measurable A B = Datatypes_prod__canonical__measure_Measurable A0 B0).
exact: prodType_Datatypes.
(* using H3? *)
have ? : (A = A0) by admit.
subst.
have ? : (B = B0) by admit.
subst.
do 3 inj H26.
inj H6.
subst.
have -> : (f1 = f0) by apply: IH1.
by have -> : (f2 = f3) by apply: IH2.

(* simple inversion 1 => // ev.
subst.
inj H7. *)

- (* var *)
move=> l' G0 d1 d2 T1 T2 x H i H0 {}mv.
inversion 1.
subst.
do 3 inj H10.
by have -> : (H = H2) by exact: Prop_irrelevance.
- (* bernoulli *)
move=> l' G0 r r1 H0 {}mv.
inversion 1.
do 3 inj H5.
by have -> : (r1 = r2) by exact: Prop_irrelevance.
- (* poisson *)
move=> l' k e0 f mf e1 IH0 G0 {}mv.
inversion 1.
do 3 inj H3.
clear H4.
by have -> : (f = f1) by exact: IH0.
- (* norm *)
move=> l0 e0 dT0 T0 k e1 IH0 f {}mv.
simple inversion 1 => // ev.
subst.
injection H4 => ?.
subst e2.
(* do 1 inj H5.
do 1 inj H6. *)
(* Search existT. *)
(* apply EqdepFacts.eq_sigT_fst in H6. *)
(* rewrite H2 in H6. *)
have Hd : (dT0 = dT1) by admit.
subst.
have HT : (T0 = T1) by admit.
subst.
do 3 inj H5.
by have -> : (k = k0) by apply: IH0.
- (* sample *)
move=> l0 G0 dT0 T0 e0 p e1 IH0 k H.
simple inversion H => // _ ev.
subst.
inj H3.
subst.
do 3 inj H5.
subst.
have pp0 : (p = p0).
have := IH0 (cst p0) (measurable_fun_cst p0).
injection H4 => <-.
move=>/(_ ev) cstp.
by rewrite (inj_cst cstp).
by subst.
Admitted.

Lemma eval_uniqP (l : context') (G := prod_meas (map snd l)) dT (T : measurableType dT) (e : expP R) (u v : R.-sfker projT2 G ~> T) :
  evalP e u -> evalP e v -> u = v.
Proof.
move=> hu.
apply: (@evalP_mut_ind R
  (fun (l : _) (G := prod_meas (map snd l)) dT (T : measurableType dT) (e : expD R) (f : projT2 G -> T) (mf : measurable_fun setT f) (h1 : evalD e mf) =>
    forall (v : projT2 G -> T) (mv : measurable_fun setT v), evalD e mv -> f = v)
  (fun (l : _) (G := prod_meas (map snd l)) dT (T : measurableType dT) (e : expP R) (u : R.-sfker projT2 G ~> T) (h1 : evalP e u) =>
    forall (v : R.-sfker projT2 G ~> T), evalP e v -> u = v)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ dT T e); last exact: hu.
admit. admit. admit. admit. admit. admit. admit. admit.
- (* sample *)
move=> l0 G0 dT0 T0 e0 p e1 IH0 k H.
simple inversion H => // _ ev.
subst.
inj H3.
subst.
do 3 inj H5.
subst.
have pp0 : (p = p0).
have := IH0 (cst p0) (measurable_fun_cst p0).
injection H4 => <-.
move=>/(_ ev) cstp.
by rewrite (inj_cst cstp).
by subst.
- (* if *)
move=> l0 dT0 T0 e1 f1 mf e2 k2 e3 k3 ev1 IH0 ev2 IH1 ev3 IH2 k.
inversion 1.
inj H0; subst.
do 3 inj H8.
have f12 : (f1 = f2) by exact: IH0.
subst.
have -> : (mf0 = mf) by exact: Prop_irrelevance.
have -> : (k2 = k0) by exact: IH1.
by have -> : (k3 = k1) by exact: IH2.
move=> l0 G0 e0 f mf e1 IH0 k.
inversion 1.
subst.
do 3 inj H3.
have ff0 : (f = f0) by exact: IH0.
subst.
by have -> : (mf1 = mf) by exact: Prop_irrelevance.
move=> l0 dT0 T0 e0 f mf e1 IH0 k.
simple inversion 1 => // ev.
subst.
inj H3.
subst.
do 3 inj H5.
have ff0 : (f = f0).
have := IH0 _ mf0.
injection H4 => <-.
by move=>/(_ ev).
subst.
by have -> : (mf0 = mf) by exact: Prop_irrelevance.
move=> l0 G0 dY Y dZ Z e1 e2 k1 k2 x e0 IH0 ev1 IH1 k.
simple inversion 1 => // ev2 ev3.
subst.
inj H4.
subst.
do 3 inj H6.
subst.
injection H5 => ? ? ?.
subst x0 e3 e4.
have dyY : (dy = dY) by admit.
subst.
have YY0 : (Y = Y0) by admit.
subst.
have k01 : (k1 = k0).
by apply: IH0.
subst.
by have <- : (k2 = k3) by apply: IH1.
Admitted.

Axiom largest_var_in_expP : forall e : expP R, nat.
(* return the larget var in e *)

Lemma eval_full dA (A : measurableType dA) l s :
  prod_meas s = existT _ _ A ->
  forall e, (largest_var_in_expP e <= size s)%nat ->
    exists dB (B : measurableType dB) v, @evalP R l dB B e v.
Proof.
move=> HA e Hs.
(* apply: (@expP_mut_ind R
  (fun (e : expD R) =>
    exists dB (B : measurableType dB) (v : A -> B) (mv : measurable_fun setT v), evalD l e mv)
  (fun (e : expP R) =>
    exists dB B (v : R.-sfker A ~> B), evalP l e v)
  _ _ _ _ _ _ _ _ _ _ _ _ _).
-
  move=> x.
  eexists.
  eexists.
  have s1 : (1 < size s)%nat.
  admit.
  destruct s.
  done.
  simpl in HA.
  inj HA.
  (* exists [the measurableType _ of (munit * munit)%type].
  exists (proj1_sig (var_i_of2 0.+1)).
  exists (proj2_sig (var_i_of2 0.+1)).
  exact: E_var. *)
- 
  do 1 eexists.
  exists munit.
  exists (cst tt).
  exists ktt.
  exact: E_unit.
-
  move=> b.
  do 1 eexists.
  exists mbool.
  exists (cst b).
  exists (kb b).
  exact: E_bool.
-
  move=> r.
  do 1 eexists.
  exists (mR R).
  exists (cst r).
  exists (kr r).
  exact: E_real.
-
  move=> e1 ih1 e2 ih2.
  destruct ih1 as (dB1 & B1 & v1 & mv1 & ih1).
  destruct ih2 as (dB2 & B2 & v2 & mv2 & ih2).
  eexists.
  exists [the measurableType _ of (B1 * B2)%type].
  eexists.
  exists (@measurable_fun_pair _ _ _ _ _ _ _ _ mv1 mv2).
  by apply/E_pair.
-
  move=> r.
  (* have r1 : (r%:num <= 1)%R. *)
  admit.
  (* do 3 eexists.
  exists (measurable_fun_cst (bernoulli r1 : pprobability _ _)).
  exact: E_bernoulli. *)
-
  (* move=> n e0 ih.
  do 1 eexists.
  exists (mR R).
  eexists. *)
  (* exists (measurable_fun_comp (mpoisson n)).
  exact: E_poisson. *)
  admit.
-
  move=> e0 ih1.
  do 3 eexists.
  (* exists (measurable_fun_normalize _ (bernoulli p27)).
  exact: E_norm. *)
  admit.
-
  (* move=> e1 ih1 e2 ih2 e3 ih3.
  apply ex_intro in ih1.
  (* destruct ih1 as (dA1 & A1 & dB1 & B1 & f1 & mf1 & ih1). *)
  do 2 eexists. *)
  (* exists (ite mf1). *)
-
- *)
Admitted.

Definition execP (dA dB : measure_display) (A : measurableType dA) (B : measurableType dB) :
  expP R -> R.-sfker A ~> B.
Proof.
move=> e.
(* have /cid h := eval_full A B e. *)
(* exact: (proj1_sig h). *)
(* Defined. *)
Admitted.

End eval_prop.

Section letinC.
Variables (dG : _) (G : measurableType dG) (dT : _) (T : measurableType dT)
  (dU : _) (U : measurableType dU) (R : realType).

Lemma tt' t (t' : R.-sfker [the measurableType _ of (U * munit)%type] ~> T) : forall x, t =1 fun z => t' (x, z).
Admitted.

Lemma uu' u (u' : R.-sfker [the measurableType _ of (T * munit)%type] ~> U) : forall y, u =1 fun z => u' (y, z).
Admitted.

Lemma __ : @evalD R
  [:: ("y", existT _ _ U);
          ("x", existT _ _ T)] _ _
  (exp_var "y") fst var1of2.
Proof.
have -> : (var1of4' = (@mvarof R [:: ("y", existT _ _ U); ("x", existT _ _ T)] 0 (false_index_size (_ : ("y" \in map fst [:: ("y", existT _ _ U); ("x", existT _ _ T)]))))) by done.
exact: (@E_var R [:: ("y", existT _ _ U); ("x", existT _ _ T)] _ _ _ _ "y").
Qed.


Lemma letinC' (t u : expP R) (v1 v2 : R.-sfker _ ~> _) z A :
  let x := "x" in let y := "y" in
  measurable A ->
  @evalP R [::] _ [the measurableType _ of (U * T)%type]
  (exp_letin x t (exp_letin y u
    (exp_return (exp_pair (exp_var x) (exp_var y))))) v1 ->
  @evalP R [::] _ [the measurableType _ of _]
  (exp_letin y u (exp_letin x t
    (exp_return (exp_pair (exp_var x) (exp_var y))))) v2 ->
  v1 z A = v2 z A.
Proof.
move=> x y mA.
pose vt : R.-sfker munit ~> T := execP munit T t.
pose vu : R.-sfker [the measurableType _ of (T * munit)%type] ~> U := execP _ _ u.
move=> evalv1 evalv2.
have -> : v2 = (letin' vt (letin' vu (ret (measurable_fun_pair var1of3' var2of3')))).
apply: (eval_uniqP evalv2).
apply /E_letin /E_letin.
admit. admit.
apply /E_return /E_pair.
have -> : (var1of4' = (@mvarof R [:: (x, existT _ _ U); (y, existT _ _ T)] 0 (false_index_size (_ : (x \in map fst [:: (x, existT _ _ U); (y, existT _ _ T)]))))) by done.
apply: (@E_var R [:: (x, existT _ _ U); (y, existT _ _ T)] _ _ _ _ x) => //.
have -> : (var2of4' = (@mvarof R [:: (x, existT _ _ U); (y, existT _ _ T)] 1 (false_index_size (_ : (y \in map fst [:: (x, existT _ _ U); (y, existT _ _ T)]))))) by done.
apply: (@E_var R [:: (x, existT _ _ U); (y, existT _ _ T)] _ _ _ _ y) => //.
pose vt' : R.-sfker [the measurableType _ of (U * munit)%type] ~> T := execP _ _ t.
pose vu' : R.-sfker munit ~> U := execP _ _ u.
have -> : v1 = (letin' vu' (letin' vt' (ret (measurable_fun_pair var2of3' var1of3')))).
apply: (eval_uniqP evalv1).
apply/E_letin /E_letin.
admit. admit.
apply/E_return /E_pair.
have -> : (var2of4' = (@mvarof R [:: (y, existT _ _ T); (x, existT _ _ U)] 1 (false_index_size (_ : (x \in map fst [:: (y, existT _ _ T); (x, existT _ _ U)]))))) by done.
apply: (@E_var R [:: (y, existT _ _ T); (x, existT _ _ U)] _ _ _ _ x) => //.
have -> : (var1of4' = (@mvarof R [:: (y, existT _ _ T); (x, existT _ _ U)] 0 (false_index_size (_ : (y \in map fst [:: (y, existT _ _ T); (x, existT _ _ U)]))))) by done.
apply: (@E_var R [:: (y, existT _ _ T); (x, existT _ _ U)] _ _ _ _ y) => //.
rewrite !letin'E.
under eq_integral.
  move=> x0 _.
  rewrite letin'E /=.
  rewrite -(tt' vt).
  (* under eq_integral do rewrite retE /=. *)
  over.
rewrite (sfinite_fubini _ _ (fun x => \d_(x.1, x.2) A))//; last 3 first.
exact: sfinite_kernel_measure.
exact: sfinite_kernel_measure.
apply/EFin_measurable_fun => /=.
rewrite (_ : (fun x => _) = @mindic _ [the measurableType _ of (U * T)%type] R _ mA).
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
