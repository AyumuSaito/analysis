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

Section type_syntax.
Variables (R : realType).

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
End type_syntax.

Arguments typei {R}.

Section context.
Definition context := seq (string * types)%type.
End context.

(* 
TODO: expD : type -> Type := ...
*)

Section expr.
(* Variables (R : realType). *)
Inductive expD : Type :=
| exp_var  : string -> expD
| exp_unit : expD
| exp_bool : bool -> expD
| exp_real {R: realType} : R -> expD
| exp_pair : expD -> expD -> expD
(* | exp_plus : expD -> expD -> expD *)
(* | val_unif : val *)
| exp_bernoulli {R : realType} : {nonneg R} -> expD
| exp_poisson : nat -> expD -> expD
| exp_norm : expP -> expD
(* | exp_if : forall z, expD -> exp z -> exp z -> exp z *)
with expP :=
| exp_if : expD -> expP -> expP -> expP
| exp_letin : string -> expP -> expP -> expP
| exp_sample : expD -> expP
| exp_score : expD -> expP
| exp_return : expD -> expP.

End expr.

(* Arguments expD {R}.
Arguments expP {R}. *)

(* Arguments exp_var {R}. *)
(* Arguments exp_unit {R}. *)
(* Arguments exp_bool {R}. *)
(* Arguments exp_real {R}. *)
(* Arguments exp_pair {R}. *)
(* Arguments exp_bernoulli {R}. *)
(* Arguments exp_poisson {R}. *)
(* Arguments exp_norm {R}. *)
(* Arguments exp_if {R}. *)
(* Arguments exp_letin {R}. *)
(* Arguments exp_sample {R}. *)
(* Arguments exp_score {R}. *)
(* Arguments exp_return {R}. *)

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

Lemma false_index_size2 (x : string) (l : context) (H : x \in (map fst l)) :
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

(* add : exp Int -> exp Int -> exp Int *)
Inductive evalD : forall (l : context) 
(* (G := prod_meas (map snd l)) *)
    (T : types) (e : expD) 
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

| E_var : forall (l : context) (T : types) (x : string) (H : x \in (map fst l)),
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

with evalP : forall (l : context) (T : types),
  expP ->
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


Fixpoint evalD

End eval.
Section test.
Variables (R : realType).
Goal ret (R := R) (@measurable_fun_id _ mbool _) true [set: bool] = 1.
Proof.
by rewrite retE diracE in_setT.
Qed.

End test.

Section ttype.
Variables (R : realType).
Inductive ttype : Type := D | P.

Definition ttype_denote (t : ttype) :=
  match t with
  | D => forall dA dB (A : measurableType dA) (B : measurableType dB), {f : A -> B | measurable_fun setT f}
  | P => forall dA dB (A : measurableType dA) (B : measurableType dB), R.-sfker A ~> B
  end.

End ttype.

Section type.
Inductive type : Type :=
| Real | Bool | Unit
.

Definition type_eqb (t t' : type) : bool :=
match t, t' with
| _, _ => true
end.

Definition type_eqb_dec (t t' : type) : {is_true (type_eqb t t')} + {~ is_true (type_eqb t t')}.
destruct (type_eqb t t').
by left. 
by right.
Defined.

(* Variables (R : realType). *)
Fixpoint type_denote {R : realType} (t : type) : Type :=
  match t with
  | Real => R
  | Bool => bool
  | Unit => unit
  end.

End type.

Section expr.
Variables (R : realType).
Variables var : type -> Type.

Inductive expr : type -> Type :=
| Num : R -> expr Real
| Bol : bool -> expr Bool
| TT : expr Unit
| Var : forall t, var t -> expr t
.

Inductive exprP : type -> Type :=
| Ret : forall t t1, expr t -> expr t1
.

End expr.

Section expr_denote.
Variable (R : realType).

Fixpoint expr_denote (t : type) (e : expr R type_denote t) : type_denote t :=
  match e in (expr _ _ t) return (type_denote t) with
  | Num r => r
  | Bol b => b
  | TT => tt
  | Var _ x => x
  | Ret _ _ t => expr_denote t
  end.

End expr_denote.

