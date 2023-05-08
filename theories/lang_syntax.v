From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp.classical Require Import mathcomp_extra boolp classical_sets.
From mathcomp.classical Require Import functions cardinality fsbigop.
Require Import signed reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure numfun lebesgue_integral kernel prob_lang.

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

Declare Scope lang_scope.

Reserved Notation "l # e -D-> v ; mv" (at level 40).
Reserved Notation "l # e -P-> v" (at level 40).

Section type_syntax.
Variables (R : realType).

Section string_eq.

Definition string_eqMixin := @EqMixin string eqb eqb_spec.
Canonical string_eqType := EqType string string_eqMixin.

End string_eq.

Fixpoint prod_meas (l : list {d & measurableType d})
    : {d & measurableType d} :=
  match l with
  | [::] => existT measurableType _ munit
  | h :: t => let t' := prod_meas t in
    existT _ _ [the measurableType (projT1 h, projT1 t').-prod of (projT2 h * projT2 t')%type]
  end.

Inductive stype :=
| sunit : stype
| sbool : stype
| sreal : stype
| spair : stype -> stype -> stype
| sprob : stype -> stype
| slist : list stype -> stype.

Canonical stype_eqType := Equality.Pack (@gen_eqMixin stype).

Fixpoint typei (t : stype) : {d & measurableType d} :=
  match t with
  | sunit => existT _ _ munit
  | sbool => existT _ _ mbool
  | sreal => existT _ _ (mR R)
  | spair A B => existT _ _
      [the measurableType (projT1 (typei A), projT1 (typei B)).-prod%mdisp of
      (projT2 (typei A) * projT2 (typei B))%type]
  | sprob A => existT _ _ (pprobability (projT2 (typei A)) R)
  | slist l => prod_meas (map typei l)
  end.

Definition typei2 t := projT2 (typei t).

End type_syntax.

Arguments typei {R}.
Arguments typei2 {R}.

Definition context := seq (string * stype)%type.

Section expr.
Variables (R : realType).

Inductive expD : context -> stype -> Type :=
| expWD l st x (e : expD l st) : x.1 \notin map fst l -> expD (x :: l) st
| exp_unit l : expD l sunit
| exp_bool l : bool -> expD l sbool
| exp_real l : R -> expD l sreal
| exp_pair l t1 t2 : expD l t1 -> expD l t2 -> expD l (spair t1 t2)
| exp_var (l : context) x t : (* x \in map fst l -> *)
  t = nth sunit (map snd l) (seq.index x (map fst l)) ->
  expD l t
| exp_bernoulli l (r : {nonneg R}) (r1 : (r%:num <= 1)%R) : expD l (sprob sbool)
| exp_poisson l : nat -> expD l sreal -> expD l sreal
| exp_norm l t : expP l t -> expD l (sprob t)
with expP : context -> stype -> Type :=
| expWP l st x (e : expP l st) : x.1 \notin map fst l -> expP (x :: l) st
(* | expWPL l st xs (e : expP l st) : subseq (map fst xs) (map fst l) -> expP (xs ++ l) st *)
| exp_if l t : expD l sbool -> expP l t -> expP l t -> expP l t
| exp_letin l t1 t2 (x : string) :
  expP l t1 -> expP ((x, t1) :: l) t2 -> expP l t2
(* | exp_sample : forall t l, expD (sprob t) l -> expP t l *)
| exp_sample_bern l (r : {nonneg R}) (r1 : (r%:num <= 1)%R) : expP l sbool
| exp_score l : expD l sreal -> expP l sunit
| exp_return l t : expD l t -> expP l t.

End expr.

Arguments expD {R}.
Arguments expP {R}.
Arguments expWD {R l st x}.
Arguments exp_unit {R l}.
Arguments exp_bool {R l}.
Arguments exp_real {R l}.
Arguments exp_pair {R l _ _}.
Arguments exp_var {R _}.
Arguments exp_bernoulli {R l}.
Arguments exp_poisson {R l}.
Arguments exp_norm {R l _}.
Arguments expWP {R l st x}.
Arguments exp_if {R l t}.
Arguments exp_letin {R l _ _}.
Arguments exp_sample_bern {R} l r.
Arguments exp_score {R l}.
Arguments exp_return {R l _}.

Declare Custom Entry expr.
Notation "[ e ]" := e (e custom expr at level 5) : lang_scope.
Notation "x ':r'" := (@exp_real _ _ x%R) (in custom expr at level 1) 
  : lang_scope.
Notation "'Ret' x" := (@exp_return _ _ _ x) (in custom expr at level 2) 
  : lang_scope.
Notation "% x" := (@exp_var _ _ x _ erefl) (in custom expr at level 1) 
  : lang_scope.
Notation "%WP x # e" := (@expWP _ _ _ (x, _) e erefl)
  (in custom expr at level 1) : lang_scope.
Notation "( x , y )" := (exp_pair x y) (in custom expr at level 1) : lang_scope.
Notation "'Let' x '<~' e 'In' f" := (exp_letin x e f)
  (in custom expr at level 3,
   x constr,
   (* e custom expr at level 2, *)
   f custom expr at level 3,
   left associativity) : lang_scope.
(*Notation "( x )" := x (in custom expr, x at level 50).*)
Notation "'If' e1 'Then' e2 'Else' e3" := (exp_if e1 e2 e3) 
  (in custom expr at level 1) : lang_scope.
Notation "{ x }" := x (in custom expr, x constr) : lang_scope.
Notation "x" := x (in custom expr at level 0, x ident) : lang_scope.

Section varof.
Context {R : realType}.

Fixpoint varof (l : seq stype) (i : nat) :
  typei2 (slist l) -> @typei2 R (nth sunit l i) :=
  match l return (typei2 (slist l) -> typei2 (nth sunit l i)) with
  | [::] => match i with | O => id | j.+1 => id end
  | _ :: _ => match i with
               | O => fst
               | j.+1 => fun H => varof j H.2
               end
  end.

Lemma mvarof (l : seq stype) (i : nat) : measurable_fun setT (@varof l i).
Proof.
elim: l i => //= h t ih [|j]; first exact: measurable_fun_fst.
exact: (measurable_funT_comp (ih _) (@measurable_fun_snd _ _ _ _)).
Qed.
End varof.

Arguments varof {R} l i.
Arguments mvarof {R} l i.

Section eval.
Variables (R : realType).

Lemma eq_probability d (Y : measurableType d) (m1 m2 : probability Y R) :
  (m1 = m2 :> (set Y -> \bar R)) -> m1 = m2.
Proof.
move: m1 m2 => [m1 +] [m2 +] /= m1m2.
rewrite -{}m1m2 => -[[c11 c12] [m01] [sf1] [sig1] [fin1] [sub1] [p1]]
                    [[c21 c22] [m02] [sf2] [sig2] [fin2] [sub2] [p2]].
have ? : c11 = c21 by exact: Prop_irrelevance.
subst c21.
have ? : c12 = c22 by exact: Prop_irrelevance.
subst c22.
have ? : m01 = m02 by exact: Prop_irrelevance.
subst m02.
have ? : sf1 = sf2 by exact: Prop_irrelevance.
subst sf2.
have ? : sig1 = sig2 by exact: Prop_irrelevance.
subst sig2.
have ? : fin1 = fin2 by exact: Prop_irrelevance.
subst fin2.
have ? : sub1 = sub2 by exact: Prop_irrelevance.
subst sub2.
have ? : p1 = p2 by exact: Prop_irrelevance.
subst p2.
by f_equal.
Qed.

Section measurable_fun_normalize.
Context d d' (X : measurableType d) (Y : measurableType d').
Variable k : R.-sfker X ~> Y.

Lemma measurable_fun_normalize :
  measurable_fun setT (fun x => normalize k point x : pprobability Y R).
Proof.
apply: (@measurability _ _ _ _ _ _
  (@pset _ _ _ : set (set (pprobability Y R)))) => //.
move=> _ -[_ [r r01] [Ys mYs <-]] <-.
rewrite /normalize /mnormalize /mset /preimage/=.
apply: emeasurable_fun_infty_o => //.
rewrite /mnormalize/=.
rewrite (_ : (fun x => _) = (fun x => if (k x setT == 0) || (k x setT == +oo)
    then \d_point Ys else k x Ys * ((fine (k x setT))^-1)%:E)); last first.
  by apply/funext => x/=; case: ifPn.
apply: measurable_fun_if => //.
- apply: (measurable_fun_bool true) => //.
  rewrite (_ : _ @^-1` _ = [set t | k t setT == 0] `|`
                           [set t | k t setT == +oo]); last first.
    by apply/seteqP; split=> x /= /orP//.
  by apply: measurableU; exact: kernel_measurable_eq_cst.
- exact: measurable_fun_cst.
- apply/emeasurable_funM; first exact/measurable_funTS/measurable_kernel.
  apply/EFin_measurable_fun; rewrite setTI.
  apply: (@measurable_fun_comp _ _ _ _ _ _ [set r : R | r != 0%R]).
  + exact: open_measurable.
  + by move=> /= _ [x /norP[s0 soo]] <-; rewrite -eqe fineK ?ge0_fin_numE ?ltey.
  + apply: open_continuous_measurable_fun => //; apply/in_setP => x /= x0.
    exact: inv_continuous.
  + apply: measurable_funT_comp; last exact/measurable_funTS/measurable_kernel.
    exact: measurable_fun_fine.
Qed.

End measurable_fun_normalize.

Definition eta1 x (l : context) t
    (f : @typei2 R (slist (map snd l)) -> @typei2 R t) :
    typei2 (slist (map snd (x :: l))) -> @typei2 R t :=
  f \o snd.

Lemma meta1 x (l : context) t
    (f : @typei2 R (slist (map snd l)) -> @typei2 R t)
    (mf : measurable_fun setT f) :
  measurable_fun setT (@eta1 x l t f).
Proof. by apply/(measurable_funT_comp mf); exact: measurable_fun_snd. Qed.

Definition keta1 (x : string * stype) (l : context) t
    (k : R.-sfker (@typei2 R (slist (map snd l))) ~> @typei2 R t) :
    @typei2 R (slist (map snd (x :: l))) -> {measure set @typei2 R t -> \bar R}
  := k \o snd.

Section kernel_eta1.
Variables (x : string * stype) (l : context) (t : stype)
  (k : R.-sfker (@typei2 R (slist (map snd l))) ~> @typei2 R t).

Let mk U : measurable U -> measurable_fun setT ((@keta1 x l t k) ^~ U).
Proof.
move=> mU; rewrite (_ : (@keta1 x l t k) ^~ U = (k ^~ U) \o snd)//.
apply: measurable_funT_comp.
  exact: measurable_kernel.
exact: measurable_fun_snd.
Qed.

HB.instance Definition _ :=
  isKernel.Build _ _ _ _ _ (@keta1 x l t k) mk.
End kernel_eta1.

Section sfkernel.
Variables (x : string * stype) (l : context) (t : stype)
  (k : R.-sfker (@typei2 R (slist (map snd l))) ~> @typei2 R t).

Let sk : exists2 s : (R.-ker (@typei2 R (slist (map snd (x :: l)))) ~> @typei2 R t)^nat,
  forall n, measure_fam_uub (s n) &
  forall x0 U, measurable U -> (@keta1 x l t k) x0 U = kseries s x0 U .
Proof.
have [s hs] := sfinite k.
exists (fun n => [the _.-ker _ ~> _ of @keta1 x l t (s n)]).
  move=> n.
  have [M hM] := measure_uub (s n).
  exists M => x0.
  exact: hM.
move=> x0 U mU.
by rewrite /keta1/= hs.
Qed.

HB.instance Definition _ :=
  Kernel_isSFinite_subdef.Build _ _ _ _ _ (@keta1 x l t k) sk.

End sfkernel.

Section fkernel_eta1.
Variables (x : string * stype) (l : context) (t : stype)
  (k : R.-fker (@typei2 R (slist (map snd l))) ~> @typei2 R t).

Let uub : measure_fam_uub (@keta1 x l t k).
Proof.
have [M hM] := measure_uub k.
exists M => x0.
exact: hM.
Qed.

HB.instance Definition _ := @Kernel_isFinite.Build _ _ _ _ _
  (@keta1 x l t k) uub.
End fkernel_eta1.

Fixpoint free_varsD l t (e : @expD R l t) : seq string :=
  match e with
  | exp_var _ x (*_*) _ _             => [:: x]
  | exp_poisson _ _ e       => free_varsD e
  | exp_pair _ _ _ e1 e2    => free_varsD e1 ++ free_varsD e2
  | exp_unit _              => [::]
  | exp_bool _ _            => [::]
  | exp_real _ _            => [::]
  | exp_bernoulli _ _ _     => [::]
  | exp_norm _ _ e          => free_varsP e
  | expWD _ _ x e _ => rem x.1 (free_varsD e)
  end
with free_varsP T l (e : expP T l) : seq _ :=
  match e with
  | exp_if _ _ e1 e2 e3     => free_varsD e1 ++ free_varsP e2 ++ free_varsP e3
  | exp_letin _ _ _ x e1 e2 => free_varsP e1 ++ rem x (free_varsP e2)
  | exp_sample_bern _ _ _   => [::]
  | exp_score _ e           => free_varsD e
  | exp_return _ _ e        => free_varsD e
  | expWP _ _ x e _ => free_varsP e (*NB: why different from expWD case?*)
  end.

Inductive evalD : forall (l : context) (T : stype) (e : @expD R l T)
  (f : typei2 (slist (map snd l)) -> typei2 T),
  measurable_fun setT f -> Prop :=
| EV_unit l :
  l # exp_unit -D-> cst tt ; ktt

| EV_bool l b :
  l # exp_bool b -D-> cst b ; kb b

| EV_real l r :
  l # exp_real r -D-> cst r ; kr r

| EV_pair l t1 t2 (G := slist (map snd l)) e1 f1 mf1 e2 f2 mf2 :
  l # e1 -D-> f1 ; mf1 ->
  l # e2 -D-> f2 ; mf2 ->

  l # exp_pair e1 e2 -D-> fun x => (f1 x, f2 x) ;
  @measurable_fun_pair _ _ _ (typei2 G) (typei2 t1) (typei2 t2) f1 f2 mf1 mf2

| EV_var (l : context) (x : string) :
  let i := seq.index x (map fst l) in
  l # exp_var x _ erefl -D-> varof (map snd l) i ; mvarof (map snd l) i

| EV_bernoulli l (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
  l # exp_bernoulli r r1 -D->
  cst [the probability _ _ of bernoulli r1] ; measurable_fun_cst _

| EV_poisson l k e f mf :
  l # e -D-> f ; mf ->
  l # exp_poisson k e -D-> poisson k \o f ;
  measurable_funT_comp (mpoisson k) mf

| EV_norm l (t : stype) (e : expP l t) (k : R.-sfker _ ~> typei2 t) :
  l # e -P-> k ->
  l # exp_norm e -D-> (normalize k point : _ -> pprobability _ _) ;
  measurable_fun_normalize k

| EV_WeakD l (t : stype) (e : expD l t) x (xl : x.1 \notin map fst l) f mf :
  l # e -D-> f ; mf ->
  (x :: l) # expWD e xl -D-> (@eta1 x l t f) ; (@meta1 x l t f mf)

where "l # e -D-> v ; mv" := (@evalD l _ e v mv)

with evalP : forall (l : context) (T : stype),
  expP l T ->
  R.-sfker (typei2 (slist (map snd l))) ~> typei2 T -> Prop :=
| EV_sample l (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
  l # @exp_sample_bern R _ r r1 -P->
  sample [the probability _ _ of bernoulli r1]

| EV_ifP l T e1 f1 mf e2 k2 e3 k3 :
  l # e1 -D-> f1 ; mf ->
  l # e2 -P-> k2 ->
  l # e3 -P-> k3 ->
  l # exp_if e1 e2 e3 : expP l T -P-> ite mf k2 k3

| EV_score l (G := slist (map snd l)) e (f : typei2 G -> R)
  (mf : measurable_fun _ f) :
  l # e : expD l sreal -D-> f ; mf ->
  l # exp_score e -P-> [the R.-sfker _ ~> _ of kscore mf]

| EV_return l T e (f : _ -> _) (mf : measurable_fun _ f) :
  l # e -D-> f ; mf ->
  l # exp_return e : expP l T -P-> ret mf

| EV_letin (l : context) (G := slist (map snd l)) (t1 t2 : stype)
  (x : string) (e1 : expP l t1) (e2 : expP ((x, t1) :: l) t2)
  (k1 : R.-sfker (typei2 G) ~> typei2 t1)
  (k2 : R.-sfker (typei2 (spair t1 G)) ~> typei2 t2) :
  l # e1 -P-> k1 ->
  ((x, t1) :: l)%SEQ # e2 -P-> k2 ->
  l # exp_letin x e1 e2 -P-> letin' k1 k2

| EV_WeakP l (t : stype) (e : expP l t) x (xl : x.1 \notin map fst l) k :
  l # e -P-> k ->
  (x :: l) # expWP e xl -P-> [the R.-sfker _ ~> _ of @keta1 x l t k]
where "l # e -P-> v" := (@evalP l _ e v).

End eval.
Notation "l # e -D-> v ; mv" := (@evalD _ l _ e v mv) : lang_scope.
Notation "l # e -P-> v" := (@evalP _ l _ e v) : lang_scope.

Require Import Classical_Prop. (* NB: to compile with Coq 8.17 *)

Ltac inj_ex H := revert H;
  match goal with
  | |- existT ?P ?l (existT ?Q ?t (existT ?R ?u (existT ?T ?v ?v1))) =
       existT ?P ?l (existT ?Q ?t (existT ?R ?u (existT ?T ?v ?v2))) -> _ =>
    (intro H; do 4 apply Classical_Prop.EqdepTheory.inj_pair2 in H)
  | |- existT ?P ?l (existT ?Q ?t (existT ?R ?u ?v1)) =
       existT ?P ?l (existT ?Q ?t (existT ?R ?u ?v2)) -> _ =>
    (intro H; do 3 apply Classical_Prop.EqdepTheory.inj_pair2 in H)
  | |- existT ?P ?l (existT ?Q ?t ?v1) =
       existT ?P ?l (existT ?Q ?t ?v2) -> _ =>
    (intro H; do 2 apply Classical_Prop.EqdepTheory.inj_pair2 in H)
  | |- existT ?P ?l ?v1 =
       existT ?P ?l ?v2 -> _ =>
    (intro H; apply Classical_Prop.EqdepTheory.inj_pair2 in H)
end.

Scheme evalD_mut_ind := Induction for evalD Sort Prop
with evalP_mut_ind := Induction for evalP Sort Prop.

Scheme expD_mut_ind := Induction for expD Sort Prop
with expP_mut_ind := Induction for expP Sort Prop.

Section eval_prop.
Local Open Scope lang_scope.
Variables (R : realType).

Lemma evalD_uniq (l : context) (G := slist (map snd l)) t
  (e : @expD R l t) (u v : typei2 G -> typei2 t)
  (mu : measurable_fun setT u) (mv : measurable_fun setT v) :
  l # e -D-> u ; mu -> l # e -D-> v ; mv -> u = v.
Proof.
move=> hu.
apply: (@evalD_mut_ind R
  (fun l (G := slist (map snd l)) t (e : expD l t) (f : typei2 G -> typei2 t)
  (mf : measurable_fun setT f) (h1 : evalD e mf) =>
    forall (v : typei2 G -> typei2 t) (mv : measurable_fun setT v), evalD e mv -> f = v)
  (fun l (G := slist (map snd l)) t (e : expP l t)
    (u : R.-sfker typei2 G ~> typei2 t) (h1 : evalP e u) =>
    forall (v : R.-sfker typei2 G ~> typei2 t), evalP e v -> u = v)); last exact: hu.
all: (rewrite {l G t e u v mu mv hu}).
- move=> l {}v {}mv.
  inversion 1; subst l0.
  by inj_ex H3.
- move=> l b {}v {}mv.
  inversion 1; subst l0 b0.
  by inj_ex H3.
- move=> l r {}v {}mv.
  inversion 1; subst l0 r0.
  by inj_ex H3.
- move=> l t1 t2 G e1 f1 mf1 e2 f2 mf2 ev1 IH1 ev2 IH2 {}v {}mv.
  simple inversion 1 => //; subst l0.
  case: H3 => ? ?; subst t0 t3.
  inj_ex H4; case: H4 => He1 He2.
  inj_ex He1; subst e0.
  inj_ex He2; subst e3.
  inj_ex H5; subst v.
  by move=> /IH1 <- /IH2 <-.
- move=> l x n {}v {}mv.
  inversion 1; subst l0 x0.
  inj_ex H6.
  by inj_ex H7.
- move=> l r r1 {}v {}mv.
  inversion 1; subst l0 r0.
  inj_ex H3; subst v.
  by have -> : r1 = r3 by exact: Prop_irrelevance.
- move=> l k e0 f mf ev IH {}v {}mv.
  inversion 1; subst l0 k0.
  inj_ex H2; subst e0.
  inj_ex H4; subst v.
  by rewrite (IH _ _ H3).
- move=> l t e0 k ev IH {}v {}mv.
  inversion 1; subst l0 t0.
  inj_ex H2; subst e0.
  inj_ex H4; subst v.
  by rewrite (IH _ H3).
- move=> l t e0 x xl f mf ev IH {}v {}mv.
  simple inversion 1 => //; subst t0.
  case: H1 => ? ?; subst x0 l0.
  inj_ex H3; case: H3 => H3; inj_ex H3; subst e0.
  inj_ex H4; subst v.
  by move=> /IH <-.
- move=> l r r1 p.
  inversion 1; subst l0 r0.
  inj_ex H3; subst p.
  by have -> : r1 = r3 by exact: Prop_irrelevance.
- move=> l t e0 f1 mf1 e2 k2 e3 k3 ev1 IH1 ev2 IH2 ev3 IH3 k.
  inversion 1; subst l0 T.
  inj_ex H0; subst e0.
  inj_ex H1; subst e4.
  inj_ex H5; subst k.
  inj_ex H2; subst e5.
  have ? := IH1 _ _ H6; subst f2.
  have -> : mf1 = mf by exact: Prop_irrelevance.
  by rewrite (IH2 _ H7) (IH3 _ H8).
- move=> l G e0 f mf ev IH k.
  simple inversion 1 => //; subst l0.
  inj_ex H4; subst k.
  inj_ex H3; case: H3 => H3; inj_ex H3; subst e0.
  move/IH => ?; subst f0.
  by have -> : mf = mf0 by exact: Prop_irrelevance.
- move=> l t e0 f mf ev IH k.
  inversion 1; subst l0 T.
  inj_ex H5; subst e1.
  inj_ex H7; subst k.
  have ? := IH _ _ H3; subst f1.
  by have -> : mf = mf1 by exact: Prop_irrelevance.
- move=> l G t1 t2 x e1 e2 k1 k2 ev1 IH1 ev2 IH2 k.
  inversion 1; subst l0 t0 t3 x0.
  inj_ex H10; subst k.
  inj_ex H8; subst e5.
  inj_ex H7; subst e4.
  by rewrite (IH1 _ H4) (IH2 _ H11).
- move=> l t e0 x xl k1 ev IH {}k.
  inversion 1; subst l0 t0 x0.
  inj_ex H4; subst e0.
  inj_ex H5; subst k.
  by rewrite (IH _ H3).
Qed.

Lemma evalP_uniq (l : context) t (e : expP l t)
  (u v : R.-sfker typei2 (slist (map snd l)) ~> typei2 t) :
  evalP e u -> evalP e v -> u = v.
Proof.
move=> hu.
apply: (@evalP_mut_ind R
  (fun l (G := slist (map snd l)) t (e : expD l t) (f : typei2 G -> typei2 t)
    (mf : measurable_fun setT f) (h1 : evalD e mf) =>
    forall (v : typei2 G -> typei2 t) (mv : measurable_fun setT v), evalD e mv -> f = v)
  (fun l (G := slist (map snd l)) t (e : expP l t)
    (u : R.-sfker typei2 G ~> typei2 t) (h1 : evalP e u) =>
    forall (v : R.-sfker typei2 G ~> typei2 t), evalP e v -> u = v)); last exact: hu.
all: rewrite {l t e u v hu}.
- move=> l {}v {}mv.
  inversion 1; subst l0.
  by inj_ex H3.
- move=> l b {}v {}mv.
  inversion 1; subst l0 b0.
  by inj_ex H3.
- move=> l r {}v {}mv.
  inversion 1; subst l0 r0.
  by inj_ex H3.
- move=> l t1 t2 G e1 f1 mf1 e2 f2 mf2 ev1 IH1 ev2 IH2 {}v {}mv.
  simple inversion 1 => //; subst l0.
  case: H3 => ? ?; subst t0 t3.
  inj_ex H4; case: H4 => He1 He2.
  inj_ex He1; subst e0.
  inj_ex He2; subst e3.
  inj_ex H5; subst v.
  move=> e1f0 e2f3.
  by rewrite (IH1 _ _ e1f0) (IH2 _ _ e2f3).
- move=> l x n {}v {}mv.
  inversion 1; subst l0.
  inj_ex H7; subst v.
  by inj_ex H6.
- move=> l r r1 {}v {}mv.
  inversion 1; subst l0 r0.
  inj_ex H3; subst v.
  by have -> : r1 = r3 by exact: Prop_irrelevance.
- move=> l k e f mf ev IH {}v {}mv.
  inversion 1; subst l0 k0.
  inj_ex H2; subst e0.
  inj_ex H4; subst v.
  inj_ex H5; subst mv.
  by rewrite (IH _ _ H3).
- move=> l t e k ev IH {}v {}mv.
  inversion 1; subst l0 t0.
  inj_ex H2; subst e0.
  inj_ex H4; subst v.
  inj_ex H5; subst mv.
  by rewrite (IH _ H3).
- move=> l t e x xl f mf ev IH {}v {}mv.
  simple inversion 1 => //; subst t0.
  case: H1 => ? ?; subst x0 l0.
  inj_ex H3; case: H3 => H3.
  inj_ex H3; subst e0.
  inj_ex H4; subst v.
  inj_ex H5; subst mv.
  by move/IH => <-.
- move=> l r r1 ev.
  inversion 1; subst l0 r0.
  inj_ex H3; subst ev.
  by have -> : r1 = r3 by exact: Prop_irrelevance.
- move=> l t e f mf e1 k1 e2 k2 ev IH ev1 IH1 ev2 IH2 k.
  inversion 1; subst l0 T.
  inj_ex H0; subst e0.
  inj_ex H1; subst e3.
  inj_ex H5; subst k.
  inj_ex H2; subst e4.
  have ? := IH _ _ H6; subst f0.
  have -> : mf0 = mf by exact: Prop_irrelevance.
  by rewrite (IH1 _ H7) (IH2 _ H8).
- move=> l G e f mf ev IH k.
  simple inversion 1 => //; subst l0.
  inj_ex H4; subst k.
  inj_ex H3; case: H3 => H3; inj_ex H3; subst e0.
  move=> /IH ?; subst f0.
  by have -> : mf = mf0 by exact: Prop_irrelevance.
- move=> l t e f mf ev IH k.
  inversion 1; subst T l0.
  inj_ex H7; subst k.
  inj_ex H5; subst e1.
  have ? := IH _ _ H3; subst f1.
  by have -> : mf = mf1 by exact: Prop_irrelevance.
- move=> l G t1 t2 x e1 e2 k1 k2 ev1 IH1 ev2 IH2 k.
  inversion 1; subst l0 x0 t3 t0.
  inj_ex H10; subst k.
  inj_ex H7; subst e4.
  inj_ex H8; subst e5.
  by rewrite (IH1 _ H4) (IH2 _ H11).
- move=> l t e x xl k1 ev IH {}k.
  inversion 1; subst x0 l0 t0.
  inj_ex H4; subst e0.
  inj_ex H5; subst k.
  by rewrite (IH _ H3).
Qed.

Lemma evalD_full (l : context) (t : stype) e :
  exists f (mf : measurable_fun _ f), @evalD R l t e f mf.
Proof.
apply: (@expD_mut_ind R
  (fun l t (e : expD l t) => exists f (mf : measurable_fun setT f), evalD e mf)
  (fun l t (e : expP l t) => exists k, evalP e k)).
all: rewrite {l t e}.
- move=> l st x e [f [mf fmf]] xl.
  by exists (eta1 f), (meta1 mf); exact/EV_WeakD.
- by do 2 eexists; exact: EV_unit.
- by do 2 eexists; exact: EV_bool.
- by do 2 eexists; exact: EV_real.
- move=> l t1 t2 e1 [f1 [mf1 H1]] e2 [f2 [mf2 H2]].
  by exists (fun x => (f1 x, f2 x)); eexists; exact: EV_pair.
- by move=> l x t tE; subst t; eexists; eexists; exact: EV_var.
- by move=> r r1; eexists; eexists; exact: EV_bernoulli.
- move=> l k e [f [mf H]].
  exists (poisson k \o f), (measurable_funT_comp (mpoisson k) mf).
  exact: EV_poisson.
- move=> l t e [k H].
  by exists (normalize k point), (measurable_fun_normalize k); exact: EV_norm.
- move=> l st x e [k H1] xl.
  by exists [the _.-sfker _ ~> _ of keta1 k]; exact: EV_WeakP.
- move=> l t e1 [f [mf H1]] e2 [k2 H2] e3 [k3 H3].
  by exists (ite mf k2 k3); exact: EV_ifP.
- move=> l t1 t2 x e1 [k1 ev1] e2 [k2 ev2].
  by exists (letin' k1 k2); exact: EV_letin.
- move=> l r r1.
  by exists (sample [the pprobability _ _ of bernoulli r1]); exact: EV_sample.
- move=> l e [f [mf f_mf]].
  by exists (score mf); exact: EV_score.
- by move=> l t e [f [mf f_mf]]; exists (ret mf); exact: EV_return.
Qed.

Lemma evalP_full (l : context) (t : stype) e :
  exists (k : R.-sfker _ ~> _), @evalP R l t e k.
Proof.
apply: (@expP_mut_ind R
  (fun l t (e : expD l t) => exists f (mf : measurable_fun _ f), evalD e mf)
  (fun l t (e : expP l t) => exists k, evalP e k)).
all: rewrite {l t e}.
- move=> l t x e [f [mf H]] xl.
  by exists (eta1 f), (meta1 mf); exact: EV_WeakD.
- by do 2 eexists; exact: EV_unit.
- by do 2 eexists; exact: EV_bool.
- by do 2 eexists; exact: EV_real.
- move=> l t1 t2 e1 [f1 [mf1 H1]] e2 [f2 [mf2 H2]].
  by exists (fun x => (f1 x, f2 x)); eexists; exact: EV_pair.
- by move=> l x t tE; subst t; eexists; eexists; exact: EV_var.
- by move=> r r1; eexists; eexists; exact: EV_bernoulli.
- move=> l k e [f [mf H]].
  exists (poisson k \o f), (measurable_funT_comp (mpoisson k) mf).
  exact: EV_poisson.
- move=> l t e []k H.
  by exists (normalize k point), (measurable_fun_normalize k); exact: EV_norm.
- move=> l s x e [k H1] xl.
  by exists [the _.-sfker _ ~> _ of keta1 k]; exact: EV_WeakP.
- move=> l t e1 [f [mf H1]] e2 [k2 H2] e3 [k3 H3].
  by exists (ite mf k2 k3); exact: EV_ifP.
- move=> l t1 t2 x e1 [k1 ev1] e2 [k2 ev2].
  by exists (letin' k1 k2); exact: EV_letin.
- move=> l r r1.
  by exists (sample [the pprobability _ _ of bernoulli r1]); exact: EV_sample.
- by move=> l e [f [mf H]]; exists (score mf); exact: EV_score.
- by move=> l t e [f [mf H]]; exists (ret mf); exact: EV_return.
Qed.

Definition execP l t (e : @expP R l t) :
  R.-sfker (@typei2 R (slist (map snd l))) ~> @typei2 R t.
Proof.
have /cid h := @evalP_full l t e.
exact: (proj1_sig h).
Defined.

Lemma evalP_execP l t e : l # e -P-> @execP l t e.
Proof. by rewrite /execP/= /sval ?/ssr_have/=; case: cid. Qed.

Definition execD l t (e : @expD R l t) :
  {f : (@typei2 R (slist (map snd l))) -> @typei2 R t & measurable_fun setT f}.
Proof.
have /cid [f /cid[mf H]] := @evalD_full l t e.
by exists f.
Defined.

Lemma evalD_execD l t e : let: x := @execD l t e in
  l # e -D-> projT1 x ; projT2 x.
Proof.
rewrite /execD ?/ssr_have /= /sval /=; case: cid => f [mf ef].
by case: cid.
Defined.

Definition execP_ret_real (l : context) (r : R) :
    R.-sfker (@typei2 R (slist (map snd l))) ~> @typei2 R sreal :=
  execP (exp_return (exp_real r)).

Scheme expD_mut_rec := Induction for expD Sort Type
with expP_mut_rec := Induction for expP Sort Type.

Require Import JMeq.

Obligation Tactic := idtac.

(*Definition vx : R.-sfker munit ~> mR R := execP_ret_real [::] 1.
Definition VX z : set (mR R) -> \bar R := vx z.
Let VX0 z : (VX z) set0 = 0. Proof. by []. Qed.
Let VX_ge0 z x : 0 <= (VX z) x. Proof. by []. Qed.
Let VX_semi_sigma_additive z : semi_sigma_additive (VX z).
Proof. exact: measure_semi_sigma_additive. Qed.
HB.instance Definition _ z := @isMeasure.Build _ R (mR R) (VX z) (VX0 z)
  (VX_ge0 z) (@VX_semi_sigma_additive z).
Let sfinVX z : sfinite_measure (VX z). Proof. exact: sfinite_kernel_measure. Qed.
HB.instance Definition _ z := @Measure_isSFinite_subdef.Build _ (mR R) R
  (VX z) (sfinVX z).

Definition vy' : R.-sfker munit ~> mR R := execP_ret_real [::] 2.
Definition VY z : set (mR R) -> \bar R := vy' z.
Let VY0 z : (VY z) set0 = 0. Proof. by []. Qed.
Let VY_ge0 z x : 0 <= (VY z) x. Proof. by []. Qed.
Let VY_semi_sigma_additive z : semi_sigma_additive (VY z).
Proof. exact: measure_semi_sigma_additive. Qed.
HB.instance Definition _ z := @isMeasure.Build _ R (mR R) (VY z) (VY0 z)
  (VY_ge0 z) (@VY_semi_sigma_additive z).
Let sfinVY z : sfinite_measure (VY z). Proof. exact: sfinite_kernel_measure. Qed.
HB.instance Definition _ z := @Measure_isSFinite_subdef.Build _ (mR R) R
  (VY z) (sfinVY z).*)

Lemma execD_real l r :
  @execD l _ [r :r] = existT _ (cst r) (kr r).
Proof.
rewrite /execD /=.
case: cid => f ?.
case: cid => ? ev1.
have ev2 := (EV_real l r).
have fcstr := (evalD_uniq ev1 ev2).
subst.
congr existT.
apply Prop_irrelevance.
Qed.

Lemma execP_WP_keta1 x l (st : stype_eqType) (e : expP l st) (xl : x.1 \notin map fst l) :
  execP (@expWP R l st _ e xl) = [the _.-sfker _ ~> _ of keta1 (execP e)].
Proof.
apply: evalP_uniq; first exact/evalP_execP.
by apply: EV_WeakP; exact: evalP_execP.
Qed.

Lemma execP_letin l x t1 t2 (e1 : expP l t1) (e2 : expP ((x, t1) :: l) t2) :
  execP [Let x <~ e1 In e2] = letin' (execP e1) (execP e2) :> (R.-sfker _ ~> _).
Proof.
apply: evalP_uniq; first exact/evalP_execP.
by apply: EV_letin; exact/evalP_execP.
Qed.

Lemma execP_ret l t (e : @expD R l t) : execP [Ret e] = ret (projT2 (execD e)).
Proof.
apply: evalP_uniq; first exact/evalP_execP.
by apply: EV_return; exact/evalD_execD.
Qed.

Lemma execD_pair l (G := slist (map snd l)) t1 t2
  (x : @expD R l t1)
  (y : @expD R l t2) :
  let f := projT1 (execD x) in
  let g := projT1 (execD y) in
  let mf := projT2 (execD x) in
  let mg := projT2 (execD y) in
  execD [(x, y)] =
  @existT _ _ (fun z => (f z, g z))
  (@measurable_fun_pair _ _ _ (typei2 (slist (map snd l))) (typei2 t1) (typei2 t2)
    f g mf mg).
Proof.
move=> f g mf mg.
rewrite /f /g /mf /mg.
set lhs := LHS.
set rhs := RHS.
have h : projT1 lhs = projT1 rhs.
  apply: (@evalD_uniq l _ [(x, y)] (projT1 lhs) (projT1 rhs) (projT2 lhs) (projT2 rhs)).
  exact: evalD_execD.
  by apply: EV_pair; exact: evalD_execD.
exact: eq_sigT_hprop.
Qed.

Lemma execD_var l (x : string) :
  let i := seq.index x (map fst l) in
  @execD l _ [% {x} ] = existT _ (varof (map snd l) i) (@mvarof R (map snd l) i).
Proof.
rewrite /execD /=.
case: cid => f ?.
case: cid => ? ev1.
have ev2 := (EV_var R l x).
have fcstr := (evalD_uniq ev1 ev2).
subst.
congr existT.
exact: Prop_irrelevance.
Qed.

End eval_prop.

Section staton_bus.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Variables (R : realType).

Example __ : @evalD R [::] _ [{3}:r] (cst 3) (kr 3).
Proof. apply/EV_real. Qed.

Example ex_ret : @evalP R [::] _ [Ret {3}:r] (ret (kr 3)).
Proof. apply/EV_return/EV_real. Qed.

Check ret (kr 3) : R.-sfker _ ~> (mR R).
Check ret (kr 3) tt : {measure set mR R -> \bar R}.
Goal (ret (kr 3) : R.-sfker _ ~> (mR R)) tt [set: R] = 1%:E.
Proof. rewrite /= diracE in_setT //. Qed.

Structure tagged_context := Tag {untag : context}.

Definition recurse_tag h := Tag h.
Canonical found_tag h := recurse_tag h.

Structure find (s : string) (t : stype) := Find {
  context_of : tagged_context ;
  ctxt_prf : t = nth sunit (map snd (untag context_of))
                           (seq.index s (map fst (untag context_of)))}.

Lemma left_pf (s : string) (t : stype) (l : context) :
  t = nth sunit (map snd ((s, t) :: l)) (seq.index s (map fst ((s, t) :: l))).
Proof.
by rewrite /= !eqxx/=.
Qed.

Canonical found_struct s t (l : context) : find s t :=
  Eval hnf in @Find s t (found_tag ((s, t) :: l)) (@left_pf s t l).

Lemma right_pf (s : string) (t : stype) (l : context) u t' :
  s != u ->
  t' = nth sunit (map snd l) (seq.index u (map fst l)) ->
  t' = nth sunit (map snd ((s, t) :: l)) (seq.index u (map fst ((s, t) :: l))).
Proof.
move=> su ut'l /=.
case: ifPn => //=.
by rewrite (negbTE su).
Qed.

Canonical recurse_struct s t t' u {su : infer (s != u)} (l : find u t') : find u t' :=
  Eval hnf in @Find u t' (recurse_tag ((s, t) :: untag (context_of l)))
  (@right_pf s t (untag (context_of l)) u t' su (ctxt_prf l)).

Definition exp_var' (x : string) (t : stype) (g : find x t) :=
  @exp_var R (untag (context_of g)) x t (ctxt_prf g).

Notation "%1 x" := (@exp_var' x%string _ _) (in custom expr at level 1).

Example staton_bus_exp := exp_norm (
  [Let "x" <~ {exp_sample_bern [::] (2 / 7%:R)%:nng p27} In
   Let "r" <~ If %1{"x"} Then Ret {3}:r Else Ret {10}:r In
   Let "_" <~ {exp_score (exp_poisson 4 [%1{"r"}])} In
   Ret %1{"x"}]).

Definition sample_bern : R.-sfker munit ~> mbool :=
  sample [the probability _ _ of bernoulli p27].
Definition ite_3_10 :
  R.-sfker [the measurableType _ of (mbool * munit)%type] ~> (mR R) :=
  ite var1of4' (ret k3) (ret k10).
Definition score_poi :
  R.-sfker [the measurableType _ of (mR R * (mbool * munit))%type] ~> munit :=
  score (measurable_funT_comp (mpoisson 4) var1of4').

Local Definition kstaton_bus'' :=
  letin' sample_bern
    (letin' ite_3_10
      (letin' score_poi (ret var3of4'))).

Example eval_staton_bus_exp :
  [::] # staton_bus_exp -D-> _ ; measurable_fun_normalize kstaton_bus''.
Proof.
apply/EV_norm/EV_letin.
- exact/EV_sample.
- apply/EV_letin.
  + apply/EV_ifP.
    * rewrite /exp_var' /=.
      rewrite (_ : left_pf _ _ _ = erefl) //.
      set l := (X in X # _ -D-> _ ; _).
      rewrite (_ : var1of2 = @mvarof R (map snd l) 0)//.
      exact: (EV_var _ _ "x").
    * exact/EV_return/EV_real.
    * exact/EV_return/EV_real.
- apply: EV_letin.
  + apply/EV_score/EV_poisson.
    rewrite /exp_var'/=.
    rewrite (_ : left_pf _ _ _ = erefl) //.
    set l := (X in X # _ -D-> _ ; _).
    rewrite (_ : var1of2 = @mvarof R (map snd l) 0)//.
    exact: (EV_var _ _ "r").
  + apply/EV_return.
    rewrite /exp_var'/=.
    rewrite (_ : right_pf _ _ _ = erefl) //.
    set l := (X in X # _ -D-> _ ; _).
    rewrite (_ : var3of4' = @mvarof R (map snd l) 2)//.
    exact: (EV_var _ _ "x").
Qed.

End staton_bus.

Section letinC.
Local Open Scope lang_scope.
Variable R : realType.

Lemma ex_var_ret l : @execP R l _ [Let "x" <~ Ret {1}:r In Ret %{"x"}] = letin' (ret (kr 1)) (ret var1of2).
Proof.
rewrite execP_letin; congr letin'.
by rewrite execP_ret execD_real.
by rewrite execP_ret execD_var; congr ret.
Qed.

Lemma ex_var_ret2 l : 
  @execP R l _ [Let "x" <~ Ret {1}:r In Let "y" <~ Ret {2}:r In 
    Ret (%{"x"}, %{"y"})] = 
  @execP R l _ [Let "y" <~ Ret {2}:r In Let "x" <~ Ret {1}:r In
    Ret (%{"x"}, %{"y"})].
Proof.
rewrite !execP_letin !execP_ret !execD_real.
rewrite !execD_pair !execD_var /=.
have -> : mvarof (R := R) [:: sreal, sreal & [seq i.2 | i <- l]] 0 = var1of2.
  exact: Prop_irrelevance.
have -> : mvarof (R := R) [:: sreal, sreal & [seq i.2 | i <- l]] 1 = var2of4'.
  exact: Prop_irrelevance.
(* rewrite (letin'C _ _ (ret (kr 2))). *)
(* rewrite letin_pair /=.
by rewrite execP_ret execD_real.
by rewrite execP_ret execD_var; congr ret. *)
Admitted.

Lemma LetInC l t1 t2 (e1 : @expP R l t1) (e2 : expP l t2)
  (xl : "x" \notin map fst l) (yl : "y" \notin map fst l) :
  forall U, measurable U ->
  execP [Let "x" <~ e1 In
        Let "y" <~ {@expWP _ _ _ ("x", t1) e2 xl} In
        Ret (%{"x"}, %{"y"})] ^~ U =
  execP [Let "y" <~ e2 In
        Let "x" <~ {@expWP _ _ _ ("y", t2) e1 yl} In
        Ret (%{"x"}, %{"y"})] ^~ U :> (typei2 (slist (map snd l)) -> \bar R).
Proof.
move=> U mU; apply/funext => x.
rewrite 4!execP_letin.
rewrite 2!execP_WP_keta1.
rewrite 2!execP_ret /=.
rewrite 2!execD_pair/=.
rewrite (execD_var _ _ "x")/= (execD_var _ _ "y")/=.
have -> : mvarof (R := R) [:: t2, t1 & [seq i.2 | i <- l]] 0 = var1of2.
  exact: Prop_irrelevance.
have -> : mvarof (R := R) [:: t2, t1 & [seq i.2 | i <- l]] 1 = var2of4'.
  exact: Prop_irrelevance.
rewrite (letin'C _ _ (execP e2) [the R.-sfker _ ~> _ of @keta1 _  ("y", t2) _ _ (execP e1)]); [ |by [] | by [] |by []].
rewrite (execD_var _ _ "x")/= (execD_var _ _ "y")/=.
have -> : mvarof (R := R) [:: t1, t2 & [seq i.2 | i <- l]] 0 = var1of2.
  exact: Prop_irrelevance.
have -> : mvarof (R := R) [:: t1, t2 & [seq i.2 | i <- l]] 1 = var2of4'.
  exact: Prop_irrelevance.
done.
Qed.

(* Reserved Notation "x =k y". *)

Lemma execP_LetInL l t1 t2 x (e1 : @expP R l t1) (e1' : expP l t1) (e2 : expP ((x, t1) :: l) t2) :
  forall U, measurable U ->
  execP e1 = (* =k *) execP e1' ->
  execP [Let x <~ e1 In e2] ^~ U =
  execP [Let x <~ e1' In e2] ^~ U.
Proof.
by move=> U mU e1e1'; rewrite !execP_letin e1e1'.
Qed.

Lemma execP_LetInR l t1 t2 x (e1 : @expP R l t1) (e2 : expP _ t2) (e2' : expP ((x, t1) :: l) t2) :
  forall U, measurable U ->
  execP e2 = execP e2' ->
  execP [Let x <~ e1 In e2] ^~ U =
  execP [Let x <~ e1 In e2'] ^~ U.
Proof.
by move=> U mU e1e1'; rewrite !execP_letin e1e1'.
Qed.

Example LetInC12 : forall U, measurable U ->
  @execP R [::] _ [Let "x" <~ Ret {1}:r In
         Let "y" <~ Ret {2}:r In
         Ret (%{"x"}, %{"y"})] ^~ U =
  execP [Let "y" <~ Ret {2}:r In
         Let "x" <~ Ret {1}:r In
         Ret (%{"x"}, %{"y"})] ^~ U.
Proof.
move=> U mU.
apply: (@trans_eq _ _ (execP
  [Let "x" <~ Ret {1} :r In 
   Let "y" <~ {@expWP R [::] sreal ("x", sreal) [Ret {2}:r] erefl} In Ret (% {"x"}, % {"y"})] ^~ U)).
  apply: execP_LetInR => //.
  apply: eq_sfkernel=> ? ?.
  (* apply: execP_LetInL => //.
  have H : (execP [Ret {2}:r] = execP (@expWP R [::] sreal ("x", sreal) [Ret {2}:r] erefl)).
    rewrite execP_WP_keta1 !execP_ret !execD_real.
    exact/eq_sfkernel.
  apply: execP_LetInR => //.
  erewrite (execP_LetIn _ _ _  H).
rewrite LetInC //.
apply: execP_LetIn3.
  have H : (execP [Ret {1}:r] = execP (@expWP R [::] sreal ("y", sreal) [Ret {1}:r] erefl)).
  rewrite execP_WP_keta1 !execP_ret !execD_real.
  exact/eq_sfkernel.
  apply: execP_LetIn3.
exact: LetInC. *)
Admitted.

Lemma LetInA l t1 t2 t3 (e1 : @expP R l t1) (e2 : expP [:: ("y", t1) & l] t2) 
  (e3 : expP l t3) (xl : "x" \notin map fst l) (yl : "y" \notin map fst l) :
  forall U, measurable U ->
  execP [Let "y" <~ e1 In
         Let "x" <~ e2 In
         {@expWP _ _ _ ("x", t2) (@expWP _ _ _ ("y", t1) e3 yl) xl}] ^~ U =
  execP [Let "x" <~ Let "y" <~ e1 In e2 In 
         {@expWP _ _ _ ("x", t2) e3 xl}] ^~ U.
Proof.
move=> U mU; apply/funext=> x.
rewrite !execP_letin !execP_WP_keta1.
exact: letin'A.
Qed.

Example LetInA12 : forall U, measurable U ->
  @execP R [::] _ [Let "y" <~ Ret {1}:r In
         Let "x" <~ Ret {2}:r In Ret %{"x"}] ^~ U =
  @execP R [::] _ [Let "x" <~ Let "y" <~ Ret {1}:r In Ret {2}:r In 
         Ret %{"x"}] ^~ U.
Proof.
move=> U mU.
(* apply: (@trans_eq _ _ (execP
  [Let "x" <~ Let "y" <~ Ret {1}:r In Ret {2}:r In Ret %{"x"}] ^~ U)). *)
(* apply: (@trans_eq _ _ (execP
  [Let "y" <~ Ret {1}:r In
   Let "x" <~ Ret {2}:r In
   Ret %{"x"}] ^~ U)). *)
(* apply: letinA. *)
rewrite !execP_letin !execP_ret !execD_real !execD_var /=.
apply: funext=> x.
exact: letin'A.
Qed.

Lemma letinC l t1 t2 (e1 : @expP R l t1) (e2 : expP l t2)
  (xl : "x" \notin map fst l) (yl : "y" \notin map fst l)
  (v1 v2 : R.-sfker typei2 (slist (map snd l)) ~> typei2 (spair t1 t2)) :
  l # [Let "x" <~ e1 In
        Let "y" <~ {@expWP _ _ _ ("x", t1) e2 xl} In
        Ret (%{"x"}, %{"y"})] -P-> v1
  ->
  l # [Let "y" <~ e2 In
        Let "x" <~ {@expWP _ _ _ ("y", t2) e1 yl} In
        Ret (%{"x"}, %{"y"})] -P-> v2 ->
  forall U, measurable U -> v1 ^~ U = v2 ^~ U.
Proof.
move=> ev1 ev2.
pose k1 : R.-sfker _ ~> typei2 t1 := execP e1.
pose k2' : R.-sfker _ ~> _ := @execP R (("x", t1) :: l) t2 (@expWP _ _ _ ("x", t1) e2 xl).
pose vx : R.-sfker typei2 (slist (map snd l)) ~>
    [the measurableType _ of (typei2 t1 * typei2 t2)%type] :=
  letin' k1
  (letin' k2'
  (ret (measurable_fun_pair
    (T:= [the measurableType _ of
      (typei2 t2 * (typei2 t1 * (projT2 (prod_meas (map typei (map snd l))))))%type])
    (T1:= typei2 t1)
    (f := fst \o snd) (g:= fst) var2of4' var1of2))).
have ev1' : l # [Let "x" <~ e1 In Let "y" <~ {@expWP _ _ _ ("x", t1) e2 xl} In Ret (%{"x"}, %{"y"})] -P-> vx.
  apply: EV_letin; first exact: evalP_execP.
  apply: EV_letin; first exact: evalP_execP.
  apply/EV_return/EV_pair.
  - have -> : var2of4' = @mvarof R (t2 :: t1 :: map snd l) 1 by [].
    exact: EV_var.
  - have -> : var1of2 = @mvarof R (t2 :: t1 :: map snd l) 0 by [].
    exact: EV_var.
rewrite (evalP_uniq ev1 ev1').
pose k2 : R.-sfker _ ~> typei2 t2 := @execP R l t2 e2.
pose k1' : R.-sfker _ ~> _ := @execP R [:: ("y", t2) & l] t1 (@expWP _ _ _ ("y", t2) e1 yl).
pose vy : R.-sfker typei2 (slist (map snd l)) ~>
    [the measurableType _ of (typei2 t1 * typei2 t2)%type] :=
   letin' k2 (letin' k1'
   (ret (measurable_fun_pair
     (T := [the measurableType _ of
       typei2 t1 * (typei2 t2 * (projT2 (prod_meas (map typei (map snd l)))))]%type)
     (T2 := typei2 t2) (f := fst) (g:= fst \o snd) var1of2 var2of4'))).
have ev2' : l # [Let "y" <~ e2 In Let "x" <~ {@expWP _ _ _ ("y", t2) e1 yl} In Ret (%{"x"}, %{"y"})] -P-> vy.
  apply: EV_letin; first exact: evalP_execP.
  apply: EV_letin; first exact: evalP_execP.
  apply/EV_return/EV_pair.
  - have -> : var1of2 = @mvarof R (t1 :: t2 :: map snd l) 0 by [].
    exact: EV_var.
  - have -> : var2of4' = @mvarof R (t1 :: t2 :: map snd l) 1 by [].
    exact: EV_var.
rewrite (evalP_uniq ev2 ev2').
rewrite /vx /vy => t U/=.
apply/funext => x.
apply: (@letin'C _ _ _ (typei2 t1) (typei2 t2)).
- move=> ST /= TATBU.
  rewrite /k1' /k1.
  by rewrite (@execP_WP_keta1 _ ("y", t2) _ _ e1).
- move=> ST /= TATBU.
  rewrite /k2 /k2'.
  by rewrite (@execP_WP_keta1 _ ("x", t1) _ _ e2).
- by [].
Qed.

Example letinr_ ta tb (l := [:: ("r", ta); ("_", tb)]) t1 t2
  (e1 : @expP R l t1) (e2 : expP l t2)
  (v1 v2 : (R.-sfker typei2 (slist (map snd l)) ~> typei2 (spair t1 t2))) :
  l # [Let "x" <~ e1 In
        Let "y" <~ %WP {"x"} # e2 In
        Ret (%{"x"}, %{"y"})] -P-> v1
  ->
  l # [Let "y" <~ e2 In
        Let "x" <~ %WP {"y"} # e1 In
        Ret (%{"x"}, %{"y"})] -P-> v2 ->
  forall U, measurable U -> v1 ^~ U = v2 ^~ U.
Proof. exact: letinC. Abort.

End letinC.
