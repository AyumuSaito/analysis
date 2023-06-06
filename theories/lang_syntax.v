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

Section string_eq.

Definition string_eqMixin := @EqMixin string eqb eqb_spec.
Canonical string_eqType := EqType string string_eqMixin.

End string_eq.

Section context.
Variables (R : realType).
Definition ctx := seq (string * typ).

Definition measurable_of_ctx (l : ctx) := @measurable_of_seq R (map snd l).
Definition mctx l := projT2 (measurable_of_ctx l).

End context.
Arguments measurable_of_ctx {R}.
Arguments mctx {R}.

Definition insert (T : eqType) (l : seq T) (x : T) (n : nat) :=
  (take n l ++ x :: drop n l)%SEQ.

Section expr.
Variables (R : realType).

Local Open Scope seq_scope.
Inductive expD : ctx -> typ -> Type :=
| expWD l1 l2 t x : expD (l1 ++ l2) t -> x.1 \notin map fst (l1 ++ l2) -> expD (l1 ++ x :: l2) t
| exp_unit l : expD l Unit
| exp_bool l : bool -> expD l Bool
| exp_real l : R -> expD l Real
| exp_pair l t1 t2 : expD l t1 -> expD l t2 -> expD l (t1, t2)%P
| exp_var (l : ctx) x t :
  t = nth Unit (map snd l) (seq.index x (map fst l)) ->
  expD l t
| exp_bernoulli l (r : {nonneg R}) (r1 : (r%:num <= 1)%R) : expD l (Prob Bool)
| exp_poisson l : nat -> expD l Real -> expD l Real
| exp_norm l t : expP l t -> expD l (Prob t)
with expP : ctx -> typ -> Type :=
| expWP l1 l2 t x : expP (l1 ++ l2) t -> x.1 \notin map fst (l1 ++ l2) -> expP (l1 ++ x :: l2) t
| exp_if l t : expD l Bool -> expP l t -> expP l t -> expP l t
| exp_letin l t1 t2 (x : string) :
  expP l t1 -> expP ((x, t1) :: l) t2 -> expP l t2
| exp_sample l t : expD l (Prob t) -> expP l t
| exp_score l : expD l Real -> expP l Unit
| exp_return l t : expD l t -> expP l t.

End expr.

Arguments expD {R}.
Arguments expP {R}.
Arguments expWD {R l1 l2 t x}.
Arguments exp_unit {R l}.
Arguments exp_bool {R l}.
Arguments exp_real {R l}.
Arguments exp_pair {R l t1 t2}.
Arguments exp_var {R l} _ {t}.
Arguments exp_bernoulli {R l}.
Arguments exp_poisson {R l}.
Arguments exp_norm {R l _}.
Arguments expWP {R l1 l2 t x}.
Arguments exp_if {R l t}.
Arguments exp_letin {R l _ _}.
(* Arguments exp_sample {R l t}. *)
(*Arguments exp_sample_bern {R} l r.*)
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
Notation "e \U x" := (@expWP _ [::] _ _ (x, _) e erefl)
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

Local Open Scope lang_scope.

Definition dval (R : realType) (l : ctx) (t : typ) :=
  @mctx R l -> @mtyp R t.
Definition pval (R : realType) (l : ctx) (t : typ) :=
  R.-sfker @mctx R l ~> @mtyp R t.

Section kweaken.
Variables (R : realType).

Definition weaken x (l : ctx) t (f : dval R l t) : dval R (x :: l) t
  := f \o snd.

Lemma mweaken x (l : ctx) t (f : dval R l t)
  (mf : measurable_fun setT f) : measurable_fun setT (@weaken x l t f).
Proof. exact: (measurableT_comp mf). Qed.

Definition kweaken (x : string * typ) l t (k : R.-sfker (@mctx R l) ~> @mtyp R t)
  : mctx (x :: l) -> {measure set mtyp t -> \bar R} := k \o snd.

Section kernel_weaken.
Context (x : string * typ) l t (k : pval R l t).

Let mk U : measurable U -> measurable_fun setT ((@kweaken x l t k) ^~ U).
Proof.
move=> mU; rewrite (_ : (@kweaken x l t k) ^~ U = (k ^~ U) \o snd)//.
by apply: measurableT_comp => //; exact: measurable_kernel.
Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ _ (@kweaken x l t k) mk.
End kernel_weaken.

Section sfkernel.
Context (x : string * typ) l t (k : pval R l t).

Let sk : exists2 s : (R.-ker @mctx R (x :: l) ~> @mtyp R t)^nat,
  forall n, measure_fam_uub (s n) &
  forall x0 U, measurable U -> (@kweaken x l t k) x0 U = kseries s x0 U .
Proof.
have [s hs] := sfinite_kernel k.
exists (fun n => [the _.-ker _ ~> _ of @kweaken x l t (s n)]).
  move=> n.
  have [M hM] := measure_uub (s n).
  exists M => x0.
  exact: hM.
move=> x0 U mU.
by rewrite /kweaken/= hs.
Qed.

HB.instance Definition _ :=
  Kernel_isSFinite_subdef.Build _ _ _ _ _ (@kweaken x l t k) sk.

End sfkernel.

Section fkernel_weaken.
Context (x : string * typ) l t (k : R.-fker @mctx R l ~> @mtyp R t).

Let uub : measure_fam_uub (@kweaken x l t k).
Proof.
have [M hM] := measure_uub k.
exists M => x0.
exact: hM.
Qed.

HB.instance Definition _ := @Kernel_isFinite.Build _ _ _ _ _
  (@kweaken x l t k) uub.
End fkernel_weaken.

End kweaken.

Section kweaken2.
Variables (R : realType).
Local Open Scope seq_scope.

Definition weaken3 : forall (l1 l2 : ctx) x (f : @mctx R (l1 ++ x :: l2)), @mctx R (l1 ++ l2).
fix H 1.
intros l1 l2 x f.
destruct l1 as [|h1 l1].
  destruct f as [f1 f2].
  exact: f2.
destruct f as [f1 f2].
split.
  exact: f1.
apply: H.
exact: f2.
Show Proof.
Abort.

Fixpoint weaken3 (l1 l2 : ctx) x (f : @mctx R (l1 ++ x :: l2)) : @mctx R (l1 ++ l2) :=
  match l1 as l return (mctx (l ++ x :: l2) -> mctx (l ++ l2)) with
  | [::] => fun f0 : mctx ([::] ++ x :: l2) => let (a, b) := f0 in (fun=> id) a b
  | a :: l => uncurry (fun a b => (a, @weaken3 l l2 x b))
  end f.

Definition weaken2 : forall (l1 l2 : ctx) x t (f : dval R (l1 ++ l2) t), dval R (l1 ++ x :: l2) t.
intros l1 l2 x t f z.
apply f.
exact: weaken3 z.
Defined.

Lemma mweaken3_helper (g : string * typ) (l1 : seq (string * typ))
  (ih : forall l2 x, measurable_fun setT (@weaken3 l1 l2 x))
  (l2 : ctx) (x : string * typ) :
  measurable_fun (T:=mctx (g :: l1 ++ x :: l2))
    setT (uncurry (fun a b => (a, @weaken3 l1 l2 x b))).
Proof.
apply/prod_measurable_funP; split.
  rewrite [X in measurable_fun _ X](_ : _ = fst)//.
  apply/funext => z /=.
  rewrite /uncurry.
  by destruct z.
rewrite [X in measurable_fun _ X](_ : _ = @weaken3 l1 l2 x \o snd)//; last first.
  apply/funext => z/=.
  rewrite /uncurry.
  by destruct z.
exact: measurableT_comp.
Qed.

Lemma mweaken3 (l1 l2 : ctx) x :
  measurable_fun (T:=mctx (l1 ++ x :: l2)) setT (@weaken3 l1 l2 x).
Proof.
elim: l1 l2 x => [l2 x|g l1 ih l2 x].
  exact: measurable_snd.
exact: mweaken3_helper.
Qed.

Lemma mweaken2 (l1 l2 : ctx) x t (f : dval R (l1 ++ l2) t)
  (mf : measurable_fun setT f) : measurable_fun setT (@weaken2 l1 l2 x t f).
Proof.
apply: measurableT_comp.
  exact: mf.
exact: mweaken3.
Qed.

(*Definition weaken2 : forall (l1 l2 : ctx) x t (f : dval R (l1 ++ l2) t), dval R (l1 ++ x :: l2) t.
fix H 1.
intros l1 l2 x t f.
destruct l1 as [|h1 l1].
  exact (f \o snd).
intros [u1 u2].
refine (H _ _ _ _ _ u2).
intros H1.
refine (f _).
exact (u1, H1).
Abort.

Fixpoint weaken2 (l1 l2 : ctx) x t (f : dval R (l1 ++ l2) t) : dval R (l1 ++ x :: l2) t :=
  match l1 as l return (dval R (l ++ l2) t -> dval R (l ++ x :: l2) t) with
   | [::] => fun f0 : dval R ([::] ++ l2) t => f0 \o snd
   | a :: l => fun f0 : dval R ((a :: l) ++ l2) t =>
  uncurry (fun u1 => @weaken2 l l2 x t ((fun H1 => f0 (u1, H1))))
   end f.

Lemma mweaken2 (l1 l2 : ctx) x t (f : dval R (l1 ++ l2) t)
  (mf : measurable_fun setT f) : measurable_fun setT (@weaken2 l1 l2 x t f).
Proof.
elim: l1 l2 x t f mf => /= [l2 x t f mf|[a1 a2] l1 ih l2 [x1 x2] t f mf].
  exact: measurableT_comp.

Admitted.*)

Definition kweaken2 l1 l2 (x : string * typ) t (k : R.-sfker (@mctx R (l1 ++ l2)) ~> @mtyp R t)
  : @mctx R (l1 ++ x :: l2) -> {measure set @mtyp R t -> \bar R} :=
fun z => k (@weaken3 l1 l2 x z).

Section kernel_weaken2.
Context l1 l2 (x : string * typ) t (k : pval R (l1 ++ l2) t).

Let mk U : measurable U -> measurable_fun setT ((@kweaken2 l1 l2 x t k) ^~ U).
Proof.
move=> mU.
rewrite (_ : kweaken2 _ ^~ U = (k ^~U \o (@weaken3 l1 l2 x)))//.
apply: measurableT_comp => //.
  exact: measurable_kernel.
exact: mweaken3.
Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ _ (@kweaken2 l1 l2 x t k) mk.
End kernel_weaken2.

Section sfkernel.
Context l1 l2 (x : string * typ) t (k : pval R (l1 ++ l2) t).

Let sk : exists2 s : (R.-ker @mctx R (l1 ++ x :: l2) ~> @mtyp R t)^nat,
  forall n, measure_fam_uub (s n) &
  forall x0 U, measurable U -> (@kweaken2 l1 l2 x t k) x0 U = kseries s x0 U .
Proof.
have [s hs] := sfinite_kernel k.
exists (fun n => [the _.-ker _ ~> _ of @kweaken2 l1 l2 x t (s n)]).
  move=> n.
  have [M hM] := measure_uub (s n).
  exists M => x0.
  exact: hM.
move=> x0 U mU.
by rewrite /kweaken2/= hs.
Qed.

HB.instance Definition _ :=
  Kernel_isSFinite_subdef.Build _ _ _ _ _ (@kweaken2 l1 l2 x t k) sk.

End sfkernel.

Section fkernel_weaken.
Context l1 l2 (x : string * typ) t (k : R.-fker @mctx R (l1 ++ l2) ~> @mtyp R t).

Let uub : measure_fam_uub (@kweaken2 l1 l2 x t k).
Proof.
have [M hM] := measure_uub k.
exists M => x0.
exact: hM.
Qed.

HB.instance Definition _ := @Kernel_isFinite.Build _ _ _ _ _
  (@kweaken2 l1 l2 x t k) uub.
End fkernel_weaken.

End kweaken2.

Lemma eq_probability R d (Y : measurableType d) (m1 m2 : probability Y R) :
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

Section eval.
Variables (R : realType).

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
  | expWD _ _ _ x e _ => rem x.1 (free_varsD e)
  end
with free_varsP T l (e : expP T l) : seq _ :=
  match e with
  | exp_if _ _ e1 e2 e3     => free_varsD e1 ++ free_varsP e2 ++ free_varsP e3
  | exp_letin _ _ _ x e1 e2 => free_varsP e1 ++ rem x (free_varsP e2)
  | exp_sample _ _ _ => [::]
(*  | exp_sample_bern _ _ _   => [::]*)
  | exp_score _ e           => free_varsD e
  | exp_return _ _ e        => free_varsD e
  | expWP _ _ _ x e _ => rem x.1 (free_varsP e)
  end.

Definition mtyps l := projT2 (@measurable_of_seq R l).

Definition mval (R : realType) (l : seq typ) (t : typ) :=
  @mtyps l -> @mtyp R t.

Definition acc_typ : forall (l : seq typ) (i : nat),
  projT2 (@measurable_of_seq R l) ->
  projT2 (@measurable_of_typ R (nth Unit l i)).
fix H 1.
intros l i x.
destruct l as [|l].
  destruct i as [|i].
    exact tt.
  exact tt.
destruct i as [|i].
  exact (fst x).
rewrite /=.
apply H.
exact: (snd x).
Defined.

Lemma macc_typ (l : seq typ) (i : nat) : measurable_fun setT (@acc_typ l i).
Proof.
elim: l i => //= h t ih [|j].
  exact: measurable_fst.
apply: (measurableT_comp (ih _)).
exact: measurable_fun_snd.
Qed.
Local Open Scope seq_scope.
Inductive evalD : forall l t (e : @expD R l t)
  (f : mval R (map snd l) t), measurable_fun setT f -> Prop :=
| EV_unit l :
  l # exp_unit -D-> cst tt ; ktt

| EV_bool l b :
  l # exp_bool b -D-> cst b ; kb b

| EV_real l r :
  l # [r :r] -D-> cst r ; kr r

| EV_pair l t1 t2 e1 f1 mf1 e2 f2 mf2 :
  l # e1 -D-> f1 ; mf1 ->
  l # e2 -D-> f2 ; mf2 ->
  l # [(e1, e2)] -D-> fun x => (f1 x, f2 x) ;
  @measurable_fun_prod _ _ _ (mctx l) (mtyp t1) (mtyp t2) f1 f2 mf1 mf2

| EV_var (l : ctx) (x : string) :
  let i := seq.index x (map fst l) in
  l # [% x] -D-> @acc_typ (map snd l) i ;
                 (@macc_typ (map snd l) i)

| EV_bernoulli l (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
  l # exp_bernoulli r r1 -D->
  cst [the probability _ _ of bernoulli r1] ; measurable_cst _

| EV_poisson l k e f mf :
  l # e -D-> f ; mf ->
  l # exp_poisson k e -D-> poisson k \o f ;
  measurableT_comp (mpoisson k) mf

| EV_norm l t (e : expP l t) k :
  l # e -P-> k ->
  l # exp_norm e -D-> (normalize k point : _ -> pprobability _ _) ;
  measurable_fun_mnormalize k

| EV_WeakD l1 l2 t (e : expD (l1 ++ l2) t) x (xl : x.1 \notin map fst (l1 ++ l2)) f mf :
  (l1 ++ l2) # e -D-> f ; mf ->
  (l1 ++ x :: l2)%SEQ # expWD e xl -D-> (@weaken2 R l1 l2 x t f) ; (@mweaken2 R l1 l2 x t f mf)

where "l # e -D-> v ; mv" := (@evalD l _ e v mv)

with evalP : forall l t, expP l t ->
  pval R l t -> Prop :=

| EV_sample l t (e : expD l (Prob t)) (p : mctx l -> pprobability (mtyp t) R)
  mp :
  l # e -D-> p ; mp ->
  l # @exp_sample R l _ e -P-> sample p mp

(* | EV_sample_bern l (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
  l # exp_bernoulli r r1 -D-> cst (@bernoulli R r r1) ; (measurable_cst _) ->
  l # exp_sample (exp_bernoulli r r1) -P-> sample_cst (bernoulli r1) *)
  (* l # @exp_sample_bern R _ r r1 -P->
  sample_cst [the probability _ _ of bernoulli r1] *)

| EV_ifP l T e1 f1 mf e2 k2 e3 k3 :
  l # e1 -D-> f1 ; mf ->
  l # e2 -P-> k2 ->
  l # e3 -P-> k3 ->
  l # [If e1 Then e2 Else e3] : expP l T -P-> ite mf k2 k3

| EV_score l e (f : mctx l -> R)
  (mf : measurable_fun _ f) :
  l # e : expD l Real -D-> f ; mf ->
  l # exp_score e -P-> [the R.-sfker _ ~> _ of kscore mf]

| EV_return l T e (f : _ -> _) (mf : measurable_fun _ f) :
  l # e -D-> f ; mf ->
  l # [Ret e] : expP l T -P-> ret mf

| EV_letin l t1 t2
  (x : string) (e1 : expP l t1) (e2 : expP ((x, t1) :: l) t2)
  (k1 : R.-sfker (mctx l) ~> mtyp t1)
  (k2 : R.-sfker (mctx ((x, t1) :: l)) ~> mtyp t2) :
  l # e1 -P-> k1 ->
  ((x, t1) :: l)%SEQ # e2 -P-> k2 ->
  l # [Let x <~ e1 In e2] -P-> letin' k1 k2

| EV_WeakP l1 l2 t (e : expP (l1 ++ l2) t) x (xl : x.1 \notin map fst (l1 ++ l2)) k :
  (l1 ++ l2) # e -P-> k ->
  (l1 ++ x :: l2) # expWP e xl -P-> [the R.-sfker _ ~> _ of @kweaken2 R l1 l2 x t k]
where "l # e -P-> v" := (@evalP l _ e v).

Example ex1 := (exp_sample (exp_bernoulli _ p27)) : @expP R [::] _.

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
Variables (R : realType).

Local Ltac inj := let H := fresh in intros H; injection H; clear H; auto.

Lemma inj_cst x y : @exp_real R [::] x = exp_real y -> x = y.
Proof.
inj.
Qed.

Lemma sample_sample_cst  dX dY (X : measurableType dX) (Y : measurableType dY) p : @sample_cst dX _ X _ R p = @sample _ dY _ Y R (@cst X _ p) (measurable_cst p).
Proof.
Abort.

Lemma __ dX dY (X : measurableType dX) Y x y : @cst X _ x = cst y -> @sample_cst dX dY X Y R x = sample_cst y.
Proof.
Abort.

Lemma evalD_uniq l t
  (e : @expD R l t) (u v : dval R l t)
  (mu : measurable_fun setT u) (mv : measurable_fun setT v) :
  l # e -D-> u ; mu -> l # e -D-> v ; mv -> u = v.
Proof.
move=> hu.
apply: (@evalD_mut_ind R
  (fun l t (e : expD l t) (f : dval R l t)
  (mf : measurable_fun setT f) (h1 : evalD e mf) =>
    forall (v : dval R l t) (mv : measurable_fun setT v),
    evalD e mv -> f = v)
  (fun l t (e : expP l t)
    (u : R.-sfker mctx l ~> mtyp t) (h1 : evalP e u) =>
    forall (v : R.-sfker mctx l ~> mtyp t), evalP e v -> u = v)); last exact: hu.
all: (rewrite {l t e u v mu mv hu}).
- move=> l {}v {}mv.
  inversion 1; subst l0.
  by inj_ex H3.
- move=> l b {}v {}mv.
  inversion 1; subst l0 b0.
  by inj_ex H3.
- move=> l r {}v {}mv.
  inversion 1; subst l0 r0.
  by inj_ex H3.
- move=> l t1 t2 e1 f1 mf1 e2 f2 mf2 ev1 IH1 ev2 IH2 {}v {}mv.
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
- move=> l1 l2 t e0 x xl f mf ev IH {}v {}mv.
  inversion 1.
  subst t0 l0 l3 x0.
  inj_ex H9.
  inj_ex H11.
  inj_ex H7.
  subst e0.
  by rewrite (IH _ _ H3).
- move=> l t e0 p mp ev IH k.
  simple inversion 1 => //; subst.
  inj_ex H4; subst.
  inj_ex H3; subst.
  case: H3 => H3; inj_ex H3; subst e0 => ev1.
  have Hp := IH _ _ ev1.
  subst p0.
  by have -> : mp = mp0 by exact: Prop_irrelevance.
- move=> l t e0 f1 mf1 e2 k2 e3 k3 ev1 IH1 ev2 IH2 ev3 IH3 k.
  inversion 1; subst l0 T.
  inj_ex H0; subst e0.
  inj_ex H1; subst e4.
  inj_ex H5; subst k.
  inj_ex H2; subst e5.
  have ? := IH1 _ _ H6; subst f2.
  have -> : mf1 = mf by exact: Prop_irrelevance.
  by rewrite (IH2 _ H7) (IH3 _ H8).
- move=> l e0 f mf ev IH k.
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
- move=> l t1 t2 x e1 e2 k1 k2 ev1 IH1 ev2 IH2 k.
  inversion 1; subst l0 t0 t3 x0.
  inj_ex H7; subst k.
  inj_ex H6; subst e5.
  inj_ex H5; subst e4.
  by rewrite (IH1 _ H4) (IH2 _ H8).
- move=> l1 l2 t e0 x xl k1 ev IH {}k.
  inversion 1; subst x0 t0 l0 l3.
  inj_ex H9.
  inj_ex H7; subst e0.
  rewrite /=.
  by rewrite (IH _ H3).
Qed.

Lemma evalP_uniq l t (e : expP l t)
  (u v : R.-sfker mctx l ~> mtyp t) :
  evalP e u -> evalP e v -> u = v.
Proof.
move=> hu.
apply: (@evalP_mut_ind R
  (fun l t (e : expD l t) (f : dval R l t)
    (mf : measurable_fun setT f) (h1 : evalD e mf) =>
    forall (v : dval R l t) (mv : measurable_fun setT v), evalD e mv -> f = v)
  (fun l t (e : expP l t)
    (u : R.-sfker mctx l ~> mtyp t) (h1 : evalP e u) =>
    forall (v : R.-sfker mctx l ~> mtyp t), evalP e v -> u = v)); last exact: hu.
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
- move=> l t1 t2 e1 f1 mf1 e2 f2 mf2 ev1 IH1 ev2 IH2 {}v {}mv.
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
- move=> l1 l2 t e x xl f mf ev IH {}v {}mv.
  inversion 1; subst x0 l0 l3 t0.
  inj_ex H7; subst e1.
  inj_ex H9.
  inj_ex H11.
  by rewrite (IH _ _ H3).
- move=> l t e p mp ep IH v.
  inversion 1; subst l0 t0.
  inj_ex H7; subst v.
  inj_ex H5; subst e1.
  have ? := IH _ _ H3; subst p1.
  by have -> : mp = mp1 by apply: Prop_irrelevance.
- move=> l t e f mf e1 k1 e2 k2 ev IH ev1 IH1 ev2 IH2 k.
  inversion 1; subst l0 T.
  inj_ex H0; subst e0.
  inj_ex H1; subst e3.
  inj_ex H5; subst k.
  inj_ex H2; subst e4.
  have ? := IH _ _ H6; subst f0.
  have -> : mf0 = mf by exact: Prop_irrelevance.
  by rewrite (IH1 _ H7) (IH2 _ H8).
- move=> l e f mf ev IH k.
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
- move=> l t1 t2 x e1 e2 k1 k2 ev1 IH1 ev2 IH2 k.
  inversion 1; subst l0 x0 t3 t0.
  inj_ex H7; subst k.
  inj_ex H5; subst e4.
  inj_ex H6; subst e5.
  by rewrite (IH1 _ H4) (IH2 _ H8).
- move=> l1 l2 t e x xl k1 ev IH {}k.
  inversion 1; subst x0 t0 l0 l3.
  inj_ex H9.
  inj_ex H7; subst e1.
  rewrite /=.
  by rewrite (IH _ H3).
Qed.

Lemma evalD_full l t (e : expD l t) :
  exists f (mf : measurable_fun _ f), @evalD R l t e f mf.
Proof.
apply: (@expD_mut_ind R
  (fun l t (e : expD l t) => exists f (mf : measurable_fun setT f), evalD e mf)
  (fun l t (e : expP l t) => exists k, evalP e k)).
all: rewrite {l t e}.
- move=> l1 l2 st x e [f [mf fmf]] xl.
  by exists (weaken2 f), (mweaken2 mf); exact/EV_WeakD.
- by do 2 eexists; exact: EV_unit.
- by do 2 eexists; exact: EV_bool.
- by do 2 eexists; exact: EV_real.
- move=> l t1 t2 e1 [f1 [mf1 H1]] e2 [f2 [mf2 H2]].
  by exists (fun x => (f1 x, f2 x)); eexists; exact: EV_pair.
- by move=> l x t tE; subst t; eexists; eexists; exact: EV_var.
- by move=> r r1; eexists; eexists; exact: EV_bernoulli.
- move=> l k e [f [mf H]].
  exists (poisson k \o f), (measurableT_comp (mpoisson k) mf).
  exact: EV_poisson.
- move=> l t e [k H].
  by exists (normalize k point), (measurable_fun_mnormalize k); exact: EV_norm.
- move=> l1 l2 st x e [k H1] xl.
  by exists [the _.-sfker _ ~> _ of kweaken2 k]; exact: EV_WeakP.
- move=> l t e1 [f [mf H1]] e2 [k2 H2] e3 [k3 H3].
  by exists (ite mf k2 k3); exact: EV_ifP.
- move=> l t1 t2 x e1 [k1 ev1] e2 [k2 ev2].
  by exists (letin' k1 k2); exact: EV_letin.
- move=> l t e [f [/= mf ef]].
  eexists.
  apply: EV_sample.
    exact: mf.
  move=> mf'.
  by have <- : mf = mf' by exact: Prop_irrelevance.
(*- move=> l r r1.
  by exists (sample_cst [the pprobability _ _ of bernoulli r1]); exact: EV_sample.*)
- move=> l e [f [mf f_mf]].
  by exists (score mf); exact: EV_score.
- by move=> l t e [f [mf f_mf]]; exists (ret mf); exact: EV_return.
Qed.

Lemma evalP_full l t (e : expP l t) :
  exists (k : R.-sfker _ ~> _), @evalP R l t e k.
Proof.
apply: (@expP_mut_ind R
  (fun l t (e : expD l t) => exists f (mf : measurable_fun _ f), evalD e mf)
  (fun l t (e : expP l t) => exists k, evalP e k)).
all: rewrite {l t e}.
- move=> l1 l2 t x e [f [mf H]] xl.
  by exists (weaken2 f), (mweaken2 mf); exact: EV_WeakD.
- by do 2 eexists; exact: EV_unit.
- by do 2 eexists; exact: EV_bool.
- by do 2 eexists; exact: EV_real.
- move=> l t1 t2 e1 [f1 [mf1 H1]] e2 [f2 [mf2 H2]].
  by exists (fun x => (f1 x, f2 x)); eexists; exact: EV_pair.
- by move=> l x t tE; subst t; eexists; eexists; exact: EV_var.
- by move=> r r1; eexists; eexists; exact: EV_bernoulli.
- move=> l k e [f [mf H]].
  exists (poisson k \o f), (measurableT_comp (mpoisson k) mf).
  exact: EV_poisson.
- move=> l t e []k H.
  by exists (normalize k point), (measurable_fun_mnormalize k); exact: EV_norm.
- move=> l1 l2 s x e [k H1] xl.
  by exists [the _.-sfker _ ~> _ of kweaken2 k]; exact: EV_WeakP.
- move=> l t e1 [f [mf H1]] e2 [k2 H2] e3 [k3 H3].
  by exists (ite mf k2 k3); exact: EV_ifP.
- move=> l t1 t2 x e1 [k1 ev1] e2 [k2 ev2].
  by exists (letin' k1 k2); exact: EV_letin.
- move=> l t e [f [mf ef]].
  eexists.
  apply: EV_sample.
    exact: mf.
  move=> mf'.
  by have <- : mf = mf' by exact: Prop_irrelevance.
- by move=> l e [f [mf H]]; exists (score mf); exact: EV_score.
- by move=> l t e [f [mf H]]; exists (ret mf); exact: EV_return.
Qed.

Definition execP l t (e : @expP R l t) :
  R.-sfker @mctx R l ~> @mtyp R t.
Proof.
have /cid h := @evalP_full l t e.
exact: (proj1_sig h).
Defined.

Lemma evalP_execP l t e : l # e -P-> @execP l t e.
Proof. by rewrite /execP/= /sval ?/ssr_have/=; case: cid. Qed.

Definition execD l t (e : @expD R l t) :
  {f : dval R l t & measurable_fun setT f}.
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

Definition execP_ret_real (l : ctx) (r : R) :
    R.-sfker @mctx R l ~> @mtyp R Real :=
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

Lemma execD_poisson l k (e : expD l Real) :
  execD (exp_poisson k e) = existT _ (poisson k \o (projT1 (execD e)))
  (measurableT_comp (mpoisson k) (projT2 (execD e))).
Proof.
rewrite /execD /=.
case: cid => f ?.
case: cid => mf ev1.
have IHev : (l # e -D-> projT1 (execD e); projT2 (execD e)).
exact/evalD_execD.
have ev2 := (EV_poisson k IHev).
have ? := (evalD_uniq ev1 ev2).
subst.
congr existT.
exact/Prop_irrelevance.
Qed.

Lemma execP_WP_kweaken l1 l2 x t (e : expP (l1 ++ l2)%SEQ t) (xl : x.1 \notin map fst (l1 ++ l2)) :
  execP (@expWP R l1 l2 t _ e xl) = [the _.-sfker _ ~> _ of kweaken2 (execP e)].
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

Lemma execP_sample_bern l r r1 :
  execP (exp_sample (@exp_bernoulli R l r r1)) = sample_cst (bernoulli r1).
Proof.
apply: evalP_uniq; first exact/evalP_execP.
apply: EV_sample => /=.
exact: EV_bernoulli.
Qed.

Lemma execP_score l (e : @expD R l Real) : execP (exp_score e) = score (projT2 (execD e)).
Proof.
apply: evalP_uniq; first exact/evalP_execP.
exact/EV_score/evalD_execD.
Qed.

Lemma execP_if l st e1 e2 e3 : @execP l st [If e1 Then e2 Else e3] = ite (projT2 (execD e1)) (execP e2) (execP e3).
Proof.
apply/evalP_uniq; first exact/evalP_execP.
apply/EV_ifP.
exact/evalD_execD.
exact/evalP_execP.
exact/evalP_execP.
Qed.

Lemma execD_pair l (G := map snd l) t1 t2
  (x : @expD R l t1)
  (y : @expD R l t2) :
  let f := projT1 (execD x) in
  let g := projT1 (execD y) in
  let mf := projT2 (execD x) in
  let mg := projT2 (execD y) in
  execD [(x, y)] =
  @existT _ _ (fun z => (f z, g z))
  (@measurable_fun_prod _ _ _ (mctx l) (mtyp t1) (mtyp t2)
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

Lemma execD_var (l : ctx) (x : string) :
  let i := seq.index x (map fst l) in
  @execD l _ [% {x} ] = existT _ (@acc_typ R (map snd l) i) (@macc_typ R (map snd l) i).
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

Structure tagged_context := Tag {untag : ctx}.

Definition recurse_tag h := Tag h.
Canonical found_tag h := recurse_tag h.

Structure find (s : string) (t : typ) := Find {
  context_of : tagged_context ;
  ctxt_prf : t = nth Unit (map snd (untag context_of))
                           (seq.index s (map fst (untag context_of)))}.

Lemma left_pf (s : string) (t : typ) (l : ctx) :
  t = nth Unit (map snd ((s, t) :: l)) (seq.index s (map fst ((s, t) :: l))).
Proof.
by rewrite /= !eqxx/=.
Qed.

Canonical found_struct s t (l : ctx) : find s t :=
  Eval hnf in @Find s t (found_tag ((s, t) :: l)) (@left_pf s t l).

Lemma right_pf (s : string) (t : typ) (l : ctx) u t' :
  s != u ->
  t' = nth Unit (map snd l) (seq.index u (map fst l)) ->
  t' = nth Unit (map snd ((s, t) :: l)) (seq.index u (map fst ((s, t) :: l))).
Proof.
move=> su ut'l /=.
case: ifPn => //=.
by rewrite (negbTE su).
Qed.

Canonical recurse_struct s t t' u {su : infer (s != u)} (l : find u t') : find u t' :=
  Eval hnf in @Find u t' (recurse_tag ((s, t) :: untag (context_of l)))
  (@right_pf s t (untag (context_of l)) u t' su (ctxt_prf l)).

Definition exp_var' (x : string) (t : typ) (g : find x t) :=
  @exp_var R (untag (context_of g)) x t (ctxt_prf g).

Notation "%1 x" := (@exp_var' x%string _ _) (in custom expr at level 1).

(* Lemma execD_var' l t (x : string) i :
  i = seq.index x (map fst l) ->
  @execD R ((x, t) :: l) t (exp_var x (left_pf x _ l)) = execD [% x].
Proof. congr execD; congr exp_var; exact: Prop_irrelevance. Qed. *)

Example e3 := [Let "x" <~ Ret {1%:R}:r In
               Let "y" <~ Ret %1{"x"} In
               Let "z" <~ Ret %1{"y"} In Ret %1{"z"}] : expP [::] _.

Example staton_bus_exp := exp_norm (
  [Let "x" <~ {exp_sample (@exp_bernoulli _ [::] (2 / 7%:R)%:nng p27)} In
   Let "r" <~ If %1{"x"} Then Ret {3}:r Else Ret {10}:r In
   Let "_" <~ {exp_score (exp_poisson 4 [%1{"r"}])} In
   Ret %1{"x"}]).

Definition sample_bern : R.-sfker munit ~> mbool :=
  sample_cst [the probability _ _ of bernoulli p27].
Definition ite_3_10 :
  R.-sfker [the measurableType _ of (mbool * munit)%type] ~> (mR R) :=
  ite (@macc0of2 _ _ _ _) (ret k3) (ret k10).
Definition score_poi :
  R.-sfker [the measurableType _ of (mR R * (mbool * munit))%type] ~> munit :=
  score (measurableT_comp (mpoisson 4) (@macc0of2 _ _ _ _)).

Example kstaton_bus_exp : expP [::] Bool :=
  [Let "x" <~ {exp_sample (@exp_bernoulli R [::] (2 / 7%:R)%:nng p27)} In
   Let "r" <~ If %1{"x"} Then Ret {3}:r Else Ret {10}:r In
   Let "_" <~ {exp_score (exp_poisson 4 [%1{"r"}])} In
   Ret %{"x"}].

Local Definition kstaton_bus'' :=
  letin' sample_bern
    (letin' ite_3_10
      (letin' score_poi (ret (@macc2of4' _ _ _ _ _ _ _ _)))).

Example eval_staton_bus :
  [::] # kstaton_bus_exp -P-> kstaton_bus''.
Proof.
apply/EV_letin.
  apply: EV_sample.
  exact: EV_bernoulli.
apply/EV_letin.
  apply/EV_ifP/EV_return/EV_real/EV_return/EV_real.
  rewrite/exp_var'/=.
  have /= := (EV_var R [:: ("x", Bool)] "x").
  have <- : ([% {"x"}] = @exp_var R _ "x" _ (left_pf "x" Bool [::])).
    congr exp_var; exact: Prop_irrelevance.
  congr evalD; exact: Prop_irrelevance.
apply/EV_letin.
  apply/EV_score.
  apply/EV_poisson.
  rewrite/exp_var'/=.
  have /= := (EV_var R [:: ("r", Real); ("x", Bool)] "r").
  have <- : ([% {"r"}] = @exp_var R _ "r" _ (left_pf "r" Real [:: ("x", Bool)])).
    congr exp_var; exact: Prop_irrelevance.
  congr evalD; exact: Prop_irrelevance.
apply/EV_return.
have /= := (EV_var R [:: ("_", Unit); ("r", Real); ("x", Bool)] "x").
rewrite/acc2of4'/comp/=.
congr evalD; exact: Prop_irrelevance.
Qed.

Example exec_staton_bus :
  execP kstaton_bus_exp = kstaton_bus''.
Proof.
rewrite /kstaton_bus''.
rewrite 3!execP_letin execP_sample_bern.
congr letin'.
rewrite !execP_if !execP_ret !execD_real.
have -> : @execD R _ _ (exp_var "x" (left_pf "x" Bool [::])) = execD [% {"x"}].
congr execD; congr exp_var; exact: Prop_irrelevance.
rewrite execD_var /= /ite_3_10.
have -> : (@macc_typ R [:: Bool] 0 = @macc0of2 _ _ _ _) by [].
congr letin'.
rewrite execP_score execD_poisson /=.
have -> : (@execD R _ _ (exp_var "r" (left_pf "r" Real [:: ("x", Bool)])) = execD [% {"r"}]).
congr execD; congr exp_var; exact: Prop_irrelevance.
rewrite execD_var /=.
have ->/= : (@macc_typ R [:: Real; Bool] 0 = @macc0of2 _ _ _ _) by [].
congr letin'.
rewrite (execD_var _ _ "x") /=.
by have -> : (@macc_typ _ [:: Unit; Real; Bool] 2 = @macc2of4' _ _ _ _ _ _ _ _).
Qed.

End staton_bus.

Section letinC.
Local Open Scope lang_scope.
Variable R : realType.

Lemma ex_var_ret l : @execP R l _ [Let "x" <~ Ret {1}:r In Ret %{"x"}] = letin' (ret (kr 1)) (ret (@macc0of2 _ _ _ _)).
Proof.
rewrite execP_letin; congr letin'.
by rewrite execP_ret execD_real.
by rewrite execP_ret execD_var; congr ret.
Qed.

Lemma LetInC l t1 t2 (e1 : @expP R l t1) (e2 : expP l t2)
  (xl : "x" \notin map fst l) (yl : "y" \notin map fst l) :
  forall U, measurable U ->
  execP [Let "x" <~ e1 In
        Let "y" <~ {@expWP _ [::] _ _ ("x", t1) e2 xl} In
        Ret (%{"x"}, %{"y"})] ^~ U =
  execP [Let "y" <~ e2 In
        Let "x" <~ {@expWP _ [::] _ _ ("y", t2) e1 yl} In
        Ret (%{"x"}, %{"y"})] ^~ U.
        (* :> (mtyp (slist (map snd l)) -> \bar R). *)
Proof.
move=> U mU; apply/funext => x.
rewrite 4!execP_letin.
rewrite (@execP_WP_kweaken _ [::] l).
rewrite (@execP_WP_kweaken _ [::] l).
rewrite 2!execP_ret/=.
rewrite 2!execD_pair/=.
rewrite !(execD_var _ _ "x")/= !(execD_var _ _ "y")/=.
have -> : @macc_typ _ [:: t2, t1 & [seq i.2 | i <- l]] 0 = @macc0of3' _ _ _ _ _ _ by [].
have -> : @macc_typ _ [:: t2, t1 & [seq i.2 | i <- l]] 1 = @macc1of3' _ _ _ _ _ _ by [].
rewrite (letin'C _ _ (execP e2) [the R.-sfker _ ~> _ of @kweaken2 _ [::] _ ("y", t2) _ (execP e1)]); [ |by [] | by [] |by []].
have -> : @macc_typ _ [:: t1, t2 & [seq i.2 | i <- l]] 0 = @macc0of3' _ _ _ _ _ _ by [].
have -> : @macc_typ _ [:: t1, t2 & [seq i.2 | i <- l]] 1 = @macc1of3' _ _ _ _ _ _ by [].
reflexivity.
Qed.

Lemma LetInC_test (l := [:: ("a", Unit); ("b", Bool)]) t1 t2
    (e1 : @expP R l t1)
    (e2 : expP l t2) :
  forall U, measurable U ->
  execP [Let "x" <~ e1 In
         Let "y" <~ e2 \U {"x"} In
         Ret (%{"x"}, %{"y"})] ^~ U =
  execP [Let "y" <~ e2 In
         Let "x" <~ e1 \U {"y"} In
         Ret (%{"x"}, %{"y"})] ^~ U.
Proof.
move=> U mU.
exact: LetInC.
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
apply: funext=> x.
rewrite !execP_letin !execP_ret !execD_real !execD_pair.
rewrite (execD_var _ _ "x")/= (execD_var _ _ "y")/=.
(* TODO: Use LetInC *)
Abort.

Lemma LetInA l t1 t2 t3
  (e1 : @expP R l t1)
  (e2 : expP [:: ("y", t1) & l] t2)
  (e3 : expP [:: ("x", t2) & l] t3)
  (xl : "x" \notin map fst l)
  (yl : "y" \notin map fst [:: ("x", t2) & l]) :
  forall U, measurable U ->
  execP [Let "y" <~ e1 In
         Let "x" <~ e2 In
         {(@expWP _ [:: ("x", t2)] l _ ("y", t1) e3 yl)}] ^~ U =
  execP [Let "x" <~ Let "y" <~ e1 In e2 In
         e3] ^~ U.
Proof.
move=> U mU; apply/funext=> x.
rewrite !execP_letin.
rewrite (@execP_WP_kweaken _ [:: ("x", t2)]).
apply: letin'A => //.
move=> y z.
rewrite /=.
rewrite /kweaken2 /weaken3 /=.
by destruct z.
Qed.

Example LetInA12 : forall U, measurable U ->
  @execP R [::] _ [Let "y" <~ Ret {1}:r In
         Let "x" <~ Ret {2}:r In Ret %{"x"}] ^~ U =
  @execP R [::] _ [Let "x" <~ Let "y" <~ Ret {1}:r In Ret {2}:r In
         Ret %{"x"}] ^~ U.
Proof.
move=> U mU.
rewrite !execP_letin !execP_ret !execD_real !execD_var /=.
apply: funext=> x.
exact: letin'A.
(* TODO: Use LetInA *)
Qed.

End letinC.
