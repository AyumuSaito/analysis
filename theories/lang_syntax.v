Require Import String ZArith.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp.classical Require Import mathcomp_extra boolp classical_sets.
From mathcomp.classical Require Import functions cardinality fsbigop.
Require Import signed reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure numfun lebesgue_integral kernel prob_lang.
Require Import inj_ex.

(******************************************************************************)
(*       Syntax and Evaluation for a probabilistic programming language       *)
(*                                                                            *)
(*                 typ == syntax for types of data structures                 *)
(*              mtyp t == the measurable type corresponding to the type t,    *)
(*                        i.e., the semantics of t                            *)
(*                 ctx == type of context                                     *)
(*                     := seq (string * type)                                 *)
(*              mctx l := the measurable type corresponding to the context l  *)
(*                        It is formed of nested pairings of measurable       *)
(*                        spaces.                                             *)
(*            expD l t == syntax of deterministic terms of type t in context l*)
(*            expP l t == syntax of probabilistic terms                       *)
(*   l # e -D-> f ; mf == the evaluation of the deterministic expression e    *)
(*                        in the context l leads to the measurable function f *)
(*                        (mf is the proof that v is measurable)              *)
(*        l # e -P-> k == the evaluation of the probabilistic function f in   *)
(*                        the context l leads to the s-finite kernel k        *)
(*             execD e == a dependent pair of a function corresponding to the *)
(*                        evaluation of e and a proof that this function is   *)
(*                        measurable                                          *)
(*             execP e == a s-finite kernel corresponding to the evaluation   *)
(*                        of the probabilistic expression e                   *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

(* TODO: move *)
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

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Declare Scope lang_scope.

Reserved Notation "l # e -D-> f ; mf" (at level 40).
Reserved Notation "l # e -P-> k" (at level 40).

Declare Scope prob_lang_scope.
Delimit Scope prob_lang_scope with P.

Section syntax_of_types.
Import Notations.
Context {R : realType}.

Inductive typ :=
| Unit | Bool | Real
| Pair : typ -> typ -> typ
| Prob : typ -> typ.

Local Notation "( x , y , .. , z )" :=
  (Pair .. (Pair x y) .. z) : prob_lang_scope.

Canonical stype_eqType := Equality.Pack (@gen_eqMixin typ).

Fixpoint measurable_of_typ (t : typ) : {d & measurableType d} :=
  match t with
  | Unit => existT _ _ munit
  | Bool => existT _ _ mbool
  | Real => existT _ _ (mR R)
  | (A, B)%P => existT _ _
      [the measurableType (projT1 (measurable_of_typ A),
                           projT1 (measurable_of_typ B)).-prod%mdisp of
      (projT2 (measurable_of_typ A) *
       projT2 (measurable_of_typ B))%type]
  | Prob A => existT _ _ (pprobability (projT2 (measurable_of_typ A)) R)
  end.

Definition mtyp t : measurableType (projT1 (measurable_of_typ t)) :=
  projT2 (measurable_of_typ t).

Definition measurable_of_seq (l : seq typ) : {d & measurableType d} :=
  iter_mprod (map measurable_of_typ l).

End syntax_of_types.
Arguments measurable_of_typ {R}.
Arguments mtyp {R}.
Arguments measurable_of_seq {R}.

Notation "( x , y , .. , z )" := (Pair .. (Pair x y) .. z) : prob_lang_scope.

Definition string_eqMixin := @EqMixin string String.eqb eqb_spec.
Canonical string_eqType := EqType string string_eqMixin.

Section context.
Variables (R : realType).
Definition ctx := seq (string * typ).

Definition mctx (l : ctx)
    : measurableType (projT1 (measurable_of_seq (map snd l))) :=
  projT2 (@measurable_of_seq R (map snd l)).

End context.
Arguments mctx {R}.

Section syntrax_of_expression.
Context {R : realType}.

Inductive expD : ctx -> typ -> Type :=
| exp_unit l : expD l Unit
| exp_bool l : bool -> expD l Bool
| exp_real l : R -> expD l Real
| exp_pair l t1 t2 : expD l t1 -> expD l t2 -> expD l (t1, t2)%P
| exp_var l x t : t = nth Unit (map snd l) (index x (map fst l)) ->
    expD l t
| exp_bernoulli l (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
    expD l (Prob Bool)
| exp_poisson l : nat -> expD l Real -> expD l Real
| exp_normalize l t : expP l t -> expD l (Prob t)
| expD_weak l k t x : expD (l ++ k) t -> x.1 \notin map fst (l ++ k) ->
    expD (l ++ x :: k) t
with expP : ctx -> typ -> Type :=
| exp_if l t : expD l Bool -> expP l t -> expP l t -> expP l t
| exp_letin l t1 t2 str : expP l t1 -> expP ((str, t1) :: l) t2 ->
    expP l t2
| exp_sample l t : expD l (Prob t) -> expP l t
| exp_score l : expD l Real -> expP l Unit
| exp_return l t : expD l t -> expP l t
| expP_weak l k t x : expP (l ++ k) t -> x.1 \notin map fst (l ++ k) ->
    expP (l ++ x :: k) t.

End syntrax_of_expression.

Arguments expD {R}.
Arguments exp_unit {R l}.
Arguments exp_bool {R l}.
Arguments exp_real {R l}.
Arguments exp_pair {R l t1 t2}.
Arguments exp_var {R l} _ {t}.
Arguments exp_bernoulli {R l}.
Arguments exp_poisson {R l}.
Arguments exp_normalize {R l _}.
Arguments expD_weak {R l k t x}.
Arguments expP {R}.
Arguments exp_if {R l t}.
Arguments exp_letin {R l _ _}.
Arguments exp_sample {R l t}.
Arguments exp_score {R l}.
Arguments exp_return {R l _}.
Arguments expP_weak {R l k t x}.

Declare Custom Entry expr.
Notation "[ e ]" := e (e custom expr at level 5) : lang_scope.
Notation "x ':r'" := (@exp_real _ _ x%R) (in custom expr at level 1)
  : lang_scope.
Notation "'Ret' x" := (@exp_return _ _ _ x) (in custom expr at level 2)
  : lang_scope.
Notation "% x" := (@exp_var _ _ x _ erefl) (in custom expr at level 1)
: lang_scope.
Notation "e \U x" := (@expP_weak _ [::] _ _ (x, _) e erefl)
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

Section free_vars.
Context {R : realType}.

Fixpoint free_varsD l t (e : @expD R l t) : seq string :=
  match e with
  | exp_unit _            => [::]
  | exp_bool _ _          => [::]
  | exp_real _ _          => [::]
  | exp_pair _ _ _ e1 e2  => free_varsD e1 ++ free_varsD e2
  | exp_var _ x _ _       => [:: x]
  | exp_bernoulli _ _ _   => [::]
  | exp_poisson _ _ e     => free_varsD e
  | exp_normalize _ _ e   => free_varsP e
  | expD_weak _ _ _ x e _ => rem x.1 (free_varsD e)
  end
with free_varsP T l (e : expP T l) : seq _ :=
  match e with
  | exp_if _ _ e1 e2 e3     => free_varsD e1 ++ free_varsP e2 ++ free_varsP e3
  | exp_letin _ _ _ x e1 e2 => free_varsP e1 ++ rem x (free_varsP e2)
  | exp_sample _ _ _        => [::]
  | exp_score _ e           => free_varsD e
  | exp_return _ _ e        => free_varsD e
  | expP_weak _ _ _ x e _   => rem x.1 (free_varsP e)
  end.

End free_vars.

Definition dval (R : realType) (l : ctx) (t : typ) :=
  @mctx R l -> @mtyp R t.
Definition pval (R : realType) (l : ctx) (t : typ) :=
  R.-sfker @mctx R l ~> @mtyp R t.

Section weak.
Context {R : realType}.
Local Open Scope seq_scope.
Implicit Types (l k : ctx) (x : string * typ).

Fixpoint mctx_strong l k x (f : @mctx R (l ++ x :: k)) : @mctx R (l ++ k) :=
  match l as l return mctx (l ++ x :: k) -> mctx (l ++ k) with
  | [::] => fun f0 : mctx ([::] ++ x :: k) => let (a, b) := f0 in (fun=> id) a b
  | a :: l => uncurry (fun a b => (a, @mctx_strong l k x b))
  end f.

Definition weak l k x t (f : dval R (l ++ k) t) : dval R (l ++ x :: k) t :=
  f \o @mctx_strong l k x.

Lemma measurable_fun_mctx_strong l k x :
  measurable_fun setT (@mctx_strong l k x).
Proof.
elim: l k x => [l2 x|g l ih k x]; first exact: measurable_snd.
apply/prod_measurable_funP; split.
- rewrite [X in measurable_fun _ X](_ : _ = fst)//.
  by apply/funext => -[].
- rewrite [X in measurable_fun _ X](_ : _ = @mctx_strong l k x \o snd).
    exact: measurableT_comp.
  by apply/funext => -[].
Qed.

Lemma mweak l k x t (f : dval R (l ++ k) t) :
  measurable_fun setT f -> measurable_fun setT (@weak l k x t f).
Proof.
move=> mf; apply: measurableT_comp; first exact: mf.
exact: measurable_fun_mctx_strong.
Qed.

Definition kweak l k x t (f : R.-sfker (@mctx R (l ++ k)) ~> @mtyp R t)
    : @mctx R (l ++ x :: k) -> {measure set @mtyp R t -> \bar R} :=
  f \o @mctx_strong l k x.

Section kernel_weak.
Context l k x t (f : pval R (l ++ k) t).

Let mf U : measurable U -> measurable_fun setT (@kweak l k x t f ^~ U).
Proof.
move=> mU.
rewrite (_ : kweak _ ^~ U = f ^~ U \o @mctx_strong l k x)//.
apply: measurableT_comp => //; first exact: measurable_kernel.
exact: measurable_fun_mctx_strong.
Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ _ (@kweak l k x t f) mf.
End kernel_weak.

Section sfkernel_weak.
Context l k (x : string * typ) t (f : pval R (l ++ k) t).

Let sf : exists2 s : (R.-ker @mctx R (l ++ x :: k) ~> @mtyp R t)^nat,
  forall n, measure_fam_uub (s n) &
  forall z U, measurable U -> (@kweak l k x t f) z U = kseries s z U .
Proof.
have [s hs] := sfinite_kernel f.
exists (fun n => [the _.-ker _ ~> _ of @kweak l k x t (s n)]).
  by move=> n; have [M hM] := measure_uub (s n); exists M => x0; exact: hM.
by move=> z U mU; by rewrite /kweak/= hs.
Qed.

HB.instance Definition _ :=
  Kernel_isSFinite_subdef.Build _ _ _ _ _ (@kweak l k x t f) sf.

End sfkernel_weak.

Section fkernel_weak.
Context l k x t (f : R.-fker @mctx R (l ++ k) ~> @mtyp R t).

Let uub : measure_fam_uub (@kweak l k x t f).
Proof. by have [M hM] := measure_uub f; exists M => x0; exact: hM. Qed.

HB.instance Definition _ := @Kernel_isFinite.Build _ _ _ _ _
  (@kweak l k x t f) uub.
End fkernel_weak.

End weak.

Section accessor_functions.
Context {R : realType}.

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
Show Proof.
Defined.

Lemma macc_typ (l : seq typ) (i : nat) : measurable_fun setT (@acc_typ l i).
Proof.
elim: l i => //= h t ih [|j].
  exact: measurable_fst.
apply: (measurableT_comp (ih _)).
exact: measurable_snd.
Qed.

End accessor_functions.

Section eval.
Context {R : realType}.

Definition mtyps l := projT2 (@measurable_of_seq R l).

Definition mval (R : realType) (l : seq typ) (t : typ) :=
  @mtyps l -> @mtyp R t.

Local Open Scope seq_scope.
Inductive evalD : forall l t (e : @expD R l t)
  (f : mval R (map snd l) t), measurable_fun setT f -> Prop :=
| eval_unit l :
  l # exp_unit -D-> cst tt ; ktt

| eval_bool l b :
  l # exp_bool b -D-> cst b ; kb b

| eval_real l r :
  l # [r :r] -D-> cst r ; kr r

| eval_pair l t1 t2 e1 f1 mf1 e2 f2 mf2 :
  l # e1 -D-> f1 ; mf1 ->
  l # e2 -D-> f2 ; mf2 ->
  l # [(e1, e2)] -D-> fun x => (f1 x, f2 x) ;
  @measurable_fun_prod _ _ _ (mctx l) (mtyp t1) (mtyp t2) f1 f2 mf1 mf2

| eval_var (l : ctx) (x : string) :
  let i := index x (map fst l) in
  l # [% x] -D-> @acc_typ R (map snd l) i ;
                 (@macc_typ R (map snd l) i)

| eval_bernoulli l (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
  l # exp_bernoulli r r1 -D->
  cst [the probability _ _ of bernoulli r1] ; measurable_cst _

| eval_poisson l k e f mf :
  l # e -D-> f ; mf ->
  l # exp_poisson k e -D-> poisson k \o f ;
  measurableT_comp (mpoisson k) mf

| eval_normalize l t (e : expP l t) k :
  l # e -P-> k ->
  l # exp_normalize e -D-> (normalize k point : _ -> pprobability _ _) ;
  measurable_fun_mnormalize k

| evalD_weak l k t (e : expD (l ++ k) t) x
    (xl : x.1 \notin map fst (l ++ k)) f mf :
  (l ++ k) # e -D-> f ; mf ->
  (l ++ x :: k) # expD_weak e xl -D-> @weak R l k x t f ; @mweak R l k x t f mf

where "l # e -D-> v ; mv" := (@evalD l _ e v mv)

with evalP : forall l t, expP l t ->
  pval R l t -> Prop :=

| eval_ifP l T e1 f1 mf e2 k2 e3 k3 :
  l # e1 -D-> f1 ; mf ->
  l # e2 -P-> k2 ->
  l # e3 -P-> k3 ->
  l # [If e1 Then e2 Else e3] : expP l T -P-> ite mf k2 k3

| eval_letin l t1 t2 str (e1 : expP l t1) (e2 : expP ((str, t1) :: l) t2)
  (k1 : @pval R l t1)
  (k2 : @pval R ((str, t1) :: l) t2) :
  l # e1 -P-> k1 ->
  ((str, t1) :: l) # e2 -P-> k2 ->
  l # [Let str <~ e1 In e2] -P-> letin' k1 k2

| eval_sample l t (e : expD l (Prob t)) (p : mctx l -> pprobability (mtyp t) R)
  mp :
  l # e -D-> p ; mp ->
  l # @exp_sample R l _ e -P-> sample p mp

| eval_score l e (f : mctx l -> R)
  (mf : measurable_fun _ f) :
  l # e : expD l Real -D-> f ; mf ->
  l # exp_score e -P-> [the R.-sfker _ ~> _ of kscore mf]

| eval_return l T e (f : _ -> _) (mf : measurable_fun _ f) :
  l # e -D-> f ; mf ->
  l # [Ret e] : expP l T -P-> ret mf

| evalP_weak l k t (e : expP (l ++ k) t) x
    (xl : x.1 \notin map fst (l ++ k)) f :
  (l ++ k) # e -P-> f ->
  (l ++ x :: k) # expP_weak e xl -P-> [the R.-sfker _ ~> _ of @kweak R l k x t f]
where "l # e -P-> v" := (@evalP l _ e v).

End eval.

Notation "l # e -D-> v ; mv" := (@evalD _ l _ e v mv) : lang_scope.
Notation "l # e -P-> v" := (@evalP _ l _ e v) : lang_scope.

Scheme evalD_mut_ind := Induction for evalD Sort Prop
with evalP_mut_ind := Induction for evalP Sort Prop.

Scheme expD_mut_ind := Induction for expD Sort Prop
with expP_mut_ind := Induction for expP Sort Prop.

(* properties of the evaluation relation *)
Section eval_prop.
Variables (R : realType).

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
    (u : @pval R l t) (h1 : evalP e u) =>
    forall (v : @pval R l t), evalP e v -> u = v)); last exact: hu.
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
- move=> l k t e0 x xl f mf ev IH {}v {}mv.
  inversion 1; subst t0 l0 k0 x0.
  inj_ex H9; rewrite -H9.
  clear H11.
  inj_ex H7; subst e0.
  by rewrite (IH _ _ H3).
- move=> l t e0 f1 mf1 e2 k2 e3 k3 ev1 IH1 ev2 IH2 ev3 IH3 k.
  inversion 1; subst l0 T.
  inj_ex H0; subst e0.
  inj_ex H1; subst e4.
  inj_ex H5; subst k.
  inj_ex H2; subst e5.
  have ? := IH1 _ _ H6; subst f2.
  have -> : mf1 = mf by exact: Prop_irrelevance.
  by rewrite (IH2 _ H7) (IH3 _ H8).
- move=> l t1 t2 x e1 e2 k1 k2 ev1 IH1 ev2 IH2 k.
  inversion 1; subst l0 t0 t3 x.
  inj_ex H7; subst k.
  inj_ex H6; subst e5.
  inj_ex H5; subst e4.
  by rewrite (IH1 _ H4) (IH2 _ H8).
- move=> l t e0 p mp ev IH k.
  simple inversion 1 => //; subst.
  inj_ex H4; subst.
  inj_ex H3; subst.
  case: H3 => H3; inj_ex H3; subst e0 => ev1.
  have Hp := IH _ _ ev1.
  subst p0.
  by have -> : mp = mp0 by exact: Prop_irrelevance.
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
- move=> l k t e0 x xl k1 ev IH.
  inversion 1; subst x0 l0 k0 t0.
  inj_ex H9; rewrite -H9.
  inj_ex H7; subst e0.
  by rewrite (IH _ H3).
Qed.

Lemma evalP_uniq l t (e : expP l t) (u v : @pval R l t) :
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
- move=> l k t e x xl f mf ev IH {}v {}mv.
  inversion 1; subst x0 l0 k0 t0.
  inj_ex H7; subst e1.
  inj_ex H9; rewrite -H9.
  clear H11.
  by rewrite (IH _ _ H3).
- move=> l t e f mf e1 k1 e2 k2 ev IH ev1 IH1 ev2 IH2 k.
  inversion 1; subst l0 T.
  inj_ex H0; subst e0.
  inj_ex H1; subst e3.
  inj_ex H5; subst k.
  inj_ex H2; subst e4.
  have ? := IH _ _ H6; subst f0.
  have -> : mf0 = mf by exact: Prop_irrelevance.
  by rewrite (IH1 _ H7) (IH2 _ H8).
- move=> l t1 t2 x e1 e2 k1 k2 ev1 IH1 ev2 IH2 k.
  inversion 1; subst l0 x t3 t0.
  inj_ex H7; subst k.
  inj_ex H5; subst e4.
  inj_ex H6; subst e5.
  by rewrite (IH1 _ H4) (IH2 _ H8).
- move=> l t e p mp ep IH v.
  inversion 1; subst l0 t0.
  inj_ex H7; subst v.
  inj_ex H5; subst e1.
  have ? := IH _ _ H3; subst p1.
  by have -> : mp = mp1 by apply: Prop_irrelevance.
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
- move=> l k t e x xl k1 ev IH.
  inversion 1; subst x0 l0 k0 t0.
  inj_ex H9; rewrite -H9.
  inj_ex H7; subst e1.
  by rewrite (IH _ H3).
Qed.

Lemma evalD_full l t (e : expD l t) :
  exists f (mf : measurable_fun _ f), @evalD R l t e f mf.
Proof.
apply: (@expD_mut_ind R
  (fun l t (e : expD l t) => exists f (mf : measurable_fun setT f), evalD e mf)
  (fun l t (e : expP l t) => exists k, evalP e k)).
all: rewrite {l t e}.
- by do 2 eexists; exact: eval_unit.
- by do 2 eexists; exact: eval_bool.
- by do 2 eexists; exact: eval_real.
- move=> l t1 t2 e1 [f1 [mf1 H1]] e2 [f2 [mf2 H2]].
  by exists (fun x => (f1 x, f2 x)); eexists; exact: eval_pair.
- by move=> l x t tE; subst t; eexists; eexists; exact: eval_var.
- by move=> r r1; eexists; eexists; exact: eval_bernoulli.
- move=> l k e [f [mf H]].
  exists (poisson k \o f), (measurableT_comp (mpoisson k) mf).
  exact: eval_poisson.
- move=> l t e [k H].
  by exists (normalize k point), (measurable_fun_mnormalize k); exact: eval_normalize.
- move=> l1 l2 st x e [f [mf fmf]] xl.
  by exists (weak f), (mweak mf); exact/evalD_weak.
- move=> l t e1 [f [mf H1]] e2 [k2 H2] e3 [k3 H3].
  by exists (ite mf k2 k3); exact: eval_ifP.
- move=> l t1 t2 x e1 [k1 ev1] e2 [k2 ev2].
  by exists (letin' k1 k2); exact: eval_letin.
- move=> l t e [f [/= mf ef]].
  eexists; apply: eval_sample.
    exact: mf.
  move=> mf'.
  by have <- : mf = mf' by exact: Prop_irrelevance.
- move=> l e [f [mf f_mf]].
  by exists (score mf); exact: eval_score.
- by move=> l t e [f [mf f_mf]]; exists (ret mf); exact: eval_return.
- move=> l1 l2 st x e [k H1] xl.
  by exists [the _.-sfker _ ~> _ of kweak k]; exact: evalP_weak.
Qed.

Lemma evalP_full l t (e : expP l t) :
  exists (k : R.-sfker _ ~> _), @evalP R l t e k.
Proof.
apply: (@expP_mut_ind R
  (fun l t (e : expD l t) => exists f (mf : measurable_fun _ f), evalD e mf)
  (fun l t (e : expP l t) => exists k, evalP e k)).
all: rewrite {l t e}.
- by do 2 eexists; exact: eval_unit.
- by do 2 eexists; exact: eval_bool.
- by do 2 eexists; exact: eval_real.
- move=> l t1 t2 e1 [f1 [mf1 H1]] e2 [f2 [mf2 H2]].
  by exists (fun x => (f1 x, f2 x)); eexists; exact: eval_pair.
- by move=> l x t tE; subst t; eexists; eexists; exact: eval_var.
- by move=> r r1; eexists; eexists; exact: eval_bernoulli.
- move=> l k e [f [mf H]].
  exists (poisson k \o f), (measurableT_comp (mpoisson k) mf).
  exact: eval_poisson.
- move=> l t e []k H.
  by exists (normalize k point), (measurable_fun_mnormalize k); exact: eval_normalize.
- move=> l1 l2 t x e [f [mf H]] xl.
  by exists (weak f), (mweak mf); exact: evalD_weak.
- move=> l t e1 [f [mf H1]] e2 [k2 H2] e3 [k3 H3].
  by exists (ite mf k2 k3); exact: eval_ifP.
- move=> l t1 t2 x e1 [k1 ev1] e2 [k2 ev2].
  by exists (letin' k1 k2); exact: eval_letin.
- move=> l t e [f [mf ef]].
  eexists; apply: eval_sample.
    exact: mf.
  move=> mf'.
  by have <- : mf = mf' by exact: Prop_irrelevance.
- by move=> l e [f [mf H]]; exists (score mf); exact: eval_score.
- by move=> l t e [f [mf H]]; exists (ret mf); exact: eval_return.
- move=> l1 l2 s x e [k H1] xl.
  by exists [the _.-sfker _ ~> _ of kweak k]; exact: evalP_weak.
Qed.

End eval_prop.

(* execution functions *)
Section exec.
Context {R : realType}.

Definition execD l t (e : @expD R l t) :
    {f : dval R l t & measurable_fun setT f} :=
  let: exist _ H := cid (evalD_full e) in
  existT _ _ (projT1 (cid H)).

Lemma evalD_execD l t e : let: x := @execD l t e in
  l # e -D-> projT1 x ; projT2 x.
 by rewrite /execD /=; case: cid => f [mf ?] /=; case: cid. Qed.

Definition execP l t (e : @expP R l t) : R.-sfker @mctx R l ~> @mtyp R t :=
  proj1_sig (cid (evalP_full e)).

Lemma evalP_execP l t (e : expP l t) : l # e -P-> execP e.
Proof. by rewrite /execP; case: cid. Qed.

Definition execP_ret_real (l : ctx) (r : R) :
    R.-sfker @mctx R l ~> @mtyp R Real :=
  execP (exp_return (exp_real r)).

Lemma execD_real l r : @execD l _ [r :r] = existT _ (cst r) (kr r).
Proof.
rewrite /execD /=.
case: cid => f ?.
case: cid => ? ev1.
have ev2 := eval_real l r.
have ? := evalD_uniq ev1 ev2; subst f.
by congr existT; exact: Prop_irrelevance.
Qed.

Lemma execD_pair l t1 t2 (x : @expD R l t1) (y : @expD R l t2) :
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
  apply: (@evalD_uniq _ l _ [(x, y)] (projT1 lhs) (projT1 rhs) (projT2 lhs) (projT2 rhs)).
    exact: evalD_execD.
  by apply: eval_pair; exact: evalD_execD.
exact: eq_sigT_hprop.
Qed.

Lemma execD_var l str :
  let i := index str (map fst l) in
  @execD l _ [% {str} ] = existT _ (@acc_typ R (map snd l) i)
                                   (@macc_typ R (map snd l) i).
Proof.
rewrite /execD /=.
case: cid => f ?.
case: cid => ? ev1.
have ev2 := @eval_var R l str.
have ? := evalD_uniq ev1 ev2; subst f.
by congr existT; exact: Prop_irrelevance.
Qed.

Lemma execD_poisson l k (e : expD l Real) :
  execD (exp_poisson k e) =
    existT _ (poisson k \o (projT1 (execD e)))
             (measurableT_comp (mpoisson k) (projT2 (execD e))).
Proof.
rewrite /execD /=.
case: cid => f ?.
case: cid => mf ev1.
have IHev : (l # e -D-> projT1 (execD e); projT2 (execD e)).
  exact: evalD_execD.
have ev2 := eval_poisson k IHev.
have ? := evalD_uniq ev1 ev2; subst f.
by congr existT; exact: Prop_irrelevance.
Qed.

Lemma execP_if l st e1 e2 e3 :
  @execP l st [If e1 Then e2 Else e3] =
  ite (projT2 (execD e1)) (execP e2) (execP e3).
Proof.
apply/evalP_uniq; first exact/evalP_execP.
by apply/eval_ifP; [exact: evalD_execD|exact: evalP_execP|exact: evalP_execP].
Qed.

Lemma execP_letin l x t1 t2 (e1 : expP l t1) (e2 : expP ((x, t1) :: l) t2) :
  execP [Let x <~ e1 In e2] = letin' (execP e1) (execP e2) :> (R.-sfker _ ~> _).
Proof.
apply: evalP_uniq; first exact/evalP_execP.
by apply: eval_letin; exact/evalP_execP.
Qed.

Lemma execP_sample_bern l r r1 :
  execP (exp_sample (@exp_bernoulli R l r r1)) = sample_cst (bernoulli r1).
Proof.
apply: evalP_uniq; first exact/evalP_execP.
by apply: eval_sample => /=; exact: eval_bernoulli.
Qed.

Lemma execP_score l (e : @expD R l Real) :
  execP (exp_score e) = score (projT2 (execD e)).
Proof.
apply: evalP_uniq; first exact/evalP_execP.
exact/eval_score/evalD_execD.
Qed.

Lemma execP_ret l t (e : @expD R l t) : execP [Ret e] = ret (projT2 (execD e)).
Proof.
apply: evalP_uniq; first exact/evalP_execP.
by apply: eval_return; exact/evalD_execD.
Qed.

Lemma execP_weak l k x t (e : expP (l ++ k) t)
    (xl : x.1 \notin map fst (l ++ k)) :
  execP (@expP_weak R l k t _ e xl) = [the _.-sfker _ ~> _ of kweak (execP e)].
Proof.
apply: evalP_uniq; first exact/evalP_execP.
by apply: evalP_weak; exact: evalP_execP.
Qed.

End exec.

Section letinC.
Local Open Scope lang_scope.
Variable R : realType.

Lemma ex_var_ret l :
  @execP R l _ [Let "x" <~ Ret {1}:r In Ret %{"x"}] =
  letin' (ret (kr 1)) (ret (@macc0of2 _ _ _ _)).
Proof.
rewrite execP_letin; congr letin'.
by rewrite execP_ret execD_real.
by rewrite execP_ret execD_var; congr ret.
Qed.

(* generic version *)
Lemma letinC l t1 t2 (e1 : @expP R l t1) (e2 : expP l t2)
  (xl : "x" \notin map fst l) (yl : "y" \notin map fst l) :
  forall U, measurable U ->
  execP [Let "x" <~ e1 In
        Let "y" <~ {@expP_weak _ [::] _ _ ("x", t1) e2 xl} In
        Ret (%{"x"}, %{"y"})] ^~ U =
  execP [Let "y" <~ e2 In
        Let "x" <~ {@expP_weak _ [::] _ _ ("y", t2) e1 yl} In
        Ret (%{"x"}, %{"y"})] ^~ U.
Proof.
move=> U mU; apply/funext => x.
rewrite 4!execP_letin.
rewrite (@execP_weak _ [::] l).
rewrite (@execP_weak _ [::] l).
rewrite 2!execP_ret/=.
rewrite 2!execD_pair/=.
rewrite !(execD_var _ "x")/= !(execD_var _ "y")/=.
have -> : @macc_typ _ [:: t2, t1 & [seq i.2 | i <- l]] 0 = macc0of3' by [].
have -> : @macc_typ _ [:: t2, t1 & [seq i.2 | i <- l]] 1 = macc1of3' by [].
rewrite (letin'C _ _ (execP e2) [the R.-sfker _ ~> _ of @kweak _ [::] _ ("y", t2) _ (execP e1)]); [ |by [] | by [] |by []].
have -> : @macc_typ _ [:: t1, t2 & [seq i.2 | i <- l]] 0 = macc0of3' by [].
by have -> : @macc_typ _ [:: t1, t2 & [seq i.2 | i <- l]] 1 = macc1of3' by [].
Qed.

(* letinC with a concrete context *)
Lemma letinC_list (l := [:: ("a", Unit); ("b", Bool)]) t1 t2
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
exact: letinC.
Qed.

Lemma letinC12 : forall U, measurable U ->
  @execP R [::] _ [Let "x" <~ Ret {1}:r In
         Let "y" <~ Ret {2}:r In
         Ret (%{"x"}, %{"y"})] ^~ U =
  execP [Let "y" <~ Ret {2}:r In
         Let "x" <~ Ret {1}:r In
         Ret (%{"x"}, %{"y"})] ^~ U.
Proof.
move=> U mU.
apply: funext => x.
rewrite !execP_letin !execP_ret !execD_real !execD_pair.
rewrite (execD_var _ "x")/= (execD_var _ "y")/=.
(* TODO: Use letinC *)
Abort.

(* TODO *)
Lemma execP_LetInL l t1 t2 x (e1 : @expP R l t1) (e1' : expP l t1) (e2 : expP ((x, t1) :: l) t2) :
  forall U, measurable U ->
  execP e1 = execP e1' ->
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

End letinC.

Section letinA.
Local Open Scope lang_scope.
Variable R : realType.

Lemma letinA l t1 t2 t3
  (e1 : @expP R l t1)
  (e2 : expP [:: ("y", t1) & l] t2)
  (e3 : expP [:: ("x", t2) & l] t3)
  (xl : "x" \notin map fst l)
  (yl : "y" \notin map fst [:: ("x", t2) & l]) :
  forall U, measurable U ->
  execP [Let "y" <~ e1 In
         Let "x" <~ e2 In
         {(@expP_weak _ [:: ("x", t2)] l _ ("y", t1) e3 yl)}] ^~ U =
  execP [Let "x" <~ Let "y" <~ e1 In e2 In
         e3] ^~ U.
Proof.
move=> U mU; apply/funext=> x.
rewrite !execP_letin.
rewrite (@execP_weak _ [:: ("x", t2)]).
apply: letin'A => //.
move=> y z.
rewrite /=.
rewrite /kweak /mctx_strong /=.
by destruct z.
Qed.

Lemma letinA12 : forall U, measurable U ->
  @execP R [::] _ [Let "y" <~ Ret {1}:r In
         Let "x" <~ Ret {2}:r In Ret %{"x"}] ^~ U =
  @execP R [::] _ [Let "x" <~ Let "y" <~ Ret {1}:r In Ret {2}:r In
         Ret %{"x"}] ^~ U.
Proof.
move=> U mU.
rewrite !execP_letin !execP_ret !execD_real !execD_var /=.
apply: funext=> x.
exact: letin'A.
(* TODO: Use letinA *)
Qed.

End letinA.

Section exp_var'.
Context {R : realType}.

Structure tagged_context := Tag {untag : ctx}.

Definition recurse_tag h := Tag h.
Canonical found_tag h := recurse_tag h.

Structure find (s : string) (t : typ) := Find {
  context_of : tagged_context ;
  ctxt_prf : t = nth Unit (map snd (untag context_of))
                           (index s (map fst (untag context_of)))}.

Lemma left_pf (s : string) (t : typ) (l : ctx) :
  t = nth Unit (map snd ((s, t) :: l)) (index s (map fst ((s, t) :: l))).
Proof.
by rewrite /= !eqxx/=.
Qed.

Canonical found_struct s t (l : ctx) : find s t :=
  Eval hnf in @Find s t (found_tag ((s, t) :: l)) (@left_pf s t l).

Lemma right_pf (s : string) (t : typ) (l : ctx) u t' :
  s != u ->
  t' = nth Unit (map snd l) (index u (map fst l)) ->
  t' = nth Unit (map snd ((s, t) :: l)) (index u (map fst ((s, t) :: l))).
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

Local Notation "%1 x" := (@exp_var' x%string _ _) (in custom expr at level 1).

Example e3 := [Let "x" <~ Ret {1%:R}:r In
               Let "y" <~ Ret %1{"x"} In
               Let "z" <~ Ret %1{"y"} In Ret %1{"z"}] : expP [::] _.

End exp_var'.

Section staton_bus.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Import Notations.
Context {R : realType}.

Goal (ret (kr 3) : R.-sfker _ ~> (mR R)) tt [set: R] = 1%:E.
Proof. rewrite /= diracE in_setT //. Qed.

Local Notation "%1 x" := (@exp_var' R x%string _ _) (in custom expr at level 1).

Example staton_bus_exp := exp_normalize (
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
      (letin' score_poi (ret macc2of4'))).

Lemma eval_staton_bus : [::] # kstaton_bus_exp -P-> kstaton_bus''.
Proof.
apply: eval_letin.
  by apply: eval_sample; exact: eval_bernoulli.
apply: eval_letin.
  apply/eval_ifP/eval_return/eval_real/eval_return/eval_real.
  rewrite/exp_var'/=.
  have /= := @eval_var R [:: ("x", Bool)] "x".
  have <- : ([% {"x"}] = @exp_var R _ "x" _ (left_pf "x" Bool [::])).
    congr exp_var; exact: Prop_irrelevance.
  by congr evalD; exact: Prop_irrelevance.
apply: eval_letin.
  apply/eval_score/eval_poisson.
  rewrite /exp_var'/=.
  have /= := @eval_var R [:: ("r", Real); ("x", Bool)] "r".
  have <- : ([% {"r"}] = @exp_var R _ "r" _ (left_pf "r" Real [:: ("x", Bool)])).
    by congr exp_var; exact: Prop_irrelevance.
  by congr evalD; exact: Prop_irrelevance.
apply/eval_return.
have /= := @eval_var R [:: ("_", Unit); ("r", Real); ("x", Bool)] "x".
rewrite /acc2of4' /comp/=.
by congr evalD; exact: Prop_irrelevance.
Qed.

Lemma exec_staton_bus : execP kstaton_bus_exp = kstaton_bus''.
Proof.
rewrite /kstaton_bus''.
rewrite 3!execP_letin execP_sample_bern.
congr letin'.
rewrite !execP_if !execP_ret !execD_real.
have -> : @execD R _ _ (exp_var "x" (left_pf "x" Bool [::])) = execD [% {"x"}].
  by congr execD; congr exp_var; exact: Prop_irrelevance.
rewrite execD_var /= /ite_3_10.
have -> : @macc_typ R [:: Bool] 0 = @macc0of2 _ _ _ _ by [].
congr letin'.
rewrite execP_score execD_poisson /=.
have -> : (@execD R _ _ (exp_var "r" (left_pf "r" Real [:: ("x", Bool)])) = execD [% {"r"}]).
  by congr execD; congr exp_var; exact: Prop_irrelevance.
rewrite execD_var /=.
have ->/= : @macc_typ R [:: Real; Bool] 0 = @macc0of2 _ _ _ _ by [].
congr letin'.
rewrite (execD_var _ "x") /=.
by have -> : (@macc_typ _ [:: Unit; Real; Bool] 2 = macc2of4').
Qed.

End staton_bus.
