Require Import String.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp.classical Require Import mathcomp_extra boolp classical_sets.
From mathcomp.classical Require Import functions cardinality fsbigop.
Require Import signed reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure numfun lebesgue_integral kernel prob_lang.
Require Import lang_syntax_util.
From mathcomp Require Import ring.

(******************************************************************************)
(*       Syntax and Evaluation for a probabilistic programming language       *)
(*                                                                            *)
(*                 typ == syntax for types of data structures                 *)
(* measurable_of_typ t == the measurable type corresponding to type t         *)
(*                        It is of type {d & measurableType d}                *)
(*              mtyp t == the measurable type corresponding to type t         *)
(*                        It is of type                                       *)
(*                        measurableType (projT1 (measurable_of_typ t))       *)
(* measurable_of_seq s == the product space corresponding to the              *)
(*                        list s : seq typ                                    *)
(*                        It is of type {d & measurableType d}                *)
(*         acc_typ s n == function that access the nth element of s : seq typ *)
(*                        It is a function from projT2 (measurable_of_seq s)  *)
(*                        to projT2 (measurable_of_typ (nth Unit s n))        *)
(*                 ctx == type of context                                     *)
(*                     := seq (string * type)                                 *)
(*              mctx g := the measurable type corresponding to the context g  *)
(*                        It is formed of nested pairings of measurable       *)
(*                        spaces. It is of type measurableType                *)
(*                        (projT1 (measurable_of_seq (map snd g)))            *)
(*                flag == a flag is either D (deterministic) or               *)
(*                        P (probabilistic)                                   *)
(*           exp f g t == syntax of expressions with flag f of type t         *)
(*                        context g                                           *)
(*          dval R g t == "deterministic value", i.e.,                        *)
(*                        function from mctx g to mtyp t                      *)
(*          pval R g t == "probabilistic value", i.e.,                        *)
(*                        s-finite kernel, from mctx g to mtyp t              *)
(*       e -D-> f ; mf == the evaluation of the deterministic expression e    *)
(*                        leads to the deterministic value f                  *)
(*                        (mf is the proof that f is measurable)              *)
(*            e -P-> k == the evaluation of the probabilistic function f      *)
(*                        leads to the probabilistic value k                  *)
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

Reserved Notation "f .; g" (at level 60, right associativity,
  format "f  .; '/ '  g").
Reserved Notation "e -D-> f ; mf" (at level 40).
Reserved Notation "e -P-> k" (at level 40).

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

(* TODO: document *)
Section mswap.
Context d d' d3 (X : measurableType d) (Y : measurableType d')
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

Notation "l .; k" := (mkcomp l [the _.-ker _ ~> _ of mkswap k]) : ereal_scope.

(* TODO: document *)
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

Section letin'C.
Import Notations.
Context d d1 d' (X : measurableType d) (Y : measurableType d1)
  (Z : measurableType d') (R : realType).

(* TODO: remove? *)
Lemma letin'C12 z A : measurable A ->
  @letin' _ _ _ _ _ _ R (ret (kr 1))
    (letin' (ret (kb true))
      (ret (measurable_fun_prod
              (measurable_acc [:: existT _ _ mbool; existT _ _ (mR R)] 1)
              (measurable_acc [:: existT _ _ mbool; existT _ _ (mR R)] 0))))
   z A =
  letin' (ret (kb true))
    (letin' (ret (kr 1))
      (ret (measurable_fun_prod
         (measurable_acc [:: existT _ _ (mR R); existT _ _ mbool] 0)
         (measurable_acc [:: existT _ _ (mR R); existT _ _ mbool] 1))))
  z A.
Proof.
move=> mA.
have : acc [:: existT _ _ mbool; existT _ _ (mR R)] 1 =
       acc [:: existT _ _ mbool; existT _ _ (mR R)] 1.
rewrite /acc /=.
(* rewrite !letin'E. *)
Abort.

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

(* TODO: remove? *)
Check (ret (measurable_fun_prod (measurable_acc
  [:: existT _ _ Y; existT _ _ X; existT _ _ Z] 1) (measurable_acc
  [:: existT _ _ Y; existT _ _ X; existT _ _ Z]
  0))).

Check (ret (kr 1)) : R.-sfker munit ~> mR R.

Lemma letin'C z A : measurable A ->
  letin' t
  (letin' u'
  (ret (measurable_fun_prod macc1of3' macc0of3'))) z A =
  letin' u
  (letin' t'
  (ret (measurable_fun_prod macc0of3' macc1of3'))) z A.
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

Declare Scope lang_scope.
Delimit Scope lang_scope with P.

Section syntax_of_types.
Import Notations.
Context {R : realType}.

Inductive typ :=
| Unit | Bool | Real
| Pair : typ -> typ -> typ
| Prob : typ -> typ.

Canonical stype_eqType := Equality.Pack (@gen_eqMixin typ).

Fixpoint measurable_of_typ (t : typ) : {d & measurableType d} :=
  match t with
  | Unit => existT _ _ munit
  | Bool => existT _ _ mbool
  | Real => existT _ _ (mR R)
  | Pair A B => existT _ _
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

Section accessor_functions.
Context {R : realType}.

(* NB: almost the same as acc (map (@measurable_of_typ R) s) n l,
   modulo commutativity of map and measurable_of_typ *)
Fixpoint acc_typ (s : seq typ) n :
  projT2 (@measurable_of_seq R s) ->
  projT2 (measurable_of_typ (nth Unit s n)) :=
  match s return
    projT2 (measurable_of_seq s) -> projT2 (measurable_of_typ (nth Unit s n))
  with
  | [::] => match n with | 0 => (fun=> tt) | m.+1 => (fun=> tt) end
  | a :: l => match n with
              | 0 => fst
              | m.+1 => fun H => @acc_typ l m H.2
              end
  end.

(*Definition acc_typ : forall (s : seq typ) n,
  projT2 (@measurable_of_seq R s) ->
  projT2 (@measurable_of_typ R (nth Unit s n)).
fix H 1.
intros s n x.
destruct s as [|s].
  destruct n as [|n].
    exact tt.
  exact tt.
destruct n as [|n].
  exact (fst x).
rewrite /=.
apply H.
exact: (snd x).
Show Proof.
Defined.*)

Lemma measurable_acc_typ (s : seq typ) n : measurable_fun setT (@acc_typ s n).
Proof.
elim: s n => //= h t ih [|m]; first exact: measurable_fst.
by apply: (measurableT_comp (ih _)); exact: measurable_snd.
Qed.

End accessor_functions.
Arguments measurable_acc_typ {R} s n.

Section context.
Variables (R : realType).
Definition ctx := seq (string * typ).

Definition mctx (g : ctx)
    : measurableType (projT1 (measurable_of_seq (map snd g))) :=
  projT2 (@measurable_of_seq R (map snd g)).

End context.
Arguments mctx {R}.

Section syntax_of_expressions.
Context {R : realType}.

Inductive flag := D | P.

Inductive exp : flag -> ctx -> typ -> Type :=
| exp_unit g : exp D g Unit
| exp_bool g : bool -> exp D g Bool
| exp_real g : R -> exp D g Real
| exp_pair g t1 t2 : exp D g t1 -> exp D g t2 -> exp D g (Pair t1 t2)
| exp_var g x t : t = nth Unit (map snd g) (index x (map fst g)) ->
    exp D g t
| exp_bernoulli g (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
    exp D g (Prob Bool)
| exp_poisson g : nat -> exp D g Real -> exp D g Real
| exp_normalize g t : exp P g t -> exp D g (Prob t)
| exp_if dp g t : exp D g Bool -> exp dp g t -> exp dp g t -> exp dp g t
| exp_letin g t1 t2 str : exp P g t1 -> exp P ((str, t1) :: g) t2 ->
    exp P g t2
| exp_sample g t : exp D g (Prob t) -> exp P g t
| exp_score g : exp D g Real -> exp P g Unit
| exp_return g t : exp D g t -> exp P g t
| exp_weak dp g h t x : exp dp (g ++ h) t -> x.1 \notin map fst (g ++ h) ->
    exp dp (g ++ x :: h) t.

End syntax_of_expressions.

Arguments exp {R}.
Arguments exp_unit {R g}.
Arguments exp_bool {R g}.
Arguments exp_real {R g}.
Arguments exp_pair {R g t1 t2}.
Arguments exp_var {R g} _ {t}.
Arguments exp_bernoulli {R g}.
Arguments exp_poisson {R g}.
Arguments exp_normalize {R g _}.
Arguments exp_if {R dp g t}.
Arguments exp_letin {R g _ _}.
Arguments exp_sample {R g t}.
Arguments exp_score {R g}.
Arguments exp_return {R g _}.
Arguments exp_weak {R dp g h t x}.

Declare Custom Entry expr.
Notation "[ e ]" := e (e custom expr at level 5) : lang_scope.
Notation "x ':R'" := (@exp_real _ _ x%R)
  (in custom expr at level 1) : lang_scope.
Notation "'return' x" := (@exp_return _ _ _ x)
  (in custom expr at level 2) : lang_scope.
Notation "% x" := (@exp_var _ _ x _ erefl)
  (in custom expr at level 1) : lang_scope.
Notation "e :+ x" := (@exp_weak _ _ [::] _ _ (x, _) e erefl)
  (in custom expr at level 1) : lang_scope.
Notation "( x , y )" := (exp_pair x y)
  (in custom expr at level 1) : lang_scope.
Notation "'let' x ':=' e 'in' f" := (exp_letin x e f)
  (in custom expr at level 3,
   x constr,
   f custom expr at level 3,
   left associativity) : lang_scope.
(*Notation "( x )" := x (in custom expr, x at level 50).*)
Notation "'if' e1 'then' e2 'else' e3" := (exp_if e1 e2 e3)
  (in custom expr at level 1) : lang_scope.
Notation "{ x }" := x
  (in custom expr, x constr) : lang_scope.
Notation "x" := x
  (in custom expr at level 0, x ident) : lang_scope.
Notation "'Sample' e" := (exp_sample e)
  (in custom expr at level 2) : lang_scope.
Notation "'Score' e" := (exp_score e)
  (in custom expr at level 2) : lang_scope.

Section free_vars.
Context {R : realType}.

Fixpoint free_vars k g t (e : @exp R k g t) : seq string :=
  match e with
  | exp_unit _              => [::]
  | exp_bool _ _            => [::]
  | exp_real _ _            => [::]
  | exp_pair _ _ _ e1 e2    => free_vars e1 ++ free_vars e2
  | exp_var _ x _ _         => [:: x]
  | exp_bernoulli _ _ _     => [::]
  | exp_poisson _ _ e       => free_vars e
  | exp_normalize _ _ e     => free_vars e
  | exp_if _ _ _ e1 e2 e3   => free_vars e1 ++ free_vars e2 ++ free_vars e3
  | exp_letin _ _ _ x e1 e2 => free_vars e1 ++ rem x (free_vars e2)
  | exp_sample _ _ _        => [::]
  | exp_score _ e           => free_vars e
  | exp_return _ _ e        => free_vars e
  | exp_weak _ _ _ _ x e _  => rem x.1 (free_vars e)
  end.

End free_vars.

Definition dval (R : realType) (g : ctx) (t : typ) :=
  @mctx R g -> @mtyp R t.
Definition pval (R : realType) (g : ctx) (t : typ) :=
  R.-sfker @mctx R g ~> @mtyp R t.

Section weak.
Context {R : realType}.
Implicit Types (g h : ctx) (x : string * typ).

Fixpoint mctx_strong g h x (f : @mctx R (g ++ x :: h)) : @mctx R (g ++ h) :=
  match g as g0 return mctx (g0 ++ x :: h) -> mctx (g0 ++ h) with
  | [::] => fun f0 : mctx ([::] ++ x :: h) => let (a, b) := f0 in (fun=> id) a b
  | a :: t => uncurry (fun a b => (a, @mctx_strong t h x b))
  end f.

Definition weak g h x t (f : dval R (g ++ h) t) : dval R (g ++ x :: h) t :=
  f \o @mctx_strong g h x.

Lemma measurable_fun_mctx_strong g h x :
  measurable_fun setT (@mctx_strong g h x).
Proof.
elim: g h x => [h x|x g ih h x0]; first exact: measurable_snd.
apply/prod_measurable_funP; split.
- rewrite [X in measurable_fun _ X](_ : _ = fst)//.
  by apply/funext => -[].
- rewrite [X in measurable_fun _ X](_ : _ = @mctx_strong g h x0 \o snd).
    apply: measurableT_comp; last exact: measurable_snd.
    exact: ih.
  by apply/funext => -[].
Qed.

Lemma mweak g h x t (f : dval R (g ++ h) t) :
  measurable_fun setT f -> measurable_fun setT (@weak g h x t f).
Proof.
move=> mf; apply: measurableT_comp; first exact: mf.
exact: measurable_fun_mctx_strong.
Qed.

Definition kweak g h x t (f : pval R (g ++ h) t)
    : @mctx R (g ++ x :: h) -> {measure set @mtyp R t -> \bar R} :=
  f \o @mctx_strong g h x.

Section kernel_weak.
Context g h x t (f : pval R (g ++ h) t).

Let mf U : measurable U -> measurable_fun setT (@kweak g h x t f ^~ U).
Proof.
move=> mU.
rewrite (_ : kweak _ ^~ U = f ^~ U \o @mctx_strong g h x)//.
apply: measurableT_comp => //; first exact: measurable_kernel.
exact: measurable_fun_mctx_strong.
Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ _ (@kweak g h x t f) mf.
End kernel_weak.

Section sfkernel_weak.
Context g h (x : string * typ) t (f : pval R (g ++ h) t).

Let sf : exists2 s : (R.-ker @mctx R (g ++ x :: h) ~> @mtyp R t)^nat,
  forall n, measure_fam_uub (s n) &
  forall z U, measurable U -> (@kweak g h x t f) z U = kseries s z U .
Proof.
have [s hs] := sfinite_kernel f.
exists (fun n => [the _.-ker _ ~> _ of @kweak g h x t (s n)]).
  by move=> n; have [M hM] := measure_uub (s n); exists M => x0; exact: hM.
by move=> z U mU; by rewrite /kweak/= hs.
Qed.

HB.instance Definition _ :=
  Kernel_isSFinite_subdef.Build _ _ _ _ _ (@kweak g h x t f) sf.

End sfkernel_weak.

Section fkernel_weak.
Context g h x t (f : R.-fker @mctx R (g ++ h) ~> @mtyp R t).

Let uub : measure_fam_uub (@kweak g h x t f).
Proof. by have [M hM] := measure_uub f; exists M => x0; exact: hM. Qed.

HB.instance Definition _ := @Kernel_isFinite.Build _ _ _ _ _
  (@kweak g h x t f) uub.
End fkernel_weak.

End weak.

Section eval.
Context {R : realType}.
Implicit Type (g : ctx) (str : string).
Local Open Scope lang_scope.

Inductive evalD : forall g t, exp D g t ->
  forall f : dval R g t, measurable_fun setT f -> Prop :=
| eval_unit g : @exp_unit _ g -D-> cst tt ; ktt

| eval_bool g b : @exp_bool _ g b -D-> cst b ; kb b

| eval_real g r : ([r :R] : exp D g _) -D-> cst r ; kr r

| eval_pair g t1 (e1 : exp D g t1) f1 mf1 t2 (e2 : exp D g t2) f2 mf2 :
  e1 -D-> f1 ; mf1 -> e2 -D-> f2 ; mf2 ->
  [(e1, e2)] -D-> fun x => (f1 x, f2 x) ;
  measurable_fun_prod mf1 mf2

| eval_var g str : let i := index str (map fst g) in
  ([% str] : exp D g _) -D-> @acc_typ R (map snd g) i ; measurable_acc_typ (map snd g) i

| eval_bernoulli g (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
  @exp_bernoulli _ g _ r1 -D-> cst (bernoulli r1) ; measurable_cst _

| eval_poisson g n (e : exp D g _) f mf :
  e -D-> f ; mf ->
  exp_poisson n e -D-> poisson n \o f ; measurableT_comp (measurable_poisson n) mf

| eval_normalize g t (e : exp P g t) k :
  e -P-> k ->
  exp_normalize e -D-> normalize k point ;
                       measurable_fun_mnormalize k

| evalD_if g t (e1 : exp D g Bool) f1 mf1 (e2 : exp D g t) f2 mf2 (e3 : exp D g t) f3 mf3 :
  e1 -D-> f1 ; mf1 -> e2 -D-> f2 ; mf2 -> e3 -D-> f3 ; mf3 ->
  [if e1 then e2 else e3] -D-> fun x => if f1 x then f2 x else f3 x ;
                                        measurable_fun_ifT mf1 mf2 mf3

| evalD_weak g h t (e : exp D (g ++ h) t) x
    (Hx : x.1 \notin map fst (g ++ h)) f mf :
  e -D-> f ; mf ->
  exp_weak e Hx -D-> @weak R g h x t f ; @mweak R g h x t f mf

where "e -D-> v ; mv" := (@evalD _ _ e v mv)

with evalP : forall g t, exp P g t -> pval R g t -> Prop :=

| evalP_if g t (e1 : exp D g Bool) f1 mf (e2 : exp P g t) k2 (e3 : exp P g t) k3 :
  e1 -D-> f1 ; mf -> e2 -P-> k2 -> e3 -P-> k3 ->
  [if e1 then e2 else e3] -P-> ite mf k2 k3

| eval_letin g t1 t2 str (e1 : exp P g t1) (e2 : exp P ((str, t1) :: g) t2)
  (k1 : @pval R g t1) (k2 : @pval R ((str, t1) :: g) t2) :
  e1 -P-> k1 ->
  e2 -P-> k2 ->
  [let str := e1 in e2] -P-> letin' k1 k2

| eval_sample g t (e : exp D g (Prob t))
    (p : mctx g -> pprobability (mtyp t) R) mp :
  e -D-> p ; mp ->
  [Sample e] -P-> sample p mp

| eval_score g (e : exp D g Real) (f : mctx g -> R) (mf : measurable_fun _ f) :
  e -D-> f ; mf ->
  [Score e] -P-> kscore mf

| eval_return g t (e : exp D g t) (f : _ -> _) (mf : measurable_fun _ f) :
  e -D-> f ; mf -> [return e] -P-> ret mf

| evalP_weak g h t (e : exp P (g ++ h) t) x
    (Hx : x.1 \notin map fst (g ++ h)) f :
  e -P-> f ->
  exp_weak e Hx -P-> @kweak R g h x t f

where "e -P-> v" := (@evalP _ _ e v).

End eval.

Notation "e -D-> v ; mv" := (@evalD _ _ _ e v mv) : lang_scope.
Notation "e -P-> v" := (@evalP _ _ _ e v) : lang_scope.

Scheme evalD_mut_ind := Induction for evalD Sort Prop
with evalP_mut_ind := Induction for evalP Sort Prop.

(* properties of the evaluation relation *)
Section eval_prop.
Variables (R : realType).
Local Open Scope lang_scope.

Lemma evalD_uniq g t (e : exp D g t) (u v : dval R g t)
    (mu : measurable_fun setT u) (mv : measurable_fun setT v) :
  e -D-> u ; mu -> e -D-> v ; mv -> u = v.
Proof.
move=> hu.
apply: (@evalD_mut_ind R
  (fun g t (e : exp D g t) (f : dval R g t)
  (mf : measurable_fun setT f) (h1 : evalD e mf) =>
    forall (v : dval R g t) (mv : measurable_fun setT v),
    evalD e mv -> f = v)
  (fun g t (e : exp P g t)
    (u : @pval R g t) (h1 : evalP e u) =>
    forall (v : @pval R g t), evalP e v -> u = v)); last exact: hu.
all: (rewrite {g t e u v mu mv hu}).
- move=> g {}v {}mv.
  inversion 1; subst g0.
  by inj_ex H3.
- move=> g b {}v {}mv.
  inversion 1; subst g0 b0.
  by inj_ex H3.
- move=> g r {}v {}mv.
  inversion 1; subst g0 r0.
  by inj_ex H3.
- move=> g t1 e1 f1 mf1 t2 e2 f2 mf2 ev1 IH1 ev2 IH2 {}v {}mv.
  simple inversion 1 => //; subst g0.
  case: H3 => ? ?; subst t0 t3.
  inj_ex H4; case: H4 => He1 He2.
  inj_ex He1; subst e0.
  inj_ex He2; subst e3.
  inj_ex H5; subst v.
  by move=> /IH1 <- /IH2 <-.
- move=> g str n {}v {}mv.
  inversion 1; subst g0.
  inj_ex H6; rewrite -H6.
  by inj_ex H7.
- move=> g r r1 {}v {}mv.
  inversion 1; subst g0 r0.
  inj_ex H3; subst v.
  by have -> : r1 = r3 by exact: Prop_irrelevance.
- move=> g n e0 f mf ev IH {}v {}mv.
  inversion 1; subst g0 n0.
  inj_ex H2; subst e0.
  inj_ex H4; subst v.
  by rewrite (IH _ _ H3).
- move=> g t e0 k ev IH {}v {}mv.
  inversion 1; subst g0 t0.
  inj_ex H2; subst e0.
  inj_ex H4; subst v.
  by rewrite (IH _ H3).
- move=> g t e1 f1 mf1 e2 f2 mf2 e3 f3 mf3 ev1 IH1 ev2 IH2 ev3 IH3 f mf.
  inversion 1; subst g0 t0.
  inj_ex H2; subst e0.
  inj_ex H6; subst e6.
  inj_ex H7; subst e7.
  inj_ex H9; subst f.
  clear H11.
  have ? := IH1 _ _ H5; subst f6.
  have ? := IH2 _ _ H12; subst f7.
  by have ? := IH3 _ _ H13; subst f8.
- move=> g h t e0 x xgh f mf ev IH {}v {}mv.
  inversion 1; subst t0 g0 h0 x0.
  inj_ex H9; rewrite -H9.
  clear H11.
  inj_ex H7; subst e0.
  by rewrite (IH _ _ H3).
- move=> g t e1 f1 mf1 e2 k2 e3 k3 ev1 IH1 ev2 IH2 ev3 IH3 k.
  inversion 1; subst g0 t0.
  inj_ex H0; subst e0.
  inj_ex H1; subst e4.
  inj_ex H5; subst k.
  inj_ex H2; subst e5.
  have ? := IH1 _ _ H6; subst f2.
  have -> : mf1 = mf by exact: Prop_irrelevance.
  by rewrite (IH2 _ H7) (IH3 _ H8).
- move=> g t1 t2 x e1 e2 k1 k2 ev1 IH1 ev2 IH2 k.
  inversion 1; subst g0 t0 t3 x.
  inj_ex H7; subst k.
  inj_ex H6; subst e5.
  inj_ex H5; subst e4.
  by rewrite (IH1 _ H4) (IH2 _ H8).
- move=> g t e p mp ev IH k.
  inversion 1; subst g0.
  inj_ex H5; subst t0.
  inj_ex H5; subst e1.
  inj_ex H7; subst k.
  have ? := IH _ _ H3; subst p1.
  by have -> : mp = mp1 by exact: Prop_irrelevance.
- move=> g e f mf ev IH k.
  inversion 1; subst g0.
  inj_ex H0; subst e0.
  inj_ex H4; subst k.
  have ? := IH _ _ H2; subst f1.
  by have -> : mf = mf0 by exact: Prop_irrelevance.
- move=> g t e0 f mf ev IH k.
  inversion 1; subst g0 t0.
  inj_ex H5; subst e1.
  inj_ex H7; subst k.
  have ? := IH _ _ H3; subst f1.
  by have -> : mf = mf1 by exact: Prop_irrelevance.
- move=> g h t e x xgh k ek IH.
  inversion 1; subst x0 g0 h0 t0.
  inj_ex H9; rewrite -H9.
  inj_ex H7; subst e1.
  by rewrite (IH _ H3).
Qed.

Lemma evalP_uniq g t (e : exp P g t) (u v : @pval R g t) :
  e -P-> u -> e -P-> v -> u = v.
Proof.
move=> eu.
apply: (@evalP_mut_ind R
  (fun g t (e : exp D g t) (f : dval R g t)
    (mf : measurable_fun setT f) (h1 : evalD e mf) =>
    forall (v : dval R g t) (mv : measurable_fun setT v), evalD e mv -> f = v)
  (fun g t (e : exp P g t)
    (u : pval R g t) (h1 : evalP e u) =>
    forall (v : pval R g t), evalP e v -> u = v)); last exact: eu.
all: rewrite {g t e u v eu}.
- move=> g {}v {}mv.
  inversion 1; subst g0.
  by inj_ex H3.
- move=> g b {}v {}mv.
  inversion 1; subst g0 b0.
  by inj_ex H3.
- move=> g r {}v {}mv.
  inversion 1; subst g0 r0.
  by inj_ex H3.
- move=> g t1 e1 f1 mf1 t2 e2 f2 mf2 ev1 IH1 ev2 IH2 {}v {}mv.
  simple inversion 1 => //; subst g0.
  case: H3 => ? ?; subst t0 t3.
  inj_ex H4; case: H4 => He1 He2.
  inj_ex He1; subst e0.
  inj_ex He2; subst e3.
  inj_ex H5; subst v.
  move=> e1f0 e2f3.
  by rewrite (IH1 _ _ e1f0) (IH2 _ _ e2f3).
- move=> g x n {}v {}mv.
  inversion 1; subst g0.
  inj_ex H7; subst v.
  by inj_ex H6.
- move=> g r r1 {}v {}mv.
  inversion 1; subst g0 r0.
  inj_ex H3; subst v.
  by have -> : r1 = r3 by exact: Prop_irrelevance.
- move=> g n e f mf ev IH {}v {}mv.
  inversion 1; subst g0 n0.
  inj_ex H2; subst e0.
  inj_ex H4; subst v.
  inj_ex H5; subst mv.
  by rewrite (IH _ _ H3).
- move=> g t e k ev IH {}v {}mv.
  inversion 1; subst g0 t0.
  inj_ex H2; subst e0.
  inj_ex H4; subst v.
  inj_ex H5; subst mv.
  by rewrite (IH _ H3).
- move=> g t e1 f1 mf1 e2 f2 mf2 e3 f3 mf3 ev IH ev1 IH1 ev2 IH2 f mf.
  inversion 1; subst g0 t0.
  inj_ex H2; subst e0.
  inj_ex H6; subst e6.
  inj_ex H7; subst e7.
  inj_ex H9; subst f.
  clear H11.
  have ? := IH1 _ _ H12; subst f7.
  have ? := IH2 _ _ H13; subst f8.
  by have ? := IH _ _ H5; subst f6.
- move=> g h t e x xgh f mf ef IH {}v {}mv.
  inversion 1; subst x0 g0 h0 t0.
  inj_ex H7; subst e1.
  inj_ex H9; rewrite -H9.
  clear H11.
  by rewrite (IH _ _ H3).
- move=> g t e f mf e1 k1 e2 k2 ev IH ev1 IH1 ev2 IH2 k.
  inversion 1; subst g0 t0.
  inj_ex H0; subst e0.
  inj_ex H1; subst e3.
  inj_ex H5; subst k.
  inj_ex H2; subst e4.
  have ? := IH _ _ H6; subst f0.
  have -> : mf0 = mf by exact: Prop_irrelevance.
  by rewrite (IH1 _ H7) (IH2 _ H8).
- move=> g t1 t2 x e1 e2 k1 k2 ev1 IH1 ev2 IH2 k.
  inversion 1; subst g0 x t3 t0.
  inj_ex H7; subst k.
  inj_ex H5; subst e4.
  inj_ex H6; subst e5.
  by rewrite (IH1 _ H4) (IH2 _ H8).
- move=> g t e p mp ep IH v.
  inversion 1; subst g0 t0.
  inj_ex H7; subst v.
  inj_ex H5; subst e1.
  have ? := IH _ _ H3; subst p1.
  by have -> : mp = mp1 by apply: Prop_irrelevance.
- move=> g e f mf ev IH k.
  inversion 1; subst g0.
  inj_ex H0; subst e0.
  inj_ex H4; subst k.
  have ? := IH _ _ H2; subst f1.
  by have -> : mf = mf0 by exact: Prop_irrelevance.
- move=> g t e f mf ev IH k.
  inversion 1; subst g0 t0.
  inj_ex H7; subst k.
  inj_ex H5; subst e1.
  have ? := IH _ _ H3; subst f1.
  by have -> : mf = mf1 by exact: Prop_irrelevance.
- move=> g h t e x xgh k ek IH.
  inversion 1; subst x0 g0 h0 t0.
  inj_ex H9; rewrite -H9.
  inj_ex H7; subst e1.
  by rewrite (IH _ H3).
Qed.

Definition eval_total_statement dp g t :=
  match dp with
  | D => fun (e : @exp R D g t) =>
      exists f (mf : measurable_fun _ f), e -D-> f ; mf
  | P => fun (e : @exp R P g t) =>
      exists (k : pval R g t), @evalP R g t e k
  end.

Lemma eval_total dp g t (e : @exp R dp g t) : eval_total_statement e.
Proof.
elim: e.
all: rewrite {dp g t}.
- by do 2 eexists; exact: eval_unit.
- by do 2 eexists; exact: eval_bool.
- by do 2 eexists; exact: eval_real.
- move=> g t1 t2 e1 [f1 [mf1 H1]] e2 [f2 [mf2 H2]].
  by exists (fun x => (f1 x, f2 x)); eexists; exact: eval_pair.
- by move=> g x t tE; subst t; eexists; eexists; exact: eval_var.
- by move=> r r1; eexists; eexists; exact: eval_bernoulli.
- move=> g h e [f [mf H]].
  by exists (poisson h \o f); eexists; exact: eval_poisson.
- move=> g t e [k ek].
  by exists (normalize k point); eexists; exact: eval_normalize.
- case.
  + move=> g t e1 [f [mf H1]] e2 [f2 [mf2 H2]] e3 [f3 [mf3 H3]].
    rewrite /eval_total_statement.
    exists (fun g => if f g then f2 g else f3 g),
      (measurable_fun_ifT mf mf2 mf3).
    exact: evalD_if.
  + move=> g t e1 [f [mf H1]] e2 [k2 H2] e3 [k3 H3].
    by exists (ite mf k2 k3); exact: evalP_if.
- move=> g t1 t2 x e1 [k1 ev1] e2 [k2 ev2].
  by exists (letin' k1 k2); exact: eval_letin.
- move=> g t e [f [/= mf ef]].
  by eexists; exact: (@eval_sample _ _ _ _ _ mf).
- move=> g e [f [mf f_mf]].
  by exists (kscore mf); exact: eval_score.
- by move=> g t e [f [mf f_mf]]; exists (ret mf); exact: eval_return.
- move=> [|].
  + move=> g h t x e [f [mf ef]] xgh.
    by exists (weak f), (mweak mf); exact/evalD_weak.
  + move=> g h st x e [k ek] xgh.
    by exists (kweak k); exact: evalP_weak.
Qed.

Lemma evalD_total g t (e : @exp R D g t) :
  exists f (mf : measurable_fun _ f), e -D-> f ; mf.
Proof. exact: (eval_total e). Qed.

Lemma evalP_total g t (e : @exp R P g t) :
  exists (k : pval R g t), @evalP R g t e k.
Proof. exact: (eval_total e). Qed.

End eval_prop.

(* execution functions *)
Section exec.
Local Open Scope lang_scope.
Context {R : realType}.
Implicit Type g : ctx.

Definition execD g t (e : exp D g t) :
    {f : dval R g t & measurable_fun setT f} :=
  let: exist _ H := cid (evalD_total e) in
  existT _ _ (projT1 (cid H)).

Lemma eq_execD g t (p1 p2 : @exp R D g t) : 
  projT1 (execD p1) = projT1 (execD p2) -> execD p1 = execD p2.
Proof.
rewrite /execD /=.
case: cid => /= f1 [mf1 ev1].
case: cid => /= f2 [mf2 ev2] f12.
subst f2.
have ? : mf1 = mf2.
  exact: Prop_irrelevance.
subst mf2.
congr existT.
rewrite /sval.
case: cid => mf1' ev1'.
have ? : mf1 = mf1'.
  exact: Prop_irrelevance.
subst mf1'.
case: cid => mf2' ev2'.
have ? : mf1 = mf2'.
  exact: Prop_irrelevance.
by subst mf2'.
Qed.

Lemma evalD_execD g t e :
  let: x := @execD g t e in e -D-> projT1 x ; projT2 x.
 by rewrite /execD /=; case: cid => f [mf ?] /=; case: cid. Qed.

Definition execP g t (e : exp P g t) : pval R g t :=
  proj1_sig (cid (evalP_total e)).

Lemma evalP_execP g t (e : exp P g t) : e -P-> execP e.
Proof. by rewrite /execP; case: cid. Qed.

Definition execP_return_real g (r : R) : pval R g Real :=
  execP (exp_return (exp_real r)).

Lemma execD_real g r : @execD g _ [r :R] = existT _ (cst r) (kr r).
Proof.
rewrite /execD /=.
case: cid => f ?.
case: cid => ? ev1.
have ev2 := eval_real g r.
have ? := evalD_uniq ev1 ev2; subst f.
by congr existT; exact: Prop_irrelevance.
Qed.

Lemma execD_bool g b : @execD g _ (exp_bool b) = existT _ (cst b) (kb b).
Proof.
rewrite /execD /=.
case: cid => f ?.
case: cid => ? ev1.
have ev2 := @eval_bool R g b.
have ? := evalD_uniq ev1 ev2; subst f.
by congr existT; exact: Prop_irrelevance.
Qed.

Lemma execD_unit g : @execD g _ exp_unit = existT _ (cst tt) ktt.
Proof.
rewrite /execD /=.
case: cid => f ?.
case: cid => ? ev1.
have ev2 := @eval_unit R g.
have ? := evalD_uniq ev1 ev2; subst f.
by congr existT; exact: Prop_irrelevance.
Qed.

Lemma execD_normalize g t (e : exp P g t) : @execD g _ (exp_normalize e) = existT _ (normalize (execP e) point : _ -> pprobability _ _) (measurable_fun_mnormalize (execP e)).
Proof.
rewrite /execD /=.
case: cid => f [mf ?].
case: cid => ? ev1.
have ev2 := eval_normalize (evalP_execP e).
have ? := evalD_uniq ev1 ev2; subst f.
by congr existT; exact: Prop_irrelevance.
Qed.

Lemma execD_pair g t1 t2 (e1 : exp D g t1) (e2 : exp D g t2) :
  let f1 := projT1 (execD e1) in
  let f2 := projT1 (execD e2) in
  let mf1 := projT2 (execD e1) in
  let mf2 := projT2 (execD e2) in
  execD [(e1, e2)] =
  @existT _ _ (fun z => (f1 z, f2 z))
              (@measurable_fun_prod _ _ _ (mctx g) (mtyp t1) (mtyp t2)
              f1 f2 mf1 mf2).
Proof.
move=> f1 f2 mf1 mf2; rewrite /f1 /f2 /mf1 /mf2.
set lhs := LHS; set rhs := RHS.
have h : projT1 lhs = projT1 rhs.
  apply: (@evalD_uniq _ g _ [(e1, e2)] (projT1 lhs) (projT1 rhs)
                                       (projT2 lhs) (projT2 rhs)).
    exact: evalD_execD.
  by apply: eval_pair; exact: evalD_execD.
exact: eq_sigT_hprop.
Qed.

Lemma execD_var g str :
  let i := index str (map fst g) in
  @execD g _ [% {str} ] = existT _ (@acc_typ R (map snd g) i)
                                   (measurable_acc_typ (map snd g) i).
Proof.
rewrite /execD /=.
case: cid => f ?.
case: cid => ? ev1.
have ? := evalD_uniq ev1 (@eval_var R g str); subst f.
by congr existT; exact: Prop_irrelevance.
Qed.

Lemma execD_bernoulli g r (r1 : (r%:num <= 1)%R) :
  @execD g _ (exp_bernoulli r r1) = existT _ (cst [the probability _ _ of bernoulli r1]) (measurable_cst _).
rewrite /execD /=.
case: cid => f ?.
case: cid => ? ev1.
have ? := evalD_uniq ev1 (@eval_bernoulli R g r r1); subst f.
by congr existT; exact: Prop_irrelevance.
Qed.

Lemma execD_poisson g n (e : exp D g Real) :
  execD (exp_poisson n e) =
    existT _ (poisson n \o (projT1 (execD e)))
             (measurableT_comp (measurable_poisson n) (projT2 (execD e))).
Proof.
rewrite /execD /=.
case: cid => f ?.
case: cid => mf ev1.
have IHev : e -D-> projT1 (execD e); projT2 (execD e).
  exact: evalD_execD.
have ? := evalD_uniq ev1 (eval_poisson n IHev); subst f.
by congr existT; exact: Prop_irrelevance.
Qed.

Lemma execP_if g st e1 e2 e3 :
  @execP g st [if e1 then e2 else e3] =
  ite (projT2 (execD e1)) (execP e2) (execP e3).
Proof.
apply/evalP_uniq; first exact/evalP_execP.
by apply/evalP_if; [exact: evalD_execD|exact: evalP_execP|exact: evalP_execP].
Qed.

Lemma execP_letin g x t1 t2 (e1 : exp P g t1) (e2 : exp P ((x, t1) :: g) t2) :
  execP [let x := e1 in e2] = letin' (execP e1) (execP e2) :> (R.-sfker _ ~> _).
Proof.
apply: evalP_uniq; first exact/evalP_execP.
by apply: eval_letin; exact/evalP_execP.
Qed.

Lemma execP_sample_bern g r r1 :
  execP [Sample {@exp_bernoulli R g r r1}] = sample_cst (bernoulli r1).
Proof.
apply: evalP_uniq; first exact/evalP_execP.
by apply: eval_sample => /=; exact: eval_bernoulli.
Qed.

Lemma execP_score g (e : exp D g Real) :
  execP [Score e] = score (projT2 (execD e)).
Proof.
apply: evalP_uniq; first exact/evalP_execP.
exact/eval_score/evalD_execD.
Qed.

Lemma execP_return g t (e : exp D g t) :
  execP [return e] = ret (projT2 (execD e)).
Proof.
apply: evalP_uniq; first exact/evalP_execP.
by apply: eval_return; exact/evalD_execD.
Qed.

Lemma execP_weak g h x t (e : exp P (g ++ h) t)
    (xl : x.1 \notin map fst (g ++ h)) :
  execP (@exp_weak R P g h t _ e xl) = [the _.-sfker _ ~> _ of kweak (execP e)].
Proof.
apply: evalP_uniq; first exact/evalP_execP.
by apply: evalP_weak; exact: evalP_execP.
Qed.

End exec.

Section letinC.
Local Open Scope lang_scope.
Variable R : realType.

Lemma ex_var_ret g :
  @execP R g _ [let "x" := return {1}:R in return %{"x"}] =
  letin' (ret (kr 1)) (ret (@macc0of2 _ _ _ _)).
Proof.
rewrite execP_letin; congr letin'.
by rewrite execP_return execD_real.
by rewrite execP_return execD_var; congr ret.
Qed.

(* generic version *)
Lemma letinC g t1 t2 (e1 : @exp R P g t1) (e2 : exp P g t2)
  (xl : "x" \notin map fst g) (yl : "y" \notin map fst g) :
  forall U, measurable U ->
  execP [let "x" := e1 in
         let "y" := {@exp_weak _ _ [::] _ _ ("x", t1) e2 xl} in
         return (%{"x"}, %{"y"})] ^~ U =
  execP [let "y" := e2 in
         let "x" := {@exp_weak _ _ [::] _ _ ("y", t2) e1 yl} in
         return (%{"x"}, %{"y"})] ^~ U.
Proof.
move=> U mU; apply/funext => x.
rewrite 4!execP_letin.
rewrite (@execP_weak _ [::] g).
rewrite (@execP_weak _ [::] g).
rewrite 2!execP_return/=.
rewrite 2!execD_pair/=.
rewrite !(execD_var _ "x")/= !(execD_var _ "y")/=.
have -> : measurable_acc_typ [:: t2, t1 & map snd g] 0 = macc0of3' by [].
have -> : measurable_acc_typ [:: t2, t1 & map snd g] 1 = macc1of3' by [].
rewrite (letin'C _ _ (execP e2)
  ([the R.-sfker _ ~> _ of @kweak _ [::] _ ("y", t2) _ (execP e1)]));
  [ |by [] | by [] |by []].
have -> : measurable_acc_typ [:: t1, t2 & map snd g] 0 = macc0of3' by [].
by have -> : measurable_acc_typ [:: t1, t2 & map snd g] 1 = macc1of3' by [].
Qed.

(* letinC with a concrete context *)
Lemma letinC_list (g := [:: ("a", Unit); ("b", Bool)]) t1 t2
    (e1 : @exp R P g t1)
    (e2 : exp P g t2) :
  forall U, measurable U ->
  execP [let "x" := e1 in
         let "y" := e2 :+ {"x"} in
         return (%{"x"}, %{"y"})] ^~ U =
  execP [let "y" := e2 in
         let "x" := e1 :+ {"y"} in
         return (%{"x"}, %{"y"})] ^~ U.
Proof.
move=> U mU.
exact: letinC.
Qed.

Lemma letinC12 : forall U, measurable U ->
  @execP R [::] _ [let "x" := return {1}:R in
                   let "y" := return {2}:R in
                   return (%{"x"}, %{"y"})] ^~ U =
  execP [let "y" := return {2}:R in
         let "x" := return {1}:R in
         return (%{"x"}, %{"y"})] ^~ U.
Proof.
move=> U mU.
apply: funext => x.
rewrite !execP_letin !execP_return !execD_real !execD_pair.
rewrite (execD_var _ "x")/= (execD_var _ "y")/=.
(* TODO: Use letinC *)
Abort.

(* TODO *)
Lemma execP_LetInL g t1 t2 x (e1 : @exp R P g t1) (e1' : exp P g t1)
   (e2 : exp P ((x, t1) :: g) t2) :
  forall U, measurable U ->
  execP e1 = execP e1' ->
  execP [let x := e1 in e2] ^~ U =
  execP [let x := e1' in e2] ^~ U.
Proof.
by move=> U mU e1e1'; rewrite !execP_letin e1e1'.
Qed.

Lemma execP_LetInR g t1 t2 x (e1 : @exp R P g t1)
    (e2 : exp P _ t2) (e2' : exp P ((x, t1) :: g) t2) :
  forall U, measurable U ->
  execP e2 = execP e2' ->
  execP [let x := e1 in e2] ^~ U =
  execP [let x := e1 in e2'] ^~ U.
Proof.
by move=> U mU e1e1'; rewrite !execP_letin e1e1'.
Qed.

End letinC.

Section letinA.
Local Open Scope lang_scope.
Variable R : realType.

Lemma letinA g (xg : "x" \notin map fst g) t1 t2 t3
  (e1 : @exp R P g t1)
  (e2 : exp P [:: ("x", t1) & g] t2)
  (e3 : exp P [:: ("y", t2) & g] t3) :
  forall U, measurable U ->
  execP [let "x" := e1 in
         let "y" := e2 in
         {@exp_weak _ _ [:: ("y", t2)] _ _ ("x", t1) e3 xg}] ^~ U =
  execP [let "y" :=
           let "x" := e1 in e2 in
         e3] ^~ U.
Proof.
move=> U mU; apply/funext=> x.
rewrite !execP_letin.
rewrite (@execP_weak _ [:: ("y", t2)]).
apply: letin'A => //.
move=> y z.
rewrite /=.
rewrite /kweak /mctx_strong /=.
by destruct z.
Qed.

Lemma letinA12 : forall U, measurable U ->
  @execP R [::] _ [let "y" := return {1}:R in
                   let "x" := return {2}:R in
                   return %{"x"}] ^~ U =
  @execP R [::] _ [let "x" :=
                   let "y" := return {1}:R in return {2}:R in
                   return %{"x"}] ^~ U.
Proof.
move=> U mU.
rewrite !execP_letin !execP_return !execD_real !execD_var /=.
apply: funext=> x.
exact: letin'A.
Qed.

End letinA.

Section exp_var'.
Context {R : realType}.

Definition exp_var' (str : string) (t : typ) (g : find str t) :=
  @exp_var R (untag (ctx_of g)) str t (ctx_prf g).

Lemma execD_var' str t (f : find str t) H : 
  @execD R _ t (exp_var' f) = execD (exp_var str H).
Proof. by rewrite /exp_var'; have -> : ctx_prf f = H. Qed.

Local Notation "# str" := (@exp_var' str%string _ _) (in custom expr at level 1).

Local Open Scope lang_scope.
Example e3 : exp P [::] _ :=
  [let "x" := return {1}:R in
   let "y" := return #{"x"} in
   let "z" := return #{"y"} in return #{"z"}].

End exp_var'.

Arguments execD_var' {R} str.

Section staton_bus.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Import Notations.
Context {R : realType}.

Goal (ret (kr 3) : R.-sfker _ ~> (mR R)) tt [set: R] = 1%:E.
Proof. rewrite /= diracE in_setT //. Qed.

Local Notation "# x" := (@exp_var' R x%string _ _) (in custom expr at level 1).

Definition sample_bern : R.-sfker munit ~> mbool :=
  sample_cst [the probability _ _ of bernoulli p27].

Definition ite_3_10 :
  R.-sfker [the measurableType _ of (mbool * munit)%type] ~> (mR R) :=
  ite (@macc0of2 _ _ _ _) (ret k3) (ret k10).

Definition score_poi :
  R.-sfker [the measurableType _ of (mR R * (mbool * munit))%type] ~> munit :=
  score (measurableT_comp (measurable_poisson 4) (@macc0of2 _ _ _ _)).

Example kstaton_bus_exp : exp P [::] Bool :=
  [let "x" := Sample {(exp_bernoulli (2 / 7%:R)%:nng p27)} in
   let "r" := if #{"x"} then return {3}:R else return {10}:R in
   let "_" := Score {(exp_poisson 4 [#{"r"}])} in
   return %{"x"}].

Example staton_bus_exp : exp D [::] (Prob Bool) := exp_normalize kstaton_bus_exp.

Local Definition kstaton_bus'' :=
  letin' sample_bern
    (letin' ite_3_10
      (letin' score_poi (ret macc2of4'))).

Lemma eval_staton_bus : kstaton_bus_exp -P-> kstaton_bus''.
Proof.
apply: eval_letin.
  by apply: eval_sample; exact: eval_bernoulli.
apply: eval_letin.
  apply/evalP_if/eval_return/eval_real/eval_return/eval_real.
  rewrite/exp_var'/=.
  have /= := @eval_var R [:: ("x", Bool)] "x".
  have <- : ([% {"x"}] = @exp_var R _ "x" _ (ctx_prf_head "x" Bool [::])).
    congr exp_var; exact: Prop_irrelevance.
  by congr evalD; exact: Prop_irrelevance.
apply: eval_letin.
  apply/eval_score/eval_poisson.
  rewrite /exp_var'/=.
  have /= := @eval_var R [:: ("r", Real); ("x", Bool)] "r".
  have <- : ([% {"r"}] = @exp_var R _ "r" _ (ctx_prf_head "r" Real [:: ("x", Bool)])).
    by congr exp_var; exact: Prop_irrelevance.
  by congr evalD; exact: Prop_irrelevance.
apply/eval_return.
have /= := @eval_var R [:: ("_", Unit); ("r", Real); ("x", Bool)] "x".
rewrite /acc2of4' /comp/=.
by congr evalD; exact: Prop_irrelevance.
Qed.

Lemma exec_kstaton_bus : execP kstaton_bus_exp = kstaton_bus''.
Proof.
rewrite /kstaton_bus''.
rewrite 3!execP_letin execP_sample_bern.
congr letin'.
rewrite !execP_if !execP_return !execD_real.
have -> : @execD R _ _ (exp_var "x" (ctx_prf_head "x" Bool [::])) = execD [% {"x"}].
  by congr execD; congr exp_var; exact: Prop_irrelevance.
rewrite execD_var /= /ite_3_10.
have -> : measurable_acc_typ [:: Bool] 0 = @macc0of2 _ _ _ _ by [].
congr letin'.
rewrite execP_score execD_poisson /=.
have -> : (@execD R _ _ (exp_var "r" (ctx_prf_head "r" Real [:: ("x", Bool)])) =
          execD [% {"r"}]).
  by congr execD; congr exp_var; exact: Prop_irrelevance.
rewrite execD_var /=.
have ->/= : measurable_acc_typ [:: Real; Bool] 0 = macc0of2 by [].
congr letin'.
rewrite (execD_var _ "x") /=.
by have -> : measurable_acc_typ [:: Unit; Real; Bool] 2 = macc2of4'.
Qed.


Lemma exec_staton_bus : execD staton_bus_exp =
  existT _ (normalize kstaton_bus'' point)(measurable_fun_mnormalize _).
Proof. by rewrite execD_normalize exec_kstaton_bus. Qed.

End staton_bus.

(* TODO: move *)
Lemma integral_bernoulli {R : realType}
    (p : {nonneg R}) (p1 : (p%:num <= 1)%R) (f : bool -> set bool -> _) U :
  (forall x y, 0 <= f x y) ->
  \int[bernoulli p1]_y (f y ) U =
  p%:num%:E * f true U + (`1-(p%:num))%:E * f false U.
Proof.
move=> f0.
rewrite ge0_integral_measure_sum// 2!big_ord_recl/= big_ord0 adde0/=.
by rewrite !ge0_integral_mscale//= !integral_dirac//= indicT 2!mul1e.
Qed.

Section bernoulli_example.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Import Notations.
Context {R : realType}.

Local Notation "# str" := (@exp_var' R str%string _ _) (in custom expr at level 1).

Let p13 : (1 / 3%:R)%:nng%:num <= 1 :> R. Proof. by rewrite p1S. Qed.

Definition bernoulli12_score := exp_normalize
  [let "x" := Sample {@exp_bernoulli R [::] (1 / 2%:R)%:nng p12} in
   let "r" := if #{"x"} then Score {(1 / 3)}:R else Score {(2 / 3)}:R in
   return #{"x"}].

Lemma exec_bernoulli_score : 
  execD (exp_bernoulli (1 / 3%:R)%:nng p13) = execD bernoulli12_score.
Proof.
apply: eq_execD.
rewrite /bernoulli12_score.
rewrite execD_normalize 2!execP_letin execP_sample_bern execP_if /=.
rewrite execD_var'.
rewrite (execD_var _ "x") !execP_return/= 2!execP_score 2!execD_real /=.
rewrite execD_bernoulli/=.
apply: funext=> g; apply: eq_probability; apply: funext=> U.
rewrite normalizeE.
rewrite !letin'E/=.
under eq_integral.
  move=> x _.
  rewrite !letin'E.
  under eq_integral do rewrite retE /=.
  over.
rewrite !integral_measure_add //=; last first.
  by move=> b _; rewrite integral_ge0.
rewrite !ge0_integral_mscale //=; last 2 first.
  by move=> b _; rewrite integral_ge0.
  by move=> b _; rewrite integral_ge0.
rewrite !integral_dirac// !indicE !in_setT !mul1e.
rewrite iteE/= !ge0_integral_mscale//=.
rewrite ger0_norm// ?divr_ge0 ?ler0n//.
rewrite !integral_indic//= !iteE/= /mscale/=.
rewrite setTI diracE !in_setT !mule1.
rewrite ger0_norm// ?divr_ge0 ?ler0n//.
rewrite -EFinD/= eqe.
rewrite /onem [X in X - _](splitr 1) addrK -mulrDr mulf_eq0.
rewrite mulf_eq0 !oner_eq0/= invr_eq0/= pnatr_eq0/= -mulrDl mulf_eq0 invr_eq0.
rewrite pnatr_eq0/=.
rewrite !letin'E/= !iteE/=.
rewrite !ge0_integral_mscale//=.
rewrite ger0_norm// ?divr_ge0 ?ler0n//.
rewrite !integral_dirac//=.
rewrite !indicE !in_setT /= !mul1e.
rewrite ger0_norm// ?divr_ge0 ?ler0n//.
rewrite (execD_var' "x") (execD_var _ "x")/=.
rewrite /bernoulli/= measure_addE/=.
rewrite /mscale/= !mul1r.
rewrite muleDl//; congr (_ + _)%E;
  rewrite -!EFinM;
  congr (_%:E);
  by rewrite indicE /onem; case: (_ \in _); field.
Qed.

End bernoulli_example.

Section score_fail.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Import Notations.
Context {R : realType}.

Local Notation "# str" := (@exp_var' R str%string _ _) (in custom expr at level 1).

(* lhs *)
Definition scorer (r : {nonneg R}) : exp P [::] Unit := [Score {r%:num}:R].

Definition ex_fail g : @exp R P g Unit :=
  [let "x" := Score {0}:R in return {exp_unit}].

Lemma ex_fail_fail g x U : execP (ex_fail g) x U = fail tt U.
Proof.
rewrite execP_letin execP_score execD_real execP_return execD_unit/=.
rewrite letin'E integral_indic//= /mscale/= normr0 mul0e.
by rewrite /kcomp /kscore /= ge0_integral_mscale//= normr0 mul0e.
Qed.

(* rhs *)
Definition iffail (r : {nonneg R}) (r1 : (r%:num <= 1)%R) : exp P [::] Unit :=
  [let "x" := Sample {exp_bernoulli r r1} in
  if #{"x"} then return {exp_unit} else {ex_fail _}].

Lemma ex_score_fail r (r1 : (r%:num <= 1)%R) :
  execP (scorer r) = execP (iffail r1).
Proof.
rewrite /scorer /iffail.
rewrite execP_score execD_real /= score_fail.
rewrite execP_letin execP_sample_bern execP_if execP_return execD_unit.
set tmp := (execD [# {"x"}]).
have -> : tmp = execD [% {"x"}].
  by congr execD; congr exp_var; exact: Prop_irrelevance.
rewrite execD_var/=.
apply: eq_sfkernel=> /= x U.
rewrite /kcomp/= letin'E/=.
congr integral; apply: funext=> b.
rewrite 2!iteE.
case: b => //=.
by rewrite (@ex_fail_fail [:: ("x", Bool)]).
Qed.

End score_fail.

(* TODO: move *)
Lemma normalize_kdirac (R : realType) d (T : measurableType d) d' (T' : measurableType d') (x : T) (r : T') P :
  normalize (kdirac (measurable_cst r)) P x = \d_r :> probability T' R.
Proof.
apply: eq_probability; apply: funext=> ?.
rewrite normalizeE /= diracE in_setT/=.
by rewrite onee_eq0/= indicE in_setT/= -div1r divr1 mule1.
Qed.

Section normalize_return.
Local Open Scope lang_scope.
Import Notations.
Context (R : realType).

Goal execP [return {1}:R] = ret (kr 1) :> pval R [::] _.
Proof. by rewrite execP_return execD_real. Qed.

Goal projT1 (execD (exp_normalize [return {1}:R])) =
  normalize (ret (kr 1)) point :> dval R [::] _.
Proof. by rewrite execD_normalize execP_return execD_real. Qed.

Lemma exec_normalize_return g x r :
  projT1 (@execD _ g _ (exp_normalize [return {r}:R])) x = \d_r
  :> probability _ R.
Proof.
by rewrite execD_normalize execP_return execD_real/= normalize_kdirac.
Qed.

Goal @ret _ _ _ _ R _ (kr 1) tt [set (1%R : mR R)] = 1%:E.
Proof.
rewrite retE diracE/= mem_set//. Qed.

End normalize_return.
