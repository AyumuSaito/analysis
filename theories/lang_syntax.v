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

Reserved Notation "l |- e -D-> v # mv" (at level 50).
Reserved Notation "l |- e -P-> v" (at level 50).

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
    existT _ _ [the measurableType _ of (projT2 h * projT2 t')%type]
  end.

Inductive stype :=
| sunit : stype
| sbool : stype
| sreal : stype
| spair : stype -> stype -> stype
| sprob : stype -> stype
| sprod : list stype -> stype.

Canonical stype_eqType := Equality.Pack (@gen_eqMixin stype).

Fixpoint typei (t : stype) : {d & measurableType d} :=
  match t with
  | sunit => existT _ _ munit
  | sbool => existT _ _ mbool
  | sreal => existT _ _ (mR R)
  | spair A B => existT _ _
      [the measurableType ((projT1 (typei A), projT1 (typei B)).-prod)%mdisp of
      (projT2 (typei A) * projT2 (typei B))%type]
  | sprob A => existT _ _ (pprobability (projT2 (typei A)) R)
  | sprod l => prod_meas (map typei l)
  end.

Definition typei2 t := projT2 (typei t).

End type_syntax.

Arguments typei {R}.
Arguments typei2 {R}.

Definition context := seq (string * stype)%type.

Section expr.
Variables (R : realType).

(*Fixpoint assoc_get {A : eqType} {B : Type} (a : A) (l : seq (A * B)) : option B :=
  match l with
  | nil => None
  | h :: t => if h.1 == a then Some h.2 else assoc_get a t
  end.*)

Inductive expD : context -> stype -> Type :=
| expWD l st x (e : expD l st) : x \notin l -> expD (x :: l) st
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
| expWP l st x (e : expP l st) : x \notin l -> expP (x :: l) st
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

Fixpoint varof (l : seq (string * stype)) (i : nat) :
  projT2 (typei (sprod (map snd l))) -> projT2 (@typei R (nth sunit (map snd l) i)) :=
  match
    l return (projT2 (typei (sprod (map snd l))) -> projT2 (typei (nth sunit (map snd l) i)))
  with
  | [::] => match i with | O => id | j.+1 => id end
  | _ :: _ => match i with
               | O => fst
               | j.+1 => fun H => varof j H.2
               end
  end.

(*Definition varof (l : seq (string * stype)%type) (i : nat) :
  projT2 (@typei R (sprod (map snd l))) ->
  projT2 (@typei R (nth sunit (map snd l) i)).
revert l i.
fix H 1.
destruct l.
  by destruct i.
destruct i.
simpl.
intro K.
exact: K.1.
simpl.
move=> K.
refine (H _ _ K.2).
Defined.*)

(*Definition varof (l : seq (string * stype)%type) (i : nat) (li : (i < size l)%nat) :
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
Defined.*)

(*Lemma false_index_size (x : string) (l : seq (string * stype)%type) (H : x \in map fst l) :
	(seq.index x (map fst l) < size l)%nat.
Proof. by rewrite -(size_map fst) index_mem. Qed.*)

(*Lemma mvarof (l : seq (string * stype)%type) (i : nat) (*(li : (i < size l)%nat)*) :
  measurable_fun setT (@varof l i (*li*)).
Proof.
revert l i (*li*).
induction l.
  by destruct i.
destruct i.
intro K.
exact: measurable_fun_fst.
move=> K.
apply: (measurable_funT_comp (IHl _) (@measurable_fun_snd _ _ _ _)).
apply: K.
Qed.*)

Lemma mvarof (l : seq (string * stype)%type) (i : nat) :
  measurable_fun setT (@varof l i).
Proof.
elim: l i => //= h t ih [|j]; first exact: measurable_fun_fst.
exact: (measurable_funT_comp (ih _) (@measurable_fun_snd _ _ _ _)).
Qed.

Lemma measurable_fun_normalize d d' (X : measurableType d) (Y : measurableType d') (k : R.-sfker X ~> Y) :
  measurable_fun setT (normalize k point : X -> pprobability Y R).
Proof.
(* have := measurable_kernel k set0 measurable0.
rewrite /normalize /mnormalize.
(* rewrite [X in measurable_fun X](_ : _ = (fun x : X =>
                            if (k x [set: Y] == 0) || (k x [set: Y] == +oo)
                            then fun U : set Y =>point U
                            else fun U : set Y => k x U * ((fine (k x [set: Y]))^-1)%:E)); last first. *)
suff: measurable_fun (T:=X) (U:=pprobability Y R) [set: X]
  (fun x : X =>
   fun U : set Y =>
                           if (k x [set: Y] == 0) || (k x [set: Y] == +oo)
                           then point U
                           else k x U * ((fine (k x [set: Y]))^-1)%:E).
have:= (@measurable_fun_if _ _ _ _ (fun x => _) (fun x U => k x U * ((fine (k x [set: Y]))^-1)%:E) (fun x => (k x [set: Y] == 0) || (k x [set: Y] == +oo))).
(* move=> mX U mU.
rewrite setTI. *)
apply: measurability.
reflexivity.
move=> B [Z [r r01]] [Z0 mZ0 <-{Z}] <-{B}.
rewrite /normalize.
rewrite /mnormalize.
rewrite setTI.
rewrite /mset /preimage /= /mnormalize.
rewrite [X in measurable X](_ : _ = (fun x : X =>
                            if (k x [set: Y] == 0) || (k x [set: Y] == +oo)
                            then fun U : set Y =>point U
                            else fun U : set Y => k x U * ((fine (k x [set: Y]))^-1)%:E) @^-1`
   [set mu | mu Z0 < r%:E]); last first.
  apply/funext => x/=.
  rewrite /mset/= /mnormalize.
  case: ifP => //= ?.
  rewrite diracE.
  case: (point \in Z0) => /=.
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
have := measurable_kernel [the kernel _ _ _ of (normalize k : X -> pprobability Y R)].
rewrite preimage. *)
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

Definition eta1 x (l : context) t
  (f : projT2 (@typei R (sprod (map snd l))) -> projT2 (@typei R t)) :
  projT2 (typei (sprod (map snd (x :: l)))) -> projT2 (@typei R t) := f \o snd.

Lemma meta1 x (l : context) t
    (f : projT2 (@typei R (sprod (map snd l))) -> projT2 (@typei R t))
    (mf : measurable_fun setT f) :
  measurable_fun setT (@eta1 x l t f).
Proof. by apply: (measurable_funT_comp mf); exact: measurable_fun_snd. Qed.

Definition keta1 (x : string * stype) (l : context) t
  (k : R.-sfker (@typei2 R (sprod (map snd l))) ~> @typei2 R t) :
  (@typei2 R (sprod (map snd (x :: l)))) -> {measure set @typei2 R t -> \bar R}
  := k \o snd.

Section kernel_eta1.
Variables (x : string * stype) (l : context) (t : stype)
  (k : R.-sfker (@typei2 R (sprod (map snd l))) ~> @typei2 R t).

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
  (k : R.-sfker (@typei2 R (sprod (map snd l))) ~> @typei2 R t).

Let sk : exists2 s : (R.-ker (@typei2 R (sprod (map snd (x :: l)))) ~> @typei2 R t)^nat,
  forall n, measure_fam_uub (s n) &
  forall x0 U, measurable U -> (@keta1 x l t k) x0 U = kseries s x0 U .
Proof.
have [s hs] := sfinite k.
exists (fun n => @keta1 x l t (s n)).
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
  (k : R.-fker (@typei2 R (sprod (map snd l))) ~> @typei2 R t).

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
  | expWP _ _ _ e _ => free_varsP e
  end.

Inductive evalD : forall (l : context) (T : stype) (e : @expD R l T)
  (f : projT2 (typei (sprod (map snd l))) -> projT2 (typei T)),
  measurable_fun setT f -> Prop :=
| E_unit l :
  l |- exp_unit -D-> cst tt # ktt

| E_bool l b :
  l |- exp_bool b -D-> cst b # kb b

| E_real l r :
  l |- exp_real r -D-> cst r # kr r

| E_pair l (G := sprod (map snd l)) A B e1 f1 mf1 e2 f2 mf2 :
  l |- e1 -D-> f1 # mf1 -> (* (f1 : projT2 (typei G) -> projT2 (typei A)) *)
  l |- e2 -D-> f2 # mf2 -> (* (f2 : projT2 (typei G) -> projT2 (typei B)) *)

  l |- exp_pair e1 e2 -D-> fun x => (f1 x, f2 x) #
  (@measurable_fun_pair _ _ _ (projT2 (typei G)) (projT2 (typei A))
  (projT2 (typei B)) f1 f2 mf1 mf2)
  (*
  ((fun x : projT2 (typei G) => (f1 x, f2 x))
    : projT2 (typei G) -> projT2 (typei (spair A B)))
  *)

| E_var (l : context) (x : string) (*(H : x \in map fst l) *)
(* (H' : assoc_get x l = Some _)  *)
:
  let i := seq.index x (map fst l) in
  l |- exp_var x _ erefl -D-> @varof l i (*(false_index_size H)*) #
  @mvarof l i (*(false_index_size H)*)

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

| E_WD l (t : stype) (e : expD l t) x (xl : x \notin l) f mf :
  (* x.1 \notin free_varsD e ->  *)
  l |- e -D-> f # mf ->
  (x :: l) |- expWD e xl -D-> (@eta1 x l t f) # (@meta1 x l t f mf)

where "l |- e -D-> v # mv" := (@evalD l _ e v mv)

with evalP : forall (l : context) (T : stype),
  expP l T ->
  R.-sfker (projT2 (typei (sprod (map snd l)))) ~> projT2 (typei T) -> Prop :=
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
  ((x, t1) :: l)%SEQ |- e2 -P-> k2 ->
  l |- exp_letin x e1 e2 -P-> letin' k1 k2

| E_WP l (t : stype) (e : expP l t) x (xl : x \notin l) k :
  l |- e -P-> k ->
  (x :: l) |- expWP e xl -P-> [the R.-sfker _ ~> _ of (@keta1 x l t k)]
where "l |- e -P-> v" := (@evalP l _ e v).

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

Lemma evalD_uniq (l : context) (G := sprod (map snd l)) (t : stype)
  (e : expD l t) (u v : projT2 (typei G) -> projT2 (typei t))
  (mu : measurable_fun _ u) (mv : measurable_fun _ v) :
  @evalD R l t e u mu -> evalD e mv -> u = v.
Proof.
move=> hu.
apply: (@evalD_mut_ind R
  (fun (l : _) (G := sprod (map snd l)) (t : stype) (e : expD l t)
  (f : projT2 (typei G) -> projT2 (typei t)) (mf : measurable_fun setT f)
  (h1 : evalD e mf) => forall (v : projT2 (typei G) -> projT2 (typei t))
                              (mv : measurable_fun setT v), evalD e mv -> f = v)
  (fun (l : _) (G := sprod (map snd l)) (t : stype) (e : expP l t)
  (u : R.-sfker projT2 (typei G) ~> projT2 (typei t)) (h1 : evalP e u) =>
  forall (v : R.-sfker projT2 (typei G) ~> projT2 (typei t)),
  evalP e v -> u = v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l t e); last exact: hu.
- move=> l' {}v {}mv.
  inversion 1.
  by do 2 inj H3.
- move=> l' b {}v {}mv.
  inversion 1.
  by do 2 inj H3.
- move=> l' r {}v {}mv.
  inversion 1.
  subst.
  by do 2 inj H3.
- (* pair *) move=> l' G0 A B e1 f1 mf1 e2 f2 mf2 ev1 IH1 ev2 IH2 {}v {}mv H.
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
- (* var *) move=> l' x (*H*) n {}v {}mv.
  inversion 1.
  do 2 inj H7.
  do 2 inj H6.
  done.
  (*by have -> : (n = H0) by exact: Prop_irrelevance.*)
- (* bernoulli *) move=> l' r r1 {}v {}mv.
  inversion 1.
  subst.
  do 2 inj H3.
  subst.
  by have -> : (r1 = r3) by exact: Prop_irrelevance.
- (* poisson *) move=> l' k e0 f mf ev IH {}v {}mv.
  inversion 1.
  subst.
  inj H2.
  do 2 inj H4.
  subst.
  by rewrite (IH _ _ H3).
- (* norm *) move=> l' A e0 k ev IH {}v {}mv.
  inversion 1.
  do 2 inj H2.
  do 2 inj H4.
  subst.
  by rewrite (IH _ H3).
- (* W *) move=> l' A e0 x xl f mf ev IH {}v {}mv H.
  simple inversion H => // ev0.
  subst.
  case: H1 => ? ?.
  subst.
  do 2 inj H3.
  do 2 inj H4.
  rewrite /eta1.
  subst.
  case: H3=> H4.
  do 2 inj H4.
  subst.
  by rewrite (IH _ _ ev0).
- (* sample *) move=> l' r r1 p.
  inversion 1.
  (* do 2 inj H0. *)
  do 2 inj H3.
  subst.
  by have -> : (r1 = r3) by apply: Prop_irrelevance.
- (* if *) move=> l' G0 e0 f1 mf1 e2 k2 e3 k3 ev1 IH1 ev2 IH2 ev3 IH3 k.
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
- (* score *) move=> l' G0 e0 f mf ev IH k H.
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
- (* return *) move=> l' A e0 f mf ev IH k.
  inversion 1.
  subst.
  do 2 inj H5.
  do 2 inj H7.
  subst.
  have ? := IH _ _ H3.
  subst f1.
  by have -> : (mf = mf1) by exact: Prop_irrelevance.
- (* letin *) move=> l' G0 A B x e1 e2 k1 k2 ev1 IH1 ev2 IH2 k.
  inversion 1.
  subst.
  do 2 inj H10.
  do 2 inj H7.
  do 4 inj H8.
  subst.
  by rewrite (IH1 _ H4) (IH2 _ H11).
- move=> l' A e0 x xl k1 ev IH {}k.
  inversion 1.
  subst A.
  do 2 inj H4.
  do 2 inj H5.
  subst.
  by rewrite (IH _ H3).
Qed.

(* TODO: factorize proof *)
Lemma evalP_uniq (l : context) (t : stype) (e : expP l t)
  (u v : R.-sfker typei2 (sprod (map snd l)) ~> typei2 t) :
  evalP e u -> evalP e v -> u = v.
Proof.
move=> hu.
apply: (@evalP_mut_ind R
  (fun (l : _) (G := sprod (map snd l)) (t : stype) (e : expD l t)
    (f : projT2 (typei G) -> projT2 (typei t))
    (mf : measurable_fun setT f) (h1 : evalD e mf) =>
    forall (v : projT2 (typei G) -> projT2 (typei t)) (mv : measurable_fun setT v),
    evalD e mv -> f = v)
  (fun (l : _) (G := sprod (map snd l)) (t : stype) (e : expP l t)
    (u : R.-sfker projT2 (typei G) ~> projT2 (typei t)) (h1 : evalP e u) =>
    forall (v : R.-sfker projT2 (typei G) ~> projT2 (typei t)),
    evalP e v -> u = v)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l t e); last exact: hu.
- move=> l' {}v {}mv.
  inversion 1.
  by do 2 inj H3.
- move=> l' b {}v {}mv.
  inversion 1.
  by do 2 inj H3.
- move=> l' r {}v {}mv.
  inversion 1.
  subst.
  by do 2 inj H3.
- (* pair *) move=> l' G0 A B e1 f1 mf1 e2 f2 mf2 ev1 IH1 ev2 IH2 {}v {}mv H.
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
- (* var *) move=> l' x (*H*) n {}v {}mv.
  inversion 1.
  do 2 inj H7.
  do 2 inj H6.
  done.
  (*by have -> : (n = H0) by exact: Prop_irrelevance.*)
- (* bernoulli *) move=> l' r r1 {}v {}mv.
  inversion 1.
  subst.
  do 2 inj H3.
  subst.
  by have -> : (r1 = r3) by exact: Prop_irrelevance.
- (* poisson *) move=> l' k e0 f mf ev IH {}v {}mv.
  inversion 1.
  subst.
  inj H2.
  do 2 inj H4; clear H5.
  subst.
  by rewrite (IH _ _ H3).
- (* norm *) move=> l' A e0 k ev IH {}v {}mv.
  inversion 1.
  do 2 inj H2.
  do 2 inj H4.
  subst.
  by rewrite (IH _ H3).
- (* W *) move=> l' A e0 x xl f mf ev IH {}v {}mv H.
  simple inversion H => // ev0.
  subst.
  case: H1 => ? ?.
  subst.
  do 2 inj H3.
  do 2 inj H4.
  rewrite /eta1.
  subst.
  case: H3=> H4.
  do 2 inj H4.
  subst.
  by rewrite (IH _ _ ev0).
- (* sample *) move=> l' r r1 ev.
  inversion 1.
  (* do 2 inj H0. *)
  do 2 inj H3.
  subst.
  by have -> : r1 = r3 by exact: Prop_irrelevance.
- (* if *) move=> l' G0 e0 f1 mf1 e2 k2 e3 k3 ev1 IH1 ev2 IH2 ev3 IH3 k.
  inversion 1.
  inj H0.
  do 2 inj H1.
  do 2 inj H2.
  subst.
  do 2 inj H5.
  have ? := IH1 _ _ H6.
  subst f1.
  have -> : mf1 = mf by exact: Prop_irrelevance.
  by rewrite (IH2 _ H7) (IH3 _ H8).
- (* score *) move=> l' G0 e0 f mf ev IH k H.
  simple inversion H => // ev0.
  subst.
  do 2 inj H4.
  do 2 inj H3.
  injection H3 => H5.
  inj H5.
  subst.
  have ? := IH _ _ ev0.
  subst f0.
  by have -> : mf = mf0 by exact: Prop_irrelevance.
- (* return *) move=> l' A e0 f mf ev IH k.
  inversion 1.
  subst.
  do 2 inj H5.
  do 2 inj H7.
  subst.
  have ? := IH _ _ H3.
  subst f1.
  by have -> : mf = mf1 by exact: Prop_irrelevance.
- (* letin *) move=> l' G0 A B x e1 e2 k1 k2 ev1 IH1 ev2 IH2 k.
  inversion 1.
  subst.
  do 2 inj H10.
  do 2 inj H7.
  do 4 inj H8.
  subst.
  by rewrite (IH1 _ H4) (IH2 _ H11).
- move=> l' A e0 x xl k1 ev IH {}k.
  inversion 1.
  subst A.
  do 2 inj H4.
  do 2 inj H5.
  subst.
  by rewrite (IH _ H3).
Qed.

Lemma evalD_full (l : context) (t : stype) : forall e,
  (* {subset (free_varsD e) <= map fst l} -> *)
  exists f (mf : measurable_fun _ f), @evalD R l t e f mf.
Proof.
move=> e.
apply: (@expD_mut_ind R
  (fun (l : context) (t : stype) (e : expD l t) =>
    (*{subset (free_varsD e) <= map fst l} ->*)
    exists f (mf : measurable_fun _ f), evalD e mf)
  (fun (l : context) (t : stype) (e : expP l t) =>
    (* {subset (free_varsP e) <= map fst l} -> *)
    exists k, evalP e k) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l t e).
- move=> l0 st x e1 H1 xl0.
  destruct H1 as [f [mf]].
  exists (eta1 f).
  exists (meta1 mf).
  exact/E_WD.
- by do 2 eexists; apply/E_unit.
- by do 2 eexists; apply/E_bool.
- by do 2 eexists; apply/E_real.
- move=> l0 t1 t2 e1 H1 e2 H2.
  destruct H1 as [f1 [mf1]].
  destruct H2 as [f2 [mf2]].
  exists (fun x => (f1 x, f2 x)).
  eexists.
  exact: E_pair.
- move=> l0 x t0 (*xl0*) t0E.
  subst t0.
  eexists.
  eexists.
  by apply/E_var.
- move=> r r1.
  eexists.
  eexists.
  exact: E_bernoulli.
- move=> l0 k e0 H.
  destruct H as [f [mf]].
  exists (poisson k \o f).
  exists (measurable_funT_comp (mpoisson k) mf).
  exact: E_poisson.
- move=> l0 t0 e0 H.
  destruct H as [k].
  exists (normalize k point).
  exists (measurable_fun_normalize k).
  exact: E_norm.
- move=> l0 st x e1 H1 xl0.
  destruct H1 as [k].
  exists (@keta1 R x l0 st k).
  exact/E_WP.
- move=> l0 t0 e1 H1 e2 H2 e3 H3.
  destruct H1 as [f [mf]].
  destruct H2 as [k2].
  destruct H3 as [k3].
  exists (ite mf k2 k3).
  exact: E_ifP.
- move=> l0 t1 t2 x e1 H1 e2 H2.
  destruct H1 as [k1 ev1].
  destruct H2 as [k2 ev2].
  subst.
  exists (letin' k1 k2).
  exact: E_letin.
- move=> l0 r r1.
  exists (sample [the pprobability _ _ of bernoulli r1]).
  exact: E_sample.
- move=> l0 e0 [f [mf f_mf]].
  exists (score mf).
  exact: E_score.
- move=> l0 t0 e0 [f [mf f_mf]].
  exists (ret mf).
  exact: E_return.
Qed.

(* move=> l0 st x e1 H1 xl0.
have h1 : {subset free_varsD e1 <= map fst (x :: l0)}.
  move=> x0 x0e1.
  (* have [|] := eqVneq x0 x.1.
  have /= := el x0.
  have : (x0 \in free_varsD (expWD (x:=x) e1 xl0)).
  rewrite /free_varsD.
  fold (free_varsD e1).
  rewrite inE =>/orP[|//]. *)
  admit.
have h2 : {subset l0 <= x :: l0}.

move: H1 => /(_ _ h1) => H1.
destruct H1 as [f [mf]].
exists (eta1 f).
eexists.
(* exists (meta1 f). *)
exact/E_WD.
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
move=> l0 st x e1 H1 xl0 el.
have h1 : {subset free_varsP e1 <= map fst l0}.
  move=> x0 x0e0.
  admit.
  (* by apply: el => /=. *)
move: H1 => /(_ h1) => H1.
destruct H1 as [k].
exists (@eta_kernel R x l0 st k).
exact/E_WP.
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
Admitted. *)

Lemma evalP_full (l : context) (t : stype) e :
  (* {subset (free_varsP e) <= map fst l} -> *)
  exists (k : R.-sfker _ ~> _), @evalP R l t e k.
Proof.
apply: (@expP_mut_ind R
  (fun (l : context) (t : stype) (e : expD l t) =>
    (* {subset (free_varsD e) <= map fst l} -> *)
    exists f (mf : measurable_fun _ f), evalD e mf)
  (fun (l : context) (t : stype) (e : expP l t) =>
    (* {subset (free_varsP e) <= map fst l} -> *)
    exists k, evalP e k) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l t e).
- move=> l0 st x e1 H1 xl0.
  destruct H1 as [f [mf]].
  exists (eta1 f).
  exists (meta1 mf).
  exact/E_WD.
- by do 2 eexists; apply/E_unit.
- by do 2 eexists; apply/E_bool.
- by do 2 eexists; apply/E_real.
- move=> l0 t1 t2 e1 H1 e2 H2.
  destruct H1 as [f1 [mf1]].
  destruct H2 as [f2 [mf2]].
  exists (fun x => (f1 x, f2 x)).
  eexists; exact: E_pair.
- move=> l0 x t0 (*xl0*) t0E.
  subst t0.
  eexists.
  eexists.
  by apply/E_var.
- move=> r r1.
  eexists.
  eexists.
  exact: E_bernoulli.
- move=> l0 k e0 H.
  destruct H as [f [mf]].
  exists (poisson k \o f).
  exists (measurable_funT_comp (mpoisson k) mf).
  exact: E_poisson.
- move=> l0 t0 e0 H.
  destruct H as [k].
  exists (normalize k point).
  exists (measurable_fun_normalize k).
  exact: E_norm.
- move=> l0 st x e1 H1 xl0.
  destruct H1 as [k].
  exists (@keta1 R x l0 st k).
  exact/E_WP.
- move=> l0 t0 e1 H1 e2 H2 e3 H3.
  destruct H1 as [f [mf]].
  destruct H2 as [k2].
  destruct H3 as [k3].
  exists (ite mf k2 k3).
  exact: E_ifP.
- move=> l0 t1 t2 x e1 H1 e2 H2.
  destruct H1 as [k1 ev1].
  destruct H2 as [k2 ev2].
  subst.
  exists (letin' k1 k2).
  exact: E_letin.
- move=> l0 r r1.
  exists (sample [the pprobability _ _ of bernoulli r1]).
  exact: E_sample.
- move=> l0 e0 H.
  destruct H as [f [mf]].
  exists (score mf).
  exact: E_score.
- move=> l0 t0 e0 H.
  destruct H as [f [mf]].
  exists (ret mf).
  exact: E_return.
Qed.

(* admit.
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
admit.
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
Admitted. *)

(* Variables (A B C : stype).
Definition X := @typei2 R A.
Definition Y := @typei2 R B.
Definition Z := @typei2 R C. *)

Definition execP l t (e : @expP R l t) (H : {subset free_varsP e <= map fst l}):
  R.-sfker (@typei2 R (sprod (map snd l))) ~> @typei2 R t.
Proof.
have /cid h := @evalP_full l t e.
exact: (proj1_sig h).
Defined.

Definition execP_cst (l l' : context) (r : R) :
  R.-sfker (@typei2 R (sprod (map (@snd string stype) l'))) ~> @typei2 R sreal.
Proof.
have H0 : {subset free_varsP (exp_return (exp_real r) : expP [::] _) <= map (@fst string stype) l'}.
  by move=> x /=.
have /cid h := @evalP_full l' _ (exp_return (exp_real r)).
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
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l t e).
- move=> l0 st x e0 H1 xl H2.
(* apply (expWD e0 x). *)
admit.
move=> ? ?; exact: exp_unit.
move=> ? b ?; exact: (exp_bool b).
move=> ? r ?; exact: (exp_real r).
move=> t1 t2 ? e1 t1nil e2 t2nil H.
rewrite /= in H.
apply: exp_pair.
apply: t1nil.
(* by destruct (free_varsD e1).
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
admit.
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
move=> ? t1 t2 x e1 h1 e2 h2 H. *)
Abort.

(* Variables (dT : measure_display) (T : measurableType dT).
(* Definition m := fun A => (_ : {measure set (@typei2 R A) -> \bar R}). *)

Axiom same_expP : forall (l l' : context) (T : stype) (e : @expP R T l)
  (e' : @expP R T l'), Prop. *)


Lemma evalP_uni_new x r
  (u : R.-sfker munit ~> mR R)
  (v : R.-sfker projT2 (typei (sprod [seq i.2 | i <- [:: (x, sreal)]])) ~> mR R) :
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

Require Import JMeq.

Obligation Tactic := idtac.

Program Fixpoint wP {st} {l : context} (x : string * stype) (e : @expP R l st)
  : @expP R (x :: l) st :=
match e with
| exp_return l0 _ e0 => @exp_return R (x :: l0) _ (wD x e0)
| exp_if l0 _ e1 e2 e3 => @exp_if R (x :: l0) _ (wD x e1) (wP x e2) (wP x e3)
| exp_letin l0 _ _ x0 e1 e2 => @exp_letin R (x :: l0) _ _ x0 (wP x e1) (wP _ e2)
| exp_sample_bern l0 _ _ => _
| exp_score l0 e1 => _
| expWP l0 _ x e0 xl => _
end with wD {st} {l : context} x (e : @expD R l st) :=
match e with
| _ => _
end.
Next Obligation.
Admitted.
Next Obligation.
move=> st l x e l0 ? ? x0 e1 e2 l0l ? ?.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Definition vx : R.-sfker munit ~> mR R := execP_cst [:: ("x", sreal)] [::] 1.
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

Definition vy' : R.-sfker munit ~> mR R := execP_cst  [::] [::] 2.
Definition VY z : set (mR R) -> \bar R := vy' z.
Let VY0 z : (VY z) set0 = 0. Proof. by []. Qed.
Let VY_ge0 z x : 0 <= (VY z) x. Proof. by []. Qed.
Let VY_semi_sigma_additive z : semi_sigma_additive (VY z).
Proof. exact: measure_semi_sigma_additive. Qed.
HB.instance Definition _ z := @isMeasure.Build _ R (mR R) (VY z) (VY0 z)
  (VY_ge0 z) (@VY_semi_sigma_additive z).
Let sfinVY z : sfinite_measure (VY z). Proof. exact: sfinite_kernel_measure. Qed.
HB.instance Definition _ z := @Measure_isSFinite_subdef.Build _ (mR R) R
  (VY z) (sfinVY z).

End eval_prop.

Definition context_of_expP R (l : context) (s : stype) (e : @expP R l s) := l.

Declare Custom Entry expr.
Notation "[ e ]" := e (e custom expr at level 5).
Notation "x ':r'" := (@exp_real _ _ x%R) (in custom expr at level 1).
Notation "'Ret' x" := (@exp_return _ _ _ x) (in custom expr at level 2).
Notation "% x" := (@exp_var _ _ x _ erefl) (in custom expr at level 1).
Notation "%WP x # e" := (@expWP _ _ _ (x, _) e erefl) (in custom expr at level 1).
Notation "( x , y )" := (exp_pair x y) (in custom expr at level 1).
Notation "'Let' x '<~' e 'In' f" := (exp_letin x e f)
  (in custom expr at level 3,
   x constr,
   (* e custom expr at level 2, *)
   f custom expr at level 3,
   left associativity).
(*Notation "( x )" := x (in custom expr, x at level 50).*)
Notation "'If' e1 'Then' e2 'Else' e3" := (exp_if e1 e2 e3) (in custom expr at level 1).
Notation "{ x }" := x (in custom expr, x constr).
Notation "x" := x (in custom expr at level 0, x ident).

Section letinC.
Variable R : realType.

(* Check [Let "x" <~ Ret {1}:r In Ret %{"x"}].
Check [Let "x" <~ Ret {1}:r In
        Let "y" <~ Ret {2}:r In
        Ret (%{"x"} # {[:: ("y", sreal); ("x", sreal)]}, %{"y"} # {[:: ("y", sreal); ("x", sreal)]})]. *)

(* Lemma letinC12 v1 v2 t M :
  let x := "x" in
  let y := "y" in
  (* let s1 := [:: (y, sreal); (x, sreal)] in
  let s2 := [:: (x, sreal); (y, sreal)] in *)
  measurable M ->
  [::] |- [Let x <~ Ret {1}:r In
           Let y <~ Ret {2}:r In
           Ret (%x, %y)] : @expP R _ _ -P-> v1
  ->
  [::] |- [Let y <~ Ret {2}:r In
           Let x <~ Ret {1}:r In
           Ret (%x, %y)] -P-> v2 ->
  v1 t M = v2 t M.
Proof.
set d := (x in (projT1 x).-measurable _).
rewrite -/d in M v1 v2 *.
move=> x y mM ev1 ev2.
pose vx : R.-sfker munit ~> mR R := execP_cst [:: (x, sreal)] [::] 1.
pose vy : R.-sfker [the measurableType _ of (mR R * munit)%type] ~> mR R :=
  execP_cst [:: (x, sreal)] [:: (x, sreal)] 2.
have -> : v1 =
  letin' (vx) (letin' (vy) (ret (measurable_fun_pair var2of3' var1of3'))).
apply: (evalP_uniq ev1).
apply/E_letin /E_letin.
rewrite /vx /execP_cst /sval/=.
by case: cid => // ? h.
rewrite /vy /execP_cst /sval/=.
by case: cid => // ? h.
apply/E_return /E_pair.
have -> : (var2of3' = (@mvarof R [:: (y, sreal); (x, sreal)] 1 (false_index_size (_ : (x \in map fst [:: (y, sreal); (x, sreal)]))))) by [].
apply/(@E_var R [:: (y, sreal); (x, sreal)] x).
have -> : (var1of4' = (@mvarof R [:: (y, sreal); (x, sreal)] 0 (false_index_size (_ : (y \in map fst [:: (y, sreal); (x, sreal)]))))) by [].
apply/(@E_var R [:: (y, sreal); (x, sreal)] y is_true_true).
pose vy' : R.-sfker munit ~> mR R := execP_cst  [::] [::] 2.
pose vx' : R.-sfker [the measurableType _ of (mR R * munit)%type] ~> mR R :=    execP_cst [:: (y, sreal)] [:: (y, sreal)] 1.
have -> : v2 = letin' (vy') (letin' (vx') (ret (measurable_fun_pair var1of3' var2of3'))).
apply: (evalP_uniq ev2).
apply/E_letin /E_letin.
rewrite /vy' /execP_cst /sval/=.
case: cid => //.
rewrite /vx' /execP_cst /sval/=.
case: cid => //.
apply/E_return /E_pair.
have -> : (var1of3' = (@mvarof R [:: (x, sreal); (y, sreal)] 0 (false_index_size (_ : (x \in map fst [:: (x, sreal); (y, sreal)]))))) by [].
apply/(@E_var R [:: (x, sreal); (y, sreal)] x is_true_true).
have -> : (var2of3' = (@mvarof R [:: (x, sreal); (y, sreal)] 1 (false_index_size (_ : (y \in map fst [:: (x, sreal); (y, sreal)]))))) by [].
apply/(@E_var R [:: (x, sreal); (y, sreal)] y is_true_true).
apply: letin'C; last by [].
move=> x0 t0.
rewrite (@evalP_uni_new _ y 1 vx vx'); last 2 first.
  rewrite /vx /execP_cst /sval/=.
  by case: cid.
  rewrite /vx' /execP_cst /sval/=.
  by case: cid.
  by [].
move=> x0 t0.
  rewrite /vy /vy' /execP_cst /sval/=.
  case: cid => sy.
  case: cid => sy'.
  move=> er1 er2.
  apply/esym/evalP_uni_new.
  exact: er2.
  exact: er1.
Qed. *)

(* Lemma evalP_uni_new x r
  (u : R.-sfker munit ~> mR R)
  (v : R.-sfker prod_meas_obligation_2 prod_meas
                (existT [eta measurableType] default_measure_display (mR R))
                [::] ~> mR R) :
  evalP (exp_return (exp_real r) : expP [::] sreal) u ->
  evalP (exp_return (exp_real r) : expP [:: (x, sreal)] sreal) v ->
  forall x0 t, v (x0, t) = u t. *)

Ltac inj H := apply Classical_Prop.EqdepTheory.inj_pair2 in H.

Lemma evalP_uniq_sub (l : context) (st : stype) e (u1 : R.-sfker _ ~> _)
  (* (u1' : R.-sfker prod_meas_obligation_2 prod_meas
         (existT [eta measurableType] _ (typei2 st)) _ ~> _)  *)
  (xtl : ("x", st) \notin l) M y0 t :
  let x := "x" in
  (* let y := "y" in *)
  x \notin free_varsP e ->
  measurable M ->
  l |- e -P-> u1 ->
  (* evalP ([e1'] : expP [:: (y, st)] st) u1' -> *)
  ((x, st) :: l)%SEQ |- (@expWP R l st (x, st) e xtl) : expP ((x, st) :: l)%SEQ st -P-> (keta1 u1) ->
  u1 t M = (@keta1 R (x, st) _ _ u1) (y0, t) M.
Proof.
move=> x xNe1 mst.
move=> hu.
by rewrite /keta1 /=.
(*
apply: (@evalP_mut_ind R
  (fun (l : _) (st : stype) (e : expD l st) (f : projT2 (typei _) -> projT2 (typei st)) (mf : measurable_fun setT f) (h1 : l |- e -D-> f # mf) =>
    forall (xtl : (x, st) \notin l) M y0 t, ((x, st) :: l)%SEQ |- (@expWD R l st (x, st) e xtl) -D-> (@eta1 R (x, st) l st f) # (meta1 mf) -> f t = (@eta1 R (x, st) l st f) (y0, t)
    )
  (fun (l : _) (st : stype) (e : expP l st) (u : R.-sfker _ ~> projT2 (typei st)) (h1 : evalP e u) =>
    forall (xtl : (x, st) \notin l) M y0 t, ((x, st) :: l)%SEQ |- (@expWP R l st (x, st) e xtl) -P-> (@keta1 R (x, st) l st u) -> u t M = (@keta1 R (x, st) l st u) (y0, t) M)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l st e); last exact: hu.
move=> l' ? ? ? ?.
by inversion 1.*)
Qed.

Lemma letinC ta tb (l0 := [:: ("a", ta); ("b", tb)]) st
  (e1 : @expP R l0 st) (e2 : expP l0 st) v1 v2 :
  "x" \notin free_varsP e2 ->
  "y" \notin free_varsP e1 ->
  l0 |- [Let "x" <~ e1 In
         Let "y" <~ %WP {"x"} # e2 In
         Ret (%{"x"}, %{"y"})] -P-> v1
  ->
  l0 |- [Let "y" <~ e2 In
         Let "x" <~ %WP {"y"} # e1 In
         Ret (%{"x"}, %{"y"})] -P-> v2 ->
  v1 = v2.
Admitted.

(*Lemma letinC (l : context) st v1 v2 t M (e1 : @expP R l st) (e2 : expP l st)
(Hx1 : "x" \in map fst ([:: ("y", st); ("x", st)] ++ l)%SEQ)
(Hy1 : "y" \in map fst ([:: ("y", st); ("x", st)] ++ l)%SEQ)
(Hx2 : "x" \in map fst ([:: ("x", st); ("y", st)] ++ l)%SEQ)
(Hy2 : "y" \in map fst ([:: ("x", st); ("y", st)] ++ l)%SEQ)
(xtl : ("x", st) \notin l) (ytl : ("y", st) \notin l) :
  let x := "x" in
  let y := "y" in
  "x" \notin free_varsP e2 ->
  "y" \notin free_varsP e1 ->
  measurable M ->
  l |- [Let x <~ e1 In
        Let y <~ {(@expWP R l st (x, st) e2 xtl)} In
        Ret (%x # Hx1, %y # Hy1)] : @expP R _ _ -P-> v1
  ->
  l |- [Let y <~ e2 In
        Let x <~ {(@expWP R l st (y, st) e1 ytl)} In
        Ret (%x # Hx2, %y # Hy2)] -P-> v2 ->
  v1 t M = v2 t M.
Proof.
rewrite /=.
Admitted.*)

End letinC.

Section example.

Local Open Scope ring_scope.
Variables (R : realType).

Example __ : @evalD R [::] _ [{3}:r] (cst 3) (kr 3).
Proof. apply/E_real. Qed.

Example ex_ret : @evalP R [::] _ [Ret {3}:r] (ret (kr 3)).
Proof. apply/E_return/E_real. Qed.

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

Example pgm1 := exp_norm (
  [Let "x" <~ {exp_sample_bern [::] (2 / 7%:R)%:nng p27} In
   Let "r" <~ If %1{"x"} Then Ret {3}:r Else Ret {10}:r In
   Let "_" <~ {exp_score (exp_poisson 4 [%1{"r"}])} In
   Ret %1{"x"}]).

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
- by apply/E_sample.
- apply/E_ifP.
  + rewrite /exp_var' /=.
    set l := (X in X |- _ -D-> _ # _).
    rewrite (_ : left_pf _ _ _ = erefl) //.
    rewrite (_ : var1of2 = @mvarof R l 0)//.
    exact: (@E_var R l "x").
  + by apply/E_return /E_real.
  + by apply/E_return /E_real.
- apply/E_score /E_poisson.
  set l := (X in X |- _ -D-> _ # _).
  rewrite /exp_var'/=.
  rewrite (_ : left_pf _ _ _ = erefl) //.
  rewrite (_ : var1of2 = @mvarof R l 0)//.
  exact: (@E_var R l "r").
- apply/E_return.
  set l := (X in X |- _ -D-> _ # _).
  rewrite /exp_var'/=.
  rewrite (_ : right_pf _ _ _ = erefl) //.
  rewrite (_ : var3of4' = @mvarof R l 2)//.
  exact: (@E_var R l "x").
Qed.

End example.