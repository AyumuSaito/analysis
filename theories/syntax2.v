From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure fsbigop numfun lebesgue_integral kernel.
Require Import prob_lang.

Set Implicit Arguments.
Implicit Types V : Set.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Require Import String ZArith.
Local Open Scope string.

Section string_eq.

Definition string_eqMixin := @EqMixin string eqb eqb_spec.
Canonical string_eqType := EqType string string_eqMixin.

End string_eq.

Section syntax.
Variables (R : realType).

Inductive Ty : Set :=
| TyReal
| TyBool
| TyUnit
| TyPair : Ty -> Ty -> Ty
| TyProb : Ty -> Ty.

Inductive expD : Type :=
| Var  : string -> expD
| Unit : expD
| Bool : bool -> expD
| Real : R -> expD
| Plus : expD -> expD -> expD
| Pair : expD -> expD -> expD
(* | val_unif : val *)
| Bernoulli : {nonneg R} -> expD
| Poisson : nat -> expD -> expD
| Norm : expP -> expD
(* | exp_if : forall z, expD -> exp z -> exp z -> exp z *)
with expP :=
| If : expD -> expP -> expP -> expP
| Letin : string -> expP -> expP -> expP
| Sample : expD -> expP
| Score : expD -> expP
| Return : expD -> expP.

Definition Env := seq (string * Type)%type.

Definition Env' := seq (string * forall d, measurableType d)%type.

Section value.
Variables (d d1 : _) (A : measurableType d) (A1 : measurableType d1).
(* 
Inductive value : forall {dG dT} {G : measurableType dG} {T : measurableType dT}, Set :=
| VReal dG {G : measurableType dG} : {f : G -> R | measurable_fun setT f} -> Val
| VBool dG {G : measurableType dG} : {f : G -> bool | measurable_fun setT f} -> Val
| VUnit dG {G : measurableType dG} : {f : G -> unit | measurable_fun setT f} -> Val
| VPair :
  Val v1
(* | VPair dG {G : measurableType dG} dT1 dT2 (T1 : measurableType dT1) (T2 : measurableType dT2) : @Val _ _ G T1 -> @Val _ _ G T2 -> @Val _ _ G [the measurableType _ of (T1 * T2)%type] *)
(* | VId dX dY (X : measurableType dX) (Y : measurableType dY) : {f : (X * Y)%type -> A1 | measurable_fun setT f} -> Val *)
. 
*)

Inductive value : expD -> Prop :=
| VReal : forall r, value (Real r)
| VPair : forall v1 v2,
  value v1 -> value v2 ->
  value (Pair v1 v2)
.

End value.

Section eval.
Import Notations.
Definition typ2 {d1 d2} (T1 : measurableType d1) (T2 : measurableType d2)
(i : nat) : {d & measurableType d} :=
  if i == O then existT _ d1 T1 else existT _ d2 T2.

Definition var_i_of2 {dA dB} {A : measurableType dA} {B : measurableType dB} (i : nat)
    : {f : [the measurableType _ of (A * B)%type] -> projT2 (typ2 A B i) | measurable_fun setT f} :=
  match i with
  | 0 => exist (fun x => measurable_fun setT x) (_ : A * B -> A) var1of2
  | _ => exist (fun x => measurable_fun setT x) (snd : A * B -> B) var2of2
  end.

(* Variables (dG dT : _) (G : measurableType dG) (T : measurableType dT).
Variables (dG1 : _) (G1 : measurableType dG1). *)
Reserved Notation "[ G |- a ====> v ]".

Inductive EvalD : Env -> expD -> expD -> Prop :=
| EReal : forall E r, 
  EvalD E (Real r) (Real r)

| EPlusl : forall E e1 e1' e2,
  EvalD E e1 e1' ->
  (* EvalD E e2 e2' -> *)
  EvalD E (Plus e1 e2) (Plus e1' e2) 

| EPlusr : forall E v1 e2 e2',
  value v1 ->
  EvalD E e2 e2' ->
  EvalD E (Plus v1 e2) (Plus v1 e2')

| EPlus : forall E r1 r2,
  EvalD E (Plus (Real r1) (Real r2)) (Real (r1 + r2))

| EBool : forall E b,
  EvalD E (Bool b) (Bool b)
(* | EBool : forall dG G E b, 
  @EvalD dG G _ mbool E (exp_bool b) (VBool _)
| EUnit : forall dG G E,
  @EvalD dG G _ munit E (exp_unit) VUnit *)
with EvalP : Env -> expP -> expP -> Prop :=
| ERet : forall E e1 e1',
  EvalD E e1 e1' ->
  EvalP E (Return e1) (Return e1')

.

Definition relation X := X -> X -> Prop.

Inductive multi {X:Type} (r : relation X) : relation X :=
  | multi_refl  : forall (x : X), multi r x x
  | multi_step : forall (x y z : X),
                    r x y ->
                    multi r y z ->
                    multi r x z.

Notation multistep := (multi (EvalP [::])).

Definition ex1 := Return (Plus (Real 1) (Real 2)).
Definition ex1' := Return (Real 3).

Lemma __ : multistep ex1 ex1'.
Proof.
rewrite/ex1 /ex1'.
apply/multi_step.
apply/ERet.
apply/EPlus.
apply/multi_refl.
Qed.


(*
Inductive EvalD : forall dG (G : measurableType dG) dT (T : measurableType dT) (E : Env) (e : expD), expD -> Prop :=
| EBool : forall dG G E b, 
  @EvalD dG G _ mbool E (exp_bool b) (@VBool _ _ G _ (exist _ (cst b) (kb b)))
| EUnit : forall dG G E, 
  @EvalD dG G _ munit E (exp_unit) (@VUnit _ _ G _ (exist _ (cst tt) ktt)) *)
(* | EPair : forall dG G dA A dB B E e1 e2 v1 v2,
  @EvalD dG G dA A E e1 v1 ->
  @EvalD dG G dB B E e2 v2 ->
  @EvalD dG G _ _ E (exp_pair e1 e2) (VPair v1 v2) *)
(* | EVar2 : forall (E : Env) x dX dY (X : measurableType dX) (Y : measurableType dY),
  let i := seq.index x (map fst E) in
  EvalD E (exp_var x) (@VId _ _ _ _ _ _ [the measurableType _ of (X * Y)%type] (projT2 (typ2 X Y i)) (var_i_of2 i.+1)) *)
.
(* where "[G |- a ==> v]" := (Eval G a v). *)

End syntax.

(* Import Notations.

Section check.
Variable (R : realType).
Check sample (bernoulli p27) : R.-sfker _ ~> mbool.
Check (sample (bernoulli p27) : R.-sfker munit ~> mbool) tt setT.
Check ite (kb true) (ret k3) (ret k10) : R.-sfker munit ~> (mR R).
Check @score _ _ _ (poisson 4) _ : R.-sfker (mR R) ~> munit.
Check letin (sample (bernoulli p27)) (ret var1of2).
Check letin.
Check ret.

End check.

Section bind.
Variables (d1 d2 d3 : _) (X : measurableType d1) (Y : measurableType d2)
          (Z : measurableType d3) (R : realType).
Definition ret' {f : X -> Y} : measurable_fun setT f -> R.-sfker X ~> Y := ret.
Definition bind' (k : R.-sfker X ~> Y) {f : Y -> Z} (l : measurable_fun setT f -> R.-sfker Y ~> Z) : R.-sfker X ~> Z := letin k (ret var1of2).

End bind. *)

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

End expression.

Arguments exp_unit {R}.
Arguments exp_bool {R}.
Arguments exp_var {R}.

Section context.

Definition context := seq (string * Type)%type.

Definition context' := seq (string * forall d, measurableType d)%type.

End context.

Import Notations.

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

Local Open Scope ring_scope.

Definition pgm1 : expP R := exp_sample (exp_bernoulli (2 / 7%:R)%:nng).

Example tc_1 : type_checkP [::] pgm1 bool.
Proof. apply/tc_sample /tc_bernoulli. Qed.

Definition pgm2 : expP R := exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng)) (exp_return (exp_var "x")).

Example tc_2 : type_checkP [::] pgm2 bool.
Proof.
apply/(@tc_letin _ _ _ _ bool).
apply/tc_sample /tc_bernoulli.
apply/tc_return /(@tc_var [::] "x").
Qed.

Example pgm3 : expD R := exp_norm (
  exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng)) (
  exp_letin "r" (exp_if (exp_var "x") (exp_return (exp_real 3%:R)) (exp_return (exp_real 10%:R))) (
  exp_letin "_" (exp_score (exp_poisson 4 (exp_var  "r"))) (
  exp_return (exp_var "x"))))).

Example tc_3 : type_checkD [::] pgm3 (probability mbool R).
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

(* Inductive type :=
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
  end. *)

(* Set Printing All.
Definition execD (l : seq (string * type)%type) (e : expD) : forall d (A : measurableType d), {f : A -> (typ_of_exp l e) | measurable_fun setT f} :=
  match e in expD
  return forall d (A : measurableType d), {f : A -> (typ_of_exp l e) | measurable_fun setT f}
  with
  | exp_var v => fun d A => @exist _ _ _ var1of2
  | exp_real r => fun d A => @exist _ _ (@cst A (mR R) r) (kr r)
  | exp_bool b => fun d A => @exist _ _ (@cst A mbool b) (kb b)
  | exp_unit => fun _ _ => @exist _ _ _ ktt
  (* | _ => fun=> ktt *)
  end. *)

Notation var1of4 := (measurable_fun_comp (@measurable_fun_fst _ _ _ _)
  (measurable_fun_comp (@measurable_fun_fst _ _ _ _)
  (@measurable_fun_fst _ _ _ _))).
Notation var2of4 := (measurable_fun_comp (@measurable_fun_snd _ _ _ _)
  (measurable_fun_comp (@measurable_fun_fst _ _ _ _)
  (@measurable_fun_fst _ _ _ _))).
Notation var3of4 := (measurable_fun_comp (@measurable_fun_snd _ _ _ _)
  (@measurable_fun_fst _ _ _ _)).
Notation var4of4 := (@measurable_fun_snd _ _ _ _).

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

Definition var_i_of4 {dA dB dC dD} {A : measurableType dA} {B : measurableType dB} {C : measurableType dC} {D : measurableType dD} (i : nat)
  : {f : [the measurableType _ of (A * B * C * D)%type] -> projT2 (typ4 A B C D i) | measurable_fun setT f} :=
  match i with
  | 0 => exist (fun x => measurable_fun setT x) (_ : A * B * C * D -> A) var1of4
  | 1 => exist (fun x => measurable_fun setT x) (_ : A * B * C * D -> B) var2of4
  | 2 => exist (fun x => measurable_fun setT x) (_ : A * B * C * D -> C) var3of4
  | _ => exist (fun x => measurable_fun setT x) (_ : A * B * C * D -> D) var4of4
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

Eval vm_compute in prod_meas (existT _ _ munit :: [::]).

Eval vm_compute in size (existT _ _ munit :: [::]).

Lemma prod_meas_size_1 (l : list {d & measurableType d}) : size l = 1%N ->
  exists d (T : measurableType d), prod_meas l = existT _ _ [the measurableType _ of (T * munit)%type].
Proof.
destruct l => //.
destruct l => //.
destruct s => /= _.
exists x, t.
rewrite /=.
rewrite /prod_meas_obligation_1/=.
rewrite /prod_meas_obligation_2/=.
done.
Qed.

Lemma prod_meas_size_2 (l : list {d & measurableType d}) : size l = 2%N ->
  exists d (T : measurableType d) d' (T' : measurableType d'), prod_meas l = existT _ _ [the measurableType _ of (T * T' * munit)%type].
Admitted.

(* From Equations Require Import Equations.
Obligation Tactic := idtac. *)

(*
Equations? product_type (h : {d & measurableType d}) (t : seq {d & measurableType d}) : Type by wf (size t) lt :=
  product_type h [::] := projT2 h;
  product_type h (t1 :: t1s) := product_type t1 (belast t1 t1s) * projT2 (last t1 t1s).
Proof.
rewrite size_belast /=.
apply/ssrnat.ltP. exact: leqnn.
(* Admitted. *)
Defined. *)

(*
Program Definition product_type' (h : {d & measurableType d}) (t : seq {d & measurableType d}) (f : forall t', (size t' < size t)%coq_nat -> {d & measurableType d}) 
(* : Type := *)
: {d & measurableType d} :=
  match t with
  | [::] => h
  | t1 :: t1s => [the measurableType _ of ((projT2 (f (belast t1 t1s) _)) * (projT2 (last t1 t1s)))%type]
  end.
Next Obligation.
move=> ? ? ? ? ? <-.
rewrite size_belast //.
Defined.

(* Lemma well_founded_lt_size : well_founded (fun ) *)

Program Definition product_type (h : {d & measurableType d}) := Fix _ (fun=> Type) (product_type' h).
Next Obligation.
move=> ?.
apply: (@well_founded_lt_compat _ _) => x y; exact.
Defined.

Lemma product_typeE (h : {d & measurableType d}) (t : seq {d & measurableType d}) : product_type h t =
  match t with
  | [::] => projT2 h
  | t1 :: t1s => (product_type t1 (belast t1 t1s) * projT2 (last t1 t1s))%type
  end.
Proof.
elim: t => // h1 t1.
rewrite /product_type.
rewrite /product_type'.
rewrite /=.
(* rewrite Fix_eq.  *)
Admitted.

Lemma __ dA dB dC dD A B C D : product_type (existT _ dA A) [:: (existT _ dB B); (existT _ dC C); (existT _ dD D)] = (A * B * C * D)%type.
Proof.
Admitted.
(* rewrite
rewrite /=. 2!prodA. Qed. *)

Check @measurable_fun_id.

Fixpoint comp_fst (h : {d & measurableType d}) (t : seq {d & measurableType d}) : {f | measurable_fun setT f} :=
  match size t
  return forall d (A : measurableType d), {f : product_type h t -> A | measurable_fun setT f} with
  | 0 => fun _ _ => @exist _ _ _ (@measurable_fun_id _ _ _)
  | 1 => @exist _ _ _ (@measurable_fun_fst _ _ _ _)
  | k.+1 => fun=>
  (* @measurable_fun_comp _ _ _ _ _ _ _ _ (@measurable_fun_fst _ _ A _) *)
  @measurable_fun_id _ _ _
  (* @measurable_fun_id _ A s *)
  (* @measurable_fun_comp _ _ _ _ _ _ _ _ _ _ (@measurable_fun_fst _ _ G G) (@measurable_fun_fst _ _ G G) *)
  end.
*)

(* product type is measurable type? *)
(* Definition var1ofn (h : {d & measurableType d}) (t : seq {d & measurableType d}) i : {f : [the measurableType _ of (product_type h t)] -> projT2 (typn h t i) | measurable_fun setT f}. *)

Program Definition var_i_of4' {dA dB dC dD} {A : measurableType dA}
{B : measurableType dB} {C : measurableType dC} {D : measurableType dD} (i : nat) : forall (i_lt4 : (i < 4)%coq_nat),
{f : [the measurableType _ of (A * B * C * D)%type] ->
projT2 (@typn (existT _ dA A) [:: (existT _ dB B); (existT _ dC C); (existT _ dD D)] i) | measurable_fun setT f} :=
  match i as i return forall (i_lt4 : (i < 4)%coq_nat), {f : [the measurableType _ of (A * B * C * D)%type] ->
projT2 (@typn (existT _ dA A) [:: (existT _ dB B); (existT _ dC C); (existT _ dD D)] i) | measurable_fun setT f} with
  | 0 => fun i_lt4 => exist (fun x => measurable_fun setT x) (_ : A * B * C * D -> A) var1of4
  | 1 => fun i_lt4 => exist (fun x => measurable_fun setT x) (_ : A * B * C * D -> B) var2of4
  | 2 => fun i_lt4 => exist (fun x => measurable_fun setT x) (_ : A * B * C * D -> C) var3of4
  | 3 => fun i_lt4 => exist (fun x => measurable_fun setT x) (_ : A * B * C * D -> D) var4of4
  | _ => fun i_lt4 => False_rect _ (Nat.lt_irrefl _ i_lt4)
  end.
Next Obligation.
move=> dA dB dC dD A B C D ? ? ? ? n2.
by move/ssrnat.ltP.
Defined.

(*
value ::= measurable function (evalD)
        | kernel (evalP)
        | probability (eval) (-> into measurable fun.?)
*)

(* Lemma nth_ : seq.index ("x", R) [:: ("x", R); ("y", nat)] = 1%N.
Proof. rewrite /=. *)

Fixpoint only_left A B (l : seq (A * B)%type) :=
  match l with
  | [::] => [::]
  | h :: t => h.1 :: only_left t
  end.

Lemma measurable_fun_normalize (R : realType) dX (X : measurableType dX)
   dY (Y : measurableType dY) (k : R.-sfker X ~> Y) (P : probability Y R) :
  measurable_fun setT (normalize k P : X -> pprobability Y R).
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

Inductive evalD : forall d (G : measurableType d) (l : seq (string * Type))
    dT (T : measurableType dT) (e : expD R) (f : G -> T), measurable_fun setT f -> Prop :=
| E_unit : forall d G l, @evalD d G l _ munit exp_unit (cst tt) ktt

| E_bool : forall d G l b, @evalD d G l _ mbool (exp_bool b) (cst b) (kb b)

| E_real : forall d G l r, @evalD d G l _ _ (exp_real r) (cst r) (kr r)

| E_pair : forall d G l dA dB A B e1 f1 mf1 e2 f2 mf2,
  @evalD d G l dA A e1 (f1 : G -> A) mf1 ->
  @evalD d G l dB B e2 (f2 : G -> B) mf2 ->
  @evalD _ _ l _ _ (exp_pair e1 e2) 
    (_ : G -> Datatypes_prod__canonical__measure_Measurable A B) (@measurable_fun_pair _ _ _ G A B f1 f2 mf1 mf2)

| E_var2 : forall l d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) x,
  (* assoc_get x l = Some (bool : Type) -> *)
  (* seq.index x (only_left l) = i ->  *)
  let i := seq.index x (map fst l) in
  @evalD _ [the measurableType _ of (T1 * T2)%type] l _ _ (exp_var x) (proj1_sig (var_i_of2 i.+1)) (proj2_sig (var_i_of2 i.+1))

| E_var3 : forall l d1 d2 d3 (T1 : measurableType d1) (T2 : measurableType d2) (T3 : measurableType d3) x i,
  (* assoc_get x l = Some i ->  *)
  seq.index x (map fst l) = i ->
  (* let i := seq.index x (only_left l) in   *)
  @evalD _ [the measurableType _ of (T1 * T2 * T3)%type] l _ _ (exp_var x)
  (proj1_sig (var_i_of3 i.+1)) (proj2_sig (var_i_of3 i.+1))

| E_var4 : forall l d1 d2 d3 d4 (T1 : measurableType d1) (T2 : measurableType d2) (T3 : measurableType d3) (T4 : measurableType d4) x i,
  (* assoc_get x l = Some i ->  *)
  seq.index x (map fst l) = i ->
  (* let i := seq.index x (only_left l) in *)
  @evalD _ [the measurableType _ of (T1 * T2 * T3 * T4)%type] l _ _ (exp_var x)
  (proj1_sig (var_i_of4 i.+1)) (proj2_sig (var_i_of4 i.+1))

  (* (@snd G T) (var_i_of_n (n + 2)%nat (i + 1)) *)

| E_bernoulli : forall d (G : measurableType d) l (r : {nonneg R}) (r1 : (r%:num <= 1)%R),
  @evalD _ _ l _ _ (exp_bernoulli r) (_ : G -> _) (measurable_fun_cst (bernoulli r1 : pprobability _ _))

| E_poisson : forall d G l k e f mf,
  @evalD d G l _ (mR R) e f mf ->
  @evalD _ _ l _ _ (exp_poisson k e) (poisson k \o f) (measurable_fun_comp (mpoisson k) mf)

| E_norm : forall l e (k : R.-sfker munit ~> mbool) P,
  @evalP _ munit l _ _ e k ->
  @evalD _ munit l _ _ (exp_norm e) (normalize k P : _ -> pprobability _ _) (measurable_fun_normalize k P)

with evalP : forall d (G : measurableType d) (l : context) dT (T : measurableType dT),
  expP R ->
  R.-sfker G ~> T ->
  Prop :=
| E_sample : forall d G dT (T : measurableType dT) l (e : expD R) (p : _ -> pprobability T R) (mp : measurable_fun setT p),
  @evalD d G l _ _ e p mp ->
  @evalP d G l _ _ (exp_sample e) (sample p mp)

| E_ifP : forall d G l dT T e1 f1 mf e2 k2 e3 k3,
  @evalD d G l _ _ e1 f1 mf ->
  @evalP d G l dT T e2 k2 ->
  @evalP d G l dT T e3 k3 ->
  @evalP d G l dT T (exp_if e1 e2 e3) (ite mf k2 k3)

| E_score : forall d (G : measurableType d) l e (f : G -> R)
(mf : measurable_fun _ f),
  @evalD _ G l _ _ e f mf ->
  @evalP _ G l _ munit (exp_score e) [the R.-sfker _ ~> _ of kscore mf]

| E_return : forall d G l dT T e (f : _ -> _) (mf : measurable_fun _ f),
  @evalD d G l dT T e f mf ->
  @evalP d G l dT T (exp_return e) (ret mf)

| E_letin : forall d (G : measurableType d) l dy (Y : measurableType dy)
dz (Z : measurableType dz) e1 e2 k1 k2 (x : string),
  @evalP _ G l _ Y e1 k1 ->
  @evalP _ [the measurableType _ of (G * Y)%type] (l ++ [:: (x, Y : Type)])%SEQ _ Z e2 k2 ->
  @evalP _ G l _ Z (exp_letin x e1 e2) (letin k1 k2)

| E_letin_ : forall d (G : measurableType d) l dy (Y : measurableType dy)
dz (Z : measurableType dz) w1 w2 t1 t2,
  @evalP _ G l _ Y w1 t1 ->
  (* @evalP _ [the measurableType _ of (G * Y)%type] n.+1 (("_", n) :: l) _ Z _ w2 t2 -> *)
  @evalP _ _ l _ Z w2 t2 ->
  @evalP _ G l _ Z (exp_letin "_" w1 w2) (letin t1 t2).

(* Arguments exp {R}. *)
(* Fixpoint vars (e : expP) : set variable :=
  match e with
  | exp_letin x e1 e2 => vars e1
  | exp_var x => [set x]
  (* | exp_return e => vars e
  | exp_norm e => vars e *)
  | _ => set0
  end. *)

(* Compute vars (exp_letin "x" (exp_var "x") (exp_var "x")). *)

(* Compute vars (exp_letin "x" (exp_var "y") (exp_letin "z" (exp_var "x") (exp_var "z"))). *)

(* Compute vars (exp_letin "x" (exp_return (exp_var "z")) (exp_letin "y" (exp_return (exp_real 2)) (exp_return (exp_pair (exp_var "x") (exp_var  "y"))))). *)

End eval.

(* Arguments E_var2 {_ _ _ _ _ _} i. *)
Arguments E_var3 {_ _ _ _ _ _ _ _ _} i.
Arguments E_var4 {_ _ _ _ _ _ _ _ _ _ _} i.

Scheme evalD_mut_ind := Induction for evalD Sort Prop
with evalP_mut_ind := Induction for evalP Sort Prop.

Scheme expD_mut_ind := Induction for expD Sort Prop
with expP_mut_ind := Induction for expP Sort Prop.

Section eval_prop.

(*
Fixpoint execD_type (e : expD) : measurableType _ :=
  match e with
  | exp_real r => mR R
  | exp_bool b => mbool
  | exp_unit => munit
  | _ => munit
  end.

Fixpoint execD (e : expD) : forall f, measurable_fun _ f :=
  match e as e return forall f, measurable_fun _ f with
  (* | exp_var v => fun=> @measurable_fun_id _ _ _ *)
  | exp_real r => fun=> kr r
  | exp_bool b => fun=> kb b
  | exp_unit => fun=> ktt
  | _ => fun=> ktt
  end.

  (* | exp_var v => @measurable_fun _ _ [the measurableType _ of (A * B)%type] A setT (@fst A B)
  | exp_real r => measurable_fun setT (@cst (mR R) _ r)
  | exp_bool b => measurable_fun setT (@cst mbool _ b)
  | exp_unit => measurable_fun setT (@cst munit _ tt)
  | exp_pair e1 e2 => execD e1
  | exp_bernoulli r => forall (r1 : (r%:num <= 1)%R), measurable_fun setT (@cst (mR R) _ r%:num)
  (* | exp_poisson k e => execD e *)
  | _ => measurable_fun setT (@cst munit _ tt) *)
  end.

Check execD.

Fixpoint execP_type (e : expP) : Type :=
  match e with
  | exp_if e1 e2 e3 => execP_type e2
  | exp_sample _ => R.-sfker A ~> mbool
  | exp_return e1 => R.-sfker A ~> mR R
  | _ => R.-sfker A ~> B
  end.

Fixpoint execP (e : expP) : execP_type e :=
  match e with
  | exp_if e1 e2 e3 => ite _ (execP e2) (execP e3)
  | exp_sample e => sample (bernoulli p27)
  | exp_return e => ret (kr 1)
  end.
*)

Require Import Coq.Program.Equality.


(*Lemma eval_sample_uniqP (e : expD) u v :
  @evalP _ A [::] _ B (exp_sample e) u ->
  @evalP _ A [::] _ B (exp_sample e) v ->
  u = v.
Proof.
inversion 1.
apply Classical_Prop.EqdepTheory.inj_pair2 in H11.
apply Classical_Prop.EqdepTheory.inj_pair2 in H0.
(* subst.
apply Classical_Prop.EqdepTheory.inj_pair2 in H5. *)
Admitted.*)

Ltac inj H := apply Classical_Prop.EqdepTheory.inj_pair2 in H.

Variable R : realType.

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

Lemma eval_uniqP (dA dB : measure_display) (A : measurableType dA) (B : measurableType dB)
    (e : expP R) l (u v : R.-sfker A ~> B) :
  evalP l e u -> evalP l e v -> u = v.
Proof.
move=> hu.
apply: (@evalP_mut_ind R
  (fun d (G : measurableType d) (l : _) dT (T : measurableType dT) (e : expD R)
      (f : G -> T) (mf : measurable_fun setT f) (h1 : evalD l e mf) =>
    forall (v : G -> T) (mv : measurable_fun setT v), evalD l e mv -> f = v)
  (fun d (G : measurableType d) (l : _) dT (T : measurableType dT) (e : expP R)
      (u : R.-sfker G ~> T) (h1 : evalP l e u) =>
    forall (v : R.-sfker G ~> T), evalP l e v -> u = v)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dA A); last exact: hu.
- (* E_unit *)
  move=> d' G' l' {}v mv.
  inversion 1.
  subst d l0.
  inj H2.
  subst G.
  do 4 inj H6.
  by [].
- (* E_bool *)
  move=> d' G' l' r' {}v mv.
  inversion 1.
  inj H2; subst.
  by do 4 inj H5.
- (* E_real *)
  move=> d' G' l' r' {}v mv.
  inversion 1.
  inj H2; subst.
  by do 4 inj H5.
- (* E_pair *)
  clear hu u v e l.
  move=> d' G' l' dA' dB' A' B' e1 f1 mf1 e2 f2 mf2 e1f1 ih1 e2f2 ih2 {}v mv.
  inversion 1.
  subst d l e0 e3.
  inj H0.
  subst G0.
  inj H13.
  inj H21.
  inj H20.
  inj H20.
  inj H28.
  inj H28.
  apply/funext => g'.
  rewrite (_ : v g' = ((v g').1, (v g').2)); last by destruct (v g').
  congr (_, _).
    have ->// := ih1 (fst \o v).
    apply: measurable_fun_comp => //.
      exact: measurable_fun_fst.
    move=> Hyp0.
    have Hd : dA0 = dA' /\ dB0 = dB'.
    apply/mdisp_pair_equal_spec /H14.
    destruct Hd.
    subst.
    have ? : A0 = A'.
      admit.
    subst A0.
    have ? : B0 = B'.
      admit.
    subst B0.
    inj H7.
    do 2 inj H8.
    inj H9.
    inj H10.
    inj H16.
    do 2 inj H17.
    inj H18.
    inj H19.
    do 2 inj H20.
    do 2 inj H25.
    inj H26.
    inj H27.
    do 2 inj H28.
    subst v.
    have ->//: Hyp0 = mf0.
    exact: Prop_irrelevance.
  have ->// := ih2 (snd \o v).
  apply: measurable_fun_comp => //.
    exact: measurable_fun_snd.
  (* same as above *)
  admit.
- (* E_var2*)
  move=> l' d1 d2 T1 T2 x i v' mv.
  simple inversion 1 => //.
  have Hd : d0 = d1 /\ d3 = d2.
  apply/mdisp_pair_equal_spec /H0.
  destruct Hd; subst.
  inj H1.
  inj H4.
  subst.
  have ? : (T0 = T1).
  admit.
  have ? : (T2 = T3).
  admit.
  subst.
  by do 4 inj H6.
  admit.
  admit.
- (* E_var3 *)
  admit.
- (* E_var4 *)
  admit.
- (* E_bernoulli *)
  move=> d' G' l' r r1 v' mv.
  simple inversion 1 => //.
  subst.
  inj H1.
  subst.
  do 4 inj H6.
  subst.
  clear H7.
  congr cst.
  injection H5 => ?.
  subst.
  congr (bernoulli _).
  exact: Prop_irrelevance.
- (* E_poisson *)
  move=> {}d {}G l' k e' f mf ef ih {}v mv.
  simple inversion 1 => // h.
  subst.
  inj H2; subst.
  do 4 inj H7; subst.
  do 5 inj H8.
  injection H6=> ? ?; subst.
  by have ? := ih _ mf0 h; subst.
- (* E_norm *)
  move=> l' e' k' P ek ih {}v mv.
  simple inversion 1 => // h.
  do 4 inj H7.
  subst.
  do 5 inj H8.
  injection H6 => ?; subst.
  have ? := ih _ h.
  subst.
  congr (normalize k).
  admit.
- (* E_sample *)
  move=> d' G' dT T l' e' p mp ep ih v'.
  simple inversion 1 => // h.
  subst.
  inj H2.
  inj H5.
  subst.
  do 4 inj H7.
  subst.
  injection H6 => ?.
  subst.
  have ? := ih _ mp0 h.
  subst.
  congr (sample p0).
  exact: Prop_irrelevance.
- (* E_ifP *)
  move=> d' G' l' dT T e1 f1 mf e2 k2 e3 k3 ef1 ih1 ef2 ih2 ef3 ih3 v'.
  simple inversion 1 => // h1 h2 h3.
  subst.
  inj H4.
  inj H7.
  subst.
  do 4 inj H9.
  subst.
  injection H8 => ? ? ?.
  subst.
  have ? := ih1 _ mf0 h1.
  have ? := ih2 _ h2.
  have ? := ih3 _ h3.
  subst.
  congr (ite _ k0 k1).
  exact: Prop_irrelevance.
- (* E_score *)
  move=> d' G' l' e' f mf ef ih v'.
  simple inversion 1 => // h.
  subst.
  inj H2.
  subst.
  do 4 inj H7.
  subst.
  injection H6 => ?.
  subst.
  have ? := ih _ mf0 h.
  subst.
  congr score.
  exact: Prop_irrelevance.
- (* E_return *)
  clear dA dB A B e l u v hu.
  move=> dG G l dT T e f mf ef ih v.
  simple inversion 1 => //.
  subst d l0 dT0.
  inj H2.
  subst G0.
  inj H5.
  subst T0.
  do 4 inj H7.
  subst v.
  case: H6 => ?; subst e0.
  move=> h.
  have ? := ih _ mf0 h.
  subst f0.
  congr ret.
  exact: Prop_irrelevance.
- (* E_letin *)
  move=> d' G' l' dY Y dZ Z e1 e2 k1 k2 x ek1 ih1 ek2 ih2 {}v.
  simple inversion 1 => // h1 h2.
  subst.
  inj H3.
  inj H6.
  subst.
  do 4 inj H8.
  subst.
  injection H7 => ? ? ?.
  subst.
  have ? := ih1 _.
  admit.
- (* E_letin_ *)
  admit.
Admitted.

Lemma eval_uniqD (dA dB : measure_display) (A : measurableType dA) (B : measurableType dB) l (e : expD R) u v mu mv :
  @evalD _ _ A l _ B e u mu ->
  @evalD _ _ A l _ B e v mv ->
  u = v.
Proof.
move=> hu.
apply: (@evalD_mut_ind R
  (fun d (G : measurableType d) (l : _) dT (T : measurableType dT) (e : expD R)
      (f : G -> T) (mf : measurable_fun setT f) (h1 : evalD l e mf) =>
    forall (v : G -> T) (mv : measurable_fun setT v), evalD l e mv -> f = v)
  (fun d (G : measurableType d) (l : _) dT (T : measurableType dT) (e : expP R)
      (u : R.-sfker G ~> T) (h1 : evalP l e u) =>
    forall (v : R.-sfker G ~> T), evalP l e v -> u = v)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dA A); last exact: hu.


dependent induction e.
inversion 1.
subst.
(* apply Classical_Prop.EqdepTheory.inj_pair2 in H18. *)
subst.
(* apply Classical_Prop.EqdepTheory.inj_pair2 in H18. *)
Admitted.

Axiom largest_var_in_expP : forall e : expP R, nat.
(* return the larget var in e *)

Lemma eval_full dA (A : measurableType dA) l s :
  prod_meas s = existT _ _ A ->
  forall e, (largest_var_in_expP e <= size s)%nat ->
    exists dB (B : measurableType dB) v, @evalP R _ A l _ B e v.
Proof.
move=> HA e Hs.
apply: (@expP_mut_ind R
  (fun (e : expD R) =>
    exists dB (B : measurableType dB) (v : A -> B) (mv : measurable_fun setT v), evalD l e mv)
  (fun (e : expP R) =>
    exists dB B (v : R.-sfker A ~> B), evalP l e v)
  _ _ _ _ _ _ _ _ _ _ _ _ _).
-
  move=> x.
  eexists.
  eexists.
  admit.
  (* exists [the measurableType _ of (munit * munit)%type].
  exists (proj1_sig (var_i_of2 0.+1)).
  exists (proj2_sig (var_i_of2 0.+1)).
  exact: E_var2. *)
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
  have r1 : (r%:num <= 1)%R.
  admit.
  do 3 eexists.
  exists (measurable_fun_cst (bernoulli r1 : pprobability _ _)).
  exact: E_bernoulli.
-
  move=> n e0 ih.
  do 1 eexists.
  exists (mR R).
  eexists.
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
  move=> e1 ih1 e2 ih2 e3 ih3.
  apply ex_intro in ih1.
  (* destruct ih1 as (dA1 & A1 & dB1 & B1 & f1 & mf1 & ih1). *)
  do 2 eexists.
  (* exists (ite mf1). *)
-
-
Admitted.
(* 
Lemma evalP_surjection dA dB (A : measurableType dA) (B : measurableType dB) l :
  forall v, exists e, @evalP R _ A l _ B e v.
Proof.
move=> v.
eexists. *)

Definition exec (dA dB : measure_display) (A : measurableType dA) (B : measurableType dB) :
  expP R -> R.-sfker A ~> B.
Proof.
move=> e.
have /cid h := eval_full A B e.
exact: (proj1_sig h).
Defined.

End eval_prop.

Section example.
Variables (d : _) (G : measurableType d) (R : realType).

Example ex_real : @evalD R _ G [::] _ _ (exp_real 3%:R) (@cst _ R 3%:R) (kr 3%:R).
Proof. apply/E_real. Qed.

Example ex_bool : @evalD R _ G [::] _ _ (exp_bool true) (cst true)
(@measurable_fun_cst _ _ _ mbool setT _).
Proof. apply/E_bool. Qed.

Example ex_pair : @evalD R _ G [::] _ _ (exp_pair (exp_real 1) (exp_real 2)) _
(@measurable_fun_pair _ _ _ _ _ _ (@cst _ R 1%R) (@cst _ R 2) (kr 1) (kr 2)).
Proof.
apply/E_pair /E_real /E_real.
Qed.

Example ex_ifP : @evalP R _ G [::] _ (mR R)
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
  @evalP R _ (mR R) [::] _ _
    (exp_sample (exp_bernoulli (2 / 7%:R)%:nng))
    (sample _ (measurable_fun_cst (bernoulli p27 : pprobability _ _))).
Proof.
exact/E_sample/E_bernoulli.
Qed.

Example sampler (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
  @evalP R _ (mR R) [::] _ _
    (exp_sample (exp_bernoulli r))
    (sample _ (measurable_fun_cst (bernoulli r1 : pprobability _ _))).
Proof. exact/E_sample/E_bernoulli. Qed.

Example score1 :
  @evalP R _ (mR R) [::] _ _ (exp_score (exp_real 1)) (score (kr 1)).
Proof. apply/E_score /E_real. Qed.

Example score2 :
  @evalP R _ (mR R) [::] _ _
    (exp_score (exp_poisson 4 (exp_real 3%:R)))
    (score (measurable_fun_comp (mpoisson 4) (kr 3%:R))).
Proof. apply/E_score /E_poisson /E_real. Qed.

(* to be failed *)
Example ex_var :
  @evalP R _ munit [::] _ _
    (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng))
      (exp_letin "r" (exp_if (exp_var "x") (exp_return (exp_real 3%:R)) (exp_return (exp_real 10%:R)))
        (exp_letin "y" (exp_score (exp_poisson 4 (exp_var "r")))
          (exp_return (exp_var "y")))))
    (kstaton_bus' _ (mpoisson 4)).
Proof.
apply/E_letin /E_letin /E_letin => /=.
(* apply/E_sample /E_bernoulli. *) admit.
apply/E_ifP /E_return /E_real /E_return /E_real.
(* apply/(E_var2 _ 0%nat). *)
exact: E_var2.
apply/E_score.
apply/E_poisson.
exact: (E_var3 1).
(* exact: (E_var3 _ 1%nat). *)
apply/E_return.
set tmp := var2of4.
have -> : tmp = proj2_sig (var_i_of4 1) by [].
(* have := @E_var4 3 [:: ("y", 2%nat); ("r", 1%nat); ("x", 0%nat)] _ _ _ _ munit mbool (mR R) munit "y" 2 erefl. *)
Abort.

Example eval5 :
  @evalP R _ munit [::] _ _
    (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng))
      (exp_letin "r" (exp_if (exp_var "x") (exp_return (exp_real 3%:R)) (exp_return (exp_real 10%:R)))
        (exp_letin "_" (exp_score (exp_poisson 4 (exp_var "r")))
          (exp_return (exp_var "x")))))
    (kstaton_bus' _ (mpoisson 4)).
Proof.
apply/E_letin /E_letin /E_letin => /=.
apply/E_sample /E_bernoulli.
apply/E_ifP /E_return /E_real /E_return /E_real.
exact: E_var2.
apply/E_score.
apply/E_poisson.
exact: (E_var3 1).
apply/E_return.
exact: (E_var4 0).
Qed.

Example eval6 P :
  @evalD R _ munit [::] _ _
    (exp_norm
      (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng))
        (exp_letin "r"
          (exp_if (exp_var "x") (exp_return (exp_real 3%:R))
                                (exp_return (exp_real 10%:R)))
          (exp_letin "_" (exp_score (exp_poisson 4 (exp_var "r")))
            (exp_return (exp_var "x"))))))
    (staton_bus' (mpoisson 4) P : _ -> pprobability _ _) (measurable_fun_normalize (R := R) (kstaton_bus' _ (mpoisson 4)) P).
    (* (@normalize _ _ munit mbool R (kstaton_bus' _ (mpoisson 4)) P). *)
Proof.
apply/E_norm.
apply/E_letin /E_letin /E_letin_.
apply/E_sample /E_bernoulli.
apply/E_ifP /E_return /E_real /E_return /E_real.
exact: E_var2.
apply/E_score.
apply/E_poisson.
exact: (E_var3 1).
apply/E_return.
exact: (E_var4 0).
Qed.

Example eval7 P :
  @evalD R _ munit [::] _ _
    (exp_norm (exp_sample (exp_bernoulli (2 / 7%:R)%:nng)))
    _
    (* (@normalize _ _ _ _ R (sample _ (measurable_fun_cst (bernoulli p27 : pprobability _ _)))) *)
    (measurable_fun_normalize (R := R) (sample _ (measurable_fun_cst (bernoulli p27 : pprobability _ _))) P).
Proof. apply/E_norm /E_sample /E_bernoulli. Qed.

Example eval7_2 P :
  @evalD R _ munit [::] _ _
    (exp_norm (exp_sample (exp_norm (exp_sample (exp_bernoulli (2 / 7%:R)%:nng)))))
    _
    (* (@normalize _ _ _ _ R
      (sample _ (measurable_fun_normalize (sample _ (@mbernoulli_density_function R _ _ (2 / 7%:R))) P)) P : _ -> pprobability _ _) *)
    (measurable_fun_normalize
      (sample _ (measurable_fun_normalize (R := R) (sample _ (measurable_fun_cst  (bernoulli p27 : pprobability _ _))) P)) P).
Proof.
apply/E_norm /E_sample.
apply/E_norm /E_sample /E_bernoulli.
Qed.

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
Admitted. *)

End example.

Section letinC.
Variables (dG : _) (G : measurableType dG) (dT : _) (T : measurableType dT)
  (dU : _) (U : measurableType dU) (R : realType).

Lemma letinC' (t u : expP R) (v1 v2 : R.-sfker _ ~> _) :
  @evalP R _ G [::] _ [the measurableType _ of (T * U)%type]
  (exp_letin "x" t (exp_letin "y" u
    (exp_return (exp_pair (exp_var "x") (exp_var "y"))))) v1 ->
  @evalP R _ G [::] _ [the measurableType _ of (T * U)%type]
  (exp_letin "y" u (exp_letin "x" t
    (exp_return (exp_pair (exp_var "x") (exp_var "y"))))) v2 ->
  v1 = v2.
Proof.
pose vt : R.-sfker G ~> T := exec G T t.
pose vu : R.-sfker [the measurableType _ of (G * T)%type] ~> U := exec _ _ u.
move=> evalv1 evalv2.
(* pose vu := exec [the measurableType _ of (G * T)%type] _ u. *)
have hv1 : v1 = (letin vt (letin vu (ret (measurable_fun_pair var2of3 var3of3)))).
  (* apply: (eval_uniq _ _ _ evalv1). *)
  (* apply: (@eval_uniq _ _ _ _ P _ _). *)
  admit.
pose vt' : R.-sfker [the measurableType _ of (G * U)%type] ~> T := exec _ _ t.
pose vu' : R.-sfker G ~> U := exec _ _ u.
have hv2 : v2 = (letin vu' (letin vt' (ret (measurable_fun_pair var3of3 var2of3)))).
  (* apply: (eval_uniq evalv2). *)
  admit.
rewrite hv1 hv2.
apply/eq_sfkernel=> x A.
apply: letinC.
Admitted.

Lemma letinC'' (t u : expP R) :
  (exp_letin "x" t (exp_letin "y" u (exp_return (exp_var "x")))) =
  (exp_letin "y" u (exp_letin "x" t (exp_return (exp_var "x")))).
Proof.
Admitted.

End letinC.
