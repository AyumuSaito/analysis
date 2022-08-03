From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure fsbigop numfun lebesgue_integral kernel prob_lang.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section v2.

Variable (R : realType).

Require Import String ZArith.
Local Open Scope string.
Section intro.

Variable (d d' : measure_display) (T : measurableType d) (T' : measurableType d').
Definition Env := list (string * (R.-ker T ~> T')).
Definition empty_env : Env := [::].
Fixpoint get x (env : Env) : R.-ker T ~> T' :=
  match env with
  | [::] => [the kernel _ _ _ of @kernel_from_mzero _ _ R _ T]
  | (x', v) :: env' => if string_dec x x' then v else get x env'
  end.
Fixpoint set x v (env : Env) :=
  match env with
  | [::] => [:: (x, v)]
  | (x', v') :: env' => if string_dec x x' then (x,v)::env' else (x',v')::set x v env'
  end.

(* Definition env1 := set "x" 1 empty_env.
Definition env2 := set "y" 6%:R env1.
Compute get "x" env1.
Lemma _get2 : get "y" env2 = 6%:R.
Proof. by []. Qed. *)

Inductive Z := P | D.

(* Variables (d d': measure_display) (T : measurableType d) (T' : measurableType d'). *)

Inductive ExpP : Type :=
  | Ret (f: T -> T') (mf : measurable_fun setT f)
  | Samp (m : probability T' R)
  .

Inductive ExpD : Type :=
  | Const (n : nat)
  (* | If (e1 : bool) (e2 e3 : ExpD)
  | Var (x : string)
  | Letin (x : string) (e1 : ExpP) (e2 : ExpD) *)
  .

Fixpoint evalP (env : Env) (e : ExpP) : R.-sfker _ ~> _ :=
  match e with 
  | Ret f mf => Return R mf
  | Samp m => [the sfinite_kernel T _ _ of kernel_probability m]
  end.

Fixpoint evalD (env : Env) (e : ExpD) : R.-sfker _ ~> _ :=
  match e with 
  | Const n => [the sfinite_kernel _ _ _ of kn n] (* Const: return measurable fun. *)
  (* | If e1 e2 e3 => if e1 then (evalD env e2) else (evalD env e3)
  | Var x => get x env
  | Letin x e1 e2 => evalD (set x (evalP env e1) env) e2 *)
  end.

Inductive ExpD : Type :=
  | Const (r : R)
  | Add (e1 e2 : ExpD)
  | If (e1 : bool) (e2 e3 : ExpD) (* If probabilistic *)
  | Var (x : string)
  | Letin (x : string) (e1 : ExpD) (e2 : ExpD)
  .

Fixpoint eval (env : Env) (e : ExpD) : R :=
  match e with 
  | Const n => n (* Const: return measurable fun. *)
  | Add e1 e2 => eval env e1 + eval env e2
  | If e1 e2 e3 => if e1 then (eval env e2) else (eval env e3)
  | Var x => get x env
  | Letin x e1 e2 => eval (set x (eval env e1) env) e2
  end.

Lemma _0 : eval empty_env (Const 0) = 0%:R.
Proof. by []. Qed.
Lemma _1 : eval env1 (Add (Const 1) (Const 2)) = 3%:R.
Proof. by []. Qed.
Lemma _2 : eval env1 (If true (Const 1) (Add (Const 1) (Const 2))) = 1%:R.
Proof. by []. Qed.
Lemma _3 : eval env1 (If false (Const 1) (Add (Const 1) (Const 2))) = 3%:R.
Proof. by []. Qed.
Lemma _4 : eval env1 (Var "x") = 1%:R.
Proof. by []. Qed.
Lemma _5 : eval env2 (Add (Var "x") (Var "y")) = 7%:R.
Proof. by []. Qed.
Lemma _6 : eval env2 (Letin "z" (Const 10%:R) (Var "z")) = 10%:R.
Proof. by []. Qed.

Definition evalp (e : expP) : R.-sfker _ ~> _ :=
  match e with
  | Ret f mf => Return R mf
  | Samp m => [the sfinite_kernel T _ _ of kernel_probability m]
  end.
End v2.

Section eval.

Variables (R : realType).
Variables (d: measure_display) (T : measurableType d).

Let mR := Real_sort__canonical__measure_Measurable R.
Let munit := Datatypes_unit__canonical__measure_Measurable.
Let mbool := Datatypes_bool__canonical__measure_Measurable.

Check evalp (Ret R (@k3 R _ munit)) tt set0.

Example __ : evalp (Ret R (@k3 R _ munit)) tt setT = 1.
Proof. 
by rewrite /evalp /Return /= diracE in_setT.
Qed.

Check evalp (Samp _ [the probability _ _ of bernoulli (twoseven_proof R)]) tt set0.

Example __sample : 
  evalp (Samp munit [the probability _ _ of bernoulli27 R]) tt setT = 1.
Proof.
by rewrite /= bernoulli_setT.
Qed.

Example _sample : 
  evalp (Samp T [the probability _ _ of bernoulli27 R]) = [the sfinite_kernel _ _ _ of kernel_probability [the probability _ _ of bernoulli27 R]].
Proof.
by [].
Qed.

Lemma _return : 
  evalp (Ret R (@k3 R _ _)) tt set0 = 1
  (* [the R.-sfker T ~> _] *)
  .
Proof.
rewrite /evalp /Return.

(* Compute evalp (Sample (bernoulli27 R)). *)
Lemma _4 : 
  evalp (Sample [the probability _ _ of bernoulli27 R]) = 
  [the kernel _ _ _ of kernel_probability [the probability _ _ of bernoulli27 R]].
Proof. by []. Qed.



Section hlist.
Variable A : Type.
Variable B : A -> Type.

Inductive hlist : list A -> Type :=
| HNil : hlist nil
| HCons : forall (x : A) (ls : list A), B x -> hlist ls -> hlist (x :: ls).
End hlist.

Arguments hlist {A}.
Arguments HNil {A B}.
Arguments HCons {A B x ls}.

Section syntax.
Variables (R : realType).
 (* (d : measure_display) (X : measurableType d). *)

Inductive type : Set :=
  (* | RealType : type  *)
  | Unit : type
  | Bool : type
  | Arrow : type -> type -> type
.

Inductive exp : list type -> type -> Set :=
  | Const : forall ts, exp ts Unit
  | Var   : forall v ts, exp ts (nth Unit ts v)
  (* | If    : forall ts t (b : exp ts Bool) (e1 e2 : exp ts t), exp ts t   *)
(* | App : forall ts dom ran, exp ts (Arrow dom ran) -> exp ts dom -> exp ts ran
| Abs : forall ts dom ran, exp (dom :: ts) ran -> exp ts (Arrow dom ran) *)
(* | Sample : forall *)
.

Arguments Const {ts}.

Fixpoint typeDenote (t : type) :=
  match t with
  (* | RealType => realType *)
  | Unit => unit
  | Bool => bool
  | Arrow t1 t2 => typeDenote t1 -> typeDenote t2
  end.

(* Check sfinite_kernel R X X.
Check X ^^> X. *)

Inductive function_or_kernel {d d' : measure_display} 
  (X : measurableType d) (Y : measurableType d') :=
  | Kernel : kernel R X Y -> function_or_kernel X Y
  | Func : (X -> Y) -> function_or_kernel X Y
.

Fixpoint ExpDenote {d d' : measure_display} {X : measurableType d} 
{Y : measurableType d'} {ts t} (e : exp ts t) : function_or_kernel X X :=
  match e with
  | Const _ => Func _ _ id
  | Var v _  => Kernel _ _ [the kernel _ _ _ of @kernel_from_dirac R d X]
  (* | If _ _ b e1 e2 => match (ExpDenote b) with
    | 
    | 
    end *)
  end.

(* Fixpoint ExpDenote (R : realType) {ts t} (e : exp ts t) {d d' : measure_display} {X : measurableType d} {Y : measurableType d'} : sfinite_kernel R X X :=
match e with
| Const _ => @kernel_from_dirac R d X
end. *)

Eval simpl in ExpDenote (@Const [::]).
Eval simpl in ExpDenote (@Const [::]).
(* Eval simpl in ExpDenote (Abs _ Unit _ Const) HNil. *)
End syntax.