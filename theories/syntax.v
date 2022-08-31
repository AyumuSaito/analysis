From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure fsbigop numfun lebesgue_integral kernel prob_lang.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Require Import String ZArith.
Local Open Scope string.

Section v4.
Variables (R : realType) (d : _) (T : measurableType d).

Inductive type :=
| t_unit
| t_real
| t_P : type -> type
| t_arrow : type -> type -> type
.

Reserved Notation "[| T |]Type".
Fixpoint interp_type (T : type) : Type :=
  match T with
  | t_unit => unit
  | t_real => \bar R
  | t_arrow A B => [| A |]Type -> [| B |]Type
  | _ => unit (* *)
  end
  where "[| T |]Type" := (interp_type T).

Definition variable := string.
Inductive context :=
| empty
| extend : context -> variable -> type -> context
.

Inductive termD :=
| TT : termD
| Var : string -> termD
| Const : R -> termD
| App : termD -> termD -> termD
| Bernoulli : R -> termD
| Ifd : termD -> termD -> termD -> termD
.

Inductive termP :=
| Ret : termD -> termP
| Sample : termD -> termP
| Score : termD -> termP
| Letin : variable -> termP -> termP -> termP
| Ifp : termD -> termP -> termP -> termP
.

Reserved Notation "[| G |]context".
Fixpoint interp_context (G : context) : Type :=
  match G with
  | empty => unit
  | extend G x T => [| G |]context * [| T |]Type
  end
  where "[| G |]context" := (interp_context G).

Example context1 := extend empty "x" t_real.

Compute [| context1 |]context.

Reserved Notation "G |-d t ::: A" (at level 50).
Inductive program_d : context -> termD -> type -> Type :=
(* | T_context : forall G x x' A A', G |-d (Var x) ::: A -> (extend G x' A') |-d (Var x) ::: A *)
(* | T_var     : forall G x A, extend G x A |-d (Var x) ::: A *)
| T_app     : forall G A B f t, G |-d f ::: t_arrow A B -> G |-d t ::: A -> G |-d App f t ::: B 
| T_unit {G} : G |-d TT ::: t_unit
| T_ifd     : forall G t u1 u2 A B, 
    G |-d t ::: A -> G |-d u1 ::: B -> G |-d u2 ::: B -> G |-d Ifd t u1 u2 ::: B
(* | T_bernoulli : forall G (r : R) A, G |-d Bernoulli r ::: t_P A *)
where "G |-d t ::: A" := (program_d G t A).

Reserved Notation "G |-p t ::: A" (at level 50). 
Inductive program_p : context -> termP -> type -> Prop :=
| T_return  : forall G t A, G |-d t ::: A -> G |-p Ret t ::: A
| T_sample  : forall G t A, G |-d t ::: (t_P A) -> G |-p Sample t ::: A
| T_score   : forall G t, G |-d t ::: t_real -> G |-p Score t ::: t_unit
| T_letin   : forall G x t u A B, 
    G |-p t ::: A -> (extend G x A) |-p u ::: B -> G |-p Letin x t u ::: B
| T_ifp     : forall G t u1 u2 A B, 
    G |-d t ::: A -> G |-p u1 ::: B -> G |-p u2 ::: B -> G |-p Ifp t u1 u2 ::: B
where "G |-p t ::: A" := (program_p G t A).

Check tt : [| t_unit |]Type.
Fixpoint denote_d {G t A} (pgm : program_d G t A) 
  : [| G |]context -> [| A |]Type (* measurable function *) := 
  match pgm with
  | T_unit _ => fun _ => tt
  | T_app _ _ _ _ _ f s => fun p => denote_d f p (denote_d s p)
  | T_ifd _ _ _ _ _ _ p1 p2 p3 => fun p => if true (* TODO *) then denote_d p2 p else denote_d p3 p
  (* | T_var _ x _ => fun _ => TT *)
  end.

(* Fixpoint denote_p {G t A} (pgm : program_p G t A)
  : R.-sfker [| G |]context ~> [| A |]Type :=
  match pgm with
  |
  end. *)

Example ex4 :
  empty |-p Letin "x" (Sample (Bernoulli (2 / 7)))
    (Ret (Var "x")) ::: t_real.
Proof. 
apply /T_letin.
Admitted.

Example k3d : empty |-d App (Const 3) TT ::: t_real.
Proof.
apply /T_app /T_unit.
Admitted.

Example k3p : empty |-p Score (App (Const 3) TT) ::: t_unit.
Proof.
apply /T_score /T_app /T_unit.
Admitted.

Example ex_p30 : 
  empty |-p Letin "x" (Sample (Bernoulli (1 / 2)))
    (Letin "r" (Ifp (Var "x") (Score (App (Const 4) TT)) (Score (App (Const 6) TT))) (Ret (Var "x"))) ::: t_real.
Proof.
apply /T_letin.
(* apply /T_sample /T_bernoulli.
apply /T_letin.
apply /T_ifp.
apply /T_var.
apply /T_score /T_app /T_unit.
apply /T_score /T_app /T_unit.
apply /T_return /T_context /T_var. *)
Admitted.

Inductive eval_termD : termD -> termD -> Prop :=
| E_var : forall x, eval_termD (Var x) (Var x)
.

(* Let mbool := Datatypes_bool__canonical__measure_Measurable.
Let munit := Datatypes_unit__canonical__measure_Measurable.
Definition eval_type (t : type) : Type :=
  match t with
  | t_unit => unit
  | t_real => R
  | t_P t_unit => probability munit R
  | t_P t_real => probability T (* R *) R
  | t_P _ => probability T R
  end. *)

End v4.

Section v2.

Variable (R : realType).

Variable (d d' : measure_display) (T : measurableType d) (T' : measurableType d').
Definition Env := list (string * (R.-ker T ~> T')).
Definition empty_env : Env := [::].
Fixpoint env_get x (env : Env) : R.-ker T ~> T' :=
  match env with
  | [::] => [the kernel _ _ _ of @kernel_from_mzero _ _ R _ T]
  | (x', v) :: env' => if string_dec x x' then v else env_get x env'
  end.
Fixpoint env_set x v (env : Env) :=
  match env with
  | [::] => [:: (x, v)]
  | (x', v') :: env' => if string_dec x x' then (x,v)::env' else (x',v')::env_set x v env'
  end.

(* Definition env1 := set "x" 1 empty_env.
Definition env2 := set "y" 6%:R env1.
Compute get "x" env1.
Lemma _get2 : get "y" env2 = 6%:R.
Proof. by []. Qed. *)

Inductive Z := P | D.

(* Variables (d d': measure_display) (T : measurableType d) (T' : measurableType d'). *)

Inductive ExpD : Type :=
  (* | Const (r : R) *)
  (* | IfD (e1 : ExpD) (e2 e3 : ExpD) *)
  (* | Var : string -> ExpD *)
  | LamE : T -> ExpD -> ExpD
  | AppE : ExpD -> ExpD -> ExpD
  (* | Letin (x : string) (e1 : ExpP) (e2 : ExpD) *)
  .

Check Return R.

(* Example pgm1 := Const 1.
(* Example pgm2 :=  *)
Example eval1 : evalD pgm1 = fun=> 1%:R.
Proof. by []. Qed. *)

Inductive ExpP : Type :=
  | RetE (x : ExpD)
  (* | Samp (m : probability T' R) *)
  .

Variable (f : T -> T') (mf : measurable_fun setT f).

Check Return R mf.

Fixpoint evalP (e : ExpP) : R.-sfker _ ~> _ :=
  match e with 
  | RetE x => Return R mf
  (* | Samp m => [the sfinite_kernel T _ _ of kernel_probability m] *)
  end.

Fail Fixpoint evalD (env : Env) (e : ExpD) : R.-sfker _ ~> _ :=
  match e with 
  (* | Const n => [the sfinite_kernel _ _ _ of [the kernel _ _ _ of kn n] _ _] Const: return measurable fun. *)
  (* | If e1 e2 e3 => if e1 then (evalD env e2) else (evalD env e3)
  | Var x => get x env
  | Letin x e1 e2 => evalD (set x (evalP env e1) env) e2 *)
  end.

Fail Inductive ExpD : Type :=
  | Const (r : R)
  | Add (e1 e2 : ExpD)
  | If (e1 : bool) (e2 e3 : ExpD) (* If probabilistic *)
  | Var (x : string)
  | Letin (x : string) (e1 : ExpD) (e2 : ExpD)
  .

Fail Fixpoint eval (env : Env) (e : ExpD) : R :=
  match e with 
  | Const n => n (* Const: return measurable fun. *)
  | Add e1 e2 => eval env e1 + eval env e2
  | If e1 e2 e3 => if e1 then (eval env e2) else (eval env e3)
  | Var x => get x env
  | Letin x e1 e2 => eval (set x (eval env e1) env) e2
  end.

Fail Definition evalp (e : ExpP) : R.-sfker _ ~> _ :=
  match e with
  | RetE f mf => Return R mf
  | Samp m => [the sfinite_kernel T _ _ of kernel_probability m]
  end.
End v2.

Section eval.

Variables (R : realType).
Variables (d: measure_display) (T : measurableType d).

Let mR := Real_sort__canonical__measure_Measurable R.
Let munit := Datatypes_unit__canonical__measure_Measurable.
Let mbool := Datatypes_bool__canonical__measure_Measurable.

End eval.