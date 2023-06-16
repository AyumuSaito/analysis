Require Import String Classical.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg.
From mathcomp.classical Require Import mathcomp_extra boolp.
Require Import signed reals topology normedtype.
Require Import lang_syntax_util.

(******************************************************************************)
(*           Intrinsically-typed concrete syntax for a toy language           *)
(*                                                                            *)
(* The main module provided by this file is "lang_intrinsic_tysc" which       *)
(* provides an example of intrinsically-typed concrete syntax for a toy       *)
(* language (a simplification of the syntax/evaluation formalized in          *)
(* lang_syntax.v). Other modules provide even more simplified language for    *)
(* pedagogical purposes.                                                      *)
(*                                                                            *)
(*      lang_extrinsic == non-intrinsic definition of expression              *)
(*   lang_intrinsic_ty == intrinsically-typed syntax                          *)
(*   lang_intrinsic_sc == intrinsically-scoped syntax                         *)
(* lang_intrinsic_tysc == intrinsically-typed/scoped syntax                  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Set Printing Implicit Defensive.

Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section type.
Variables (R : realType).

Inductive typ := Real | Unit.

Canonical typ_eqType := Equality.Pack (@gen_eqMixin typ).

Definition iter_pair (l : list Type) : Type :=
  foldr (fun x y => (x * y)%type) unit l.

Definition Type_of_typ (t : typ) : Type :=
  match t with
  | Real => R
  | Unit => unit
  end.

Definition ctx := seq (string * typ).

Definition Type_of_ctx (g : ctx) := iter_pair (map (Type_of_typ \o snd) g).

Goal Type_of_ctx [:: ("x", Real); ("y", Real)] = (R * (R * unit))%type.
Proof. by []. Qed.

End type.

Module lang_extrinsic.
Section lang_extrinsic.
Variable R : realType.
Implicit Types str : string.

Inductive exp : Type :=
| exp_unit : exp
| exp_real : R -> exp
| exp_var (g : ctx) t str : t = lookup Unit g str -> exp
| exp_add : exp -> exp -> exp
| exp_letin str : exp -> exp -> exp.
Arguments exp_var {g t}.

Fail Example letin_once : exp :=
  exp_letin "x" (exp_real 1) (exp_var "x" erefl).
Example letin_once : exp :=
  exp_letin "x" (exp_real 1) (@exp_var [:: ("x", Real)] Real "x" erefl).

End lang_extrinsic.
End lang_extrinsic.

Module lang_intrinsic_ty.
Section lang_intrinsic_ty.
Variable R : realType.
Implicit Types str : string.

Inductive exp : typ -> Type :=
| exp_unit : exp Unit
| exp_real : R -> exp Real
| exp_var g t str : t = lookup Unit g str -> exp t
| exp_add : exp Real -> exp Real -> exp Real
| exp_letin t u : string -> exp t -> exp u -> exp u.
Arguments exp_var {g t}.

Fail Example letin_once : exp Real :=
  exp_letin "x" (exp_real 1) (exp_var "x" erefl).
Example letin_once : exp Real :=
  exp_letin "x" (exp_real 1) (@exp_var [:: ("x", Real)] _ "x" erefl).

End lang_intrinsic_ty.
End lang_intrinsic_ty.

Module lang_intrinsic_sc.
Section lang_intrinsic_sc.
Variable R : realType.
Implicit Types str : string.

Inductive exp : ctx -> Type :=
| exp_unit g : exp g
| exp_real g : R -> exp g
| exp_var g t str : t = lookup Unit g str -> exp g
| exp_add g : exp g -> exp g -> exp g
| exp_letin g t str : exp g -> exp ((str, t) :: g) -> exp g.
Arguments exp_real {g}.
Arguments exp_var {g t}.
Arguments exp_letin {g t}.

Declare Custom Entry expr.

Notation "[ e ]" := e (e custom expr at level 5).
Notation "{ x }" := x (in custom expr, x constr).
Notation "x ':R'" := (exp_real x) (in custom expr at level 1).
Notation "x" := x (in custom expr at level 0, x ident).
Notation "% x" := (exp_var x erefl) (in custom expr at level 1).
Notation "x + y" := (exp_add x y)
  (in custom expr at level 2, left associativity).
Notation "'let' x ':=' e1 'in' e2" := (exp_letin x e1 e2)
  (in custom expr at level 3, x constr,
  e1 custom expr at level 2, e2 custom expr at level 3,
  left associativity).

Fail Example letin_once : exp [::] :=
  [let "x" := {1%R}:R in %{"x"}].
Example letin_once : exp [::] :=
  [let "x" := {1%R}:R in {@exp_var [:: ("x", Real)] _ "x" erefl}].

Fixpoint acc (g : ctx) (i : nat) :
  Type_of_ctx R g -> @Type_of_typ R (nth Unit (map snd g) i) :=
  match g return Type_of_ctx R g -> Type_of_typ R (nth Unit (map snd g) i) with
  | [::] => match i with | O => id | j.+1 => id end
  | _ :: _ => match i with
               | O => fst
               | j.+1 => fun H => acc j H.2
               end
  end.
Arguments acc : clear implicits.

Inductive eval : forall g (t : typ), exp g -> (Type_of_ctx R g -> Type_of_typ R t) -> Prop :=
| eval_real g c : @eval g Real [c:R] (fun=> c)
| eval_plus g (e1 e2 : exp g) (v1 v2 : R) :
    @eval g Real e1 (fun=> v1) ->
    @eval g Real e2 (fun=> v2) ->
    @eval g Real [e1 + e2] (fun=> v1 + v2)
| eval_var (g : ctx) str i :
    i = index str (map fst g) -> eval [% str] (acc g i).

Goal @eval [::] Real [{1}:R] (fun=> 1).
Proof. exact: eval_real. Qed.
Goal @eval [::] Real [{1}:R + {2}:R] (fun=> 3).
Proof. exact/eval_plus/eval_real/eval_real. Qed.
Goal @eval [:: ("x", Real)] _ [% {"x"}] (acc [:: ("x", Real)] 0).
Proof. exact: eval_var. Qed.
Check [let "x" := {1}:R in %{"x"} + {2}:R] : exp [::].

End lang_intrinsic_sc.
End lang_intrinsic_sc.

Module lang_intrinsic_tysc.
Section lang_intrinsic_tysc.
Variable R : realType.
Implicit Types str : string.

Inductive exp : ctx -> typ -> Type :=
| exp_unit g : exp g Unit
| exp_real g : R -> exp g Real
| exp_var g t str : t = lookup Unit g str -> exp g t
| exp_add g : exp g Real -> exp g Real -> exp g Real
| exp_letin g t u str : exp g t -> exp ((str, t) :: g) u -> exp g u.
Arguments exp_unit {g}.
Arguments exp_real {g}.
Arguments exp_var {g t}.
Arguments exp_add {g}.
Arguments exp_letin {g t u}.

Example e0 : exp [::] _ := exp_real 1.
Example letin_once : exp [::] _ :=
  exp_letin "x" (exp_real 1) (exp_var "x" erefl).
Example letin_twice : exp [::] _ :=
  exp_letin "x" (exp_real 1) (exp_letin "y" (exp_real 2) (exp_var "x" erefl)).

Fail Example letin_plus : exp [::] _ :=
  exp_letin "x" (exp_real 1)
  (exp_letin "y" (exp_real 2)
   (exp_add (exp_var "x" erefl) (exp_var "y" erefl))).
Example letin_plus' : exp [::] _ :=
  exp_letin "x" (exp_real 1%:R)
  (exp_letin "y" (exp_real 2%:R)
   (exp_add (@exp_var [:: ("y", Real); ("x", Real)] Real "x" erefl)
         (exp_var "y" erefl))).

Definition exp_var' str (t : typ) (g : find str t) :=
  @exp_var (untag (ctx_of g)) t str (ctx_prf g).
Arguments exp_var' str {t} g.

Example letin_plus : exp [::] _ :=
  exp_letin "x" (exp_real 1)
  (exp_letin "y" (exp_real 2)
   (exp_add (exp_var' "x" _) (exp_var' "y" _))).

Declare Custom Entry expr.

Notation "[ e ]" := e (e custom expr at level 5).
Notation "{ x }" := x (in custom expr, x constr).
Notation "x ':R'" := (exp_real x) (in custom expr at level 1).
Notation "x" := x (in custom expr at level 0, x ident).
Notation "% x" := (exp_var x erefl) (in custom expr at level 1).
Notation "# x" := (exp_var' x%string _) (in custom expr at level 1).
Notation "x + y" := (exp_add x y)
  (in custom expr at level 2, left associativity).
Notation "'let' x ':=' e1 'in' e2" := (exp_letin x e1 e2)
  (in custom expr at level 3, x constr,
  e1 custom expr at level 2, e2 custom expr at level 3,
  left associativity).

Example letin_plus_custom : exp [::] _ :=
  [let "x" := {1}:R in
   let "y" := {2}:R in
   #{"x"} + #{"y"}].

Section eval.

Fixpoint acc (g : ctx) (i : nat) :
  Type_of_ctx R g -> @Type_of_typ R (nth Unit (map snd g) i) :=
  match g return Type_of_ctx R g -> Type_of_typ R (nth Unit (map snd g) i) with
  | [::] => match i with | O => id | j.+1 => id end
  | _ :: _ => match i with
               | O => fst
               | j.+1 => fun H => acc j H.2
               end
  end.
Arguments acc : clear implicits.

Reserved Notation "e '-e->' v" (at level 40).

Inductive eval : forall g t, exp g t -> (Type_of_ctx R g -> Type_of_typ R t) -> Prop :=
| eval_tt g : (exp_unit : exp g _) -e-> (fun=> tt)
| eval_real g c : (exp_real c : exp g _) -e-> (fun=> c)
| eval_plus g (e1 e2 : exp g Real) v1 v2 :
    e1 -e-> v1 ->
    e2 -e-> v2 ->
    [e1 + e2] -e-> fun x => v1 x + v2 x
| eval_var g str :
    let i := index str (map fst g) in
    exp_var str erefl -e-> acc g i
| eval_letin g t t' str (e1 : exp g t) (e2 : exp ((str, t) :: g)  t') v1 v2 :
    e1 -e-> v1 ->
    e2 -e-> v2 ->
    exp_letin str e1 e2 -e-> (fun a => v2 (v1 a, a))
where "e '-e->' v" := (@eval _ _ e v).

Lemma eval_uniq g t (e : exp g t) u v :
  e -e-> u -> e -e-> v -> u = v.
Proof.
move=> hu.
apply: (@eval_ind
  (fun g t (e : exp g t) (u : Type_of_ctx R g -> Type_of_typ R t) =>
    forall v, e -e-> v -> u = v)); last exact: hu.
all: (rewrite {g t e u v hu}).
- move=> g v.
  inversion 1.
  by inj_ex H3.
- move=> g c v.
  inversion 1.
  by inj_ex H3.
- move=> g e1 e2 v1 v2 ev1 IH1 ev2 IH2 v.
  inversion 1.
  inj_ex H0; inj_ex H1; subst.
  inj_ex H5; subst.
  by rewrite (IH1 _ H3) (IH2 _ H4).
- move=> g x i v.
  inversion 1.
  by inj_ex H6; subst.
- move=> g t t' x0 e0 e1 v1 v2 ev1 IH1 ev2 IH2 v.
  inversion 1.
  inj_ex H5; subst.
  inj_ex H6; subst.
  inj_ex H7; subst.
  by rewrite (IH1 _ H4) (IH2 _ H8).
Qed.

Lemma eval_total g t (e : exp g t) : exists v, e -e-> v.
Proof.
elim: e.
- by eexists; exact: eval_tt.
- by eexists; exact: eval_real.
- move=> {}g {}t x e; subst t.
  by eexists; exact: eval_var.
- move=> {}g e1 [v1] IH1 e2 [v2] IH2.
  by eexists; exact: (eval_plus IH1 IH2).
- move=> {}g {}t u x e1 [v1] IH1 e2 [v2] IH2.
  by eexists; exact: (eval_letin IH1 IH2).
Qed.

Definition exec g t (e : exp g t) : Type_of_ctx R g -> Type_of_typ R t :=
  proj1_sig (cid (@eval_total g t e)).

Lemma exec_eval g t (e : exp g t) v : exec e = v <-> e -e-> v.
Proof.
split.
  by move=> <-; rewrite /exec; case: cid.
move=> ev.
by rewrite /exec; case: cid => f H/=; apply: eval_uniq; eauto.
Qed.

Lemma eval_exec g t (e : exp g t) : e -e-> exec e.
Proof. by rewrite /exec; case: cid. Qed.

Lemma exec_real g r : @exec g Real (exp_real r) = (fun=> r).
Proof. exact/exec_eval/eval_real. Qed.

Lemma exec_var g str t H :
  exec (@exp_var  _ t str H) =
    eq_rect _ (fun a => Type_of_ctx R g -> Type_of_typ R a)
      (acc g (index str (map fst g)))
        _ (esym H).
Proof.
subst t.
rewrite {1}/exec.
case: cid => f H.
inversion H; subst g0 str0.
by inj_ex H6; subst f.
Qed.

Lemma exp_var'E str t (f : find str t) H : exp_var' str f = exp_var str H.
Proof. by rewrite /exp_var'; congr exp_var. Qed.

Lemma exec_letin g x t1 t2 (e1 : exp g t1) (e2 : exp ((x, t1) :: g) t2) :
  exec [let x := e1 in e2] = (fun a => (exec e2) ((exec e1) a, a)).
Proof. by apply/exec_eval/eval_letin; exact: eval_exec. Qed.

Goal ([{1}:R] : exp [::] _) -e-> (fun=> 1).
Proof. exact: eval_real. Qed.
Goal @eval [::] _ [{1}:R + {2}:R] (fun=> 3).
Proof. exact/eval_plus/eval_real/eval_real. Qed.
Goal @eval [:: ("x", Real)] _ (exp_var "x" erefl) (@acc [:: ("x", Real)] 0).
Proof. exact: eval_var. Qed.
Goal @eval [::] _ [let "x" := {1}:R in #{"x"}] (fun=> 1).
Proof.
apply/exec_eval; rewrite exec_letin/=.
apply/funext => t/=.
by rewrite exp_var'E exec_real/= exec_var/=.
Qed.

Goal exec (g := [::]) [let "x" := {1}:R in #{"x"}] = (fun=> 1).
Proof.
rewrite exec_letin//=.
apply/funext => x.
by rewrite exp_var'E exec_var/= exec_real.
Qed.

End eval.

End lang_intrinsic_tysc.
End lang_intrinsic_tysc.
