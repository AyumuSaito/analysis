Require Import String.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg.
From mathcomp.classical Require Import mathcomp_extra boolp.
Require Import signed reals topology normedtype.
Require Import lang_syntax_util.

(******************************************************************************)
(*                 Various types of the definition of syntax                  *)
(*                                                                            *)
(* lang_extrinsic : non-intrinsic definition of expression                    *)
(* lang_intrinsic_ty : intrinsically-typed syntax                             *)
(* lang_intrinsic_sc : intrinsically-scoped syntax                            *)
(* lang_intrinsic_tysc : intrinsically-typed/scoped syntax                    *)
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
| TT : exp
| Cst : R -> exp
| Var (g : ctx) T str :
  T = nth Real (map snd g) (index str (map fst g)) -> exp
| Letin str : exp -> exp -> exp
| Plus : exp -> exp -> exp.
Arguments Var {g T}.

Fail Example letin_once : exp := @Letin "x" (Cst 1) (Var "x" erefl).
Example letin_once : exp :=
  @Letin "x" (Cst 1) (@Var [:: ("x", Real)] Real "x" erefl).

End lang_extrinsic.
End lang_extrinsic.

Module lang_intrinsic_ty.
Section lang_intrinsic_ty.
Variable R : realType.
Implicit Types str : string.

Inductive exp : typ -> Type :=
| TT : exp Unit
| Cst : R -> exp Real
| Plus : exp Real -> exp Real -> exp Real
| Var g T str :
  T = nth Unit (map snd g) (index str (map fst g)) -> exp T
| Letin t u : string -> exp t -> exp u -> exp u.
Arguments Var {g T}.

Fail Example letin_once : exp Real := Letin "x" (Cst 1) (Var "x" erefl).
Example letin_once : exp Real :=
  Letin "x" (Cst 1) (@Var [:: ("x", Real)] _ "x" erefl).

End lang_intrinsic_ty.
End lang_intrinsic_ty.

Module lang_intrinsic_sc.
Section lang_intrinsic_sc.
Variable R : realType.
Implicit Types str : string.

Inductive exp : ctx -> Type :=
| TT g : exp g
| Cst g : R -> exp g
| Plus g : exp g -> exp g -> exp g
| Var g T str :
  T = nth Unit (map snd g) (index str (map fst g)) -> exp g
| Letin g t str : exp g -> exp ((str, t) :: g) -> exp g.
Arguments Var {g T}.
Arguments Cst {g}.
Arguments Letin {g t}.

Declare Custom Entry expr.

Notation "[ e ]" := e (e custom expr at level 5).
Notation "{ x }" := x (in custom expr, x constr).
Notation "x ':R'" := (Cst x) (in custom expr at level 1).
Notation "x" := x (in custom expr at level 0, x ident).
Notation "% x" := (Var x erefl) (in custom expr at level 1).
Notation "x + y" := (Plus x y) (in custom expr at level 2, left associativity).
Notation "'let' x ':=' e1 'in' e2" := (Letin x e1 e2) (in custom expr at level 3,
  x constr,
  e1 custom expr at level 2, e2 custom expr at level 3,
  left associativity).

Fail Example letin_once : exp [::] := [let "x" := {1%R}:R in %{"x"}].
Example letin_once : exp [::] :=
  [let "x" := {1%R}:R in {@Var [:: ("x", Real)] _ "x" erefl}].

Fixpoint acc (g : ctx) (i : nat) :
  Type_of_ctx R g -> @Type_of_typ R (nth Unit (map snd g) i) :=
  match g return Type_of_ctx R g -> Type_of_typ R (nth Unit (map snd g) i) with
  | [::] => match i with | O => id | j.+1 => id end
  | _ :: _ => match i with
               | O => fst
               | j.+1 => fun H => acc j H.2
               end
  end.

Inductive eval : forall g (t : typ), exp g -> (Type_of_ctx R g -> Type_of_typ R t) -> Prop :=
| eval_real g c : @eval g Real [c:R] (fun=> c)
| eval_plus g (e1 e2 : exp g) (v1 v2 : R) :
    @eval g Real e1 (fun=> v1) ->
    @eval g Real e2 (fun=> v2) ->
    @eval g Real [e1 + e2] (fun=> v1 + v2)
| eval_var (g : ctx) str i :
    i = index str (map fst g) -> eval [% str] (@acc g i).

Goal @eval [::] Real [{1}:R] (fun=> 1).
Proof. exact: eval_real. Qed.
Goal @eval [::] Real [{1}:R + {2}:R] (fun=> 3).
Proof. exact/eval_plus/eval_real/eval_real. Qed.
Goal @eval [:: ("x", Real)] _ [% {"x"}] (@acc [:: ("x", Real)] 0).
Proof. exact: eval_var. Qed.
Check [let "x" := {1}:R in %{"x"} + {2}:R] : exp [::].

End lang_intrinsic_sc.
End lang_intrinsic_sc.

Module lang_intrinsic_tysc.
Section lang_intrinsic_tysc.
Variable R : realType.
Implicit Types str : string.

Inductive exp : ctx -> typ -> Type :=
| TT g : exp g Unit
| Cst g : R -> exp g Real
| Plus g : exp g Real -> exp g Real -> exp g Real
| Var g T str :
    T = nth Unit (map snd g) (index str (map fst g)) ->
    exp g T
| Letin g t u str : exp g t -> exp ((str, t) :: g) u -> exp g u.
Arguments TT {g}.
Arguments Cst {g}.
Arguments Plus {g}.
Arguments Var {g T}.
Arguments Letin {g t u}.

Example e0 : exp [::] _ := Cst 1.
Example letin_once : exp [::] _ := Letin "x" (Cst 1) (Var "x" erefl).
Example letin_twice : exp [::] _ :=
  Letin "x" (Cst 1) (Letin "y" (Cst 2) (Var "x" erefl)).

Fail Example letin_plus : exp [::] _ :=
  Letin "x" (Cst 1)
  (Letin "y" (Cst 2)
   (Plus (Var "x" erefl) (Var "y" erefl))).
Example letin_plus' : exp [::] _ :=
  Letin "x" (Cst 1%:R)
  (Letin "y" (Cst 2%:R)
   (Plus (@Var [:: ("y", Real); ("x", Real)] Real "x" erefl)
         (Var "y" erefl))).

Definition Var' str (t : typ) (g : find str t) :=
  @Var (untag (ctx_of g)) t str (ctx_prf g).

Example letin_plus : exp [::] _ :=
  Letin "x" (Cst 1)
  (Letin "y" (Cst 2)
   (Plus (@Var' "x" _ _) (@Var' "y" _ _))).

Declare Custom Entry expr.

Notation "[ e ]" := e (e custom expr at level 5).
Notation "{ x }" := x (in custom expr, x constr).
Notation "x ':R'" := (Cst x) (in custom expr at level 1).
Notation "x" := x (in custom expr at level 0, x ident).
Notation "% x" := (Var x erefl) (in custom expr at level 1).
Notation "x + y" := (Plus x y) (in custom expr at level 2, left associativity).
Notation "'let' x ':=' e1 'in' e2" := (Letin x e1 e2) (in custom expr at level 3,
  x constr,
  e1 custom expr at level 2, e2 custom expr at level 3,
  left associativity).


Notation "# x" := (@Var' x%string _ _) (in custom expr at level 1).

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

Reserved Notation "e '-e->' v" (at level 40).

Inductive eval : forall g t, exp g t -> (Type_of_ctx R g -> Type_of_typ R t) -> Prop :=
| eval_tt g : (TT : exp g _) -e-> (fun=> tt)
| eval_real g c : (Cst c : exp g _) -e-> (fun=> c)
| eval_plus g (e1 e2 : exp g Real) v1 v2 :
    e1 -e-> v1 ->
    e2 -e-> v2 ->
    Plus e1 e2 -e-> fun x => v1 x + v2 x
| eval_var g str :
    let i := index str (map fst g) in
    Var str erefl -e-> @acc g i
| eval_letin g t t' str (e1 : exp g t) (e2 : exp ((str, t) :: g)  t') v1 v2 :
    e1 -e-> v1 ->
    e2 -e-> v2 ->
    Letin str e1 e2 -e-> (fun a => v2 (v1 a, a))
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
eexists; exact: eval_tt.
eexists; exact: eval_real.
move=> {}g e1 [v1] IH1 e2 [v2] IH2.
eexists; exact: (eval_plus IH1 IH2).
move=> {}g {}t x e; subst t.
eexists; exact: eval_var.
move=> {}g {}t u x e1 [v1] IH1 e2 [v2] IH2.
eexists; exact: (eval_letin IH1 IH2).
Qed.

Definition exec g t (e : exp g t) : Type_of_ctx R g -> Type_of_typ R t.
Proof.
have /cid h := @eval_total g t e.
exact: (proj1_sig h).
Defined.

Lemma eval_exec g t e : e -e-> @exec g t e.
Proof. by rewrite /exec/= /sval; case: cid. Qed.

Lemma exec_real g r : @exec g Real (Cst r) = (fun=> r).
Proof.
apply: eval_uniq.
exact: eval_exec.
apply: eval_real.
Qed.

Goal ([{1}:R] : exp [::] _) -e-> (fun=> 1).
Proof. exact: eval_real. Qed.
Goal @eval [::] _ [{1}:R + {2}:R] (fun=> 3).
Proof. exact/eval_plus/eval_real/eval_real. Qed.
Goal @eval [:: ("x", Real)] _ [% {"x"}] (@acc [:: ("x", Real)] 0).
Proof. exact: eval_var. Qed.
Goal @eval [::] _ [let "x" := {1}:R in %{"x"}] (fun=> 1).
Proof. exact: (eval_letin (eval_real _ _) (eval_var _ _)). Qed.

Goal exec (g := [::]) [let "x" := {1}:R in %{"x"}] = (fun=> 1).
Proof.
apply: eval_uniq; first exact: eval_exec.
exact: (eval_letin (eval_real _ _) (eval_var _ _)).
Qed.

End eval.

End lang_intrinsic_tysc.
End lang_intrinsic_tysc.
