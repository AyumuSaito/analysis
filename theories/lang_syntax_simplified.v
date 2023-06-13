Require Import String.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp.classical Require Import mathcomp_extra boolp classical_sets.
From mathcomp.classical Require Import functions cardinality fsbigop.
Require Import signed reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure numfun lebesgue_integral kernel.
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

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Declare Scope easylang_scope.

Section type.
Variables (R : realType).

Inductive typ := Real | Unit.

Canonical typ_eqType := Equality.Pack (@gen_eqMixin typ).

Fixpoint iter_pair (l : list Type) : Type :=
  match l with
  | [::] => unit
  | h :: t => let t' := iter_pair t in (h * t')%type
  end.

Definition Type_of_typ (t : typ) : Type :=
  match t with
  | Real => R
  | Unit => unit
  end.

Definition ctx := seq (string * typ)%type.

Definition ctxi (g : ctx) := iter_pair (map (Type_of_typ \o snd) g).

Goal ctxi [:: ("x", Real); ("y", Real)] = (R * (R * unit))%type.
Proof. by []. Qed.

End type.

Module lang_extrinsic.
Section lang_extrinsic.
Variables (R : realType).

Section exp.
Inductive exp : Type :=
| TT : exp
| Cst : R -> exp
| Var g T (str : string) :
  T = nth Real (map snd g) (index str (map fst g)) -> exp
| Letin (str : string) : exp -> exp -> exp
| Plus : exp -> exp -> exp.
End exp.

Arguments Var {g T}.
Declare Custom Entry exp.

Notation "[ e ]" := e (e custom exp at level 5) : easylang_scope.
Notation "x ':R'" := (Cst x) (in custom exp at level 1)
  : easylang_scope.
Notation "x + y" := (Plus x y) (in custom exp at level 2)
  : easylang_scope.
Notation "% x" := (Var x erefl) (in custom exp at level 1)
  : easylang_scope.
Notation "'Let' x '<~' e1 'In' e2" := (Letin x e1 e2) (in custom exp at level 3,
   x constr,
   e1 custom exp at level 2,
   e2 custom exp at level 3,
   left associativity) : easylang_scope.
Notation "{ x }" := x (in custom exp, x constr) : easylang_scope.
Notation "x" := x (in custom exp at level 0, x ident) : easylang_scope.

Local Open Scope easylang_scope.

Fail Example letin_once := @Letin "x" (Cst 1) (Var "x" erefl).
Example letin_once := @Letin "x" (Cst 1) (@Var [:: ("x", Real)] Real "x" erefl).

End lang_extrinsic.
End lang_extrinsic.

Module lang_intrinsic_ty.
Section lang_intrinsic_ty.
Variables (R : realType).

Section exp.
Inductive exp : typ -> Type :=
| TT : exp Unit
| Cst : R -> exp Real
| Plus : exp Real -> exp Real -> exp Real
| Var g T (str : string) :
  T = nth Unit (map snd g) (index str (map fst g)) -> exp T
| Letin t u : string -> exp t -> exp u -> exp u.
End exp.
Arguments Var {g T}.

Fail Example letin_once := (Letin "x" (Cst 1%R) (Var "x" erefl)).
Example letin_once := (Letin "x" (Cst 1%R) (@Var [:: ("x", Real)] _ "x" erefl)).

End lang_intrinsic_ty.
End lang_intrinsic_ty.

Module lang_intrinsic_sc.
Section lang_intrinsic_sc.
Variables (R : realType).

Section exp.
Inductive exp : ctx -> Type :=
| TT g : exp g
| Cst g : R -> exp g
| Plus g : exp g -> exp g -> exp g
| Var g T (str : string) :
  T = nth Unit (map snd g) (index str (map fst g)) -> exp g
| Letin g t (x : string) : exp g -> exp ((x, t) :: g) -> exp g.
End exp.
Arguments Var {g T}.
Arguments Cst {g}.
Arguments Letin {g t}.

Declare Custom Entry exp.
Notation "[ e ]" := e (e custom exp at level 5) : easylang_scope.
Notation "x ':R'" := (Cst x) (in custom exp at level 1)
  : easylang_scope.
Notation "x + y" := (Plus x y) (in custom exp at level 2)
  : easylang_scope.
Notation "% x" := (Var x erefl) (in custom exp at level 1)
  : easylang_scope.
Notation "'Let' x '<~' e1 'In' e2" := (Letin x e1 e2) (in custom exp at level 3,
   x constr,
   e1 custom exp at level 2,
   e2 custom exp at level 3,
   left associativity) : easylang_scope.
Notation "{ x }" := x (in custom exp, x constr) : easylang_scope.
Notation "x" := x (in custom exp at level 0, x ident) : easylang_scope.

Local Open Scope easylang_scope.

Fail Example letin_once := (Letin "x" (Cst 1) (Var "x" erefl)) : exp [::].
Example letin_once := (Letin "x" (Cst 1) (@Var [:: ("x", Real)] _ "x" erefl)) : exp [::].

Fixpoint acc (g : ctx) (i : nat) :
  ctxi R g -> @Type_of_typ R (nth Unit (map snd g) i) :=
  match g return (ctxi R g -> Type_of_typ R (nth Unit (map snd g) i)) with
  | [::] => match i with | O => id | j.+1 => id end
  | _ :: _ => match i with
               | O => fst
               | j.+1 => fun H => acc j H.2
               end
  end.

Inductive eval : forall (g : ctx) (t : typ), exp g -> (ctxi R g -> Type_of_typ R t) -> Prop :=
| eval_real g c : @eval g Real (Cst c) (fun=> c)
| eval_plus g (e1 e2 : exp g) (v1 v2 : R) :
    @eval g Real e1 (fun=> v1) ->
    @eval g Real e2 (fun=> v2) ->
    @eval g Real (Plus e1 e2) (fun=> (v1 + v2)%R)
| eval_var (g : ctx) (x : string) i :
    i = index x (map fst g) -> eval (Var x erefl) (@acc g i).

Goal @eval [::] Real [{1%R}:R] (fun=> 1%R).
Proof. exact/eval_real. Qed.
Goal @eval [::] Real [{1%R}:R + {2%R}:R] (fun=> 3%R).
Proof. exact/eval_plus/eval_real/eval_real. Qed.
Goal @eval [:: ("x", Real)] _ [% {"x"}] (@acc [:: ("x", Real)] 0).
Proof. exact: eval_var. Qed.
Check [Let "x" <~ {1%R}:R In %{"x"} + {2}:R].

End lang_intrinsic_sc.
End lang_intrinsic_sc.

Module lang_intrinsic_tysc.
Section lang_intrinsic_tysc.
Variables (R : realType).

Section exp.
Inductive exp : ctx -> typ -> Type :=
| TT g : exp g Unit
| Cst g : R -> exp g Real
| Plus g : exp g Real -> exp g Real -> exp g Real
| Var g T (str : string) :
    (* (x, T) \in G ->  *)
    T = nth Unit (map snd g) (index str (map fst g)) ->
    exp g T
| Letin g t u (x : string) : exp g t -> exp ((x, t) :: g) u -> exp g u.
End exp.

Arguments TT {g}.
Arguments Cst {g}.
Arguments Plus {g}.
Arguments Var {g T}.
Arguments Letin {g t u}.

Declare Custom Entry exp.
Notation "[ e ]" := e (e custom exp at level 5) : easylang_scope.
Notation "x ':R'" := (Cst x) (in custom exp at level 1)
  : easylang_scope.
Notation "x + y" := (Plus x y) (in custom exp at level 2)
  : easylang_scope.
Notation "% x" := (Var x erefl) (in custom exp at level 1)
  : easylang_scope.
Notation "'Let' x '<~' e1 'In' e2" := (Letin x e1 e2) (in custom exp at level 3,
   x constr,
   e1 custom exp at level 2,
   e2 custom exp at level 3,
   left associativity) : easylang_scope.
Notation "{ x }" := x (in custom exp, x constr) : easylang_scope.
Notation "x" := x (in custom exp at level 0, x ident) : easylang_scope.

Local Open Scope easylang_scope.

Example e0 := [{1%R}:R] : exp [::] _.
Example letin_once := (Letin "x" (Cst 1%R) (Var "x" erefl)) : exp [::] _.
Example letin_twice := (Letin "x" (Cst 1%R) (Letin "y" (Cst 2%R) (Var "x" erefl))) : exp [::] _.

Fail Example letin_plus := Letin "x" (Cst 1%R) (Letin "y" (Cst 2%R) (Plus (Var "x" erefl) (Var "y" erefl))) : exp [::] _.
Example letin_plus' := Letin "x" (Cst 1%:R)
                      (Letin "y" (Cst 2%:R)
                      (Plus (@Var [:: ("y", Real); ("x", Real)] Real "x" erefl) (Var "y" erefl))) : exp [::] _.

Definition Var' (x : string) (t : typ) (g : find x t) :=
  @Var (untag (ctx_of g)) t x (ctx_prf g).

Notation "# x" := (@Var' x%string _ _) (in custom exp at level 1) : easylang_scope.

Example letin_plus := Letin "x" (Cst 1%R) (Letin "y" (Cst 2%R) (Plus (@Var' "x" _ _) (@Var' "y" _ _))) : exp [::] _.

Section eval.

Fixpoint acc (g : ctx) (i : nat) :
  ctxi R g -> @Type_of_typ R (nth Unit (map snd g) i) :=
  match g return (ctxi R g -> Type_of_typ R (nth Unit (map snd g) i)) with
  | [::] => match i with | O => id | j.+1 => id end
  | _ :: _ => match i with
               | O => fst
               | j.+1 => fun H => acc j H.2
               end
  end.

Reserved Notation "e '-e->' v" (at level 40).

Inductive eval : forall g t, exp g t -> (ctxi R g -> Type_of_typ R t) -> Prop :=
| eval_tt g : (TT : exp g _) -e-> (fun=> tt)
| eval_real g c : (Cst c : exp g _) -e-> (fun=> c)
| eval_plus g (e1 e2 : exp g Real) v1 v2 :
    e1 -e-> v1 ->
    e2 -e-> v2 ->
    Plus e1 e2 -e-> (fun x => v1 x + v2 x)%R
| eval_var g str :
    let i := index str (map fst g) in
    Var str erefl -e-> @acc g i
| eval_letin g t t' str (e1 : exp g t) (e2 : exp ((str, t) :: g)  t') v1 v2 :
    e1 -e-> v1 ->
    e2 -e-> v2 ->
    Letin str e1 e2 -e-> (fun a => v2 (v1 a, a))
where "e '-e->' v" := (@eval _ _ e v).

Scheme eval_ind' := Induction for eval Sort Prop.

Lemma eval_uniq g t (e : exp g t) u v :
  e -e-> u -> e -e-> v -> u = v.
Proof.
move=> hu.
apply: (@eval_ind
  (fun g t (e : exp g t) (u : ctxi R g -> Type_of_typ R t) => forall v, e -e-> v -> u = v)); last exact: hu.
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

Definition exec g t (e : exp g t) : ctxi R g -> Type_of_typ R t.
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

Goal ([{1%R}:R] : exp [::] _) -e-> (fun=> 1%R).
Proof. exact/eval_real. Qed.
Goal @eval [::] _ [{1%R}:R + {2}:R] (fun=> 3%R).
Proof. exact/eval_plus/eval_real/eval_real. Qed.
Goal @eval [:: ("x", Real)] _ [% {"x"}] (@acc [:: ("x", Real)] 0).
Proof. exact: eval_var. Qed.
Goal @eval [::] _ [Let "x" <~ {1%R}:R In %{"x"}] (fun=> 1%R).
Proof. exact: (eval_letin (eval_real _ _) (eval_var _ _)). Qed.

Goal exec (g := [::]) [Let "x" <~ {1%R}:R In %{"x"}] = (fun=> 1%R).
Proof.
apply: eval_uniq; first exact: eval_exec.
exact: (eval_letin (eval_real _ _) (eval_var _ _)).
Qed.

End eval.

End lang_intrinsic_tysc.
End lang_intrinsic_tysc.
