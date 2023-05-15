From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp.classical Require Import mathcomp_extra boolp classical_sets.
From mathcomp.classical Require Import functions cardinality fsbigop.
Require Import signed reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure numfun lebesgue_integral kernel.

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

Declare Scope easylang_scope.

Section string_eq.

Definition string_eqMixin := @EqMixin string eqb eqb_spec.
Canonical string_eqType := EqType string string_eqMixin.

Definition x := "x".
Definition y := "y".

End string_eq.

Section type.
Variables (R : realType).

Inductive Ty := TReal | TUnit
  | TArrow : Ty -> Ty -> Ty.

Fixpoint typei (t : Ty) : Type :=
  match t with
  | TReal => R
  | TUnit => unit
  | TArrow t u => typei t -> typei u
  end.

End type.

Definition Ctx := seq (string * Ty)%type.

Module lang_syntax_simple.
Section expression.
Variables (R : realType).

Inductive exp (g : Ctx) : Ty -> Type :=
| Real : R -> exp g TReal
| Var t x : t = nth TUnit (map snd g) (seq.index x (map fst g)) ->
  exp g t
(* | App t u : exp g (TArrow t u) -> exp g t -> exp g u *)
| Letin t u x : exp g t -> exp ((x, t) :: g) u -> exp g u
| Plus : exp g TReal -> exp g TReal -> exp g TReal
.

End expression.

Arguments Real {R g}.
Arguments Var {R g _}.
Arguments Letin {R g _ _}.

Declare Custom Entry exp.
Notation "[ e ]" := e (e custom exp at level 5) : easylang_scope.
Notation "x ':r'" := (@Real _ _ x%R) (in custom exp at level 1) 
  : easylang_scope.
Notation "x + y" := (Plus x y) (in custom exp at level 1) 
  : easylang_scope.
Notation "% x" := (Var x erefl) (in custom exp at level 1) 
  : easylang_scope.
Notation "'Let' x '<~' e 'In' f" := (Letin x e f)
  (in custom exp at level 3,
   x constr,
   (* e custom expr at level 2, *)
   f custom exp at level 2,
   left associativity) : easylang_scope.
Notation "{ x }" := x (in custom exp, x constr) : easylang_scope.
Notation "x" := x (in custom exp at level 0, x ident) : easylang_scope.

Local Open Scope easylang_scope.
Section example.
Variables (R : realType).

Fail Definition e1 := [Let "x" <~ {1%:R}:r In %{"x"}].

Fail Example e3 := [Let x <~ {1%:R}:r In
                    Let y <~ {2%:R}:r In 
                    %x] : exp R [::].

Structure tagged_context := Tag {untag : Ctx}.

Definition recurse_tag h := Tag h.
Canonical found_tag h := recurse_tag h.

Structure find (s : string) (t : Ty) := Find {
  context_of : tagged_context ;
  ctxt_prf : t = nth TUnit (map snd (untag context_of))
                           (seq.index s (map fst (untag context_of)))}.

Lemma left_pf (s : string) (t : Ty) (l : Ctx) :
  t = nth TUnit (map snd ((s, t) :: l)) (seq.index s (map fst ((s, t) :: l))).
Proof.
by rewrite /= !eqxx/=.
Qed.

Canonical found_struct s t (l : Ctx) : find s t :=
  Eval hnf in @Find s t (found_tag ((s, t) :: l)) (@left_pf s t l).

Lemma right_pf (s : string) (t : Ty) (l : Ctx) u t' :
  s != u ->
  t' = nth TUnit (map snd l) (seq.index u (map fst l)) ->
  t' = nth TUnit (map snd ((s, t) :: l)) (seq.index u (map fst ((s, t) :: l))).
Proof.
move=> su ut'l /=.
case: ifPn => //=.
by rewrite (negbTE su).
Qed.

Canonical recurse_struct s t t' u {su : infer (s != u)} (l : find u t') : find u t' :=
  Eval hnf in @Find u t' (recurse_tag ((s, t) :: untag (context_of l)))
  (@right_pf s t (untag (context_of l)) u t' su (ctxt_prf l)).

Definition Var' (x : string) (t : Ty) (g : find x t) :=
  @Var R (untag (context_of g)) t x (ctxt_prf g).

Notation "%1 x" := (@Var' x%string _ _) (in custom exp at level 1) : easylang_scope.

Example e1 := [Let x <~ {1%:R}:r In %1{"x"}] : exp R [::] _.

Example e2 := [Let "x" <~ {1%:R}:r In Let "y" <~ %{"x"} In %{"y"}] : exp R [::] TReal.

Goal (0 = seq.index 1 [:: 1; 2])%nat.
exact: erefl.
Abort.
Goal False.
evar (a : list nat).
have : (0 = seq.index 1 (1 :: a))%nat.
exact: erefl.
(* Print a. *)
Abort.

Example e3 := Letin "x" (Real 1%:R) 
              (Letin "y" (Real 2%:R) 
              (Plus (@Var R [:: ("y", TReal); ("x", TReal)] TReal x erefl) (Var "y" erefl))) : exp R [::] _.
               
Example e4 := [Let x <~ {1%:R}:r In
               Let y <~ {2%:R}:r In 
               %1{x} + %1{y}] : exp R [::] _.

End example.

End lang_syntax_simple.

Module withoutType.

Section expression.
Variables (R : realType).

Inductive exp (g : list string) : Type :=
| Real : R -> exp g
| Var x : x \in g -> exp g
(* | App t u : exp g (TArrow t u) -> exp g t -> exp g u *)
| Letin x : exp g -> exp (x :: g) -> exp g
| Plus : exp g -> exp g -> exp g
.

End expression.

Arguments Real {R g}.
Arguments Var {R g}.
Arguments Letin {R g}.

(* Declare Custom Entry exp. *)
Notation "[ e ]" := e (e custom exp at level 5) : easylang_scope.
Notation "x ':r'" := (@Real _ _ x%R) (in custom exp at level 1) 
  : easylang_scope.
Notation "x + y" := (Plus x y) (in custom exp at level 1) 
  : easylang_scope.
Notation "% x" := (Var x erefl) (in custom exp at level 1) 
  : easylang_scope.
Notation "'Let' x '<~' e 'In' f" := (Letin x e f)
  (in custom exp at level 3,
   x constr,
   (* e custom expr at level 2, *)
   f custom exp at level 2,
   left associativity) : easylang_scope.
Notation "{ x }" := x (in custom exp, x constr) : easylang_scope.
Notation "x" := x (in custom exp at level 0, x ident) : easylang_scope.

Local Open Scope easylang_scope.
Section example.
Variables (R : realType).

Fail Definition e1 := [Let "x" <~ {1%:R}:r In %{"x"}].

Fail Example e := [Let x <~ {1%:R}:r In
                   Let y <~ {2%:R}:r In 
                   %x] : exp R [::].

Example e := [Let x <~ {1%:R}:r In
               Let y <~ {2%:R}:r In 
               {@Var R [:: y; x] x erefl}] : exp R [::].

End example.
End withoutType.


Section eval.
Variables (R : realType).

End eval.