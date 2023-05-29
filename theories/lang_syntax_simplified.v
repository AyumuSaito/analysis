From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp.classical Require Import mathcomp_extra boolp classical_sets.
From mathcomp.classical Require Import functions cardinality fsbigop.
Require Import signed reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure numfun lebesgue_integral kernel.

(**************************************************************)
(*        Various types of the definition of syntax           *)
(* lang_extrinsic : non-intrinsic definition of expression    *)
(* lang_intrinsic_ty : intrinsically-typed syntax             *)
(* lang_intrinsic_sc : intrinsically-scoped syntax            *)
(* lang_intrinsic_tysc : intrinsically-typed/scoped syntax    *)
(*                                                            *)
(**************************************************************)

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
  | TArrow : Ty -> Ty -> Ty
  | TList : seq Ty -> Ty
  .

Fixpoint prod_meas (l : list Type)
    : Type :=
  match l with
  | [::] => unit
  | h :: t => let t' := prod_meas t in (h * t')%type
  end.

Fixpoint typei (t : Ty) : Type :=
  match t with
  | TReal => R
  | TUnit => unit
  | TArrow t u => typei t -> typei u
  | TList l => prod_meas (map typei l)
  end.

Definition Ctx := seq (string * Ty)%type.

Definition ctxi (G : Ctx) := prod_meas (map (typei \o snd) G).

Goal ctxi [:: ("x", TReal); ("y", TReal)] = (R * (R * unit))%type.
Proof. by []. Qed.

End type.

Module lang_extrinsic.
Section lang_extrinsic.
Variables (R : realType).

Section exp.
Inductive exp : Type :=
| Real : R -> exp
| Var G T (x : string) : 
  T = nth TReal (map snd G) (seq.index x (map fst G)) -> exp
| Letin (x : string) : exp -> exp -> exp
| Plus : exp -> exp -> exp.
End exp.

Arguments Var {G T}.
Declare Custom Entry exp.

Notation "[ e ]" := e (e custom exp at level 5) : easylang_scope.
Notation "x ':r'" := (Real x) (in custom exp at level 1) 
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

Example e1' := @Letin "x" (Real 1) (@Var [:: ("x", TReal)] TReal x erefl).
Fail Example e1 := [Let x <~ {1%:R}:r In %{"x"}].
Fail Example e2 := [Let "x" <~ {1%:R}:r In Let "y" <~ %{"x"} In %{"y"}].
Fail Example e3 := [Let x <~ {1%:R}:r In
               Let y <~ {2%:R}:r In 
               %{x} + %{y}].

Fixpoint acc (g : Ctx) (i : nat) :
  ctxi R g -> @typei R (nth TUnit (map snd g) i) :=
  match g return (ctxi R g -> typei R (nth TUnit (map snd g) i)) with
  | [::] => match i with | O => id | j.+1 => id end
  | _ :: _ => match i with
               | O => fst
               | j.+1 => fun H => acc j H.2
               end
  end.


Inductive eval : forall (g : Ctx) (t : Ty), exp -> (ctxi R g -> typei R t) -> Prop :=
| EVReal g c : @eval g TReal (Real c) (fun=> c)
| EVPlus g e1 e2 (v1 v2 : R) : 
    @eval g TReal e1 (fun=> v1) -> 
    @eval g TReal e2 (fun=> v2) -> 
    @eval g TReal (Plus e1 e2) (fun=> (v1 + v2)%R)
(* | EVVar (g : Ctx) (t : Ty) (x : string) : 
  let i := seq.index x (map fst g) in @eval g t (Var x) (@acc (map snd g) i) *)
(* | EVLetin (g : Ctx) (t : Ty) (x : string) e1 e2 v1 (v2 : R -> R) :
    @eval g TReal e1 (fun=> v1) ->
    @eval ((x, TReal) :: g) TReal e2 (fun x => v2 x) ->
    @eval g TReal (Letin x e1 e2) (fun=> v2 v1) *)
.

Fail Compute eval [::] (Const 1) (fun=> 1%R).

End lang_extrinsic.
End lang_extrinsic.

Module lang_intrinsic_ty.
Section lang_intrinsic_ty.
Variables (R : realType).

Section exp.
Inductive exp : Ty -> Type :=
| Real : R -> exp TReal
| Plus : exp TReal -> exp TReal -> exp TReal
| Var G T (x : string) :
  T = nth TUnit (map snd G) (seq.index x (map fst G)) -> exp T
| Letin t u : string -> exp t -> exp u -> exp u
.
End exp.

Arguments Var {G T}.
Declare Custom Entry exp.
Notation "[ e ]" := e (e custom exp at level 5) : easylang_scope.
Notation "x ':r'" := (Real x) (in custom exp at level 1) 
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

Example e1 := (Letin "x" (Real 1%R) (@Var [:: ("x", TReal)] _ "x" erefl)).
Fail Example e1 := [Let x <~ {1%:R}:r In %{"x"}] : exp TReal.
Fail Example e2' := (Letin x [{1%:R}:r] (@Letin TReal _ y [%{"x"}] [%{"y"}])) : exp TReal.
Fail Example e2 := [Let x <~ {1%:R}:r In Let y <~ %{"x"} In %{"y"}] : exp TReal.
Fail Example e3 := [Let x <~ {1%:R}:r In
               Let y <~ {2%:R}:r In 
               %{x} + %{y}] : exp _.

Fixpoint acc (g : Ctx) (i : nat) :
  ctxi R g -> @typei R (nth TUnit (map snd g) i) :=
  match g return (ctxi R g -> typei R (nth TUnit (map snd g) i)) with
  | [::] => match i with | O => id | j.+1 => id end
  | _ :: _ => match i with
               | O => fst
               | j.+1 => fun H => acc j H.2
               end
  end.

Inductive eval : forall (g : Ctx) (t : Ty), exp t -> (typei R (TList (map snd g)) -> typei R t) -> Prop :=
| EVReal g c : @eval g _ (Real c) (fun=> c)
| EVPlus g (e1 e2 : exp TReal) (v1 v2 : _ -> _) : 
    @eval g TReal e1 v1 -> 
    @eval g TReal e2 v2 -> 
    @eval g TReal (Plus e1 e2) (fun x => v1 x + v2 x)%R
(* | EVVar (g : Ctx) (x : string) i : 
    i = seq.index x (map fst g) -> eval (Var x erefl) (@acc (map snd g) i) *)
(* | EVLetin (g : Ctx) (t : Ty) (x : string) e1 e2 (v1 v2 : _ -> _) :
    @eval g TReal e1 v1 ->
    @eval ((x, TReal) :: g) TReal e2 v2 ->
    @eval g TReal (Letin x e1 e2) (v2 \o v1) *)
.

(* Goal @eval [::] _ [{1%R}:r] (fun=> 1%R).
Proof. exact/EVReal. Qed.
Goal @eval [::] _ [{1%R}:r + {2%R}:r] (fun=> 3%R).
Proof. exact/EVPlus/EVReal/EVReal. Qed.
Goal @eval [:: ("x", TReal)] _ [% {"x"}] (@varof [:: TReal] 0).
Proof. exact/EVVar. Qed.
Goal @eval [::] _ [Let x <~ {1%R}:r In %{"x"} + {2%R}:r] (fun=> 3).
Proof. Abort. *)

End lang_intrinsic_ty.
End lang_intrinsic_ty.

Module lang_intrinsic_sc.
Section lang_intrinsic_sc.
Variables (R : realType).

Section exp.
Inductive exp : Ctx -> Type :=
| Real g : R -> exp g
| Plus g : exp g -> exp g -> exp g
| Var G T (x : string) : 
  T = nth TUnit (map snd G) (seq.index x (map fst G)) -> exp G
| Letin g t (x : string) : exp g -> exp ((x, t) :: g) -> exp g
.
End exp.

Arguments Var {G T}.
Arguments Real {g}.
Arguments Letin {g t}.
Declare Custom Entry exp.
Notation "[ e ]" := e (e custom exp at level 5) : easylang_scope.
Notation "x ':r'" := (Real x) (in custom exp at level 1) 
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

Example e0 := [{1%:R}:r] : exp [::].
Example e1 := (Letin "x" (Real 1%R) (@Var [:: ("x", TReal)] _ "x" erefl)) : exp [::].
Fail Example e1 := [Let x <~ {1%:R}:r In %{"x"}] : exp [::].
Fail Example e2 := [Let x <~ {1%:R}:r In Let y <~ %{"x"} In %{"y"}] : exp [::].
Fail Example e3 := [Let x <~ {1%:R}:r In
                    Let y <~ {2%:R}:r In
                    %{x} + %{y}] : exp [::].

Fixpoint acc (g : Ctx) (i : nat) :
  ctxi R g -> @typei R (nth TUnit (map snd g) i) :=
  match g return (ctxi R g -> typei R (nth TUnit (map snd g) i)) with
  | [::] => match i with | O => id | j.+1 => id end
  | _ :: _ => match i with
               | O => fst
               | j.+1 => fun H => acc j H.2
               end
  end.


Inductive eval : forall (g : Ctx) (t : Ty), exp g -> (ctxi R g -> typei R t) -> Prop :=
| EVReal g c : @eval g TReal (Real c) (fun=> c)
| EVPlus g (e1 e2 : exp g) (v1 v2 : R) : 
    @eval g TReal e1 (fun=> v1) -> 
    @eval g TReal e2 (fun=> v2) -> 
    @eval g TReal (Plus e1 e2) (fun=> (v1 + v2)%R)
| EVVar (g : Ctx) (x : string) i : 
    i = seq.index x (map fst g) -> eval (Var x erefl) (@acc g i)
(* | EVLetin :  *)
.

Goal @eval [::] TReal [{1%R}:r] (fun=> 1%R).
Proof. exact/EVReal. Qed.
Goal @eval [::] TReal [{1%R}:r + {2%R}:r] (fun=> 3%R).
Proof. exact/EVPlus/EVReal/EVReal. Qed.
Goal @eval [:: ("x", TReal)] _ [% {"x"}] (@acc [:: ("x", TReal)] 0).
Proof. exact/EVVar. Qed.
Check [Let x <~ {1%R}:r In %{"x"} + {2%R}:r].

End lang_intrinsic_sc.
End lang_intrinsic_sc.

Module lang_intrinsic_full.
Section lang_intrinsic_full.
Variables (R : realType).

Section exp.
Inductive exp : Ctx -> Ty -> Type :=
| Real g : R -> exp g TReal
| Plus g : exp g TReal -> exp g TReal -> exp g TReal
| Var G T (x : string) : 
    T = nth TUnit (map snd G) (seq.index x (map fst G)) -> 
    exp G T
| Letin g t u (x : string) : exp g t -> exp ((x, t) :: g) u -> exp g u.
End exp.

Arguments Real {g}.
Arguments Plus {g}.
Arguments Var {G T}.
Arguments Letin {g t u}.

Declare Custom Entry exp.
Notation "[ e ]" := e (e custom exp at level 5) : easylang_scope.
Notation "x ':r'" := (Real x) (in custom exp at level 1) 
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

Example e0 := [{1%:R}:r] : exp [::] _.
Example e1 := (Letin "x" (Real 1%R) (Var "x" erefl)) : exp [::] _.
Example e1' := [Let x <~ {1%:R}:r In %{"x"}] : exp [::] TReal.
Example e2 := Letin "x" (Real 1%R) (Letin "y" (Var "x" erefl) (Var "x" erefl)) : exp [::] _.
Example e3 := Letin "x" (Real 1%R) (Letin "y" (Real 2%R) (@Plus [:: ("y", TReal); ("x", TReal)] (Var "x" erefl) (Var "y" erefl))) : exp [::] _.
Example e2' := Letin "x" [{1%:R}:r] (Letin "y" [%{"x"}] [%{"y"}]) : exp [::] _.
Example e2'' := [Let x <~ {1%:R}:r In Let y <~ %{"x"} In %{"y"}] : exp [::] _.
(* Example e3 := [Let x <~ {1%:R}:r In
               Let y <~ {2%:R}:r In
               %{x} + %{y}] : exp [::] TReal. *)

Fixpoint acc (g : Ctx) (i : nat) :
  ctxi R g -> @typei R (nth TUnit (map snd g) i) :=
  match g return (ctxi R g -> typei R (nth TUnit (map snd g) i)) with
  | [::] => match i with | O => id | j.+1 => id end
  | _ :: _ => match i with
               | O => fst
               | j.+1 => fun H => acc j H.2
               end
  end.

(* Definition coucou (g : Ctx) (t t' : Ty) (e1 : exp g t) x (e2 :exp ((x, t)::g) t') (v1 : typei R (TList (map snd g)) -> typei R t)
(v2 : typei R (TList (map snd ((x,t)::g))) -> typei R t')
: typei R (TList (map snd (g))) -> typei R t'.
move=> a.
apply v2.
split.
apply: v1.
exact: a.
Show Proof.
done.
Show Proof.
Abort. *)

Inductive eval : forall (g : Ctx) (t : Ty), exp g t -> (ctxi R g -> typei R t) -> Prop :=
| EVReal g c : @eval g _ (Real c) (fun=> c)
| EVPlus g (e1 e2 : exp g TReal) v1 v2 : 
    @eval g TReal e1 v1 -> 
    @eval g TReal e2 v2 -> 
    @eval g TReal (Plus e1 e2) (fun x => v1 x + v2 x)%R
| EVVar (g : Ctx) (x : string) : 
    let i := seq.index x (map fst g) in eval (Var x erefl) (@acc g i)
| EVLetin (g : Ctx) (t t' : Ty) (x : string) (e1 : exp g t) (e2 : exp _ t') v1 v2 :
    @eval g t e1 v1 ->
    @eval ((x, t) :: g) t' e2 v2 ->
    @eval g t' (Letin x e1 e2) (fun a => v2 (v1 a, a))
.

Goal @eval [::] _ [{1%R}:r] (fun=> 1%R).
Proof. exact/EVReal. Qed.
Goal @eval [::] _ [{1%R}:r + {2%R}:r] (fun=> 3%R).
Proof. exact/EVPlus/EVReal/EVReal. Qed.
Goal @eval [:: ("x", TReal)] _ [% {"x"}] (@acc [:: ("x", TReal)] 0).
Proof. exact/EVVar. Qed.
Goal @eval [::] _ [Let x <~ {1%R}:r In %{"x"}] (fun=> 1%R).
Proof. exact: (EVLetin (EVReal _ _) (EVVar _ _)). Qed.

End lang_intrinsic_full.
End lang_intrinsic_full.

Module lang_syntax_simple.
Section lang_syntax_simple.
Variables (R : realType).

Section exp.
Inductive exp : Ctx -> Ty -> Type :=
| Real g : R -> exp g TReal
| Var (g : Ctx) t (x : string) : 
    t = nth TUnit (map snd g) (seq.index x (map fst g)) ->
    exp g t
(* | App t u : exp g (TArrow t u) -> exp g t -> exp g u *)
| Letin g t u x : exp g t -> exp ((x, t) :: g) u -> exp g u
| Plus g : exp g TReal -> exp g TReal -> exp g TReal
.
End exp.

Arguments Real {g}.
Arguments Plus {g}.
Arguments Var {g t}.
Arguments Letin {g t u}.

Declare Custom Entry exp.
Notation "[ e ]" := e (e custom exp at level 5) : easylang_scope.
Notation "x ':r'" := (Real x%R) (in custom exp at level 1) 
  : easylang_scope.
Notation "x + y" := (Plus x y) (in custom exp at level 2) 
  : easylang_scope.
Notation "% x" := (Var x erefl) (in custom exp at level 1) 
  : easylang_scope.
Notation "'Let' x '<~' e 'In' f" := (Letin x e f)
  (in custom exp at level 3,
   x constr,
   e custom exp at level 2,
   f custom exp at level 3,
   left associativity) : easylang_scope.
Notation "{ x }" := x (in custom exp, x constr) : easylang_scope.
Notation "x" := x (in custom exp at level 0, x ident) : easylang_scope.

Local Open Scope easylang_scope.

Section example.

Example e0 := [{1%R}:r + {2%R}:r] : exp [::] _.
Example e1 := [Let x <~ {1%:R}:r In %{"x"}] : exp [::] _.
Example e2 := [Let x <~ {1%:R}:r In Let y <~ %{"x"} In %{"y"}] : exp [::] _.

Fail Example e3 := [Let x <~ {1%:R}:r In
               Let y <~ {2%:R}:r In
               %{x} + %{y}] : exp [::] TReal.

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
  @Var (untag (context_of g)) t x (ctxt_prf g).

Notation "%1 x" := (@Var' x%string _ _) (in custom exp at level 1) : easylang_scope.

Fixpoint acc (l : seq Ty) (i : nat) :
  typei R (TList l) -> @typei R (nth TUnit l i) :=
  match l return (typei R (TList l) -> typei R (nth TUnit l i)) with
  | [::] => match i with | O => id | j.+1 => id end
  | _ :: _ => match i with
               | O => fst
               | j.+1 => fun H => acc j H.2
               end
  end.

Program Inductive eval : forall (g : Ctx) (t : Ty), exp g t -> (typei R (TList (map snd g)) -> typei R t) -> Prop :=
| EVReal g c : @eval g _ (Real c) (fun=> c)
| EVPlus g (e1 e2 : exp g TReal) v1 v2 : 
    @eval g TReal e1 v1 -> 
    @eval g TReal e2 v2 -> 
    @eval g TReal (Plus e1 e2) (fun x => v1 x + v2 x)%R
| EVVar (g : Ctx) (x : string) (i := seq.index x (map fst g)) : 
    eval (Var x erefl) (@acc (map snd g) i)
(* | EVVar' (g : Ctx) (x : string) : 
    let i := seq.index x (map fst g) in eval [%1 x] (@acc (map snd g) i) *)
| EVLetin (g : Ctx) (t t' : Ty) (x : string) (e1 : exp g t) (e2 : exp _ t') v1 v2 :
    @eval g t e1 v1 ->
    @eval ((x, t) :: g) t' e2 v2 ->
    @eval g t' (Letin x e1 e2) (fun a => v2 (v1 a, a))
.

Example e2' := [Let x <~ {1%:R}:r In
               Let y <~ {2%:R}:r In 
               %{x}] : exp [::] _.
Goal eval e2' (fun=> 1%R).
Proof.
apply: (EVLetin (EVReal _ 1%R) (EVLetin (EVReal _ 2%R) (EVVar _ "x"))).
Qed.

Example e3' := Letin "x" (Real 1%:R) 
              (Letin "y" (Real 2%:R) 
              (Plus (@Var [:: ("y", TReal); ("x", TReal)] TReal x erefl) (Var "y" erefl))) : exp [::] _.

Lemma eval3' : @eval [::] TReal e3' (fun=> 3%R).
Proof.
exact: (EVLetin (EVReal [::] 1%R) (EVLetin (EVReal [:: ("x", TReal)] 2%R) (EVPlus (EVVar [:: ("y", TReal); ("x", TReal)] "x") (EVVar [:: ("y", TReal); ("x", TReal)] "y")))).
Qed.

Example e3 := [Let x <~ {1%:R}:r In
               Let y <~ {2%:R}:r In 
               %1{x} + %1{y}] : exp [::] _.

Lemma eval3 : @eval [::] TReal e3 (fun=> 3%R).
Proof.
have:= (EVLetin (EVReal [::] 1%R) (EVLetin (EVReal [:: ("x", TReal)] 2%R) (EVPlus (EVVar [:: ("y", TReal); ("x", TReal)] "x") (EVVar [:: ("y", TReal); ("x", TReal)] "y")))).
congr eval.
do 2 congr Letin.
congr Plus.
congr Var; exact: Prop_irrelevance.
congr Var; exact: Prop_irrelevance.
Qed.

End example.

End lang_syntax_simple.
End lang_syntax_simple.
