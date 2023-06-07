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

Inductive Ty := TReal | TUnit.

Definition eqbTy (t1 t2 : Ty) :=
  match t1, t2 with
  | TReal, TReal => true
  | TUnit, TUnit => true
  | _, _ => false
  end.

Lemma eqbTy_spec (t1 t2 : Ty) : reflect (t1 = t2) (eqbTy t1 t2).
Proof.
destruct t1, t2; constructor. all: easy.
Qed.

Definition Ty_eqMixin := @EqMixin Ty eqbTy eqbTy_spec.
Canonical Ty_eqType := EqType Ty Ty_eqMixin.

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
  (* | TArrow t u => typei t -> typei u
  | TList l => prod_meas (map typei l) *)
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

Example e1' := @Letin "x" (Real 1) (@Var [:: ("x", TReal)] TReal "x" erefl).
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
| eval_real g c : @eval g TReal (Real c) (fun=> c)
| eval_plus g e1 e2 (v1 v2 : R) :
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
| Letin t u : string -> exp t -> exp u -> exp u.
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
| eval_real g c : @eval g TReal (Real c) (fun=> c)
| eval_plus g (e1 e2 : exp g) (v1 v2 : R) :
    @eval g TReal e1 (fun=> v1) ->
    @eval g TReal e2 (fun=> v2) ->
    @eval g TReal (Plus e1 e2) (fun=> (v1 + v2)%R)
| eval_var (g : Ctx) (x : string) i :
    i = seq.index x (map fst g) -> eval (Var x erefl) (@acc g i)
(* | EVLetin :  *)
.

Goal @eval [::] TReal [{1%R}:r] (fun=> 1%R).
Proof. exact/eval_real. Qed.
Goal @eval [::] TReal [{1%R}:r + {2%R}:r] (fun=> 3%R).
Proof. exact/eval_plus/eval_real/eval_real. Qed.
Goal @eval [:: ("x", TReal)] _ [% {"x"}] (@acc [:: ("x", TReal)] 0).
Proof. exact: eval_var. Qed.
Check [Let "x" <~ {1%R}:r In %{"x"} + {2%R}:r].

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
    (* (x, T) \in G ->  *)
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
Example e1' := [Let "x" <~ {1%:R}:r In %{"x"}] : exp [::] TReal.
Example e4 := Letin "x" (Real 1%R) (Letin "y" (Var "x" erefl) (Var "x" erefl)) : exp [::] _.
Example e2_ := Letin "x" (Real 1%R) (Letin "y" (Real 2%R) (@Plus [:: ("y", TReal); ("x", TReal)] (Var "x" erefl) (Var "y" erefl))) : exp [::] _.

Example e5 := Letin "x" (Real 1%R) (Letin "y" (Real 2%R) (Plus (Real 1) (Real 2))) : exp [::] _.

Example e4' := Letin "x" [{1%:R}:r] (Letin "y" [%{"x"}] [%{"y"}]) : exp [::] _.
Example e4'' := [Let "x" <~ {1%:R}:r In Let "y" <~ %{"x"} In %{"y"}] : exp [::] _.
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

Reserved Notation "G # e '-e->' v" (at level 40).

Inductive eval : forall (g : Ctx) (t : Ty), exp g t -> (ctxi R g -> typei R t) -> Prop :=
| eval_real g c : g # Real c -e-> (fun=> c)
| eval_plus g (e1 e2 : exp g TReal) v1 v2 :
    g # e1 -e-> v1 ->
    g # e2 -e-> v2 ->
    g # Plus e1 e2 -e-> (fun x => v1 x + v2 x)%R
| eval_var (g : Ctx) (x : string) :
    let i := seq.index x (map fst g) in
    g # Var x erefl -e-> @acc g i
| eval_letin (g : Ctx) (t t' : Ty) (x : string) (e1 : exp g t) (e2 : exp _ t') v1 v2 :
    g # e1 -e-> v1 ->
    ((x, t) :: g) # e2 -e-> v2 ->
    g # Letin x e1 e2 -e-> (fun a => v2 (v1 a, a))
where "G # e '-e->' v" := (@eval G _ e v).

Scheme eval_ind' := Induction for eval Sort Prop.

Lemma eval_uniq g t (e : exp g t) u v :
  g # e -e-> u ->
  g # e -e-> v ->
  u = v.
Proof.
move=> hu.
apply: (@eval_ind
  (fun g t (e : exp g t) (u : ctxi R g -> typei R t) => forall v, g # e -e-> v -> u = v)); last exact: hu.
all: (rewrite {g t e u v hu}).
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

Lemma eval_total g t (e : exp g t) : exists v, g # e -e-> v.
Proof.
elim: e.
eexists; exact: eval_real.
move=> {}g e1 [v1] IH1 e2 [v2] IH2.
eexists; exact: (eval_plus IH1 IH2).
move=> {}g {}t x e; subst t.
eexists; exact: eval_var.
move=> {}g {}t u x e1 [v1] IH1 e2 [v2] IH2.
eexists; exact: (eval_letin IH1 IH2).
Qed.

Definition exec g t (e : exp g t) : ctxi R g -> typei R t.
Proof.
have /cid h := @eval_total g t e.
exact: (proj1_sig h).
Defined.

Lemma eval_exec g t e : g # e -e-> @exec g t e.
Proof. by rewrite /exec/= /sval; case: cid. Qed.

Lemma exec_real g r : @exec g TReal (Real r) = (fun=> r).
Proof.
apply: eval_uniq.
exact: eval_exec.
apply: eval_real.
Qed.

Goal [::] # [{1%R}:r] -e-> (fun=> 1%R).
Proof. exact/eval_real. Qed.
Goal @eval [::] _ [{1%R}:r + {2%R}:r] (fun=> 3%R).
Proof. exact/eval_plus/eval_real/eval_real. Qed.
Goal @eval [:: ("x", TReal)] _ [% {"x"}] (@acc [:: ("x", TReal)] 0).
Proof. exact: eval_var. Qed.
Goal @eval [::] _ [Let "x" <~ {1%R}:r In %{"x"}] (fun=> 1%R).
Proof. exact: (eval_letin (eval_real _ _) (eval_var _ _)). Qed.

Goal exec (g := [::]) [Let "x" <~ {1%R}:r In %{"x"}] = (fun=> 1%R).
Proof.
apply: eval_uniq; first exact: eval_exec.
exact: (eval_letin (eval_real _ _) (eval_var _ _)).
Qed.

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

Example e2' := Letin "x" (Real 1%:R)
              (Letin "y" (Real 2%:R)
              (Plus (@Var [:: ("y", TReal); ("x", TReal)] TReal "x" erefl) (Var "y" erefl))) : exp [::] _.

Lemma eval3' : @eval [::] TReal e2' (fun=> 3%R).
Proof.
exact: (eval_letin (eval_real [::] 1%R)
         (eval_letin (eval_real [:: ("x", TReal)] 2%R)
           (eval_plus (eval_var [:: ("y", TReal); ("x", TReal)] "x")
                      (eval_var [:: ("y", TReal); ("x", TReal)] "y")))).
Qed.

Example e2 := [Let "x" <~ {1%:R}:r In
               Let "y" <~ {2%:R}:r In
               %1{"x"} + %1{"y"}] : exp [::] _.

Lemma eval2 : @eval [::] TReal e2 (fun=> 3%R).
Proof.
have:= eval_letin (eval_real [::] 1%R)
         (eval_letin (eval_real [:: ("x", TReal)] 2%R)
           (eval_plus (eval_var [:: ("y", TReal); ("x", TReal)] "x")
                      (eval_var [:: ("y", TReal); ("x", TReal)] "y"))).
congr eval.
do 2 congr Letin.
congr Plus.
congr Var; exact: Prop_irrelevance.
congr Var; exact: Prop_irrelevance.
Qed.

End lang_intrinsic_full.
End lang_intrinsic_full.
