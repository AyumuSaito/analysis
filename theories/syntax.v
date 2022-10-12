From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure fsbigop numfun lebesgue_integral kernel prob_lang.

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


Section association_list.

Fixpoint assoc_get {A : eqType} {B : Type} (a : A) (l : seq (A * B)) : option B :=
  match l with
  | nil => None
  | h :: t => if h.1 == a then Some h.2 else assoc_get a t
  end.

Lemma __ : assoc_get "b" [:: ("a", 1%nat); ("b", 2%nat)] = Some 2%nat.
Proof. rewrite //. Abort.

End association_list.

Section v8.
Variables (R : realType).
Let variable := string.
Import Notations.

Section def.
Inductive Z := D | P.

Inductive exp : Z -> Type :=
| exp_var {z} : variable -> exp z
| exp_unit : exp D
| exp_bool : bool -> exp D
| exp_real : R -> exp D
(* | val_unif : val *)
| exp_bernoulli : R -> exp D
| exp_poisson : nat -> exp D -> exp D
| exp_if : forall z, exp D -> exp z -> exp z -> exp z
| exp_letin : variable -> exp P -> exp P -> exp P
| exp_sample : exp D -> exp P
| exp_score : exp D -> exp P
| exp_return : exp D -> exp P
| exp_norm : exp P -> exp D
.

End def.

Section eval.
Notation var2of4 := (measurable_fun_comp (@measurable_fun_snd _ _ _ _)(measurable_fun_comp (@measurable_fun_fst _ _ _ _) (@measurable_fun_fst _ _ _ _))).

Inductive evalD : forall d (G : measurableType d) (i : nat) (l : seq (string * nat)%type) dT (T : measurableType dT) (z : Z) (e : exp z) (f : G -> T), measurable_fun setT f -> Prop :=
| E_unit : forall d G i l, @evalD d G i l _ munit D exp_unit (fun _ => tt) (@measurable_fun_cst _ _ _ _ setT _)

| E_bool : forall d G i l b, @evalD d G i l _ mbool _ (exp_bool b) (fun _ => b) (@measurable_fun_cst _ _ _ _ setT _)

| E_real : forall d G i l r, @evalD d G i l _ _ _ (exp_real r) (cst r) (kr r)

| E_var0 : forall i l d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) x z, @evalD _ _ i l _ _ z (@exp_var z x) (@fst T1 T2) var1of2

| E_var1 : forall i l x z n d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (f : (T1 * T2)%type -> T2) mf,
  assoc_get x l = Some n ->
  @evalD _ _ i l _ _ _ (@exp_var z x) f mf

| E_var2 : forall i l d1 d2 d3 (T1 : measurableType d1) (T2 : measurableType d2) (T3 : measurableType d3) x z, 
  @evalD _ _ i l _ _ _ (@exp_var z x) ((@snd T1 T2) \o (@fst _ T3)) var2of3

| E_var3 : forall i (l : seq (string * nat)%type) d1 d2 d3 d4 
(T1 : measurableType d1) (T2 : measurableType d2) (T3 : measurableType d3) 
(T4 : measurableType d4) x z n, 
  assoc_get x l = Some n -> 
  @evalD _ _ i l _ _ _ (@exp_var z x) 
  ((@snd T1 T2) \o ((@fst _ T3) \o (@fst _ T4))) var2of4

| E_var : forall i l x z n d dT (G : measurableType d) (T : measurableType dT) (f : G -> T) mf,
  assoc_get x l = Some n ->
  @evalD _ _ i l _ _ _ (@exp_var z x) f mf

(* | E_bernoulli : forall d G i l r, @evalD d G i l _ _ (exp_bernoulli r) (bernoulli p27) (@measurable_fun_cst _ _ _ _ setT _) *)

| E_poisson : forall d G i l n e f mf, 
  @evalD d G i l _ (mR R) _ e f mf -> 
  @evalD _ _ i l _ _ _ (exp_poisson n e) (poisson n \o f) 
    (measurable_fun_comp (mpoisson n) mf)

(* | E_norm : forall i l dT (T : measurableType dT) e (k : R.-sfker munit ~> T) (P : probability T R),
  @evalP _ munit i l _ _ _ e k ->
  @evalD _ munit i l _ T _ (exp_norm e) (normalize k P) *)
(* Example eval1 d G i l r : @evalD d G i l _ mR (exp_real r) (fun _ => r) (@measurable_fun_cst _ _ _ _ setT _).
Proof. apply E_real. Qed.

(*
TODO: function to kernel  
*)

Check (sample (bernoulli p27)) : _.-sfker _ ~> _.
Check [the R.-sfker _ ~> mbool of (sample (bernoulli p27))]. *)

with evalP : forall d (G : measurableType d) 
n (l : seq (string * nat)%type) dT (T : measurableType dT) (z: Z),
  exp z ->
  R.-sfker G ~> T ->
  Prop :=
(* | E_bernoulli : forall d G r, @eval d G _ _ _ _ (exp_bernoulli r) (mbernoulli p27) *)

(* | E_sample : forall d G n l dT T e t (p : probability _ _), 
  @eval d G n l dT T e t -> 
  @eval d G n l dT T (exp_sample e) (sample p) *)

| E_if : forall d G i l dT T z e1 f1 mf e2 k2 e3 k3,
  @evalD d G i l _ _ _ e1 f1 mf ->
  @evalP d G i l dT T _ e2 k2 ->
  @evalP d G i l dT T _ e3 k3 ->
  @evalP d G i l dT T z (exp_if e1 e2 e3) (ite mf k2 k3)

| E_sample_bernoulli : forall d G n l (r : R),
  @evalP d G n l _ mbool _ (exp_sample (exp_bernoulli r)) 
    (sample (bernoulli p27))

| E_score : forall d (G : measurableType d) i l e (f: G -> R) 
(mf : measurable_fun _ f), 
  @evalD _ G i l _ _ _ e f mf -> 
  @evalP _ G i l _ munit _ (exp_score e) [the R.-sfker _ ~> _ of kscore mf]

| E_return : forall d G i l dT T e (f : _ -> _) (mf : measurable_fun _ f),
  @evalD d G i l dT T _ e f mf -> 
  @evalP d G i l dT T _ (exp_return e) (ret mf)

| E_letin : forall d (G : measurableType d) n l dy (Y : measurableType dy) 
dz (Z : measurableType dz) w1 w2 t1 t2 (x : string),
  @evalP _ G n l _ Y _ w1 t1 ->
  @evalP _ [the measurableType _ of (G * Y)%type] n.+1 ((x, n) :: l) _ Z _ w2 t2 ->
  @evalP _ G n l _ Z _ (exp_letin x w1 w2) (letin t1 t2)
.
Inductive eval : forall d (G : measurableType d) n 
(l : seq (string * nat)%type) dT (T : measurableType dT),
  exp D ->
  measure R T ->
  Prop :=
| E_norm : forall i l dT (T : measurableType dT) e (k : R.-sfker munit ~> T) P,
  @evalP _ munit i l _ _ _ e k ->
  @eval _ munit i l _ T (exp_norm e) (normalize k P tt : measure R T)
.
End eval.

Section example.
Variable (d : _) (G : measurableType d).

Example ex_real : @evalD d G 0 [::] _ _ _ (exp_real 3) (@cst _ R 3) (kr 3).
Proof. apply/E_real. Qed.

Example ex_bool (b : bool) : @evalD d G 0 [::] _ _ _ (exp_bool b) (fun _ => b) (@measurable_fun_cst _ _ _ mbool setT _).
Proof. apply/E_bool. Qed.

Example ex_if : @evalP d G 0 [::] _ (mR R) _ 
  (exp_if (exp_bool true) (exp_return (exp_real 3)) (exp_return (exp_real 10)))
  (ite (@measurable_fun_cst _ _ _ mbool setT true) (ret k3) (ret k10)).
Proof. apply/E_if /E_return /E_real /E_return /E_real /E_bool. Qed.

Example ex_ite : 
  @ite _ _ _ (mR R) R _ (@measurable_fun_cst _ _ _ mbool setT true) (ret k3) (ret k10) tt = ret k3 tt.
Proof. by rewrite iteE. Qed.

Example sample1 :
  @evalP _ (mR R) 0 [::] _ _ _ 
    (exp_sample (exp_bernoulli (2 / 7))) 
    (sample (bernoulli p27)).
Proof.
apply/E_sample_bernoulli.
Qed.
Example score1 :
  @evalP _ (mR R) 0 [::] _ _ _ (exp_score (exp_real 1)) (score (kr 1)).
Proof. 
apply/E_score /E_real. 
Qed.
Example score2 :
  @evalP _ (mR R) 0 [::] _ _ _ 
    (exp_score (exp_poisson 4 (exp_real 3))) 
    (score (measurable_fun_comp (mpoisson 4) (kr 3))).
Proof.
apply/E_score /E_poisson /E_real.
Qed.

Example eval5 :
  @evalP _ munit 0 [::] _ _ _
    (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7)))
      (exp_letin "r" (exp_if (exp_var "x") (exp_return (exp_real 3)) (exp_return (exp_real 10)))
        (exp_letin "_" (exp_score (exp_poisson 4 (exp_var "r")))
          (exp_return (exp_var "x"))))) 
    (kstaton_bus'' R).
Proof.
apply/E_letin /E_letin /E_letin.
apply/E_sample_bernoulli.
apply/E_if /E_return /E_real /E_return /E_real.
apply/E_var => //.
apply/E_score.
apply/E_poisson.
apply/E_var => //.
apply/E_return.
apply/E_var.
rewrite //.
Qed.

Check @normalize _ _ munit mbool R (kstaton_bus'' R) (bernoulli p27) tt : measure _ _.

Example eval6 P :
  @eval _ munit 0 [::] _ _
    (exp_norm
      (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7)))
        (exp_letin "r" (exp_if (exp_var "x") (exp_return (exp_real 3)) (exp_return (exp_real 10)))
          (exp_letin "_" (exp_score (exp_poisson 4 (exp_var "r")))
            (exp_return (exp_var "x"))))))
    (@normalize _ _ munit mbool R (kstaton_bus'' R) P tt).
Proof.
apply/E_norm.
apply/E_letin /E_letin /E_letin.
apply/E_sample_bernoulli.
apply/E_if /E_return /E_real /E_return /E_real.
apply/E_var => //.
apply/E_score.
apply/E_poisson.
apply/E_var => //.
apply/E_return.
apply/E_var => //.
Qed.

End example.



End v8.



Section v7.
Variable (R : realType).
Let variable := string.

Section def.

Inductive mtype :=
| ty_unit
| ty_bool
| ty_real
.

Inductive type :=
| mty : mtype -> type
| ty_prob : mtype -> type
.

Inductive context :=
| empty
| extend : context -> variable -> mtype -> context
.

Inductive exp : Type :=
| exp_var : variable -> exp
| exp_unit : exp
| exp_bool : bool -> exp
| exp_real : R -> exp
(* | val_unif : val *)
| exp_bernoulli : R -> exp
| exp_poisson : nat -> exp -> exp
| exp_if : exp -> exp -> exp -> exp
| exp_letin : variable -> exp -> exp -> exp
| exp_sample : exp -> exp
| exp_score : exp -> exp
| exp_return : exp -> exp
.
End def.

Section eval.
Let mR := Real_sort__canonical__measure_Measurable R.
Let munit := Datatypes_unit__canonical__measure_Measurable.
Let mbool := Datatypes_bool__canonical__measure_Measurable.

Definition interp_mtype (mty : mtype) :=
  match mty with
  | ty_unit => munit
  | ty_bool => mbool
  | ty_real => mR
  end.

(* Definition interp_type (ty : type) : Type :=
  match ty with 
  | mty t => interp_mtype t
  | ty_prob t => probability (interp_mtype t) R
  end.

Fixpoint G_to_mdisp (G : context) :=
  match G with
  | empty => default_measure_display
  | extend G' x T => (G_to_mdisp G', default_measure_display).-prod%mdisp
  end.

Fixpoint interp_context (G : context) : measurableType (G_to_mdisp G) :=
  match G with
  | empty => munit : measurableType (G_to_mdisp empty)
  | extend G' x T => [the measurableType _ of (interp_context G' * interp_mtype T)%type]
  end. *)

Notation var1of2 := (@measurable_fun_fst _ _ _ _).
Notation var2of2 := (@measurable_fun_snd _ _ _ _).
Notation var1of3 := (measurable_fun_comp (@measurable_fun_fst _ _ _ _)
                                         (@measurable_fun_fst _ _ _ _)).
Notation var2of3 := (measurable_fun_comp (@measurable_fun_snd _ _ _ _)
                                         (@measurable_fun_fst _ _ _ _)).
Notation var3of3 := (@measurable_fun_snd _ _ _ _).
Notation var2of4 := (measurable_fun_comp (@measurable_fun_snd _ _ _ _)(measurable_fun_comp (@measurable_fun_fst _ _ _ _) (@measurable_fun_fst _ _ _ _))).

(* Inductive var_i_of_n 
  d (G : measurableType d) dT (T : measurableType dT) (f : G -> T) (i n : nat) : measurable_fun setT f -> Prop := 
  (* match n with *)
  |  => @measurable_fun_snd _ _ _ _
  |  => @measurable_fun_snd _ _ _ _
  |  => @measurable_fun_snd _ _ _ _
  | n.+1 => @measurable_fun_snd _ _ _ _
  . *)

Inductive evalD : forall d (G : measurableType d) (i : nat) (l : seq (string * nat)%type) dT (T : measurableType dT) (e : exp) (f : G -> T), measurable_fun setT f -> Prop :=
| E_unit : forall d G i l, @evalD d G i l _ munit exp_unit (fun _ => tt) (@measurable_fun_cst _ _ _ _ setT _)
| E_bool : forall d G i l b, @evalD d G i l _ mbool (exp_bool b) (fun _ => b) (@measurable_fun_cst _ _ _ _ setT _)
| E_real : forall d G i l r, @evalD d G i l _ mR (exp_real r) (fun _ => r) (@measurable_fun_cst _ _ _ _ setT _)

| E_var0 : forall i l d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) x, @evalD _ _ i l _ _ (exp_var x) (@fst T1 T2) var1of2

| E_var1 : forall i l d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) x, @evalD _ _ i l _ _ (exp_var x) (@snd T1 T2) var2of2

| E_var2 : forall i l d1 d2 d3 (T1 : measurableType d1) (T2 : measurableType d2) (T3 : measurableType d3) x, @evalD _ _ i l _ _ (exp_var x) ((@snd T1 T2) \o (@fst (T1 * T2)%type T3)) var2of3

| E_var3 : forall i (l : seq (string * nat)%type) d1 d2 d3 d4 (T1 : measurableType d1) (T2 : measurableType d2) (T3 : measurableType d3) (T4 : measurableType d4) x, 
  @string_dec x (nth ("_", 0%nat) l 2).1 -> 
  @evalD _ _ i l _ _ (exp_var x) ((@snd T1 T2) \o ((@fst (T1 * T2)%type T3) \o (@fst (T1 * T2 * T3)%type T4))) var2of4

(* | E_bernoulli : forall d G i l r, @evalD d G i l _ _ (exp_bernoulli r) (bernoulli p27) (@measurable_fun_cst _ _ _ _ setT _) *)

| E_poisson : forall d G i l n e f mf, @evalD d G i l _ mR e f mf -> @evalD _ _ i l _ _ (exp_poisson n e) (poisson n \o f) (measurable_fun_comp (mpoisson n) mf)


(* Example eval1 d G i l r : @evalD d G i l _ mR (exp_real r) (fun _ => r) (@measurable_fun_cst _ _ _ _ setT _).
Proof. apply E_real. Qed.

(*
TODO: function to kernel
*)

Check (sample (bernoulli p27)) : _.-sfker _ ~> _.
Check [the R.-sfker _ ~> mbool of (sample (bernoulli p27))]. *)

with eval : forall d (G : measurableType d) 
n (l : seq (string * nat)%type) dT (T : measurableType dT),
  exp ->
  R.-sfker G ~> T ->
  Prop :=
(* | E_bernoulli : forall d G r, @eval d G _ _ _ _ (exp_bernoulli r) (mbernoulli p27) *)

(* | E_sample : forall d G n l dT T e t (p : probability _ _), 
  @eval d G n l dT T e t -> 
  @eval d G n l dT T (exp_sample e) (sample p) *)
| E_real : forall d G n l r,
  @eval d G n l _ mR (exp_real r) (ret (kr r))

| E_if : forall d G i l dT T e1 f1 mf e2 k2 e3 k3,
  @evalD d G i l _ _ e1 f1 mf ->
  @eval d G i l dT T e2 k2 ->
  @eval d G i l dT T e3 k3 ->
  @eval d G i l dT T (exp_if e1 e2 e3) (ite mf k2 k3)

| E_sample_bernoulli : forall d G n l (r : R),
  @eval d G n l _ mbool (exp_sample (exp_bernoulli r)) (sample (bernoulli p27))

| E_score : forall d (G : measurableType d) i l e (f: G -> R) (mf : measurable_fun _ f), 
  @evalD _ G i l _ _ e f mf -> 
  @eval _ G i l _ munit (exp_score e) [the R.-sfker _ ~> _ of kscore mf]

| E_return : forall d G i l dT T e (f : _ -> _) (mf : measurable_fun _ f),
  @evalD d G i l dT T e f mf -> 
  @eval d G i l dT T (exp_return e) (ret mf)

| E_letin : forall d (G : measurableType d) n l dy (Y : measurableType dy) 
dz (Z : measurableType dz) w1 w2 t1 t2 (x : string),
  @eval _ G n l _ Y w1 t1 ->
  @eval _ [the measurableType _ of (G * Y)%type] n.+1 ((x, n) :: l) _ Z w2 t2 ->
  @eval _ G n l _ Z (exp_letin x w1 w2) (letin t1 t2)
.

Example eval2 d (G : measurableType d) i l r : 
  @eval _ G i l _ _ (exp_sample (exp_bernoulli r)) (sample (bernoulli p27)).
Proof.
apply E_sample_bernoulli.
Qed.

Example eval3 d (G : measurableType d) r:
  @eval _ G 0 [::] _ _ (exp_letin "x" (exp_sample (exp_bernoulli r)) (exp_return (exp_var "x"))) (letin (sample (bernoulli p27)) (ret var2of2)).
Proof.
apply /E_letin.
apply /E_sample_bernoulli.
apply /E_return.
apply /E_var1.
Qed.

Example eval4 d (G : measurableType d) :
  @eval _ G 0 [::] _ _ 
  (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7)))
    (exp_if (exp_var "x") (exp_real 3) (exp_real 10))) (sample_and_branch R G).
Proof.
apply /E_letin.
apply /E_sample_bernoulli.
apply /E_if.
apply /E_var1.
apply /E_real.
apply /E_real.
Qed.

Example eval5 :
  @eval _ munit 0 [::] _ _
    (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7)))
      (exp_letin "r" (exp_if (exp_var "x") (exp_real 3) (exp_real 10))
        (exp_letin "_" (exp_score (exp_poisson 4 (exp_var "r")))
          (exp_return (exp_var "x"))))) 
    (kstaton_bus'' R).
Proof.
apply/E_letin /E_letin /E_letin.
apply /E_sample_bernoulli.
apply /E_if /E_real /E_real.
apply /E_var1.
apply /E_score.
apply /E_poisson.
apply /E_var1.
apply /E_return.
apply /E_var3.
rewrite //.
Qed.

Example eval6 :
  @eval _ munit 0 [::] _ _
    (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7)))
      (exp_letin "r" 
        (exp_letin "_" (exp_if (exp_var "x") (exp_real 3) (exp_real 10))
          (exp_score (exp_poisson 4 (exp_var "r"))))
        (exp_return (exp_var "x"))))
    (@kstaton_bus R _ munit _ (@mpoisson R 4)).
Proof.
apply/E_letin /E_letin.
apply/E_sample_bernoulli.
apply/E_letin.
apply/E_if /E_real /E_real /E_var1.
apply/E_score /E_poisson.
apply/E_var1.
apply/E_return.
apply/E_var2.
Qed.

(* 
DONE: (sample) probability to kernel
TODO: (sample_bernoulli) genelalize p27
DONE: (score/return) measurable_fun to kernel
DONE: (score/return) relation t and f
*)

End eval.
End v7.

Section dist_salgebra_instance.
Variables (d : _) (T : measurableType d) (R : realType).
Variables p0 : probability T R.

Definition prob_pointed := Pointed.Class (Choice.Class gen_eqMixin (Choice.Class gen_eqMixin gen_choiceMixin)) p0.

Canonical probability_eqType := EqType (probability T R) prob_pointed.
Canonical probability_choiceType := ChoiceType (probability T R) prob_pointed.
Canonical probability_ptType := PointedType (probability T R) prob_pointed.

Definition mset (U : set T) (r : R) := [set mu : probability T R | mu U < r%:E].

Definition pset : set (set (probability T R)) :=
  [set mset U r | r in `[0%R, 1%R]%classic & U in @measurable d T].

Definition sset := [the measurableType pset.-sigma of salgebraType pset].

End dist_salgebra_instance.

(* Section v7.
Variable (R : realType).
Let variable := string.
Inductive type :=
| ty_unit
| ty_bool
| ty_real
| ty_prob : type -> type
.

Let mR := Real_sort__canonical__measure_Measurable R.
Let munit := Datatypes_unit__canonical__measure_Measurable.
Let mbool := Datatypes_bool__canonical__measure_Measurable.

Check sset.

Fixpoint interp_type (ty : type) : measurableType _ :=
  match ty with
  | ty_unit => munit
  | ty_bool => mbool
  | ty_real => mR
  | ty_prob ty0 => sset (probability mbool R)
  end.

Definition interp_type (ty : type) : Type :=
  match ty with 
  | mty t => interp_mtype t
  | ty_prob t => probability (interp_mtype t) R
  end.

End v7. *)

Section v6.
Variable (R : realType).
Let variable := string.

Section def.

Inductive mtype :=
| ty_unit
| ty_bool
| ty_real
.

Inductive type :=
| mty : mtype -> type
| ty_prob : mtype -> type
.

Inductive context :=
| empty
| extend : context -> variable -> mtype -> context
.

Inductive val : Type :=
| val_var : variable -> val
| val_unit : val
| val_bool : bool -> val
| val_real : R -> val
(* | val_unif : val *)
| val_bernoulli : R -> val
with expD : Type :=
| exp_val : val -> expD 
| exp_if : expD -> expD -> expD -> expD
with expP : Type :=
| exp_letin : variable -> expP -> expP -> expP
| exp_sample : expD -> expP
| exp_score : expD -> expP
| exp_return : expD -> expP
.

Coercion exp_val : val >-> expD.

Definition pgm1 := exp_letin "x" (exp_sample (exp_val (val_bernoulli 1%R))) (exp_return (exp_val (val_var "x"))).


Inductive wf_val (G : context) : val -> type -> Type :=
(* | wf_val_var {x} : wf_val G (val_var x) (G x) *)
| wf_val_unit : wf_val G val_unit (mty ty_unit)
| wf_val_bool b : wf_val G (val_bool b) (mty ty_bool)
| wf_val_real r : wf_val G (val_real r) (mty ty_real)
(* | wf_val_unif : wf_val G val_unif (ty_prob ty_real) *)
| wf_val_bernoulli r : wf_val G (val_bernoulli r) (ty_prob ty_bool)

with wf_expD (G : context) : expD -> type -> Type :=
| wf_exp_val {v T} : wf_val G v T -> wf_expD G v T
| wf_exp_if {e1 e2 e3 T} :
    wf_expD G e1 (mty ty_bool) -> wf_expD G e2 T -> wf_expD G e3 T ->
    wf_expD G (exp_if e1 e2 e3) T

with wf_expP (G : context) : expP -> mtype -> Type :=
| wf_exp_letin {x t u A B} :
    wf_expP G t A -> wf_expP (extend G x A) u B -> wf_expP G (exp_letin x t u) B
| wf_exp_sample {e T} : 
    wf_expD G e (ty_prob T) -> wf_expP G (exp_sample e) T
| wf_exp_return {e T} : 
    wf_expD G e (mty T) -> wf_expP G (exp_return e) T
.

(* Example wf5 :=
  @wf_exp_letin empty "x" _ _ _ _ 
    (wf_exp_sample (wf_exp_val (wf_val_bernoulli empty (5 / 7)%R)))
    (wf_exp_return (wf_exp_val (wf_val_real (extend empty "x" ty_bool) 1))). *)


End def.

Section interp.

Let mR := Real_sort__canonical__measure_Measurable R.
Let munit := Datatypes_unit__canonical__measure_Measurable.
Let mbool := Datatypes_bool__canonical__measure_Measurable.

Axiom prob_measurableType : forall (d : measure_display) (T : measurableType d) (R : realType), measurableType d.

Definition interp_mtype (mty : mtype) :=
  match mty with
  | ty_unit => munit
  | ty_bool => mbool
  | ty_real => mR
  end.

Definition interp_type (ty : type) : Type :=
  match ty with 
  | mty t => interp_mtype t
  | ty_prob t => probability (interp_mtype t) R
  end.

Fixpoint G_to_mdisp (G : context) :=
  match G with
  | empty => default_measure_display
  | extend G' x T => (G_to_mdisp G', default_measure_display).-prod%mdisp
  end.

Fixpoint interp_context (G : context) : measurableType (G_to_mdisp G) :=
  match G with
  | empty => munit : measurableType (G_to_mdisp empty)
  | extend G' x T => [the measurableType _ of (interp_context G' * interp_mtype T)%type]
  end.

Definition interp_wf_val {G a T} (wf : wf_val G a T) 
  : interp_context G -> interp_type T :=
  match wf with
  | wf_val_unit => fun _ => tt
  | wf_val_bool b => fun _ => b
  | wf_val_real r => fun _ => r
  | wf_val_bernoulli r => fun _ => [the probability mbool R of bernoulli p27]
  (* | _ => fun _ => tt *)
  end.

Fixpoint interp_wf_expD {G a T} (wf : wf_expD G a T) 
  : interp_context G -> interp_type T :=
  match wf with 
  | wf_exp_val _ _ w => interp_wf_val w
  | wf_exp_if _ _ _ T w1 w2 w3 => fun p => 
    if interp_wf_expD w1 p then interp_wf_expD w2 p else interp_wf_expD w3 p
  end.

Axiom tmp : forall (G : context) a T (w : wf_expD G a (mty T)),
measurable_fun [set: interp_context G] (interp_wf_expD w).

Require Import Program.
Obligation Tactic := idtac.
Inductive interp_wf_expP : forall d (G : measurableType d) n (l : seq (string * nat)%type) dT (T : measurableType dT),
    expP ->
    R.-sfker G ~> T ->
    Prop :=
| interp_let : forall d (G : measurableType d) n l dy (Y : measurableType dy) dz (Z : measurableType dz) w1 w2 t1 t2 (x : string),
  @interp_wf_expP _ G n l _ Y w1 t1 ->
  
  @interp_wf_expP _ [the measurableType _ of (G * Y)%type] n.+1 ((x, n) :: l) _ Z w2 t2 ->
  
  @interp_wf_expP _ G n l _ Z (exp_letin x w1 w2) (letin t1 t2).

| inter_var : forall G.
  (x, n) \in l ->
  @interp_wf_expP _ G n l _ Z (val_var x) (access_function x n : )





Fixpoint interp_wf_expP {G a T} (wf : wf_expP G a T)
  : R.-sfker interp_context G ~> interp_mtype T :=
  match wf with
  | wf_exp_letin _ _ _ _ _ w1 w2 => letin (interp_wf_expP w1) (interp_wf_expP w2)
  | wf_exp_sample a' T' w => sample (interp_wf_expD w point)
  (* sample _ (interp_wf_expD w tt) : R.-sfker munit ~> _ *)
  | wf_exp_return _ _ w => @ret _ _ _ _ _ (interp_wf_expD w) (@tmp _ _ _ w)
  end.

Example wf1 := 
  wf_exp_val (wf_val_bool empty true).
Example interp1 : interp_wf_expD wf1 = fun => true.
Proof. by []. Qed.
Example wf2 := 
  wf_exp_if (wf_exp_val (wf_val_bool empty false)) 
            (wf_exp_val (wf_val_real empty 10)) 
            (wf_exp_val (wf_val_real empty 3)).
Example interp2 : interp_wf_expD wf2 tt = 3%R.
Proof. by []. Qed.
Example wf3 :=
  wf_exp_val (wf_val_bernoulli empty 1%R).
Example interp3 : interp_wf_expD wf3 tt = [the probability _ _ of bernoulli27 R].
Proof. by []. Qed.
Example wf4 :=
  wf_exp_sample (wf_exp_val (wf_val_bernoulli empty 1%R)).
Example interp4 :
  interp_wf_expP wf4 = sample_bernoulli27 R _.
Proof. by []. Qed.

End interp.

End v6.


Section v5.
Variable (R : realType).

Section def.

Inductive type :=
| ty_unit
| ty_bool
| ty_real
| ty_pair : type -> type -> type
| ty_prob : type -> type
.

(* Inductive type :=
| mty : mtype -> type
| ty_prob : mtype -> type
. *)

Inductive context :=
| empty
.

Inductive val : Type :=
(* | val_var : V -> val *)
| val_unit : val
| val_bool : bool -> val
| val_real : R -> val
(* | val_unif : val *)
| val_bernoulli : R -> val
with expD : Type :=
| exp_val : val -> expD 
| exp_if : expD -> expD -> expD -> expD
with expP : Type :=
| exp_sample : expD -> expP
| exp_score : expD -> expP
.

Coercion exp_val : val >-> expD.

Inductive wf_val (G : context) : val -> type -> Type :=
(* | wf_val_var {x} : wf_val G (val_var x) (G x) *)
| wf_val_unit : wf_val G val_unit ty_unit
| wf_val_bool b : wf_val G (val_bool b) ty_bool
| wf_val_real r : wf_val G (val_real r) ty_real
(* | wf_val_unif : wf_val G val_unif (ty_prob ty_real) *)
(* | wf_val_bernoulli r : wf_val G (val_bernoulli r) (ty_prob ty_bool) *)

with wf_expD (G : context) : expD -> type -> Type :=
| wf_exp_val {v T} : wf_val G v T -> wf_expD G v T
| wf_exp_if {e1 e2 e3 T} :
    wf_expD G e1 ty_bool -> wf_expD G e2 T -> wf_expD G e3 T ->
    wf_expD G (exp_if e1 e2 e3) T

with wf_expP (G : context) : expP -> type -> Type :=
| wf_exp_sample {e T} : 
    wf_expD G e (ty_prob T) -> wf_expP G (exp_sample e) T
.

End def.

Section interp.

Let mR := Real_sort__canonical__measure_Measurable R.
Let munit := Datatypes_unit__canonical__measure_Measurable.
Let mbool := Datatypes_bool__canonical__measure_Measurable.

Axiom prob_measurableType : forall (d : measure_display) (T : measurableType d) (R : realType), measurableType d.

Fixpoint interp_type (ty : type) : {d & measurableType d} :=
  match ty with
  | ty_unit => existT _ _ munit
  | ty_bool => existT _ _ mbool
  | ty_real => existT _ _ mR
    (* [the measurableType _ of \bar R] *)
  | ty_pair t1 t2 => 
    let: existT d1 A1 := interp_type t1 in 
    let: existT d2 A2 := interp_type t2 in
    existT _ _ [the measurableType _ of (A1 * A2)%type]
  | ty_prob t =>
    let: existT d A := interp_type t in
    existT _ _ (prob_measurableType A R)
    (* [the measurableType d of probability A R] *)
  end.

Fixpoint type_to_measuredisplay (ty : type) : measure_display :=
  match ty with
  | ty_pair t1 t2 => (type_to_measuredisplay t1, type_to_measuredisplay t2).-prod
  (* | ty_prob t => let: existT d A := interp_type t in d *)
  | _ => default_measure_display
  end.

Fixpoint interp_type_2 (ty : type) : measurableType (type_to_measuredisplay ty) :=
  match ty with
  (* | ty_unit => munit *)
  | ty_bool => mbool
  | ty_real => mR
    (* [the measurableType _ of \bar R] *)
  | ty_pair t1 t2 => 
    [the measurableType _ of (interp_type_2 t1 * interp_type_2 t2)%type]
  (* | ty_prob t =>  *)
    (* prob_measurableType (interp_type_2 t) R *)
    (* [the measurableType d of probability A R] *)
  | _ => (munit : measurableType (type_to_measuredisplay ty_unit))
  end.

Definition interp_context (G : context) :=
  match G with
  | empty => unit
  end.

Definition interp_wf_val {G a T} (wf : wf_val G a T) 
  : interp_context empty -> interp_type_2 T :=
  match wf with
  | wf_val_unit => fun _ => (tt : interp_type_2 ty_unit)
  | wf_val_bool b => fun _ => b
  | wf_val_real r => fun _ => r
  (* | wf_val_bernoulli r => fun _ => [the probability mbool R of bernoulli27 R] *)
  (* | _ => fun _ => tt *)
  end.

Fixpoint interp_wf_expD {G a T} (wf : wf_expD G a T) 
  : interp_context empty -> interp_type_2 T :=
  match wf with 
  | wf_exp_val _ _ w => interp_wf_val w
  | wf_exp_if _ _ _ T w1 w2 w3 => fun p => 
    if (interp_wf_expD w1 p) then (interp_wf_expD w2 p) else (interp_wf_expD w3 p)
  end.

Fixpoint interp_wf_expP {G a T} (wf : wf_expP G a T)
  : R.-sfker _ ~> interp_type_2 T :=
  match wf with
  | wf_exp_sample _ _ w => sample (interp_wf_expD w tt)
  end.

Example wf1 := 
  wf_exp_val (wf_val_bool empty true).
Fail Example interp1 : interp_wf_expD wf1 = fun => true.
(* Proof. by []. Qed. *)
Example wf2 := 
  wf_exp_if (wf_exp_val (wf_val_bool empty true)) 
            (wf_exp_val (wf_val_real empty 0)) 
            (wf_exp_val (wf_val_real empty 1)).
Fail Example interp2 : interp_wf_expD wf2 = fun => 0 
    :> (interp_context empty -> \bar R).
(* Proof. by []. Qed. *)

End interp.

End v5.

Section dist_salgebra_instance.
Variables (d : measure_display) (T : measurableType d) (R : realType).

Definition mset (U : set T) (r : R) := [set mu : probability T R | mu U < r%:E].
Definition pset := 
  [set mset U r | r in `[0%R,1%R]%classic & U in @measurable d T].
Fail Definition sset := [the measurableType _ of salgebraType pset].

End dist_salgebra_instance.
(*
Section v4.
Variables (R : realType) (d : _) (mT : measurableType d).

Let mR := Real_sort__canonical__measure_Measurable R.
Let munit := Datatypes_unit__canonical__measure_Measurable.
Let mbool := Datatypes_bool__canonical__measure_Measurable.

Inductive type :=
| t_unit
| t_real
| t_bool
| t_P : type -> type
(* | t_arrow : type -> type -> type *)
.

Reserved Notation "[| T |]Type".

Check munit : measurableType _.
Check [the measurableType _ of \bar R] : measurableType _.

Fixpoint interp_type (T : type) : measurableType _ :=
  match T with
  | t_unit => munit
  | t_real => [the measurableType _ of \bar R]
  | t_bool => mbool 
  (* TODO: A -> B is measurable type ? *)
  (* | t_arrow A B => [the measurableType _ of [| A |]Type -> [| B |]Type] *)
  (* TODO : probability is measurable type ? *)
  (* | t_P t => [the measurableType _ of probability [the measurableType _ of [| T |]Type] R] *)
  | _ => [the measurableType _ of \bar R] 
  end
  where "[| T |]Type" := (interp_type T).

Definition variable := string.
Inductive context :=
| empty
| extend : context -> variable -> Type -> context
.

Inductive termB := True | False.

Inductive function := 
| f_const : R -> function
.

Inductive termD :=
| TT : termD
| Var : variable -> termD
| Const : R -> termD
| App : function -> termD -> termD
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
  | extend G x T => [| G |]context * T
  end
  where "[| G |]context" := (interp_context G).

Example context1 := extend empty "x" R.
Example context2 := extend context1 "y" R.

Compute [| context1 |]context.
Compute [| context2 |]context.

Fixpoint lookup (x : string) (G : context) : option _ :=
  match G with
  | empty => None
  | extend G' y T => if string_dec x y then Some T else lookup x G'
  end.

Inductive var : context -> string -> Type -> Type :=
| V1 : forall {G : context} {x : string} {t : Type}, var G x t
| VS : forall {G : context} {x} {A A'}, var G x A' -> var (extend G x A) x A'
.

Check Set : Type.
Reserved Notation "G |-d t ::: A" (at level 50).
Inductive program_d : context -> termD -> Type -> Type :=
(* | T_context : forall G x x' A A', G |-d (Var x) ::: A -> (extend G x' A') |-d (Var x) ::: A *)
| T_var     : forall G x A, lookup x G = Some A -> G |-d Var x ::: A
(* extend G x A |-d (Var x) ::: A *)
| T_app {G A B f t} : 
    G |-d f ::: (A -> B)%type -> G |-d t ::: A -> G |-d App f t ::: B 
| T_unit {G} : G |-d TT ::: [| t_unit |]Type
| T_ifd {G t u1 u2 B} : 
    G |-d t ::: [| t_bool |]Type -> G |-d u1 ::: B -> G |-d u2 ::: B -> 
    G |-d Ifd t u1 u2 ::: B
| T_bernoulli {G r} : G |-d Bernoulli r ::: probability mbool R
where "G |-d t ::: A" := (program_d G t A).

Reserved Notation "G |-p t ::: A" (at level 50). 
Inductive program_p : context -> termP -> Type -> Type :=
| T_return  : forall G t A, G |-d t ::: A -> G |-p Ret t ::: A
| T_sample  : forall G t A, G |-d t ::: probability mbool (* ? *) R -> G |-p Sample t ::: A
| T_score   : forall G t, G |-d t ::: R -> G |-p Score t ::: unit
| T_letin   : forall G x t u A B, 
    G |-p t ::: A -> (extend G x A) |-p u ::: B -> G |-p Letin x t u ::: B
| T_ifp     : forall G t u1 u2 A B, 
    G |-d t ::: A -> G |-p u1 ::: B -> G |-p u2 ::: B -> G |-p Ifp t u1 u2 ::: B
where "G |-p t ::: A" := (program_p G t A).

(* Example pgm1 := empty |-p Letin "x" (Score (Const 1)) (Ret (Var "x")) ::: t_unit.
Example _pgm1 : pgm1.
Proof. apply /T_letin.
apply /T_score. admit.
apply /T_return. admit.
Admitted. *)

Check tt : [| t_unit |]Type.

Fixpoint denote_d {G t A} (pgm : program_d G t A) 
  : [| G |]context -> A  (* TODO: measurable function *) := 
  match pgm with
  | T_unit _ => fun _ => tt
  | T_app _ _ _ _ _ f s => fun g => denote_d f g (denote_d s g)
  | T_ifd _ _ _ _ _ p1 p2 p3 => 
      fun p => if denote_d p1 p then denote_d p2 p else denote_d p3 p
  | T_var G' x t H => fun g => lookup x G
  | T_bernoulli _ r => fun _ => [the probability _ _ of bernoulli27 R] (* r *)
  end.

Example pgmd := @T_unit empty.
Compute denote_d pgmd.
Example denote_pgmd : denote_d pgmd tt = tt.
Proof. by []. Qed. 
Example pgmd2 := @T_bernoulli empty 1.
Example denote_pgmd2 : denote_d pgmd2 tt = [the probability _ _ of bernoulli27 R].
Proof. by []. Qed.  

Fixpoint denote_p {G t A} (pgm : program_p G t A)
  : R.-sfker _ ~> _ := 
  (* [the measurableType _ of [| G |]context] ~> [| A |]Type := *)
  match pgm with
  (* | T_return _ _ _ s => Return R (denote_d s _) *)
  (* | T_sample G t A p => sample (denote_d p _) *)
  | _ => sample [the probability _ _ of bernoulli27 R]
  end.

Example ex4 :
  empty |-p Letin "x" (Sample (Bernoulli (2 / 7)))
    (Ret (Var "x")) ::: R.
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
*)
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