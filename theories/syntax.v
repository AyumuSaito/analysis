From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure fsbigop numfun lebesgue_integral kernel.
Require Import prob_lang type_checking.

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
Variables (R : realType) (d : _) (G : measurableType d) (dT : _) (T : measurableType dT).
Let variable := string.
Import Notations.

Check fun r => @existT (R -> R) _ (cst r) (kr r).

Definition execD' r := @existT (R -> R) _ (cst r) (kr r).
Check execD'.

Section def.
Section expression.
Inductive Z := D | P.

Inductive exp : Z -> Type :=
| exp_var  : variable -> exp D
| exp_unit : exp D
| exp_bool : bool -> exp D
| exp_real : R -> exp D
| exp_pair : exp D -> exp D -> exp D
(* | val_unif : val *)
| exp_bernoulli : {nonneg R} -> exp D
| exp_poisson : nat -> exp D -> exp D
(* | exp_if : forall z, exp D -> exp z -> exp z -> exp z *)
| exp_if : exp D -> exp P -> exp P -> exp P
| exp_letin : variable -> exp P -> exp P -> exp P
| exp_sample : exp D -> exp P
| exp_score : exp D -> exp P
| exp_return : exp D -> exp P
| exp_norm : exp P -> exp D
.

End expression.
End def.


(* Inductive type :=
| ty_unit
| ty_bool
| ty_real
.

Definition interp_mtype (ty : type) :=
  match ty with
  | ty_unit => munit
  | ty_bool => mbool
  | ty_real => mR R
  end.

Definition typ_of_exp (l : seq (string * type)%type) (e : exp D) :=
  match e with
  (* | exp_var v => if assoc_get v l is Some t then interp_mtype t else munit *)
  | exp_real r => mR R
  | exp_bool b => mbool
  | exp_unit => munit
  (* | exp_bernoulli r => mR R *)
  end. *)

(* Set Printing All.
Definition execD (l : seq (string * type)%type) (e : exp D) : forall d (A : measurableType d), {f : A -> (typ_of_exp l e) | measurable_fun setT f} :=
  match e in exp D
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

Definition var_i_of2 {dA dB} {A : measurableType dA} {B : measurableType dB} (i : nat) : {f : [the measurableType _ of (A * B)%type] -> projT2 (typ2 A B i) | measurable_fun setT f} := 
  match i with
  | 0 => exist (fun x => measurable_fun setT x) (_ : A * B -> A) var1of2
  | _ => exist (fun x => measurable_fun setT x) (snd : A * B -> B) var2of2
  end.

Definition typ3 {d1 d2 d3} (T1 : measurableType d1) (T2 : measurableType d2) (T3 : measurableType d3) (i : nat) : {d & measurableType d} := 
  match i with 
  | 0 => existT _ d1 T1 
  | 1 => existT _ d2 T2
  | _ => existT _ d3 T3
  end.

Definition var_i_of3 {dA dB dC} {A : measurableType dA} {B : measurableType dB} 
{C : measurableType dC} (i : nat) : 
{f : [the measurableType _ of (A * B * C)%type] -> projT2 (typ3 A B C i) 
| measurable_fun setT f} := 
  match i with
  | 0 => exist (fun x => measurable_fun setT x) (_ : A * B * C -> A) var1of3
  | 1 => exist (fun x => measurable_fun setT x) (_ : A * B * C -> B) var2of3
  | _ => exist (fun x => measurable_fun setT x) (_ : A * B * C -> C) var3of3
  end.

Definition typ4 {d1 d2 d3 d4} (T1 : measurableType d1) (T2 : measurableType d2) 
(T3 : measurableType d3) (T4 : measurableType d4) i : {d & measurableType d} := 
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

Definition var_i_of4 {dA dB dC dD} {A : measurableType dA} 
{B : measurableType dB} {C : measurableType dC} {D : measurableType dD} (i : nat) :
{f : [the measurableType _ of (A * B * C * D)%type] -> 
projT2 (typ4 A B C D i) | measurable_fun setT f} := 
  match i with
  | 0 => exist (fun x => measurable_fun setT x) (_ : A * B * C * D -> A) var1of4
  | 1 => exist (fun x => measurable_fun setT x) (_ : A * B * C * D -> B) var2of4
  | 2 => exist (fun x => measurable_fun setT x) (_ : A * B * C * D -> C) var3of4
  | _ => exist (fun x => measurable_fun setT x) (_ : A * B * C * D -> D) var4of4
  end.

From Equations Require Import Equations.
Obligation Tactic := idtac.

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


Check exp_unit.

(* Lemma nth_ : seq.index ("x", R) [:: ("x", R); ("y", nat)] = 1%N.
Proof. rewrite /=. *)

Fixpoint only_left A B (l : seq (A * B)%type) :=
  match l with
  | [::] => [::]
  | h :: t => h.1 :: only_left t
  end.

Inductive evalD : forall d (G : measurableType d) (l : context) dT (T : measurableType dT) (e : exp D) (f : G -> T), measurable_fun setT f -> Prop :=
| E_unit : forall d G l, @evalD d G l _ munit exp_unit (cst tt) ktt

| E_bool : forall d G l b, @evalD d G l _ mbool (exp_bool b) (cst b) (kb b)

| E_real : forall d G l r, @evalD d G l _ _ (exp_real r) (cst r) (kr r)

| E_pair : forall d G l dA dB A B e1 f1 mf1 e2 f2 mf2, 
  @evalD d G l dA A e1 f1 mf1 ->
  @evalD d G l dB B e2 f2 mf2 ->
  @evalD _ _ l _ _ (exp_pair e1 e2) _ (@measurable_fun_pair _ _ _ _ _ _ f1 f2 mf1 mf2)

| E_var2 : forall l d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) x, 
  (* assoc_get x l = Some (bool : Type) -> *)
  (* seq.index x (only_left l) = i ->  *)
  let i := seq.index x (only_left l) in
  @evalD _ [the measurableType _ of (T1 * T2)%type] l _ _ (exp_var x) (proj1_sig (var_i_of2 i.+1)) (proj2_sig (var_i_of2 i.+1)) 

| E_var3 : forall l d1 d2 d3 
(T1 : measurableType d1) (T2 : measurableType d2) (T3 : measurableType d3) x i, 
  (* assoc_get x l = Some i ->  *)
  seq.index x (only_left l) = i ->
  (* let i := seq.index x (only_left l) in   *)
  @evalD _ [the measurableType _ of (T1 * T2 * T3)%type] l _ _ (exp_var x) 
  (proj1_sig (var_i_of3 i.+1)) (proj2_sig (var_i_of3 i.+1)) 

| E_var4 : forall l d1 d2 d3 d4 
(T1 : measurableType d1) (T2 : measurableType d2) (T3 : measurableType d3) 
(T4 : measurableType d4) x i, 
  (* assoc_get x l = Some i ->  *)
  seq.index x (only_left l) = i ->
  (* let i := seq.index x (only_left l) in *)
  @evalD _ [the measurableType _ of (T1 * T2 * T3 * T4)%type] l _ _ (exp_var x) 
  (proj1_sig (var_i_of4 i.+1)) (proj2_sig (var_i_of4 i.+1)) 

  (* (@snd G T) (var_i_of_n (n + 2)%nat (i + 1)) *)

| E_poisson : forall d G l k e f mf, 
  @evalD d G l _ (mR R) e f mf -> 
  @evalD _ _ l _ _ (exp_poisson k e) (poisson k \o f) 
    (measurable_fun_comp (mpoisson k) mf)

with evalP : forall d (G : measurableType d) (l : context) dT (T : measurableType dT),
  exp P ->
  R.-sfker G ~> T ->
  Prop :=
| E_sample : forall d G l e p,
  @eval d G l _ mbool e p ->
  @evalP d G l _ _ (exp_sample e) (sample p)

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
  @evalP _ G l _ Z (exp_letin "_" w1 w2) (letin t1 t2)

with eval : forall d (G : measurableType d) (l : context) dT (T : measurableType dT),
  exp D ->
  probability _ R ->
  Prop :=
| E_bernoulli : forall d G dT T l r (r1 : (r%:num <= 1)%R),
  @eval d G l dT T (exp_bernoulli r) (bernoulli r1)

| E_norm : forall l dT (T : measurableType dT) e (k : R.-sfker munit ~> mbool) P,
  @evalP _ munit l _ _ e k ->
  @eval _ munit l _ T (exp_norm e) (normalize k P tt)
.

(* Arguments exp {R}. *)
Fixpoint vars z (e : exp z) : set variable := 
  match e with
  | exp_letin x e1 e2 => vars e1
  | exp_var x => [set x]
  (* | exp_return e => vars e
  | exp_norm e => vars e *)
  | _ => set0
  end.

(* Compute vars (exp_letin "x" (exp_var "x") (exp_var "x")). *)

(* Compute vars (exp_letin "x" (exp_var "y") (exp_letin "z" (exp_var "x") (exp_var "z"))). *)

Compute vars (exp_letin "x" (exp_return (exp_var "z")) (exp_letin "y" (exp_return (exp_real 2)) (exp_return (exp_pair (exp_var "x") (exp_var  "y"))))).

End eval.

(* Arguments E_var2 {_ _ _ _ _ _} i. *)
Arguments E_var3 {_ _ _ _ _ _ _ _} i.
Arguments E_var4 {_ _ _ _ _ _ _ _ _ _} i.

Section exec.
Variable (dA dB : measure_display) (A : measurableType dA) (B : measurableType dB).

(*
Fixpoint execD_type (e : exp D) : measurableType _ :=
  match e with
  | exp_real r => mR R
  | exp_bool b => mbool
  | exp_unit => munit
  | _ => munit
  end.

Fixpoint execD (e : exp D) : forall f, measurable_fun _ f :=
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

Fixpoint execP_type (e : exp P) : Type :=
  match e with
  | exp_if e1 e2 e3 => execP_type e2
  | exp_sample _ => R.-sfker A ~> mbool
  | exp_return e1 => R.-sfker A ~> mR R
  | _ => R.-sfker A ~> B
  end.

Fixpoint execP (e : exp P) : execP_type e :=
  match e with
  | exp_if e1 e2 e3 => ite _ (execP e2) (execP e3)
  | exp_sample e => sample (bernoulli p27)
  | exp_return e => ret (kr 1)
  end.
*)

Require Import Coq.Program.Equality.
Lemma eval_uniq (e : exp  P) u v : 
  @evalP _ A [::] _ B e u -> 
  @evalP _ A [::] _ B e v -> 
  u = v.
Proof.
(* apply/evalP_ind. *)
dependent induction e.
admit.
- inversion 1 as [h|h|h|h|h|h].
(* elim: e u v. *)
Admitted.

Lemma eval_full : forall e, exists v, @evalP _ A [::] _ B e v.
Proof.
Admitted.

Definition exec : exp P -> R.-sfker A ~> B.
move=> e.
have := eval_full e.
move/cid.
move=> h.
exact: (proj1_sig h).
Defined.

End exec.

Section example.

Example ex_real : @evalD _ G [::] _ _ (exp_real 3) (@cst _ R 3) (kr 3).
Proof. apply/E_real. Qed.

Example ex_bool : @evalD _ G [::] _ _ (exp_bool true) (cst true) 
(@measurable_fun_cst _ _ _ mbool setT _).
Proof. apply/E_bool. Qed.

Example ex_pair : @evalD d G [::] _ _ (exp_pair (exp_real 1) (exp_real 2)) _ 
(@measurable_fun_pair _ _ _ _ _ _ (@cst _ R 1%R) (@cst _ R 2) (kr 1) (kr 2)).
Proof.
apply/E_pair /E_real /E_real.
Qed.

Example ex_ifP : @evalP d G [::] _ (mR R) 
  (exp_if (exp_bool true) (exp_return (exp_real 3)) (exp_return (exp_real 10)))
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
  @evalP _ (mR R) [::] _ _ 
    (exp_sample (exp_bernoulli (2 / 7%:R)%:nng)) 
    (sample (bernoulli p27)).
Proof.
apply/E_sample /E_bernoulli.
Qed.

Example sampler (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
  @evalP _ (mR R) [::] _ _ 
    (exp_sample (exp_bernoulli r)) 
    (sample (bernoulli r1)).
Proof.
apply/E_sample /E_bernoulli.
Qed.

Example score1 :
  @evalP _ (mR R) [::] _ _ (exp_score (exp_real 1)) (score (kr 1)).
Proof. apply/E_score /E_real. Qed.

Example score2 :
  @evalP _ (mR R) [::] _ _ 
    (exp_score (exp_poisson 4 (exp_real 3))) 
    (score (measurable_fun_comp (mpoisson 4) (kr 3))).
Proof. apply/E_score /E_poisson /E_real. Qed.

(* to be failed *)
Example ex_var :
  @evalP _ munit [::] _ _
    (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng))
      (exp_letin "r" (exp_if (exp_var "x") (exp_return (exp_real 3)) (exp_return (exp_real 10)))
        (exp_letin "y" (exp_score (exp_poisson 4 (exp_var "r")))
          (exp_return (exp_var "y"))))) 
    (kstaton_bus' _ (mpoisson 4)).
Proof.
apply/E_letin /E_letin /E_letin => /=.
apply/E_sample /E_bernoulli.
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
  @evalP _ munit [::] _ _
    (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng))
      (exp_letin "r" (exp_if (exp_var "x") (exp_return (exp_real 3)) (exp_return (exp_real 10)))
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
  @eval _ munit [::] _ mbool
    (exp_norm
      (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng))
        (exp_letin "r"  
          (exp_if (exp_var "x") (exp_return (exp_real 3)) 
                                (exp_return (exp_real 10)))
          (exp_letin "_" (exp_score (exp_poisson 4 (exp_var "r")))
            (exp_return (exp_var "x"))))))
    (staton_bus' (mpoisson 4) P tt).
    (* (@normalize _ _ munit mbool R (kstaton_bus' _ (mpoisson 4)) P tt). *)
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
  @eval _ munit [::] _ mbool
    (exp_norm (exp_sample (exp_bernoulli (2 / 7%:R)%:nng)))
    (@normalize _ _ _ _ R (sample (bernoulli p27)) P tt).
Proof. apply/E_norm /E_sample /E_bernoulli. Qed.

Example eval7_2 P :
  @eval _ munit [::] _ mbool
    (exp_norm (exp_sample (exp_norm (exp_sample (exp_bernoulli (2 / 7%:R)%:nng)))))
    (@normalize _ _ _ _ R 
      (sample (@normalize _ _ _ _ R (sample (bernoulli p27)) P tt)) P tt).
Proof.
apply/E_norm /E_sample.
apply/E_norm /E_sample /E_bernoulli.
Qed.

Example exp_staton_bus' := 
  (exp_norm
    (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng))
      (exp_letin "r"
        (exp_letin "_"
          (exp_if (exp_var "x") (exp_return (exp_real 3)) 
                                (exp_return (exp_real 10)))
          (exp_score (exp_poisson 4 (exp_var "r"))))
        (exp_return (exp_var "x"))))).

Example exp_staton_bus := 
  (exp_norm
    (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng))
      (exp_letin "r"  
        (exp_if (exp_var "x") (exp_return (exp_real 3)) 
                              (exp_return (exp_real 10)))
        (exp_letin "_" (exp_score (exp_poisson 4 (exp_var "r")))
          (exp_return (exp_var "x")))))).

Lemma eq_statonbus (t u : exp P) (v1 v2 : probability _ _) U :
  eval munit [::] mbool exp_staton_bus v1 ->
  eval munit [::] mbool exp_staton_bus' v2 ->
  v1 U = v2 U.
Proof.
have -> : v1 = staton_bus (mpoisson 4) (bernoulli p27) tt.
admit.
have -> : v2 = staton_bus' (mpoisson 4) (bernoulli p27) tt.
admit.
move=> h1 h2.
by rewrite staton_busE staton_busE'.
Admitted.

End example.

Section letinC.
Variable (dU : _) (U : measurableType dU).

Lemma letinC' (t u : exp P) (v1 v2 : R.-sfker _ ~> _) :
  @evalP _ G [::] _ [the measurableType _ of (T * U)%type]
  (exp_letin "x" t (exp_letin "y" u 
    (exp_return (exp_pair (exp_var "x") (exp_var "y"))))) v1 ->
  @evalP _ G [::] _ [the measurableType _ of (T * U)%type] 
  (exp_letin "y" u (exp_letin "x" t 
    (exp_return (exp_pair (exp_var "x") (exp_var "y"))))) v2 ->
  v1 = v2.
Proof.
pose vt : R.-sfker G ~> T := exec G T t.
pose vu : R.-sfker [the measurableType _ of (G * T)%type] ~> U := exec _ _ u.
move=> evalv1 evalv2.
(* pose vu := exec [the measurableType _ of (G * T)%type] _ u. *)
have hv1 : v1 = (letin vt (letin vu (ret (measurable_fun_pair var2of3 var3of3)))).
  apply: (eval_uniq evalv1).
  admit.
pose vt' : R.-sfker [the measurableType _ of (G * U)%type] ~> T := exec _ _ t.
pose vu' : R.-sfker G ~> U := exec _ _ u.
have hv2 : v2 = (letin vu' (letin vt' (ret (measurable_fun_pair var3of3 var2of3)))).
  apply: (eval_uniq evalv2).
  admit.
rewrite hv1 hv2.
apply/eq_sfkernel=> x A.
apply: letinC.
Admitted.

Lemma letinC'' (t u : exp P) :
  (exp_letin "x" t (exp_letin "y" u (exp_return (exp_var "x")))) =
  (exp_letin "y" u (exp_letin "x" t (exp_return (exp_var "x")))).
Proof.
Admitted.

End letinC.
End v8.