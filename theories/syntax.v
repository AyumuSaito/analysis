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
Variables (R : realType) (d : _) (G : measurableType d) (dT : _) (T : measurableType dT).
Let variable := string.
Import Notations.

Section def.
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

End def.

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
  (* if i == 0 then h else nth h t i.-1. *)

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

Fixpoint product_type (h : {d & measurableType d}) (t : seq {d & measurableType d}) : Type :=
  match t with
  | [::] => projT2 h
  | t1 :: t1s => projT2 h * product_type t1 t1s
  end.

Lemma prodA X Y Z : (X * (Y * Z))%type = ((X * Y) * Z)%type.
Proof. rewrite /=. Admitted.

Lemma __ dA dB dC dD A B C D : product_type (existT _ dA A) [:: (existT _ dB B); (existT _ dC C); (existT _ dD D)] = (A * B * C * D)%type.
Proof. by rewrite /= 2!prodA. Qed.

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

Inductive evalD : forall d (G : measurableType d) (n : nat) (l : seq (string * nat)%type) dT (T : measurableType dT) (e : exp D) (f : G -> T), measurable_fun setT f -> Prop :=
| E_unit : forall d G n l, @evalD d G n l _ munit exp_unit (cst tt) ktt

| E_bool : forall d G n l b, @evalD d G n l _ mbool (exp_bool b) (cst b) (kb b)

| E_real : forall d G n l r, @evalD d G n l _ _ (exp_real r) (cst r) (kr r)

| E_pair : forall d G n l dA dB A B e1 f1 mf1 e2 f2 mf2, 
  @evalD d G n l dA A e1 f1 mf1 ->
  @evalD d G n l dB B e2 f2 mf2 ->
  @evalD _ _ n l _ _ (exp_pair e1 e2) _ (@measurable_fun_pair _ _ _ _ _ _ f1 f2 mf1 mf2)

(* | E_ifD : forall d G n l dT T e1 f1 mf1 e2 f2 mf2 e3 f3 mf3,
  @evalD d G n l _ _ e1 f1 mf1 ->
  @evalD d G n l dT T e2 f2 mf2 ->
  @evalD d G n l dT T e3 f3 mf3 ->
  @evalD d G n l dT T (exp_if e1 e2 e3) _ (@measurable_fun_if_pair _ _ _ _ _ _ mf2 mf3 _ setT _ _) *)

| E_var2 : forall n l d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) x i, 
  assoc_get x l = Some i -> 
  @evalD _ [the measurableType _ of (T1 * T2)%type] n l _ _ (exp_var x) (proj1_sig (var_i_of2 i.+1)) (proj2_sig (var_i_of2 i.+1)) 

| E_var3 : forall n l d1 d2 d3 
(T1 : measurableType d1) (T2 : measurableType d2) (T3 : measurableType d3) x i, 
  assoc_get x l = Some i -> 
  @evalD _ [the measurableType _ of (T1 * T2 * T3)%type] n l _ _ (exp_var x) 
  (proj1_sig (var_i_of3 i.+1)) (proj2_sig (var_i_of3 i.+1)) 

| E_var4 : forall n l d1 d2 d3 d4 
(T1 : measurableType d1) (T2 : measurableType d2) (T3 : measurableType d3) 
(T4 : measurableType d4) x i, 
  assoc_get x l = Some i -> 
  @evalD _ [the measurableType _ of (T1 * T2 * T3 * T4)%type] n l _ _ (exp_var x) 
  (proj1_sig (var_i_of4 i.+1)) (proj2_sig (var_i_of4 i.+1)) 

  (* (@snd G T) (var_i_of_n (n + 2)%nat (i + 1)) *)

| E_poisson : forall d G n l k e f mf, 
  @evalD d G n l _ (mR R) e f mf -> 
  @evalD _ _ n l _ _ (exp_poisson k e) (poisson k \o f) 
    (measurable_fun_comp (mpoisson k) mf)
with evalP : forall d (G : measurableType d) 
n (l : seq (string * nat)%type) dT (T : measurableType dT),
  exp P ->
  R.-sfker G ~> T ->
  Prop :=
| E_sample : forall d G n l e p,
  @eval d G n l _ mbool e p ->
  @evalP d G n l _ _ (exp_sample e) (sample p)

| E_ifP : forall d G n l dT T e1 f1 mf e2 k2 e3 k3,
  @evalD d G n l _ _ e1 f1 mf ->
  @evalP d G n l dT T e2 k2 ->
  @evalP d G n l dT T e3 k3 ->
  @evalP d G n l dT T (exp_if e1 e2 e3) (ite mf k2 k3)

(* | E_sample_bernoulli : forall d G n l (r : R),
  @evalP d G n l _ mbool _ (exp_sample (exp_bernoulli r)) 
  (sample (bernoulli p27)) *)

| E_score : forall d (G : measurableType d) n l e (f: G -> R) 
(mf : measurable_fun _ f), 
  @evalD _ G n l _ _ e f mf -> 
  @evalP _ G n l _ munit (exp_score e) [the R.-sfker _ ~> _ of kscore mf]

| E_return : forall d G n l dT T e (f : _ -> _) (mf : measurable_fun _ f),
  @evalD d G n l dT T e f mf -> 
  @evalP d G n l dT T (exp_return e) (ret mf)

| E_letin : forall d (G : measurableType d) n l dy (Y : measurableType dy) 
dz (Z : measurableType dz) w1 w2 t1 t2 (x : string),
  @evalP _ G n l _ Y w1 t1 ->
  @evalP _ [the measurableType _ of (G * Y)%type] n.+1 ((x, n) :: l) _ Z w2 t2 ->
  @evalP _ G n l _ Z (exp_letin x w1 w2) (letin t1 t2)

| E_letin_ : forall d (G : measurableType d) n l dy (Y : measurableType dy) 
dz (Z : measurableType dz) w1 w2 t1 t2,
  @evalP _ G n l _ Y w1 t1 ->
  (* @evalP _ [the measurableType _ of (G * Y)%type] n.+1 (("_", n) :: l) _ Z _ w2 t2 -> *)
  @evalP _ _ n l _ Z w2 t2 ->
  @evalP _ G n l _ Z (exp_letin "_" w1 w2) (letin t1 t2)

with eval : forall d (G : measurableType d) (i : nat) (l : seq (string * nat)%type) dT (T : measurableType dT),
  exp D ->
  probability _ R ->
  Prop :=
| E_bernoulli : forall d G dT T n l r (r1 : (r%:num <= 1)%R),
  @eval d G n l dT T (exp_bernoulli r) (bernoulli r1)

| E_norm : forall n l e (k : R.-sfker munit ~> mbool) P,
  @evalP _ munit n l _ _ e k ->
  @eval _ munit n l _ mbool (exp_norm e) (normalize k P tt)
.

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

Compute vars (exp_letin "x" (exp_return (exp_var "z")) (exp_letin "y" (exp_return (exp_real 2)) (exp_return (exp_pair (exp_var "x") (exp_var "y"))))).

End eval.

Section exec.
Variable (dA dB : measure_display) (A : measurableType dA) (B : measurableType dB).

Fixpoint execD_type (e : exp D) : measurableType _ :=
  match e with
  | exp_real r => mR R
  | exp_bool b => mbool
  | exp_unit => munit
  | _ => munit
  end.

Fixpoint execD (e : exp D) : @measurable_fun _ _ _ (execD_type e) _ _ :=
  match e with
  | exp_var v => var1of2
  | exp_real r => kr r
  | exp_bool b => kb b
  | exp_unit => ktt
  | _ => var1of2
  end.

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

Require Import Coq.Program.Equality.
Lemma eval_uniq (e : exp P) u v : 
  @evalP _ A 0 [::] _ B e u -> 
  @evalP _ A 0 [::] _ B e v -> 
  u = v.
Proof.
(* apply/evalP_ind. *)
dependent induction e.
admit.

- inversion 1 as [h|h|h|h|h|h].

(* elim: e u v. *)
Admitted.
Lemma eval_full : forall e, exists v, @evalP _ A 0 [::] _ B e v.
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

Arguments E_var2 n {_ _ _ _ _ _} i.
Arguments E_var3 n {_ _ _ _ _ _ _ _} i.
Arguments E_var4 n {_ _ _ _ _ _ _ _ _ _} i.
(* Arguments evalP {_ _} n l {_ _ _}. *)

Section example.
Variable (d : _) (G : measurableType d).

Example ex_real : @evalD _ G 0 [::] _ _ (exp_real 3) (@cst _ R 3) (kr 3).
Proof. apply/E_real. Qed.

Example ex_bool : @evalD _ G 0 [::] _ _ (exp_bool true) (cst true) 
(@measurable_fun_cst _ _ _ mbool setT _).
Proof. apply/E_bool. Qed.

Example ex_pair : @evalD d G 0 [::] _ _ (exp_pair (exp_real 1) (exp_real 2)) _ 
(@measurable_fun_pair _ _ _ _ _ _ (@cst _ R 1%R) (@cst _ R 2) (kr 1) (kr 2)).
Proof.
apply/E_pair /E_real /E_real.
Qed.

Example ex_ifP : @evalP d G 0 [::] _ (mR R) 
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
  @evalP _ (mR R) 0 [::] _ _ 
    (exp_sample (exp_bernoulli (2 / 7%:R)%:nng)) 
    (sample (bernoulli p27)).
Proof.
apply/E_sample /E_bernoulli.
Qed.

Example sampler (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
  @evalP _ (mR R) 0 [::] _ _ 
    (exp_sample (exp_bernoulli r)) 
    (sample (bernoulli r1)).
Proof.
apply/E_sample /E_bernoulli.
Qed.

Example score1 :
  @evalP _ (mR R) 0 [::] _ _ (exp_score (exp_real 1)) (score (kr 1)).
Proof. 
apply/E_score /E_real. 
Qed.

Example score2 :
  @evalP _ (mR R) 0 [::] _ _ 
    (exp_score (exp_poisson 4 (exp_real 3))) 
    (score (measurable_fun_comp (mpoisson 4) (kr 3))).
Proof.
apply/E_score /E_poisson /E_real.
Qed.

(* to be failed *)
Example ex_var :
  @evalP _ munit 0 [::] _ _
    (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng))
      (exp_letin "r" (exp_if (exp_var "x") (exp_return (exp_real 3)) (exp_return (exp_real 10)))
        (exp_letin "y" (exp_score (exp_poisson 4 (exp_var "r")))
          (exp_return (exp_var "y"))))) 
    (kstaton_bus' _ (mpoisson 4)).
Proof.
apply/E_letin /E_letin /E_letin.
apply/E_sample /E_bernoulli.
apply/E_ifP /E_return /E_real /E_return /E_real.
(* Unset Printing Notations. *)
exact: (E_var2 _ 0%nat).
apply/E_score.
apply/E_poisson.
exact: (E_var3 _ 1%nat).
apply/E_return.
set tmp := var2of4.
have -> : tmp = proj2_sig (var_i_of4 1) by [].
have := @E_var4 3 [:: ("y", 2%nat); ("r", 1%nat); ("x", 0%nat)] _ _ _ _ munit mbool (mR R) munit "y" 2 erefl.
Admitted.

Example eval5 :
  @evalP _ munit 0 [::] _ _
    (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7%:R)%:nng))
      (exp_letin "r" (exp_if (exp_var "x") (exp_return (exp_real 3)) (exp_return (exp_real 10)))
        (exp_letin "_" (exp_score (exp_poisson 4 (exp_var "r")))
          (exp_return (exp_var "x"))))) 
    (kstaton_bus' _ (mpoisson 4)).
Proof.
apply/E_letin /E_letin /E_letin_.
apply/E_sample /E_bernoulli.
apply/E_ifP /E_return /E_real /E_return /E_real.
exact: (E_var2 _ 0).
apply/E_score.
apply/E_poisson.
exact: (E_var3 _ 1).
apply/E_return.
exact: (E_var4 _ 0).
Qed.

(* Check @normalize _ _ munit mbool R (kstaton_bus'' R) (bernoulli p27) tt : measure _ _. *)

Example eval6 P :
  @eval _ munit 0 [::] _ mbool
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
exact: (E_var2 _ 0).
apply/E_score.
apply/E_poisson.
exact: (E_var3 _ 1).
apply/E_return.
exact: (E_var4 _ 0).
Qed.

Example eval7 P :
  @eval _ munit 0 [::] _ mbool
    (exp_norm (exp_sample (exp_bernoulli (2 / 7%:R)%:nng)))
    (@normalize _ _ _ _ R (sample (bernoulli p27)) P tt).
Proof. apply/E_norm /E_sample /E_bernoulli. Qed.

(* Check (@knormalize _ _ _ _ R (sample (bernoulli p27)) (bernoulli p27)) : kernel _ _ _. *)

Example eval7_2 P :
  @eval _ munit 0 [::] _ mbool
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

Compute vars exp_staton_bus.

Lemma eq_statonbus (t u : exp P) (v1 v2 : probability _ _) U :
  eval munit 0 [::] mbool exp_staton_bus v1 ->
  eval munit 0 [::] mbool exp_staton_bus' v2 ->
  v1 U = v2 U.
Proof.
have -> : v1 = staton_bus (mpoisson 4) (bernoulli p27) tt.
admit.
have -> : v2 = staton_bus' (mpoisson 4) (bernoulli p27) tt.
admit.
move=> h1 h2.
by rewrite staton_busE staton_busE'.
Admitted.

(*
TODO: use funext 
*)

(* Example ex1 :=
  (exp_letin "x" (exp_sample (exp_bernoulli (2 / 7))) (exp_letin "y" (exp_return (exp_real 3)) ()) *)
Variable (dU : _) (U : measurableType dU).

Lemma letinC' (t u : exp P) (v1 v2 : R.-sfker _ ~> _) :
  @evalP _ G 0 [::] _ [the measurableType _ of (T * U)%type]
  (exp_letin "x" t (exp_letin "y" u 
    (exp_return (exp_pair (exp_var "x") (exp_var "y"))))) v1 ->
  @evalP _ G 0 [::] _ [the measurableType _ of (T * U)%type] 
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
rewrite letinC.
apply letinC.


Admitted.

Lemma letinC'' (t u : exp P) :
  (exp_letin "x" t (exp_letin "y" u (exp_return (exp_var "x")))) =
  (exp_letin "y" u (exp_letin "x" t (exp_return (exp_var "x")))).
Proof.
Admitted.

End example.
End v8.

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