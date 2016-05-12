(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From SsrReals Require Import xfinmap boolp reals discrete.
From SsrReals Require Import realseq realsum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Local Notation simpm := Monoid.simpm.

(* -------------------------------------------------------------------- *)
Require Import xfinmap.

(* -------------------------------------------------------------------- *)
Reserved Notation "\dlet_ ( i <- d ) E"
  (at level 36, E at level 36, i, d at level 50,
     format "'[' \dlet_ ( i  <-  d ) '/  '  E ']'").

Reserved Notation "\dlim_ ( n ) E"
  (at level 36, E at level 36, n at level 50,
     format "'[' \dlim_ ( n ) '/  '  E ']'").

Reserved Notation "\P_[ mu ] E" (at level 2, format "\P_[ mu ]  E").
Reserved Notation "\P_[ mu , A ] E" (at level 2, format "\P_[ mu ,  A ]  E").
Reserved Notation "\E?_[ mu ] f" (at level 2, format "\E?_[ mu ]  f").
Reserved Notation "\E_[ mu ] f" (at level 2, format "\E_[ mu ]  f").
Reserved Notation "\E_[ mu , A ] f" (at level 2, format "\E_[ mu ,  A ]  f").

(* -------------------------------------------------------------------- *)
Section Distribution.
Variables (R : realType) (T : choiceType).

Structure distr := Distr {
  mu :> T -> R;
  _  :  forall x, 0 <= mu x;
  _  :  summable mu;
  _  :  psum mu <= 1
}.

Definition distr_of of phant R & phant T := distr.
End Distribution.

Notation "{ 'distr' T / R }" := (distr_of (Phant R) (Phant T))
  (at level 0, T at level 2, format "{ 'distr'  T  /  R }")
  : type_scope.

(* -------------------------------------------------------------------- *)
Section DistrCoreTh.
Context {R : realType} (T : choiceType) (mu : {distr T / R}).

Lemma ge0_mu : forall x, 0 <= mu x.
Proof. by case: mu. Qed.

Lemma le1_mu : psum mu <= 1.
Proof. by case: mu. Qed.

Lemma summable_mu : summable mu.
Proof. by case: mu. Qed.
End DistrCoreTh.

Hint Resolve ge0_mu le1_mu summable_mu.

(* -------------------------------------------------------------------- *)
Section Clamp.
Context {R : realType}.

Definition clamp (x : R) :=
  Num.max (Num.min x 1) 0.

Lemma ge0_clamp x : 0 <= clamp x.
Proof. by rewrite ler_maxr lerr orbT. Qed.

Lemma le1_clamp x : clamp x <= 1.
Proof. by rewrite ler_maxl ler_minl lerr ler01 orbT. Qed.

Definition cp01_clamp := (ge0_clamp, le1_clamp).

Lemma clamp_in01 x : 0 <= x <= 1 -> clamp x = x.
Proof.
case/andP=> ge0_x le1_x; rewrite /clamp maxr_l.
  by rewrite ler_minr ge0_x ler01. by rewrite minr_l.
Qed.

Lemma clamp_id x : clamp (clamp x) = clamp x.
Proof. by rewrite clamp_in01 // !cp01_clamp. Qed.

Lemma clamp0 : clamp 0 = 0.
Proof. by rewrite clamp_in01 // lerr ler01. Qed.

Lemma clamp1 : clamp 1 = 1.
Proof. by rewrite clamp_in01 // lerr ler01. Qed.
End Clamp.

(* -------------------------------------------------------------------- *)
Section StdDefs.
Context {R : realType} (T : choiceType).

Implicit Types (mu : {distr T / R}) (A B E : pred T) (f : T -> R).

Definition dinsupp mu := fun x => mu x != 0 :> R.

Lemma dinsuppP mu x : reflect (mu x <> 0) (x \in dinsupp mu).
Proof. by apply: (iffP idP) => /eqP. Qed.

Lemma dinsuppPn mu x : reflect (mu x = 0) (x \notin dinsupp mu).
Proof. by rewrite -topredE /dinsupp /= negbK; apply/eqP. Qed.

Definition pr   mu E   := psum (fun x => (E x)%:R * mu x).
Definition prc  mu E A := pr mu [predI E & A] / pr mu A.
Definition esp  mu f   := sum (fun x => f x * mu x).
Definition espc mu f A := sum (fun x => f x * prc mu (pred1 x) A).

Definition has_esp mu f := summable (fun x => f x * mu x).
End StdDefs.

Notation "\P_[ mu ] E"     := (pr mu E).
Notation "\P_[ mu , A ] E" := (prc mu E A).
Notation "\E_[ mu ] f"     := (esp mu f).
Notation "\E_[ mu , A ] f" := (espc mu f A).
Notation "\E?_[ mu ] f"    := (has_esp mu f).

(* -------------------------------------------------------------------- *)
Section DistrTheory.
Context {R : realType} {T : choiceType} (mu : T -> R).

Definition isdistr :=
  (forall x, 0 <= mu x) /\ (forall J, uniq J -> \sum_(j <- J) mu j <= 1).

Hypothesis isd : isdistr.

Local Lemma isd1 : forall x, 0 <= mu x.
Proof. by case: isd. Qed.

Local Lemma isd2 : summable mu.
Proof.
case: isd=> _ h; apply/summable_seqP; exists 1=> //.
move=> s /h /(ler_trans _); apply; rewrite ler_eqVlt; apply/orP.
by left; apply/eqP/eq_bigr=> i _; rewrite ger0_norm ?isd1.
Qed.

Local Lemma isd3 : psum mu <= 1.
Proof.
rewrite psumE; [apply/isd1 | apply/isd2 | apply/sup_le_ub].
  by exists 0; apply/imsetbP; exists fset0; rewrite big_fset0.
apply/ubP=> y /imsetbP[x ->]; rewrite big_fset_seq /=.
by case: isd => _; apply; case: x => x /= /canonical_uniq.
Qed.

Definition mkdistr := @Distr R T mu isd1 isd2 isd3.

Lemma mkdistrE : mkdistr =1 mu.
Proof. by []. Qed.

Definition ispredistr {T : choiceType} (mu : T -> R) :=
  [/\ forall x, 0 <= mu x & summable mu].
End DistrTheory.

Lemma isdistr_finP {R : realType} {I : finType} (mu : I -> R) :
  (isdistr mu) <-> (forall x, 0 <= mu x) /\ (\sum_j mu j <= 1).
Proof. split=> -[ge0_mu le1]; split=> //.
+ by apply/le1; rewrite /index_enum -enumT enum_uniq.
+ move=> J uqJ; rewrite big_uniq 1?(ler_trans _ le1) //=.
  by rewrite [X in _<=X](bigID (mem J)) /= ler_addl sumr_ge0.
Qed.

Lemma le1_mu1
  {R : realType} {T : choiceType} (mu : {distr T / R}) x : mu x <= 1.
Proof.
apply/(@ler_trans _ (psum mu)) => //; rewrite -[mu x]ger0_norm //.
by apply/ger1_psum.
Qed.

(* -------------------------------------------------------------------- *)
Section DistrD.
Context {R : realType} {T : choiceType} (mu : T -> R).

Definition mnull := fun x : T => (0 : R).

Lemma isd_mnull : isdistr mnull.
Proof. by split=> // J _; rewrite big1 ?ler01. Qed.

Definition dnull := locked (mkdistr isd_mnull).

Lemma dnullE x : dnull x = 0.
Proof. by unlock dnull. Qed.

Definition mkdistrd : {distr T / R} :=
  if @idP `[< isdistr mu >] is ReflectT Px then
    mkdistr (asboolE Px)
  else dnull.
End DistrD.

(* -------------------------------------------------------------------- *)
Lemma lef_dnull {R : realType} {T : choiceType} (mu : {distr T / R}) :
  dnull <=1 mu.
Proof. by move=> x; rewrite dnullE ge0_mu. Qed.

(* -------------------------------------------------------------------- *)
Section DRat.
Context {R : realType} (T : choiceType).

Local Notation distr := {distr T / R}.

Implicit Types (s : seq T).

Definition mrat (s : seq T) : T -> R :=
  fun x : T => (count (pred1 x) s)%:R / (size s)%:R.

Lemma ge0_mrat s : forall x, 0 <= mrat s x.
Proof. by move=> x; rewrite mulr_ge0 ?invr_ge0 // ler0n. Qed.

Lemma summable_mrat s: summable (mrat s).
Proof.
apply/summable_seqP; exists 1=> // J uqJ; rewrite (eq_bigr (mrat s)).
  by move=> j _; rewrite ger0_norm ?ge0_mrat.
rewrite -mulr_suml /= -natr_sum; case: (size s =P 0%N).
  by move=> ->; rewrite invr0 mulr0 ler01.
move=> /eqP nz_s; rewrite ler_pdivr_mulr ?ltr0n ?lt0n // mul1r.
rewrite ler_nat (bigID (mem s)) /= [X in (_+X)%N]big1 ?addn0.
   by move=> i /count_memPn.
Admitted.

Lemma isd_mrat s : isdistr (mrat s).
Proof. Admitted.

Definition drat s := locked (mkdistr (isd_mrat s)).

Lemma drat1E s x :
  drat s x = (count_mem x s)%:R / (size s)%:R.
Proof. by unlock drat; rewrite mkdistrE. Qed.

Definition dunit x := locked (drat [:: x]).
Definition duni  s := locked (drat (undup s)).

Lemma dunit1E x y : (dunit x) y = (x == y)%:R.
Proof. by unlock dunit; rewrite drat1E /= !(simpm, invr1). Qed.

Lemma duni1E s x : (duni s) x = (x \in s)%:R / (size (undup s))%:R.
Proof.
by unlock duni; rewrite drat1E count_uniq_mem ?(mem_undup, undup_uniq).
Qed.
End DRat.

(* -------------------------------------------------------------------- *)
Section Flip.
Context {R : realType}.

Definition mflip (xt : R) :=
  fun b => if b then clamp xt else 1 - clamp xt.

Lemma isd_mflip xt : isdistr (mflip xt).
Proof. apply/isdistr_finP; split=> [b|].
+ by case: b; rewrite ?subr_ge0 cp01_clamp.
+ by rewrite /index_enum !unlock /= addr0 addrCA subrr addr0.
Qed.

Definition dflip (xt : R) := locked (mkdistr (isd_mflip xt)).

Lemma dflip1E xt : dflip xt =1 mflip xt.
Proof. by unlock dflip; apply/mkdistrE. Qed.
End Flip.

(* -------------------------------------------------------------------- *)
Section Std.
Context {R : realType}.

Local Notation distr T := {distr T / R}.

Implicit Types (T U : choiceType).

(* -------------------------------------------------------------------- *)
Section Bind.
Variables (T U : choiceType) (f : T -> distr U) (mu : distr T).

Definition mlet := fun y : U =>
  psum (fun x => mu x * f x y).

Lemma isd_mlet : isdistr mlet.
Proof.
split=> [x|J uqJ]; first by apply/ge0_psum.
Admitted.

Definition dlet := locked (mkdistr isd_mlet).
End Bind.

Notation "\dlet_ ( i <- d ) E" := (dlet (fun i => E) d).

(* -------------------------------------------------------------------- *)
Section BindTheory.
Variables (T U : choiceType).

Implicit Types (f g : T -> distr U) (mu nu : distr T).

Lemma dlet_null f : dlet f dnull =1 dnull.
Proof.
move=> x; unlock dlet; rewrite dnullE /= /mlet psum_eq0 //.
by move=> y; rewrite dnullE mul0r.
Qed.

Lemma dlet_unit f v : \dlet_(y <- dunit v) f y = f v.
Proof using Type. Admitted.

Lemma eq_in_dlet f g mu nu : {in dinsupp mu, f =2 g} -> mu =1 nu ->
  dlet f mu =1 dlet g nu.
Proof.
move=> eq_f eq_mu; unlock dlet=> y /=; apply/eq_psum=> x.
rewrite -eq_mu; case/boolP: (x \in dinsupp mu) => [/eq_f ->//|].
by move/dinsuppPn=> ->; rewrite !mul0r.
Qed.

Local Lemma summable_mlet f mu y :
  summable (fun x : T => mu x * (f x) y).
Proof.
case/summable_seqP: (summable_mu mu)=> M ge0_M h.
apply/summable_seqP; exists M => // J uqJ.
apply/(@ler_trans _ (\sum_(j <- J) `|mu j|))/h => //.
apply/ler_sum=> j _; rewrite normrM ger0_norm //.
by apply/ler_pimulr=> //; rewrite ger0_norm ?le1_mu1.
Qed.

Lemma le_in_dlet f g mu : {in dinsupp mu, f <=2 g} ->
  dlet f mu <=1 dlet g mu.
Proof.                          (* summable -> refactor *)
move=> le_f; unlock dlet=> y /=; apply/le_psum/summable_mlet.
move=> x; rewrite mulr_ge0 //=; case: (mu x =P 0).
  by move=> ->; rewrite !mul0r.
by move/dinsuppPn/le_f/(_ y) => h; rewrite ler_pmul.
Qed.

Lemma le_mu_dlet f mu nu : mu <=1 nu -> dlet f mu <=1 dlet f nu.
Proof.
move=> le_mu x; unlock dlet; rewrite /= /mlet.
apply/le_psum/summable_mlet => y; rewrite mulr_ge0 //=.
case: (mu y =P 0) => [->|]; first by rewrite mul0r mulr_ge0.
by move=>/dinsuppPn=> h; rewrite ler_pmul.
Qed.
End BindTheory.

Lemma dlet_dlet (T U V:choiceType) (mu : {distr T / R}) :
  forall (f1 : T -> distr U) (f2 : U -> distr V),
    \dlet_(x <- \dlet_(y <- mu) f1 y) f2 x =
    \dlet_(y <- mu) (\dlet_(x <- f1 y) f2 x).
Proof. Admitted.

(* -------------------------------------------------------------------- *)
Definition mlim T (f : nat -> distr T) : T -> R :=
  fun x => nlim (fun n => f n x).

Lemma isd_mlim T (f : nat -> distr T) : isdistr (mlim f).
Proof. split=> [x|J]; rewrite /mlim.
+ case: nlimP=> // l cvSl; apply/le0R/(ncvg_geC _ cvSl).
  by move=> n; apply/ge0_mu.
move=> uqJ; pose F j :=
  if `[< iscvg (fun n => f n j) >] then fun n => f n j else 0%:S.
apply/(@ler_trans _ (\sum_(j <- J) (nlim (F j) : R))).
  apply/ler_sum=> j _; rewrite /F; case/boolP: `[< _ >] => //.
  move/asboolPn=> h; rewrite nlimC; case: nlimP=> //.
  by case=> // l cf; case: h; exists l.
rewrite -lee_fin -nlim_sumR => [i _|].
  rewrite /F; case/boolP: `[< _ >] => [/asboolP //|].
  by move=> _; apply/iscvgC.
rewrite leeNgt; apply/negP; pose s n := \sum_(j <- J) F j n.
move/ncvg_gt=> -/(_ s (nlim_ncvg _)) [].
  suff: iscvg s by case=> l cs; exists l%:E.
  apply/iscvg_sum=> j _; rewrite /F; case/boolP: `[< _ >].
    by move/asboolP. by move=> _; apply/iscvgC.
move=> K /(_ _ (leqnn K)) /=; apply/negP; rewrite -lerNgt.
apply/(@ler_trans _ (\sum_(j <- J) f K j)); last first.
  have /(gerfinseq_psum uqJ) := summable_mu (f K).
  move/ler_trans=> -/(_ _ (le1_mu (f K)))=> h.
  by apply/(ler_trans _ h)/ler_sum=> i _; apply/ler_norm.
apply/ler_sum=> j _; rewrite /F; case/boolP: `[< _ >] => //.
by move=> _; apply/ge0_mu.
Qed.

Definition dlim T (f : nat -> distr T) :=
  locked (mkdistr (isd_mlim f)).

Notation "\dlim_ ( n ) E" := (dlim (fun n => E)).

Lemma dlimE T (f : nat -> distr T) x :
  (\dlim_(n) f n) x = nlim (fun n => f n x).
Proof. by unlock dlim. Qed.

(* -------------------------------------------------------------------- *)
Section DLimTheory.
Variables (T U : choiceType).

Implicit Types (f g : nat -> distr T) (h : T -> {distr U / R}).
Implicit Types (mu : {distr T / R}).

Lemma eq_dlim f g : f =2 g -> dlim f =1 dlim g.
Proof.
move=> eq_f; unlock dlim=> x /=; rewrite /mlim; congr (_ _).
by apply/eq_nlim => n; rewrite eq_f.
Qed.

Lemma le_dlim f g : (forall n, f n <=1 g n) -> dlim f <=1 dlim g.
Proof using Type. Admitted.

Lemma leub_dlim f mu : (forall n, f n <=1 mu) -> dlim f <=1 mu.
Proof.
move=> le x; apply/(@ler_trans _ ((\dlim_(n) mu) x)).
  by apply/le_dlim. by unlock dlim; rewrite /mlim /= nlimC.
Qed.

Lemma dlim_ub f k :
  (forall n m, (n <= m)%N -> f n <=1 f m) -> f k <=1 dlim f.
Proof using Type. Admitted.

Lemma dlet_lim f h :
  \dlet_(x <- dlim f) h x = \dlim_(n) \dlet_(x <- f n) h x.
Proof using Type. Admitted.
End DLimTheory.

(* -------------------------------------------------------------------- *)
Section Marginals.
Variable (T U : choiceType) (h : T -> U) (mu : distr T).

Definition dmargin := \dlet_(x <- mu) (dunit (h x)).

Lemma dmarginE : dmargin = \dlet_(y <- mu) (dunit (h y)).
Proof. by unlock dmargin. Qed.
End Marginals.

End Std.

Notation dfst mu := (dmargin fst mu).
Notation dsnd mu := (dmargin snd mu).

(* -------------------------------------------------------------------- *)
Notation "\dlet_ ( i <- d ) E" := (dlet (fun i => E) d).
Notation "\dlim_ ( n ) E" := (dlim (fun n => E)).

(* -------------------------------------------------------------------- *)
Section PrTheory.
Context {R : realType} (T U : choiceType).

Implicit Types (mu : {distr T / R}) (A B E : pred T).

Lemma pr_pred1 mu x : mu x = \P_[mu] (pred1 x).
Proof using Type. Admitted.

Lemma pr_exp mu (E : pred T) : \P_[mu] E = \E_[mu] (fun m => (E m)%:R).
Proof using Type. Admitted.

Lemma pr_predT mu : \P_[mu] predT = psum mu.
Proof. by apply/eq_psum=> x; rewrite mul1r. Qed.

Lemma pr_dunit E x : \P_[dunit x] E = (E x)%:R :> R.
Proof using Type. Admitted.

Lemma exp_dunit (f : T -> R) (x : T) : \E_[dunit x] f = f x.
Proof using Type. Admitted.

Lemma pr_dlet E f (mu : {distr U / R}) :
  \P_[dlet f mu] E = \E_[mu] (fun x => \P_[f x] E).
Proof using Type. Admitted.

Lemma ge0_pr A mu : 0 <= \P_[mu] A.
Proof. by apply/ge0_psum. Qed.

Lemma eq_pr A B mu : A =i B -> \P_[mu] A = \P_[mu] B.
Proof.
move=> eq_AB; apply/eq_psum => x; congr ((_ _)%:R * _).
by have := eq_AB x; rewrite -!topredE.
Qed.

Lemma subset_pr A B mu : {subset B <= A} -> \P_[mu] B <= \P_[mu] A.
Proof.
move=> le_BA; apply/le_psum; last first.
  apply/summableMl => //; exists 1=> // x.
  by rewrite ger0_norm ?(ler0n, lern1) ?leq_b1.
move=> x; rewrite mulr_ge0 ?ler0n ?ler_wpmul2r //.
rewrite ler_nat; have := le_BA x; rewrite -!topredE /=.
by case: (B x) => // ->.
Qed.

Lemma le1_pr A mu : \P_[mu] A <= 1.
Proof.
apply/(@ler_trans _ \P_[mu] predT).
  by apply/subset_pr. by rewrite pr_predT le1_mu.
Qed.

Lemma le_exp mu f1 f2:
  f1 <=1 f2 -> \E_[mu] f1 <= \E_[mu] f2.
Proof using Type. Admitted.

Lemma pr_or A B mu : \P_[mu] [predU A & B] =
  \P_[mu] A + \P_[mu] B - \P_[mu] [predI A & B].
Proof using Type. Admitted.

Lemma pr_and A B mu : \P_[mu] [predI A & B] =
  \P_[mu] A + \P_[mu] B - \P_[mu] [predU A & B].
Proof. by rewrite pr_or opprB addrCA subrr addr0. Qed.

Lemma ler_pr_or A B mu :
  \P_[mu] [predU A & B] <= \P_[mu] A + \P_[mu] B.
Proof. by rewrite pr_or ler_subl_addr ler_addl ge0_pr. Qed.

Lemma ler_pr_and A B mu :
  \P_[mu] [predI A & B] <= \P_[mu] A + \P_[mu] B.
Proof. by rewrite pr_and ler_subl_addr ler_addl ge0_pr. Qed.

Lemma pr_split B A mu : \P_[mu] A =
    \P_[mu]        B  * \P_[mu,       B] A
  + \P_[mu] (predC B) * \P_[mu, predC B] A.
Proof using Type. Admitted.

Lemma exp_split A f mu : \E?_[mu] f -> \E_[mu] f =
    \P_[mu]        A  * \E_[mu,       A] f
  + \P_[mu] (predC A) * \E_[mu, predC A] f.
Proof using Type. Admitted.

Lemma has_esp_bounded f mu :
  (exists M, forall x, `|f x| < M) -> \E?_[mu] f.
Proof using Type. Admitted.
End PrTheory.

(* -------------------------------------------------------------------- *)
