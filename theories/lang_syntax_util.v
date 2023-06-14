Require Import String.
Require Import Classical_Prop. (* NB: to compile with Coq 8.17 *)
From mathcomp Require Import all_ssreflect.
Require Import signed.

(******************************************************************************)
(*                  Shared by lang_syntax_*.v files                           *)
(******************************************************************************)

Definition string_eqMixin := @EqMixin string String.eqb eqb_spec.
Canonical string_eqType := EqType string string_eqMixin.

Ltac inj_ex H := revert H;
  match goal with
  | |- existT ?P ?l (existT ?Q ?t (existT ?R ?u (existT ?T ?v ?v1))) =
       existT ?P ?l (existT ?Q ?t (existT ?R ?u (existT ?T ?v ?v2))) -> _ =>
    (intro H; do 4 apply Classical_Prop.EqdepTheory.inj_pair2 in H)
  | |- existT ?P ?l (existT ?Q ?t (existT ?R ?u ?v1)) =
       existT ?P ?l (existT ?Q ?t (existT ?R ?u ?v2)) -> _ =>
    (intro H; do 3 apply Classical_Prop.EqdepTheory.inj_pair2 in H)
  | |- existT ?P ?l (existT ?Q ?t ?v1) =
       existT ?P ?l (existT ?Q ?t ?v2) -> _ =>
    (intro H; do 2 apply Classical_Prop.EqdepTheory.inj_pair2 in H)
  | |- existT ?P ?l (existT ?Q ?t ?v1) =
       existT ?P ?l (existT ?Q ?t' ?v2) -> _ =>
    (intro H; do 2 apply Classical_Prop.EqdepTheory.inj_pair2 in H)
  | |- existT ?P ?l ?v1 =
       existT ?P ?l ?v2 -> _ =>
    (intro H; apply Classical_Prop.EqdepTheory.inj_pair2 in H)
  | |- existT ?P ?l ?v1 =
       existT ?P ?l' ?v2 -> _ =>
    (intro H; apply Classical_Prop.EqdepTheory.inj_pair2 in H)
end.

Set Implicit Arguments.
Unset Strict Implicit.
Set Printing Implicit Defensive.

Section tagged_context.
Context {T : eqType} {t0 : T}.
Let ctx := seq (string * T).
Implicit Types (str : string) (g : ctx) (t : T).

Structure tagged_ctx := Tag {untag : ctx}.

Structure find str t := Find {
  ctx_of : tagged_ctx ;
  ctx_prf : t = nth t0 (map snd (untag ctx_of))
                       (index str (map fst (untag ctx_of)))}.

Lemma ctx_prf_head str t g :
  t = nth t0 (map snd ((str, t) :: g))
             (index str (map fst ((str, t) :: g))).
Proof. by rewrite /= !eqxx. Qed.

Lemma ctx_prf_tail str t g str' t' :
  str != str' ->
  t' = nth t0 (map snd g) (index str' (map fst g)) ->
  t' = nth t0 (map snd ((str, t) :: g))
              (index str' (map fst ((str, t) :: g))).
Proof.
by move=> strstr' t'g /=; case: ifPn => //=; rewrite (negbTE strstr').
Qed.

Definition recurse_tag g := Tag g.
Canonical found_tag g := recurse_tag g.

Canonical found str t g : find str t :=
  @Find str t (found_tag ((str, t) :: g))
              (@ctx_prf_head str t g).

Canonical recurse str t str' t' {H : infer (str != str')}
    (F : find str' t') : find str' t' :=
  @Find str' t' (recurse_tag ((str, t) :: untag (ctx_of F)))
    (@ctx_prf_tail str t (untag (ctx_of F)) str' t' H (ctx_prf F)).

End tagged_context.
