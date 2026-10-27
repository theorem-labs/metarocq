(* Distributed under the terms of the MIT license. *)
(* BET-315 eta lane, C3 prover A (branch frac/eta-c3-a).
   Scratch definitions of [upto_domain] (plan row U1) and [eta1] (plan row U3) on the
   9.2 AST, exactly as plan.md rev 11 §3 states them, plus the C3 statement.
   Self-contained: does NOT depend on L2's PCUICEtaReduction.v (not yet landed). *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Primitive.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICInduction PCUICPrimitive
     PCUICCases PCUICClosed PCUICTactics PCUICEquality PCUICReduction.

From Stdlib Require Import ssreflect ssrbool CRelationClasses.
From Equations.Prop Require Import DepElim.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
Set Equations Transparent.
Set Default Goal Selector "!".

Local Open Scope type_scope.
Import ListNotations.

(** ** Syntactic equality up to domains (plan row U1; 2020 PCUICEquality.v:1439-1498 ported to 9.2).
    Ignores exactly: lambda domains, lambda/Prod/LetIn binder annotations/names, fix/cofix [dname]. *)

Inductive upto_domain : term -> term -> Type :=
| utd_Rel n : upto_domain (tRel n) (tRel n)

| utd_Evar e args args' :
    All2 upto_domain args args' ->
    upto_domain (tEvar e args) (tEvar e args')

| utd_Var id : upto_domain (tVar id) (tVar id)

| utd_Sort s : upto_domain (tSort s) (tSort s)

| utd_App t t' u u' :
    upto_domain t t' ->
    upto_domain u u' ->
    upto_domain (tApp t u) (tApp t' u')

| utd_Const c u : upto_domain (tConst c u) (tConst c u)

| utd_Ind i u : upto_domain (tInd i u) (tInd i u)

| utd_Construct i k u : upto_domain (tConstruct i k u) (tConstruct i k u)

| utd_Lambda na na' ty ty' t t' :
    upto_domain t t' ->
    upto_domain (tLambda na ty t) (tLambda na' ty' t')

| utd_Prod na na' a a' b b' :
    upto_domain a a' ->
    upto_domain b b' ->
    upto_domain (tProd na a b) (tProd na' a' b')

| utd_LetIn na na' t t' ty ty' u u' :
    upto_domain t t' ->
    upto_domain ty ty' ->
    upto_domain u u' ->
    upto_domain (tLetIn na t ty u) (tLetIn na' t' ty' u')

| utd_Case ci p p' c c' brs brs' :
    All2 upto_domain p.(pparams) p'.(pparams) ->
    p.(puinst) = p'.(puinst) ->
    eq_context_upto_names p.(pcontext) p'.(pcontext) ->
    upto_domain p.(preturn) p'.(preturn) ->
    upto_domain c c' ->
    All2 (fun br br' =>
            eq_context_upto_names br.(bcontext) br'.(bcontext) ×
            upto_domain br.(bbody) br'.(bbody)) brs brs' ->
    upto_domain (tCase ci p c brs) (tCase ci p' c' brs')

| utd_Proj p c c' :
    upto_domain c c' ->
    upto_domain (tProj p c) (tProj p c')

| utd_Fix mfix mfix' idx :
    All2 (fun x y => upto_domain x.(dtype) y.(dtype) ×
                     upto_domain x.(dbody) y.(dbody) ×
                     x.(rarg) = y.(rarg)) mfix mfix' ->
    upto_domain (tFix mfix idx) (tFix mfix' idx)

| utd_CoFix mfix mfix' idx :
    All2 (fun x y => upto_domain x.(dtype) y.(dtype) ×
                     upto_domain x.(dbody) y.(dbody) ×
                     x.(rarg) = y.(rarg)) mfix mfix' ->
    upto_domain (tCoFix mfix idx) (tCoFix mfix' idx)

| utd_Prim p p' :
    onPrims upto_domain eq p p' ->
    upto_domain (tPrim p) (tPrim p').

Derive Signature for upto_domain.

#[global] Instance upto_domain_refl : Reflexive upto_domain.
Proof.
  intro t.
  induction t using term_forall_list_ind; try solve [constructor; auto].
  - constructor. eapply All_All2; eauto.
  - destruct X as (IHpars & _ & IHret).
    constructor; auto; try reflexivity.
    + eapply All_All2; eauto.
    + eapply All_All2; [eassumption|]. intros x [_ Hbody]. split; [reflexivity|exact Hbody].
  - constructor. eapply All_All2; eauto. intros x [? ?]; repeat split; auto.
  - constructor. eapply All_All2; eauto. intros x [? ?]; repeat split; auto.
  - constructor. destruct p as [? m]; destruct m; cbn in X |- *; try solve [constructor; auto].
    destruct X as (IHty & IHdef & IHval).
    constructor; cbn; auto. eapply All_All2; eauto.
Qed.

(** ** η-contraction + congruences (plan row U3; 2020 PCUICConversionDef.v:361-523 ported to 9.2). *)

Notation "'eta_redex' na A t" := (tLambda na A (tApp (lift0 1 t) (tRel 0)))
  (at level 30, na at level 0, A at level 0, t at level 0).

Inductive eta1 : term -> term -> Type :=
(* Head η-contraction *)
| eta_red na A t : eta1 (eta_redex na A t) t

(* Congruences *)
| abs_eta_l na M M' N : eta1 M M' -> eta1 (tLambda na M N) (tLambda na M' N)
| abs_eta_r na M M' N : eta1 M M' -> eta1 (tLambda na N M) (tLambda na N M')

| letin_eta_def na b t b' r : eta1 b r -> eta1 (tLetIn na b t b') (tLetIn na r t b')
| letin_eta_ty na b t b' r : eta1 t r -> eta1 (tLetIn na b t b') (tLetIn na b r b')
| letin_eta_body na b t b' r : eta1 b' r -> eta1 (tLetIn na b t b') (tLetIn na b t r)

| case_eta_pars ci p params' c brs :
    OnOne2 eta1 p.(pparams) params' ->
    eta1 (tCase ci p c brs) (tCase ci (set_pparams p params') c brs)
| case_eta_pret ci p preturn' c brs :
    eta1 p.(preturn) preturn' ->
    eta1 (tCase ci p c brs) (tCase ci (set_preturn p preturn') c brs)
| case_eta_discr ci p c c' brs : eta1 c c' -> eta1 (tCase ci p c brs) (tCase ci p c' brs)
| case_eta_brs ci p c brs brs' :
    OnOne2 (on_Trel_eq eta1 bbody bcontext) brs brs' ->
    eta1 (tCase ci p c brs) (tCase ci p c brs')

| proj_eta p c c' : eta1 c c' -> eta1 (tProj p c) (tProj p c')

| app_eta_l M1 N1 M2 : eta1 M1 N1 -> eta1 (tApp M1 M2) (tApp N1 M2)
| app_eta_r M2 N2 M1 : eta1 M2 N2 -> eta1 (tApp M1 M2) (tApp M1 N2)

| prod_eta_l na M1 M2 N1 : eta1 M1 N1 -> eta1 (tProd na M1 M2) (tProd na N1 M2)
| prod_eta_r na M2 N2 M1 : eta1 M2 N2 -> eta1 (tProd na M1 M2) (tProd na M1 N2)

| evar_eta ev l l' : OnOne2 eta1 l l' -> eta1 (tEvar ev l) (tEvar ev l')

| fix_eta_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq eta1 dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    eta1 (tFix mfix0 idx) (tFix mfix1 idx)
| fix_eta_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq eta1 dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
    eta1 (tFix mfix0 idx) (tFix mfix1 idx)

| cofix_eta_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq eta1 dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    eta1 (tCoFix mfix0 idx) (tCoFix mfix1 idx)
| cofix_eta_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq eta1 dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
    eta1 (tCoFix mfix0 idx) (tCoFix mfix1 idx)

| array_eta_val arr value :
    OnOne2 eta1 arr.(array_value) value ->
    eta1 (tPrim (primArray; primArrayModel arr))
         (tPrim (primArray; primArrayModel (set_array_value arr value)))
| array_eta_def arr def :
    eta1 arr.(array_default) def ->
    eta1 (tPrim (primArray; primArrayModel arr))
         (tPrim (primArray; primArrayModel (set_array_default arr def)))
| array_eta_type arr ty :
    eta1 arr.(array_type) ty ->
    eta1 (tPrim (primArray; primArrayModel arr))
         (tPrim (primArray; primArrayModel (set_array_type arr ty))).

Derive Signature for eta1.

Definition eta := clos_refl_trans eta1.

(** ** C3: Hindley strong commutation modulo [upto_domain] (plan §3, row C3). *)
Definition C3_statement {cf : checker_flags} (Σ : global_env) (Γ : context) (t v u : term) :=
  ∑ w w', clos_refl (red1 Σ Γ) u w × clos_refl_trans eta1 v w' × upto_domain w w'.
