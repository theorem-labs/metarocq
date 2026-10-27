(* BET-315 eta lane, C3 prover D (adversarial), branch frac/eta-c3-d.

   This file carries, on the 9.2 AST, the definitions row C3 depends on (eta1 of U3,
   upto_domain of U1, upto_domain_ctx of the C section) EXACTLY as plan.md §3 states them,
   and the C3 statement itself together with the one-sided helper statements that encode the
   proof route EtaC3D recommends (lanes/eta/EtaC3D.md).

   Provenance: eta1 and upto_domain are the 2020 definitions
   (origin/eta_postpo:pcuic/theories/{PCUICConversionDef.v:361-523, PCUICEquality.v:1439-1498})
   transliterated to the 9.2 tCase (predicate/branch records), mirroring the base 9.2 red1 case
   congruences (PCUICReduction.v:94-109). upto_domain ignores, as plan I2 states, lambda domains,
   lambda/Prod/LetIn binder names, fix/cofix dname — and, for case binder contexts (pcontext,
   bcontext), their declaration types and names, keeping only their length (the arity): the
   case-context analogue of "ignores lambda domains", and the shape plan risk-5's fallback uses.

   No Admitted, no Axiom: this unit is the definitions, the C3 statement as a Prop, and the
   one-sided helper statements as Props. The C3 proof is the lane's open work (route in the
   EtaC3D lane file); this file is its faithful, building foundation. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICOnOne PCUICLiftSubst
     PCUICCases PCUICReduction PCUICEquality.
From Equations.Type Require Import Relation Relation_Properties.

(* clos_refl (0-or-1 step) as plan.md §3 writes it; defined locally to avoid relying on the
   exact Equations.Type.Relation export name. *)
Definition clos_refl {A} (R : A -> A -> Type) (x y : A) : Type := (x = y) + R x y.

(** ** η-contraction (eta1), 9.2 AST — plan U3 *)

Notation " 'eta_redex' na A t " :=
  (tLambda na A (tApp (lift0 1 t) (tRel 0)))
  (at level 30, na at level 0, A at level 0, t at level 0).

Inductive eta1 : term -> term -> Type :=
(* contraction at head *)
| eta_red na t A :
    eta1 (eta_redex na A t) t

(* congruences *)
| abs_eta_l na M M' N : eta1 M M' -> eta1 (tLambda na M N) (tLambda na M' N)
| abs_eta_r na M M' N : eta1 M M' -> eta1 (tLambda na N M) (tLambda na N M')

| letin_eta_def  na b t b' r : eta1 b r  -> eta1 (tLetIn na b t b') (tLetIn na r t b')
| letin_eta_ty   na b t b' r : eta1 t r  -> eta1 (tLetIn na b t b') (tLetIn na b r b')
| letin_eta_body na b t b' r : eta1 b' r -> eta1 (tLetIn na b t b') (tLetIn na b t r)

(* case: mirror base red1's case_red_param/return/discr/brs (PCUICReduction.v:94-109) *)
| case_eta_param ci p params' c brs :
    OnOne2 eta1 p.(pparams) params' ->
    eta1 (tCase ci p c brs) (tCase ci (set_pparams p params') c brs)
| case_eta_return ci p preturn' c brs :
    eta1 p.(preturn) preturn' ->
    eta1 (tCase ci p c brs) (tCase ci (set_preturn p preturn') c brs)
| case_eta_discr ci p c c' brs :
    eta1 c c' -> eta1 (tCase ci p c brs) (tCase ci p c' brs)
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
    eta1 (tCoFix mfix0 idx) (tCoFix mfix1 idx).

Definition eta := clos_refl_trans eta1.

(** ** Syntactic equality up-to domains (upto_domain), 9.2 AST — plan U1.
    Ignores lambda domains, lambda/Prod/LetIn binder names, fix/cofix dname, and (new on 9.2)
    case binder-context types/names, keeping context length (arity). *)

Inductive upto_domain : term -> term -> Type :=
| utd_Rel n : upto_domain (tRel n) (tRel n)
| utd_Var id : upto_domain (tVar id) (tVar id)
| utd_Sort s : upto_domain (tSort s) (tSort s)
| utd_Const c u : upto_domain (tConst c u) (tConst c u)
| utd_Ind i u : upto_domain (tInd i u) (tInd i u)
| utd_Construct i k u : upto_domain (tConstruct i k u) (tConstruct i k u)
| utd_Prim p : upto_domain (tPrim p) (tPrim p)

| utd_Evar e args args' :
    All2 upto_domain args args' -> upto_domain (tEvar e args) (tEvar e args')

| utd_App t t' u u' :
    upto_domain t t' -> upto_domain u u' -> upto_domain (tApp t u) (tApp t' u')

| utd_Lambda na na' ty ty' t t' :
    upto_domain t t' -> upto_domain (tLambda na ty t) (tLambda na' ty' t')

| utd_Prod na na' a a' b b' :
    upto_domain a a' -> upto_domain b b' -> upto_domain (tProd na a b) (tProd na' a' b')

| utd_LetIn na na' t t' ty ty' u u' :
    upto_domain t t' -> upto_domain ty ty' -> upto_domain u u' ->
    upto_domain (tLetIn na t ty u) (tLetIn na' t' ty' u')

| utd_Case ci p p' c c' brs brs' :
    #|pcontext p| = #|pcontext p'| ->
    puinst p = puinst p' ->
    All2 upto_domain (pparams p) (pparams p') ->
    upto_domain (preturn p) (preturn p') ->
    upto_domain c c' ->
    All2 (fun x y => (#|bcontext x| = #|bcontext y|) × upto_domain (bbody x) (bbody y)) brs brs' ->
    upto_domain (tCase ci p c brs) (tCase ci p' c' brs')

| utd_Proj p c c' : upto_domain c c' -> upto_domain (tProj p c) (tProj p c')

| utd_Fix mfix mfix' idx :
    All2 (fun x y => upto_domain x.(dtype) y.(dtype) × upto_domain x.(dbody) y.(dbody)
                     × x.(rarg) = y.(rarg)) mfix mfix' ->
    upto_domain (tFix mfix idx) (tFix mfix' idx)
| utd_CoFix mfix mfix' idx :
    All2 (fun x y => upto_domain x.(dtype) y.(dtype) × upto_domain x.(dbody) y.(dbody)
                     × x.(rarg) = y.(rarg)) mfix mfix' ->
    upto_domain (tCoFix mfix idx) (tCoFix mfix' idx).

(** upto_domain_ctx: declarationwise upto_domain on bodies and types, annotations ignored
    (plan.md §3, C section, line 537). *)
Definition upto_domain_decl (d d' : context_decl) : Type :=
  (((d.(decl_body) = None) × (d'.(decl_body) = None)) +
   { b & { b' & (d.(decl_body) = Some b) × (d'.(decl_body) = Some b') × upto_domain b b' } })
  × upto_domain d.(decl_type) d'.(decl_type).

Definition upto_domain_ctx (Γ Γ' : context) : Type := All2 upto_domain_decl Γ Γ'.

(** ** C3 statement (plan.md §3 row C3), and the one-sided helpers of the recommended route. *)

Section C3.
  Context {cf : checker_flags} (Σ : global_env) (Γ : context).

  (* Hindley strong commutation modulo upto_domain.  From a common source t, one red1 step to v
     and one eta1 step to u join at w ≈ w' where u→w is AT MOST ONE red1 and v→*w' is pure η. *)
  Definition C3_statement : Type :=
    forall t u v,
      red1 Σ Γ t v -> eta1 t u ->
      { w & { w' & (clos_refl (red1 Σ Γ) u w) *
                   (clos_refl_trans eta1 v w') *
                   upto_domain w w' } }%type.

  (* The go/no-go helper for the four unlocking cases, red_fix shown (red_cofix_case,
     red_cofix_proj, red_proj are the same shape).  When red1 at t is a red_fix firing on
     mkApps (tFix mfix idx) args and the eta1 step is on the fix head (mfix → mfix1), the join is
     ONE-SIDED exactly as C3 needs: the red1-reduct mkApps fn args closes by PURE η to mkApps fn'
     args (the fix body was η-reduced), and the eta-reduct mkApps (tFix mfix1 idx) args closes by
     ONE red_fix (is_constructor narg args preserved by η). *)
  Definition C3_unlock_fix_statement : Type :=
    forall mfix mfix1 idx args narg fn,
      unfold_fix mfix idx = Some (narg, fn) ->
      is_constructor narg args = true ->
      OnOne2 (on_Trel_eq eta1 dbody (fun x => (dname x, dtype x, rarg x))) mfix mfix1 ->
      { fn' & (clos_refl_trans eta1 fn fn')             (* red1-reduct side: PURE η *)
              × (unfold_fix mfix1 idx = Some (narg, fn')) }%type.
End C3.
