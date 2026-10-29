(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICUnivSubst PCUICEquality
     PCUICReduction PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICTypingEta
     PCUICWellScopedCumulativity PCUICWellScopedCumulativityEta PCUICContextSubst.
From Equations.Type Require Import Relation.
From Equations Require Import Equations.

(** * ETAK (EtaK7): the definitional η copies the η checker needs

  BET-64 EtaCheckerLane, worker EtaK7, 2026-10-29; base [frac/eta] @ [0cb773a4].

  Definitions only: no hypothesis. Each one is the base definition with [typing] replaced by [typingE]
  and the cumulativity by [ws_cumul_pbE]:
  - [isTypeE], [isTypeRelE], [wf_local_relE]: [EnvironmentTyping.v:2752-2783] at [typingE];
  - the bidirectional judgments [inferingE], [infering_sortE], [infering_prodE], [infering_induE],
    [checkingE] ([BDTyping.v:40-172]). Base [checking] compares with [cumulAlgo] (unscoped) and the
    case rule compares parameters with [convAlgo]; here both compare with [ws_cumul_pbE] (scoped), which
    is what the η conversion returns ([isconv_term_sound]), so the checker needs no forgetful step;
    [ws_cumul_pbE_forget] gives the unscoped join [JoinE] when a later proof wants it;
  - [subsletE] ([PCUICSubstitution.v:45]), [spine_substE] ([PCUICSpine.v:226]), [typing_spineE]
    ([PCUICArities.v:44]), [ws_cumul_ctx_pbE_rel] ([PCUICConversion.v:3422]), and [ctx_instE] (the
    generic [ctx_inst] at [typingE], as base [PCUICSpine.v:28] instantiates it at [typing]).

  Plan rows: T0 owns [isType], [subslet], [spine_subst], [typing_spine]; T6 owns [Bidirectional/BD*].
  When those rows land, their files own these definitions and this file goes. *)

Implicit Types (cf : checker_flags) (Σ : global_env_ext) (Γ : context).

(** ** Well-scoped cumulativity notations over [ws_cumul_pbE] *)

Notation " Σ ;;; Γ ⊢E t ≤[ pb ] u " := (ws_cumul_pbE pb Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢E  t  ≤[ pb ]  u") : type_scope.
Notation " Σ ;;; Γ ⊢E t ≤ u " := (ws_cumul_pbE Cumul Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢E  t  ≤  u") : type_scope.
Notation " Σ ;;; Γ ⊢E t = u " := (ws_cumul_pbE Conv Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢E  t  =  u") : type_scope.

(** ** Types over [typingE] *)

Definition isTypeRelE `{checker_flags} (Σ : global_env_ext) (Γ : context) (t : term) (rel : relevance) :=
  on_type_rel (lift_typing typingE) Σ Γ t rel.

Definition isTypeE `{checker_flags} (Σ : global_env_ext) (Γ : context) (t : term) :=
  on_type (lift_typing typingE) Σ Γ t.

Definition isTypeRelE_isTypeE `{checker_flags} (Σ : global_env_ext) (Γ : context) (t : term) (r : relevance) :
  isTypeRelE Σ Γ t r -> isTypeE Σ Γ t.
Proof. apply lift_sorting_forget_rel. Defined.
Coercion isTypeRelE_isTypeE : isTypeRelE >-> isTypeE.

Definition wf_local_relE `{checker_flags} Σ := All_local_rel (lift_typing1 (typingE Σ)).

Notation ctx_instE Σ := (PCUICTyping.ctx_inst (typingE Σ)).

(** [PCUICSpine.ctx_inst_sub] at [typingE]. *)
Fixpoint ctx_inst_subE {cf:checker_flags} {Σ Γ Δ args} (c : ctx_instE Σ Γ args Δ) {struct c} : list term :=
  match c return _ with
  | ctx_inst_nil => []
  | ctx_inst_ass na t i inst Δ P c => ctx_inst_subE c ++ [i]
  | ctx_inst_def na b t inst Δ c => ctx_inst_subE c ++ [b]
  end.

Definition isWfArityE {cf : checker_flags} Σ (Γ : context) T :=
  (isTypeE Σ Γ T × { ctx & { s & (destArity [] T = Some (ctx, s)) } }).

Definition isTypeE_welltypedE {cf Σ} {Γ T} : isTypeE Σ Γ T -> welltypedE Σ Γ T.
Proof. intros [_ [s []]]. now econstructor. Qed.

Definition isTypeRelE_welltypedE {cf Σ} {Γ T r} : isTypeRelE Σ Γ T r -> welltypedE Σ Γ T.
Proof. intros [_ [s []]]. now econstructor. Qed.

Definition has_sort_isTypeE {cf Σ} {Γ T} s : Σ ;;; Γ |-E T : tSort s -> isTypeE Σ Γ T.
Proof. repeat (eexists; tea). Defined.

Definition has_sort_isTypeRelE {cf Σ} {Γ T} s r :
  isSortRel s r -> Σ ;;; Γ |-E T : tSort s -> isTypeRelE Σ Γ T r.
Proof. repeat (eexists; tea). Defined.

Lemma typingE_welltypedE {cf Σ} {Γ t T} : Σ ;;; Γ |-E t : T -> welltypedE Σ Γ t.
Proof. intros h. now econstructor. Qed.

(** ** Bidirectional typing over E *)

Reserved Notation " Σ ;;; Γ |-E t ▹ T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ |-E t ▹□ u " (at level 50, Γ, t, u at next level).
Reserved Notation " Σ ;;; Γ |-E t ▹Π ( na , A , B ) " (at level 50, Γ, t, na, A, B at next level).
Reserved Notation " Σ ;;; Γ |-E t ▹{ ind } ( u , args )" (at level 50, Γ, t, ind, u, args at next level).
Reserved Notation " Σ ;;; Γ |-E t ◃ T " (at level 50, Γ, t, T at next level).
Reserved Notation "'wf_local_bdE' Σ Γ " (at level 9, Σ, Γ at next level).
Reserved Notation "'wf_local_bd_relE' Σ Γ Γ'" (at level 9, Σ, Γ, Γ' at next level).

From MetaRocq.PCUIC Require BDTyping.

Inductive inferingE `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| inferE_Rel n decl :
  nth_error Γ n = Some decl ->
  Σ ;;; Γ |-E tRel n ▹ lift0 (S n) (decl_type decl)

| inferE_Sort s :
  wf_sort Σ s ->
  Σ ;;; Γ |-E tSort s ▹ tSort (Sort.super s)

| inferE_Prod na A B s1 s2 :
  lift_sorting (checkingE Σ Γ) (infering_sortE Σ Γ) (j_vass_s na A s1) ->
  Σ ;;; Γ ,, vass na A |-E B ▹□ s2 ->
  Σ ;;; Γ |-E tProd na A B ▹ tSort (Sort.sort_of_product s1 s2)

| inferE_Lambda na A t B :
  lift_sorting (checkingE Σ Γ) (infering_sortE Σ Γ) (j_vass na A) ->
  Σ ;;; Γ ,, vass na A |-E t ▹ B ->
  Σ ;;; Γ |-E tLambda na A t ▹ tProd na A B

| inferE_LetIn na b B t A :
  lift_sorting (checkingE Σ Γ) (infering_sortE Σ Γ) (j_vdef na b B) ->
  Σ ;;; Γ ,, vdef na b B |-E t ▹ A ->
  Σ ;;; Γ |-E tLetIn na b B t ▹ tLetIn na b B A

| inferE_App t na A B u :
  Σ ;;; Γ |-E t ▹Π (na,A,B) ->
  Σ ;;; Γ |-E u ◃ A ->
  Σ ;;; Γ |-E tApp t u ▹ B{0 := u}

| inferE_Const cst u :
  forall decl (isdecl : declared_constant Σ.1 cst decl),
  consistent_instance_ext Σ (cst_universes decl) u ->
  Σ ;;; Γ |-E tConst cst u ▹ subst_instance u (cst_type decl)

| inferE_Ind ind u :
  forall mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl),
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  Σ ;;; Γ |-E tInd ind u ▹ subst_instance u (ind_type idecl)

| inferE_Construct ind i u :
  forall mdecl idecl cdecl (isdecl : declared_constructor Σ.1 (ind, i) mdecl idecl cdecl),
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  Σ ;;; Γ |-E tConstruct ind i u ▹ type_of_constructor mdecl cdecl (ind, i) u

| inferE_Case ci p c brs args u ps mdecl idecl :
  let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
  let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
  Σ ;;; Γ |-E c ▹{ci} (u,args) ->
  declared_inductive Σ.1 ci.(ci_ind) mdecl idecl ->
  Σ ;;; Γ ,,, predctx |-E p.(preturn) ▹□ ps ->
  (* case_side_conditions *)
  mdecl.(ind_npars) = ci.(ci_npar) ->
  eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
  wf_predicate mdecl idecl p ->
  consistent_instance_ext Σ (ind_universes mdecl) (puinst p) ->
  wf_local_bd_relE Σ Γ predctx ->
  is_allowed_elimination Σ (ind_kelim idecl) ps ->
  isSortRel ps ci.(ci_relevance) ->
  PCUICTyping.ctx_inst (checkingE Σ) Γ (pparams p)
      (List.rev mdecl.(ind_params)@[p.(puinst)]) ->
  implb (isCoFinite mdecl.(ind_finite)) (on_free_vars (strengthenP 0 1 ssrbool.xpredT) p.(preturn)) = true ->
  cmp_ind_universes Σ ci #|args| u (puinst p) ->
  All2 (ws_cumul_pbE Conv Σ Γ) (firstn (ci_npar ci) args) (pparams p) ->
  (* case_branch_typing *)
  wf_branches idecl brs ->
  All2i (fun i cdecl br =>
    eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl) ×
    let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
    wf_local_bd_relE Σ Γ brctxty.1 ×
    Σ ;;; Γ ,,, brctxty.1 |-E br.(bbody) ◃ brctxty.2)
    0 idecl.(ind_ctors) brs ->
  Σ ;;; Γ |-E tCase ci p c brs ▹ mkApps ptm (skipn ci.(ci_npar) args ++ [c])

| inferE_Proj p c u mdecl idecl cdecl pdecl args :
  declared_projection Σ.1 p mdecl idecl cdecl pdecl ->
  Σ ;;; Γ |-E c ▹{p.(proj_ind)} (u,args) ->
  #|args| = ind_npars mdecl ->
  Σ ;;; Γ |-E tProj p c ▹ subst0 (c :: List.rev args) (subst_instance u pdecl.(proj_type))

| inferE_Fix mfix n decl :
  fix_guard Σ Γ mfix ->
  nth_error mfix n = Some decl ->
  All (on_def_type (lift_sorting1 (checkingE Σ) (infering_sortE Σ)) Γ) mfix ->
  All (on_def_body (lift_sorting1 (checkingE Σ) (infering_sortE Σ)) (fix_context mfix) Γ) mfix ->
  BDTyping.wf_fixpoint_red Σ Γ mfix ->
  Σ ;;; Γ |-E tFix mfix n ▹ dtype decl

| inferE_CoFix mfix n decl :
  cofix_guard Σ Γ mfix ->
  nth_error mfix n = Some decl ->
  All (on_def_type (lift_sorting1 (checkingE Σ) (infering_sortE Σ)) Γ) mfix ->
  All (on_def_body (lift_sorting1 (checkingE Σ) (infering_sortE Σ)) (fix_context mfix) Γ) mfix ->
  BDTyping.wf_cofixpoint_red Σ Γ mfix ->
  Σ ;;; Γ |-E tCoFix mfix n ▹ dtype decl

| inferE_Prim p prim_ty cdecl :
   primitive_constant Σ (prim_val_tag p) = Some prim_ty ->
   declared_constant Σ prim_ty cdecl ->
   primitive_invariants (prim_val_tag p) cdecl ->
   primitive_typing_hyps (checkingE Σ) Σ Γ p ->
   Σ ;;; Γ |-E tPrim p ▹ prim_type p prim_ty

with infering_sortE `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> sort -> Type :=
| inferE_sort_Sort t T u:
  Σ ;;; Γ |-E t ▹ T ->
  red Σ Γ T (tSort u) ->
  Σ ;;; Γ |-E t ▹□ u

with infering_prodE `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> aname -> term -> term -> Type :=
| inferE_prod_Prod t T na A B:
  Σ ;;; Γ |-E t ▹ T ->
  red Σ Γ T (tProd na A B) ->
  Σ ;;; Γ |-E t ▹Π (na,A,B)

with infering_induE `{checker_flags} (Σ : global_env_ext) (Γ : context) : inductive -> term -> Instance.t -> list term -> Type :=
| inferE_ind_Ind ind t T u args:
  Σ ;;; Γ |-E t ▹ T ->
  red Σ Γ T (mkApps (tInd ind u) args) ->
  Σ ;;; Γ |-E t ▹{ind} (u,args)

with checkingE `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| checkE_Cumul t T T':
  Σ ;;; Γ |-E t ▹ T ->
  ws_cumul_pbE Cumul Σ Γ T T' ->
  Σ ;;; Γ |-E t ◃ T'

where " Σ ;;; Γ |-E t ▹ T " := (@inferingE _ Σ Γ t T) : type_scope
and " Σ ;;; Γ |-E t ▹□ u " := (@infering_sortE _ Σ Γ t u) : type_scope
and " Σ ;;; Γ |-E t ▹Π ( na , A , B ) " := (@infering_prodE _ Σ Γ t na A B) : type_scope
and " Σ ;;; Γ |-E t ▹{ ind } ( u , args ) " := (@infering_induE _ Σ Γ ind t u args) : type_scope
and " Σ ;;; Γ |-E t ◃ T " := (@checkingE _ Σ Γ t T) : type_scope
and "'wf_local_bdE' Σ Γ" := (All_local_env (lift_sorting1 (checkingE Σ) (infering_sortE Σ)) Γ)
and "'wf_local_bd_relE' Σ Γ Γ'" := (All_local_rel (lift_sorting1 (checkingE Σ) (infering_sortE Σ)) Γ Γ').

Derive Signature for inferingE infering_sortE infering_prodE infering_induE checkingE.

(** ** Substitutions, spines and context cumulativity over E *)

Inductive subsletE {cf:checker_flags} Σ (Γ : context) : list term -> context -> Type :=
| emptysletE : subsletE Σ Γ [] []
| cons_let_assE Δ s na t T : subsletE Σ Γ s Δ ->
              Σ ;;; Γ |-E t : subst0 s T ->
             subsletE Σ Γ (t :: s) (Δ ,, vass na T)
| cons_let_defE Δ s na t T :
    subsletE Σ Γ s Δ ->
    Σ ;;; Γ |-E subst0 s t : subst0 s T ->
    subsletE Σ Γ (subst0 s t :: s) (Δ ,, vdef na t T).
Derive Signature for subsletE.

Record spine_substE {cf:checker_flags} Σ Γ inst s (Δ : context) := mkSpineSubstE {
  spine_dom_wfE : wf_localE Σ Γ;
  spine_codom_wfE : wf_localE Σ (Γ ,,, Δ);
  inst_ctx_substE :> context_subst Δ inst s;
  inst_subsletE :> subsletE Σ Γ s Δ }.
Arguments inst_ctx_substE {cf Σ Γ inst s Δ}.
Arguments inst_subsletE {cf Σ Γ inst s Δ}.

Inductive typing_spineE {cf} Σ (Γ : context) : term -> list term -> term -> Type :=
| type_spine_nilE ty ty' :
    isTypeE Σ Γ ty ->
    isTypeE Σ Γ ty' ->
    Σ ;;; Γ ⊢E ty ≤ ty' ->
    typing_spineE Σ Γ ty [] ty'

| type_spine_consE ty hd tl na A B B' :
    isTypeE Σ Γ ty ->
    isTypeE Σ Γ (tProd na A B) ->
    Σ ;;; Γ ⊢E ty ≤ tProd na A B ->
    Σ ;;; Γ |-E hd : A ->
    typing_spineE Σ Γ (subst10 hd B) tl B' ->
    typing_spineE Σ Γ ty (hd :: tl) B'.
Derive Signature for typing_spineE.

Definition ws_cumul_ctx_pbE_rel {cf} pb Σ Γ Δ Δ' :=
  is_closed_context Γ ×
  All2_fold (fun Γ' _ => All_decls_alpha_pb pb (fun pb x y => Σ ;;; Γ ,,, Γ' ⊢E x ≤[pb] y)) Δ Δ'.
