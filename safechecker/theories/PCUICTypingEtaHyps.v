(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config uGraph PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive PCUICLiftSubst PCUICUnivSubst
     PCUICSigmaCalculus PCUICEquality PCUICReduction PCUICOnFreeVars PCUICClosed PCUICTyping PCUICCumulativity
     PCUICCumulativitySpec PCUICWellScopedCumulativity PCUICContextSubst PCUICCases PCUICNormal PCUICPosition
     PCUICConversion PCUICFixWitness PCUICWfUniverses PCUICClosedBodies PCUICSpine PCUICWeakeningEnv
     PCUICInductiveInversion PCUICContextConversionTyp
     PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd PCUICEtaI5 PCUICWellScopedCumulativityEta
     PCUICConversionEtaCongr PCUICContextConversionEta PCUICWsCumulEtaSubst PCUICEtaA6
     PCUICClosedTypEta PCUICWeakeningEnvTypEta.
(** [ws_cumul_ctx_pbE_rel] and [ws_cumul_ctx_pbE_rel_app] are canonical in [PCUICWsCumulEtaCtx] (P3, ArityLane). *)
From MetaRocq.PCUIC Require Import PCUICWsCumulEtaCtx.
From MetaRocq.PCUIC Require PCUICInductives PCUICSubstitution PCUICSafeLemmata.
From Stdlib Require Import Program.Equality.
(* for the section "PROVED rows" (EtaHypProve's proofs) *)
From MetaRocq.PCUIC Require Import PCUICTactics PCUICRenameDef PCUICEtaA6Ind PCUICEtaA6More PCUICGlobalEnvEta
     PCUICWeakeningTypEta PCUICRenameTypEta PCUICInstDefEta PCUICInstTypEta PCUICCasesWfTypEta PCUICGuardClosureEta
     PCUICInversionEta PCUICSREtaConv.
From MetaRocq.PCUIC Require PCUICSR PCUICInduction PCUICPositionEta PCUICInstConv PCUICContexts PCUICWeakeningConv.
From MetaRocq.SafeChecker Require Import PCUICTypingEtaDefs.

(** * ETAK (EtaK7): the η typing facts the η checker needs, as NAMED hypotheses

  BET-64 EtaCheckerLane, worker EtaK7, 2026-10-29; base [frac/eta] @ [0cb773a4]. Plan rows K7/K8 (the η
  copies of [PCUICTypeChecker], [PCUICSafeChecker], [PCUICSafeRetyping], [PCUICRetypingEnvIrrelevance],
  [SafeTemplateChecker]) need the E version of each base typing-metatheory lemma they use. The exact list
  is the inventory [lanes/eta/etak/EtaK7-inventory.md] (from the base build's [.glob] files).

  Each fact is the base lemma with [typing] → [typingE], [wf]/[wf_ext] → [wfE]/[wf_extE],
  [wf_local] → [wf_localE], [isType] → [isTypeE], [welltyped] → [welltypedE], the bidirectional judgments →
  the canonical E judgments of EtaMetaLane's [BDTypingEta] (re-exported by [PCUICTypingEtaDefs]), and the
  well-scoped cumulativity → [ws_cumul_pbE]. It keeps the
  base lemma's NAME, so the copies' proof scripts read as base's; this file is imported LAST.

  - Facts no row has proved yet are fields of one class per plan row ([T0_facts], [T1_facts], [T2a_facts],
    [T6_facts], [T6BD_facts], [T6BDu_facts], [T6BDc_facts], and [U_facts] for untyped plumbing). The copies
    take them through ONE implicit Prop premise [{EtaF : EtaFacts}] (the squashes of the eight classes, end
    of this file), so extraction erases them. When a row lands, its class gets an instance and its field of
    [EtaFacts] is proved.
  - Facts that follow from what base already proves over E ([PCUICClosedTypEta], [PCUICTypingEtaInd],
    [PCUICEtaA6], [PCUICWsCumulEtaSubst], [PCUICWellScopedCumulativityEta], [PCUICEtaI5]) or from the class
    fields are PROVED below the classes, under the base name ("Derived", "Derived, second part", "PROVED
    rows", "Derived lemmas that use former fields").
  - Bundle size: 44 named hypotheses (class fields). Audits hyp-audit-A.md and hyp-audit-B.md
    (lanes/eta/etak/) turned 9 former fields into PROVED lemmas, which are NO LONGER hypotheses (bundle
    101 -> 92): [type_Cumul_alt] (T1), [isType_Sort_inv] (T2a), [inversion_Const], [inversion_LetIn],
    [inversion_Prod], [inversion_Rel], [inversion_Sort] (T6), [type_ws_cumul_pb] and
    [mfix_body_on_red_unique] (T0; these two are STATEMENT CHANGEs, marked where they occur). Then
    [ws_cumul_ctx_pb_rel_app] (class A, the last field of A) became a PROVED lemma from
    [PCUICWsCumulEtaCtx.ws_cumul_ctx_pbE_rel_app] ([frac/eta] @ [d8120081]); class A is gone (bundle 92 -> 91).
    Then 47 more former fields became PROVED lemmas of the same name and statement (EtaHypProve's proofs,
    section "PROVED rows"; bundle 91 -> 44): T0 37, U 8, T1 [isType_prim_arg_types], T6BD [wf_rel_weak].
  - Instances. EVERY one of the 44 fields has a concrete satisfying instance, in the final section
    "Instances" of this file (one lemma [<field>_inst] per field, proved without any class field; written
    by EtaK7Inst). Per class, fields = instances: T0_facts 12, U_facts 1, T1_facts 4, T2a_facts 2,
    T6_facts 1, T6BD_facts 9, T6BDu_facts 9, T6BDc_facts 6. Each instance carries a tag
    [(* non-degenerate *)] or [(* degenerate: NOT BUILT — <why> *)]; 37 are non-degenerate (three of them
    type through an η step: [validity], [checking_typing], [infering_checking], via [cumul_eta_l]), 0 are
    IMPOSSIBLE and 7 are NOT BUILT ([inductive_cumulative_indices], [isTypeRel_cstr_type],
    [isType_mkApps_Ind_inv], [typing_spine_ind_type_inv], [wf_case_branch_type], [wf_case_predicate_context],
    [wf_case_branches_types']: each needs a new inductive declaration, an indexed family or one with a redex
    in its arity; list and reasons at the top of the section "Instances"). Non-degenerate instances show
    satisfiability on ordinary typed terms; outside the three η rows none exercises an eta pair;
    the eta-case truth of these hypotheses is established by T6, not by the instance. The
    environment is [si_Σ] of [PCUICCumulativitySpecEtaClosureInstances], or, for the primitive-operation
    field of T1, [Σ_po] of [PCUICEtaPrimOpInstance] (convention of [PCUICEtaFracInstances]). An instance
    shows only that the field's premises can hold at a real environment, and does NOT discharge the field
    at [typingE]: subject reduction over [typingE] (row T1), validity (T2a), the inversions and the
    bidirectional facts (T6, whose completeness part T6BDc is as strong as typed T8) and the
    infrastructure copies (T0) remain hypotheses until their rows land.

  Not stated here, on purpose: base [ws_cumul_pb_Sort_r_inv] (used only by [PCUICSafeRetyping]): its E form
  ([T ≤E tSort s] → [T ⇝ tSort s']) is FALSE untyped (plan §3, A6 F rows); its typed form is T8. *)

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(** ** T0 (E copies of the typing infrastructure: Substitution, Typing/*, Spine, Inductives, Contexts, WfUniverses, FixWitness, Arities, InductiveInversion) *)
Class T0_facts {cf : checker_flags} := {
  closed_context_cumulativity :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ.1} (Γ : context) {pb : conv_pb} {t : term} {T : term} {Γ' : context}, Σ;;; Γ |-E t : T -> wf_localE Σ Γ' -> ws_cumul_ctx_pbE pb Σ Γ' Γ -> Σ;;; Γ' |-E t : T ;
  inductive_cumulative_indices :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {ind : inductive} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {u : Instance.t} {u' : Instance.t} {napp : nat}, declared_inductive Σ ind mdecl idecl -> consistent_instance_ext Σ (ind_universes mdecl) u -> consistent_instance_ext Σ (ind_universes mdecl) u' -> PCUICEquality.cmp_ind_universes Σ ind napp u u' -> forall (Γ : context) (pars : list term) (pars' : list term) (parsubst : list term) (parsubst' : list term), spine_substE Σ Γ pars parsubst (ind_params mdecl)@[u] -> spine_substE Σ Γ pars' parsubst' (ind_params mdecl)@[u'] -> ws_cumul_pbE_terms Σ Γ pars pars' -> let indctx := (ind_indices idecl)@[u] in let indctx' := (ind_indices idecl)@[u'] in let pindctx := subst_context parsubst 0 indctx in let pindctx' := subst_context parsubst' 0 indctx' in ws_cumul_ctx_pbE_rel Cumul Σ Γ (smash_context [] pindctx) (smash_context [] pindctx') ;
  invert_type_mkApps_ind :
    forall (Σ : global_env_ext) (Γ : context) (ind : inductive) (u : Instance.t) (args : list term) (T : term) (mdecl : mutual_inductive_body) (idecl : one_inductive_body), wfE Σ.1 -> declared_inductive Σ.1 ind mdecl idecl -> Σ;;; Γ |-E mkApps (tInd ind u) args : T -> typing_spineE Σ Γ (ind_type idecl)@[u] args T × consistent_instance_ext Σ (ind_universes mdecl) u ;
  isTypeRel_cstr_type :
    forall (Σ : global_env_ext) (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (cdecl : constructor_body) (n : nat), wfE Σ.1 -> nth_error (ind_bodies mdecl) n = Some idecl -> cstr_type cdecl = it_mkProd_or_LetIn (ind_params mdecl,,, cstr_args cdecl) (mkApps (tRel (#|ind_params mdecl,,, cstr_args cdecl| + (#|ind_bodies mdecl| - S n))) (to_extended_list_k (ind_params mdecl) #|cstr_args cdecl| ++ cstr_indices cdecl)) -> isTypeE Σ [] (ind_type idecl) -> PCUICReduction.red Σ.1 [] (ind_type idecl) (it_mkProd_or_LetIn (ind_params mdecl) (it_mkProd_or_LetIn (ind_indices idecl) (tSort (ind_sort idecl)))) -> isTypeE Σ [] (it_mkProd_or_LetIn (ind_params mdecl) (it_mkProd_or_LetIn (ind_indices idecl) (tSort (ind_sort idecl)))) -> isSortRel (ind_sort idecl) (ind_relevance idecl) -> ctx_instE Σ (arities_context (ind_bodies mdecl),,, ind_params mdecl,,, cstr_args cdecl) (cstr_indices cdecl) (List.rev (lift_context #|cstr_args cdecl| 0 (ind_indices idecl))) -> isTypeE Σ (arities_context (ind_bodies mdecl)) (cstr_type cdecl) -> isTypeRelE Σ (arities_context (ind_bodies mdecl)) (cstr_type cdecl) (ind_relevance idecl) ;
  isType_mkApps_Ind :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {mdecl : mutual_inductive_body} {ind : inductive} {idecl : one_inductive_body} (decli : declared_inductive Σ ind mdecl idecl) {Γ : context} {puinst : Instance.t} {args : list term} {inst : list term}, consistent_instance_ext Σ (ind_universes mdecl) puinst -> spine_substE Σ Γ args inst (ind_params mdecl,,, ind_indices idecl)@[puinst] -> Σ;;; Γ |-E mkApps (tInd ind puinst) args : tSort (ind_sort idecl)@[puinst] ;
  isType_mkApps_Ind_inv :
    forall {Σ : global_env_ext} {Γ : context} {ind : inductive} {u : Instance.t} {args : list term} (wfΣ : wfE Σ.1) {mdecl : mutual_inductive_body} {idecl : one_inductive_body} (declm : declared_inductive Σ.1 ind mdecl idecl), wf_localE Σ Γ -> isTypeE Σ Γ (mkApps (tInd ind u) args) -> ∑ parsubst argsubst : list term, let parctx := (ind_params mdecl)@[u] in let argctx := subst_context parsubst 0 (ind_indices idecl)@[u] in [× spine_substE Σ Γ (firstn (ind_npars mdecl) args) parsubst parctx, spine_substE Σ Γ (skipn (ind_npars mdecl) args) argsubst argctx, #|firstn (ind_npars mdecl) args| = ind_npars mdecl, #|skipn (ind_npars mdecl) args| = context_assumptions (ind_indices idecl) & consistent_instance_ext Σ (ind_universes mdecl) u] ;
  on_minductive_wf_params :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {ind : kername} {mdecl : mutual_inductive_body} {u : Instance.t}, declared_minductive Σ.1 ind mdecl -> consistent_instance_ext Σ (ind_universes mdecl) u -> wf_localE Σ (ind_params mdecl)@[u] ;
  on_minductive_wf_params_indices_inst :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {mdecl : mutual_inductive_body} {ind : inductive} {idecl : one_inductive_body} (decli : declared_inductive Σ ind mdecl idecl) (u : Instance.t), consistent_instance_ext Σ (ind_universes mdecl) u -> wf_localE Σ (ind_params mdecl,,, ind_indices idecl)@[u] ;
  typing_spine_ind_type_inv :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {mdecl : mutual_inductive_body} {ind : inductive} {idecl : one_inductive_body} (decli : declared_inductive Σ ind mdecl idecl) (Γ : context) (u : Instance.t) (args : list term) (T : term), wf_localE Σ Γ -> consistent_instance_ext Σ (ind_universes mdecl) u -> typing_spineE Σ Γ (ind_type idecl)@[u] args T -> typing_spineE Σ Γ (it_mkProd_or_LetIn (ind_params mdecl,,, ind_indices idecl) (tSort (ind_sort idecl)))@[u] args T ;
  wf_case_branch_type :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {ci : case_info} {p : predicate term} (ps : sort) (args : list term), declared_inductive Σ ci mdecl idecl -> isTypeE Σ Γ (mkApps (tInd ci (puinst p)) (pparams p ++ args)) -> wf_predicate mdecl idecl p -> let predctx := case_predicate_context ci mdecl idecl p in Σ;;; Γ,,, predctx |-E preturn p : tSort ps -> let ptm := it_mkLambda_or_LetIn predctx (preturn p) in All2 PCUICEquality.eq_decl_upto_names (pcontext p) (ind_predicate_context ci mdecl idecl) -> forall (i : nat) (cdecl : constructor_body) (br : branch term), declared_constructor Σ (ci, i) mdecl idecl cdecl -> wf_branch cdecl br -> let cstr_br_ctx := case_branch_context_nopars ci mdecl (puinst p) cdecl in let brctx' := map2 set_binder_name (forget_types (bcontext br)) cstr_br_ctx in let brctxty := case_branch_type ci mdecl idecl p br ptm i cdecl in [× wf_branch cdecl br, wf_localE Σ (Γ,,, (ind_params mdecl)@[puinst p],,, cstr_br_ctx), wf_localE Σ (Γ,,, (ind_params mdecl)@[puinst p],,, brctx'), wf_localE Σ (Γ,,, brctxty.1) & Σ;;; Γ,,, brctxty.1 |-E brctxty.2 : tSort ps] ;
  wf_case_predicate_context :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {ci : case_info} {p : predicate term} {args : list term}, declared_inductive Σ ci mdecl idecl -> isTypeE Σ Γ (mkApps (tInd ci (puinst p)) (pparams p ++ args)) -> wf_predicate mdecl idecl p -> let predctx := case_predicate_context ci mdecl idecl p in wf_localE Σ (Γ,,, predctx) ;
  wf_case_branches_types' :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {ci : case_info} {p : predicate term} (ps : sort) (args : list term) (brs : list (branch term)), declared_inductive Σ ci mdecl idecl -> isTypeE Σ Γ (mkApps (tInd ci (puinst p)) (pparams p ++ args)) -> wf_predicate mdecl idecl p -> let predctx := case_predicate_context ci mdecl idecl p in Σ;;; Γ,,, predctx |-E preturn p : tSort ps -> let ptm := it_mkLambda_or_LetIn predctx (preturn p) in wf_branches idecl brs -> All2 PCUICEquality.eq_decl_upto_names (pcontext p) (ind_predicate_context ci mdecl idecl) -> All2i (fun (i : nat) (cdecl : constructor_body) (br : branch term) => let cstr_br_ctx := case_branch_context_nopars ci mdecl (puinst p) cdecl in let brctx' := map2 set_binder_name (forget_types (bcontext br)) cstr_br_ctx in let brctxty := case_branch_type ci mdecl idecl p br ptm i cdecl in [× wf_branch cdecl br, wf_localE Σ (Γ,,, (ind_params mdecl)@[puinst p],,, cstr_br_ctx), wf_localE Σ (Γ,,, (ind_params mdecl)@[puinst p],,, brctx'), wf_localE Σ (Γ,,, brctxty.1) & Σ;;; Γ,,, brctxty.1 |-E brctxty.2 : tSort ps]) 0 (ind_ctors idecl) brs
}.

(** ** U (untyped facts whose base statement takes [wf Σ] only for closed bodies or universes; reduction is unchanged in E, so these are plumbing over [wfE_ClosedBodies], not research) *)
Class U_facts {cf : checker_flags} := {
  whnf_red_inv :
    forall {Σ : global_env_ext} (Γ : context) (t t' : term), wfE Σ -> whnf RedFlags.default Σ Γ t -> Σ ;;; Γ ⊢ t ⇝ t' -> whnf_red Σ Γ t t'
}.

(** ** T1 (subject reduction over [typingE], PCUICSR) *)
Class T1_facts {cf : checker_flags} := {
  isType_prim_shape_type :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {s : PrimitiveOps.prim_shape} {res : term}, wf_localE Σ Γ -> PCUICPrimOpType.prim_shape_type (retroknowledge Σ.1) s = Some res -> on_prim_op_result Σ s -> isTypeE Σ Γ res ;
  isType_red :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {T : term} {U : term}, isTypeE Σ Γ T -> PCUICReduction.red Σ Γ T U -> isTypeE Σ Γ U ;
  subject_reduction :
    forall (Σ : global_env_ext) (Γ : context) (t : term) (u : term) (T : term), wfE Σ -> Σ;;; Γ |-E t : T -> PCUICReduction.red Σ Γ t u -> Σ;;; Γ |-E u : T ;
  type_reduction_closed :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t : term} {A : term} {B : term}, Σ;;; Γ |-E t : A -> Σ ;;; Γ ⊢ A ⇝ B -> Σ;;; Γ |-E t : B
}.

(** ** T2a (validity over [typingE], PCUICValidity) *)
Class T2a_facts {cf : checker_flags} := {
  inversion_mkApps :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ.1} {Γ : context} {f : term} {u : list term} {T : term}, Σ;;; Γ |-E mkApps f u : T -> ∑ A : term, Σ;;; Γ |-E f : A × typing_spineE Σ Γ A u T ;
  validity :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t : term} {T : term}, Σ;;; Γ |-E t : T -> isTypeE Σ Γ T
}.

(** ** T6 (inversion and classification over [typingE], PCUICInversion, PCUICClassification) *)
Class T6_facts {cf : checker_flags} := {
  typing_spine_smash :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ.1) (Γ : context) (Δ : context) (T : term) (args : list term) (T' : term), typing_spineE Σ Γ (it_mkProd_or_LetIn Δ T) args T' -> typing_spineE Σ Γ (it_mkProd_or_LetIn (smash_context [] Δ) (expand_lets Δ T)) args T'
}.

(** ** T6, bidirectional soundness (BDToPCUIC over E) *)
Class T6BD_facts {cf : checker_flags} := {
  checking_typing :
    forall (Σ : global_env_ext) (Γ : context) (t : term) (T : term) (wfΣ : wfE Σ), wf_localE Σ Γ -> isTypeE Σ Γ T -> Σ;;; Γ |-E t ◃ T -> Σ;;; Γ |-E t : T ;
  ctx_inst_bd_typing :
    forall (Σ : global_env_ext) (Γ : list context_decl) (l : list term) (Δ : list context_decl) (wfΣ : wfE Σ), wf_localE Σ (Γ,,, Δ) -> PCUICTyping.ctx_inst (checkingE Σ) Γ l (List.rev Δ) -> ctx_instE Σ Γ l (List.rev Δ) ;
  infering_ind_typing :
    forall (Σ : global_env_ext) (Γ : context) (t : term) (ind : inductive) (u : Instance.t) (args : list term) (wfΣ : wfE Σ), wf_localE Σ Γ -> Σ;;; Γ |-E t ▹{ ind}(u, args) -> Σ;;; Γ |-E t : mkApps (tInd ind u) args ;
  infering_prod_typing :
    forall (Σ : global_env_ext) (Γ : context) (t : term) (na : aname) (A : term) (B : term) (wfΣ : wfE Σ), wf_localE Σ Γ -> Σ;;; Γ |-E t ▹Π (na, A, B) -> Σ;;; Γ |-E t : tProd na A B ;
  infering_sort_isTypeRel :
    forall (Σ : global_env_ext) (Γ : context) (t : term) (u : sort) (wfΣ : wfE Σ), wf_localE Σ Γ -> Σ;;; Γ |-E t ▹□ u -> isTypeRelE Σ Γ t (relevance_of_sort u) ;
  infering_sort_typing :
    forall (Σ : global_env_ext) (Γ : context) (t : term) (u : sort) (wfΣ : wfE Σ), wf_localE Σ Γ -> Σ;;; Γ |-E t ▹□ u -> Σ;;; Γ |-E t : tSort u ;
  infering_typing :
    forall (Σ : global_env_ext) (Γ : context) (t : term) (T : term) (wfΣ : wfE Σ), wf_localE Σ Γ -> Σ;;; Γ |-E t ▹ T -> Σ;;; Γ |-E t : T ;
  lift_sorting_lift_typing :
    forall (Σ : global_env_ext) (Γ : context) (j : judgment) (wfΣ : wfE Σ), wf_localE Σ Γ -> lift_sorting (checkingE Σ Γ) (infering_sortE Σ Γ) j -> lift_typing typingE Σ Γ j ;
  wf_local_bd_rel_typing :
    forall (Σ : global_env_ext) (Γ : context) (Γ' : context) (wfΣ : wfE Σ), wf_localE Σ Γ -> wf_local_bd_relE Σ Γ Γ' -> wf_local_relE Σ Γ Γ'
}.

(** ** T6, bidirectional uniqueness (BDUnique over E): inferred types are unique up to [red] *)
Class T6BDu_facts {cf : checker_flags} := {
  infering_checking :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : context} (wfΓ : wf_localE Σ Γ) {t : term} {T : term} {T' : term}, on_free_vars (shiftnP #|Γ| xpred0) T' -> Σ;;; Γ |-E t ▹ T -> Σ;;; Γ |-E t ◃ T' -> Σ ;;; Γ ⊢E T ≤ T' ;
  infering_ind_ind :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : context} (wfΓ : wf_localE Σ Γ) {t : term} {ind : inductive} {ind' : inductive} {u : Instance.t} {u' : Instance.t} {args : list term} {args' : list term}, Σ;;; Γ |-E t ▹{ ind}(u, args) -> Σ;;; Γ |-E t ▹{ ind'}(u', args') -> ∑ args'' : list term, [× ind = ind', u = u', red_terms Σ Γ args args'' & red_terms Σ Γ args' args''] ;
  infering_ind_infering :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : context} (wfΓ : wf_localE Σ Γ) {t : term} {ind : inductive} {u : Instance.t} {args : list term} {T : term}, Σ;;; Γ |-E t ▹{ ind}(u, args) -> Σ;;; Γ |-E t ▹ T -> ∑ args' : list term, Σ ;;; Γ ⊢ T ⇝ mkApps (tInd ind u) args' × red_terms Σ Γ args args' ;
  infering_prod_infering :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : context} (wfΓ : wf_localE Σ Γ) {t : term} {na : aname} {A : term} {B : term} {T : term}, Σ;;; Γ |-E t ▹Π (na, A, B) -> Σ;;; Γ |-E t ▹ T -> ∑ A' B' : term, [× Σ ;;; Γ ⊢ T ⇝ tProd na A' B', Σ ;;; Γ ⊢ A ⇝ A' & Σ ;;; Γ,, vass na A ⊢ B ⇝ B'] ;
  infering_prod_prod :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : context} (wfΓ : wf_localE Σ Γ) {t : term} {na : aname} {na' : aname} {A : term} {A' : term} {B : term} {B' : term}, Σ;;; Γ |-E t ▹Π (na, A, B) -> Σ;;; Γ |-E t ▹Π (na', A', B') -> ∑ A'' B'' : term, [× na = na', Σ ;;; Γ ⊢ A ⇝ A'', Σ ;;; Γ ⊢ A' ⇝ A'', Σ ;;; Γ,, vass na A ⊢ B ⇝ B'' & Σ ;;; Γ,, vass na A' ⊢ B' ⇝ B''] ;
  infering_sort_infering :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : context} {wfΓ : wf_localE Σ Γ} {t : term} {u : sort} {T : term}, Σ;;; Γ |-E t ▹□ u -> Σ;;; Γ |-E t ▹ T -> Σ ;;; Γ ⊢ T ⇝ tSort u ;
  infering_sort_sort :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : context} (wfΓ : wf_localE Σ Γ) {t : term} {u : sort} {u' : sort}, Σ;;; Γ |-E t ▹□ u -> Σ;;; Γ |-E t ▹□ u' -> u = u' ;
  infering_unique :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : context} (wfΓ : wf_localE Σ Γ) {t : term} {T : term} {T' : term}, Σ;;; Γ |-E t ▹ T -> Σ;;; Γ |-E t ▹ T' -> ∑ T'' : term, Σ ;;; Γ ⊢ T ⇝ T'' × Σ ;;; Γ ⊢ T' ⇝ T'' ;
  isTypeRel_unique :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : context} {T : term} {rel : relevance} {rel' : relevance}, isTypeRelE Σ Γ T rel -> isTypeRelE Σ Γ T rel' -> rel = rel'
}.

(** ** T6, bidirectional completeness (BDFromPCUIC over E). Its E proof needs T8 (a well-typed type E-convertible to a Π/Sort/Ind reduces to one).
    Together these six fields are as strong as typed T8 (plan risk rank 3): any forecast resting on this
    bundle assumes something as strong as T8; taking Refused_c removed T8 from the failure paths only.
    (Why, EtaHypAuditB hyp-audit-B.md §3.6: [typing_infering] implies typed T8-Prod and
    [typing_infering_sort] implies typed T8-Sort.)
    Uses (EtaK7, 2026-10-29): [PCUICTypeCheckerEta] uses these fields at 16 sites, 6 on error paths
    ([eapply absurd]) and 10 on SUCCESS paths (lambda/let binder types, case predicate and branch contexts and
    parameters, fix/cofix types and bodies, [branch_helper]), so they stay in the bundle for F2-early; the
    error paths are not turned into refusals (lane lead's decision). [PCUICSafeCheckerEta]: no use.
    PCUICSafeRetyping's 7 T6BDc uses: UNCLASSIFIED, erasure-only, off the F2-early path; to be classified
    when the fully-proved chain includes erasure. *)
Class T6BDc_facts {cf : checker_flags} := {
  ctx_inst_typing_bd :
    forall (Σ : global_env_ext) (Γ : context) (l : list term) (Δ : context) (wfΣ : wfE Σ), ctx_instE Σ Γ l Δ -> PCUICTyping.ctx_inst (checkingE Σ) Γ l Δ ;
  lift_typing_lift_sorting :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : context} {tm : option term} {ty : term} {rel : option relevance}, lift_typing typingE Σ Γ (Judge tm ty None rel) -> lift_sorting (checkingE Σ Γ) (infering_sortE Σ Γ) (Judge tm ty None rel) ;
  typing_checking :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t : term} {T : term}, Σ;;; Γ |-E t : T -> Σ;;; Γ |-E t ◃ T ;
  typing_infering :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t : term} {T : term}, Σ;;; Γ |-E t : T -> ∑ T' : term, Σ;;; Γ |-E t ▹ T' × Σ ;;; Γ ⊢E T' ≤ T ;
  typing_infering_sort :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t : term} {u : sort}, Σ;;; Γ |-E t : tSort u -> ∑ u' : sort, Σ;;; Γ |-E t ▹□ u' × leq_sort Σ u' u ;
  wf_local_rel_wf_local_bd :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : list context_decl} {Γ' : context}, wf_local_relE Σ Γ Γ' -> wf_local_bd_relE Σ Γ Γ'
}.

(** ** Derived: proved from base's E lemmas or from the class fields, under the base names *)

Section Derived.
  Context {cf : checker_flags}.

  (** From [PCUICTypingEtaInd], [PCUICClosedTypEta], [PCUICWeakeningEnvTypEta]. *)
  Lemma typing_wf_local {Σ : global_env_ext} {Γ : context} {t T : term} :
    Σ ;;; Γ |-E t : T -> wf_localE Σ Γ.
  Proof. exact typingE_wf_local. Qed.

  Lemma closed_wf_local {Σ : global_env_ext} {Γ : context} : wfE Σ.1 -> wf_localE Σ Γ -> closed_ctx Γ.
  Proof. exact closed_wf_localE. Qed.

  Lemma type_is_open_term {Σ : global_env_ext} {wfΣ : wfE Σ.1} {Γ : context} {t T : term} :
    Σ ;;; Γ |-E t : T -> is_open_term Γ T.
  Proof. exact type_is_open_termE. Qed.

  Lemma subject_is_open_term {Σ : global_env_ext} {wfΣ : wfE Σ.1} {Γ : context} {t T : term} :
    Σ ;;; Γ |-E t : T -> is_open_term Γ t.
  Proof. exact subject_is_open_termE. Qed.

  Lemma wf_local_closed_context {Σ : global_env_ext} {Γ : context} {wfΣ : wfE Σ} :
    wf_localE Σ Γ -> on_free_vars_ctx xpred0 Γ.
  Proof. exact wf_local_closed_contextE. Qed.

  Lemma declared_minductive_closed {Σ : global_env} {wfΣ : wfE Σ} {mdecl : mutual_inductive_body} {mind : kername} :
    declared_minductive Σ mind mdecl -> closed_inductive_decl mdecl.
  Proof. exact declared_minductive_closedE. Qed.

  Lemma on_declared_inductive {Σ : global_env} {ref : inductive} {mdecl : mutual_inductive_body}
    {idecl : one_inductive_body} {wfΣ : wfE Σ} :
    declared_inductive Σ ref mdecl idecl ->
    on_inductive cumulSpecE0 (lift_typing typingE) (Σ, ind_universes mdecl) (inductive_mind ref) mdecl ×
    on_ind_body cumulSpecE0 (lift_typing typingE) (Σ, ind_universes mdecl) (inductive_mind ref) mdecl
      (inductive_ind ref) idecl.
  Proof. exact on_declared_inductiveE. Qed.

  Definition isTypeRel_isType (Σ : global_env_ext) (Γ : context) (t : term) (r : relevance) :
    isTypeRelE Σ Γ t r -> isTypeE Σ Γ t := isTypeRelE_isTypeE Σ Γ t r.

  Lemma isType_wf_local {Σ : global_env_ext} {Γ : context} {T : term} : isTypeE Σ Γ T -> wf_localE Σ Γ.
  Proof. intros (_ & s & Hs & _). exact (typingE_wf_local Hs). Qed.

  Lemma isType_Sort {Σ : global_env_ext} {Γ : context} {s : sort} :
    wf_sort Σ s -> wf_localE Σ Γ -> isTypeE Σ Γ (tSort s).
  Proof. intros ws wfΓ. apply has_sort_isTypeE with (s := Sort.super s). now constructor. Qed.

  Lemma isType_is_open_term {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ : context) (T : term) :
    isTypeE Σ Γ T -> is_open_term Γ T.
  Proof. intros (_ & s & Hs & _). exact (subject_is_open_termE (wfΣ := wfΣ) Hs). Qed.

  Lemma isType_closed {Σ : global_env_ext} {wfΣ : wfE Σ.1} {Γ : context} {T : term} :
    isTypeE Σ Γ T -> closedn #|Γ| T.
  Proof. intros (_ & s & Hs & _). exact (subject_closedE Hs). Qed.

  Lemma subslet_length {Σ : global_env_ext} {Γ : context} {s : list term} {Δ : context} :
    subsletE Σ Γ s Δ -> #|s| = #|Δ|.
  Proof. induction 1; cbn; congruence. Qed.

  Lemma subslet_ass_tip {Σ : global_env_ext} {Γ : context} {na : aname} {t T : term} :
    Σ ;;; Γ |-E t : T -> subsletE Σ Γ [t] [vass na T].
  Proof. intros h. constructor; [constructor|]. now rewrite subst_empty. Qed.

  Lemma typing_spine_isType_dom {Σ : global_env_ext} {Γ : context} {T : term} {args : list term} {S : term} :
    typing_spineE Σ Γ T args S -> isTypeE Σ Γ T.
  Proof. now intros []. Qed.

  Lemma typing_spine_wf_local {Σ : global_env_ext} {Γ : context} {T : term} {args : list term} {T' : term} :
    typing_spineE Σ Γ T args T' -> wf_localE Σ Γ.
  Proof. intros h. exact (isType_wf_local (typing_spine_isType_dom h)). Qed.


  Lemma wt_closed_red_refl {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t T : term} :
    Σ ;;; Γ |-E t : T -> Σ ;;; Γ ⊢ t ⇝ t.
  Proof.
    intros h. apply into_closed_red; [reflexivity| |].
    - exact (wf_local_closed_contextE (typingE_wf_local h)).
    - exact (subject_is_open_termE h).
  Qed.

  (** From A1/A6/A7 ([PCUICWellScopedCumulativityEta], [PCUICEtaA6], [PCUICWsCumulEtaSubst]), whose
      lemmas take [ClosedBodies Σ]; [wfE Σ] gives it ([wfE_ClosedBodies]). *)
  Lemma ws_cumul_pb_Prod_Prod_inv {Σ : global_env_ext} {wfΣ : wfE Σ} {pb : conv_pb} {Γ : context}
    {na na' : aname} {dom dom' codom codom' : term} :
    Σ ;;; Γ ⊢E tProd na dom codom ≤[pb] tProd na' dom' codom' ->
    [× eq_binder_annot na na', Σ ;;; Γ ⊢E dom = dom' & Σ ;;; Γ,, vass na' dom' ⊢E codom ≤[pb] codom'].
  Proof. exact ws_cumul_pbE_Prod_Prod_inv. Qed.

  Lemma ws_cumul_pb_Prod_Sort_inv {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {s : sort} {na : aname}
    {dom codom : term} (pb : conv_pb) :
    Σ ;;; Γ ⊢E tProd na dom codom ≤[pb] tSort s -> False.
  Proof. exact (ws_cumul_pbE_Prod_Sort_inv pb). Qed.

  Lemma ws_cumul_pb_Sort_Prod_inv {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {s : sort} {na : aname}
    {dom codom : term} (pb : conv_pb) :
    Σ ;;; Γ ⊢E tSort s ≤[pb] tProd na dom codom -> False.
  Proof. exact (ws_cumul_pbE_Sort_Prod_inv pb). Qed.

  Lemma ws_cumul_pb_Sort_inv {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {s s' : sort} (pb : conv_pb) :
    Σ ;;; Γ ⊢E tSort s ≤[pb] tSort s' -> compare_sort Σ pb s s'.
  Proof. exact (ws_cumul_pbE_Sort_inv pb). Qed.

  Lemma red_ws_cumul_pb {Σ : global_env_ext} {wfΣ : wfE Σ} {pb : conv_pb} {Γ : context} {t u : term} :
    Σ ;;; Γ ⊢ t ⇝ u -> Σ ;;; Γ ⊢E t ≤[pb] u.
  Proof. exact red_ws_cumul_pbE. Qed.

  Lemma red_ws_cumul_pb_inv {Σ : global_env_ext} {wfΣ : wfE Σ} {pb : conv_pb} {Γ : context} {t u : term} :
    Σ ;;; Γ ⊢ t ⇝ u -> Σ ;;; Γ ⊢E u ≤[pb] t.
  Proof. exact red_ws_cumul_pbE_inv. Qed.

  Lemma red_conv {Σ : global_env_ext} {wfΣ : wfE Σ} {pb : conv_pb} {Γ : context} {t u : term} :
    Σ ;;; Γ ⊢ t ⇝ u -> Σ ;;; Γ ⊢E t ≤[pb] u.
  Proof. exact red_ws_cumul_pbE. Qed.

  Lemma ws_cumul_pb_refl {Σ : global_env_ext} {wfΣ : wfE Σ} {pb : conv_pb} {Γ : context} {t : term} :
    is_closed_context Γ -> is_open_term Γ t -> Σ ;;; Γ ⊢E t ≤[pb] t.
  Proof. exact ws_cumul_pbE_refl. Qed.

  Lemma ws_cumul_pb_eq_le {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t u : term} :
    Σ ;;; Γ ⊢E t = u -> Σ ;;; Γ ⊢E t ≤ u.
  Proof. exact ws_cumul_eq_pbE. Qed.

  Lemma isType_ws_cumul_pb_refl {Σ : global_env_ext} {wfΣ : wfE Σ} {pb : conv_pb} (Γ : context) (T : term) :
    isTypeE Σ Γ T -> Σ ;;; Γ ⊢E T ≤[pb] T.
  Proof.
    intros h. apply ws_cumul_pbE_refl.
    - exact (wf_local_closed_contextE (isType_wf_local h)).
    - exact (isType_is_open_term Γ T h).
  Qed.

  Lemma substitution0_ws_cumul_pb {Σ : global_env_ext} {wfΣ : wfE Σ} {pb : conv_pb} {Γ : context} {na : aname}
    {T t M N : term} :
    Σ ;;; Γ |-E t : T -> Σ ;;; Γ,, vass na T ⊢E M ≤[pb] N -> Σ ;;; Γ ⊢E M {0 := t} ≤[pb] N {0 := t}.
  Proof. intros ht h. exact (substitution0_ws_cumul_pbE (subject_is_open_termE ht) h). Qed.

  Lemma weakening_ws_cumul_pb {Σ : global_env_ext} {wfΣ : wfE Σ} {pb : conv_pb} {Γ Γ' Γ'' : context} {M N : term} :
    Σ ;;; Γ,,, Γ' ⊢E M ≤[pb] N -> on_free_vars_ctx xpred0 (Γ,,, Γ'') ->
    Σ ;;; Γ,,, Γ'',,, lift_context #|Γ''| 0 Γ' ⊢E lift #|Γ''| #|Γ'| M ≤[pb] lift #|Γ''| #|Γ'| N.
  Proof. exact weakening_ws_cumul_pbE. Qed.

  Lemma red_terms_ws_cumul_pb_terms {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {u u' : list term} :
    red_terms Σ Γ u u' -> ws_cumul_pbE_terms Σ Γ u u'.
  Proof. intros h. eapply All2_impl; [exact h|]. intros x y r. exact (red_ws_cumul_pbE r). Qed.

  (** The transitivity and symmetry of [ws_cumul_pbE_terms] (base gets them from [All2] over [ws_cumul_pb]). *)
  #[global] Instance ws_cumul_pbE_terms_trans {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} :
    CRelationClasses.Transitive (ws_cumul_pbE_terms Σ Γ).
  Proof.
    intros x y z h1 h2. unfold ws_cumul_pbE_terms in *.
    exact (All2_trans _ (@ws_cumul_pbE_trans _ Σ (wfE_ClosedBodies Σ) Conv Γ) x y z h1 h2).
  Qed.

  #[global] Instance ws_cumul_pbE_terms_sym {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} :
    CRelationClasses.Symmetric (ws_cumul_pbE_terms Σ Γ).
  Proof.
    intros x y h. unfold ws_cumul_pbE_terms in *.
    eapply All2_sym, All2_impl; [exact h|]. intros a b ab.
    exact (ws_cumul_pbE_sym_pb ab).
  Qed.

  (** Untyped reduction inversions: base's [_cb] versions over [ClosedBodies], with [wfE_ClosedBodies]. *)
  Lemma invert_red_prod {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {na : aname} {dom codom T : term} :
    Σ ;;; Γ ⊢ tProd na dom codom ⇝ T ->
    ∑ dom' codom' : term, [× T = tProd na dom' codom', Σ ;;; Γ ⊢ dom ⇝ dom' & Σ ;;; Γ,, vass na dom ⊢ codom ⇝ codom'].
  Proof. exact (invert_red_prod_cb (cbΣ := wfE_ClosedBodies Σ)). Qed.

  Lemma invert_red_mkApps_tInd {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {ind : inductive} {u : Instance.t}
    (args : list term) (c : term) :
    Σ ;;; Γ ⊢ mkApps (tInd ind u) args ⇝ c ->
    ∑ args' : list term, [× c = mkApps (tInd ind u) args', on_free_vars_ctx xpred0 Γ & red_terms Σ Γ args args'].
  Proof. exact (invert_red_mkApps_tInd_cb (cbΣ := wfE_ClosedBodies Σ) args c). Qed.

  Lemma red_it_mkProd_or_LetIn_mkApps_Ind {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {ctx : context}
    {ind : inductive} {u : Instance.t} {args : list term} {v : term} :
    Σ ;;; Γ ⊢ it_mkProd_or_LetIn ctx (mkApps (tInd ind u) args) ⇝ v ->
    ∑ (ctx' : context) (args' : list term), v = it_mkProd_or_LetIn ctx' (mkApps (tInd ind u) args').
  Proof. exact (PCUICInductives.red_it_mkProd_or_LetIn_mkApps_Ind_cb (wfΣ := wfE_ClosedBodies Σ)). Qed.

  (** [onNpars] of the declaration, from [on_declared_minductiveE]. *)
  Lemma declared_minductive_ind_npars {Σ : global_env} {wfΣ : wfE Σ} {mdecl : mutual_inductive_body} {ind : kername} :
    declared_minductive Σ ind mdecl -> ind_npars mdecl = context_assumptions (ind_params mdecl).
  Proof. intros h. pose proof (on_declared_minductiveE wfΣ h) as onm. now rewrite (onNpars onm). Qed.

  (** The specification side, for the [on_global_env cumulSpecE0 …] the environment checker builds. *)
  Lemma red_cumul {Σ : global_env_ext} {Γ : context} {t u : term} : red Σ Γ t u -> JoinE Σ Γ Cumul t u.
  Proof. exact (JoinE_red_l Σ Γ Cumul t u). Qed.

  Lemma type_Cumul' {Σ : global_env_ext} {Γ : context} {t : term} (T : term) {T' : term} :
    Σ ;;; Γ |-E t : T -> isTypeE Σ Γ T' -> cumulSpecE Σ Γ T T' -> Σ ;;; Γ |-E t : T'.
  Proof. intros ht (_ & s & hs & _) c. exact (typeE_Cumul _ _ _ _ _ _ ht hs c). Qed.

  Lemma eq_term_upto_univ_cumulSpec (Σ : global_env_ext) (Γ : context) {pb : conv_pb} (M N : term) :
    compare_term Σ Σ pb M N -> cumulSpecE0 Σ Γ pb M N.
  Proof. intros h. apply cumulSpec0_incl_E. exact (PCUICConversion.eq_term_upto_univ_cumulSpec Σ Γ M N h). Qed.

  Lemma cumulAlgo_cumulSpec {Σ : global_env_ext} {wfΣ : wfE Σ} {pb : conv_pb} (Γ : context) (M N : term) :
    Σ ;;; Γ ⊢E M ≤[pb] N -> cumulSpecE0 Σ Γ pb M N.
  Proof. intros h. exact (ws_cumul_pbE_forget_spec (wfΣ := wfE_ClosedBodies Σ) h). Qed.

  Lemma eq_context_cumul_Spec_rel (Σ : global_env_ext) (Ξ0 : list context_decl) (Γ Δ : context) :
    PCUICEquality.compare_context Σ Σ Cumul Γ Δ -> cumul_ctx_rel cumulSpecE0 Σ Ξ0 Γ Δ.
  Proof.
    intros h. pose proof (PCUICContextConversionTyp.eq_context_cumul_Spec_rel Σ Ξ0 Γ Δ h) as h'.
    eapply All2_fold_impl; [exact h'|]. intros ? ? ? ? c.
    destruct c; constructor; auto; now apply cumulSpec0_incl_E.
  Qed.

  (** From the T2a fields. *)
  Lemma validity_wf {hT2a : T2a_facts} (Σ : global_env_ext) (hΣ : wfE Σ) {Γ : context} {t T : term} :
    ∥ Σ ;;; Γ |-E t : T ∥ -> welltypedE Σ Γ T.
  Proof. intros [h]. exact (isTypeE_welltypedE (validity (wfΣ := hΣ) h)). Qed.

  Lemma wat_welltyped (Σ : global_env_ext) {Γ : context} {T : term} : ∥ isTypeE Σ Γ T ∥ -> welltypedE Σ Γ T.
  Proof. intros [h]. exact (isTypeE_welltypedE h). Qed.

End Derived.

(** ** The premise the copies take

  One implicit Prop premise [{EF : EtaFacts}], found by typeclass resolution, so that every function of
  the copies has the same signature whatever facts its obligations use, and extraction erases it. Each
  field is the squash of one row's class; when a row lands, its field is proved by [sq] of the row's
  instance. *)
(** [ws_cumul_ctx_pb_rel_app] over E: formerly the only field of class A (the A rows); PROVED here from
    [PCUICWsCumulEtaCtx.ws_cumul_ctx_pbE_rel_app] (P3, ArityLane, [frac/eta] @ [d8120081]), which needs no
    [wf] premise. The statement is the former field's, unchanged ([wfΣ] is unused). *)
Lemma ws_cumul_ctx_pb_rel_app {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {pb : conv_pb}
  {Γ Δ Δ' : list context_decl} :
  ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ' <~> ws_cumul_ctx_pbE pb Σ (Γ,,, Δ) (Γ,,, Δ').
Proof. exact ws_cumul_ctx_pbE_rel_app. Qed.

Class EtaFacts {cf : checker_flags} : Prop := {
  eta_T0 : ∥ T0_facts ∥ ;
  eta_U : ∥ U_facts ∥ ;
  eta_T1 : ∥ T1_facts ∥ ;
  eta_T2a : ∥ T2a_facts ∥ ;
  eta_T6 : ∥ T6_facts ∥ ;
  eta_T6BD : ∥ T6BD_facts ∥ ;
  eta_T6BDu : ∥ T6BDu_facts ∥ ;
  eta_T6BDc : ∥ T6BDc_facts ∥ }.

(** [sq] of the copies: first open the premise, so that the rows' classes are in the context (as
    instances) for the base proof scripts. It projects the fields once (a section variable [EtaF] cannot be
    destructed away, so a [repeat destruct] would loop) and does nothing if they are already there. *)
Ltac unpack_eta_facts :=
  lazymatch goal with
  | _ : T0_facts |- _ => idtac
  | _ : ∥ T0_facts ∥ |- _ => idtac
  | EF : EtaFacts |- _ =>
      (* fixed, unusual names, so that the base proof scripts' generated names (H, H0, X1, ...) are unchanged *)
      pose proof (@eta_T0 _ EF) as etaf_T0; pose proof (@eta_U _ EF) as etaf_U;
      pose proof (@eta_T1 _ EF) as etaf_T1; pose proof (@eta_T2a _ EF) as etaf_T2a;
      pose proof (@eta_T6 _ EF) as etaf_T6; pose proof (@eta_T6BD _ EF) as etaf_T6BD;
      pose proof (@eta_T6BDu _ EF) as etaf_T6BDu; pose proof (@eta_T6BDc _ EF) as etaf_T6BDc
  | _ => idtac
  end.
Ltac sq := unpack_eta_facts; MRSquash.sq.
(** Open the facts without touching the goal: project them, and unsquash only them when the goal is a Prop
    (in a Type goal they stay squashed and nothing else changes). For proofs that use a fact before any
    [sq]. *)
Ltac open_eta_facts :=
  unpack_eta_facts;
  repeat match goal with
  | H : ∥ ?C ∥ |- _ =>
      lazymatch C with
      | @T0_facts _ => idtac | @U_facts _ => idtac | @T1_facts _ => idtac | @T2a_facts _ => idtac
      | @T6_facts _ => idtac | @T6BD_facts _ => idtac | @T6BDu_facts _ => idtac | @T6BDc_facts _ => idtac
      end;
      case H; clear H; intro H
  end.

(** ** Derived, second part: facts that are proved here from the classes or from facts above *)

(** The E copy of base [ShapeCheck] ([PCUICFixWitness.v:131-140]): its reduction law takes [wfE] (base's
    takes [wf], which [wfE] does not give). STATEMENT CHANGE (EtaK7, 2026-10-29, found by EtaHypAuditA):
    [mfix_body_on_red_unique] is stated over [ShapeCheckE] and is now PROVED below (it was a T0 field
    over base [ShapeCheck], whose law the E environment cannot meet). *)
Class ShapeCheckE {cf : checker_flags} (check : def term -> option kername) : Prop := {
  shapeE_check_dbody d bo :
    check {| dname := d.(dname); dtype := d.(dtype); dbody := bo; rarg := d.(rarg) |} = check d;
  shapeE_check_eq_term_upto {Σ cmp_universe cmp_sort} d t u :
    eq_term_upto_univ Σ cmp_universe cmp_sort Conv t u ->
    check (def_with_type d t) = check (def_with_type d u);
  shapeE_check_closed_red {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ d ty v mind} :
    Σ ;;; Γ ⊢ ty ⇝ v ->
    check (def_with_type d ty) = Some mind ->
    check (def_with_type d v) = Some mind }.

Derive Signature for typingE.

Section DerivedTwo.
  Context {cf : checker_flags}.

  (** STATEMENT CHANGE (EtaK7, 2026-10-29, found by EtaHypAuditA): base [type_ws_cumul_pb] has no [wf]
      premise (its proof uses none, [PCUICArities.v:228]); over E the only route from [ws_cumul_pbE] to the
      specification [cumulSpecE0] ([I5_join_to_spec]) needs [ClosedBodies], so the E form takes
      [{wfΣ : wfE Σ}]. With it the fact is PROVED here (it was a T0 hypothesis). Every use has [wfE]. *)
  Lemma type_ws_cumul_pb {Σ : global_env_ext} {wfΣ : wfE Σ} {pb : conv_pb} {Γ : context} {t : term} (T : term)
    {U : term} :
    Σ ;;; Γ |-E t : T -> isTypeE Σ Γ U -> Σ ;;; Γ ⊢E T ≤[pb] U -> Σ ;;; Γ |-E t : U.
  Proof.
    intros ht hU c.
    have c' : Σ ;;; Γ ⊢E T ≤ U.
    { destruct pb; [exact (ws_cumul_eq_pbE c)|exact c]. }
    exact (type_Cumul' T ht hU (cumulAlgo_cumulSpec Γ T U c')).
  Qed.

  (** *** Eight former fields, PROVABLE NOW (EtaHypAuditB, hyp-audit-B.md §3.1-3.3, §3.7) *)

  Lemma typing_ws_cumul_pbE {Σ : global_env_ext} {wfΣ : wfE Σ} {le : conv_pb} {Γ : context} {t T : term} :
    Σ ;;; Γ |-E t : T -> Σ ;;; Γ ⊢E T ≤[le] T.
  Proof.
    intros ht. apply ws_cumul_pbE_refl.
    - exact (wf_local_closed_contextE (typingE_wf_local ht)).
    - exact (type_is_open_termE ht).
  Qed.

  Lemma cumul_stepE {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t A B X : term} {s : sort} :
    Σ ;;; Γ |-E t : A -> Σ ;;; Γ |-E B : tSort s -> cumulSpecE Σ Γ A B ->
    Σ ;;; Γ ⊢E X ≤ A -> Σ ;;; Γ ⊢E X ≤ B.
  Proof.
    intros ht hB c hX.
    refine (@ws_cumul_pbE_trans _ Σ (wfE_ClosedBodies Σ) Cumul Γ _ _ _ hX _).
    apply (into_ws_cumul_pbE_spec (wfΣ := wfE_ClosedBodies Σ)); [exact c| | |].
    - exact (wf_local_closed_contextE (typingE_wf_local ht)).
    - exact (type_is_open_termE ht).
    - exact (subject_is_open_termE hB).
  Qed.

  Lemma inversion_Rel (Σ : global_env_ext) (wfΣ : wfE Σ) {Γ : context} {n : nat} {T : term} :
    Σ ;;; Γ |-E tRel n : T ->
    ∑ decl : context_decl, wf_localE Σ Γ × nth_error Γ n = Some decl × Σ ;;; Γ ⊢E lift0 (S n) (decl_type decl) ≤ T.
  Proof.
    intros h. remember (tRel n) as t0 eqn:heqt. revert n heqt.
    induction h; intros n' heqt; try discriminate heqt.
    - injection heqt; intros; subst. exists decl. split; [assumption|split; [assumption|]].
      eapply typing_ws_cumul_pbE. econstructor; eassumption.
    - match goal with IH : forall n0, _ = tRel n0 -> _ |- _ =>
        destruct (IH _ heqt) as [decl [wfl [hn cc]]] end.
      exists decl. split; [assumption|split; [assumption|]].
      refine (cumul_stepE _ _ _ cc); eassumption.
  Qed.

  Lemma inversion_Sort (Σ : global_env_ext) (wfΣ : wfE Σ) {Γ : context} {s : sort} {T : term} :
    Σ ;;; Γ |-E tSort s : T -> wf_localE Σ Γ × wf_sort Σ s × Σ ;;; Γ ⊢E tSort (Sort.super s) ≤ T.
  Proof.
    intros h. remember (tSort s) as t0 eqn:heqt. revert s heqt.
    induction h; intros s' heqt; try discriminate heqt.
    - injection heqt; intros; subst. split; [assumption|split; [assumption|]].
      eapply typing_ws_cumul_pbE. econstructor; eassumption.
    - match goal with IH : forall s0, _ = tSort s0 -> _ |- _ =>
        destruct (IH _ heqt) as [wfl [ws cc]] end.
      split; [assumption|split; [assumption|]].
      refine (cumul_stepE _ _ _ cc); eassumption.
  Qed.

  Lemma inversion_Prod (Σ : global_env_ext) (wfΣ : wfE Σ) {Γ : context} {na : aname} {A B T : term} :
    Σ ;;; Γ |-E tProd na A B : T ->
    ∑ s1 s2 : sort, lift_typing typingE Σ Γ (j_vass_s na A s1) × Σ ;;; Γ ,, vass na A |-E B : tSort s2 ×
      Σ ;;; Γ ⊢E tSort (Sort.sort_of_product s1 s2) ≤ T.
  Proof.
    intros h. remember (tProd na A B) as t0 eqn:heqt. revert na A B heqt.
    induction h; intros na' A' B' heqt; try discriminate heqt.
    - injection heqt; intros; subst. exists s1, s2. split; [assumption|split; [assumption|]].
      eapply typing_ws_cumul_pbE. econstructor; eassumption.
    - match goal with IH : forall na0 A0 B0, _ = tProd na0 A0 B0 -> _ |- _ =>
        destruct (IH _ _ _ heqt) as [s1 [s2 [hA [hB cc]]]] end.
      exists s1, s2. split; [assumption|split; [assumption|]].
      refine (cumul_stepE _ _ _ cc); eassumption.
  Qed.

  Lemma inversion_LetIn (Σ : global_env_ext) (wfΣ : wfE Σ) {Γ : context} {na : aname} {b B t T : term} :
    Σ ;;; Γ |-E tLetIn na b B t : T ->
    ∑ A : term, lift_typing typingE Σ Γ (j_vdef na b B) × Σ ;;; Γ ,, vdef na b B |-E t : A ×
      Σ ;;; Γ ⊢E tLetIn na b B A ≤ T.
  Proof.
    intros h. remember (tLetIn na b B t) as t0 eqn:heqt. revert na b B t heqt.
    induction h; intros na' b' B' t' heqt; try discriminate heqt.
    - injection heqt; intros; subst. exists A. split; [assumption|split; [assumption|]].
      eapply typing_ws_cumul_pbE. econstructor; eassumption.
    - match goal with IH : forall na0 b0 B0 t1, _ = tLetIn na0 b0 B0 t1 -> _ |- _ =>
        destruct (IH _ _ _ _ heqt) as [A' [hb [ht cc]]] end.
      exists A'. split; [assumption|split; [assumption|]].
      refine (cumul_stepE _ _ _ cc); eassumption.
  Qed.

  Lemma inversion_Const (Σ : global_env_ext) (wfΣ : wfE Σ) {Γ : context} {c : kername} {u : Instance.t} {T : term} :
    Σ ;;; Γ |-E tConst c u : T ->
    ∑ decl : constant_body, wf_localE Σ Γ × declared_constant Σ c decl ×
      consistent_instance_ext Σ (cst_universes decl) u × Σ ;;; Γ ⊢E (cst_type decl)@[u] ≤ T.
  Proof.
    intros h. remember (tConst c u) as t0 eqn:heqt. revert c u heqt.
    induction h; intros c' u' heqt; try discriminate heqt.
    - injection heqt; intros; subst. exists decl. split; [assumption|split; [assumption|split; [assumption|]]].
      eapply typing_ws_cumul_pbE. econstructor; eassumption.
    - match goal with IH : forall c0 u0, _ = tConst c0 u0 -> _ |- _ =>
        destruct (IH _ _ heqt) as [decl [wfl [hd [hu cc]]]] end.
      exists decl. split; [assumption|split; [assumption|split; [assumption|]]].
      refine (cumul_stepE _ _ _ cc); eassumption.
  Qed.

  Lemma isType_Sort_inv {Σ : global_env_ext} {Γ : context} {s : sort} :
    wfE Σ -> isTypeE Σ Γ (tSort s) -> wf_sort Σ s.
  Proof.
    intros wfΣ (_ & s' & hs & _). exact (fst (snd (inversion_Sort Σ wfΣ hs))).
  Qed.

  Lemma type_Cumul_alt {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ : context) (t T T' : term) :
    Σ ;;; Γ |-E t : T -> isTypeE Σ Γ T' -> JoinE Σ Γ Cumul T T' -> Σ ;;; Γ |-E t : T'.
  Proof.
    intros ht (_ & s & hT' & _) j.
    refine (typeE_Cumul _ _ _ _ _ _ ht hT' _).
    exact (I5_join_to_spec Σ (wfE_ClosedBodies Σ) Γ Cumul T T'
             (wf_local_closed_contextE (typingE_wf_local ht)) (type_is_open_termE ht)
             (subject_is_open_termE hT') j).
  Qed.
End DerivedTwo.

(** ** PROVED rows (integration of EtaHypProve's [PCUICTypingEtaHypsProved.v] @ [29c23129], K7 sections)

  47 former class fields ([T0_facts] 37, [U_facts] 8, [T1_facts] 1, [T6BD_facts] 1) are proved here. Their proofs
  are EtaHypProve's, copied unchanged (comments included) from its K7 sections; its [_fits] identity checks are
  replaced by the lemmas at the end of this block, which restate each former field verbatim under its name
  (the build checks that [<field>_proved] proves that text). Not copied: its REDUCE, EtaConv, EtaPosK4 and
  "Duplicate GENUINE" sections (other owners) and [ctf_wf_universes_proved] (EtaConv's row). Their imports are at the top of
  this file (as in EtaHypProve's file, this file's own names come after them and so take precedence). *)


(** ** K7 ([PCUICTypingEtaHyps]): the exact twins of [Typing/PCUICWeakeningTypEta] *)

Lemma All_mfix_wf_proved {cf : checker_flags} :
    forall (Σ : global_env × universes_decl) (Γ : context) (mfix : list (def term)), wfE Σ.1 -> wf_localE Σ Γ -> All (fun d : def term => isTypeRelE Σ Γ (dtype d) (binder_relevance (dname d))) mfix -> wf_localE Σ (Γ,,, fix_context mfix).
Proof. intros Σ Γ mfix. exact (All_mfix_wfE Σ Γ mfix). Qed.

Lemma isTypeRel_lift_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {n : nat} {Γ : list context_decl} {ty : term} {r : relevance} (isdecl : n <= #|Γ|), wfE Σ -> wf_localE Σ Γ -> isTypeRelE Σ (skipn n Γ) ty r -> isTypeRelE Σ Γ (lift0 n ty) r.
Proof. intros Σ n Γ ty r isdecl. exact (isTypeRel_liftE isdecl). Qed.

Lemma isType_lift_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {n : nat} {Γ : list context_decl} {ty : term} (isdecl : n <= #|Γ|), wfE Σ -> wf_localE Σ Γ -> isTypeE Σ (skipn n Γ) ty -> isTypeE Σ Γ (lift0 n ty).
Proof. intros Σ n Γ ty isdecl. exact (isType_liftE isdecl). Qed.

Lemma weaken_ctx_proved {cf : checker_flags} :
    forall {Σ : global_env × universes_decl} {Γ : context} {t : term} {T : term} (Δ : context), wfE Σ.1 -> wf_localE Σ Δ -> Σ;;; Γ |-E t : T -> Σ;;; Δ,,, Γ |-E t : T.
Proof. intros Σ Γ t T Δ. exact (weaken_ctxE Δ). Qed.

Lemma weaken_wf_local_proved {cf : checker_flags} :
    forall {Σ : global_env × universes_decl} {Δ : context} (Γ : context), wfE Σ.1 -> wf_localE Σ Γ -> wf_localE Σ Δ -> wf_localE Σ (Γ,,, Δ).
Proof. intros Σ Δ Γ. exact (weaken_wf_localE Γ). Qed.

Lemma weakening_wf_local_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {Γ' : list context_decl} {Γ'' : list context_decl}, wf_localE Σ (Γ,,, Γ') -> wf_localE Σ (Γ,,, Γ'') -> wf_localE Σ (Γ,,, Γ'',,, lift_context #|Γ''| 0 Γ').
Proof. intros Σ wfΣ Γ Γ' Γ''. exact (weakening_wf_localE (wfΣ := wfΣ)). Qed.

Lemma isType_weaken_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {T : term}, wf_localE Σ Γ -> isTypeE Σ [] T -> isTypeE Σ Γ T.
Proof.
  intros Σ wfΣ Γ T wfΓ h. exact (lift_typing_weaken_ctxE Σ [] Γ _ wfΣ wfΓ h).
Qed.

Lemma wf_rel_weak_proved {cf : checker_flags} :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ) (Γ : context), wf_localE Σ Γ -> forall (Γ' : context), wf_localE Σ Γ' -> wf_local_relE Σ Γ Γ'.
Proof.
  intros Σ wfΣ Γ wfΓ Γ' wfΓ'.
  induction wfΓ' as [|Δ na t wfΔ IH h|Δ na b t wfΔ IH h].
  - exact All_local_rel_nil.
  - apply All_local_rel_abs; [exact IH|].
    exact (lift_typing_weaken_ctxE Σ Δ Γ _ wfΣ wfΓ h).
  - apply All_local_rel_def; [exact IH|].
    exact (lift_typing_weaken_ctxE Σ Δ Γ _ wfΣ wfΓ h).
Qed.

(** ** K7: inversions of products *)

Lemma isType_tProd_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {na : aname} {A : term} {B : term}, isTypeE Σ Γ (tProd na A B) <~> isTypeRelE Σ Γ A (binder_relevance na) × isTypeE Σ (Γ,, vass na A) B.
Proof.
  intros Σ wfΣ Γ na A B. split; intro HH.
  - destruct HH as (_ & s & H & _).
    destruct (inversion_Prod Σ wfΣ H) as [s1 [s2 [HA [HB _]]]].
    apply lift_sorting_forget_univ in HA.
    split; [exact HA|exact (has_sort_isTypeE _ HB)].
  - destruct HH as [HA HB].
    pose proof (lift_sorting_extract HA).
    destruct HB as (_ & sB & HB & _).
    eapply has_sort_isTypeE.
    eapply typeE_Prod; eassumption.
Qed.

Lemma welltyped_prod_codomain_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {na : aname} {A : term} {B : term}, welltypedE Σ Γ (tProd na A B) -> welltypedE Σ (Γ,, vass na A) B.
Proof.
  intros Σ wfΣ Γ na A B [T hT].
  destruct (inversion_Prod Σ wfΣ hT) as (s1 & s2 & _ & hB & _).
  econstructor. exact hB.
Qed.

(** [PCUICArities.it_mkProd_or_LetIn_wf_local] over [typingE]. *)
Lemma hyp_it_mkProd_or_LetIn_wf_local {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Δ T U} :
  Σ ;;; Γ |-E it_mkProd_or_LetIn Δ T : U -> wf_localE Σ (Γ ,,, Δ).
Proof.
  move: Γ T U. induction Δ as [|d Δ IHΔ] using rev_ind => Γ T U.
  - cbn. intros h. exact (typingE_wf_local h).
  - rewrite it_mkProd_or_LetIn_app. destruct d as [na [b|] ty]; cbn; move=> H.
    + destruct (inversion_LetIn Σ wfΣ H) as (A & _ & HT & _).
      apply IHΔ in HT. rewrite /app_context -app_assoc. exact HT.
    + destruct (inversion_Prod Σ wfΣ H) as (s1 & s2 & _ & HT & _).
      apply IHΔ in HT. rewrite /app_context -app_assoc. exact HT.
Qed.

Lemma isType_it_mkProd_or_LetIn_wf_local_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {Δ : context} {T : term}, isTypeE Σ Γ (it_mkProd_or_LetIn Δ T) -> wf_localE Σ (Γ,,, Δ).
Proof.
  intros Σ wfΣ Γ Δ T (_ & s & Hs & _). exact (hyp_it_mkProd_or_LetIn_wf_local (wfΣ := wfΣ) Hs).
Qed.

(** ** K7: structural spine and context facts (T0 rows 4, 5, 23, 24, 25, 26, 29) and T1 [isType_prim_arg_types]
    (helpers [stc_*]) *)

(** [PCUICSpine.ctx_inst_subst_length] at [typingE]. *)
Lemma stc_ctx_inst_subE_length {cf : checker_flags} {Σ : global_env_ext} {Γ} {Δ : context} {args}
  (c : ctx_instE Σ Γ args Δ) :
  #|ctx_inst_subE c| = #|Δ|.
Proof.
  induction c; simpl; auto; try lia;
  rewrite length_app IHc subst_telescope_length /=; lia.
Qed.

(** [PCUICSpine.ctx_inst_sub_spec] at [typingE]. *)
Lemma stc_ctx_inst_subE_spec {cf : checker_flags} {Σ : global_env_ext} {Γ Δ args}
  (c : ctx_instE Σ Γ args Δ) :
  make_context_subst Δ args [] = Some (ctx_inst_subE c).
Proof.
  induction c; simpl; auto.
  now apply (make_context_subst_tele [] [i]) in IHc.
  apply (make_context_subst_tele [] [b]) in IHc.
  now rewrite subst_empty.
Qed.

(** [PCUICSpine.ctx_inst_app] at [typingE]. *)
Lemma stc_ctx_instE_app {cf : checker_flags} {Σ : global_env_ext} {Γ} {Δ : context} {Δ' args args'}
  (dom : ctx_instE Σ Γ args Δ) :
  ctx_instE Σ Γ args' (subst_telescope (ctx_inst_subE dom) 0 Δ') ->
  ctx_instE Σ Γ (args ++ args') (Δ ++ Δ').
Proof.
  induction dom in args', Δ' |- *; simpl.
  - now rewrite subst_telescope_empty.
  - rewrite subst_app_telescope /= stc_ctx_inst_subE_length /= subst_telescope_length Nat.add_0_r /=.
    move/IHdom => IH.
    constructor => //.
    now rewrite subst_telescope_app Nat.add_0_r.
  - rewrite subst_app_telescope /= stc_ctx_inst_subE_length /= subst_telescope_length Nat.add_0_r /=.
    move/IHdom => IH.
    constructor => //.
    now rewrite subst_telescope_app Nat.add_0_r.
Qed.

(** Row 26. Port of [PCUICSpine.spine_subst_ctx_inst] (syntactic in the typing judgment). *)
Lemma spine_subst_ctx_inst_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {Γ : context} {Δ : context} {args : list term} {s : list term}, spine_substE Σ Γ args s Δ -> ctx_instE Σ Γ args (List.rev Δ).
Proof.
  intros Σ Γ Δ args s [wfd _ cs subsl].
  induction subsl in args, cs |- *.
  - DepElim.depelim cs. constructor.
  - DepElim.depelim cs.
    specialize (IHsubsl _ cs).
    unshelve eapply stc_ctx_instE_app; tea. cbn.
    rewrite /map_decl /=. repeat constructor.
    pose proof (stc_ctx_inst_subE_spec IHsubsl) as msub.
    eapply make_context_subst_spec in msub.
    rewrite List.rev_involutive in msub.
    now pose proof (context_subst_fun cs msub); subst s.
  - DepElim.depelim cs.
    specialize (IHsubsl _ cs). cbn.
    rewrite -(app_nil_r args).
    unshelve eapply stc_ctx_instE_app; tea. cbn.
    rewrite /map_decl /=. repeat constructor.
Qed.


(** Row 29. Only the [context_subst] component of the spine is used (as in [PCUICSR.spine_subst_inst_subst]). *)
Lemma spine_subst_inst_subst_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {Γ : context} {inst : list term} {s : list term} {Δ : context} {Δ' : context}, spine_substE Σ Γ inst s Δ -> subst_context s 0 Δ' = subst_context (List.rev inst) 0 (expand_lets_ctx Δ Δ').
Proof.
  intros Σ Γ inst s Δ Δ' sp.
  have cs := inst_ctx_substE sp.
  have hl := context_subst_length2 cs.
  rewrite (context_subst_subst_extended_subst _ _ _ cs).
  rewrite /expand_lets_ctx /expand_lets_k_ctx /=.
  rewrite PCUICSR.subst_context_subst_context.
  rewrite extended_subst_length Nat.add_0_l.
  rewrite PCUICInductives.subst_context_lift_context_cancel //.
  now rewrite List.length_rev hl.
Qed.


(** Row 4. Port of [PCUICSpine.ctx_inst_open_terms] with [subject_is_open_termE]. *)
Lemma ctx_inst_open_terms_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ : context) (args : list term) (Δ : context), ctx_instE Σ Γ args Δ -> All (fun t : term => on_free_vars (shiftnP #|Γ| xpred0) t) args.
Proof.
  intros Σ wfΣ Γ args Δ c.
  induction c.
  - constructor.
  - constructor; [|exact IHc].
    match goal with H : typingE _ _ _ _ |- _ => exact (subject_is_open_termE (wfΣ := wfΣ) H) end.
  - exact IHc.
Qed.


(** [PCUICSpine.ctx_inst_smash_acc] at [typingE] (its proof is [Proof using Type]: no typing fact used). *)
Lemma stc_ctx_instE_smash_acc {cf : checker_flags} {Σ : global_env_ext} {Γ i Δ} :
  ctx_instE Σ Γ i Δ <~>
  ctx_instE Σ Γ i (List.rev (smash_context [] (List.rev Δ))).
Proof.
  split.
  - induction 1.
    + constructor.
    + simpl.
      rewrite smash_context_app_ass. len.
      rewrite List.rev_app_distr /=.
      constructor. auto.
      rewrite subst_telescope_subst_context.
      rewrite -smash_context_subst /=; len.
      now rewrite subst_context_rev_subst_telescope.
    + simpl. rewrite smash_context_app_def.
      now rewrite subst_context_rev_subst_telescope.
  - induction Δ using PCUICInduction.ctx_length_ind in i |- *; simpl; auto.
    destruct d as [na [b|] ty] => /=.
    * rewrite smash_context_app_def /=.
      rewrite subst_context_rev_subst_telescope.
      intros ctxi. constructor.
      apply X => //. now rewrite subst_telescope_length //.
    * rewrite smash_context_app_ass List.rev_app_distr /=.
      intros ctxi; DepElim.depelim ctxi.
      constructor => //.
      apply X. rewrite subst_telescope_length //.
      rewrite subst_telescope_subst_context in ctxi.
      rewrite -(smash_context_subst []) in ctxi.
      now rewrite subst_context_rev_subst_telescope in ctxi.
Qed.

(** Row 5. Port of [PCUICSpine.ctx_inst_smash]. *)
Lemma ctx_inst_smash_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {Γ : context} {i : list term} {Δ : list context_decl}, ctx_instE Σ Γ i (List.rev Δ) <~> ctx_instE Σ Γ i (List.rev (smash_context [] Δ)).
Proof.
  intros Σ Γ i Δ. split; intros X.
  - apply (fst stc_ctx_instE_smash_acc) in X. now rewrite List.rev_involutive in X.
  - apply (snd stc_ctx_instE_smash_acc). now rewrite List.rev_involutive.
Qed.


(** Row 23. Port of [PCUICContexts.sorts_local_ctx_wf_local]. *)
Lemma sorts_local_ctx_wf_local_proved {cf : checker_flags} :
    forall (Σ : global_env_ext) (Γ : context) (Δ : context) (s : list sort), wf_localE Σ Γ -> sorts_local_ctx (lift_typing typingE) Σ Γ Δ s -> wf_localE Σ (Γ,,, Δ).
Proof.
  intros Σ Γ Δ. induction Δ as [|[na [b|] ty] Δ IH]; intros s wfΓ wfctx.
  - exact wfΓ.
  - cbn in wfctx. destruct wfctx as [h1 h2].
    constructor; [exact (IH _ wfΓ h1)|exact h2].
  - destruct s as [|u s]; cbn in wfctx; [destruct wfctx|].
    destruct wfctx as [h1 h2].
    constructor; [exact (IH _ wfΓ h1)|].
    exact (lift_sorting_forget_univ h2).
Qed.


(** Row 24. Port of [PCUICContexts.type_local_ctx_wf_local]. *)
Lemma type_local_ctx_wf_local_proved {cf : checker_flags} :
    forall (Σ : global_env_ext) (Γ : context) (Δ : context) (s : sort), wf_localE Σ Γ -> type_local_ctx (lift_typing typingE) Σ Γ Δ s -> wf_localE Σ (Γ,,, Δ).
Proof.
  intros Σ Γ Δ s wfΓ. induction Δ as [|[na [b|] ty] Δ IH]; intros wfctx.
  - exact wfΓ.
  - cbn in wfctx. destruct wfctx as [h1 h2].
    constructor; [exact (IH h1)|exact h2].
  - cbn in wfctx. destruct wfctx as [h1 h2].
    constructor; [exact (IH h1)|].
    exact (lift_sorting_forget_univ h2).
Qed.


(** [PCUICSpine.subslet_app] at [typingE]. *)
Lemma stc_subsletE_app {cf : checker_flags} (Σ : global_env_ext) Γ s s' Δ Δ' :
  subsletE Σ Γ s (subst_context s' 0 Δ) ->
  subsletE Σ Γ s' Δ' ->
  subsletE Σ Γ (s ++ s') (Δ' ,,, Δ).
Proof.
  induction Δ in s, s', Δ' |- *; simpl; auto; move=> sub'.
  - DepElim.depelim sub'. auto.
  - rewrite subst_context_snoc in sub' => sub''.
    move:(subslet_length sub') => /=.
    rewrite /snoc /= subst_context_length /= => Hlen.
    destruct a as [na [b|] ty].
    * DepElim.depelim sub'; simpl in t0, Hlen.
      rewrite -subst_app_simpl' /=. lia.
      constructor. eauto.
      now rewrite - !subst_app_simpl' in t0; try lia.
    * rewrite /subst_decl /map_decl /snoc /= in sub'.
      DepElim.depelim sub'; simpl in Hlen.
      rewrite - !subst_app_simpl' in t0; try lia.
      simpl; constructor; eauto.
Qed.

(** Row 25. Port of [PCUICSpine.spine_subst_app]. *)
Lemma spine_subst_app_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {Γ : list context_decl} {Δ : context} {Δ' : list context_decl} {inst : list term} {inst' : list term} {insts : list term}, #|inst| = context_assumptions Δ -> wf_localE Σ (Γ,,, Δ,,, Δ') -> spine_substE Σ Γ inst (skipn #|Δ'| insts) Δ -> spine_substE Σ Γ inst' (firstn #|Δ'| insts) (subst_context (skipn #|Δ'| insts) 0 Δ') -> spine_substE Σ Γ (inst ++ inst') insts (Δ,,, Δ').
Proof.
  intros Σ Γ Δ Δ' inst inst' insts len wf [wfdom wfcodom cs subst] [wfdom' wfcodom' cs' subst'].
  split; auto.
  now rewrite app_context_assoc.
  eapply context_subst_app_inv; split; auto.
  rewrite skipn_all_app_eq; try lia. auto.
  rewrite (firstn_app_left) ?Nat.add_0_r // firstn_0 // app_nil_r //.
  rewrite -(firstn_skipn #|Δ'| insts).
  eapply stc_subsletE_app; auto.
Qed.


(** T1 [isType_prim_arg_types]. Port of [PCUICSR.isType_prim_arg_types] (same premises): [typeE_Const] for
    the domain, [isType_liftE] for the codomain, [typeE_Prod] inlined for [isType_tProd]. *)
Lemma isType_prim_arg_types_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {tags : list prim_tag} {res : term} {T : term}, wf_localE Σ Γ -> (forall t : prim_tag, In t tags -> t <> primArray) -> All (prim_op_tag_declared Σ) tags -> PCUICPrimOpType.prim_arg_types (retroknowledge Σ.1) tags res = Some T -> isTypeE Σ Γ res -> isTypeE Σ Γ T.
Proof.
  intros Σ wfΣ Γ tags res T wfΓ.
  induction tags as [|t tags ih] in T |- *; cbn; intros hna hall h hres.
  - noconf h. exact hres.
  - depelim hall.
    destruct (PCUICPrimOpType.prim_tag_type _ t) as [a|] eqn:ht => //.
    destruct (PCUICPrimOpType.prim_arg_types _ tags res) as [rest|] eqn:hr => //.
    cbn in h. noconf h.
    destruct p as (kn & d & [hpc hd hinv]).
    unfold PCUICPrimOpType.prim_tag_type in ht.
    destruct (EnvironmentTyping.retro_type_constant _ t) as [kn'|] eqn:hrt => //.
    cbn in ht. noconf ht.
    assert (ept : primitive_constant Σ t = EnvironmentTyping.retro_type_constant (retroknowledge Σ) t)
      by (destruct t; reflexivity).
    rewrite ept hrt in hpc. noconf hpc.
    assert (hnat : t <> primArray) by (apply hna; now left).
    assert (hrest : isTypeE Σ Γ rest).
    { eapply (ih rest); tea; try reflexivity. intros t' ht'. apply hna. now right. }
    (* the domain: a type constant, of sort [Set], relevant *)
    assert (hdom : isTypeRelE Σ Γ (tConst kn' []) Relevant).
    { destruct t; try congruence; cbn in hinv.
      all: destruct hinv as [hty hbod huniv]; split; [constructor|];
        exists (Sort.type0@[[]]); repeat split.
      all: try reflexivity.
      all: change (tSort ?s@[[]]) with (tSort s)@[[]];
        rewrite <- hty; refine (typeE_Const _ _ _ [] _ wfΓ hd _); rewrite huniv //. }
    have hcod : isTypeE Σ (Γ ,, vass (mkBindAnn nAnon Relevant) (tConst kn' [])) (lift0 1 rest).
    { eapply (isType_liftE (n := 1) (Γ := Γ ,, vass (mkBindAnn nAnon Relevant) (tConst kn' []))); cbn; tea.
      + lia.
      + constructor; tea. }
    unfold tImpl.
    pose proof (lift_sorting_extract hdom) as hA.
    destruct hcod as (_ & sB & HB & _).
    eapply has_sort_isTypeE.
    eapply typeE_Prod; eassumption.
Qed.


(** ** The universe facts of [typingE] (helpers [univ_*])

  Rows: [wf_universes_inst], [LSet_in_global_bounded] (U_facts); [type_local_ctx_wf],
  [typing_wf_universes], [typing_wf_sort], [isType_wf_universes] (T0_facts); [ctf_wf_universes]
  (ConvTypedFacts of EtaConv @ c7cbbe73, at [welltypedE]/[wf_extE]).

  Transport. Base proves the universe lemmas under a premise [wf Σ] that their proofs read only
  through [on_global_univs Σ.(universes)]. [univ_strip Σ] keeps the universes and the
  retroknowledge of [Σ] and drops the declarations: [wfE Σ] gives base [wf (univ_strip Σ)]
  (no declaration is left to type, [univ_wf_strip]), and every universe notion ([global_levels],
  [global_ext_levels], [wf_universes], [wf_instance], [wf_ctx_universes], [on_udecl_prop]) reads
  only [Σ.(universes)], so it is CONVERTIBLE between [Σ] and [univ_strip Σ]. The base lemma
  applied at [univ_strip Σ] therefore type-checks at [Σ]. *)

Definition univ_strip (Σ : global_env) : global_env :=
  {| universes := Σ.(universes); declarations := []; retroknowledge := Σ.(retroknowledge) |}.

Lemma univ_wf_strip {cf : checker_flags} {Σ : global_env} : wfE Σ -> wf (univ_strip Σ).
Proof.
  intros [onu [onr _]]. split; [exact onu|]. split; [exact onr|]. cbn. constructor.
Qed.

Lemma univ_extends_strip {Σ Σ' : global_env} : extends Σ Σ' -> extends (univ_strip Σ) (univ_strip Σ').
Proof.
  intros [hu _ hr]. split; [exact hu| |exact hr].
  intros c. exists []. reflexivity.
Qed.

(** U_facts [wf_universes_inst] (audit hyp-audit-C.md line 182: syntactic): base
    [PCUICWfUniverses.wf_universes_inst] at [univ_strip Σ.1]. *)
Lemma wf_universes_inst_proved {cf : checker_flags} :
  forall {Σ : global_env_ext} (univs : universes_decl) (t : term) (u : list LevelSet.elt), wfE Σ -> on_udecl_prop Σ.1 univs -> wf_instance Σ u -> wf_universes (Σ.1, univs) t -> wf_universes Σ t@[u].
Proof.
  intros Σ univs t u wfΣ ond wfu wft.
  exact (@PCUICWfUniverses.wf_universes_inst cf (univ_strip Σ.1, Σ.2) univs t u (univ_wf_strip wfΣ) ond wfu wft).
Qed.

(** U_facts [LSet_in_global_bounded] (line 182: [not_var_global_levels] reads only
    [on_global_univs]): base [PCUICInductiveInversion.LSet_in_global_bounded] at [univ_strip Σ]. *)
Lemma LSet_in_global_bounded_proved {cf : checker_flags} :
  forall {Σ : global_env} {l : LevelSet.elt} (k : nat), wfE Σ -> LevelSet.In l (global_levels Σ) -> closedu_level k l.
Proof.
  intros Σ l k wfΣ hin.
  exact (@PCUICInductiveInversion.LSet_in_global_bounded cf (univ_strip Σ) l k (univ_wf_strip wfΣ) hin).
Qed.

(** T0 row 48 [type_local_ctx_wf] (structural): base [PCUICInductives.type_local_ctx_wf]'s proof;
    the empty context case of [type_local_ctx] is [wf_sort Σ s] itself. *)
Lemma type_local_ctx_wf_proved {cf : checker_flags} :
  forall {Σ : global_env_ext} {Γ Δ : context} {s : sort}, wfE Σ.1 -> type_local_ctx (lift_typing typingE) Σ Γ Δ s -> wf_sort Σ s.
Proof.
  intros Σ Γ Δ s wfΣ.
  induction Δ as [|[na [b|] ty] Δ]; simpl; intuition auto.
Qed.

(** Helpers for T0 row 36 [typing_wf_universes]: the port of base [PCUICWfUniverses.wf_types]
    over [typingE_ind_env]. *)

Ltac univ_to_prop :=
  repeat match goal with
  | [ H: is_true (?x && ?y) |- _ ] =>
   let x := fresh in let y := fresh in move/andP: H; move=> [x y]; rewrite ?x ?y; simpl
  end.

Ltac univ_to_wfu :=
  repeat match goal with
  | [ H: is_true (wf_universeb _ ?x) |- _ ] => apply (ssrbool.elimT (@wf_universe_reflect _ x)) in H
  | [ |- is_true (wf_universeb _ ?x) ] => apply (ssrbool.introT (@wf_universe_reflect _ x))
  | [ H: is_true (Sort.on_sort (wf_universeb _) _ ?x) |- _ ] => apply (ssrbool.elimT (@wf_sort_reflect _ x)) in H
  | [ |- is_true (Sort.on_sort (wf_universeb _) _ ?x) ] => apply (ssrbool.introT (@wf_sort_reflect _ x))
  | [ H: is_true (wf_sortb _ ?x) |- _ ] => apply (ssrbool.elimT (@wf_sort_reflect _ x)) in H
  | [ |- is_true (wf_sortb _ ?x) ] => apply (ssrbool.introT (@wf_sort_reflect _ x))
  end.

Ltac univ_specIH :=
  repeat match goal with
  | [ H : on_udecl _ _, H' : on_udecl _ _ -> _ |- _ ] => specialize (H' H)
  end.

Lemma univ_weaken_wf_universes {cf : checker_flags} {Σ Σ' : global_env} φ t :
  wfE Σ -> wfE Σ' -> extends Σ Σ' -> wf_universes (Σ, φ) t -> wf_universes (Σ', φ) t.
Proof.
  intros wfΣ wfΣ' ext.
  exact (@PCUICWfUniverses.weaken_wf_universes cf (univ_strip Σ, φ) (univ_strip Σ') t
    (univ_wf_strip wfΣ) (univ_wf_strip wfΣ') (univ_extends_strip ext)).
Qed.

(** E copy of base [PCUICWfUniverses.wf_universes_weaken] (same proof). *)
Lemma univ_wf_universes_weakenE {cf : checker_flags} :
  weaken_env_prop cumulSpecE0 (lift_typing typingE)
    (fun Σ _ j => option_default (wf_universes Σ) (j_term j) true && wf_universes Σ (j_typ j) && option_default (wf_sortb Σ) (j_univ j) true).
Proof.
  intros Σ Σ' φ wfΣ wfΣ' Hext _ j Hj.
  pose proof (fun t => @univ_weaken_wf_universes cf Σ Σ' φ t wfΣ wfΣ' Hext) as H.
  rtoProp; repeat split; auto.
  1: destruct j_term => //; cbn in *; auto.
  1: destruct j_univ => //; cbn in *; now apply (H (tSort _)).
Qed.

Lemma univ_wf_ctx_universes_closed {cf : checker_flags} {Σ : global_env} {wfΣ : wfE Σ} {univs ctx} :
  on_udecl_prop Σ univs ->
  wf_ctx_universes (Σ, univs) ctx ->
  test_context (closedu #|polymorphic_instance univs|) ctx.
Proof.
  exact (@PCUICWfUniverses.wf_ctx_universes_closed cf (univ_strip Σ) (univ_wf_strip wfΣ) univs ctx).
Qed.

(** Base [PCUICWfUniverses.closed_ind_predicate_context] without its unused premises
    ([wf Σ], [declared_inductive]); same proof. *)
Lemma univ_closed_ind_predicate_context {ind mdecl idecl} :
  test_context (closedu #|polymorphic_instance (ind_universes mdecl)|) (ind_params mdecl) ->
  test_context (closedu #|polymorphic_instance (ind_universes mdecl)|) (ind_indices idecl) ->
  test_context (closedu #|abstract_instance (ind_universes mdecl)|) (ind_predicate_context ind mdecl idecl).
Proof.
  rewrite /ind_predicate_context; cbn.
  rewrite closedu_mkApps /=.
  rewrite closedu_abstract_instance /= => clpars clinds.
  apply/andP; split.
  * apply closedu_expand_lets_ctx. now rewrite clpars clinds.
  * apply closedu_to_extended_list_k.
    rewrite test_context_app.
    rewrite (closedu_smash_context _ _ clpars).
    apply closedu_expand_lets_ctx => //.
    now rewrite clpars.
Qed.

(** Base [PCUICWfUniverses.closedu_inds] without its unused premise [wf Σ]; same proof. *)
Lemma univ_closedu_inds {ind mdecl} :
  forallb (closedu #|abstract_instance (ind_universes mdecl)|)
    (inds ind (abstract_instance (ind_universes mdecl)) (ind_bodies mdecl)).
Proof.
  rewrite /inds.
  induction #|ind_bodies mdecl|; cbn; auto.
  rewrite IHn andb_true_r.
  eapply closedu_abstract_instance.
Qed.

(** The port of base [wf_types]. Inside a module so that the local hypothesis-naming hook
    (the E twin of base's, [PCUICWeakeningEnvTypEta.my_rename_hypE]) ends with the module
    (checked, build u5: after [End univ_WfTypesE], [rename_all_hyps] leaves a [wfE] and a
    [typingE] hypothesis unrenamed, so the parts concatenated after this one are unaffected). The
    script is base's with: [typing_ind_env] → [typingE_ind_env], [declared_*_inv] →
    [declared_*_invE], [wf_universes_weaken] → [univ_wf_universes_weakenE], [wf_universes_inst] →
    [wf_universes_inst_proved], [wf_ctx_universes_closed] / [closed_ind_predicate_context] /
    [closedu_inds] → the [univ_] helpers above. The [typeE_Cumul] case is closed by the preamble's
    [auto] from the two induction hypotheses; the conversion premise is not read. *)
Module univ_WfTypesE.

#[local] Ltac rename_hyp h ht ::= my_rename_hypE h ht.

Theorem univ_wf_typesE {cf : checker_flags} :
  env_propE (fun Σ Γ t T => wf_universes Σ t && wf_universes Σ T)
    (fun Σ _ j => lift_wfbu_term (wf_universes Σ) (wf_sortb Σ) j)
    (fun Σ Γ => wf_ctx_universes Σ Γ).
Proof.
    apply typingE_ind_env; unfold lift_wfbu_term; intros; rename_all_hyps; cbn; rewrite -!/(wf_universes _ _) ;
    univ_specIH; univ_to_prop;
    cbn; auto.

    - eapply MRReflect.introT. 1: apply lift_wfu_wfbu_term.
      apply lift_typing_subjtyp with (1 := X) => //= t T [] _ /andP[] //.

    - apply All_local_env_cst, All_forallb in X0.
      apply forallb_impl with (2 := X0) => [] [na bo ty] _ //= /andP[] //=.

    - rewrite wf_universes_lift.
      eapply forallb_nth_error with (n := n) in H0. rewrite heq_nth_error /= in H0.
      now move/andP: H0.

    - apply/andP; split; univ_to_wfu; cbn ; eauto with pcuic.

    - cbn in *; univ_to_wfu ; eauto with pcuic.
    - rewrite wf_universes_subst. constructor. univ_to_wfu; auto. constructor.
      now move/andP: H1 => [].

    - apply/andP; split.
      { rewrite wf_universeb_instance_forall.
        apply/wf_instanceP.
        eapply consistent_instance_ext_wf; eauto. }
      pose proof (declared_constant_invE _ _ _ _ univ_wf_universes_weakenE wf X H0) as [[_ X0]%andb_and _]%andb_and.
      unshelve eapply declared_constant_to_gen in H0; eauto.
      epose proof (weaken_lookup_on_global_env' Σ.1 _ _ wf H0).
      eapply wf_universes_inst_proved. 2:eauto. all:eauto.
      now eapply consistent_instance_ext_wf.

    - apply/andP; split.
      { rewrite wf_universeb_instance_forall.
        apply/wf_instanceP.
        eapply consistent_instance_ext_wf; eauto. }
      pose proof (declared_inductive_invE univ_wf_universes_weakenE wf X isdecl).
      move/onArity : X0 => /andP[] /andP[] /= _ Hind _.
      unshelve eapply declared_inductive_to_gen in isdecl; eauto.
      eapply wf_universes_inst_proved; eauto.
      exact (weaken_lookup_on_global_env' Σ.1 _ _ wf (proj1 isdecl)).
      now eapply consistent_instance_ext_wf.

    - apply/andP; split.
      { rewrite wf_universeb_instance_forall.
        apply/wf_instanceP.
        eapply consistent_instance_ext_wf; eauto. }
      pose proof (declared_constructor_invE univ_wf_universes_weakenE wf X isdecl) as [sc [nthe onc]].
      unfold type_of_constructor.
      rewrite wf_universes_subst.
      { apply wf_universes_inds.
        now eapply consistent_instance_ext_wf. }
      move/on_ctype : onc => /andP[] /andP[] /= _ onc _.
      clear nthe. unshelve eapply declared_constructor_to_gen in isdecl; eauto.
      eapply wf_universes_inst_proved; eauto.
      exact (weaken_lookup_on_global_env' Σ.1 _ _ wf (proj1 (proj1 isdecl))).
      now eapply consistent_instance_ext_wf.

    - rewrite wf_universes_mkApps in H6.
      move/andP: H6 => /= [] wfu; rewrite forallb_app.
      move/andP=> [] wfpars wfinds.
      cbn in wfu.
      rewrite wfu /= wfpars wf_universes_mkApps /=
        forallb_app wfinds /= H0 /= !andb_true_r.
      pose proof (declared_inductive_invE univ_wf_universes_weakenE wf X isdecl).
      move:(onArityRed X3) => /andP[] /andP[] /= _ hty _.
      rewrite !wf_universes_it_mkProd_or_LetIn in hty.
      move/and3P: hty => [] wfp wfindis wfisort.
      have ond : on_udecl_prop Σ (ind_universes mdecl).
      { eapply (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl)); eauto.
      unshelve eapply declared_inductive_to_gen in isdecl; eauto.
      }
      eapply univ_wf_ctx_universes_closed in wfp => //.
      eapply univ_wf_ctx_universes_closed in wfindis => //.
      rewrite (consistent_instance_length H2).
      erewrite closedu_compare_decls; tea.
      rewrite univ_closed_ind_predicate_context // /=.
      unfold test_branch.
      apply/andP; split.
      * have wfbrctx : All (fun cdecl =>
          test_context (closedu #|polymorphic_instance (ind_universes mdecl)|) (cstr_args cdecl))
          (ind_ctors idecl).
        { pose proof (onConstructors := onConstructors X3).
          clear -wf ond onConstructors.
          red in onConstructors. solve_all. destruct X.
          move : on_ctype => /andP[] /andP[] /= _ wfty _.
          rewrite cstr_eq in wfty.
          rewrite !wf_universes_it_mkProd_or_LetIn in wfty.
          move/and3P: wfty => [] _ clargs _.
          apply univ_wf_ctx_universes_closed in clargs => //. }
        solve_all.
        erewrite closedu_compare_decls; [|tea].
        rewrite /cstr_branch_context.
        eapply closedu_expand_lets_ctx.
        rewrite wfp. eapply closedu_subst_context.
        rewrite a.
        now rewrite univ_closedu_inds.
      * rewrite wf_universes_it_mkLambda_or_LetIn H7 andb_true_r.
        move: H4.
        rewrite /wf_ctx_universes forallb_app => /andP[hctx _].
        apply (MRReflect.introT onctxP).
        solve_all. unfold ondecl, wf_decl_universes, on_decl_universes in *.
        move/andP:H3 => [Hb Ht] //; split; tas.
        now destruct decl_body.

    - rewrite /subst1. rewrite wf_universes_subst.
      constructor => //. eapply All_rev.
      rewrite wf_universes_mkApps in H2.
      move/andP: H2 => [].
      now intros _ hargs%forallb_All.
      pose proof (declared_projection_invE univ_wf_universes_weakenE wf X isdecl).
      destruct (declared_inductive_invE); simpl in *.
      destruct ind_ctors as [|cs []] => //.
      destruct ind_cunivs as [|cunivs []] => //;
      destruct X0 as [[[? ?] ?] ?] => //.
      red in o0.
      destruct nth_error eqn:heq => //.
      destruct o0  as [_ ->].
      rewrite wf_universes_mkApps {1}/wf_universes /= -!/(wf_universes _ _)
        wf_universeb_instance_forall in H2.
      move/andP: H2 => [/wf_instanceP wfu wfargs].
      unshelve eapply declared_projection_to_gen in isdecl; eauto.
      eapply (wf_universes_inst_proved (ind_universes mdecl)); eauto.
      exact (weaken_lookup_on_global_env' Σ.1 _ _ wf (proj1 (proj1 (proj1 isdecl)))).
      rewrite wf_universes_subst.
      eapply wf_universes_inds; eauto.
      eapply wf_abstract_instance.
      rewrite wf_universes_subst. apply wf_projs.
      rewrite wf_universes_lift.
      rewrite smash_context_app smash_context_acc in heq.
      autorewrite with len in heq. rewrite nth_error_app_lt in heq.
      autorewrite with len. lia.
      rewrite PCUICSubstitution.nth_error_subst_context in heq.
      autorewrite with len in heq. simpl in heq.
      epose proof (nth_error_lift_context_eq _ (smash_context [] (ind_params mdecl)) _ _).
      autorewrite with len in H0. simpl in H0. rewrite -> H0 in heq. clear H0.
      autorewrite with len in heq.
      simpl in heq.
      destruct nth_error eqn:hnth; simpl in * => //.
      noconf heq. simpl.
      rewrite wf_universes_subst.
      apply wf_extended_subst.
      move:onArityRed => /andP[] /andP[] /= _ Hs _.
      rewrite !wf_universes_it_mkProd_or_LetIn in Hs.
      now move/andP: Hs => /andP /andP [].
      rewrite wf_universes_lift.
      eapply PCUICWfUniverses.wf_universes_local_ctx_smash in s.
      eapply wf_universes_local_ctx_nth_error in s; eauto.

    - clear X X1. unfold on_def_type, on_def_body in *; cbn in *.
      apply/andP; split; auto.
      solve_all.
      eapply nth_error_all in X0 as (? & _)%andb_and; eauto.

    - clear X X1. unfold on_def_type, on_def_body in *; cbn in *.
      apply/andP; split; auto.
      solve_all.
      eapply nth_error_all in X0 as (? & _)%andb_and; eauto.

    - apply/andP; split; eauto.
      destruct X0; cbn => //.
      rtoProp; intuition eauto. solve_all.
      destruct X0; cbn => //.
      simp prim_type. cbn. rtoProp; intuition.
Qed.

End univ_WfTypesE.

(** T0 row 36 [typing_wf_universes]: base [PCUICWfUniverses.typing_wf_universes] over the port. *)
Lemma typing_wf_universes_proved {cf : checker_flags} :
  forall {Σ : global_env_ext} {Γ : context} {t : term} {T : term}, wfE Σ -> Σ;;; Γ |-E t : T -> wf_universes Σ t && wf_universes Σ T.
Proof.
  intros Σ Γ t T wfΣ Hty.
  exact (env_propE_typing univ_WfTypesE.univ_wf_typesE _ wfΣ _ _ _ Hty).
Qed.

(** T0 row 35 [typing_wf_sort]: from row 36, base's proof. *)
Lemma typing_wf_sort_proved {cf : checker_flags} :
  forall {Σ : global_env_ext} {Γ : context} {t : term} {s : sort}, wfE Σ -> Σ;;; Γ |-E t : tSort s -> wf_sort Σ s.
Proof.
  intros Σ Γ t s wfΣ Hty.
  apply typing_wf_universes_proved in Hty as [_ wfs]%andb_and; auto.
  cbn in wfs. now univ_to_wfu.
Qed.

(** T0 row 20 [isType_wf_universes]: from row 36, base's proof. *)
Lemma isType_wf_universes_proved {cf : checker_flags} :
  forall {Σ : global_env × universes_decl} {Γ : context} {T : term}, wfE Σ.1 -> isTypeE Σ Γ T -> wf_universes Σ T.
Proof.
  intros Σ Γ T wfΣ (_ & s & Hs & _).
  now eapply typing_wf_universes_proved in Hs as [HT _]%andb_and.
Qed.

(** [ConvTypedFacts.ctf_wf_universes] of EtaConv's [PCUICSafeConversionEtaFacts.v] @ [c7cbbe73] (class not
    in this branch), at [wt := welltypedE], [wfP := wf_extE]: row 36, as the base instance
    [conv_typed_facts_base] does with base [typing_wf_universes]. *)

(** ** K7 T0 [isType_it_mkProd_or_LetIn] (row 47): base [PCUICInductiveInversion.isType_it_mkProd_or_LetIn]'s
    proof; the let case types [tLetIn] at [tSort s] through [typing_wf_sort_proved] (row 35) and the zeta
    step [red1_cumulSpec], included into [cumulSpecE] by [cumulSpec0_incl_E]. *)
Lemma isType_it_mkProd_or_LetIn_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {Γ Δ : list context_decl} {T : term}, wfE Σ.1 -> isTypeE Σ (Γ,,, Δ) T -> isTypeE Σ Γ (it_mkProd_or_LetIn Δ T).
Proof.
  intros Σ Γ Δ T wfΣ. revert T.
  induction Δ as [|[na [b|] ty] Δ IHΔ].
  - now simpl.
  - intros T Hty.
    rewrite /= /mkProd_or_LetIn /=.
    eapply IHΔ.
    apply lift_sorting_it_impl_gen with Hty => // Hs.
    have wf : wf_localE Σ ((Γ ,,, Δ) ,, vdef na b ty) := typingE_wf_local Hs.
    apply All_local_env_tip in wf as [wf hd].
    eapply type_Cumul'.
    + eapply typeE_LetIn; [exact hd|exact Hs].
    + eapply isType_Sort; [exact (typing_wf_sort_proved (Σ := Σ) wfΣ Hs)|exact wf].
    + apply cumulSpec0_incl_E. eapply convSpec_cumulSpec, red1_cumulSpec. repeat constructor.
  - intros T (_ & s & Hs & _).
    apply IHΔ.
    have wf : wf_localE Σ ((Γ ,,, Δ) ,, vass na ty) := typingE_wf_local Hs.
    apply All_local_env_tip in wf as [_ hd].
    pose proof (lift_sorting_extract hd).
    eapply has_sort_isTypeE with (s := Sort.sort_of_product _ s).
    eapply typeE_Prod; eassumption.
Qed.

(** ** K7 reduction facts and telescope inversions: U rows [closed_red_confluence], [closed_red_from_empty],
    [red_expand_let], [red_it_mkProd_or_LetIn_smash], [red_mkApps_smash_witness],
    [red_rec_arg_check_one_fix]; T0 rows [inversion_it_mkProd_or_LetIn], [ind_arity_relevant].
    Reduction is unchanged in E: the base proofs go through over [ClosedBodies Σ], which [wfE Σ] gives
    ([wfE_ClosedBodies]); three U rows are inhabited directly by lemmas landed in [PCUICSREtaConv]
    ([frac/eta] @ [da1eb84b]). Helpers carry the prefix [rdx_]. *)

(** [closed_red_confluence] (U): base [PCUICContextConversion.closed_red_confluence] over
    [red_confluence_cb] ([PCUICConfluence.v:4070]). *)
Lemma closed_red_confluence_proved {cf : checker_flags} : forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {t : term} {u : term} {v : term}, Σ ;;; Γ ⊢ t ⇝ u -> Σ ;;; Γ ⊢ t ⇝ v -> ∑ v' : term, Σ ;;; Γ ⊢ u ⇝ v' × Σ ;;; Γ ⊢ v ⇝ v'.
Proof.
  intros Σ wfΣ Γ t u v [clΓ clT r] [clΓ' clT' r'].
  pose proof (wfE_ClosedBodies Σ) as cbΣ.
  have clu : is_open_term Γ u := red_is_open_term_cb (cf := cf) (wfΣ := cbΣ) t u r clΓ clT.
  have clv : is_open_term Γ v := red_is_open_term_cb (cf := cf) (wfΣ := cbΣ) t v r' clΓ clT.
  destruct (PCUICConfluence.red_confluence_cb (Γ := exist Γ clΓ) (t := exist t clT) r r') as [v' [redl redr]].
  exists v'. split.
  - exact (into_closed_red redl clΓ clu).
  - exact (into_closed_red redr clΓ clv).
Qed.

(** [closed_red_from_empty] (U): inhabited by the landed [closed_red_from_empty_cb]
    ([pcuic/theories/PCUICSREtaConv.v:524], [frac/eta] @ [da1eb84b]), at [wfE_ClosedBodies Σ]. *)
Lemma closed_red_from_empty_proved {cf : checker_flags} : forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {M : term} {N : term}, on_free_vars_ctx xpred0 Γ -> closed M -> PCUICReduction.red Σ [] M N -> Σ ;;; Γ ⊢ M ⇝ N.
Proof.
  intros Σ wfΣ Γ M N.
  exact (@closed_red_from_empty_cb cf Σ (wfE_ClosedBodies Σ) Γ M N).
Qed.

(** [red_expand_let] (U): inhabited by the landed [red_expand_letE] ([PCUICSREtaConv.v:512]). *)
Lemma red_expand_let_proved {cf : checker_flags} : forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {na : aname} {b : term} {ty : term} {t : term}, wf_localE Σ (Γ,,, [vdef na b ty]) -> on_free_vars (shiftnP #|Γ,,, [vdef na b ty]| (fun _ : nat => false)) t -> Σ ;;; Γ,, vdef na b ty ⊢ t ⇝ lift0 1 (t {0 := b}).
Proof.
  intros Σ wfΣ Γ na b ty t.
  exact (@red_expand_letE cf Σ wfΣ Γ na b ty t).
Qed.

(** [red_it_mkProd_or_LetIn_smash] (U): inhabited by the landed [red_it_mkProd_or_LetIn_smash_cb]
    ([PCUICSREtaConv.v:540]), at [wfE_ClosedBodies Σ]. *)
Lemma red_it_mkProd_or_LetIn_smash_proved {cf : checker_flags} : forall {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ : list context_decl) (ctx : context) (t : term) (u : term) (n : nat) (c : context_decl), Σ ;;; Γ ⊢ it_mkProd_or_LetIn ctx t ⇝ u -> nth_error (List.rev (smash_context [] ctx)) n = Some c -> ∑ (ctx' : context) (t' : term) (d : context_decl), [× decompose_prod_assum [] u = (ctx', t'), nth_error (List.rev (smash_context [] ctx')) n = Some d & Σ ;;; Γ,,, skipn (#|smash_context [] ctx| - n) (smash_context [] ctx) ⊢ decl_type c ⇝ decl_type d].
Proof.
  intros Σ wfΣ.
  exact (@red_it_mkProd_or_LetIn_smash_cb cf Σ (wfE_ClosedBodies Σ)).
Qed.

(** The base proof scripts below come from [PCUICInductives.v] and [PCUICFixWitness.v]; they run with
    the settings and imports of [PCUICInductives.v] (all modules already loaded), kept local by the
    section. *)
Section RdxBaseScripts.
Import PCUICTactics PCUICInduction PCUICContexts PCUICSubstitution.
Local Set SimplIsCbn.
Local Arguments subst_context !s _ !Γ.
Local Arguments it_mkProd_or_LetIn !l _.

(** Base [PCUICInductives.red_it_mkProd_or_LetIn_to_smash] (:2268): its [wf] premise is unused, so the
    same script proves it with no environment premise. *)
Lemma rdx_red_it_mkProd_or_LetIn_to_smash {Σ : global_env_ext} Γ Δ T :
  is_closed_context Γ ->
  is_open_term Γ (it_mkProd_or_LetIn Δ T) ->
  Σ ;;; Γ ⊢ it_mkProd_or_LetIn Δ T ⇝ it_mkProd_or_LetIn (smash_context [] Δ) (expand_lets Δ T).
Proof.
  intros clΓ clt.
  eapply into_closed_red => //.
  clear clΓ clt.
  induction Δ in Γ, T |- * using ctx_length_rev_ind; simpl; auto.
  - rewrite expand_lets_nil. reflexivity.
  - rewrite PCUICContexts.smash_context_app_expand /=.
    destruct d as [na [b|] ty].
    * rewrite expand_lets_vdef {1}it_mkProd_or_LetIn_app /= subst_context_nil app_context_nil_l.
      rewrite PCUICContexts.expand_lets_smash_context /= PCUICContexts.expand_lets_k_ctx_nil.
      rewrite /expand_lets_ctx /expand_lets_k_ctx /= subst_empty lift0_id lift0_context.
      rewrite /mkProd_or_LetIn /=.
      etransitivity.
      + eapply red1_red, red_zeta.
      + rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r.
        now eapply X; len.
    * rewrite expand_lets_vass it_mkProd_or_LetIn_app /=.
      rewrite it_mkProd_or_LetIn_app /=.
      eapply red_prod. reflexivity.
      rewrite PCUICContexts.expand_lets_smash_context /= PCUICContexts.expand_lets_k_ctx_nil.
      rewrite expand_lets_ctx_assumption_context. repeat constructor.
      now eapply X.
Qed.

(** [red_mkApps_smash_witness] (U): the script of base [PCUICFixWitness.red_mkApps_smash_witness]. *)
Lemma red_mkApps_smash_witness_proved {cf : checker_flags} : forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {C : term} {ctx : context} {i : inductive} {u : Instance.t} {l : list term}, Σ ;;; Γ ⊢ C ⇝ it_mkProd_or_LetIn ctx (mkApps (tInd i u) l) -> ∑ l' : list term, Σ ;;; Γ ⊢ C ⇝ it_mkProd_or_LetIn (smash_context [] ctx) (mkApps (tInd i u) l').
Proof.
  intros Σ wfΣ Γ C ctx i u l r.
  pose proof (wfE_ClosedBodies Σ) as cbΣ.
  have clΓ := clrel_ctx r.
  have opr : is_open_term Γ (it_mkProd_or_LetIn ctx (mkApps (tInd i u) l))
    := closed_red_open_right_cb (cf := cf) r.
  have h : Σ ;;; Γ ⊢ it_mkProd_or_LetIn ctx (mkApps (tInd i u) l) ⇝
           it_mkProd_or_LetIn (smash_context [] ctx) (expand_lets ctx (mkApps (tInd i u) l)).
  { now eapply rdx_red_it_mkProd_or_LetIn_to_smash. }
  rewrite expand_lets_mkApps in h.
  rewrite /expand_lets /expand_lets_k /= in h.
  eexists.
  transitivity (it_mkProd_or_LetIn ctx (mkApps (tInd i u) l)); [exact r|exact h].
Qed.

(** Base [PCUICInductives.closed_red_it_mkProd_or_LetIn_assum_nth] (:2246): its [wf] premise is unused. *)
Lemma rdx_closed_red_it_mkProd_or_LetIn_assum_nth {Σ : global_env_ext} Γ sctx T n c A' :
  assumption_context sctx ->
  is_open_term Γ (it_mkProd_or_LetIn sctx T) ->
  nth_error (List.rev sctx) n = Some c ->
  Σ ;;; Γ ,,, skipn (#|sctx| - n) sctx ⊢ decl_type c ⇝ A' ->
  ∑ sctx',
    [× assumption_context sctx',
       #|sctx'| = #|sctx|,
       nth_error (List.rev sctx') n = Some (vass (decl_name c) A'),
       (forall i, i <> n -> nth_error (List.rev sctx') i = nth_error (List.rev sctx) i) &
       Σ ;;; Γ ⊢ it_mkProd_or_LetIn sctx T ⇝ it_mkProd_or_LetIn sctx' T].
Proof.
  intros ass op hnth hred.
  have clΓ : is_closed_context Γ.
  { move: (clrel_ctx hred). rewrite on_free_vars_ctx_app => /andP[] //. }
  destruct (PCUICInductives.red_it_mkProd_or_LetIn_assum_nth (Σ := Σ) Γ sctx T n c A' ass hnth (clrel_rel hred))
    as [sctx' [ass' hlen hnth' hother r]].
  exists sctx'; split; try assumption.
  now apply into_closed_red.
Qed.

(** [red_rec_arg_check_one_fix] (U): the script of base [PCUICInductives.red_rec_arg_check_one_fix]
    over the two helpers above. *)
Lemma red_rec_arg_check_one_fix_proved {cf : checker_flags} : forall {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ : list context_decl) (d : def term) (ctx : context) (concl : term) (c : context_decl) (ind : inductive) (u : Instance.t) (args : list term), on_free_vars (shiftnP #|Γ| xpred0) (dtype d) -> decompose_prod_assum [] (dtype d) = (ctx, concl) -> nth_error (List.rev (smash_context [] ctx)) (rarg d) = Some c -> Σ ;;; Γ,,, skipn (#|smash_context [] ctx| - rarg d) (smash_context [] ctx) ⊢ decl_type c ⇝ mkApps (tInd ind u) args -> has_rec_arg d × (∑ ty : term, Σ ;;; Γ ⊢ dtype d ⇝ ty × check_one_fix (def_with_type d ty) = Some (inductive_mind ind)).
Proof.
  intros Σ wfΣ Γ d ctx concl c ind u args op decomp hnth hred.
  pose proof (wfE_ClosedBodies Σ) as cbΣ.
  have clΓ : is_closed_context Γ.
  { move: (clrel_ctx hred). rewrite on_free_vars_ctx_app => /andP[] //. }
  have eqty := PCUICSubstitution.decompose_prod_assum_it_mkProd_or_LetIn _ _ _ _ decomp.
  cbn in eqty.
  have r1 : Σ ;;; Γ ⊢ dtype d ⇝ it_mkProd_or_LetIn (smash_context [] ctx) (expand_lets ctx concl).
  { rewrite eqty. apply rdx_red_it_mkProd_or_LetIn_to_smash => //. now rewrite -eqty. }
  have ass : assumption_context (smash_context [] ctx).
  { apply PCUICContexts.smash_context_assumption_context; constructor. }
  destruct (rdx_closed_red_it_mkProd_or_LetIn_assum_nth Γ _ _ _ _ _ ass (closed_red_open_right_cb (cf := cf) r1) hnth hred)
    as [sctx' [ass' hlen hnth' _ r2]].
  split.
  - have hlt := nth_error_Some_length hnth. rewrite List.length_rev smash_context_length /= in hlt.
    rewrite /has_rec_arg decomp /=. now apply Nat.ltb_lt.
  - exists (it_mkProd_or_LetIn sctx' (expand_lets ctx concl)). split.
    + now transitivity (it_mkProd_or_LetIn (smash_context [] ctx) (expand_lets ctx concl)).
    + eapply PCUICInductives.check_one_fix_it_mkProd_or_LetIn_assum; [exact ass'|exact hnth'|reflexivity].
Qed.

End RdxBaseScripts.


(** ** T0 rows [ind_arity_relevant] and [inversion_it_mkProd_or_LetIn] *)

(** A sort comparison as a [ws_cumul_pbE] between the two sorts. *)
Lemma rdx_sort_le {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {a b : sort} :
  is_closed_context Γ -> leq_sort Σ a b -> Σ ;;; Γ ⊢E tSort a ≤ tSort b.
Proof.
  intros clΓ h.
  apply into_ws_cumul_pbE_spec; [|exact clΓ|reflexivity|reflexivity].
  apply eq_term_upto_univ_cumulSpec. constructor. exact h.
Qed.

(** The let-in step of row 9's route (hyp-audit-C §3.5 row 9): [ws_cumul_pbE_LetIn_l_inv]
    ([PCUICEtaA6.v:361]), [red_expand_letE], [weakening_ws_cumul_pbE] ([PCUICWsCumulEtaSubst.v:189]). *)
Lemma rdx_letin_le_sort {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {na : aname}
  {b B A : term} {s : sort} :
  wf_localE Σ (Γ ,, vdef na b B) -> is_open_term (Γ ,, vdef na b B) A ->
  Σ ;;; Γ ⊢E tLetIn na b B A ≤ tSort s -> Σ ;;; Γ ,, vdef na b B ⊢E A ≤ tSort s.
Proof.
  intros wfΓ opA c.
  have c1 : Σ ;;; Γ ⊢E A {0 := b} ≤ tSort s by exact (ws_cumul_pbE_LetIn_l_inv c).
  have clΓ : is_closed_context (Γ ,,, [vdef na b B]) by exact (wf_local_closed_contextE wfΓ).
  have w : Σ ;;; Γ ,, vdef na b B ⊢E lift0 1 (A {0 := b}) ≤ tSort s
    by exact (weakening_ws_cumul_pbE (Γ := Γ) (Γ' := []) (Γ'' := [vdef na b B]) c1 clΓ).
  have r : Σ ;;; Γ ,, vdef na b B ⊢ A ⇝ lift0 1 (A {0 := b}) by exact (@red_expand_letE cf Σ wfΣ Γ na b B A wfΓ opA).
  exact (@ws_cumul_pbE_trans _ Σ (wfE_ClosedBodies Σ) Cumul _ _ _ _ (red_ws_cumul_pb (pb := Cumul) r) w).
Qed.

(** Inversion of a typed telescope that stops before the final cumulativity: the body has a type
    below the telescope's sort. Unlike [inversion_it_mkProd_or_LetIn], it needs no [wf_sort] of that
    sort, because it never retypes the body at it. *)
Lemma rdx_inversion_it_mkProd_or_LetIn_le {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
  (Δ : context) : forall (Γ : context) (T X : term) (s : sort),
  Σ ;;; Γ |-E it_mkProd_or_LetIn Δ T : X -> Σ ;;; Γ ⊢E X ≤ tSort s ->
  ∑ X' : term, Σ ;;; Γ ,,, Δ |-E T : X' × Σ ;;; Γ ,,, Δ ⊢E X' ≤ tSort s.
Proof.
  induction Δ as [|d Δ IH]; intros Γ T X s h c.
  - exists X. split; assumption.
  - destruct (IH Γ (mkProd_or_LetIn d T) X s h c) as [X1 [h1 c1]].
    destruct d as [na [b|] ty]; cbn [mkProd_or_LetIn decl_body decl_name decl_type] in h1.
    + destruct (inversion_LetIn Σ wfΣ h1) as [A [_ [hA cA]]].
      exists A. split; [exact hA|].
      apply rdx_letin_le_sort.
      * exact (typingE_wf_local hA).
      * exact (type_is_open_termE hA).
      * exact (@ws_cumul_pbE_trans _ Σ (wfE_ClosedBodies Σ) Cumul _ _ _ _ cA c1).
    + destruct (inversion_Prod Σ wfΣ h1) as [s1 [s2 [_ [hB cB]]]].
      exists (tSort s2). split; [exact hB|].
      have clΓ : is_closed_context (Γ ,,, Δ ,, vass na ty) by exact (wf_local_closed_contextE (typingE_wf_local hB)).
      have hle : leq_sort Σ (Sort.sort_of_product s1 s2) s
        by exact (ws_cumul_pbE_Sort_inv Cumul (@ws_cumul_pbE_trans _ Σ (wfE_ClosedBodies Σ) Cumul _ _ _ _ cB c1)).
      exact (@ws_cumul_pbE_trans _ Σ (wfE_ClosedBodies Σ) Cumul _ _ _ _
               (rdx_sort_le clΓ (leq_sort_product _ s1 s2)) (rdx_sort_le clΓ hle)).
Qed.

(** [ind_arity_relevant] (T0, row 7): base [PCUICInductiveInversion.ind_arity_relevant] with
    [rdx_inversion_it_mkProd_or_LetIn_le] in place of [inversion_it_mkProd_or_LetIn], then K7
    [inversion_Sort], [ws_cumul_pbE_Sort_inv] ([PCUICEtaA6.v:176]), [leq_relevance], [relevance_super]. *)
Lemma ind_arity_relevant_proved {cf : checker_flags} : forall (Σ : global_env_ext) (mdecl : mutual_inductive_body) (idecl : one_inductive_body), wfE Σ.1 -> let ind_type := it_mkProd_or_LetIn (ind_params mdecl) (it_mkProd_or_LetIn (ind_indices idecl) (tSort (ind_sort idecl))) in isTypeE Σ [] ind_type -> isTypeRelE Σ [] ind_type rel_of_Type.
Proof.
  intros Σ mdecl idecl wfΣ ind_type (_ & s & Hs & _ & _).
  repeat (eexists; tea). cbn in Hs |- *.
  rewrite /ind_type in Hs.
  rewrite -it_mkProd_or_LetIn_app in Hs.
  destruct (rdx_inversion_it_mkProd_or_LetIn_le (wfΣ := wfΣ) _ _ _ _ s Hs (typing_ws_cumul_pbE (le := Cumul) Hs))
    as [X [hX cX]].
  destruct (inversion_Sort Σ wfΣ hX) as [_ [_ cS]].
  have hle : leq_sort Σ (Sort.super (ind_sort idecl)) s
    by exact (ws_cumul_pbE_Sort_inv Cumul (@ws_cumul_pbE_trans _ Σ (wfE_ClosedBodies Σ) Cumul _ _ _ _ cS cX)).
  eapply leq_relevance; tea.
  eapply relevance_super.
Qed.

(** [inversion_it_mkProd_or_LetIn] (T0, row 9): base [PCUICSpine.inversion_it_mkProd_or_LetIn] reaches
    the body's sort through [type_it_mkProd_or_LetIn_inv]; here [rdx_inversion_it_mkProd_or_LetIn_le]
    gives a type of the body below [tSort s], and K7 [type_ws_cumul_pb] retypes it at [tSort s], whose
    well-formedness is [typing_wf_sort_proved] (row 35, above). *)
Lemma inversion_it_mkProd_or_LetIn_proved {cf : checker_flags} : forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {Δ : context} {t : term} {s : sort}, Σ;;; Γ |-E it_mkProd_or_LetIn Δ t : tSort s -> Σ;;; Γ,,, Δ |-E t : tSort s.
Proof.
  intros Σ wfΣ Γ Δ t s h.
  destruct (rdx_inversion_it_mkProd_or_LetIn_le Δ Γ t (tSort s) s h (typing_ws_cumul_pbE (le := Cumul) h))
    as [X [hX cX]].
  apply (type_ws_cumul_pb (pb := Cumul) X hX); [|exact cX].
  apply isType_Sort; [exact (typing_wf_sort_proved wfΣ h)|exact (typingE_wf_local hX)].
Qed.

(** ** K7 substitution and spine facts: T0 rows 30, 31, 14, 34, 27, 2, 6 (helpers [sbs_*]) *)

(** [PCUICSubstitution.subslet_untyped_subslet] over [subsletE]. *)
Lemma sbs_subsletE_untyped {cf : checker_flags} {Σ : global_env_ext} {Γ s Δ} :
  subsletE Σ Γ s Δ -> PCUICSubstitution.untyped_subslet Γ s Δ.
Proof. induction 1; constructor; auto. Qed.

(** [PCUICSubstitution.subslet_nth_error] over [subsletE]. *)
Lemma sbs_subsletE_nth_error {cf : checker_flags} {Σ Γ s Δ decl n} :
  subsletE Σ Γ s Δ ->
  nth_error Δ n = Some decl ->
  ∑ t, nth_error s n = Some t ×
  let ty := subst0 (skipn (S n) s) (decl_type decl) in
  Σ ;;; Γ |-E t : ty ×
  match decl_body decl return Type with
  | Some t' =>
    let b := subst0 (skipn (S n) s) t' in
    (t = b)
  | None => unit
  end.
Proof.
  intros h; induction h as [|Δ s na t T h IH ht|Δ s na t T h IH ht] in n |- *.
  - intros hn. rewrite nth_error_nil in hn. discriminate.
  - destruct n as [|n]; cbn.
    + intros [= <-]. exists t. split; [reflexivity|]. cbn. split; [exact ht|exact tt].
    + intros hn. exact (IH n hn).
  - destruct n as [|n]; cbn.
    + intros [= <-]. exists (subst0 s t). split; [reflexivity|]. cbn. split; [exact ht|reflexivity].
    + intros hn. exact (IH n hn).
Qed.

(** The terms of a [subsletE] are open in its context. *)
Lemma sbs_subsletE_open {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ s Δ} :
  subsletE Σ Γ s Δ -> forallb (is_open_term Γ) s.
Proof.
  intros h; induction h as [|Δ s na t T h IH ht|Δ s na t T h IH ht]; cbn [forallb].
  - reflexivity.
  - rewrite IH andb_true_r. exact (subject_is_open_termE ht).
  - rewrite IH andb_true_r. exact (subject_is_open_termE ht).
Qed.

Section SbsSigma.
  Local Open Scope sigma_scope.
  Local Set Keyed Unification.

  (** [PCUICSubstitution.subslet_well_subst] over [subsletE] / [well_substE]; base's proof. *)
  Lemma sbs_subslet_well_substE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Γ' s Δ} :
    subsletE Σ Γ s Γ' ->
    wf_localE Σ (Γ ,,, subst_context s 0 Δ) ->
    well_substE Σ (Γ ,,, Γ' ,,, Δ) (⇑^#|Δ| (s ⋅n ids)) (Γ ,,, subst_context s 0 Δ).
  Proof.
    intros hs hsΔ. split.
    2: exact (PCUICSubstitution.subslet_usubst (sbs_subsletE_untyped hs)).
    intros x decl hx. rewrite PCUICInstConv.lift0_inst inst_assoc. revert hx.
    case: nth_error_app_context => //.
    { intros d hnth hn [= ->].
      rewrite {1}Upn_eq subst_consn_lt; len => //. rewrite /subst_fn.
      rewrite idsn_lt //.
      eapply meta_convE.
      - econstructor; auto.
        rewrite nth_error_app_lt; len => //.
        now rewrite PCUICSubstitution.nth_error_subst_context hnth.
      - rewrite /subst_decl. simpl.
        sigma. rewrite -shiftk_shift -subst_compose_assoc -shiftk_shift.
        rewrite subst_shift_comm.
        rewrite -subst_fn_subst_consn. lia_f_equal. }
    { intros n hnth; len; intros hd [= ->].
      pose proof (subslet_length hs) as H.
      move: hnth; case: nth_error_app_context => //.
      * intros n hnth hx [= ->].
        rewrite {1}Upn_eq subst_consn_ge; len => //; try lia.
        rewrite subst_consn_compose.
        rewrite subst_consn_lt; len; try lia.
        unfold subst_fn. rewrite nth_error_map.
        destruct (sbs_subsletE_nth_error hs hnth) as [t [hnths [hty hb]]].
        rewrite hnths /=. sigma in hty.
        eapply meta_convE in hty.
        2:now rewrite skipn_subst ?Upn_0; try lia.
        eapply (shift_typingE (Δ := subst_context s 0 Δ)) in hty.
        2:tas.
        2:now len.
        rewrite inst_assoc in hty.
        rewrite Upn_eq.
        eapply meta_convE; eauto.
        eapply inst_ext.
        rewrite (shift_subst_consn_ge (S x)); len; try lia.
        rewrite subst_compose_assoc.
        now replace (S x - #|Δ|) with (S (x - #|Δ|)) by lia.
      * intros n hnth hn [= ->].
        eapply meta_conv_allE.
        2:reflexivity.
        2:{ rewrite Upn_subst_consn_ge; try lia. rewrite compose_ids_l.
            instantiate (1 := tRel (x - #|s|)).
            rewrite /shiftk. lia_f_equal. }
        2:{ econstructor; eauto. }
        eapply meta_convE.
        { econstructor; tas.
          rewrite nth_error_app_context_ge; len; try lia.
          rewrite H. erewrite <- hnth. lia_f_equal. }
        rewrite PCUICInstConv.lift0_inst.
        rewrite Upn_eq.
        rewrite shift_subst_consn_ge; len; try lia.
        rewrite subst_consn_compose shift_subst_consn_ge; len; try lia.
        rewrite H. rewrite shiftk_compose. lia_f_equal.
    }
  Qed.
End SbsSigma.

(** *** Row 31: [substitution_wf_local] (base [PCUICSubstitution.All_local_env_inst], over [type_instE]) *)
Lemma substitution_wf_local_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {Γ' : context} {s : list term} {Δ : list context_decl}, subsletE Σ Γ s Γ' -> wf_localE Σ (Γ,,, Γ',,, Δ) -> wf_localE Σ (Γ,,, subst_context s 0 Δ).
Proof.
  intros Σ wfΣ Γ Γ' s Δ hs wf.
  pose proof (env_propE_wf_local type_instE Σ wfΣ _ wf) as X. cbv beta in X.
  eapply All_local_env_app_inv in X as [_ XΔ].
  have wfΓ : wf_localE Σ Γ.
  { apply wf_localE_app_l in wf. exact (wf_localE_app_l _ _ _ wf). }
  rewrite PCUICInstConv.subst_context_inst_context.
  eapply (wf_local_app_instE _ (Γ ,,, Γ')); [exact XΔ| |exact wfΓ].
  pose proof (sbs_subslet_well_substE (Δ := []) hs) as hw.
  rewrite subst_context_nil in hw. exact (hw wfΓ).
Qed.

(** *** Row 30: [substitution] (base [PCUICSubstitution.substitution_prop]: [type_inst] + [subslet_well_subst]) *)
Lemma substitution_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {Γ' : context} {s : list term} {Δ : list context_decl} {t : term} {T : term}, subsletE Σ Γ s Γ' -> Σ;;; Γ,,, Γ',,, Δ |-E t : T -> Σ;;; Γ,,, subst_context s 0 Δ |-E subst s #|Δ| t : subst s #|Δ| T.
Proof.
  intros Σ wfΣ Γ Γ' s Δ t T hs ht.
  pose proof (substitution_wf_local_proved (wfΣ := wfΣ) hs (typingE_wf_local ht)) as wfΔ.
  rewrite !subst_inst.
  exact (typing_instE Σ _ t T _ _ wfΔ (sbs_subslet_well_substE hs wfΔ) ht).
Qed.

(** [PCUICSubstitution.isType_subst] over E. *)
Lemma sbs_isType_subst {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Δ s T} :
  subsletE Σ Γ s Δ -> isTypeE Σ (Γ ,,, Δ) T -> isTypeE Σ Γ (subst0 s T).
Proof.
  intros hs (_ & u & hu & _).
  apply (has_sort_isTypeE u).
  exact (substitution_proved (Δ := []) hs hu).
Qed.

(** *** Row 14: [isType_apply] ([PCUICArities.isType_apply]: [isType_tProd] + [isType_subst]) *)
Lemma isType_apply_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {na : aname} {A : term} {B : term} {t : term}, isTypeE Σ Γ (tProd na A B) -> Σ;;; Γ |-E t : A -> isTypeE Σ Γ (B {0 := t}).
Proof.
  intros Σ wfΣ Γ na A B t (_ & s & hs & _) ht.
  destruct (inversion_Prod Σ wfΣ hs) as (s1 & s2 & _ & hB & _).
  apply (has_sort_isTypeE s2).
  exact (substitution_proved (Γ' := [vass na A]) (Δ := []) (subslet_ass_tip ht) hB).
Qed.

(** *** Row 34: [typing_spine_strengthen] (the head cumulativity composes: [ws_cumul_pbE_trans]) *)
Lemma typing_spine_strengthen_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {T : term} {args : list term} {U : term}, typing_spineE Σ Γ T args U -> forall T' : term, isTypeE Σ Γ T' -> Σ ;;; Γ ⊢E T' ≤ T -> typing_spineE Σ Γ T' args U.
Proof.
  intros Σ wfΣ Γ T args U sp.
  destruct sp as [ty ty' isty isty' c'|ty hd tl na A B B' isty isP c' hhd sp]; intros T' isT' c.
  - exact (type_spine_nilE Σ Γ T' ty' isT' isty'
      (@ws_cumul_pbE_trans _ Σ (wfE_ClosedBodies Σ) Cumul Γ _ _ _ c c')).
  - exact (type_spine_consE Σ Γ T' hd tl na A B B' isT' isP
      (@ws_cumul_pbE_trans _ Σ (wfE_ClosedBodies Σ) Cumul Γ _ _ _ c c') hhd sp).
Qed.

(** *** Row 27: [spine_subst_cumul] ([PCUICSpine.subslet_cumul] + [spine_subst_cumul]) *)
Lemma sbs_subsletE_vass_inv {cf : checker_flags} {Σ Γ args Δ na T} :
  subsletE Σ Γ args (Δ ,, vass na T) ->
  ∑ t s, (args = t :: s) × subsletE Σ Γ s Δ × (Σ ;;; Γ |-E t : subst0 s T).
Proof.
  intros h. DepElim.depelim h. eexists _, _. split; [reflexivity|split; eassumption].
Qed.

Lemma sbs_context_subst_cumul {cf : checker_flags} {Σ : global_env_ext} {pb Δ Γ Γ' args s} :
  PCUICLiftSubst.assumption_context Γ -> PCUICLiftSubst.assumption_context Γ' ->
  ws_cumul_ctx_pbE_rel pb Σ Δ Γ Γ' ->
  context_subst Γ args s -> context_subst Γ' args s.
Proof.
  intros ass ass' [_ hA].
  induction hA as [|d d' Γ0 Γ0' hA IH p] in args, s, ass, ass' |- *; intros ctxs.
  - exact ctxs.
  - destruct d as [na [b|] T]; [exfalso; inversion ass|].
    destruct d' as [na' [b'|] T']; [exfalso; inversion ass'|].
    have ass0 : PCUICLiftSubst.assumption_context Γ0 by inversion ass.
    have ass0' : PCUICLiftSubst.assumption_context Γ0' by inversion ass'.
    DepElim.depelim ctxs. constructor. eapply IH; eassumption.
Qed.

Lemma sbs_subsletE_cumul {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {pb Δ args Γ Γ'} :
  PCUICLiftSubst.assumption_context Γ -> PCUICLiftSubst.assumption_context Γ' ->
  wf_localE Σ (Δ ,,, Γ) -> wf_localE Σ (Δ ,,, Γ') ->
  ws_cumul_ctx_pbE_rel pb Σ Δ Γ Γ' ->
  subsletE Σ Δ args Γ -> subsletE Σ Δ args Γ'.
Proof.
  intros ass ass' wf wf' [cl hA].
  induction hA as [|d d' Γ0 Γ0' hA IH p] in args, ass, ass', wf, wf' |- *; intros subsl.
  - exact subsl.
  - destruct d as [na [b|] T]; [exfalso; inversion ass|].
    destruct d' as [na' [b'|] T']; [exfalso; inversion ass'|].
    have ass0 : PCUICLiftSubst.assumption_context Γ0 by inversion ass.
    have ass0' : PCUICLiftSubst.assumption_context Γ0' by inversion ass'.
    destruct (sbs_subsletE_vass_inv subsl) as (t & s & -> & subsl' & ht).
    destruct (All_local_env_tip wf) as [wf0 _].
    destruct (All_local_env_tip wf') as [wf0' hT'].
    have subsl'' : subsletE Σ Δ s Γ0'.
    { eapply IH; eassumption. }
    constructor; [exact subsl''|].
    DepElim.depelim p.
    apply (type_ws_cumul_pb (pb := pb) (subst0 s T) ht).
    + destruct hT' as (_ & u & hu & _).
      apply (has_sort_isTypeE u).
      exact (substitution_proved (Δ := []) subsl'' hu).
    + refine (untyped_substitution_ws_cumul_pbE (Γ'' := []) (M := T) (N := T')
        (sbs_subsletE_untyped subsl') (sbs_subsletE_open subsl') _).
      eassumption.
Qed.

Lemma spine_subst_cumul_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Δ : list context_decl} {args : list term} {Γ : context} {Γ' : context}, PCUICLiftSubst.assumption_context Γ -> PCUICLiftSubst.assumption_context Γ' -> wf_localE Σ (Δ,,, Γ) -> wf_localE Σ (Δ,,, Γ') -> ws_cumul_ctx_pbE_rel Cumul Σ Δ Γ Γ' -> spine_substE Σ Δ args (List.rev args) Γ -> spine_substE Σ Δ args (List.rev args) Γ'.
Proof.
  intros Σ wfΣ Δ args Γ Γ' ass ass' wf wf' a2 [wfΔ _ ctxs subsl].
  split.
  - exact wfΔ.
  - exact wf'.
  - exact (sbs_context_subst_cumul ass ass' a2 ctxs).
  - exact (sbs_subsletE_cumul ass ass' wf wf' a2 subsl).
Qed.

(** *** Row 6: [ctx_inst_spine_subst] ([PCUICSpine.ctx_inst_spine_subst]) *)

(** [PCUICSubstitution.subslet_def_tip] over [subsletE]. *)
Lemma sbs_subslet_def_tip {cf : checker_flags} {Σ : global_env_ext} {Γ na t T} :
  Σ ;;; Γ |-E t : T -> subsletE Σ Γ [t] [vdef na t T].
Proof.
  intros h. rewrite -{1}(subst_empty 0 t).
  apply cons_let_defE; [constructor|]. now rewrite !subst_empty.
Qed.

(** The substitution of a [ctx_instE] over a reversed context is a [subsletE]
    (the [subslet] half of [PCUICSpine.ctx_inst_spine_subst], by induction on the instance). *)
Lemma sbs_ctx_inst_subslet {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ args Δt}
  (ci : ctx_instE Σ Γ args Δt) :
  wf_localE Σ (Γ ,,, List.rev Δt) -> subsletE Σ Γ (ctx_inst_subE ci) (List.rev Δt).
Proof.
  induction ci as [|na t i inst Δt hi ci IH|na b t inst Δt ci IH]; intros wf;
    cbn [ctx_inst_subE List.rev] in *.
  - constructor.
  - have e : List.rev (subst_telescope [i] 0 Δt) = subst_context [i] 0 (List.rev Δt).
    { rewrite -{1}(List.rev_involutive Δt) subst_telescope_subst_context. apply List.rev_involutive. }
    have hs : subsletE Σ Γ [i] [vass na t] := subslet_ass_tip hi.
    have wf' : wf_localE Σ (Γ ,,, [vass na t] ,,, List.rev Δt) by rewrite -app_context_assoc.
    rewrite e in IH.
    exact (stc_subsletE_app _ _ _ _ _ _ (IH (substitution_wf_local_proved (wfΣ := wfΣ) hs wf')) hs).
  - have wfd : wf_localE Σ (Γ ,,, [vdef na b t] ,,, List.rev Δt) by rewrite -app_context_assoc.
    destruct (All_local_env_tip (wf_localE_app_l _ _ _ wfd)) as [_ hd0].
    have hb : Σ ;;; Γ |-E b : t by destruct hd0 as (hb & _).
    have hs : subsletE Σ Γ [b] [vdef na b t] := sbs_subslet_def_tip hb.
    have e : List.rev (subst_telescope [b] 0 Δt) = subst_context [b] 0 (List.rev Δt).
    { rewrite -{1}(List.rev_involutive Δt) subst_telescope_subst_context. apply List.rev_involutive. }
    rewrite e in IH.
    exact (stc_subsletE_app _ _ _ _ _ _ (IH (substitution_wf_local_proved (wfΣ := wfΣ) hs wfd)) hs).
Qed.

Lemma ctx_inst_spine_subst_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {Δ : list context_decl} {args : list term}, wf_localE Σ (Γ,,, Δ) -> forall (ci : ctx_instE Σ Γ args (List.rev Δ)), spine_substE Σ Γ args (ctx_inst_subE ci) Δ.
Proof.
  intros Σ wfΣ Γ Δ args wf ci.
  pose proof (make_context_subst_spec _ _ _ (stc_ctx_inst_subE_spec ci)) as msub.
  rewrite List.rev_involutive in msub.
  pose proof (sbs_ctx_inst_subslet (wfΣ := wfΣ) ci) as hs.
  rewrite List.rev_involutive in hs.
  split.
  - exact (wf_localE_app_l _ _ _ wf).
  - exact wf.
  - exact msub.
  - exact (hs wf).
Qed.

(** *** Row 2: [arity_typing_spine] ([PCUICSpine.arity_typing_spine]) *)

(** [PCUICArities.isType_tLetIn_red] over E: substitution (row 30), [ws_cumul_pbE_LetIn_l_inv],
    [type_ws_cumul_pb], and [typing_wf_sort_proved] (row 35) for the target sort; no
    [ws_cumul_pb_Sort_r_inv]. *)
Lemma sbs_isType_tLetIn_red {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ na t A B} :
  isTypeE Σ Γ (tLetIn na t A B) -> isTypeE Σ Γ (B {0 := t}).
Proof.
  intros (_ & s & H & _).
  pose proof (typing_wf_sort_proved (Σ := Σ) wfΣ H) as ws.
  destruct (inversion_LetIn Σ wfΣ H) as (A' & hb & HB & c).
  assert (ht : Σ ;;; Γ |-E t : A) by (destruct hb as (ht & _); exact ht).
  assert (HB' : Σ ;;; Γ |-E B {0 := t} : A' {0 := t}).
  { exact (substitution_proved (wfΣ := wfΣ) (Γ' := [vdef na t A]) (Δ := []) (sbs_subslet_def_tip ht) HB). }
  apply (has_sort_isTypeE s).
  exact (type_ws_cumul_pb (pb := Cumul) (A' {0 := t}) HB' (isType_Sort ws (typingE_wf_local HB'))
    (ws_cumul_pbE_LetIn_l_inv c)).
Qed.

(** [PCUICArities.typing_spine_letin_inv] over E. *)
Lemma sbs_typing_spine_letin_inv {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ na b B T args S} :
  typing_spineE Σ Γ (tLetIn na b B T) args S -> typing_spineE Σ Γ (T {0 := b}) args S.
Proof.
  intros Hsp. remember (tLetIn na b B T) as L eqn:eL. revert eL.
  destruct Hsp as [ty ty' isty isty' c|ty hd tl na' A B0 B' isty isP c hhd sp]; intros ->.
  - exact (type_spine_nilE Σ Γ _ ty' (sbs_isType_tLetIn_red isty) isty' (ws_cumul_pbE_LetIn_l_inv c)).
  - exact (type_spine_consE Σ Γ _ hd tl na' A B0 B' (sbs_isType_tLetIn_red isty) isP
      (ws_cumul_pbE_LetIn_l_inv c) hhd sp).
Qed.

Lemma sbs_context_subst_def_tip na b ty : context_subst [vdef na b ty] [] [b].
Proof. rewrite -{2}(subst_empty 0 b). exact (context_subst_def [] [] [] na b ty context_subst_nil). Qed.

Lemma sbs_context_subst_ass_tip na ty a : context_subst [vass na ty] [a] [a].
Proof. exact (context_subst_ass [] [] [] na ty a context_subst_nil). Qed.

Lemma arity_typing_spine_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {Γ' : context} {s : sort} {inst : list term} {s' : sort}, typing_spineE Σ Γ (it_mkProd_or_LetIn Γ' (tSort s)) inst (tSort s') -> [× #|inst| = context_assumptions Γ', leq_sort Σ s s' & ∑ instsubst : list term, spine_substE Σ Γ inst instsubst Γ'].
Proof.
  intros Σ wfΣ Γ Γ' s inst s' Hsp. revert s inst s' Hsp.
  induction Γ' as [|d l IH] using PCUICInduction.ctx_length_rev_ind; intros s inst s' Hsp.
  - have Hsp0 : typing_spineE Σ Γ (tSort s) inst (tSort s') := Hsp.
    clear Hsp.
    remember (tSort s) as S0 eqn:eS. remember (tSort s') as S1 eqn:eS'. revert eS eS'.
    destruct Hsp0 as [ty ty' isty isty' c|ty hd tl na A B B' isty isP c hhd sp]; intros -> ->.
    + split; [reflexivity|exact (ws_cumul_pb_Sort_inv Cumul c)|].
      exists []. split; [exact (isType_wf_local isty)|exact (isType_wf_local isty)|constructor|constructor].
    + exfalso. exact (ws_cumul_pb_Sort_Prod_inv Cumul c).
  - pose proof (isType_it_mkProd_or_LetIn_wf_local_proved (wfΣ := wfΣ) (typing_spine_isType_dom Hsp)) as wfΓ'.
    have wfd : wf_localE Σ (Γ ,,, [d] ,,, l) by rewrite -app_context_assoc.
    destruct (All_local_env_tip (wf_localE_app_l _ _ _ wfd)) as [_ hd0].
    rewrite it_mkProd_or_LetIn_app in Hsp.
    destruct d as [na [b|] ty].
    + have hb : Σ ;;; Γ |-E b : ty by destruct hd0 as (hb & _).
      have Hsp1 : typing_spineE Σ Γ (tLetIn na b ty (it_mkProd_or_LetIn l (tSort s))) inst (tSort s') := Hsp.
      pose proof (sbs_typing_spine_letin_inv (wfΣ := wfΣ) Hsp1) as Hsp2.
      rewrite /subst1 subst_it_mkProd_or_LetIn in Hsp2.
      have Hsp3 : typing_spineE Σ Γ (it_mkProd_or_LetIn (subst_context [b] 0 l) (tSort s)) inst (tSort s') := Hsp2.
      destruct (IH (subst_context [b] 0 l) ltac:(rewrite subst_context_length; lia) _ _ _ Hsp3)
        as [instlen leq [instsubst [wfdom _ cs subi]]].
      rewrite context_assumptions_subst in instlen.
      have hl : #|instsubst| = #|l| by rewrite -(context_subst_length cs) subst_context_length.
      split.
      * rewrite context_assumptions_app /=. lia.
      * exact leq.
      * exists (instsubst ++ [b]). split.
        -- exact wfdom.
        -- exact wfΓ'.
        -- apply context_subst_app_inv.
           rewrite -hl skipn_all_app firstn_app_left //.
           split; [exact cs|exact (sbs_context_subst_def_tip na b ty)].
        -- exact (stc_subsletE_app _ _ _ _ _ _ subi (sbs_subslet_def_tip hb)).
    + have Hsp1 : typing_spineE Σ Γ (tProd na ty (it_mkProd_or_LetIn l (tSort s))) inst (tSort s') := Hsp.
      clear Hsp.
      remember (tProd na ty (it_mkProd_or_LetIn l (tSort s))) as P0 eqn:eP.
      remember (tSort s') as S1 eqn:eS'. revert eP eS'.
      destruct Hsp1 as [ty0 ty' isty isty' c|ty0 hd tl na0 A B B' isty isP c hhd sp]; intros -> ->.
      * exfalso. exact (ws_cumul_pb_Prod_Sort_inv Cumul c).
      * destruct (ws_cumul_pb_Prod_Prod_inv c) as [eqna conva cumulB].
        assert (isty0 : isTypeE Σ Γ ty).
        { destruct isty as (_ & u & hu & _).
          destruct (inversion_Prod Σ wfΣ hu) as (s1 & s2 & hA & _ & _).
          destruct hA as (_ & u1 & hu1 & _). exact (has_sort_isTypeE u1 hu1). }
        assert (hdty : Σ ;;; Γ |-E hd : ty).
        { exact (type_ws_cumul_pb (pb := Conv) A hhd isty0 (ws_cumul_pbE_sym_pb conva)). }
        assert (cumulB' : Σ ;;; Γ ⊢E (it_mkProd_or_LetIn l (tSort s)) {0 := hd} ≤ B {0 := hd}).
        { exact (substitution0_ws_cumul_pbE (subject_is_open_termE hdty) cumulB). }
        pose proof (typing_spine_strengthen_proved (wfΣ := wfΣ) sp _
          (isType_apply_proved (wfΣ := wfΣ) isty hdty) cumulB') as sp1.
        rewrite /subst1 subst_it_mkProd_or_LetIn in sp1.
        have sp2 : typing_spineE Σ Γ (it_mkProd_or_LetIn (subst_context [hd] 0 l) (tSort s)) tl (tSort s') := sp1.
        destruct (IH (subst_context [hd] 0 l) ltac:(rewrite subst_context_length; lia) _ _ _ sp2)
          as [instlen leq [instsubst [wfdom _ cs subi]]].
        rewrite context_assumptions_subst in instlen.
        have hl : #|instsubst| = #|l| by rewrite -(context_subst_length cs) subst_context_length.
        split.
        -- rewrite context_assumptions_app /=. lia.
        -- exact leq.
        -- exists (instsubst ++ [hd]). split.
           ++ exact wfdom.
           ++ exact wfΓ'.
           ++ apply context_subst_app_inv.
              rewrite -hl skipn_all_app firstn_app_left //.
              split; [exact cs|exact (sbs_context_subst_ass_tip na ty hd)].
           ++ exact (stc_subsletE_app _ _ _ _ _ _ subi (subslet_ass_tip hdty)).
Qed.

(** ** K7 smash and expand_lets facts: T0 rows 44, 45, 32, 43, 28, 18 (helpers [smh_*])

  Ports of base [PCUICContexts] ([wf_local_rel_smash_context_gen], [wf_local_smash_end],
  [wf_local_smash_context], [subslet_lift], [subslet_extended_subst], [typing_expand_lets]),
  [PCUICInductives.wf_local_expand_lets], [PCUICSpine.spine_subst_smash] and
  [PCUICFixWitness] ([wf_local_nth_error_welltyped], [isType_rec_arg_welltyped]) over [typingE].
  The only non-structural step of these ports is substitution (row 30, [substitution_proved]). *)

(** [PCUICContexts.wf_local_rel_smash_context_gen] over [typingE]. *)
Lemma smh_wf_local_rel_smash_context_gen {cf : checker_flags}
  {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Δ Δ'} :
  wf_localE Σ (Δ' ,,, Γ) ->
  wf_local_relE Σ (Δ' ,,, Γ) Δ ->
  wf_local_relE Σ Δ' (smash_context Δ Γ).
Proof.
  rewrite /wf_local_relE.
  induction Γ as [|a Γ IHΓ] in Δ |- *; simpl; auto.
  intros wfΓ wfΔ.
  destruct (All_local_env_tip wfΓ) as [wfΓ' ha].
  destruct a as [na [b|] t]; simpl.
  - apply IHΓ; auto.
    apply All_local_env_fold, All_local_env_impl with (1 := wfΔ).
    intros Γ' j X.
    apply lift_typing_f_impl with (1 := X) => // ?? HT.
    rewrite Nat.add_0_r.
    have sub : subsletE Σ (Δ' ,,, Γ) [b] [vdef na b t].
    { rewrite -{1}(subst_empty 0 b). constructor; [constructor|].
      rewrite !subst_empty. eapply unlift_TermTyp; exact ha. }
    exact (@substitution_proved cf Σ wfΣ _ _ _ _ _ _ sub HT).
  - apply IHΓ; auto. eapply All_local_env_app; auto.
    + constructor; [constructor|exact ha].
    + eapply All_local_env_impl; eauto. simpl; intros.
      now rewrite app_context_assoc.
Qed.

(** [PCUICContexts.wf_local_smash_end] over [typingE]. *)
Lemma smh_wf_local_smash_end {cf : checker_flags}
  {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ Δ : list context_decl) :
  wf_localE Σ (Γ ,,, Δ) -> wf_localE Σ (Γ ,,, smash_context [] Δ).
Proof.
  intros wf.
  apply All_local_env_app.
  - exact (fst (All_local_env_app_inv wf)).
  - eapply (smh_wf_local_rel_smash_context_gen (wfΣ := wfΣ)); [exact wf|constructor].
Qed.

(** [smash_context] of a context ending in an assumption (syntactic). *)
Lemma smh_smash_context_acc_vass Δ na T :
  smash_context [mkdecl na None T] Δ =
  smash_context [] Δ ,, vass na (subst (extended_subst Δ 0) 0 (lift (context_assumptions Δ) #|Δ| T)).
Proof. rewrite smash_context_acc. reflexivity. Qed.

Lemma smh_smash_context_vass Δ na T :
  smash_context [] (Δ ,, vass na T) =
  smash_context [] Δ ,, vass na (subst (extended_subst Δ 0) 0 (lift (context_assumptions Δ) #|Δ| T)).
Proof. exact (smh_smash_context_acc_vass Δ na T). Qed.

(** [PCUICContexts.subslet_lift] over [typingE] (no substitution: [weakeningE]). *)
Lemma smh_subslet_lift {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
  (Γ Δ : context) s Δ' :
  wf_localE Σ (Γ ,,, Δ) ->
  subsletE Σ Γ s Δ' ->
  subsletE Σ (Γ ,,, Δ) (map (lift0 #|Δ|) s) (lift_context #|Δ| 0 Δ').
Proof.
  move=> wfl sub.
  induction sub as [|Δ0 s0 na t T sub IH ht|Δ0 s0 na t T sub IH ht];
    rewrite ?lift_context_snoc /=.
  - constructor.
  - rewrite -(subslet_length sub). constructor; [exact IH|].
    rewrite -distr_lift_subst. apply weakeningE; eauto.
  - rewrite -(subslet_length sub).
    rewrite distr_lift_subst. constructor; [exact IH|].
    rewrite - !distr_lift_subst. apply weakeningE; eauto.
Qed.

(** [PCUICContexts.subslet_extended_subst] over [typingE]. *)
Lemma smh_subslet_extended_subst {cf : checker_flags}
  {Σ : global_env_ext} {wfΣ : wfE Σ} Γ Δ :
  wf_localE Σ (Γ ,,, Δ) ->
  subsletE Σ (Γ ,,, smash_context [] Δ)
    (extended_subst Δ 0)
    (lift_context (context_assumptions Δ) 0 Δ).
Proof.
  move=> wfΔ.
  have wfΓ := fst (All_local_env_app_inv wfΔ).
  have wfΔ' := snd (All_local_env_app_inv wfΔ).
  clear wfΔ.
  induction Δ as [|[na [d|] ty] Δ IHΔ] in wfΔ' |- *; simpl; try constructor.
  * destruct (All_local_rel_tip wfΔ') as [wfΔt l0].
    have wfΓΔ : wf_localE Σ (Γ ,,, Δ) := All_local_env_app wfΓ wfΔt.
    specialize (IHΔ wfΔt).
    rewrite lift_context_snoc /lift_decl /= /map_decl /=.
    len.
    constructor => //.
    have l : Σ ;;; Γ ,,, Δ |-E d : ty by eapply unlift_TermTyp; exact l0.
    have wfs := smh_wf_local_smash_end (wfΣ := wfΣ) Γ Δ wfΓΔ.
    have l' := weakening_typingE (wfΣ := wfΣ) (Γ' := Δ) (Γ'' := smash_context [] Δ) wfs l.
    len in l'.
    exact (@substitution_proved cf Σ wfΣ _ _ _ [] _ _ IHΔ l').
  * rewrite (smh_smash_context_acc_vass Δ na ty).
    destruct (All_local_rel_tip wfΔ') as [wfΔt l].
    have wfΓΔ : wf_localE Σ (Γ ,,, Δ) := All_local_env_app wfΓ wfΔt.
    specialize (IHΔ wfΔt).
    rewrite lift_context_snoc /lift_decl /= /map_decl /=.
    have wfs := smh_wf_local_smash_end (wfΣ := wfΣ) Γ Δ wfΓΔ.
    assert (wf_localE Σ (Γ ,,, smash_context [] Δ ,, vass na
        (subst0 (extended_subst Δ 0) (lift (context_assumptions Δ) #|Δ| ty)))) as wfs'.
    { constructor; [exact wfs|].
      eapply lift_typing_f_impl with (f := fun t => _ (_ t)) (1 := l) => // ?? Hs.
      have Hs' := weakening_typingE (wfΣ := wfΣ) (Γ' := Δ) (Γ'' := smash_context [] Δ) wfs Hs.
      len in Hs'.
      exact (@substitution_proved cf Σ wfΣ _ _ _ [] _ _ IHΔ Hs'). }
    constructor.
    - rewrite (lift_extended_subst _ 1).
      rewrite -(PCUICWeakeningConv.lift_context_lift_context 1 _).
      exact (smh_subslet_lift _ [_] _ _ wfs' IHΔ).
    - eapply meta_convE.
      + econstructor; [exact wfs'|reflexivity].
      + simpl. rewrite (lift_extended_subst _ 1).
        rewrite distr_lift_subst. f_equal. len.
        now rewrite simpl_lift; try lia.
Qed.

(** [PCUICContexts.typing_expand_lets] over [typingE]. *)
Lemma smh_typing_expand_lets {cf : checker_flags}
  {Σ : global_env_ext} {wfΣ : wfE Σ} Γ Δ t T :
  Σ ;;; Γ ,,, Δ |-E t : T ->
  Σ ;;; Γ ,,, smash_context [] Δ |-E expand_lets Δ t : expand_lets Δ T.
Proof.
  intros Ht.
  rewrite /expand_lets /expand_lets_k.
  have wf := typingE_wf_local Ht.
  have wfs := smh_wf_local_smash_end (wfΣ := wfΣ) Γ Δ wf.
  have Ht' := weakening_typingE (wfΣ := wfΣ) (Γ' := Δ) (Γ'' := smash_context [] Δ) wfs Ht.
  len in Ht'.
  exact (@substitution_proved cf Σ wfΣ _ _ _ [] _ _ (smh_subslet_extended_subst (wfΣ := wfΣ) Γ Δ wf) Ht').
Qed.

(** [PCUICInductives.wf_local_expand_lets] over [typingE]. *)
Lemma smh_wf_local_expand_lets {cf : checker_flags}
  {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Δ Γ'} :
  wf_localE Σ (Γ ,,, Δ ,,, Γ') ->
  wf_localE Σ (Γ ,,, smash_context [] Δ ,,, expand_lets_ctx Δ Γ').
Proof.
  intros hwf.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  have wfΓΔ := fst (All_local_env_app_inv hwf).
  rewrite -app_context_assoc in hwf.
  have wfs := smh_wf_local_smash_end (wfΣ := wfΣ) Γ Δ wfΓΔ.
  have hwf' := weakening_wf_localE (wfΣ := wfΣ) (Γ'' := smash_context [] Δ) hwf wfs.
  len in hwf'.
  rewrite lift_context_app app_context_assoc Nat.add_0_r in hwf'.
  exact (substitution_wf_local_proved (wfΣ := wfΣ) (smh_subslet_extended_subst (wfΣ := wfΣ) Γ Δ wfΓΔ) hwf').
Qed.

(** The [context_subst] half of [PCUICSpine.spine_subst_smash] (syntactic). *)
Lemma smh_context_subst_smash {Δ inst s} :
  context_subst Δ inst s -> context_subst (smash_context [] Δ) inst (List.rev inst).
Proof.
  induction 1 as [|Γ' args s' na' t' a' cs IH|Γ' args s' na' b' t' cs IH].
  - constructor.
  - rewrite (smh_smash_context_vass Γ' na' t') List.rev_app_distr /=.
    constructor. exact IH.
  - simpl. exact IH.
Qed.

(** The [subslet] half of [PCUICSpine.spine_subst_smash] over [typingE] (no substitution). *)
Lemma smh_subslet_smash {cf : checker_flags} {Σ : global_env_ext} {Γ Δ inst s} :
  subsletE Σ Γ s Δ -> context_subst Δ inst s -> subsletE Σ Γ (List.rev inst) (smash_context [] Δ).
Proof.
  intros sub.
  induction sub as [|Δ0 s0 na t T sub IH ht|Δ0 s0 na t T sub IH ht] in inst |- *; intros cs.
  - DepElim.depelim cs. constructor.
  - DepElim.depelim cs.
    rewrite (smh_smash_context_vass Δ0 na T) List.rev_app_distr /=.
    constructor; [now apply IH|].
    eapply meta_convE; [exact ht|].
    rewrite distr_subst extended_subst_length Nat.add_0_r simpl_subst_k.
    + rewrite List.length_rev. symmetry. now eapply context_subst_length2.
    + f_equal. now eapply context_subst_subst_extended_subst.
  - DepElim.depelim cs. simpl. now apply IH.
Qed.

(** [PCUICSpine.spine_subst_smash] over [typingE]. *)
Lemma smh_spine_subst_smash {cf : checker_flags}
  {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ inst s Δ} :
  spine_substE Σ Γ inst s Δ ->
  spine_substE Σ Γ inst (List.rev inst) (smash_context [] Δ).
Proof.
  intros [wfΓ wfΓΔ cs sub].
  split.
  - exact wfΓ.
  - exact (smh_wf_local_smash_end (wfΣ := wfΣ) Γ Δ wfΓΔ).
  - exact (smh_context_subst_smash cs).
  - exact (smh_subslet_smash sub cs).
Qed.

(** [PCUICFixWitness.wf_local_nth_error_welltyped] over [typingE] (structural). *)
Lemma smh_wf_local_nth_error_welltyped {cf : checker_flags} {Σ : global_env_ext} {Γ n c} :
  wf_localE Σ Γ ->
  nth_error Γ n = Some c ->
  welltypedE Σ (skipn (S n) Γ) (decl_type c).
Proof.
  induction Γ as [|a Γ ih] in n |- *; intros wf hnth.
  - now rewrite nth_error_nil in hnth.
  - destruct (All_local_env_tip wf) as [wfΓ ha].
    destruct n; cbn in hnth.
    + case: hnth => <-. rewrite skipn_S skipn_0.
      destruct a as [na [b|] ty]; cbn in ha |- *.
      * apply lift_sorting_forget_body in ha.
        now eapply isTypeRelE_welltypedE.
      * now eapply isTypeRelE_welltypedE.
    + rewrite skipn_S. now eapply ih.
Qed.

(** [PCUICFixWitness.isType_rec_arg_welltyped] over [typingE]. *)
Lemma smh_isType_rec_arg_welltyped {cf : checker_flags}
  {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ T ctx concl n c} :
  isTypeE Σ Γ T ->
  decompose_prod_assum [] T = (ctx, concl) ->
  nth_error (List.rev (smash_context [] ctx)) n = Some c ->
  welltypedE Σ (Γ ,,, skipn (#|smash_context [] ctx| - n) (smash_context [] ctx)) (decl_type c).
Proof.
  intros isty decomp hnth.
  have eqty := PCUICSubstitution.decompose_prod_assum_it_mkProd_or_LetIn _ _ _ _ decomp.
  cbn in eqty. rewrite eqty in isty.
  apply (isType_it_mkProd_or_LetIn_wf_local_proved (wfΣ := wfΣ)) in isty.
  apply (smh_wf_local_smash_end (wfΣ := wfΣ)) in isty.
  have hlt : n < #|smash_context [] ctx|.
  { have h := nth_error_Some_length hnth. now rewrite List.length_rev in h. }
  rewrite (nth_error_rev_inv _ _ hlt) in hnth.
  have hnth' : nth_error (Γ ,,, smash_context [] ctx) (#|smash_context [] ctx| - S n) = Some c.
  { rewrite /app_context nth_error_app_lt //. lia. }
  have w := smh_wf_local_nth_error_welltyped isty hnth'.
  rewrite /app_context in w |- *.
  have e : S (#|smash_context [] ctx| - S n) = #|smash_context [] ctx| - n by lia.
  rewrite e skipn_app in w.
  replace (#|smash_context [] ctx| - n - #|smash_context [] ctx|) with 0 in w by lia.
  now rewrite skipn_0 in w.
Qed.

(** *** The rows *)

(** Row 45: [wf_local_smash_end] ([PCUICContexts.wf_local_smash_end]). *)
Lemma wf_local_smash_end_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ Δ : list context_decl), wf_localE Σ (Γ,,, Δ) -> wf_localE Σ (Γ,,, smash_context [] Δ).
Proof. intros Σ wfΣ Γ Δ. exact (smh_wf_local_smash_end (wfΣ := wfΣ) Γ Δ). Qed.

(** Row 44: [wf_local_smash_context] ([PCUICContexts.wf_local_smash_context]: row 45 at [Γ := []]). *)
Lemma wf_local_smash_context_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context}, wf_localE Σ Γ -> wf_localE Σ (smash_context [] Γ).
Proof.
  intros Σ wfΣ Γ wfΓ.
  have h := smh_wf_local_smash_end (wfΣ := wfΣ) [] Γ.
  rewrite !app_context_nil_l in h. exact (h wfΓ).
Qed.

(** Row 32: [typing_expand_lets] ([PCUICContexts.typing_expand_lets]). *)
Lemma typing_expand_lets_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ : list context_decl) (Δ : list context_decl) (t : term) (T : term), Σ;;; Γ,,, Δ |-E t : T -> Σ;;; Γ,,, smash_context [] Δ |-E expand_lets Δ t : expand_lets Δ T.
Proof. intros Σ wfΣ Γ Δ t T. exact (smh_typing_expand_lets (wfΣ := wfΣ) Γ Δ t T). Qed.

(** Row 43: [wf_local_expand_lets] ([PCUICInductives.wf_local_expand_lets]). *)
Lemma wf_local_expand_lets_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {Δ : list context_decl} {Γ' : list context_decl}, wf_localE Σ (Γ,,, Δ,,, Γ') -> wf_localE Σ (Γ,,, smash_context [] Δ,,, expand_lets_ctx Δ Γ').
Proof. intros Σ wfΣ Γ Δ Γ'. exact (smh_wf_local_expand_lets (wfΣ := wfΣ)). Qed.

(** Row 28: [spine_subst_smash] ([PCUICSpine.spine_subst_smash]). *)
Lemma spine_subst_smash_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {inst : list term} {s : list term} {Δ : context}, spine_substE Σ Γ inst s Δ -> spine_substE Σ Γ inst (List.rev inst) (smash_context [] Δ).
Proof. intros Σ wfΣ Γ inst s Δ. exact (smh_spine_subst_smash (wfΣ := wfΣ)). Qed.

(** Row 18: [isType_rec_arg_welltyped] ([PCUICFixWitness.isType_rec_arg_welltyped]). *)
Lemma isType_rec_arg_welltyped_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {T : term} {ctx : context} {concl : term} {n : nat} {c : context_decl}, isTypeE Σ Γ T -> decompose_prod_assum [] T = (ctx, concl) -> nth_error (List.rev (smash_context [] ctx)) n = Some c -> welltypedE Σ (Γ,,, skipn (#|smash_context [] ctx| - n) (smash_context [] ctx)) (decl_type c).
Proof.
  intros Σ wfΣ Γ T ctx concl n c.
  exact (smh_isType_rec_arg_welltyped (wfΣ := wfΣ)).
Qed.


(** *** The former fields, under their names *)
Section ProvedFields.
  Context {cf : checker_flags}.

  Lemma All_mfix_wf :
    forall (Σ : global_env × universes_decl) (Γ : context) (mfix : list (def term)), wfE Σ.1 -> wf_localE Σ Γ -> All (fun d : def term => isTypeRelE Σ Γ (dtype d) (binder_relevance (dname d))) mfix -> wf_localE Σ (Γ,,, fix_context mfix).
  Proof. exact (@All_mfix_wf_proved cf). Qed.

  Lemma arity_typing_spine :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {Γ' : context} {s : sort} {inst : list term} {s' : sort}, typing_spineE Σ Γ (it_mkProd_or_LetIn Γ' (tSort s)) inst (tSort s') -> [× #|inst| = context_assumptions Γ', leq_sort Σ s s' & ∑ instsubst : list term, spine_substE Σ Γ inst instsubst Γ'].
  Proof. exact (@arity_typing_spine_proved cf). Qed.

  Lemma ctx_inst_open_terms :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ : context) (args : list term) (Δ : context), ctx_instE Σ Γ args Δ -> All (fun t : term => on_free_vars (shiftnP #|Γ| xpred0) t) args.
  Proof. exact (@ctx_inst_open_terms_proved cf). Qed.

  Lemma ctx_inst_smash :
    forall {Σ : global_env_ext} {Γ : context} {i : list term} {Δ : list context_decl}, ctx_instE Σ Γ i (List.rev Δ) <~> ctx_instE Σ Γ i (List.rev (smash_context [] Δ)).
  Proof. exact (@ctx_inst_smash_proved cf). Qed.

  Lemma ctx_inst_spine_subst :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {Δ : list context_decl} {args : list term}, wf_localE Σ (Γ,,, Δ) -> forall (ci : ctx_instE Σ Γ args (List.rev Δ)), spine_substE Σ Γ args (ctx_inst_subE ci) Δ.
  Proof. exact (@ctx_inst_spine_subst_proved cf). Qed.

  Lemma ind_arity_relevant :
    forall (Σ : global_env_ext) (mdecl : mutual_inductive_body) (idecl : one_inductive_body), wfE Σ.1 -> let ind_type := it_mkProd_or_LetIn (ind_params mdecl) (it_mkProd_or_LetIn (ind_indices idecl) (tSort (ind_sort idecl))) in isTypeE Σ [] ind_type -> isTypeRelE Σ [] ind_type rel_of_Type.
  Proof. exact (@ind_arity_relevant_proved cf). Qed.

  Lemma inversion_it_mkProd_or_LetIn :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {Δ : context} {t : term} {s : sort}, Σ;;; Γ |-E it_mkProd_or_LetIn Δ t : tSort s -> Σ;;; Γ,,, Δ |-E t : tSort s.
  Proof. exact (@inversion_it_mkProd_or_LetIn_proved cf). Qed.

  Lemma isTypeRel_lift :
    forall {Σ : global_env_ext} {n : nat} {Γ : list context_decl} {ty : term} {r : relevance} (isdecl : n <= #|Γ|), wfE Σ -> wf_localE Σ Γ -> isTypeRelE Σ (skipn n Γ) ty r -> isTypeRelE Σ Γ (lift0 n ty) r.
  Proof. exact (@isTypeRel_lift_proved cf). Qed.

  Lemma isType_lift :
    forall {Σ : global_env_ext} {n : nat} {Γ : list context_decl} {ty : term} (isdecl : n <= #|Γ|), wfE Σ -> wf_localE Σ Γ -> isTypeE Σ (skipn n Γ) ty -> isTypeE Σ Γ (lift0 n ty).
  Proof. exact (@isType_lift_proved cf). Qed.

  Lemma isType_apply :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {na : aname} {A : term} {B : term} {t : term}, isTypeE Σ Γ (tProd na A B) -> Σ;;; Γ |-E t : A -> isTypeE Σ Γ (B {0 := t}).
  Proof. exact (@isType_apply_proved cf). Qed.

  Lemma isType_it_mkProd_or_LetIn_wf_local :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {Δ : context} {T : term}, isTypeE Σ Γ (it_mkProd_or_LetIn Δ T) -> wf_localE Σ (Γ,,, Δ).
  Proof. exact (@isType_it_mkProd_or_LetIn_wf_local_proved cf). Qed.

  Lemma isType_rec_arg_welltyped :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {T : term} {ctx : context} {concl : term} {n : nat} {c : context_decl}, isTypeE Σ Γ T -> decompose_prod_assum [] T = (ctx, concl) -> nth_error (List.rev (smash_context [] ctx)) n = Some c -> welltypedE Σ (Γ,,, skipn (#|smash_context [] ctx| - n) (smash_context [] ctx)) (decl_type c).
  Proof. exact (@isType_rec_arg_welltyped_proved cf). Qed.

  Lemma isType_tProd :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {na : aname} {A : term} {B : term}, isTypeE Σ Γ (tProd na A B) <~> isTypeRelE Σ Γ A (binder_relevance na) × isTypeE Σ (Γ,, vass na A) B.
  Proof. exact (@isType_tProd_proved cf). Qed.

  Lemma isType_wf_universes :
    forall {Σ : global_env × universes_decl} {Γ : context} {T : term}, wfE Σ.1 -> isTypeE Σ Γ T -> wf_universes Σ T.
  Proof. exact (@isType_wf_universes_proved cf). Qed.

  Lemma sorts_local_ctx_wf_local :
    forall (Σ : global_env_ext) (Γ : context) (Δ : context) (s : list sort), wf_localE Σ Γ -> sorts_local_ctx (lift_typing typingE) Σ Γ Δ s -> wf_localE Σ (Γ,,, Δ).
  Proof. exact (@sorts_local_ctx_wf_local_proved cf). Qed.

  Lemma type_local_ctx_wf_local :
    forall (Σ : global_env_ext) (Γ : context) (Δ : context) (s : sort), wf_localE Σ Γ -> type_local_ctx (lift_typing typingE) Σ Γ Δ s -> wf_localE Σ (Γ,,, Δ).
  Proof. exact (@type_local_ctx_wf_local_proved cf). Qed.

  Lemma spine_subst_app :
    forall {Σ : global_env_ext} {Γ : list context_decl} {Δ : context} {Δ' : list context_decl} {inst : list term} {inst' : list term} {insts : list term}, #|inst| = context_assumptions Δ -> wf_localE Σ (Γ,,, Δ,,, Δ') -> spine_substE Σ Γ inst (skipn #|Δ'| insts) Δ -> spine_substE Σ Γ inst' (firstn #|Δ'| insts) (subst_context (skipn #|Δ'| insts) 0 Δ') -> spine_substE Σ Γ (inst ++ inst') insts (Δ,,, Δ').
  Proof. exact (@spine_subst_app_proved cf). Qed.

  Lemma spine_subst_ctx_inst :
    forall {Σ : global_env_ext} {Γ : context} {Δ : context} {args : list term} {s : list term}, spine_substE Σ Γ args s Δ -> ctx_instE Σ Γ args (List.rev Δ).
  Proof. exact (@spine_subst_ctx_inst_proved cf). Qed.

  Lemma spine_subst_cumul :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Δ : list context_decl} {args : list term} {Γ : context} {Γ' : context}, PCUICLiftSubst.assumption_context Γ -> PCUICLiftSubst.assumption_context Γ' -> wf_localE Σ (Δ,,, Γ) -> wf_localE Σ (Δ,,, Γ') -> ws_cumul_ctx_pbE_rel Cumul Σ Δ Γ Γ' -> spine_substE Σ Δ args (List.rev args) Γ -> spine_substE Σ Δ args (List.rev args) Γ'.
  Proof. exact (@spine_subst_cumul_proved cf). Qed.

  Lemma spine_subst_smash :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {inst : list term} {s : list term} {Δ : context}, spine_substE Σ Γ inst s Δ -> spine_substE Σ Γ inst (List.rev inst) (smash_context [] Δ).
  Proof. exact (@spine_subst_smash_proved cf). Qed.

  Lemma spine_subst_inst_subst :
    forall {Σ : global_env_ext} {Γ : context} {inst : list term} {s : list term} {Δ : context} {Δ' : context}, spine_substE Σ Γ inst s Δ -> subst_context s 0 Δ' = subst_context (List.rev inst) 0 (expand_lets_ctx Δ Δ').
  Proof. exact (@spine_subst_inst_subst_proved cf). Qed.

  Lemma substitution :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {Γ' : context} {s : list term} {Δ : list context_decl} {t : term} {T : term}, subsletE Σ Γ s Γ' -> Σ;;; Γ,,, Γ',,, Δ |-E t : T -> Σ;;; Γ,,, subst_context s 0 Δ |-E subst s #|Δ| t : subst s #|Δ| T.
  Proof. exact (@substitution_proved cf). Qed.

  Lemma substitution_wf_local :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {Γ' : context} {s : list term} {Δ : list context_decl}, subsletE Σ Γ s Γ' -> wf_localE Σ (Γ,,, Γ',,, Δ) -> wf_localE Σ (Γ,,, subst_context s 0 Δ).
  Proof. exact (@substitution_wf_local_proved cf). Qed.

  Lemma typing_expand_lets :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ : list context_decl) (Δ : list context_decl) (t : term) (T : term), Σ;;; Γ,,, Δ |-E t : T -> Σ;;; Γ,,, smash_context [] Δ |-E expand_lets Δ t : expand_lets Δ T.
  Proof. exact (@typing_expand_lets_proved cf). Qed.

  Lemma typing_spine_strengthen :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {T : term} {args : list term} {U : term}, typing_spineE Σ Γ T args U -> forall T' : term, isTypeE Σ Γ T' -> Σ ;;; Γ ⊢E T' ≤ T -> typing_spineE Σ Γ T' args U.
  Proof. exact (@typing_spine_strengthen_proved cf). Qed.

  Lemma typing_wf_sort :
    forall {Σ : global_env_ext} {Γ : context} {t : term} {s : sort}, wfE Σ -> Σ;;; Γ |-E t : tSort s -> wf_sort Σ s.
  Proof. exact (@typing_wf_sort_proved cf). Qed.

  Lemma typing_wf_universes :
    forall {Σ : global_env_ext} {Γ : context} {t : term} {T : term}, wfE Σ -> Σ;;; Γ |-E t : T -> wf_universes Σ t && wf_universes Σ T.
  Proof. exact (@typing_wf_universes_proved cf). Qed.

  Lemma weaken_ctx :
    forall {Σ : global_env × universes_decl} {Γ : context} {t : term} {T : term} (Δ : context), wfE Σ.1 -> wf_localE Σ Δ -> Σ;;; Γ |-E t : T -> Σ;;; Δ,,, Γ |-E t : T.
  Proof. exact (@weaken_ctx_proved cf). Qed.

  Lemma weaken_wf_local :
    forall {Σ : global_env × universes_decl} {Δ : context} (Γ : context), wfE Σ.1 -> wf_localE Σ Γ -> wf_localE Σ Δ -> wf_localE Σ (Γ,,, Δ).
  Proof. exact (@weaken_wf_local_proved cf). Qed.

  Lemma weakening_wf_local :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {Γ' : list context_decl} {Γ'' : list context_decl}, wf_localE Σ (Γ,,, Γ') -> wf_localE Σ (Γ,,, Γ'') -> wf_localE Σ (Γ,,, Γ'',,, lift_context #|Γ''| 0 Γ').
  Proof. exact (@weakening_wf_local_proved cf). Qed.

  Lemma welltyped_prod_codomain :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {na : aname} {A : term} {B : term}, welltypedE Σ Γ (tProd na A B) -> welltypedE Σ (Γ,, vass na A) B.
  Proof. exact (@welltyped_prod_codomain_proved cf). Qed.

  Lemma wf_local_expand_lets :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {Δ : list context_decl} {Γ' : list context_decl}, wf_localE Σ (Γ,,, Δ,,, Γ') -> wf_localE Σ (Γ,,, smash_context [] Δ,,, expand_lets_ctx Δ Γ').
  Proof. exact (@wf_local_expand_lets_proved cf). Qed.

  Lemma wf_local_smash_context :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context}, wf_localE Σ Γ -> wf_localE Σ (smash_context [] Γ).
  Proof. exact (@wf_local_smash_context_proved cf). Qed.

  Lemma wf_local_smash_end :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ Δ : list context_decl), wf_localE Σ (Γ,,, Δ) -> wf_localE Σ (Γ,,, smash_context [] Δ).
  Proof. exact (@wf_local_smash_end_proved cf). Qed.

  Lemma isType_weaken :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {T : term}, wf_localE Σ Γ -> isTypeE Σ [] T -> isTypeE Σ Γ T.
  Proof. exact (@isType_weaken_proved cf). Qed.

  Lemma isType_it_mkProd_or_LetIn :
    forall {Σ : global_env_ext} {Γ Δ : list context_decl} {T : term}, wfE Σ.1 -> isTypeE Σ (Γ,,, Δ) T -> isTypeE Σ Γ (it_mkProd_or_LetIn Δ T).
  Proof. exact (@isType_it_mkProd_or_LetIn_proved cf). Qed.

  Lemma type_local_ctx_wf :
    forall {Σ : global_env_ext} {Γ Δ : context} {s : sort}, wfE Σ.1 -> type_local_ctx (lift_typing typingE) Σ Γ Δ s -> wf_sort Σ s.
  Proof. exact (@type_local_ctx_wf_proved cf). Qed.

  Lemma LSet_in_global_bounded :
    forall {Σ : global_env} {l : LevelSet.elt} (k : nat), wfE Σ -> LevelSet.In l (global_levels Σ) -> closedu_level k l.
  Proof. exact (@LSet_in_global_bounded_proved cf). Qed.

  Lemma closed_red_from_empty :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {M : term} {N : term}, on_free_vars_ctx xpred0 Γ -> closed M -> PCUICReduction.red Σ [] M N -> Σ ;;; Γ ⊢ M ⇝ N.
  Proof. exact (@closed_red_from_empty_proved cf). Qed.

  Lemma red_expand_let :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {na : aname} {b : term} {ty : term} {t : term}, wf_localE Σ (Γ,,, [vdef na b ty]) -> on_free_vars (shiftnP #|Γ,,, [vdef na b ty]| (fun _ : nat => false)) t -> Σ ;;; Γ,, vdef na b ty ⊢ t ⇝ lift0 1 (t {0 := b}).
  Proof. exact (@red_expand_let_proved cf). Qed.

  Lemma red_it_mkProd_or_LetIn_smash :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ : list context_decl) (ctx : context) (t : term) (u : term) (n : nat) (c : context_decl), Σ ;;; Γ ⊢ it_mkProd_or_LetIn ctx t ⇝ u -> nth_error (List.rev (smash_context [] ctx)) n = Some c -> ∑ (ctx' : context) (t' : term) (d : context_decl), [× decompose_prod_assum [] u = (ctx', t'), nth_error (List.rev (smash_context [] ctx')) n = Some d & Σ ;;; Γ,,, skipn (#|smash_context [] ctx| - n) (smash_context [] ctx) ⊢ decl_type c ⇝ decl_type d].
  Proof. exact (@red_it_mkProd_or_LetIn_smash_proved cf). Qed.

  Lemma red_mkApps_smash_witness :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {C : term} {ctx : context} {i : inductive} {u : Instance.t} {l : list term}, Σ ;;; Γ ⊢ C ⇝ it_mkProd_or_LetIn ctx (mkApps (tInd i u) l) -> ∑ l' : list term, Σ ;;; Γ ⊢ C ⇝ it_mkProd_or_LetIn (smash_context [] ctx) (mkApps (tInd i u) l').
  Proof. exact (@red_mkApps_smash_witness_proved cf). Qed.

  Lemma red_rec_arg_check_one_fix :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ : list context_decl) (d : def term) (ctx : context) (concl : term) (c : context_decl) (ind : inductive) (u : Instance.t) (args : list term), on_free_vars (shiftnP #|Γ| xpred0) (dtype d) -> decompose_prod_assum [] (dtype d) = (ctx, concl) -> nth_error (List.rev (smash_context [] ctx)) (rarg d) = Some c -> Σ ;;; Γ,,, skipn (#|smash_context [] ctx| - rarg d) (smash_context [] ctx) ⊢ decl_type c ⇝ mkApps (tInd ind u) args -> has_rec_arg d × (∑ ty : term, Σ ;;; Γ ⊢ dtype d ⇝ ty × check_one_fix (def_with_type d ty) = Some (inductive_mind ind)).
  Proof. exact (@red_rec_arg_check_one_fix_proved cf). Qed.

  Lemma wf_universes_inst :
    forall {Σ : global_env_ext} (univs : universes_decl) (t : term) (u : list LevelSet.elt), wfE Σ -> on_udecl_prop Σ.1 univs -> wf_instance Σ u -> wf_universes (Σ.1, univs) t -> wf_universes Σ t@[u].
  Proof. exact (@wf_universes_inst_proved cf). Qed.

  Lemma closed_red_confluence :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {t : term} {u : term} {v : term}, Σ ;;; Γ ⊢ t ⇝ u -> Σ ;;; Γ ⊢ t ⇝ v -> ∑ v' : term, Σ ;;; Γ ⊢ u ⇝ v' × Σ ;;; Γ ⊢ v ⇝ v'.
  Proof. exact (@closed_red_confluence_proved cf). Qed.

  Lemma isType_prim_arg_types :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {tags : list prim_tag} {res : term} {T : term}, wf_localE Σ Γ -> (forall t : prim_tag, In t tags -> t <> primArray) -> All (prim_op_tag_declared Σ) tags -> PCUICPrimOpType.prim_arg_types (retroknowledge Σ.1) tags res = Some T -> isTypeE Σ Γ res -> isTypeE Σ Γ T.
  Proof. exact (@isType_prim_arg_types_proved cf). Qed.

  Lemma wf_rel_weak :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ) (Γ : context), wf_localE Σ Γ -> forall (Γ' : context), wf_localE Σ Γ' -> wf_local_relE Σ Γ Γ'.
  Proof. exact (@wf_rel_weak_proved cf). Qed.
End ProvedFields.

(** ** Derived lemmas that use former fields (moved here from "Derived" and "Derived, second part") *)
Section DerivedThree.
  Context {cf : checker_flags}.

  Lemma spine_subst_wt_terms {hT0 : T0_facts} {Σ : global_env_ext} {Γ : context} {inst s : list term} {Δ : context} :
    spine_substE Σ Γ inst s Δ -> All (fun t : term => ∑ T : term, Σ ;;; Γ |-E t : T) inst.
  Proof.
    move/spine_subst_ctx_inst.
    induction 1; try constructor; auto.
    now exists t.
  Qed.

  (** [PCUICFixWitness.check_one_fix_closed_red] over [wfE], from the U field
      [red_it_mkProd_or_LetIn_smash] and the derived [invert_red_mkApps_tInd]. *)
  Lemma check_one_fix_closed_redE {hU : U_facts} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ d ty v mind} :
    Σ ;;; Γ ⊢ ty ⇝ v ->
    check_one_fix (def_with_type d ty) = Some mind ->
    check_one_fix (def_with_type d v) = Some mind.
  Proof.
    intros r hc.
    destruct (check_one_fix_inv _ _ _ hc)
      as (ctx & concl & argd & k & u & args & decomp & hnth & dapp).
    have eqty := PCUICSubstitution.decompose_prod_assum_it_mkProd_or_LetIn _ _ _ _ decomp; cbn in eqty.
    rewrite eqty in r.
    destruct (red_it_mkProd_or_LetIn_smash _ _ _ _ _ _ r hnth)
      as [ctx' [t' [d' [decomp' hnth' r']]]].
    rewrite /check_one_fix /def_with_type /= decomp' hnth'.
    rewrite dapp in r'.
    eapply invert_red_mkApps_tInd in r' as [args' [-> _ _]].
    now rewrite decompose_app_mkApps.
  Qed.

  (** [PCUICFixWitness.check_one_cofix_closed_red] over [wfE]. *)
  Lemma check_one_cofix_closed_redE {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ d ty v mind} :
    Σ ;;; Γ ⊢ ty ⇝ v ->
    check_one_cofix (def_with_type d ty) = Some mind ->
    check_one_cofix (def_with_type d v) = Some mind.
  Proof.
    intros r hc.
    destruct (check_one_cofix_inv _ _ _ hc) as [ctx [k [u [args ->]]]].
    destruct (red_it_mkProd_or_LetIn_mkApps_Ind r) as [ctx' [args' ->]].
    exact (check_one_cofix_it_mkProd (i := {| inductive_mind := mind; inductive_ind := k |})).
  Qed.

  #[global] Instance check_one_fix_shapeE {hU : U_facts} : ShapeCheckE check_one_fix :=
    {| shapeE_check_dbody := fun d bo => shape_check_dbody (check := check_one_fix) d bo;
       shapeE_check_eq_term_upto := @shape_check_eq_term_upto check_one_fix _;
       shapeE_check_closed_red := @check_one_fix_closed_redE hU |}.

  #[global] Instance check_one_cofix_shapeE : ShapeCheckE check_one_cofix :=
    {| shapeE_check_dbody := fun d bo => shape_check_dbody (check := check_one_cofix) d bo;
       shapeE_check_eq_term_upto := @shape_check_eq_term_upto check_one_cofix _;
       shapeE_check_closed_red := @check_one_cofix_closed_redE |}.

  (** The copies take the U facts squashed in [EtaFacts]; a Prop instance can still be built from them. *)
  #[global] Instance check_one_fix_shapeE_of {EF : EtaFacts} : ShapeCheckE check_one_fix :=
    match eta_U with sq hU => @check_one_fix_shapeE hU end.

  (** [PCUICFixWitness.mfix_body_on_red_unique] over E (see STATEMENT CHANGE above [ShapeCheckE]). *)
  Lemma mfix_body_on_red_unique {hU : U_facts} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {check : def term -> option kername} {shape : ShapeCheckE check} {Γ : context} {d : def term}
    {m1 m2 : kername} :
    on_def_type (lift_typing1 (typingE Σ)) Γ d ->
    mfix_body_on check (PCUICReduction.red Σ Γ) m1 d ->
    mfix_body_on check (PCUICReduction.red Σ Γ) m2 d ->
    m1 = m2.
  Proof.
    intros ond [ty1 [hc1 r1]] [ty2 [hc2 r2]].
    have isty : isTypeE Σ Γ (dtype d) by now eapply isTypeRel_isType.
    have clΓ : is_closed_context Γ.
    { eapply wf_local_closed_contextE. now eapply isType_wf_local. }
    have op : is_open_term Γ (dtype d) by now eapply isType_is_open_term.
    have c1 : Σ ;;; Γ ⊢ dtype d ⇝ ty1 by now eapply into_closed_red.
    have c2 : Σ ;;; Γ ⊢ dtype d ⇝ ty2 by now eapply into_closed_red.
    destruct (closed_red_confluence c1 c2) as [v [rv1 rv2]].
    have e1 : check (def_with_type d v) = Some m1.
    { exact (shapeE_check_closed_red (check := check) (wfΣ := wfΣ) rv1 hc1). }
    have e2 : check (def_with_type d v) = Some m2.
    { exact (shapeE_check_closed_red (check := check) (wfΣ := wfΣ) rv2 hc2). }
    rewrite e1 in e2. now injection e2.
  Qed.

End DerivedThree.


(** ** Instances: satisfying instances of the fields of the hypothesis classes above

  BET-64 EtaCheckerLane, 2026-10-29. One lemma [<field>_inst] per field of each hypothesis class above
  ([T0_facts], [U_facts], [T1_facts], [T2a_facts], [T6_facts], [T6BD_facts], [T6BDu_facts], [T6BDc_facts]),
  in the class order.
  Convention of [PCUICEtaFracInstances]: the environment is [si_Σ] of
  [PCUICCumulativitySpecEtaClosureInstances] ([Inductive I (A : Prop) : Prop := c : I A]), or, where the
  field needs a registered primitive type, [Σ_po] of [PCUICEtaPrimOpInstance] (registers [int]); the terms
  are closed.

  Each instance states the field's premises and its conclusion at the chosen arguments, as one product.
  The premise [wfE Σ] (named binder or arrow) holds by [si_wfE] or [ti_po_wfE]. Every typed premise is a
  base derivation lifted to E with [typing_incl_E] (and its consequences [ti_*] below: local environments,
  [isType], spines, substitutions, cumulativity through [ws_cumul_pb_incl_E]); the bidirectional E premises
  are built with the constructors of the canonical judgments of [BDTypingEta] (re-exported by
  [PCUICTypingEtaDefs]). The conclusion is the base lemma of the same
  name (qualified) applied at that point and lifted to E; the equivalences, the bidirectional conclusions
  and the reflexive reductions of [T6BDu_facts] are built directly. No proof uses a field of a class.

  Each instance has a tag on the line above it: [(* non-degenerate *)], or, when its point has an empty
  context or list where the field quantifies over one, a subject that is the sort Prop, or two compared
  objects that are equal (T = U, a reflexive reduction or comparison), [(* degenerate: IMPOSSIBLE — … *)]
  (no non-degenerate instance exists, by the head or shape and the rule set, or by a premise with no
  other inhabitant) or [(* degenerate: NOT BUILT — … *)] (one exists and is not built here). Counts:
  37 non-degenerate; 0 IMPOSSIBLE; 7 NOT BUILT ([inductive_cumulative_indices], [isTypeRel_cstr_type],
  [isType_mkApps_Ind_inv], [wf_case_branch_type], [wf_case_predicate_context] and
  [wf_case_branches_types'] need an indexed inductive family; [typing_spine_ind_type_inv] needs an
  inductive whose user arity reduces non-trivially to the built one, which [on_ind_body]'s [ind_arity_red]
  allows). Three instances are typed through an η step:
  [validity], [checking_typing] and [infering_checking] use the variable [y : k g] of
  [PCUICInversionEtaInstances], typed at [k (λ x : Prop. g x)] by [cumul_eta_l]; their conclusions are
  built in E directly, since base typing has no η and the base lemma cannot reach that point. (The
  instances of the 47 fields proved in the section "PROVED rows" are removed: a proved lemma needs none.)

  (1) Such an instance shows that the hypothesis is consistent and about something real. (2) It does NOT
  discharge the hypothesis at [typingE]: each field remains a hypothesis until its plan row lands (T0, T1,
  T2a, T6; T6BDc also needs T8; U is untyped plumbing over [wfE_ClosedBodies]). *)

From MetaRocq.PCUIC Require Import PCUICCumulativitySpecEtaClosureInstances PCUICEtaFracInstances
     PCUICEtaPrimOpInstance PCUICInversionEtaInstances.
From MetaRocq.PCUIC Require PCUICValidity PCUICSR PCUICArities PCUICContexts PCUICSubstitution
     PCUICWeakeningTyp PCUICContextConversion PCUICClassification PCUICClosedTyp.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

(** *** Lifting base derivations to E ([typing_incl_E] and its consequences) *)

(** Each helper takes the environment and its base well-formedness as explicit arguments; every use below
    passes a concrete one ([si_wf], [ti_po_wf]). *)

Lemma ti_lt (Σ : global_env_ext) (wfΣ : wf Σ) {Γ j} : lift_typing typing Σ Γ j -> lift_typing typingE Σ Γ j.
Proof. intros h. apply lift_typing_impl with (1 := h). intros t T ht. exact (typing_incl_E wfΣ ht). Qed.

Lemma ti_isType (Σ : global_env_ext) (wfΣ : wf Σ) {Γ T} : isType Σ Γ T -> isTypeE Σ Γ T.
Proof. intros h. apply (ti_lt Σ wfΣ). exact h. Qed.

Lemma ti_isTypeRel (Σ : global_env_ext) (wfΣ : wf Σ) {Γ T r} : isTypeRel Σ Γ T r -> isTypeRelE Σ Γ T r.
Proof. intros h. apply (ti_lt Σ wfΣ). exact h. Qed.

Lemma ti_wt (Σ : global_env_ext) (wfΣ : wf Σ) {Γ t} : welltyped Σ Γ t -> welltypedE Σ Γ t.
Proof. intros [A h]. econstructor. exact (typing_incl_E wfΣ h). Qed.

Lemma ti_wfl (Σ : global_env_ext) (wfΣ : wf Σ) {Γ} : wf_local Σ Γ -> wf_localE Σ Γ.
Proof. exact (wf_local_incl_E wfΣ). Qed.

Lemma ti_wsc (Σ : global_env_ext) (wfΣ : wf Σ) {pb Γ t u} : Σ ;;; Γ ⊢ t ≤[pb] u -> Σ ;;; Γ ⊢E t ≤[pb] u.
Proof. exact (ws_cumul_pb_incl_E (wfΣ := @PCUICClosedTyp.wf_ClosedBodies _ Σ wfΣ)). Qed.

Lemma ti_subslet (Σ : global_env_ext) (wfΣ : wf Σ) {Γ s Δ} :
  PCUICSubstitution.subslet Σ Γ s Δ -> subsletE Σ Γ s Δ.
Proof.
  induction 1 as [|Δ s na t T _ ih ht|Δ s na t T _ ih ht].
  - constructor.
  - constructor; [exact ih|exact (typing_incl_E wfΣ ht)].
  - constructor; [exact ih|exact (typing_incl_E wfΣ ht)].
Qed.

Lemma ti_spine (Σ : global_env_ext) (wfΣ : wf Σ) {Γ inst s Δ} :
  PCUICSpine.spine_subst Σ Γ inst s Δ -> spine_substE Σ Γ inst s Δ.
Proof.
  intros [h1 h2 h3 h4].
  split; [exact (ti_wfl Σ wfΣ h1)|exact (ti_wfl Σ wfΣ h2)|exact h3|exact (ti_subslet Σ wfΣ h4)].
Qed.

Lemma ti_tspine (Σ : global_env_ext) (wfΣ : wf Σ) {Γ T args U} :
  PCUICArities.typing_spine Σ Γ T args U -> typing_spineE Σ Γ T args U.
Proof.
  induction 1 as [ty ty' h1 h2 h3|ty hd tl na A B B' h1 h2 h3 h4 _ ih].
  - constructor; [exact (ti_isType Σ wfΣ h1)|exact (ti_isType Σ wfΣ h2)|exact (ti_wsc Σ wfΣ h3)].
  - econstructor; [exact (ti_isType Σ wfΣ h1)|exact (ti_isType Σ wfΣ h2)|exact (ti_wsc Σ wfΣ h3)
                  |exact (typing_incl_E wfΣ h4)|exact ih].
Qed.

Lemma ti_ctxi (Σ : global_env_ext) (wfΣ : wf Σ) {Γ args Δ} : ctx_inst Σ Γ args Δ -> ctx_instE Σ Γ args Δ.
Proof. intros h. apply ctx_inst_impl with (1 := h). intros t T ht. exact (typing_incl_E wfΣ ht). Qed.

(** At [si_Σ]. *)
Definition siT {Γ t T} (h : si_Σ ;;; Γ |- t : T) : si_Σ ;;; Γ |-E t : T := typing_incl_E (Σ := si_Σ) si_wf h.
Definition siW {Γ} (h : wf_local si_Σ Γ) : wf_localE si_Σ Γ := ti_wfl si_Σ si_wf h.
Definition siL {Γ j} (h : lift_typing typing si_Σ Γ j) : lift_typing typingE si_Σ Γ j := ti_lt si_Σ si_wf h.
Definition siI {Γ T} (h : isType si_Σ Γ T) : isTypeE si_Σ Γ T := ti_isType si_Σ si_wf h.
Definition siIR {Γ T r} (h : isTypeRel si_Σ Γ T r) : isTypeRelE si_Σ Γ T r := ti_isTypeRel si_Σ si_wf h.
Definition siWT {Γ t} (h : welltyped si_Σ Γ t) : welltypedE si_Σ Γ t := ti_wt si_Σ si_wf h.
Definition siC {pb Γ t u} (h : si_Σ ;;; Γ ⊢ t ≤[pb] u) : si_Σ ;;; Γ ⊢E t ≤[pb] u := ti_wsc si_Σ si_wf h.
Definition siS {Γ inst s Δ} (h : PCUICSpine.spine_subst si_Σ Γ inst s Δ) : spine_substE si_Σ Γ inst s Δ :=
  ti_spine si_Σ si_wf h.
Definition siTS {Γ T args U} (h : PCUICArities.typing_spine si_Σ Γ T args U) : typing_spineE si_Σ Γ T args U :=
  ti_tspine si_Σ si_wf h.
Definition siCI {Γ args Δ} (h : ctx_inst si_Σ Γ args Δ) : ctx_instE si_Σ Γ args Δ :=
  ti_ctxi si_Σ si_wf h.

(** *** Closed terms and base derivations in [si_Σ] *)

(** [∀ A : Prop. A], a closed proposition, so a closed argument for the parameter of [I]. *)
Definition ti_F : term := tProd si_na si_P (tRel 0).
(** [I ti_F], a closed proposition. *)
Definition ti_IF : term := tApp (tInd si_ind []) ti_F.
Definition ti_ΓP : context := [vass si_na si_P].
Definition ti_ΓI : context := [vass si_na ti_IF].

Lemma ti_wf_nil : wf_local si_Σ [].
Proof. constructor. Qed.

Lemma ti_P_ty Γ : wf_local si_Σ Γ -> si_Σ ;;; Γ |- si_P : tSort (Sort.super sProp).
Proof. intros h. apply type_Sort; [exact h|cbn; trivial]. Qed.

Lemma ti_vass (Γ : context) (na : aname) (A : term) (s : sort) :
  si_Σ ;;; Γ |- A : tSort s -> isSortRel s na.(binder_relevance) -> lift_typing typing si_Σ Γ (j_vass na A).
Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [exact I|exact r]. Qed.

Lemma ti_vass_s (Γ : context) (na : aname) (A : term) (s : sort) :
  si_Σ ;;; Γ |- A : tSort s -> isSortRel s na.(binder_relevance) -> lift_typing typing si_Σ Γ (j_vass_s na A s).
Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [reflexivity|exact r]. Qed.

Lemma ti_wf_cons (Γ : context) (na : aname) (A : term) (s : sort) :
  wf_local si_Σ Γ -> si_Σ ;;; Γ |- A : tSort s -> isSortRel s na.(binder_relevance) ->
  wf_local si_Σ (Γ ,, vass na A).
Proof. intros h hA r. apply localenv_cons_abs; [exact h|exact (ti_vass Γ na A s hA r)]. Qed.

Lemma ti_wf_P Γ : wf_local si_Σ Γ -> wf_local si_Σ (Γ ,, vass si_na si_P).
Proof. intros h. exact (ti_wf_cons Γ si_na si_P _ h (ti_P_ty Γ h) eq_refl). Qed.

Lemma ti_wf_ΓP : wf_local si_Σ ti_ΓP.
Proof. exact (ti_wf_P [] ti_wf_nil). Qed.

Lemma ti_arity_ty Γ : wf_local si_Σ Γ ->
  si_Σ ;;; Γ |- si_arity : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)).
Proof.
  intros h. apply type_Prod.
  - exact (ti_vass_s _ si_na _ _ (ti_P_ty Γ h) eq_refl).
  - apply type_Sort; [exact (ti_wf_P Γ h)|cbn; trivial].
Qed.

Lemma ti_F_ty Γ : wf_local si_Σ Γ -> si_Σ ;;; Γ |- ti_F : tSort sProp.
Proof.
  intros h.
  refine (type_Prod _ _ si_na si_P (tRel 0) (Sort.super sProp) sProp _ _).
  - exact (ti_vass_s _ si_na _ _ (ti_P_ty Γ h) eq_refl).
  - exact (type_Rel _ _ 0 (vass si_na si_P) (ti_wf_P Γ h) eq_refl).
Qed.

Lemma ti_cons : consistent_instance_ext si_Σ (ind_universes si_mdecl) [].
Proof. reflexivity. Qed.

Lemma ti_declared_minductive : declared_minductive si_Σ si_kn si_mdecl.
Proof. left; reflexivity. Qed.

Lemma ti_Ind_ty Γ : wf_local si_Σ Γ -> si_Σ ;;; Γ |- tInd si_ind [] : si_arity.
Proof. intros h. exact (type_Ind _ _ si_ind [] si_mdecl si_idecl h si_declared_inductive ti_cons). Qed.

Lemma ti_IF_ty Γ : wf_local si_Σ Γ -> si_Σ ;;; Γ |- ti_IF : tSort sProp.
Proof.
  intros h.
  exact (type_App _ _ (tInd si_ind []) si_na si_P (tSort sProp) _ ti_F
           (ti_arity_ty Γ h) (ti_Ind_ty Γ h) (ti_F_ty Γ h)).
Qed.

Lemma ti_wf_I Γ : wf_local si_Σ Γ -> wf_local si_Σ (Γ ,, vass si_na ti_IF).
Proof. intros h. exact (ti_wf_cons Γ si_na ti_IF sProp h (ti_IF_ty Γ h) eq_refl). Qed.

Lemma ti_wf_ΓI : wf_local si_Σ ti_ΓI.
Proof. exact (ti_wf_I [] ti_wf_nil). Qed.

(** The arities context of [I] and the type of its constructor, in [si_Σ]. *)
Lemma ti_wf_Γi : wf_local si_Σ si_Γi.
Proof.
  apply localenv_cons_abs; [constructor|].
  exact (ti_vass _ (mkBindAnn (nNamed "I") rel_of_Type) _ _ (ti_arity_ty [] ti_wf_nil) eq_refl).
Qed.

Lemma ti_ctype_ty :
  si_Σ ;;; si_Γi |- cstr_type si_cdecl : tSort (Sort.sort_of_product (Sort.super sProp) sProp).
Proof.
  have w2 := ti_wf_P si_Γi ti_wf_Γi.
  apply type_Prod.
  - exact (ti_vass_s _ si_na _ _ (ti_P_ty si_Γi ti_wf_Γi) eq_refl).
  - refine (type_App _ _ (tRel 1) si_na si_P (tSort sProp)
              (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) (tRel 0) _ _ _).
    + exact (ti_arity_ty _ w2).
    + exact (type_Rel _ _ 1 (vass (mkBindAnn (nNamed "I") rel_of_Type) si_arity) w2 eq_refl).
    + exact (type_Rel _ _ 0 (vass si_na si_P) w2 eq_refl).
Qed.

(** The parameter instance [ti_F] of [I], as a base spine substitution. *)
Lemma ti_subslet_F : PCUICSubstitution.subslet si_Σ [] [ti_F] ti_ΓP.
Proof.
  exact (PCUICSubstitution.cons_let_ass si_Σ [] [] [] si_na ti_F si_P
           (PCUICSubstitution.emptyslet si_Σ []) (ti_F_ty [] ti_wf_nil)).
Qed.

Lemma ti_spine_F : PCUICSpine.spine_subst si_Σ [] [ti_F] [ti_F] ti_ΓP.
Proof.
  split.
  - exact ti_wf_nil.
  - exact ti_wf_ΓP.
  - exact (context_subst_ass [] [] [] si_na si_P ti_F context_subst_nil).
  - exact ti_subslet_F.
Qed.

(** A fixpoint body whose declared type is [Π _ : I ti_F. Prop], recursive on its argument. *)
Definition ti_d : def term := {| dname := si_na; dtype := tProd si_na ti_IF si_P; dbody := si_P; rarg := 0 |}.

Lemma ti_wfs : wf_sort si_Σ sProp.
Proof. cbn; trivial. Qed.

Lemma ti_wfs1 : wf_sort si_Σ (Sort.super sProp).
Proof. exact (PCUICWfUniverses.wf_sort_super ti_wfs). Qed.

Lemma ti_P1_ty Γ : wf_local si_Σ Γ -> si_Σ ;;; Γ |- tSort (Sort.super sProp) : tSort (Sort.super (Sort.super sProp)).
Proof. intros h. apply type_Sort; [exact h|exact ti_wfs1]. Qed.

(** A context with one proposition-typed assumption. *)
Definition ti_ΓF : context := [vass si_na ti_F].

(** [ti_F] instantiates the telescope [ti_ΓP]; transparent, so [ctx_inst_sub] computes. *)
Definition ti_ciB : ctx_inst si_Σ [] [ti_F] (List.rev ti_ΓP).
Proof. cbn. econstructor; [exact (ti_F_ty [] ti_wf_nil)|cbn; constructor]. Defined.

Definition ti_ciE : ctx_instE si_Σ [] [ti_F] (List.rev ti_ΓP).
Proof. cbn. econstructor; [exact (siT (ti_F_ty [] ti_wf_nil))|cbn; constructor]. Defined.

(** [let _ : Prop := ti_F in _]. *)
Lemma ti_def_j : lift_typing typing si_Σ [] (j_vdef si_na ti_F si_P).
Proof.
  split; [exact (ti_F_ty [] ti_wf_nil)|].
  exists (Sort.super sProp). split; [exact (ti_P_ty [] ti_wf_nil)|split; [exact I|reflexivity]].
Qed.

Lemma ti_wf_def : wf_local si_Σ [vdef si_na ti_F si_P].
Proof. apply localenv_cons_def; [constructor|exact ti_def_j]. Qed.

Lemma ti_LetIn_ty : si_Σ ;;; [] |- tLetIn si_na ti_F si_P (tRel 0) : tLetIn si_na ti_F si_P si_P.
Proof.
  exact (type_LetIn _ _ si_na ti_F si_P (tRel 0) si_P ti_def_j
           (type_Rel _ _ 0 (vdef si_na ti_F si_P) ti_wf_def eq_refl)).
Qed.

(** The spine of [I ti_F]. *)
Lemma ti_tspine_IF : PCUICArities.typing_spine si_Σ [] (ind_type si_idecl)@[[]] [ti_F] (tSort sProp).
Proof.
  exact (fst (PCUICInductives.invert_type_mkApps_ind si_Σ [] si_ind [] [ti_F] (tSort sProp) si_mdecl si_idecl
                si_wf si_declared_inductive (ti_IF_ty [] ti_wf_nil))).
Qed.

Lemma ti_spine_nil : PCUICSpine.spine_subst si_Σ [] [] [] [].
Proof. split; [exact ti_wf_nil|exact ti_wf_nil|constructor|constructor]. Qed.

(** Base reflexive comparisons. *)
Lemma ti_ws_refl {pb} (Γ : context) (t : term) :
  is_closed_context Γ -> is_open_term Γ t -> si_Σ ;;; Γ ⊢ t ≤[pb] t.
Proof. exact PCUICWellScopedCumulativity.ws_cumul_pb_refl. Qed.

Lemma ti_cr_refl (Γ : context) (t : term) :
  is_closed_context Γ -> is_open_term Γ t -> si_Σ ;;; Γ ⊢ t ⇝ t.
Proof. intros h1 h2. split; [exact h1|exact h2|apply rt_refl]. Qed.

(** *** Terms over [I] in the context [ti_ΓP = [A : Prop]], for the non-degenerate instances *)

(** [I a] is a proposition for every proposition [a]. *)
Lemma ti_Iapp_ty Γ a : wf_local si_Σ Γ -> si_Σ ;;; Γ |- a : si_P -> si_Σ ;;; Γ |- tApp (tInd si_ind []) a : tSort sProp.
Proof.
  intros h ha.
  exact (type_App _ _ (tInd si_ind []) si_na si_P (tSort sProp) _ a (ti_arity_ty Γ h) (ti_Ind_ty Γ h) ha).
Qed.

(** [I A] and [c A], where [A] is the variable of [ti_ΓP]; [Π A : Prop. I A], the type of [c]. *)
Definition ti_IA : term := tApp (tInd si_ind []) (tRel 0).
Definition ti_cA : term := tApp (tConstruct si_ind 0 []) (tRel 0).
Definition ti_cty : term := tProd si_na si_P ti_IA.
(** One assumption [x : I A] over [ti_ΓP]; the telescope [(X : Prop) (y : X)]. *)
Definition ti_ΓIA : context := [vass si_na ti_IA].
Definition ti_Δ2 : context := [vass si_na si_P; vass si_na (tRel 0)].

Lemma ti_A_ty : si_Σ ;;; ti_ΓP |- tRel 0 : si_P.
Proof. exact (type_Rel _ _ 0 (vass si_na si_P) ti_wf_ΓP eq_refl). Qed.

Lemma ti_IA_ty : si_Σ ;;; ti_ΓP |- ti_IA : tSort sProp.
Proof. exact (ti_Iapp_ty ti_ΓP (tRel 0) ti_wf_ΓP ti_A_ty). Qed.

Lemma ti_wf_ΓPIA : wf_local si_Σ (ti_ΓP ,, vass si_na ti_IA).
Proof. exact (ti_wf_cons ti_ΓP si_na ti_IA sProp ti_wf_ΓP ti_IA_ty eq_refl). Qed.

Lemma ti_cty_ty Γ : wf_local si_Σ Γ -> si_Σ ;;; Γ |- ti_cty : tSort (Sort.sort_of_product (Sort.super sProp) sProp).
Proof.
  intros h. have h1 := ti_wf_P Γ h.
  exact (type_Prod _ _ si_na si_P ti_IA (Sort.super sProp) sProp (ti_vass_s _ si_na _ _ (ti_P_ty Γ h) eq_refl)
           (ti_Iapp_ty _ (tRel 0) h1 (type_Rel _ _ 0 (vass si_na si_P) h1 eq_refl))).
Qed.

Lemma ti_Construct_ty Γ : wf_local si_Σ Γ -> si_Σ ;;; Γ |- tConstruct si_ind 0 [] : ti_cty.
Proof.
  intros h. exact (type_Construct _ _ si_ind 0 [] si_mdecl si_idecl si_cdecl h si_declared_constructor ti_cons).
Qed.

Lemma ti_cA_ty : si_Σ ;;; ti_ΓP |- ti_cA : ti_IA.
Proof.
  exact (type_App _ _ (tConstruct si_ind 0 []) si_na si_P ti_IA _ (tRel 0)
           (ti_cty_ty ti_ΓP ti_wf_ΓP) (ti_Construct_ty ti_ΓP ti_wf_ΓP) ti_A_ty).
Qed.

(** [I A] and [c A] instantiate the telescope [ti_Δ2 = (X : Prop) (y : X)]. *)
Lemma ti_ci2B : ctx_inst si_Σ ti_ΓP [ti_IA; ti_cA] ti_Δ2.
Proof.
  econstructor; [exact ti_IA_ty|].
  change (ctx_inst si_Σ ti_ΓP [ti_cA] [vass si_na ti_IA]).
  econstructor; [exact ti_cA_ty|]. cbn. constructor.
Qed.

(** A fixpoint body over [ti_ΓP] with declared type [Π _ : I A. Prop]. *)
Definition ti_dA : def term :=
  {| dname := si_na; dtype := tProd si_na ti_IA si_P; dbody := tLambda si_na ti_IA ti_F; rarg := 0 |}.

Lemma ti_dA_ty : isTypeRel si_Σ ti_ΓP (tProd si_na ti_IA si_P) Relevant.
Proof.
  apply (has_sort_isTypeRel (Sort.sort_of_product sProp (Sort.super sProp)) Relevant eq_refl).
  apply type_Prod; [exact (ti_vass_s _ si_na _ _ ti_IA_ty eq_refl)|exact (ti_P_ty _ ti_wf_ΓPIA)].
Qed.

(** [(λ X : Prop. X) ti_F], a β-redex that reduces to [ti_F]; the context [x : (λ X : Prop. X) ti_F]. *)
Definition ti_bF : term := tApp (tLambda si_na si_P (tRel 0)) ti_F.
Definition ti_ΓbF : context := [vass si_na ti_bF].

Lemma ti_bF_ty : si_Σ ;;; [] |- ti_bF : tSort sProp.
Proof.
  have hlam : si_Σ ;;; [] |- tLambda si_na si_P (tRel 0) : tProd si_na si_P si_P :=
    type_Lambda _ _ si_na si_P (tRel 0) si_P (ti_vass [] si_na si_P _ (ti_P_ty [] ti_wf_nil) eq_refl) ti_A_ty.
  exact (type_App _ _ (tLambda si_na si_P (tRel 0)) si_na si_P si_P _ ti_F (ti_arity_ty [] ti_wf_nil) hlam
           (ti_F_ty [] ti_wf_nil)).
Qed.

Lemma ti_wf_ΓbF : wf_local si_Σ ti_ΓbF.
Proof. exact (ti_wf_cons [] si_na ti_bF sProp ti_wf_nil ti_bF_ty eq_refl). Qed.

Lemma ti_wf_ΓF : wf_local si_Σ ti_ΓF.
Proof. exact (ti_wf_cons [] si_na ti_F sProp ti_wf_nil (ti_F_ty [] ti_wf_nil) eq_refl). Qed.

Lemma ti_red_bF : si_Σ ;;; [] ⊢ ti_bF ⇝ ti_F.
Proof.
  split; [reflexivity|reflexivity|]. apply rt_step. exact (red_beta si_Σ [] si_na si_P (tRel 0) ti_F).
Qed.

(** *** The primitive-integer environment [Σ_po] *)

(** [PCUICEtaPrimOpInstance.Σ_po_wf], unsquashed: the same proof. *)
Lemma ti_po_wf_ext : wf_ext Σ_po.
Proof.
  split; [|exact po_udecl_ok].
  split; [exact po_univs_ok|]. split; [exact po_retro_wf|].
  cbn. constructor.
  - constructor; [constructor|].
    econstructor.
    + constructor.
    + exact po_udecl_ok.
    + cbn. split; [exact tt|]. exists (Sort.super Sort.type0). repeat split. apply po_int_type.
    + cbn. intros op hop. discriminate hop.
  - econstructor.
    + constructor; [intros [=]|constructor].
    + exact po_udecl_ok.
    + cbn. split; [exact tt|].
      exists (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0)).
      repeat split. exact po_land_type_typed.
    + cbn. intros op hop. injection hop as <-.
      constructor; cbn; try reflexivity.
      * exists po_land_ty. split; [reflexivity|]. apply cumul_Refl.
      * repeat constructor.
        all: exists po_int_kn, po_int_body; split; [reflexivity|now left|split; reflexivity].
      * exists po_int_kn, po_int_body; split; [reflexivity|now left|split; reflexivity].
Qed.

Definition ti_po_wf : wf Σ_po := fst ti_po_wf_ext.
Definition ti_po_wfE : wfE Σ_po := wf_incl_E ti_po_wf.

Lemma ti_po_int_declared : declared_constant Σ_po po_int_kn po_int_body.
Proof. right; left; reflexivity. Qed.

Lemma ti_po_int_tag : prim_op_tag_declared Σ_po primInt.
Proof. exists po_int_kn, po_int_body; split; [reflexivity|exact ti_po_int_declared|split; reflexivity]. Qed.

(** *** Helpers of the upgraded instances

  In [ti_ΓP = [A : Prop]]: the spine of [I A] and the substitution of [A] for the parameter of [I]; the
  β-redex [(λ X : Prop. X) A] ([ti_idA]) and its reduct [A]; [I A] at [Type] by cumulativity; the context
  [x : I ((λ X : Prop. X) A)] ([ti_ΓX]); [f : Π _ : (λ X : Prop. X) A. (λ X : Prop. X) A] ([ti_Γf]) and
  [a : A] after it ([ti_Γfa]); the telescope [(X : Prop) (Y := X)] with a let-in ([ti_Δlet]). In [Σ_po]:
  the context [x : int] ([ti_Γint]). *)

Lemma ti_tspine_IA : PCUICArities.typing_spine si_Σ ti_ΓP (ind_type si_idecl)@[[]] [tRel 0] (tSort sProp).
Proof.
  exact (fst (PCUICInductives.invert_type_mkApps_ind si_Σ ti_ΓP si_ind [] [tRel 0] (tSort sProp) si_mdecl si_idecl
                si_wf si_declared_inductive ti_IA_ty)).
Qed.

Lemma ti_spine_A : PCUICSpine.spine_subst si_Σ ti_ΓP [tRel 0] [tRel 0] ti_ΓP.
Proof.
  split.
  - exact ti_wf_ΓP.
  - exact (ti_wf_P ti_ΓP ti_wf_ΓP).
  - exact (context_subst_ass [] [] [] si_na si_P (tRel 0) context_subst_nil).
  - exact (PCUICSubstitution.cons_let_ass si_Σ ti_ΓP [] [] si_na (tRel 0) si_P
             (PCUICSubstitution.emptyslet si_Σ ti_ΓP) ti_A_ty).
Qed.

Definition ti_idP : term := tLambda si_na si_P (tRel 0).
Definition ti_idA : term := tApp ti_idP (tRel 0).

Lemma ti_idP_ty Γ : wf_local si_Σ Γ -> si_Σ ;;; Γ |- ti_idP : tProd si_na si_P si_P.
Proof.
  intros h.
  exact (type_Lambda _ _ si_na si_P (tRel 0) si_P (ti_vass _ si_na si_P _ (ti_P_ty Γ h) eq_refl)
           (type_Rel _ _ 0 (vass si_na si_P) (ti_wf_P Γ h) eq_refl)).
Qed.

(** [(λ X : Prop. X) a : Prop] for every proposition [a]. *)
Lemma ti_idapp_ty Γ a : wf_local si_Σ Γ -> si_Σ ;;; Γ |- a : si_P -> si_Σ ;;; Γ |- tApp ti_idP a : si_P.
Proof.
  intros h ha. exact (type_App _ _ ti_idP si_na si_P si_P _ a (ti_arity_ty Γ h) (ti_idP_ty Γ h) ha).
Qed.

Lemma ti_idA_ty : si_Σ ;;; ti_ΓP |- ti_idA : si_P.
Proof. exact (ti_idapp_ty ti_ΓP (tRel 0) ti_wf_ΓP ti_A_ty). Qed.

Lemma ti_red_idA : si_Σ ;;; ti_ΓP ⊢ ti_idA ⇝ tRel 0.
Proof. split; [reflexivity|reflexivity|]. apply rt_step. exact (red_beta si_Σ ti_ΓP si_na si_P (tRel 0) (tRel 0)). Qed.

(** [I A : Type], by the cumulativity [Prop ≤ Type]. *)
Lemma ti_IA_ty1 : si_Σ ;;; ti_ΓP |- ti_IA : tSort (Sort.super sProp).
Proof.
  refine (type_Cumul _ _ ti_IA (tSort sProp) (tSort (Sort.super sProp)) _ ti_IA_ty (ti_P1_ty ti_ΓP ti_wf_ΓP) _).
  apply cumul_Sort. first [exact eq_refl|exact I|cbn; trivial].
Qed.

(** [x : I ((λ X : Prop. X) A)] over [ti_ΓP]. *)
Definition ti_ΓX : context := ti_ΓP ,, vass si_na (tApp (tInd si_ind []) ti_idA).

Lemma ti_wf_ΓX : wf_local si_Σ ti_ΓX.
Proof.
  exact (ti_wf_cons ti_ΓP si_na (tApp (tInd si_ind []) ti_idA) sProp ti_wf_ΓP
           (ti_Iapp_ty ti_ΓP ti_idA ti_wf_ΓP ti_idA_ty) eq_refl).
Qed.

Lemma ti_red_idA1 : si_Σ ;;; ti_ΓX ⊢ tApp ti_idP (tRel 1) ⇝ tRel 1.
Proof. split; [reflexivity|reflexivity|]. apply rt_step. exact (red_beta si_Σ ti_ΓX si_na si_P (tRel 0) (tRel 1)). Qed.

Lemma ti_red_IidA1 : si_Σ ;;; ti_ΓX ⊢ tApp (tInd si_ind []) (tApp ti_idP (tRel 1)) ⇝ tApp (tInd si_ind []) (tRel 1).
Proof.
  split; [reflexivity|reflexivity|]. apply rt_step. apply app_red_r.
  exact (red_beta si_Σ ti_ΓX si_na si_P (tRel 0) (tRel 1)).
Qed.

(** [f : Π _ : (λ X : Prop. X) A. (λ X : Prop. X) A] over [ti_ΓP], then [a : A]; [ti_Tf] is the type of [f]
    in [ti_Γf]. *)
Definition ti_pidA : term := tProd si_na ti_idA (tApp ti_idP (tRel 1)).
Definition ti_Γf : context := ti_ΓP ,, vass si_na ti_pidA.
Definition ti_Γfa : context := ti_Γf ,, vass si_na (tRel 1).
Definition ti_Tf : term := tProd si_na (tApp ti_idP (tRel 1)) (tApp ti_idP (tRel 2)).

Lemma ti_pidA_ty : si_Σ ;;; ti_ΓP |- ti_pidA : tSort (Sort.sort_of_product sProp sProp).
Proof.
  have h1 : wf_local si_Σ (ti_ΓP ,, vass si_na ti_idA) :=
    ti_wf_cons ti_ΓP si_na ti_idA sProp ti_wf_ΓP ti_idA_ty eq_refl.
  exact (type_Prod _ _ si_na ti_idA (tApp ti_idP (tRel 1)) sProp sProp
           (ti_vass_s ti_ΓP si_na ti_idA sProp ti_idA_ty eq_refl)
           (ti_idapp_ty _ (tRel 1) h1 (type_Rel _ _ 1 (vass si_na si_P) h1 eq_refl))).
Qed.

Lemma ti_wf_Γf : wf_local si_Σ ti_Γf.
Proof. exact (ti_wf_cons ti_ΓP si_na ti_pidA (Sort.sort_of_product sProp sProp) ti_wf_ΓP ti_pidA_ty eq_refl). Qed.

Lemma ti_wf_Γfa : wf_local si_Σ ti_Γfa.
Proof.
  exact (ti_wf_cons ti_Γf si_na (tRel 1) sProp ti_wf_Γf (type_Rel _ _ 1 (vass si_na si_P) ti_wf_Γf eq_refl) eq_refl).
Qed.

Lemma ti_red_A1f : si_Σ ;;; ti_Γf ⊢ tApp ti_idP (tRel 1) ⇝ tRel 1.
Proof. split; [reflexivity|reflexivity|]. apply rt_step. exact (red_beta si_Σ ti_Γf si_na si_P (tRel 0) (tRel 1)). Qed.

Lemma ti_red_B1f : si_Σ ;;; ti_Γf ,, vass si_na (tApp ti_idP (tRel 1)) ⊢ tApp ti_idP (tRel 2) ⇝ tRel 2.
Proof.
  split; [reflexivity|reflexivity|]. apply rt_step.
  exact (red_beta si_Σ (ti_Γf ,, vass si_na (tApp ti_idP (tRel 1))) si_na si_P (tRel 0) (tRel 2)).
Qed.

Lemma ti_red_Tf : si_Σ ;;; ti_Γf ⊢ ti_Tf ⇝ tProd si_na (tRel 1) (tRel 2).
Proof.
  split; [reflexivity|reflexivity|].
  eapply rt_trans; [apply rt_step; apply prod_red_l; exact (red_beta si_Σ ti_Γf si_na si_P (tRel 0) (tRel 1))|].
  apply rt_step. apply prod_red_r.
  exact (red_beta si_Σ (ti_Γf ,, vass si_na (tRel 1)) si_na si_P (tRel 0) (tRel 2)).
Qed.

Lemma ti_red_A2fa : si_Σ ;;; ti_Γfa ⊢ tApp ti_idP (tRel 2) ⇝ tRel 2.
Proof. split; [reflexivity|reflexivity|]. apply rt_step. exact (red_beta si_Σ ti_Γfa si_na si_P (tRel 0) (tRel 2)). Qed.

Lemma ti_red_Tfa :
  si_Σ ;;; ti_Γfa ⊢ tProd si_na (tApp ti_idP (tRel 2)) (tApp ti_idP (tRel 3)) ⇝ tProd si_na (tRel 2) (tRel 3).
Proof.
  split; [reflexivity|reflexivity|].
  eapply rt_trans; [apply rt_step; apply prod_red_l; exact (red_beta si_Σ ti_Γfa si_na si_P (tRel 0) (tRel 2))|].
  apply rt_step. apply prod_red_r.
  exact (red_beta si_Σ (ti_Γfa ,, vass si_na (tRel 2)) si_na si_P (tRel 0) (tRel 3)).
Qed.

(** The telescope [(X : Prop) (Y : Prop := X)], as a context ([Y] first). *)
Definition ti_Δlet : context := [vdef si_na (tRel 0) si_P; vass si_na si_P].

Lemma ti_wf_Δlet : wf_local si_Σ (ti_ΓP ,,, ti_Δlet).
Proof.
  have h1 := ti_wf_P ti_ΓP ti_wf_ΓP.
  change (wf_local si_Σ ((ti_ΓP ,, vass si_na si_P) ,, vdef si_na (tRel 0) si_P)).
  apply localenv_cons_def; [exact h1|].
  split; [exact (type_Rel _ _ 0 (vass si_na si_P) h1 eq_refl)|].
  exists (Sort.super sProp). split; [exact (ti_P_ty _ h1)|split; [exact I|reflexivity]].
Qed.

Lemma ti_wf_letA : wf_local si_Σ (ti_ΓP ,, vdef si_na (tRel 0) si_P).
Proof.
  apply localenv_cons_def; [exact ti_wf_ΓP|].
  split; [exact ti_A_ty|].
  exists (Sort.super sProp). split; [exact (ti_P_ty _ ti_wf_ΓP)|split; [exact I|reflexivity]].
Qed.

(** [let Y : Prop := A in Prop ⇝ Prop] (ζ). *)
Lemma ti_red_TL : si_Σ ;;; ti_ΓP ⊢ tLetIn si_na (tRel 0) si_P si_P ⇝ tSort sProp.
Proof. split; [reflexivity|reflexivity|]. apply rt_step. exact (red_zeta si_Σ ti_ΓP si_na (tRel 0) si_P si_P). Qed.

(** The spine of [Π X : Prop. let Y : Prop := X in Prop] applied to [A]. *)
Lemma ti_tspine_let :
  PCUICArities.typing_spine si_Σ ti_ΓP (it_mkProd_or_LetIn ti_Δlet (tSort sProp)) [tRel 0] (tSort sProp).
Proof.
  have hT : isType si_Σ ti_ΓP (it_mkProd_or_LetIn ti_Δlet (tSort sProp)).
  { apply (PCUICInductiveInversion.isType_it_mkProd_or_LetIn (Σ := si_Σ) (Γ := ti_ΓP) (Δ := ti_Δlet) si_wf).
    exact (has_sort_isType _ (ti_P_ty _ ti_wf_Δlet)). }
  have hL : isType si_Σ ti_ΓP (tLetIn si_na (tRel 0) si_P (tSort sProp)).
  { apply (PCUICInductiveInversion.isType_it_mkProd_or_LetIn (Σ := si_Σ) (Γ := ti_ΓP)
             (Δ := [vdef si_na (tRel 0) si_P]) (T := tSort sProp) si_wf).
    exact (has_sort_isType _ (ti_P_ty _ ti_wf_letA)). }
  refine (PCUICArities.type_spine_cons (na := si_na) (A := si_P) (B := tLetIn si_na (tRel 0) si_P (tSort sProp))
            hT hT (ti_ws_refl ti_ΓP (tProd si_na si_P (tLetIn si_na (tRel 0) si_P (tSort sProp))) eq_refl eq_refl)
            ti_A_ty _).
  econstructor.
  - exact hL.
  - exact (has_sort_isType _ (ti_P_ty ti_ΓP ti_wf_ΓP)).
  - exact (PCUICWellScopedCumulativity.red_ws_cumul_pb (Σ := si_Σ) (wfΣ := si_wf) ti_red_TL).
Qed.

(** [x : int] in [Σ_po]. *)
Definition ti_Γint : context := [vass si_na (tConst po_int_kn [])].

Lemma ti_wf_Γint : wf_local Σ_po ti_Γint.
Proof.
  apply localenv_cons_abs; [constructor|].
  split; [exact tt|]. exists Sort.type0.
  split; [exact (po_int_typed Σ_po [] ltac:(constructor) ti_po_int_declared)|split; [exact I|reflexivity]].
Qed.

(** ** Instances of [T0_facts]

  Each lemma [<field>_inst] below states the premises and the conclusion of the field [<field>] of
  [T0_facts] at concrete arguments in [si_Σ] (the premise [wfE] holds there by [si_wfE]), builds each
  typed premise from a base derivation lifted with [typing_incl_E], and proves the conclusion from the base
  lemma of the same name. (1) This instance shows that the hypothesis is consistent and about something
  real. (2) It does NOT discharge the hypothesis at [typingE]: the field remains a hypothesis until plan
  row T0 (the E copies of the typing infrastructure) lands. *)

(* non-degenerate *)
Lemma closed_context_cumulativity_inst :
  [× si_Σ ;;; ti_ΓbF |-E tRel 0 : ti_bF, wf_localE si_Σ ti_ΓF, ws_cumul_ctx_pbE Cumul si_Σ ti_ΓF ti_ΓbF &
     si_Σ ;;; ti_ΓF |-E tRel 0 : ti_bF].
Proof.
  have ht : si_Σ ;;; ti_ΓbF |- tRel 0 : ti_bF := type_Rel _ _ 0 (vass si_na ti_bF) ti_wf_ΓbF eq_refl.
  (* [ti_F ≤ (λ X : Prop. X) ti_F], by the β-reduction read backwards *)
  have hc : si_Σ ;;; [] ⊢ ti_F ≤[Cumul] ti_bF :=
    PCUICWellScopedCumulativity.red_ws_cumul_pb_inv (Σ := si_Σ) (wfΣ := si_wf) ti_red_bF.
  have hctx : ws_cumul_ctx_pb Cumul si_Σ ti_ΓF ti_ΓbF.
  { constructor; [constructor|]. constructor; [reflexivity|exact hc]. }
  have hE : ws_cumul_ctx_pbE Cumul si_Σ ti_ΓF ti_ΓbF.
  { constructor; [constructor|]. constructor; [reflexivity|exact (siC hc)]. }
  split; [exact (siT ht)|exact (siW ti_wf_ΓF)|exact hE|].
  exact (siT (PCUICContextConversionTyp.closed_context_cumulativity (Σ := si_Σ) (wfΣ := si_wf) ti_ΓbF
                (pb := Cumul) (Γ' := ti_ΓF) ht ti_wf_ΓF hctx)).
Qed.

(* degenerate: NOT BUILT — I has no indices, so the conclusion compares two empty index contexts (also Γ = [], u = u', pars = pars'); a real point needs an indexed family, and u ≠ u' a cumulative universe-polymorphic one; COST: a new indexed inductive family (e.g. an equality-like [J : Prop -> Prop] with a constructor taking arguments) declared in a new environment, with its whole on_global_env proof (on_inductive / on_ind_body: arity typing, constructor typing, positivity, universe constraints, ind_arity_red), none of which si_Σ's helpers provide; stream lead 2026-10-29: stays NOT BUILT unless FRAC needs it *)
Lemma inductive_cumulative_indices_inst :
  [× declared_inductive si_Σ si_ind si_mdecl si_idecl,
     consistent_instance_ext si_Σ (ind_universes si_mdecl) [],
     consistent_instance_ext si_Σ (ind_universes si_mdecl) [],
     PCUICEquality.cmp_ind_universes si_Σ si_ind 0 [] [],
     spine_substE si_Σ [] [ti_F] [ti_F] (ind_params si_mdecl)@[[]],
     spine_substE si_Σ [] [ti_F] [ti_F] (ind_params si_mdecl)@[[]],
     ws_cumul_pbE_terms si_Σ [] [ti_F] [ti_F] &
     let indctx := (ind_indices si_idecl)@[[]] in
     let indctx' := (ind_indices si_idecl)@[[]] in
     let pindctx := subst_context [ti_F] 0 indctx in
     let pindctx' := subst_context [ti_F] 0 indctx' in
     ws_cumul_ctx_pbE_rel Cumul si_Σ [] (smash_context [] pindctx) (smash_context [] pindctx')].
Proof.
  have hcmp : PCUICEquality.cmp_ind_universes si_Σ si_ind 0 [] [].
  { unfold PCUICEquality.cmp_ind_universes. apply cmp_global_instance_refl; tc. }
  pose proof (ti_spine_F : PCUICSpine.spine_subst si_Σ [] [ti_F] [ti_F] (ind_params si_mdecl)@[[]]) as hs.
  have hw : All2 (ws_cumul_pb Conv si_Σ []) [ti_F] [ti_F] := All2_cons (ti_ws_refl [] ti_F eq_refl eq_refl) All2_nil.
  have hb := PCUICInductiveInversion.inductive_cumulative_indices (Σ := si_Σ) (wfΣ := si_wf)
    si_declared_inductive ti_cons ti_cons hcmp [] [ti_F] [ti_F] [ti_F] [ti_F] hs hs hw.
  split; [exact si_declared_inductive|exact ti_cons|exact ti_cons|exact hcmp|exact (siS hs)|exact (siS hs)
         |exact (All2_cons (fi_ws Conv [] ti_F eq_refl eq_refl) All2_nil)|].
  (* the base conclusion gives the scoping of the context; the indices of [I] are empty, so the
     comparison of the two (empty) smashed index contexts is the empty one *)
  cbv zeta in hb |- *. destruct hb as [hc _]. split; [exact hc|cbn; constructor].
Qed.

(* non-degenerate *)
Lemma invert_type_mkApps_ind_inst :
  [× wfE si_Σ.1, declared_inductive si_Σ.1 si_ind si_mdecl si_idecl,
     si_Σ ;;; ti_ΓP |-E mkApps (tInd si_ind []) [tRel 0] : tSort sProp &
     typing_spineE si_Σ ti_ΓP (ind_type si_idecl)@[[]] [tRel 0] (tSort sProp) ×
     consistent_instance_ext si_Σ (ind_universes si_mdecl) []].
Proof.
  have h : si_Σ ;;; ti_ΓP |- mkApps (tInd si_ind []) [tRel 0] : tSort sProp := ti_IA_ty.
  destruct (PCUICInductives.invert_type_mkApps_ind si_Σ ti_ΓP si_ind [] [tRel 0] (tSort sProp) si_mdecl si_idecl
              si_wf si_declared_inductive h) as [hs hc].
  split; [exact si_wfE|exact si_declared_inductive|exact (siT h)|split; [exact (siTS hs)|exact hc]].
Qed.

(* degenerate: NOT BUILT — c has no arguments and I has no indices, so the ctx_inst premise is over empty lists, and the user arity of I is already the built arity (the red premise is reflexive); a real point needs an indexed family; COST: a new indexed inductive family (e.g. an equality-like [J : Prop -> Prop] with a constructor taking arguments) declared in a new environment, with its whole on_global_env proof (on_inductive / on_ind_body: arity typing, constructor typing, positivity, universe constraints, ind_arity_red), none of which si_Σ's helpers provide; stream lead 2026-10-29: stays NOT BUILT unless FRAC needs it *)
Lemma isTypeRel_cstr_type_inst :
  [× wfE si_Σ.1,
     nth_error (ind_bodies si_mdecl) 0 = Some si_idecl,
     cstr_type si_cdecl =
       it_mkProd_or_LetIn (ind_params si_mdecl ,,, cstr_args si_cdecl)
         (mkApps (tRel (#|ind_params si_mdecl ,,, cstr_args si_cdecl| + (#|ind_bodies si_mdecl| - S 0)))
            (to_extended_list_k (ind_params si_mdecl) #|cstr_args si_cdecl| ++ cstr_indices si_cdecl)),
     isTypeE si_Σ [] (ind_type si_idecl),
     PCUICReduction.red si_Σ.1 [] (ind_type si_idecl)
       (it_mkProd_or_LetIn (ind_params si_mdecl) (it_mkProd_or_LetIn (ind_indices si_idecl) (tSort (ind_sort si_idecl)))),
     isTypeE si_Σ [] (it_mkProd_or_LetIn (ind_params si_mdecl)
                       (it_mkProd_or_LetIn (ind_indices si_idecl) (tSort (ind_sort si_idecl)))),
     isSortRel (ind_sort si_idecl) (ind_relevance si_idecl),
     ctx_instE si_Σ (arities_context (ind_bodies si_mdecl) ,,, ind_params si_mdecl ,,, cstr_args si_cdecl)
       (cstr_indices si_cdecl) (List.rev (lift_context #|cstr_args si_cdecl| 0 (ind_indices si_idecl))),
     isTypeE si_Σ (arities_context (ind_bodies si_mdecl)) (cstr_type si_cdecl) &
     isTypeRelE si_Σ (arities_context (ind_bodies si_mdecl)) (cstr_type si_cdecl) (ind_relevance si_idecl)].
Proof.
  have hT : isType si_Σ [] (ind_type si_idecl) := has_sort_isType _ (ti_arity_ty [] ti_wf_nil).
  have hT' : isType si_Σ [] (it_mkProd_or_LetIn (ind_params si_mdecl)
                (it_mkProd_or_LetIn (ind_indices si_idecl) (tSort (ind_sort si_idecl)))) := hT.
  have hr : PCUICReduction.red si_Σ.1 [] (ind_type si_idecl)
              (it_mkProd_or_LetIn (ind_params si_mdecl) (it_mkProd_or_LetIn (ind_indices si_idecl)
                 (tSort (ind_sort si_idecl)))) by apply rt_refl.
  have hci : ctx_inst si_Σ (arities_context (ind_bodies si_mdecl) ,,, ind_params si_mdecl ,,, cstr_args si_cdecl)
               (cstr_indices si_cdecl) (List.rev (lift_context #|cstr_args si_cdecl| 0 (ind_indices si_idecl)))
    by (cbn; constructor).
  have hC : isType si_Σ (arities_context (ind_bodies si_mdecl)) (cstr_type si_cdecl) :=
    has_sort_isType _ ti_ctype_ty.
  split; [exact si_wfE|reflexivity|reflexivity|exact (siI hT)|exact hr|exact (siI hT')|reflexivity
         |exact (siCI hci)|exact (siI hC)|].
  exact (siIR (PCUICInductiveInversion.isTypeRel_cstr_type si_Σ si_mdecl si_idecl si_cdecl 0 si_wf
                 eq_refl eq_refl hT hr hT' eq_refl hci hC)).
Qed.

(* non-degenerate *)
Lemma isType_mkApps_Ind_inst :
  [× declared_inductive si_Σ si_ind si_mdecl si_idecl,
     consistent_instance_ext si_Σ (ind_universes si_mdecl) [],
     spine_substE si_Σ ti_ΓP [tRel 0] [tRel 0] (ind_params si_mdecl ,,, ind_indices si_idecl)@[[]] &
     si_Σ ;;; ti_ΓP |-E mkApps (tInd si_ind []) [tRel 0] : tSort (ind_sort si_idecl)@[[]]].
Proof.
  pose proof (ti_spine_A :
    PCUICSpine.spine_subst si_Σ ti_ΓP [tRel 0] [tRel 0] (ind_params si_mdecl ,,, ind_indices si_idecl)@[[]]) as hs.
  split; [exact si_declared_inductive|exact ti_cons|exact (siS hs)|].
  exact (siT (PCUICInductives.isType_mkApps_Ind (Σ := si_Σ) (wfΣ := si_wf) si_declared_inductive (Γ := ti_ΓP)
                ti_cons hs)).
Qed.

(* degenerate: NOT BUILT — I has no indices, so the index half of the split (skipn ind_npars args, argsubst) is empty; a real point needs an indexed family (Γ = [A : Prop] and the parameter A are real); COST: a new indexed inductive family (e.g. an equality-like [J : Prop -> Prop] with a constructor taking arguments) declared in a new environment, with its whole on_global_env proof (on_inductive / on_ind_body: arity typing, constructor typing, positivity, universe constraints, ind_arity_red), none of which si_Σ's helpers provide; stream lead 2026-10-29: stays NOT BUILT unless FRAC needs it *)
Lemma isType_mkApps_Ind_inv_inst :
  [× wfE si_Σ.1, declared_inductive si_Σ.1 si_ind si_mdecl si_idecl, wf_localE si_Σ ti_ΓP,
     isTypeE si_Σ ti_ΓP (mkApps (tInd si_ind []) [tRel 0]) &
     ∑ parsubst argsubst : list term,
       let parctx := (ind_params si_mdecl)@[[]] in
       let argctx := subst_context parsubst 0 (ind_indices si_idecl)@[[]] in
       [× spine_substE si_Σ ti_ΓP (firstn (ind_npars si_mdecl) [tRel 0]) parsubst parctx,
          spine_substE si_Σ ti_ΓP (skipn (ind_npars si_mdecl) [tRel 0]) argsubst argctx,
          #|firstn (ind_npars si_mdecl) [tRel 0]| = ind_npars si_mdecl,
          #|skipn (ind_npars si_mdecl) [tRel 0]| = context_assumptions (ind_indices si_idecl) &
          consistent_instance_ext si_Σ (ind_universes si_mdecl) []]].
Proof.
  have hI : isType si_Σ ti_ΓP (mkApps (tInd si_ind []) [tRel 0]) := has_sort_isType _ ti_IA_ty.
  destruct (PCUICInductives.isType_mkApps_Ind_inv (Σ := si_Σ) (Γ := ti_ΓP) si_wf si_declared_inductive ti_wf_ΓP hI)
    as [ps [as' h]].
  cbv zeta in h. destruct h as [h1 h2 h3 h4 h5].
  split; [exact si_wfE|exact si_declared_inductive|exact (siW ti_wf_ΓP)|exact (siI hI)|].
  exists ps, as'. cbv zeta.
  split; [exact (siS h1)|exact (siS h2)|exact h3|exact h4|exact h5].
Qed.

(* non-degenerate *)
Lemma on_minductive_wf_params_inst :
  [× declared_minductive si_Σ.1 si_kn si_mdecl, consistent_instance_ext si_Σ (ind_universes si_mdecl) [] &
     wf_localE si_Σ (ind_params si_mdecl)@[[]]].
Proof.
  split; [exact ti_declared_minductive|exact ti_cons|].
  exact (siW (PCUICArities.on_minductive_wf_params (Σ := si_Σ) (wfΣ := si_wf) ti_declared_minductive ti_cons)).
Qed.

(* non-degenerate *)
Lemma on_minductive_wf_params_indices_inst_inst :
  [× declared_inductive si_Σ si_ind si_mdecl si_idecl, consistent_instance_ext si_Σ (ind_universes si_mdecl) [] &
     wf_localE si_Σ (ind_params si_mdecl ,,, ind_indices si_idecl)@[[]]].
Proof.
  split; [exact si_declared_inductive|exact ti_cons|].
  exact (siW (PCUICInductives.on_minductive_wf_params_indices_inst (Σ := si_Σ) (wfΣ := si_wf)
                si_declared_inductive [] ti_cons)).
Qed.


Lemma ti_Rel0_ty : si_Σ ;;; [] ,,, ti_ΓP ,,, [] |- tRel 0 : si_P.
Proof. exact (type_Rel _ _ 0 (vass si_na si_P) ti_wf_ΓP eq_refl). Qed.

(* degenerate: NOT BUILT — the user arity of I is already the built arity, so the premise's and the conclusion's spines are over the same type; on_ind_body's ind_arity_red only asks the user arity to REDUCE to the built one, so an inductive declared with a redex in its arity gives a real point (Γ = [A : Prop] and the argument A are real); COST: a new inductive declared with a redex in its user arity, in a new environment, with its whole on_global_env proof (on_inductive / on_ind_body: arity typing and its ind_arity_red reduction, constructor typing, positivity, universe constraints), none of which si_Σ's helpers provide; stream lead 2026-10-29: stays NOT BUILT unless FRAC needs it *)
Lemma typing_spine_ind_type_inv_inst :
  [× declared_inductive si_Σ si_ind si_mdecl si_idecl, wf_localE si_Σ ti_ΓP,
     consistent_instance_ext si_Σ (ind_universes si_mdecl) [],
     typing_spineE si_Σ ti_ΓP (ind_type si_idecl)@[[]] [tRel 0] (tSort sProp) &
     typing_spineE si_Σ ti_ΓP
       (it_mkProd_or_LetIn (ind_params si_mdecl ,,, ind_indices si_idecl) (tSort (ind_sort si_idecl)))@[[]]
       [tRel 0] (tSort sProp)].
Proof.
  split; [exact si_declared_inductive|exact (siW ti_wf_ΓP)|exact ti_cons|exact (siTS ti_tspine_IA)|].
  exact (siTS (PCUICInductives.typing_spine_ind_type_inv (Σ := si_Σ) (wfΣ := si_wf) si_declared_inductive
                 ti_ΓP [] [tRel 0] (tSort sProp) ti_wf_ΓP ti_cons ti_tspine_IA)).
Qed.

(** A case on [I ti_F]: the predicate [fun (_ : I ti_F) => Prop] and the branch of [c]. *)
Definition ti_ci : case_info := {| ci_ind := si_ind; ci_npar := 1; ci_relevance := Relevant; ci_cofix_nondep := true |}.
Definition ti_p : predicate term :=
  {| pparams := [ti_F]; puinst := []; pcontext := ind_predicate_context si_ind si_mdecl si_idecl;
     preturn := si_P |}.
Definition ti_br : branch term := {| bcontext := []; bbody := si_P |}.

Lemma ti_wfpred : wf_predicate si_mdecl si_idecl ti_p.
Proof. split; [reflexivity|repeat constructor]. Qed.

Lemma ti_eqctx : All2 PCUICEquality.eq_decl_upto_names (pcontext ti_p) (ind_predicate_context ti_ci si_mdecl si_idecl).
Proof. cbn. repeat constructor. Qed.

Lemma ti_wfbr : wf_branch si_cdecl ti_br.
Proof. constructor. Qed.

Lemma ti_wfbrs : wf_branches si_idecl [ti_br].
Proof. constructor; [exact ti_wfbr|constructor]. Qed.

Lemma ti_isT_case : isType si_Σ [] (mkApps (tInd ti_ci (puinst ti_p)) (pparams ti_p ++ [])).
Proof. exact (has_sort_isType _ (ti_IF_ty [] ti_wf_nil)). Qed.

Lemma ti_wf_predctx : wf_local si_Σ ([] ,,, case_predicate_context ti_ci si_mdecl si_idecl ti_p).
Proof.
  have h := PCUICInductiveInversion.wf_case_predicate_context (Σ := si_Σ) (wfΣ := si_wf) (Γ := [])
    (ci := ti_ci) (p := ti_p) (args := []) si_declared_inductive ti_isT_case ti_wfpred.
  cbv zeta in h. exact h.
Qed.

Lemma ti_ret_ty :
  si_Σ ;;; [] ,,, case_predicate_context ti_ci si_mdecl si_idecl ti_p |- preturn ti_p : tSort (Sort.super sProp).
Proof. exact (ti_P_ty _ ti_wf_predctx). Qed.

(* degenerate: NOT BUILT — args = [] because I has no indices, c has no arguments (empty branch context), Γ = [] and the return type is Prop; a real point needs an indexed family whose constructor takes arguments; COST: a new indexed inductive family (e.g. an equality-like [J : Prop -> Prop] with a constructor taking arguments) declared in a new environment, with its whole on_global_env proof (on_inductive / on_ind_body: arity typing, constructor typing, positivity, universe constraints, ind_arity_red), none of which si_Σ's helpers provide; stream lead 2026-10-29: stays NOT BUILT unless FRAC needs it *)
Lemma wf_case_branch_type_inst :
  [× declared_inductive si_Σ ti_ci si_mdecl si_idecl,
     isTypeE si_Σ [] (mkApps (tInd ti_ci (puinst ti_p)) (pparams ti_p ++ [])),
     wf_predicate si_mdecl si_idecl ti_p,
     si_Σ ;;; [] ,,, case_predicate_context ti_ci si_mdecl si_idecl ti_p |-E preturn ti_p : tSort (Sort.super sProp),
     All2 PCUICEquality.eq_decl_upto_names (pcontext ti_p) (ind_predicate_context ti_ci si_mdecl si_idecl),
     declared_constructor si_Σ (ti_ci, 0) si_mdecl si_idecl si_cdecl,
     wf_branch si_cdecl ti_br &
     let predctx := case_predicate_context ti_ci si_mdecl si_idecl ti_p in
     let ptm := it_mkLambda_or_LetIn predctx (preturn ti_p) in
     let cstr_br_ctx := case_branch_context_nopars ti_ci si_mdecl (puinst ti_p) si_cdecl in
     let brctx' := map2 set_binder_name (forget_types (bcontext ti_br)) cstr_br_ctx in
     let brctxty := case_branch_type ti_ci si_mdecl si_idecl ti_p ti_br ptm 0 si_cdecl in
     [× wf_branch si_cdecl ti_br,
        wf_localE si_Σ ([] ,,, (ind_params si_mdecl)@[puinst ti_p] ,,, cstr_br_ctx),
        wf_localE si_Σ ([] ,,, (ind_params si_mdecl)@[puinst ti_p] ,,, brctx'),
        wf_localE si_Σ ([] ,,, brctxty.1) &
        si_Σ ;;; [] ,,, brctxty.1 |-E brctxty.2 : tSort (Sort.super sProp)]].
Proof.
  have hb := PCUICInductiveInversion.wf_case_branch_type (Σ := si_Σ) (wfΣ := si_wf) (Γ := []) (ci := ti_ci)
    (p := ti_p) (Sort.super sProp) [] si_declared_inductive ti_isT_case ti_wfpred ti_ret_ty ti_eqctx
    0 si_cdecl ti_br si_declared_constructor ti_wfbr.
  cbv zeta in hb. destruct hb as [b1 b2 b3 b4 b5].
  split; [exact si_declared_inductive|exact (siI ti_isT_case)|exact ti_wfpred|exact (siT ti_ret_ty)
         |exact ti_eqctx|exact si_declared_constructor|exact ti_wfbr|].
  cbv zeta. split; [exact b1|exact (siW b2)|exact (siW b3)|exact (siW b4)|exact (siT b5)].
Qed.

(* degenerate: NOT BUILT — args = [] because I has no indices, and Γ = []; a real point needs an indexed family; COST: a new indexed inductive family (e.g. an equality-like [J : Prop -> Prop] with a constructor taking arguments) declared in a new environment, with its whole on_global_env proof (on_inductive / on_ind_body: arity typing, constructor typing, positivity, universe constraints, ind_arity_red), none of which si_Σ's helpers provide; stream lead 2026-10-29: stays NOT BUILT unless FRAC needs it *)
Lemma wf_case_predicate_context_inst :
  [× declared_inductive si_Σ ti_ci si_mdecl si_idecl,
     isTypeE si_Σ [] (mkApps (tInd ti_ci (puinst ti_p)) (pparams ti_p ++ [])),
     wf_predicate si_mdecl si_idecl ti_p &
     let predctx := case_predicate_context ti_ci si_mdecl si_idecl ti_p in wf_localE si_Σ ([] ,,, predctx)].
Proof.
  split; [exact si_declared_inductive|exact (siI ti_isT_case)|exact ti_wfpred|].
  cbv zeta. exact (siW ti_wf_predctx).
Qed.

(* degenerate: NOT BUILT — args = [] because I has no indices, c has no arguments (empty branch context), Γ = [] and the return type is Prop; a real point needs an indexed family whose constructor takes arguments; COST: a new indexed inductive family (e.g. an equality-like [J : Prop -> Prop] with a constructor taking arguments) declared in a new environment, with its whole on_global_env proof (on_inductive / on_ind_body: arity typing, constructor typing, positivity, universe constraints, ind_arity_red), none of which si_Σ's helpers provide; stream lead 2026-10-29: stays NOT BUILT unless FRAC needs it *)
Lemma wf_case_branches_types'_inst :
  [× declared_inductive si_Σ ti_ci si_mdecl si_idecl,
     isTypeE si_Σ [] (mkApps (tInd ti_ci (puinst ti_p)) (pparams ti_p ++ [])),
     wf_predicate si_mdecl si_idecl ti_p,
     si_Σ ;;; [] ,,, case_predicate_context ti_ci si_mdecl si_idecl ti_p |-E preturn ti_p : tSort (Sort.super sProp),
     wf_branches si_idecl [ti_br],
     All2 PCUICEquality.eq_decl_upto_names (pcontext ti_p) (ind_predicate_context ti_ci si_mdecl si_idecl) &
     let predctx := case_predicate_context ti_ci si_mdecl si_idecl ti_p in
     let ptm := it_mkLambda_or_LetIn predctx (preturn ti_p) in
     All2i (fun (i : nat) (cdecl : constructor_body) (br : branch term) =>
       let cstr_br_ctx := case_branch_context_nopars ti_ci si_mdecl (puinst ti_p) cdecl in
       let brctx' := map2 set_binder_name (forget_types (bcontext br)) cstr_br_ctx in
       let brctxty := case_branch_type ti_ci si_mdecl si_idecl ti_p br ptm i cdecl in
       [× wf_branch cdecl br,
          wf_localE si_Σ ([] ,,, (ind_params si_mdecl)@[puinst ti_p] ,,, cstr_br_ctx),
          wf_localE si_Σ ([] ,,, (ind_params si_mdecl)@[puinst ti_p] ,,, brctx'),
          wf_localE si_Σ ([] ,,, brctxty.1) &
          si_Σ ;;; [] ,,, brctxty.1 |-E brctxty.2 : tSort (Sort.super sProp)]) 0 (ind_ctors si_idecl) [ti_br]].
Proof.
  have hb := PCUICInductiveInversion.wf_case_branches_types' (Σ := si_Σ) (wfΣ := si_wf) (Γ := []) (ci := ti_ci)
    (p := ti_p) (Sort.super sProp) [] [ti_br] si_declared_inductive ti_isT_case ti_wfpred ti_ret_ty ti_wfbrs ti_eqctx.
  split; [exact si_declared_inductive|exact (siI ti_isT_case)|exact ti_wfpred|exact (siT ti_ret_ty)
         |exact ti_wfbrs|exact ti_eqctx|].
  cbv zeta in hb |- *.
  eapply All2i_impl; [exact hb|]. intros i cdecl br [b1 b2 b3 b4 b5].
  split; [exact b1|exact (siW b2)|exact (siW b3)|exact (siW b4)|exact (siT b5)].
Qed.

(** ** Instances of [U_facts]

  Each lemma [<field>_inst] states the premises and the conclusion of the field [<field>] of [U_facts] at
  concrete arguments in [si_Σ] (the premise [wfE] holds there by [si_wfE]) and proves the conclusion from
  the base lemma of the same name. (1) This instance shows that the hypothesis is consistent and about
  something real. (2) It does NOT discharge the hypothesis at [wfE]: the field remains a hypothesis until
  its proof over [wfE_ClosedBodies] lands (untyped plumbing: reduction is the same in E, [wf] serves only
  closed bodies and universes). *)

(** [let x : Prop := ti_F in I x], whose telescope has a let-in. *)
Definition ti_CLet : term := tLetIn si_na ti_F si_P (tApp (tInd si_ind []) (tRel 0)).

(* non-degenerate *)
Lemma whnf_red_inv_inst :
  [× wfE si_Σ, whnf RedFlags.default si_Σ ti_ΓP (tProd si_na ti_idA si_P),
     si_Σ ;;; ti_ΓP ⊢ tProd si_na ti_idA si_P ⇝ tProd si_na (tRel 0) si_P &
     whnf_red si_Σ ti_ΓP (tProd si_na ti_idA si_P) (tProd si_na (tRel 0) si_P)].
Proof.
  have hn : whnf RedFlags.default si_Σ ti_ΓP (tProd si_na ti_idA si_P) by apply whnf_prod.
  have hr : si_Σ ;;; ti_ΓP ⊢ tProd si_na ti_idA si_P ⇝ tProd si_na (tRel 0) si_P.
  { split; [reflexivity|reflexivity|]. apply rt_step. apply prod_red_l.
    exact (red_beta si_Σ ti_ΓP si_na si_P (tRel 0) (tRel 0)). }
  split; [exact si_wfE|exact hn|exact hr|].
  exact (PCUICNormal.whnf_red_inv (Σ := si_Σ) ti_ΓP _ _ si_wf hn hr).
Qed.

(** ** Instances of [T1_facts]

  Each lemma [<field>_inst] states the premises and the conclusion of the field [<field>] of [T1_facts] at
  concrete arguments (in [si_Σ], or for the primitive operations in [Σ_po] of [PCUICEtaPrimOpInstance],
  which registers [int]; the premise [wfE] holds by [si_wfE] and [ti_po_wfE]), builds each typed premise
  from a base derivation lifted with [typing_incl_E], and proves the conclusion from the base lemma of the
  same name. (1) This instance shows that the hypothesis is consistent and about something real. (2) It
  does NOT discharge the hypothesis at [typingE]: the field remains a hypothesis until plan row T1 (subject
  reduction over [typingE]) lands. *)

(* non-degenerate *)
Lemma isType_prim_shape_type_inst :
  [× wf_localE Σ_po ti_Γint,
     PCUICPrimOpType.prim_shape_type (retroknowledge Σ_po.1) SInt = Some (tConst po_int_kn []),
     on_prim_op_result Σ_po SInt & isTypeE Σ_po ti_Γint (tConst po_int_kn [])].
Proof.
  have hres : on_prim_op_result Σ_po SInt := ti_po_int_tag.
  split; [exact (ti_wfl Σ_po ti_po_wf ti_wf_Γint)|reflexivity|exact hres|].
  exact (ti_isType Σ_po ti_po_wf (PCUICSR.isType_prim_shape_type (Σ := Σ_po) (wfΣ := ti_po_wf) (Γ := ti_Γint)
           (s := SInt) (res := tConst po_int_kn []) ti_wf_Γint eq_refl hres)).
Qed.

(* non-degenerate *)
Lemma isType_red_inst :
  [× isTypeE si_Σ ti_ΓP ti_idA, PCUICReduction.red si_Σ ti_ΓP ti_idA (tRel 0) & isTypeE si_Σ ti_ΓP (tRel 0)].
Proof.
  have h : isType si_Σ ti_ΓP ti_idA := has_sort_isType sProp ti_idA_ty.
  have hr : PCUICReduction.red si_Σ ti_ΓP ti_idA (tRel 0) := clrel_rel ti_red_idA.
  split; [exact (siI h)|exact hr|].
  exact (siI (PCUICSR.isType_red (Σ := si_Σ) (wfΣ := si_wf) h hr)).
Qed.

(* non-degenerate *)
Lemma subject_reduction_inst :
  [× wfE si_Σ, si_Σ ;;; ti_ΓP |-E ti_idA : si_P, PCUICReduction.red si_Σ ti_ΓP ti_idA (tRel 0) &
     si_Σ ;;; ti_ΓP |-E tRel 0 : si_P].
Proof.
  have hr : PCUICReduction.red si_Σ ti_ΓP ti_idA (tRel 0) := clrel_rel ti_red_idA.
  split; [exact si_wfE|exact (siT ti_idA_ty)|exact hr|].
  exact (siT (PCUICSR.subject_reduction si_Σ ti_ΓP _ _ _ si_wf ti_idA_ty hr)).
Qed.

(** [x : (λ X : Prop. X) ti_F ⊢ x : ti_F], the type reduced by β. *)
Lemma ti_red_bF_ΓbF : si_Σ ;;; ti_ΓbF ⊢ ti_bF ⇝ ti_F.
Proof. split; [reflexivity|reflexivity|]. apply rt_step. exact (red_beta si_Σ ti_ΓbF si_na si_P (tRel 0) ti_F). Qed.

(* non-degenerate *)
Lemma type_reduction_closed_inst :
  [× si_Σ ;;; ti_ΓbF |-E tRel 0 : ti_bF, si_Σ ;;; ti_ΓbF ⊢ ti_bF ⇝ ti_F & si_Σ ;;; ti_ΓbF |-E tRel 0 : ti_F].
Proof.
  have ht : si_Σ ;;; ti_ΓbF |- tRel 0 : ti_bF := type_Rel _ _ 0 (vass si_na ti_bF) ti_wf_ΓbF eq_refl.
  split; [exact (siT ht)|exact ti_red_bF_ΓbF|].
  exact (siT (PCUICSR.type_reduction_closed (Σ := si_Σ) (wfΣ := si_wf) ht ti_red_bF_ΓbF)).
Qed.

(** ** Instances of [T2a_facts]

  Each lemma [<field>_inst] states the premises and the conclusion of the field [<field>] of [T2a_facts] at
  concrete arguments in [si_Σ] (the premise [wfE] holds there by [si_wfE]), builds each typed premise from
  a base derivation lifted with [typing_incl_E], and proves the conclusion from the base lemma of the same
  name. (1) This instance shows that the hypothesis is consistent and about something real. (2) It does
  NOT discharge the hypothesis at [typingE]: the field remains a hypothesis until plan row T2a (validity
  over [typingE]) lands. *)

(* non-degenerate *)
Lemma inversion_mkApps_inst :
  si_Σ ;;; ti_ΓP |-E mkApps (tConstruct si_ind 0 []) [tRel 0] : ti_IA ×
  ∑ A : term, si_Σ ;;; ti_ΓP |-E tConstruct si_ind 0 [] : A × typing_spineE si_Σ ti_ΓP A [tRel 0] ti_IA.
Proof.
  have h : si_Σ ;;; ti_ΓP |- mkApps (tConstruct si_ind 0 []) [tRel 0] : ti_IA := ti_cA_ty.
  split; [exact (siT h)|].
  destruct (PCUICValidity.inversion_mkApps (Σ := si_Σ) (wfΣ := si_wf) h) as [A [h1 h2]].
  exists A. split; [exact (siT h1)|exact (siTS h2)].
Qed.

(** [validity] at the η-typed variable of [PCUICInversionEtaInstances]: [y : k g ⊢ y : k (λ x : Prop. g x)]
    ([iv_rel_typed], a derivation that ends in [typeE_Cumul] with [cumul_eta_l]); its type is a type
    ([iv_keta_typed]). *)
(* non-degenerate *)
Lemma validity_inst :
  si_Σ ;;; iv_Γk |-E tRel 0 : iv_keta × isTypeE si_Σ iv_Γk iv_keta.
Proof. split; [exact iv_rel_typed|exact (has_sort_isTypeE sProp iv_keta_typed)]. Qed.

(** ** Instances of [T6_facts]

  The lemma [typing_spine_smash_inst] states the premises and the conclusion of the field
  [typing_spine_smash] of [T6_facts] at concrete arguments in [si_Σ] (the premise [wfE] holds there by
  [si_wfE]), builds the spine premise from a base spine lifted with [typing_incl_E], and proves the
  conclusion from the base lemma of the same name. (1) This instance shows that the hypothesis is
  consistent and about something real. (2) It does NOT discharge the hypothesis at [typingE]: the field
  remains a hypothesis until plan row T6 (inversion and classification over [typingE]) lands. *)

(* non-degenerate *)
Lemma typing_spine_smash_inst :
  [× wfE si_Σ.1, typing_spineE si_Σ ti_ΓP (it_mkProd_or_LetIn ti_Δlet (tSort sProp)) [tRel 0] (tSort sProp) &
     typing_spineE si_Σ ti_ΓP (it_mkProd_or_LetIn (smash_context [] ti_Δlet) (expand_lets ti_Δlet (tSort sProp)))
       [tRel 0] (tSort sProp)].
Proof.
  split; [exact si_wfE|exact (siTS ti_tspine_let)|].
  exact (siTS (PCUICSafeLemmata.typing_spine_smash (Σ := si_Σ) si_wf ti_ΓP ti_Δlet (tSort sProp) [tRel 0]
                 (tSort sProp) ti_tspine_let)).
Qed.

(** *** Bidirectional derivations over E in [si_Σ], built with the constructors of [BDTypingEta]; the
    comparison premise of [checkE_Cumul] is the join [JoinE Σ Γ Cumul], given here by [JoinE_refl] up to
    conversion. *)

Lemma ti_bdP Γ : si_Σ ;;; Γ |-E si_P ▹ tSort (Sort.super sProp).
Proof. apply inferE_Sort. exact ti_wfs. Qed.

Lemma ti_bdsP Γ : si_Σ ;;; Γ |-E si_P ▹□ Sort.super sProp.
Proof. eapply inferE_sort_Sort; [exact (ti_bdP Γ)|apply rt_refl]. Qed.

Lemma ti_bdInd Γ : si_Σ ;;; Γ |-E tInd si_ind [] ▹ (ind_type si_idecl)@[[]].
Proof. econstructor; [exact si_declared_inductive|exact ti_cons]. Qed.

Lemma ti_bdpInd Γ : si_Σ ;;; Γ |-E tInd si_ind [] ▹Π (si_na, si_P, tSort sProp).
Proof. eapply inferE_prod_Prod; [exact (ti_bdInd Γ)|apply rt_refl]. Qed.

Lemma ti_bdRel : si_Σ ;;; ti_ΓI |-E tRel 0 ▹ lift0 (S 0) (decl_type (vass si_na ti_IF)).
Proof. econstructor. reflexivity. Qed.

Lemma ti_bdiRel : si_Σ ;;; ti_ΓI |-E tRel 0 ▹{si_ind} ([], [ti_F]).
Proof. eapply inferE_ind_Ind; [exact ti_bdRel|apply rt_refl]. Qed.

(** In [ti_ΓP = [A : Prop]]: [A], [I A] and [c A]. *)
Lemma ti_bdA : si_Σ ;;; ti_ΓP |-E tRel 0 ▹ lift0 (S 0) (decl_type (vass si_na si_P)).
Proof. econstructor. reflexivity. Qed.

Lemma ti_bdcA : si_Σ ;;; ti_ΓP |-E tRel 0 ◃ si_P.
Proof. eapply checkE_Cumul; [exact ti_bdA|exact (JoinE_refl si_Σ ti_ΓP Cumul si_P)]. Qed.

Lemma ti_bdIA : si_Σ ;;; ti_ΓP |-E ti_IA ▹ tSort sProp.
Proof.
  change (si_Σ ;;; ti_ΓP |-E tApp (tInd si_ind []) (tRel 0) ▹ ((tSort sProp) {0 := tRel 0})).
  eapply inferE_App; [exact (ti_bdpInd ti_ΓP)|exact ti_bdcA].
Qed.

Lemma ti_bdsIA : si_Σ ;;; ti_ΓP |-E ti_IA ▹□ sProp.
Proof. eapply inferE_sort_Sort; [exact ti_bdIA|apply rt_refl]. Qed.

Lemma ti_bdcIA : si_Σ ;;; ti_ΓP |-E ti_IA ◃ si_P.
Proof. eapply checkE_Cumul; [exact ti_bdIA|exact (JoinE_refl si_Σ ti_ΓP Cumul si_P)]. Qed.

Lemma ti_bdC Γ : si_Σ ;;; Γ |-E tConstruct si_ind 0 [] ▹ ti_cty.
Proof.
  have h : si_Σ ;;; Γ |-E tConstruct si_ind 0 [] ▹ type_of_constructor si_mdecl si_cdecl (si_ind, 0) [].
  { econstructor; [exact si_declared_constructor|exact ti_cons]. }
  exact h.
Qed.

Lemma ti_bdpC Γ : si_Σ ;;; Γ |-E tConstruct si_ind 0 [] ▹Π (si_na, si_P, ti_IA).
Proof. eapply inferE_prod_Prod; [exact (ti_bdC Γ)|apply rt_refl]. Qed.

Lemma ti_bdcAi : si_Σ ;;; ti_ΓP |-E ti_cA ▹ ti_IA.
Proof.
  change (si_Σ ;;; ti_ΓP |-E tApp (tConstruct si_ind 0 []) (tRel 0) ▹ (ti_IA {0 := tRel 0})).
  eapply inferE_App; [exact (ti_bdpC ti_ΓP)|exact ti_bdcA].
Qed.

Lemma ti_bdccA : si_Σ ;;; ti_ΓP |-E ti_cA ◃ ti_IA.
Proof. eapply checkE_Cumul; [exact ti_bdcAi|exact (JoinE_refl si_Σ ti_ΓP Cumul ti_IA)]. Qed.

(** In [ti_ΓP]: the derivations the T6BD and T6BDc instances share. *)
Lemma ti_ci2C : PCUICTyping.ctx_inst (checkingE si_Σ) ti_ΓP [ti_IA; ti_cA] ti_Δ2.
Proof.
  econstructor; [exact ti_bdcIA|].
  change (PCUICTyping.ctx_inst (checkingE si_Σ) ti_ΓP [ti_cA] [vass si_na ti_IA]).
  econstructor; [exact ti_bdccA|]. cbn. constructor.
Qed.

Lemma ti_ltJ : lift_typing typing si_Σ ti_ΓP (Judge (Some ti_cA) ti_IA None (Some Relevant)).
Proof. split; [exact ti_cA_ty|]. exists sProp. split; [exact ti_IA_ty|split; [exact I|reflexivity]]. Qed.

Lemma ti_lsJ :
  lift_sorting (checkingE si_Σ ti_ΓP) (infering_sortE si_Σ ti_ΓP) (Judge (Some ti_cA) ti_IA None (Some Relevant)).
Proof. split; [exact ti_bdccA|]. exists sProp. split; [exact ti_bdsIA|split; [exact I|reflexivity]]. Qed.

Lemma ti_relIA : wf_local_relE si_Σ ti_ΓP ti_ΓIA.
Proof. constructor; [constructor|]. exact (siL (ti_vass ti_ΓP si_na ti_IA sProp ti_IA_ty eq_refl)). Qed.

Lemma ti_bdrelIA : wf_local_bd_relE si_Σ ti_ΓP ti_ΓIA.
Proof.
  constructor; [constructor|]. split; [exact tt|].
  exists sProp. split; [exact ti_bdsIA|split; [exact I|reflexivity]].
Qed.

(** The η-typed variable of [PCUICInversionEtaInstances]: in [iv_Γk = [y : k g; k : (Prop → Prop) → Prop;
    g : Prop → Prop]], [y] infers [k g] and checks against [k (λ x : Prop. g x)] through the η join
    [iv_join_eta] (one [cumul_eta_l] step). *)
Lemma ti_bdy : si_Σ ;;; iv_Γk |-E tRel 0 ▹ iv_kg.
Proof.
  have h : si_Σ ;;; iv_Γk |-E tRel 0 ▹ lift0 (S 0) (decl_type (vass si_na (tApp (tRel 0) (tRel 1)))).
  { econstructor. reflexivity. }
  exact h.
Qed.

Lemma ti_bdcy : si_Σ ;;; iv_Γk |-E tRel 0 ◃ iv_keta.
Proof. eapply checkE_Cumul; [exact ti_bdy|exact iv_join_eta]. Qed.

(** In [ti_ΓX]: [x] infers [I ((λ X. X) A)], an applied [I] as it is and, after β, [I A]. *)
Lemma ti_bdX : si_Σ ;;; ti_ΓX |-E tRel 0 ▹ tApp (tInd si_ind []) (tApp ti_idP (tRel 1)).
Proof.
  have h : si_Σ ;;; ti_ΓX |-E tRel 0 ▹ lift0 (S 0) (decl_type (vass si_na (tApp (tInd si_ind []) ti_idA))).
  { econstructor. reflexivity. }
  exact h.
Qed.

Lemma ti_bdiX1 : si_Σ ;;; ti_ΓX |-E tRel 0 ▹{si_ind} ([], [tApp ti_idP (tRel 1)]).
Proof. eapply inferE_ind_Ind; [exact ti_bdX|apply rt_refl]. Qed.

Lemma ti_bdiX2 : si_Σ ;;; ti_ΓX |-E tRel 0 ▹{si_ind} ([], [tRel 1]).
Proof. eapply inferE_ind_Ind; [exact ti_bdX|exact (clrel_rel ti_red_IidA1)]. Qed.

(** In [ti_Γf]: [f] infers [ti_Tf], a product as it is ([ti_bdpf1]) and after two β-steps ([ti_bdpf2]). *)
Lemma ti_bdf : si_Σ ;;; ti_Γf |-E tRel 0 ▹ ti_Tf.
Proof.
  have h : si_Σ ;;; ti_Γf |-E tRel 0 ▹ lift0 (S 0) (decl_type (vass si_na ti_pidA)).
  { econstructor. reflexivity. }
  exact h.
Qed.

Lemma ti_bdpf1 : si_Σ ;;; ti_Γf |-E tRel 0 ▹Π (si_na, tApp ti_idP (tRel 1), tApp ti_idP (tRel 2)).
Proof. eapply inferE_prod_Prod; [exact ti_bdf|apply rt_refl]. Qed.

Lemma ti_bdpf2 : si_Σ ;;; ti_Γf |-E tRel 0 ▹Π (si_na, tRel 1, tRel 2).
Proof. eapply inferE_prod_Prod; [exact ti_bdf|exact (clrel_rel ti_red_Tf)]. Qed.

(** In [ti_Γfa]: [f a] infers [(λ X. X) A] through [ti_bdpfa1] and [A] through [ti_bdpfa2]. *)
Lemma ti_bdfa : si_Σ ;;; ti_Γfa |-E tRel 1 ▹ tProd si_na (tApp ti_idP (tRel 2)) (tApp ti_idP (tRel 3)).
Proof.
  have h : si_Σ ;;; ti_Γfa |-E tRel 1 ▹ lift0 (S 1) (decl_type (vass si_na ti_pidA)).
  { econstructor. reflexivity. }
  exact h.
Qed.

Lemma ti_bdpfa1 : si_Σ ;;; ti_Γfa |-E tRel 1 ▹Π (si_na, tApp ti_idP (tRel 2), tApp ti_idP (tRel 3)).
Proof. eapply inferE_prod_Prod; [exact ti_bdfa|apply rt_refl]. Qed.

Lemma ti_bdpfa2 : si_Σ ;;; ti_Γfa |-E tRel 1 ▹Π (si_na, tRel 2, tRel 3).
Proof. eapply inferE_prod_Prod; [exact ti_bdfa|exact (clrel_rel ti_red_Tfa)]. Qed.

Lemma ti_bda : si_Σ ;;; ti_Γfa |-E tRel 0 ▹ tRel 2.
Proof.
  have h : si_Σ ;;; ti_Γfa |-E tRel 0 ▹ lift0 (S 0) (decl_type (vass si_na (tRel 1))).
  { econstructor. reflexivity. }
  exact h.
Qed.

Lemma ti_bdfa1 : si_Σ ;;; ti_Γfa |-E tApp (tRel 1) (tRel 0) ▹ tApp ti_idP (tRel 2).
Proof.
  change (si_Σ ;;; ti_Γfa |-E tApp (tRel 1) (tRel 0) ▹ ((tApp ti_idP (tRel 3)) {0 := tRel 0})).
  eapply inferE_App; [exact ti_bdpfa1|].
  eapply checkE_Cumul; [exact ti_bda|].
  exact (JoinE_red_r si_Σ ti_Γfa Cumul (tRel 2) (tApp ti_idP (tRel 2)) (clrel_rel ti_red_A2fa)).
Qed.

Lemma ti_bdfa2 : si_Σ ;;; ti_Γfa |-E tApp (tRel 1) (tRel 0) ▹ tRel 2.
Proof.
  change (si_Σ ;;; ti_Γfa |-E tApp (tRel 1) (tRel 0) ▹ ((tRel 3) {0 := tRel 0})).
  eapply inferE_App; [exact ti_bdpfa2|].
  eapply checkE_Cumul; [exact ti_bda|exact (JoinE_refl si_Σ ti_Γfa Cumul (tRel 2))].
Qed.

(** In [ti_ΓP]: [let x : Prop := A in x] infers [let x : Prop := A in Prop], which reduces (ζ) to [Prop]. *)
Definition ti_tL : term := tLetIn si_na (tRel 0) si_P (tRel 0).

Lemma ti_bdL : si_Σ ;;; ti_ΓP |-E ti_tL ▹ tLetIn si_na (tRel 0) si_P si_P.
Proof.
  have hb : si_Σ ;;; ti_ΓP ,, vdef si_na (tRel 0) si_P |-E tRel 0 ▹ lift0 (S 0) (decl_type (vdef si_na (tRel 0) si_P)).
  { econstructor. reflexivity. }
  have hj : lift_sorting (checkingE si_Σ ti_ΓP) (infering_sortE si_Σ ti_ΓP) (j_vdef si_na (tRel 0) si_P).
  { split; [exact ti_bdcA|]. exists (Sort.super sProp).
    split; [exact (ti_bdsP ti_ΓP)|split; [exact I|reflexivity]]. }
  eapply inferE_LetIn; [exact hj|exact hb].
Qed.

Lemma ti_bdsL : si_Σ ;;; ti_ΓP |-E ti_tL ▹□ sProp.
Proof. eapply inferE_sort_Sort; [exact ti_bdL|exact (clrel_rel ti_red_TL)]. Qed.

(** In [ti_ΓP]: [λ X : Prop. X] infers [Π X : Prop. Prop], and [(λ X : Prop. X) A] checks against [Prop]. *)
Lemma ti_bdidP : si_Σ ;;; ti_ΓP |-E ti_idP ▹ tProd si_na si_P si_P.
Proof.
  have hb : si_Σ ;;; ti_ΓP ,, vass si_na si_P |-E tRel 0 ▹ si_P.
  { have h : si_Σ ;;; ti_ΓP ,, vass si_na si_P |-E tRel 0 ▹ lift0 (S 0) (decl_type (vass si_na si_P)).
    { econstructor. reflexivity. }
    exact h. }
  eapply inferE_Lambda; [|exact hb].
  split; [exact tt|]. exists (Sort.super sProp). split; [exact (ti_bdsP ti_ΓP)|split; [exact I|reflexivity]].
Qed.

Lemma ti_bdidA : si_Σ ;;; ti_ΓP |-E ti_idA ▹ si_P.
Proof.
  change (si_Σ ;;; ti_ΓP |-E tApp ti_idP (tRel 0) ▹ (si_P {0 := tRel 0})).
  eapply inferE_App; [|exact ti_bdcA].
  eapply inferE_prod_Prod; [exact ti_bdidP|apply rt_refl].
Qed.

Lemma ti_bdcidA : si_Σ ;;; ti_ΓP |-E ti_idA ◃ si_P.
Proof. eapply checkE_Cumul; [exact ti_bdidA|exact (JoinE_refl si_Σ ti_ΓP Cumul si_P)]. Qed.

(** [let x : Prop := (λ X : Prop. X) A in x] infers [let x : Prop := (λ X : Prop. X) A in Prop], which reaches
    [Prop] by ζ at once ([ti_red_TL2a]) or by β in the let value and then ζ ([ti_red_TL2b]). *)
Definition ti_tL2 : term := tLetIn si_na ti_idA si_P (tRel 0).
Definition ti_TL2 : term := tLetIn si_na ti_idA si_P si_P.

Lemma ti_bdL2 : si_Σ ;;; ti_ΓP |-E ti_tL2 ▹ ti_TL2.
Proof.
  have hb : si_Σ ;;; ti_ΓP ,, vdef si_na ti_idA si_P |-E tRel 0 ▹ lift0 (S 0) (decl_type (vdef si_na ti_idA si_P)).
  { econstructor. reflexivity. }
  have hj : lift_sorting (checkingE si_Σ ti_ΓP) (infering_sortE si_Σ ti_ΓP) (j_vdef si_na ti_idA si_P).
  { split; [exact ti_bdcidA|]. exists (Sort.super sProp).
    split; [exact (ti_bdsP ti_ΓP)|split; [exact I|reflexivity]]. }
  eapply inferE_LetIn; [exact hj|exact hb].
Qed.

Lemma ti_red_TL2a : PCUICReduction.red si_Σ ti_ΓP ti_TL2 (tSort sProp).
Proof. apply rt_step. exact (red_zeta si_Σ ti_ΓP si_na ti_idA si_P si_P). Qed.

Lemma ti_red_TL2b : PCUICReduction.red si_Σ ti_ΓP ti_TL2 (tSort sProp).
Proof.
  eapply rt_trans.
  - apply rt_step. apply letin_red_def. exact (red_beta si_Σ ti_ΓP si_na si_P (tRel 0) (tRel 0)).
  - apply rt_step. exact (red_zeta si_Σ ti_ΓP si_na (tRel 0) si_P si_P).
Qed.

Lemma ti_bdsL2a : si_Σ ;;; ti_ΓP |-E ti_tL2 ▹□ sProp.
Proof. eapply inferE_sort_Sort; [exact ti_bdL2|exact ti_red_TL2a]. Qed.

Lemma ti_bdsL2b : si_Σ ;;; ti_ΓP |-E ti_tL2 ▹□ sProp.
Proof. eapply inferE_sort_Sort; [exact ti_bdL2|exact ti_red_TL2b]. Qed.

(** ** Instances of [T6BD_facts]

  Each lemma [<field>_inst] states the premises and the conclusion of the field [<field>] of [T6BD_facts]
  at concrete arguments in [si_Σ] (the premise [wfE] holds there by [si_wfE]); the bidirectional premises
  are built with the constructors of [BDTypingEta], and the conclusion from base derivations lifted
  with [typing_incl_E]. (1) This instance shows that the hypothesis is consistent and about something
  real. (2) It does NOT discharge the hypothesis at [typingE]: the field remains a hypothesis until plan
  row T6 (bidirectional soundness over E) lands. *)

(** [checking_typing] at the η-typed variable [y : k g] of [PCUICInversionEtaInstances]: [y] checks against
    [k (λ x : Prop. g x)] through the η join, and the conclusion is [iv_rel_typed], whose derivation ends in
    [typeE_Cumul] with [cumul_eta_l]. *)
(* non-degenerate *)
Lemma checking_typing_inst :
  [× wfE si_Σ, wf_localE si_Σ iv_Γk, isTypeE si_Σ iv_Γk iv_keta, si_Σ ;;; iv_Γk |-E tRel 0 ◃ iv_keta &
     si_Σ ;;; iv_Γk |-E tRel 0 : iv_keta].
Proof.
  split; [exact si_wfE|exact iv_wf_Γk|exact (has_sort_isTypeE sProp iv_keta_typed)|exact ti_bdcy|exact iv_rel_typed].
Qed.

(* non-degenerate *)
Lemma ctx_inst_bd_typing_inst :
  [× wfE si_Σ, wf_localE si_Σ (ti_ΓP ,,, List.rev ti_Δ2),
     PCUICTyping.ctx_inst (checkingE si_Σ) ti_ΓP [ti_IA; ti_cA] (List.rev (List.rev ti_Δ2)) &
     ctx_instE si_Σ ti_ΓP [ti_IA; ti_cA] (List.rev (List.rev ti_Δ2))].
Proof.
  have h1 := ti_wf_P ti_ΓP ti_wf_ΓP.
  have hw : wf_local si_Σ (ti_ΓP ,,, List.rev ti_Δ2) :=
    ti_wf_cons _ si_na (tRel 0) sProp h1 (type_Rel _ _ 0 (vass si_na si_P) h1 eq_refl) eq_refl.
  split; [exact si_wfE|exact (siW hw)|exact ti_ci2C|exact (siCI ti_ci2B)].
Qed.

(* non-degenerate *)
Lemma infering_ind_typing_inst :
  [× wfE si_Σ, wf_localE si_Σ ti_ΓI, si_Σ ;;; ti_ΓI |-E tRel 0 ▹{si_ind} ([], [ti_F]) &
     si_Σ ;;; ti_ΓI |-E tRel 0 : mkApps (tInd si_ind []) [ti_F]].
Proof.
  split; [exact si_wfE|exact (siW ti_wf_ΓI)|exact ti_bdiRel|].
  exact (siT (type_Rel _ _ 0 (vass si_na ti_IF) ti_wf_ΓI eq_refl)).
Qed.

(* non-degenerate *)
Lemma infering_prod_typing_inst :
  [× wfE si_Σ, wf_localE si_Σ ti_ΓP, si_Σ ;;; ti_ΓP |-E tConstruct si_ind 0 [] ▹Π (si_na, si_P, ti_IA) &
     si_Σ ;;; ti_ΓP |-E tConstruct si_ind 0 [] : tProd si_na si_P ti_IA].
Proof.
  split; [exact si_wfE|exact (siW ti_wf_ΓP)|exact (ti_bdpC ti_ΓP)|exact (siT (ti_Construct_ty ti_ΓP ti_wf_ΓP))].
Qed.

(* non-degenerate *)
Lemma infering_sort_isTypeRel_inst :
  [× wfE si_Σ, wf_localE si_Σ ti_ΓP, si_Σ ;;; ti_ΓP |-E ti_IA ▹□ sProp &
     isTypeRelE si_Σ ti_ΓP ti_IA (relevance_of_sort (sProp : sort))].
Proof.
  split; [exact si_wfE|exact (siW ti_wf_ΓP)|exact ti_bdsIA|].
  exact (siIR (has_sort_isTypeRel sProp _ eq_refl ti_IA_ty)).
Qed.

(* non-degenerate *)
Lemma infering_sort_typing_inst :
  [× wfE si_Σ, wf_localE si_Σ ti_ΓP, si_Σ ;;; ti_ΓP |-E ti_IA ▹□ sProp & si_Σ ;;; ti_ΓP |-E ti_IA : tSort sProp].
Proof. split; [exact si_wfE|exact (siW ti_wf_ΓP)|exact ti_bdsIA|exact (siT ti_IA_ty)]. Qed.

(* non-degenerate *)
Lemma infering_typing_inst :
  [× wfE si_Σ, wf_localE si_Σ ti_ΓP, si_Σ ;;; ti_ΓP |-E ti_cA ▹ ti_IA & si_Σ ;;; ti_ΓP |-E ti_cA : ti_IA].
Proof. split; [exact si_wfE|exact (siW ti_wf_ΓP)|exact ti_bdcAi|exact (siT ti_cA_ty)]. Qed.

(* non-degenerate *)
Lemma lift_sorting_lift_typing_inst :
  [× wfE si_Σ, wf_localE si_Σ ti_ΓP,
     lift_sorting (checkingE si_Σ ti_ΓP) (infering_sortE si_Σ ti_ΓP) (Judge (Some ti_cA) ti_IA None (Some Relevant)) &
     lift_typing typingE si_Σ ti_ΓP (Judge (Some ti_cA) ti_IA None (Some Relevant))].
Proof. split; [exact si_wfE|exact (siW ti_wf_ΓP)|exact ti_lsJ|exact (siL ti_ltJ)]. Qed.

(* non-degenerate *)
Lemma wf_local_bd_rel_typing_inst :
  [× wfE si_Σ, wf_localE si_Σ ti_ΓP, wf_local_bd_relE si_Σ ti_ΓP ti_ΓIA & wf_local_relE si_Σ ti_ΓP ti_ΓIA].
Proof. split; [exact si_wfE|exact (siW ti_wf_ΓP)|exact ti_bdrelIA|exact ti_relIA]. Qed.

(** ** Instances of [T6BDu_facts]

  Each lemma [<field>_inst] states the premises and the conclusion of the field [<field>] of [T6BDu_facts]
  at concrete arguments in [si_Σ] (the premise [wfE] holds there by [si_wfE]); the bidirectional premises
  are built with the constructors of [BDTypingEta], and the conclusion (reductions to a common
  reduct, which are base [closed_red]) directly. (1) This instance shows that the hypothesis is consistent
  and about something real. (2) It does NOT discharge the hypothesis at [typingE]: the field remains a
  hypothesis until plan row T6 (bidirectional uniqueness over E) lands. *)

(** [infering_checking] at the η-typed variable [y : k g]: [y] infers [k g] and checks against
    [k (λ x : Prop. g x)]; the conclusion is the η comparison [into_ws_cumulE_inst]. *)
(* non-degenerate *)
Lemma infering_checking_inst :
  [× wfE si_Σ, wf_localE si_Σ iv_Γk, on_free_vars (shiftnP #|iv_Γk| xpred0) iv_keta,
     si_Σ ;;; iv_Γk |-E tRel 0 ▹ iv_kg, si_Σ ;;; iv_Γk |-E tRel 0 ◃ iv_keta &
     si_Σ ;;; iv_Γk ⊢E iv_kg ≤ iv_keta].
Proof. split; [exact si_wfE|exact iv_wf_Γk|reflexivity|exact ti_bdy|exact ti_bdcy|exact into_ws_cumulE_inst]. Qed.

(* non-degenerate *)
Lemma infering_ind_ind_inst :
  [× wfE si_Σ, wf_localE si_Σ ti_ΓX, si_Σ ;;; ti_ΓX |-E tRel 0 ▹{si_ind} ([], [tApp ti_idP (tRel 1)]),
     si_Σ ;;; ti_ΓX |-E tRel 0 ▹{si_ind} ([], [tRel 1]) &
     ∑ args'' : list term, [× si_ind = si_ind, ([] : Instance.t) = [],
                              red_terms si_Σ ti_ΓX [tApp ti_idP (tRel 1)] args'' & red_terms si_Σ ti_ΓX [tRel 1] args'']].
Proof.
  split; [exact si_wfE|exact (siW ti_wf_ΓX)|exact ti_bdiX1|exact ti_bdiX2|].
  exists [tRel 1].
  split; [reflexivity|reflexivity|exact (All2_cons ti_red_idA1 All2_nil)
         |exact (All2_cons (ti_cr_refl ti_ΓX (tRel 1) eq_refl eq_refl) All2_nil)].
Qed.

(* non-degenerate *)
Lemma infering_ind_infering_inst :
  [× wfE si_Σ, wf_localE si_Σ ti_ΓX, si_Σ ;;; ti_ΓX |-E tRel 0 ▹{si_ind} ([], [tApp ti_idP (tRel 1)]),
     si_Σ ;;; ti_ΓX |-E tRel 0 ▹ tApp (tInd si_ind []) (tApp ti_idP (tRel 1)) &
     ∑ args' : list term,
       si_Σ ;;; ti_ΓX ⊢ tApp (tInd si_ind []) (tApp ti_idP (tRel 1)) ⇝ mkApps (tInd si_ind []) args' ×
       red_terms si_Σ ti_ΓX [tApp ti_idP (tRel 1)] args'].
Proof.
  split; [exact si_wfE|exact (siW ti_wf_ΓX)|exact ti_bdiX1|exact ti_bdX|].
  exists [tRel 1]. split; [exact ti_red_IidA1|exact (All2_cons ti_red_idA1 All2_nil)].
Qed.

(* non-degenerate *)
Lemma infering_prod_infering_inst :
  [× wfE si_Σ, wf_localE si_Σ ti_Γf,
     si_Σ ;;; ti_Γf |-E tRel 0 ▹Π (si_na, tApp ti_idP (tRel 1), tApp ti_idP (tRel 2)),
     si_Σ ;;; ti_Γf |-E tRel 0 ▹ ti_Tf &
     ∑ A' B' : term, [× si_Σ ;;; ti_Γf ⊢ ti_Tf ⇝ tProd si_na A' B', si_Σ ;;; ti_Γf ⊢ tApp ti_idP (tRel 1) ⇝ A' &
                        si_Σ ;;; ti_Γf ,, vass si_na (tApp ti_idP (tRel 1)) ⊢ tApp ti_idP (tRel 2) ⇝ B']].
Proof.
  split; [exact si_wfE|exact (siW ti_wf_Γf)|exact ti_bdpf1|exact ti_bdf|].
  exists (tRel 1), (tRel 2). split; [exact ti_red_Tf|exact ti_red_A1f|exact ti_red_B1f].
Qed.

(* non-degenerate *)
Lemma infering_prod_prod_inst :
  [× wfE si_Σ, wf_localE si_Σ ti_Γf,
     si_Σ ;;; ti_Γf |-E tRel 0 ▹Π (si_na, tApp ti_idP (tRel 1), tApp ti_idP (tRel 2)),
     si_Σ ;;; ti_Γf |-E tRel 0 ▹Π (si_na, tRel 1, tRel 2) &
     ∑ A'' B'' : term, [× si_na = si_na, si_Σ ;;; ti_Γf ⊢ tApp ti_idP (tRel 1) ⇝ A'', si_Σ ;;; ti_Γf ⊢ tRel 1 ⇝ A'',
                          si_Σ ;;; ti_Γf ,, vass si_na (tApp ti_idP (tRel 1)) ⊢ tApp ti_idP (tRel 2) ⇝ B'' &
                          si_Σ ;;; ti_Γf ,, vass si_na (tRel 1) ⊢ tRel 2 ⇝ B'']].
Proof.
  split; [exact si_wfE|exact (siW ti_wf_Γf)|exact ti_bdpf1|exact ti_bdpf2|].
  exists (tRel 1), (tRel 2).
  split; [reflexivity|exact ti_red_A1f|exact (ti_cr_refl ti_Γf (tRel 1) eq_refl eq_refl)|exact ti_red_B1f
         |exact (ti_cr_refl (ti_Γf ,, vass si_na (tRel 1)) (tRel 2) eq_refl eq_refl)].
Qed.

(* non-degenerate *)
Lemma infering_sort_infering_inst :
  [× wfE si_Σ, wf_localE si_Σ ti_ΓP, si_Σ ;;; ti_ΓP |-E ti_tL ▹□ sProp,
     si_Σ ;;; ti_ΓP |-E ti_tL ▹ tLetIn si_na (tRel 0) si_P si_P &
     si_Σ ;;; ti_ΓP ⊢ tLetIn si_na (tRel 0) si_P si_P ⇝ tSort sProp].
Proof. split; [exact si_wfE|exact (siW ti_wf_ΓP)|exact ti_bdsL|exact ti_bdL|exact ti_red_TL]. Qed.

(** Two [▹□] derivations of one term: the same inference, then two different reductions of its type to
    [Prop] (ζ at once; β in the let value, then ζ). *)
(* non-degenerate *)
Lemma infering_sort_sort_inst :
  [× wfE si_Σ, wf_localE si_Σ ti_ΓP, si_Σ ;;; ti_ΓP |-E ti_tL2 ▹□ sProp, si_Σ ;;; ti_ΓP |-E ti_tL2 ▹□ sProp &
     (sProp : sort) = sProp].
Proof. split; [exact si_wfE|exact (siW ti_wf_ΓP)|exact ti_bdsL2a|exact ti_bdsL2b|reflexivity]. Qed.

(* non-degenerate *)
Lemma infering_unique_inst :
  [× wfE si_Σ, wf_localE si_Σ ti_Γfa, si_Σ ;;; ti_Γfa |-E tApp (tRel 1) (tRel 0) ▹ tApp ti_idP (tRel 2),
     si_Σ ;;; ti_Γfa |-E tApp (tRel 1) (tRel 0) ▹ tRel 2 &
     ∑ T'' : term, si_Σ ;;; ti_Γfa ⊢ tApp ti_idP (tRel 2) ⇝ T'' × si_Σ ;;; ti_Γfa ⊢ tRel 2 ⇝ T''].
Proof.
  split; [exact si_wfE|exact (siW ti_wf_Γfa)|exact ti_bdfa1|exact ti_bdfa2|].
  exists (tRel 2). split; [exact ti_red_A2fa|exact (ti_cr_refl ti_Γfa (tRel 2) eq_refl eq_refl)].
Qed.

(** The two witnesses type [I A] at two different sorts: [Prop], and [Type] by cumulativity. *)
(* non-degenerate *)
Lemma isTypeRel_unique_inst :
  [× wfE si_Σ, isTypeRelE si_Σ ti_ΓP ti_IA Relevant, isTypeRelE si_Σ ti_ΓP ti_IA Relevant & Relevant = Relevant].
Proof.
  split; [exact si_wfE| | |reflexivity].
  - exact (siIR (has_sort_isTypeRel sProp Relevant eq_refl ti_IA_ty)).
  - exact (siIR (has_sort_isTypeRel (Sort.super sProp) Relevant eq_refl ti_IA_ty1)).
Qed.

(** ** Instances of [T6BDc_facts]

  Each lemma [<field>_inst] states the premises and the conclusion of the field [<field>] of [T6BDc_facts]
  at concrete arguments in [si_Σ] (the premise [wfE] holds there by [si_wfE]), in the non-empty context
  [ti_ΓP = [A : Prop]] and on the terms [I A] and [c A]: applications whose head has a Π type, so that each
  inferred type goes through an [infering_prodE] step (the type of the head reduces to a [tProd]). The
  typing premises are base derivations lifted with [typing_incl_E], and the bidirectional conclusions are
  built with the constructors of [BDTypingEta]. (1) This instance shows that the hypothesis is
  consistent and about something real. (2) It does NOT discharge the hypothesis at [typingE]: the field
  remains a hypothesis until plan row T6 (bidirectional completeness over E) lands, and its E proof also
  needs T8 (a well-typed type E-convertible to a Π, a sort or an inductive reduces to one). *)

(* non-degenerate *)
Lemma ctx_inst_typing_bd_inst :
  [× wfE si_Σ, ctx_instE si_Σ ti_ΓP [ti_IA; ti_cA] ti_Δ2 &
     PCUICTyping.ctx_inst (checkingE si_Σ) ti_ΓP [ti_IA; ti_cA] ti_Δ2].
Proof. split; [exact si_wfE|exact (siCI ti_ci2B)|exact ti_ci2C]. Qed.

(* non-degenerate *)
Lemma lift_typing_lift_sorting_inst :
  [× wfE si_Σ, lift_typing typingE si_Σ ti_ΓP (Judge (Some ti_cA) ti_IA None (Some Relevant)) &
     lift_sorting (checkingE si_Σ ti_ΓP) (infering_sortE si_Σ ti_ΓP) (Judge (Some ti_cA) ti_IA None (Some Relevant))].
Proof. split; [exact si_wfE|exact (siL ti_ltJ)|exact ti_lsJ]. Qed.

(* non-degenerate *)
Lemma typing_checking_inst :
  si_Σ ;;; ti_ΓP |-E ti_cA : ti_IA × si_Σ ;;; ti_ΓP |-E ti_cA ◃ ti_IA.
Proof. split; [exact (siT ti_cA_ty)|exact ti_bdccA]. Qed.

(* non-degenerate *)
Lemma typing_infering_inst :
  si_Σ ;;; ti_ΓP |-E ti_cA : ti_IA ×
  ∑ T' : term, si_Σ ;;; ti_ΓP |-E ti_cA ▹ T' × si_Σ ;;; ti_ΓP ⊢E T' ≤ ti_IA.
Proof.
  split; [exact (siT ti_cA_ty)|].
  exists ti_IA. split; [exact ti_bdcAi|exact (fi_ws Cumul ti_ΓP ti_IA eq_refl eq_refl)].
Qed.

(* non-degenerate *)
Lemma typing_infering_sort_inst :
  si_Σ ;;; ti_ΓP |-E ti_IA : tSort sProp × ∑ u' : sort, si_Σ ;;; ti_ΓP |-E ti_IA ▹□ u' × leq_sort si_Σ u' sProp.
Proof.
  split; [exact (siT ti_IA_ty)|].
  exists sProp. split; [exact ti_bdsIA|first [reflexivity|exact I|cbn; trivial]].
Qed.

(* non-degenerate *)
Lemma wf_local_rel_wf_local_bd_inst :
  [× wfE si_Σ, wf_local_relE si_Σ ti_ΓP ti_ΓIA & wf_local_bd_relE si_Σ ti_ΓP ti_ΓIA].
Proof. split; [exact si_wfE|exact ti_relIA|exact ti_bdrelIA]. Qed.

(** ** Base names of the [PCUICTyping] helpers, over E

  [PCUICTyping.v:442-470] ([has_sort_isType], [has_sort_isTypeRel], [isType_welltyped], [isTypeRel_welltyped])
  and base's constructor [iswelltyped], here over E, so the copies' proof scripts read as base's (definitional;
  [PCUICTypingEtaDefs] has the E-named forms). At the END of the file, so the section "Instances" above, which
  works with base derivations, still sees the base names. *)
Section BaseNames.
  Context {cf : checker_flags}.

  Definition has_sort_isType {Σ : global_env_ext} {Γ : context} {T : term} (s : sort) :
    Σ ;;; Γ |-E T : tSort s -> isTypeE Σ Γ T := has_sort_isTypeE s.
  Definition has_sort_isTypeRel {Σ : global_env_ext} {Γ : context} {T : term} (s : sort) (r : relevance) :
    isSortRel s r -> Σ ;;; Γ |-E T : tSort s -> isTypeRelE Σ Γ T r := has_sort_isTypeRelE s r.
  Definition isType_welltyped {Σ : global_env_ext} {Γ : context} {T : term} :
    isTypeE Σ Γ T -> welltypedE Σ Γ T := isTypeE_welltypedE.
  Definition isTypeRel_welltyped {Σ : global_env_ext} {Γ : context} {T : term} {r : relevance} :
    isTypeRelE Σ Γ T r -> welltypedE Σ Γ T := isTypeRelE_welltypedE.
  Definition iswelltyped {Σ : global_env_ext} {Γ : context} {t A : term} :
    Σ ;;; Γ |-E t : A -> welltypedE Σ Γ t := iswelltypedE Σ Γ t A.
End BaseNames.

(** The [fvs] hints base registers for its scoping lemmas ([wf_local_closed_context], [type_is_open_term],
    [subject_is_open_term], [isType_is_open_term]), over E (the Derived lemmas above). *)
#[global] Hint Resolve wf_local_closed_context type_is_open_term subject_is_open_term isType_is_open_term : fvs.

