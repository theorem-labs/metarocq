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
From MetaRocq.PCUIC Require PCUICInductives PCUICSubstitution.
From Stdlib Require Import Program.Equality.
From MetaRocq.SafeChecker Require Import PCUICTypingEtaDefs.

(** * ETAK (EtaK7): the η typing facts the η checker needs, as NAMED hypotheses

  BET-64 EtaCheckerLane, worker EtaK7, 2026-10-29; base [frac/eta] @ [0cb773a4]. Plan rows K7/K8 (the η
  copies of [PCUICTypeChecker], [PCUICSafeChecker], [PCUICSafeRetyping], [PCUICRetypingEnvIrrelevance],
  [SafeTemplateChecker]) need the E version of each base typing-metatheory lemma they use. The exact list
  is the inventory [lanes/eta/etak/EtaK7-inventory.md] (from the base build's [.glob] files).

  Each fact is the base lemma with [typing] → [typingE], [wf]/[wf_ext] → [wfE]/[wf_extE],
  [wf_local] → [wf_localE], [isType] → [isTypeE], [welltyped] → [welltypedE], the bidirectional judgments →
  their E copies ([PCUICTypingEtaDefs]), and the well-scoped cumulativity → [ws_cumul_pbE]. It keeps the
  base lemma's NAME, so the copies' proof scripts read as base's; this file is imported LAST.

  - Facts no row has proved yet are fields of one class per plan row ([T0_facts], [T1_facts], [T2a_facts],
    [T6_facts], [T6BD_facts], [T6BDu_facts], [T6BDc_facts], [A_facts], and [U_facts] for untyped plumbing).
    The copies take them through ONE implicit Prop premise [{EtaF : EtaFacts}] (the squashes of the nine
    classes, end of this file), so extraction erases them. When a row lands, its class gets an instance and
    its field of [EtaFacts] is proved.
  - Facts that follow from what base already proves over E ([PCUICClosedTypEta], [PCUICTypingEtaInd],
    [PCUICEtaA6], [PCUICWsCumulEtaSubst], [PCUICWellScopedCumulativityEta], [PCUICEtaI5]) or from the class
    fields are PROVED below the classes, under the base name ("Derived", "Derived, second part").
  - Bundle size: 92 named hypotheses (class fields). Audits hyp-audit-A.md and hyp-audit-B.md
    (lanes/eta/etak/) turned 9 former fields into PROVED lemmas, which are NO LONGER hypotheses (bundle
    101 -> 92): [type_Cumul_alt] (T1), [isType_Sort_inv] (T2a), [inversion_Const], [inversion_LetIn],
    [inversion_Prod], [inversion_Rel], [inversion_Sort] (T6), [type_ws_cumul_pb] and
    [mfix_body_on_red_unique] (T0; these two are STATEMENT CHANGEs, marked where they occur).
  - Instances. EVERY one of the 92 fields has a concrete satisfying instance, in the final section
    "Instances" of this file (one lemma [<field>_inst] per field, proved without any class field; written
    by EtaK7Inst). Per class, fields = instances: T0_facts 49, U_facts 9, T1_facts 5, T2a_facts 2,
    T6_facts 1, T6BD_facts 10, T6BDu_facts 9, T6BDc_facts 6, A_facts 1. Each instance carries a tag
    [(* non-degenerate *)] or [(* degenerate: <why> *)]; 16 are non-degenerate, among them all six of
    T6BDc (the list is at the top of the section "Instances"); 76 are degenerate (empty context or list,
    a Prop-sort subject, or equal compared objects). The environment is [si_Σ] of
    [PCUICCumulativitySpecEtaClosureInstances], or, for the two primitive-operation fields of T1,
    [Σ_po] of [PCUICEtaPrimOpInstance] (convention of [PCUICEtaFracInstances]). An instance shows only
    that the field's premises can hold at a real environment, and does NOT discharge the field at
    [typingE]: subject reduction over [typingE] (row T1), validity (T2a), the inversions and the
    bidirectional facts (T6, whose completeness part T6BDc is as strong as typed T8) and the
    infrastructure copies (T0) remain hypotheses until their rows land.

  Not stated here, on purpose: base [ws_cumul_pb_Sort_r_inv] (used only by [PCUICSafeRetyping]): its E form
  ([T ≤E tSort s] → [T ⇝ tSort s']) is FALSE untyped (plan §3, A6 F rows); its typed form is T8. *)

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(** ** T0 (E copies of the typing infrastructure: Substitution, Typing/*, Spine, Inductives, Contexts, WfUniverses, FixWitness, Arities, InductiveInversion) *)
Class T0_facts {cf : checker_flags} := {
  All_mfix_wf :
    forall (Σ : global_env × universes_decl) (Γ : context) (mfix : list (def term)), wfE Σ.1 -> wf_localE Σ Γ -> All (fun d : def term => isTypeRelE Σ Γ (dtype d) (binder_relevance (dname d))) mfix -> wf_localE Σ (Γ,,, fix_context mfix) ;
  arity_typing_spine :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {Γ' : context} {s : sort} {inst : list term} {s' : sort}, typing_spineE Σ Γ (it_mkProd_or_LetIn Γ' (tSort s)) inst (tSort s') -> [× #|inst| = context_assumptions Γ', leq_sort Σ s s' & ∑ instsubst : list term, spine_substE Σ Γ inst instsubst Γ'] ;
  closed_context_cumulativity :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ.1} (Γ : context) {pb : conv_pb} {t : term} {T : term} {Γ' : context}, Σ;;; Γ |-E t : T -> wf_localE Σ Γ' -> ws_cumul_ctx_pbE pb Σ Γ' Γ -> Σ;;; Γ' |-E t : T ;
  ctx_inst_open_terms :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ : context) (args : list term) (Δ : context), ctx_instE Σ Γ args Δ -> All (fun t : term => on_free_vars (shiftnP #|Γ| xpred0) t) args ;
  ctx_inst_smash :
    forall {Σ : global_env_ext} {Γ : context} {i : list term} {Δ : list context_decl}, ctx_instE Σ Γ i (List.rev Δ) <~> ctx_instE Σ Γ i (List.rev (smash_context [] Δ)) ;
  ctx_inst_spine_subst :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {Δ : list context_decl} {args : list term}, wf_localE Σ (Γ,,, Δ) -> forall (ci : ctx_instE Σ Γ args (List.rev Δ)), spine_substE Σ Γ args (ctx_inst_subE ci) Δ ;
  ind_arity_relevant :
    forall (Σ : global_env_ext) (mdecl : mutual_inductive_body) (idecl : one_inductive_body), wfE Σ.1 -> let ind_type := it_mkProd_or_LetIn (ind_params mdecl) (it_mkProd_or_LetIn (ind_indices idecl) (tSort (ind_sort idecl))) in isTypeE Σ [] ind_type -> isTypeRelE Σ [] ind_type rel_of_Type ;
  inductive_cumulative_indices :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {ind : inductive} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {u : Instance.t} {u' : Instance.t} {napp : nat}, declared_inductive Σ ind mdecl idecl -> consistent_instance_ext Σ (ind_universes mdecl) u -> consistent_instance_ext Σ (ind_universes mdecl) u' -> PCUICEquality.cmp_ind_universes Σ ind napp u u' -> forall (Γ : context) (pars : list term) (pars' : list term) (parsubst : list term) (parsubst' : list term), spine_substE Σ Γ pars parsubst (ind_params mdecl)@[u] -> spine_substE Σ Γ pars' parsubst' (ind_params mdecl)@[u'] -> ws_cumul_pbE_terms Σ Γ pars pars' -> let indctx := (ind_indices idecl)@[u] in let indctx' := (ind_indices idecl)@[u'] in let pindctx := subst_context parsubst 0 indctx in let pindctx' := subst_context parsubst' 0 indctx' in ws_cumul_ctx_pbE_rel Cumul Σ Γ (smash_context [] pindctx) (smash_context [] pindctx') ;
  inversion_it_mkProd_or_LetIn :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {Δ : context} {t : term} {s : sort}, Σ;;; Γ |-E it_mkProd_or_LetIn Δ t : tSort s -> Σ;;; Γ,,, Δ |-E t : tSort s ;
  invert_type_mkApps_ind :
    forall (Σ : global_env_ext) (Γ : context) (ind : inductive) (u : Instance.t) (args : list term) (T : term) (mdecl : mutual_inductive_body) (idecl : one_inductive_body), wfE Σ.1 -> declared_inductive Σ.1 ind mdecl idecl -> Σ;;; Γ |-E mkApps (tInd ind u) args : T -> typing_spineE Σ Γ (ind_type idecl)@[u] args T × consistent_instance_ext Σ (ind_universes mdecl) u ;
  isTypeRel_cstr_type :
    forall (Σ : global_env_ext) (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (cdecl : constructor_body) (n : nat), wfE Σ.1 -> nth_error (ind_bodies mdecl) n = Some idecl -> cstr_type cdecl = it_mkProd_or_LetIn (ind_params mdecl,,, cstr_args cdecl) (mkApps (tRel (#|ind_params mdecl,,, cstr_args cdecl| + (#|ind_bodies mdecl| - S n))) (to_extended_list_k (ind_params mdecl) #|cstr_args cdecl| ++ cstr_indices cdecl)) -> isTypeE Σ [] (ind_type idecl) -> PCUICReduction.red Σ.1 [] (ind_type idecl) (it_mkProd_or_LetIn (ind_params mdecl) (it_mkProd_or_LetIn (ind_indices idecl) (tSort (ind_sort idecl)))) -> isTypeE Σ [] (it_mkProd_or_LetIn (ind_params mdecl) (it_mkProd_or_LetIn (ind_indices idecl) (tSort (ind_sort idecl)))) -> isSortRel (ind_sort idecl) (ind_relevance idecl) -> ctx_instE Σ (arities_context (ind_bodies mdecl),,, ind_params mdecl,,, cstr_args cdecl) (cstr_indices cdecl) (List.rev (lift_context #|cstr_args cdecl| 0 (ind_indices idecl))) -> isTypeE Σ (arities_context (ind_bodies mdecl)) (cstr_type cdecl) -> isTypeRelE Σ (arities_context (ind_bodies mdecl)) (cstr_type cdecl) (ind_relevance idecl) ;
  isTypeRel_lift :
    forall {Σ : global_env_ext} {n : nat} {Γ : list context_decl} {ty : term} {r : relevance} (isdecl : n <= #|Γ|), wfE Σ -> wf_localE Σ Γ -> isTypeRelE Σ (skipn n Γ) ty r -> isTypeRelE Σ Γ (lift0 n ty) r ;
  isType_lift :
    forall {Σ : global_env_ext} {n : nat} {Γ : list context_decl} {ty : term} (isdecl : n <= #|Γ|), wfE Σ -> wf_localE Σ Γ -> isTypeE Σ (skipn n Γ) ty -> isTypeE Σ Γ (lift0 n ty) ;
  isType_apply :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {na : aname} {A : term} {B : term} {t : term}, isTypeE Σ Γ (tProd na A B) -> Σ;;; Γ |-E t : A -> isTypeE Σ Γ (B {0 := t}) ;
  isType_it_mkProd_or_LetIn_wf_local :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {Δ : context} {T : term}, isTypeE Σ Γ (it_mkProd_or_LetIn Δ T) -> wf_localE Σ (Γ,,, Δ) ;
  isType_mkApps_Ind :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {mdecl : mutual_inductive_body} {ind : inductive} {idecl : one_inductive_body} (decli : declared_inductive Σ ind mdecl idecl) {Γ : context} {puinst : Instance.t} {args : list term} {inst : list term}, consistent_instance_ext Σ (ind_universes mdecl) puinst -> spine_substE Σ Γ args inst (ind_params mdecl,,, ind_indices idecl)@[puinst] -> Σ;;; Γ |-E mkApps (tInd ind puinst) args : tSort (ind_sort idecl)@[puinst] ;
  isType_mkApps_Ind_inv :
    forall {Σ : global_env_ext} {Γ : context} {ind : inductive} {u : Instance.t} {args : list term} (wfΣ : wfE Σ.1) {mdecl : mutual_inductive_body} {idecl : one_inductive_body} (declm : declared_inductive Σ.1 ind mdecl idecl), wf_localE Σ Γ -> isTypeE Σ Γ (mkApps (tInd ind u) args) -> ∑ parsubst argsubst : list term, let parctx := (ind_params mdecl)@[u] in let argctx := subst_context parsubst 0 (ind_indices idecl)@[u] in [× spine_substE Σ Γ (firstn (ind_npars mdecl) args) parsubst parctx, spine_substE Σ Γ (skipn (ind_npars mdecl) args) argsubst argctx, #|firstn (ind_npars mdecl) args| = ind_npars mdecl, #|skipn (ind_npars mdecl) args| = context_assumptions (ind_indices idecl) & consistent_instance_ext Σ (ind_universes mdecl) u] ;
  isType_rec_arg_welltyped :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {T : term} {ctx : context} {concl : term} {n : nat} {c : context_decl}, isTypeE Σ Γ T -> decompose_prod_assum [] T = (ctx, concl) -> nth_error (List.rev (smash_context [] ctx)) n = Some c -> welltypedE Σ (Γ,,, skipn (#|smash_context [] ctx| - n) (smash_context [] ctx)) (decl_type c) ;
  isType_tProd :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {na : aname} {A : term} {B : term}, isTypeE Σ Γ (tProd na A B) <~> isTypeRelE Σ Γ A (binder_relevance na) × isTypeE Σ (Γ,, vass na A) B ;
  isType_wf_universes :
    forall {Σ : global_env × universes_decl} {Γ : context} {T : term}, wfE Σ.1 -> isTypeE Σ Γ T -> wf_universes Σ T ;
  on_minductive_wf_params :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {ind : kername} {mdecl : mutual_inductive_body} {u : Instance.t}, declared_minductive Σ.1 ind mdecl -> consistent_instance_ext Σ (ind_universes mdecl) u -> wf_localE Σ (ind_params mdecl)@[u] ;
  on_minductive_wf_params_indices_inst :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {mdecl : mutual_inductive_body} {ind : inductive} {idecl : one_inductive_body} (decli : declared_inductive Σ ind mdecl idecl) (u : Instance.t), consistent_instance_ext Σ (ind_universes mdecl) u -> wf_localE Σ (ind_params mdecl,,, ind_indices idecl)@[u] ;
  sorts_local_ctx_wf_local :
    forall (Σ : global_env_ext) (Γ : context) (Δ : context) (s : list sort), wf_localE Σ Γ -> sorts_local_ctx (lift_typing typingE) Σ Γ Δ s -> wf_localE Σ (Γ,,, Δ) ;
  type_local_ctx_wf_local :
    forall (Σ : global_env_ext) (Γ : context) (Δ : context) (s : sort), wf_localE Σ Γ -> type_local_ctx (lift_typing typingE) Σ Γ Δ s -> wf_localE Σ (Γ,,, Δ) ;
  spine_subst_app :
    forall {Σ : global_env_ext} {Γ : list context_decl} {Δ : context} {Δ' : list context_decl} {inst : list term} {inst' : list term} {insts : list term}, #|inst| = context_assumptions Δ -> wf_localE Σ (Γ,,, Δ,,, Δ') -> spine_substE Σ Γ inst (skipn #|Δ'| insts) Δ -> spine_substE Σ Γ inst' (firstn #|Δ'| insts) (subst_context (skipn #|Δ'| insts) 0 Δ') -> spine_substE Σ Γ (inst ++ inst') insts (Δ,,, Δ') ;
  spine_subst_ctx_inst :
    forall {Σ : global_env_ext} {Γ : context} {Δ : context} {args : list term} {s : list term}, spine_substE Σ Γ args s Δ -> ctx_instE Σ Γ args (List.rev Δ) ;
  spine_subst_cumul :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Δ : list context_decl} {args : list term} {Γ : context} {Γ' : context}, PCUICLiftSubst.assumption_context Γ -> PCUICLiftSubst.assumption_context Γ' -> wf_localE Σ (Δ,,, Γ) -> wf_localE Σ (Δ,,, Γ') -> ws_cumul_ctx_pbE_rel Cumul Σ Δ Γ Γ' -> spine_substE Σ Δ args (List.rev args) Γ -> spine_substE Σ Δ args (List.rev args) Γ' ;
  spine_subst_smash :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {inst : list term} {s : list term} {Δ : context}, spine_substE Σ Γ inst s Δ -> spine_substE Σ Γ inst (List.rev inst) (smash_context [] Δ) ;
  spine_subst_inst_subst :
    forall {Σ : global_env_ext} {Γ : context} {inst : list term} {s : list term} {Δ : context} {Δ' : context}, spine_substE Σ Γ inst s Δ -> subst_context s 0 Δ' = subst_context (List.rev inst) 0 (expand_lets_ctx Δ Δ') ;
  substitution :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {Γ' : context} {s : list term} {Δ : list context_decl} {t : term} {T : term}, subsletE Σ Γ s Γ' -> Σ;;; Γ,,, Γ',,, Δ |-E t : T -> Σ;;; Γ,,, subst_context s 0 Δ |-E subst s #|Δ| t : subst s #|Δ| T ;
  substitution_wf_local :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {Γ' : context} {s : list term} {Δ : list context_decl}, subsletE Σ Γ s Γ' -> wf_localE Σ (Γ,,, Γ',,, Δ) -> wf_localE Σ (Γ,,, subst_context s 0 Δ) ;
  typing_expand_lets :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ : list context_decl) (Δ : list context_decl) (t : term) (T : term), Σ;;; Γ,,, Δ |-E t : T -> Σ;;; Γ,,, smash_context [] Δ |-E expand_lets Δ t : expand_lets Δ T ;
  typing_spine_ind_type_inv :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {mdecl : mutual_inductive_body} {ind : inductive} {idecl : one_inductive_body} (decli : declared_inductive Σ ind mdecl idecl) (Γ : context) (u : Instance.t) (args : list term) (T : term), wf_localE Σ Γ -> consistent_instance_ext Σ (ind_universes mdecl) u -> typing_spineE Σ Γ (ind_type idecl)@[u] args T -> typing_spineE Σ Γ (it_mkProd_or_LetIn (ind_params mdecl,,, ind_indices idecl) (tSort (ind_sort idecl)))@[u] args T ;
  typing_spine_strengthen :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {T : term} {args : list term} {U : term}, typing_spineE Σ Γ T args U -> forall T' : term, isTypeE Σ Γ T' -> Σ ;;; Γ ⊢E T' ≤ T -> typing_spineE Σ Γ T' args U ;
  typing_wf_sort :
    forall {Σ : global_env_ext} {Γ : context} {t : term} {s : sort}, wfE Σ -> Σ;;; Γ |-E t : tSort s -> wf_sort Σ s ;
  typing_wf_universes :
    forall {Σ : global_env_ext} {Γ : context} {t : term} {T : term}, wfE Σ -> Σ;;; Γ |-E t : T -> wf_universes Σ t && wf_universes Σ T ;
  weaken_ctx :
    forall {Σ : global_env × universes_decl} {Γ : context} {t : term} {T : term} (Δ : context), wfE Σ.1 -> wf_localE Σ Δ -> Σ;;; Γ |-E t : T -> Σ;;; Δ,,, Γ |-E t : T ;
  weaken_wf_local :
    forall {Σ : global_env × universes_decl} {Δ : context} (Γ : context), wfE Σ.1 -> wf_localE Σ Γ -> wf_localE Σ Δ -> wf_localE Σ (Γ,,, Δ) ;
  weakening_wf_local :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {Γ' : list context_decl} {Γ'' : list context_decl}, wf_localE Σ (Γ,,, Γ') -> wf_localE Σ (Γ,,, Γ'') -> wf_localE Σ (Γ,,, Γ'',,, lift_context #|Γ''| 0 Γ') ;
  welltyped_prod_codomain :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {na : aname} {A : term} {B : term}, welltypedE Σ Γ (tProd na A B) -> welltypedE Σ (Γ,, vass na A) B ;
  wf_case_branch_type :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {ci : case_info} {p : predicate term} (ps : sort) (args : list term), declared_inductive Σ ci mdecl idecl -> isTypeE Σ Γ (mkApps (tInd ci (puinst p)) (pparams p ++ args)) -> wf_predicate mdecl idecl p -> let predctx := case_predicate_context ci mdecl idecl p in Σ;;; Γ,,, predctx |-E preturn p : tSort ps -> let ptm := it_mkLambda_or_LetIn predctx (preturn p) in All2 PCUICEquality.eq_decl_upto_names (pcontext p) (ind_predicate_context ci mdecl idecl) -> forall (i : nat) (cdecl : constructor_body) (br : branch term), declared_constructor Σ (ci, i) mdecl idecl cdecl -> wf_branch cdecl br -> let cstr_br_ctx := case_branch_context_nopars ci mdecl (puinst p) cdecl in let brctx' := map2 set_binder_name (forget_types (bcontext br)) cstr_br_ctx in let brctxty := case_branch_type ci mdecl idecl p br ptm i cdecl in [× wf_branch cdecl br, wf_localE Σ (Γ,,, (ind_params mdecl)@[puinst p],,, cstr_br_ctx), wf_localE Σ (Γ,,, (ind_params mdecl)@[puinst p],,, brctx'), wf_localE Σ (Γ,,, brctxty.1) & Σ;;; Γ,,, brctxty.1 |-E brctxty.2 : tSort ps] ;
  wf_case_predicate_context :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {ci : case_info} {p : predicate term} {args : list term}, declared_inductive Σ ci mdecl idecl -> isTypeE Σ Γ (mkApps (tInd ci (puinst p)) (pparams p ++ args)) -> wf_predicate mdecl idecl p -> let predctx := case_predicate_context ci mdecl idecl p in wf_localE Σ (Γ,,, predctx) ;
  wf_local_expand_lets :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {Δ : list context_decl} {Γ' : list context_decl}, wf_localE Σ (Γ,,, Δ,,, Γ') -> wf_localE Σ (Γ,,, smash_context [] Δ,,, expand_lets_ctx Δ Γ') ;
  wf_local_smash_context :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context}, wf_localE Σ Γ -> wf_localE Σ (smash_context [] Γ) ;
  wf_local_smash_end :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ Δ : list context_decl), wf_localE Σ (Γ,,, Δ) -> wf_localE Σ (Γ,,, smash_context [] Δ) ;
  isType_weaken :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {T : term}, wf_localE Σ Γ -> isTypeE Σ [] T -> isTypeE Σ Γ T ;
  isType_it_mkProd_or_LetIn :
    forall {Σ : global_env_ext} {Γ Δ : list context_decl} {T : term}, wfE Σ.1 -> isTypeE Σ (Γ,,, Δ) T -> isTypeE Σ Γ (it_mkProd_or_LetIn Δ T) ;
  type_local_ctx_wf :
    forall {Σ : global_env_ext} {Γ Δ : context} {s : sort}, wfE Σ.1 -> type_local_ctx (lift_typing typingE) Σ Γ Δ s -> wf_sort Σ s ;
  wf_case_branches_types' :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {ci : case_info} {p : predicate term} (ps : sort) (args : list term) (brs : list (branch term)), declared_inductive Σ ci mdecl idecl -> isTypeE Σ Γ (mkApps (tInd ci (puinst p)) (pparams p ++ args)) -> wf_predicate mdecl idecl p -> let predctx := case_predicate_context ci mdecl idecl p in Σ;;; Γ,,, predctx |-E preturn p : tSort ps -> let ptm := it_mkLambda_or_LetIn predctx (preturn p) in wf_branches idecl brs -> All2 PCUICEquality.eq_decl_upto_names (pcontext p) (ind_predicate_context ci mdecl idecl) -> All2i (fun (i : nat) (cdecl : constructor_body) (br : branch term) => let cstr_br_ctx := case_branch_context_nopars ci mdecl (puinst p) cdecl in let brctx' := map2 set_binder_name (forget_types (bcontext br)) cstr_br_ctx in let brctxty := case_branch_type ci mdecl idecl p br ptm i cdecl in [× wf_branch cdecl br, wf_localE Σ (Γ,,, (ind_params mdecl)@[puinst p],,, cstr_br_ctx), wf_localE Σ (Γ,,, (ind_params mdecl)@[puinst p],,, brctx'), wf_localE Σ (Γ,,, brctxty.1) & Σ;;; Γ,,, brctxty.1 |-E brctxty.2 : tSort ps]) 0 (ind_ctors idecl) brs
}.

(** ** U (untyped facts whose base statement takes [wf Σ] only for closed bodies or universes; reduction is unchanged in E, so these are plumbing over [wfE_ClosedBodies], not research) *)
Class U_facts {cf : checker_flags} := {
  LSet_in_global_bounded :
    forall {Σ : global_env} {l : LevelSet.elt} (k : nat), wfE Σ -> LevelSet.In l (global_levels Σ) -> closedu_level k l ;
  closed_red_from_empty :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {M : term} {N : term}, on_free_vars_ctx xpred0 Γ -> closed M -> PCUICReduction.red Σ [] M N -> Σ ;;; Γ ⊢ M ⇝ N ;
  red_expand_let :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {na : aname} {b : term} {ty : term} {t : term}, wf_localE Σ (Γ,,, [vdef na b ty]) -> on_free_vars (shiftnP #|Γ,,, [vdef na b ty]| (fun _ : nat => false)) t -> Σ ;;; Γ,, vdef na b ty ⊢ t ⇝ lift0 1 (t {0 := b}) ;
  red_it_mkProd_or_LetIn_smash :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ : list context_decl) (ctx : context) (t : term) (u : term) (n : nat) (c : context_decl), Σ ;;; Γ ⊢ it_mkProd_or_LetIn ctx t ⇝ u -> nth_error (List.rev (smash_context [] ctx)) n = Some c -> ∑ (ctx' : context) (t' : term) (d : context_decl), [× decompose_prod_assum [] u = (ctx', t'), nth_error (List.rev (smash_context [] ctx')) n = Some d & Σ ;;; Γ,,, skipn (#|smash_context [] ctx| - n) (smash_context [] ctx) ⊢ decl_type c ⇝ decl_type d] ;
  red_mkApps_smash_witness :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {C : term} {ctx : context} {i : inductive} {u : Instance.t} {l : list term}, Σ ;;; Γ ⊢ C ⇝ it_mkProd_or_LetIn ctx (mkApps (tInd i u) l) -> ∑ l' : list term, Σ ;;; Γ ⊢ C ⇝ it_mkProd_or_LetIn (smash_context [] ctx) (mkApps (tInd i u) l') ;
  red_rec_arg_check_one_fix :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ : list context_decl) (d : def term) (ctx : context) (concl : term) (c : context_decl) (ind : inductive) (u : Instance.t) (args : list term), on_free_vars (shiftnP #|Γ| xpred0) (dtype d) -> decompose_prod_assum [] (dtype d) = (ctx, concl) -> nth_error (List.rev (smash_context [] ctx)) (rarg d) = Some c -> Σ ;;; Γ,,, skipn (#|smash_context [] ctx| - rarg d) (smash_context [] ctx) ⊢ decl_type c ⇝ mkApps (tInd ind u) args -> has_rec_arg d × (∑ ty : term, Σ ;;; Γ ⊢ dtype d ⇝ ty × check_one_fix (def_with_type d ty) = Some (inductive_mind ind)) ;
  wf_universes_inst :
    forall {Σ : global_env_ext} (univs : universes_decl) (t : term) (u : list LevelSet.elt), wfE Σ -> on_udecl_prop Σ.1 univs -> wf_instance Σ u -> wf_universes (Σ.1, univs) t -> wf_universes Σ t@[u] ;
  closed_red_confluence :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : list context_decl} {t : term} {u : term} {v : term}, Σ ;;; Γ ⊢ t ⇝ u -> Σ ;;; Γ ⊢ t ⇝ v -> ∑ v' : term, Σ ;;; Γ ⊢ u ⇝ v' × Σ ;;; Γ ⊢ v ⇝ v' ;
  whnf_red_inv :
    forall {Σ : global_env_ext} (Γ : context) (t t' : term), wfE Σ -> whnf RedFlags.default Σ Γ t -> Σ ;;; Γ ⊢ t ⇝ t' -> whnf_red Σ Γ t t'
}.

(** ** T1 (subject reduction over [typingE], PCUICSR) *)
Class T1_facts {cf : checker_flags} := {
  isType_prim_arg_types :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {tags : list prim_tag} {res : term} {T : term}, wf_localE Σ Γ -> (forall t : prim_tag, In t tags -> t <> primArray) -> All (prim_op_tag_declared Σ) tags -> PCUICPrimOpType.prim_arg_types (retroknowledge Σ.1) tags res = Some T -> isTypeE Σ Γ res -> isTypeE Σ Γ T ;
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
    forall (Σ : global_env_ext) (Γ : context) (Γ' : context) (wfΣ : wfE Σ), wf_localE Σ Γ -> wf_local_bd_relE Σ Γ Γ' -> wf_local_relE Σ Γ Γ' ;
  wf_rel_weak :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ) (Γ : context), wf_localE Σ Γ -> forall (Γ' : context), wf_localE Σ Γ' -> wf_local_relE Σ Γ Γ'
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
    [typing_infering_sort] implies typed T8-Sort.) *)
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

  Lemma spine_subst_wt_terms {hT0 : T0_facts} {Σ : global_env_ext} {Γ : context} {inst s : list term} {Δ : context} :
    spine_substE Σ Γ inst s Δ -> All (fun t : term => ∑ T : term, Σ ;;; Γ |-E t : T) inst.
  Proof.
    move/spine_subst_ctx_inst.
    induction 1; try constructor; auto.
    now exists t.
  Qed.

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
(** ** A (typed context conversion over [ws_cumul_pbE]). EtaHypAuditB found it provable now; its proof needs
    reflexivity of [ws_cumul_ctx_pbE] at any [pb] (base E has it at [Conv] only, [PCUICContextConversionEta.v:125]);
    until that lemma exists it stays a field. *)
Class A_facts {cf : checker_flags} := {
  ws_cumul_ctx_pb_rel_app :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {pb : conv_pb} {Γ : list context_decl} {Δ : list context_decl} {Δ' : list context_decl}, ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ' <~> ws_cumul_ctx_pbE pb Σ (Γ,,, Δ) (Γ,,, Δ')
}.

Class EtaFacts {cf : checker_flags} : Prop := {
  eta_T0 : ∥ T0_facts ∥ ;
  eta_U : ∥ U_facts ∥ ;
  eta_T1 : ∥ T1_facts ∥ ;
  eta_T2a : ∥ T2a_facts ∥ ;
  eta_T6 : ∥ T6_facts ∥ ;
  eta_T6BD : ∥ T6BD_facts ∥ ;
  eta_T6BDu : ∥ T6BDu_facts ∥ ;
  eta_T6BDc : ∥ T6BDc_facts ∥ ;
  eta_A : ∥ A_facts ∥ }.

(** [sq] of the copies: first open the premise, so that the rows' classes are in the context (as
    instances) for the base proof scripts. *)
Ltac unpack_eta_facts := repeat match goal with | EF : EtaFacts |- _ => destruct EF end.
Ltac sq := unpack_eta_facts; MRSquash.sq.

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

(** ** Instances: satisfying instances of the fields of the hypothesis classes above

  BET-64 EtaCheckerLane, 2026-10-29. One lemma [<field>_inst] per field of each hypothesis class above
  ([T0_facts], [U_facts], [T1_facts], [T2a_facts], [T6_facts], [T6BD_facts], [T6BDu_facts], [T6BDc_facts]
  and, while it is a class, [A_facts]), in the class order.
  Convention of [PCUICEtaFracInstances]: the environment is [si_Σ] of
  [PCUICCumulativitySpecEtaClosureInstances] ([Inductive I (A : Prop) : Prop := c : I A]), or, where the
  field needs a registered primitive type, [Σ_po] of [PCUICEtaPrimOpInstance] (registers [int]); the terms
  are closed.

  Each instance states the field's premises and its conclusion at the chosen arguments, as one product.
  The premise [wfE Σ] (named binder or arrow) holds by [si_wfE] or [ti_po_wfE]. Every typed premise is a
  base derivation lifted to E with [typing_incl_E] (and its consequences [ti_*] below: local environments,
  [isType], spines, substitutions, cumulativity through [ws_cumul_pb_incl_E]); the bidirectional E premises
  are built with the constructors of [PCUICTypingEtaDefs]. The conclusion is the base lemma of the same
  name (qualified) applied at that point and lifted to E; the equivalences, the bidirectional conclusions
  and the reflexive reductions of [T6BDu_facts] are built directly. No proof uses a field of a class.

  Each instance has a tag on the line above it: [(* non-degenerate *)], or [(* degenerate: <why> *)] when
  its point has an empty context or list where the field quantifies over one, a subject that is the sort
  Prop, or two compared objects that are equal (T = U, a reflexive reduction or comparison). Non-degenerate
  (16): the six [T6BDc_facts] instances (in the context [A : Prop], on [I A] and [c A]), [All_mfix_wf],
  [arity_typing_spine], [closed_context_cumulativity] (a β-redex in the context), [ind_arity_relevant],
  [on_minductive_wf_params], [on_minductive_wf_params_indices_inst], [weaken_wf_local],
  [closed_red_from_empty], [infering_ind_typing] and [wf_rel_weak]. The other 76 are degenerate: each still
  meets every premise of its field, at a weaker point.

  (1) Such an instance shows that the hypothesis is consistent and about something real. (2) It does NOT
  discharge the hypothesis at [typingE]: each field remains a hypothesis until its plan row lands (T0, T1,
  T2a, T6; T6BDc also needs T8; U is untyped plumbing over [wfE_ClosedBodies]). *)

From MetaRocq.PCUIC Require Import PCUICCumulativitySpecEtaClosureInstances PCUICEtaFracInstances
     PCUICEtaPrimOpInstance.
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

(** ** Instances of [T0_facts]

  Each lemma [<field>_inst] below states the premises and the conclusion of the field [<field>] of
  [T0_facts] at concrete arguments in [si_Σ] (the premise [wfE] holds there by [si_wfE]), builds each
  typed premise from a base derivation lifted with [typing_incl_E], and proves the conclusion from the base
  lemma of the same name. (1) This instance shows that the hypothesis is consistent and about something
  real. (2) It does NOT discharge the hypothesis at [typingE]: the field remains a hypothesis until plan
  row T0 (the E copies of the typing infrastructure) lands. *)

(* non-degenerate *)
Lemma All_mfix_wf_inst :
  [× wfE si_Σ.1, wf_localE si_Σ ti_ΓP,
     All (fun d : def term => isTypeRelE si_Σ ti_ΓP (dtype d) (binder_relevance (dname d))) [ti_dA] &
     wf_localE si_Σ (ti_ΓP ,,, fix_context [ti_dA])].
Proof.
  have hd : All (fun d : def term => isTypeRel si_Σ ti_ΓP (dtype d) (binder_relevance (dname d))) [ti_dA].
  { constructor; [exact ti_dA_ty|constructor]. }
  have hdE : All (fun d : def term => isTypeRelE si_Σ ti_ΓP (dtype d) (binder_relevance (dname d))) [ti_dA].
  { constructor; [exact (siIR ti_dA_ty)|constructor]. }
  split; [exact si_wfE|exact (siW ti_wf_ΓP)|exact hdE|].
  exact (siW (PCUICWeakeningTyp.All_mfix_wf si_Σ ti_ΓP [ti_dA] si_wf ti_wf_ΓP hd)).
Qed.

(* non-degenerate *)
Lemma arity_typing_spine_inst :
  typing_spineE si_Σ ti_ΓP (it_mkProd_or_LetIn ti_ΓP (tSort sProp)) [tRel 0] (tSort sProp) ×
  [× #|[tRel 0]| = context_assumptions ti_ΓP, leq_sort si_Σ sProp sProp &
     ∑ instsubst : list term, spine_substE si_Σ ti_ΓP [tRel 0] instsubst ti_ΓP].
Proof.
  have hs : PCUICArities.typing_spine si_Σ ti_ΓP (it_mkProd_or_LetIn ti_ΓP (tSort sProp)) [tRel 0] (tSort sProp) :=
    fst (PCUICInductives.invert_type_mkApps_ind si_Σ ti_ΓP si_ind [] [tRel 0] (tSort sProp) si_mdecl si_idecl
           si_wf si_declared_inductive ti_IA_ty).
  split; [exact (siTS hs)|].
  destruct (PCUICSpine.arity_typing_spine (Σ := si_Σ) (wfΣ := si_wf) hs) as [h1 h2 [s h3]].
  split; [exact h1|exact h2|exists s; exact (siS h3)].
Qed.

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

(* degenerate: Γ = [] (the argument list [∀ A : Prop. A] and the telescope [A : Prop] are not empty) *)
Lemma ctx_inst_open_terms_inst :
  ctx_instE si_Σ [] [ti_F] (List.rev ti_ΓP) ×
  All (fun t : term => on_free_vars (shiftnP #|([] : context)| xpred0) t) [ti_F].
Proof.
  have h := PCUICSpine.spine_subst_ctx_inst ti_spine_F.
  split; [exact (siCI h)|].
  exact (PCUICSpine.ctx_inst_open_terms (Σ := si_Σ) (wfΣ := si_wf) [] [ti_F] _ h).
Qed.

(* degenerate: Γ = [], and Δ = [A : Prop] has no let-in, so smash_context is the identity *)
Lemma ctx_inst_smash_inst :
  [× ctx_instE si_Σ [] [ti_F] (List.rev ti_ΓP),
     ctx_instE si_Σ [] [ti_F] (List.rev (smash_context [] ti_ΓP)) &
     ctx_instE si_Σ [] [ti_F] (List.rev ti_ΓP) <~> ctx_instE si_Σ [] [ti_F] (List.rev (smash_context [] ti_ΓP))].
Proof.
  have h := PCUICSpine.spine_subst_ctx_inst ti_spine_F.
  have h' := fst (PCUICSpine.ctx_inst_smash (Σ := si_Σ)) h.
  split; [exact (siCI h)|exact (siCI h')|split; intros _; [exact (siCI h')|exact (siCI h)]].
Qed.

(* degenerate: Γ = [] *)
Lemma ctx_inst_spine_subst_inst :
  [× wf_localE si_Σ ([] ,,, ti_ΓP), ctx_instE si_Σ [] [ti_F] (List.rev ti_ΓP) &
     spine_substE si_Σ [] [ti_F] (ctx_inst_subE ti_ciE) ti_ΓP].
Proof.
  have hs := PCUICSpine.ctx_inst_spine_subst (Σ := si_Σ) (wfΣ := si_wf) (Γ := []) (Δ := ti_ΓP) ti_wf_ΓP ti_ciB.
  (* [ctx_inst_sub ti_ciB] and [ctx_inst_subE ti_ciE] both compute to [[ti_F]] *)
  split; [exact (siW ti_wf_ΓP)|exact ti_ciE|exact (siS hs)].
Qed.

(* non-degenerate *)
Lemma ind_arity_relevant_inst :
  let ind_type := it_mkProd_or_LetIn (ind_params si_mdecl)
                    (it_mkProd_or_LetIn (ind_indices si_idecl) (tSort (ind_sort si_idecl))) in
  [× wfE si_Σ.1, isTypeE si_Σ [] ind_type & isTypeRelE si_Σ [] ind_type rel_of_Type].
Proof.
  intros ind_type.
  have h : isType si_Σ [] ind_type := has_sort_isType _ (ti_arity_ty [] ti_wf_nil).
  split; [exact si_wfE|exact (siI h)|].
  exact (siIR (PCUICInductiveInversion.ind_arity_relevant si_Σ si_mdecl si_idecl si_wf h)).
Qed.

(* degenerate: Γ = [], u = u', pars = pars', and I has no indices, so the conclusion compares two empty contexts *)
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

(* degenerate: Γ = [], and the subject t is Prop *)
Lemma inversion_it_mkProd_or_LetIn_inst :
  si_Σ ;;; [] |-E it_mkProd_or_LetIn ti_ΓP si_P :
    tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) ×
  si_Σ ;;; [] ,,, ti_ΓP |-E si_P : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)).
Proof.
  have h : si_Σ ;;; [] |- it_mkProd_or_LetIn ti_ΓP si_P :
             tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) := ti_arity_ty [] ti_wf_nil.
  split; [exact (siT h)|].
  exact (siT (PCUICSpine.inversion_it_mkProd_or_LetIn (Σ := si_Σ) (wfΣ := si_wf) h)).
Qed.

(* degenerate: Γ = [] *)
Lemma invert_type_mkApps_ind_inst :
  [× wfE si_Σ.1, declared_inductive si_Σ.1 si_ind si_mdecl si_idecl,
     si_Σ ;;; [] |-E mkApps (tInd si_ind []) [ti_F] : tSort sProp &
     typing_spineE si_Σ [] (ind_type si_idecl)@[[]] [ti_F] (tSort sProp) ×
     consistent_instance_ext si_Σ (ind_universes si_mdecl) []].
Proof.
  have h : si_Σ ;;; [] |- mkApps (tInd si_ind []) [ti_F] : tSort sProp := ti_IF_ty [] ti_wf_nil.
  destruct (PCUICInductives.invert_type_mkApps_ind si_Σ [] si_ind [] [ti_F] (tSort sProp) si_mdecl si_idecl
              si_wf si_declared_inductive h) as [hs hc].
  split; [exact si_wfE|exact si_declared_inductive|exact (siT h)|split; [exact (siTS hs)|exact hc]].
Qed.

(* degenerate: c has no arguments and I has no indices, so the ctx_inst premise is over empty lists *)
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

(* degenerate: ty = Prop, and skipn 1 Γ = [] *)
Lemma isTypeRel_lift_inst :
  [× 1 <= #|ti_ΓP|, wfE si_Σ, wf_localE si_Σ ti_ΓP, isTypeRelE si_Σ (skipn 1 ti_ΓP) si_P Relevant &
     isTypeRelE si_Σ ti_ΓP (lift0 1 si_P) Relevant].
Proof.
  have hr : isTypeRel si_Σ (skipn 1 ti_ΓP) si_P Relevant :=
    has_sort_isTypeRel (Sort.super sProp) Relevant eq_refl (ti_P_ty [] ti_wf_nil).
  split; [exact (le_n 1)|exact si_wfE|exact (siW ti_wf_ΓP)|exact (siIR hr)|].
  exact (siIR (PCUICWeakeningTyp.isTypeRel_lift (Σ := si_Σ) (n := 1) (Γ := ti_ΓP) (le_n 1) si_wf ti_wf_ΓP hr)).
Qed.

(* degenerate: ty = Prop, and skipn 1 Γ = [] *)
Lemma isType_lift_inst :
  [× 1 <= #|ti_ΓP|, wfE si_Σ, wf_localE si_Σ ti_ΓP, isTypeE si_Σ (skipn 1 ti_ΓP) si_P &
     isTypeE si_Σ ti_ΓP (lift0 1 si_P)].
Proof.
  have hr : isType si_Σ (skipn 1 ti_ΓP) si_P := has_sort_isType _ (ti_P_ty [] ti_wf_nil).
  split; [exact (le_n 1)|exact si_wfE|exact (siW ti_wf_ΓP)|exact (siI hr)|].
  exact (siI (PCUICWeakeningTyp.isType_lift (Σ := si_Σ) (n := 1) (Γ := ti_ΓP) (le_n 1) si_wf ti_wf_ΓP hr)).
Qed.

(* degenerate: Γ = [], and B = Prop does not depend on the argument *)
Lemma isType_apply_inst :
  [× isTypeE si_Σ [] (tProd si_na si_P si_P), si_Σ ;;; [] |-E ti_F : si_P &
     isTypeE si_Σ [] (si_P {0 := ti_F})].
Proof.
  have hP : isType si_Σ [] (tProd si_na si_P si_P) := has_sort_isType _ (ti_arity_ty [] ti_wf_nil).
  have hF : si_Σ ;;; [] |- ti_F : si_P := ti_F_ty [] ti_wf_nil.
  split; [exact (siI hP)|exact (siT hF)|].
  exact (siI (PCUICArities.isType_apply (Σ := si_Σ) (wfΣ := si_wf) hP hF)).
Qed.

(* degenerate: Γ = [], and T = Prop *)
Lemma isType_it_mkProd_or_LetIn_wf_local_inst :
  isTypeE si_Σ [] (it_mkProd_or_LetIn ti_ΓP si_P) × wf_localE si_Σ ([] ,,, ti_ΓP).
Proof.
  have h : isType si_Σ [] (it_mkProd_or_LetIn ti_ΓP si_P) := has_sort_isType _ (ti_arity_ty [] ti_wf_nil).
  split; [exact (siI h)|].
  exact (siW (PCUICArities.isType_it_mkProd_or_LetIn_wf_local (Σ := si_Σ) (wfΣ := si_wf) h)).
Qed.

(* degenerate: Γ = [] *)
Lemma isType_mkApps_Ind_inst :
  [× declared_inductive si_Σ si_ind si_mdecl si_idecl,
     consistent_instance_ext si_Σ (ind_universes si_mdecl) [],
     spine_substE si_Σ [] [ti_F] [ti_F] (ind_params si_mdecl ,,, ind_indices si_idecl)@[[]] &
     si_Σ ;;; [] |-E mkApps (tInd si_ind []) [ti_F] : tSort (ind_sort si_idecl)@[[]]].
Proof.
  pose proof (ti_spine_F :
    PCUICSpine.spine_subst si_Σ [] [ti_F] [ti_F] (ind_params si_mdecl ,,, ind_indices si_idecl)@[[]]) as hs.
  split; [exact si_declared_inductive|exact ti_cons|exact (siS hs)|].
  exact (siT (PCUICInductives.isType_mkApps_Ind (Σ := si_Σ) (wfΣ := si_wf) si_declared_inductive (Γ := [])
                ti_cons hs)).
Qed.

(* degenerate: Γ = [] *)
Lemma isType_mkApps_Ind_inv_inst :
  [× wfE si_Σ.1, declared_inductive si_Σ.1 si_ind si_mdecl si_idecl, wf_localE si_Σ [],
     isTypeE si_Σ [] (mkApps (tInd si_ind []) [ti_F]) &
     ∑ parsubst argsubst : list term,
       let parctx := (ind_params si_mdecl)@[[]] in
       let argctx := subst_context parsubst 0 (ind_indices si_idecl)@[[]] in
       [× spine_substE si_Σ [] (firstn (ind_npars si_mdecl) [ti_F]) parsubst parctx,
          spine_substE si_Σ [] (skipn (ind_npars si_mdecl) [ti_F]) argsubst argctx,
          #|firstn (ind_npars si_mdecl) [ti_F]| = ind_npars si_mdecl,
          #|skipn (ind_npars si_mdecl) [ti_F]| = context_assumptions (ind_indices si_idecl) &
          consistent_instance_ext si_Σ (ind_universes si_mdecl) []]].
Proof.
  have hI : isType si_Σ [] (mkApps (tInd si_ind []) [ti_F]) := has_sort_isType _ (ti_IF_ty [] ti_wf_nil).
  destruct (PCUICInductives.isType_mkApps_Ind_inv (Σ := si_Σ) (Γ := []) si_wf si_declared_inductive ti_wf_nil hI)
    as [ps [as' h]].
  cbv zeta in h. destruct h as [h1 h2 h3 h4 h5].
  split; [exact si_wfE|exact si_declared_inductive|constructor|exact (siI hI)|].
  exists ps, as'. cbv zeta.
  split; [exact (siS h1)|exact (siS h2)|exact h3|exact h4|exact h5].
Qed.

(* degenerate: Γ = [], and the type of the argument is Prop *)
Lemma isType_rec_arg_welltyped_inst :
  [× isTypeE si_Σ [] si_arity, decompose_prod_assum [] si_arity = (ti_ΓP, tSort sProp),
     nth_error (List.rev (smash_context [] ti_ΓP)) 0 = Some (vass si_na si_P) &
     welltypedE si_Σ ([] ,,, skipn (#|smash_context [] ti_ΓP| - 0) (smash_context [] ti_ΓP))
       (decl_type (vass si_na si_P))].
Proof.
  have h : isType si_Σ [] si_arity := has_sort_isType _ (ti_arity_ty [] ti_wf_nil).
  split; [exact (siI h)|reflexivity|reflexivity|].
  exact (siWT (PCUICFixWitness.isType_rec_arg_welltyped (Σ := si_Σ) (wfΣ := si_wf) (ctx := ti_ΓP)
                 (concl := tSort sProp) (n := 0) (c := vass si_na si_P) h eq_refl eq_refl)).
Qed.

(* degenerate: Γ = [], and A = B = Prop *)
Lemma isType_tProd_inst :
  [× isTypeE si_Σ [] (tProd si_na si_P si_P),
     isTypeRelE si_Σ [] si_P (binder_relevance si_na) × isTypeE si_Σ ([] ,, vass si_na si_P) si_P &
     (isTypeE si_Σ [] (tProd si_na si_P si_P) <~>
      isTypeRelE si_Σ [] si_P (binder_relevance si_na) × isTypeE si_Σ ([] ,, vass si_na si_P) si_P)].
Proof.
  have hP : isType si_Σ [] (tProd si_na si_P si_P) := has_sort_isType _ (ti_arity_ty [] ti_wf_nil).
  destruct (fst (PCUICArities.isType_tProd (Σ := si_Σ) (wfΣ := si_wf)) hP) as [h1 h2].
  have l := siI hP.
  have r := (siIR h1, siI h2).
  split; [exact l|exact r|split; intros _; [exact r|exact l]].
Qed.

(* degenerate: Γ = [], and T = Prop *)
Lemma isType_wf_universes_inst :
  [× wfE si_Σ.1, isTypeE si_Σ [] si_P & wf_universes si_Σ si_P].
Proof.
  have h : isType si_Σ [] si_P := has_sort_isType _ (ti_P_ty [] ti_wf_nil).
  split; [exact si_wfE|exact (siI h)|exact (PCUICWfUniverses.isType_wf_universes (Σ := si_Σ) si_wf h)].
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

(* degenerate: Γ = [] *)
Lemma sorts_local_ctx_wf_local_inst :
  [× wf_localE si_Σ [], sorts_local_ctx (lift_typing typingE) si_Σ [] ti_ΓP [Sort.super sProp] &
     wf_localE si_Σ ([] ,,, ti_ΓP)].
Proof.
  have hj : lift_typing typing si_Σ [] (j_vass_s si_na si_P (Sort.super sProp)) :=
    ti_vass_s [] si_na si_P _ (ti_P_ty [] ti_wf_nil) eq_refl.
  have hb : sorts_local_ctx (lift_typing typing) si_Σ [] ti_ΓP [Sort.super sProp] := (tt, hj).
  split; [constructor|exact (tt, siL hj)|].
  exact (siW (PCUICContexts.sorts_local_ctx_wf_local si_Σ [] ti_ΓP [Sort.super sProp] ti_wf_nil hb)).
Qed.


(* degenerate: Γ = [] *)
Lemma type_local_ctx_wf_local_inst :
  [× wf_localE si_Σ [], type_local_ctx (lift_typing typingE) si_Σ [] ti_ΓF sProp &
     wf_localE si_Σ ([] ,,, ti_ΓF)].
Proof.
  have hj : lift_typing typing si_Σ [] (j_vass_s si_na ti_F sProp) :=
    ti_vass_s [] si_na ti_F sProp (ti_F_ty [] ti_wf_nil) eq_refl.
  have hb : type_local_ctx (lift_typing typing) si_Σ [] ti_ΓF sProp := (ti_wfs, hj).
  split; [constructor|exact (ti_wfs, siL hj)|].
  exact (siW (PCUICContexts.type_local_ctx_wf_local si_Σ [] ti_ΓF sProp ti_wf_nil hb)).
Qed.

(* degenerate: Γ = [], Δ' = [] and inst' = [] *)
Lemma spine_subst_app_inst :
  [× #|[ti_F]| = context_assumptions ti_ΓP,
     wf_localE si_Σ ([] ,,, ti_ΓP ,,, []),
     spine_substE si_Σ [] [ti_F] (skipn #|([] : context)| [ti_F]) ti_ΓP,
     spine_substE si_Σ [] [] (firstn #|([] : context)| [ti_F]) (subst_context (skipn #|([] : context)| [ti_F]) 0 []) &
     spine_substE si_Σ [] ([ti_F] ++ []) [ti_F] (ti_ΓP ,,, [])].
Proof.
  have hw : wf_local si_Σ ([] ,,, ti_ΓP ,,, []) := ti_wf_ΓP.
  have hs : PCUICSpine.spine_subst si_Σ [] [ti_F] (skipn #|([] : context)| [ti_F]) ti_ΓP := ti_spine_F.
  have hs' : PCUICSpine.spine_subst si_Σ [] [] (firstn #|([] : context)| [ti_F])
               (subst_context (skipn #|([] : context)| [ti_F]) 0 []) := ti_spine_nil.
  split; [reflexivity|exact (siW hw)|exact (siS hs)|exact (siS hs')|].
  exact (siS (PCUICSpine.spine_subst_app (Σ := si_Σ) (Γ := []) (Δ := ti_ΓP) (Δ' := []) (inst := [ti_F]) (inst' := [])
                (insts := [ti_F]) eq_refl hw hs hs')).
Qed.

(* degenerate: Γ = [] *)
Lemma spine_subst_ctx_inst_inst :
  spine_substE si_Σ [] [ti_F] [ti_F] ti_ΓP × ctx_instE si_Σ [] [ti_F] (List.rev ti_ΓP).
Proof. split; [exact (siS ti_spine_F)|exact (siCI (PCUICSpine.spine_subst_ctx_inst ti_spine_F))]. Qed.

(* degenerate: Δ = [], and Γ = Γ' (the context comparison is reflexive) *)
Lemma spine_subst_cumul_inst :
  [× PCUICLiftSubst.assumption_context ti_ΓP, PCUICLiftSubst.assumption_context ti_ΓP,
     wf_localE si_Σ ([] ,,, ti_ΓP), wf_localE si_Σ ([] ,,, ti_ΓP),
     ws_cumul_ctx_pbE_rel Cumul si_Σ [] ti_ΓP ti_ΓP,
     spine_substE si_Σ [] [ti_F] (List.rev [ti_F]) ti_ΓP &
     spine_substE si_Σ [] [ti_F] (List.rev [ti_F]) ti_ΓP].
Proof.
  have ha : PCUICLiftSubst.assumption_context ti_ΓP by repeat constructor.
  have hcb : PCUICConversion.ws_cumul_ctx_pb_rel Cumul si_Σ [] ti_ΓP ti_ΓP.
  { split; [reflexivity|]. constructor; [constructor|].
    constructor; [reflexivity|exact (ti_ws_refl ([] ,,, []) si_P eq_refl eq_refl)]. }
  have hcE : ws_cumul_ctx_pbE_rel Cumul si_Σ [] ti_ΓP ti_ΓP.
  { split; [reflexivity|]. constructor; [constructor|].
    constructor; [reflexivity|exact (fi_ws Cumul ([] ,,, []) si_P eq_refl eq_refl)]. }
  have hs : PCUICSpine.spine_subst si_Σ [] [ti_F] (List.rev [ti_F]) ti_ΓP := ti_spine_F.
  split; [exact ha|exact ha|exact (siW ti_wf_ΓP)|exact (siW ti_wf_ΓP)|exact hcE|exact (siS hs)|].
  exact (siS (PCUICSpine.spine_subst_cumul (Σ := si_Σ) (wfΣ := si_wf) (Δ := []) (Γ := ti_ΓP) (Γ' := ti_ΓP)
                ha ha ti_wf_ΓP ti_wf_ΓP hcb hs)).
Qed.

(* degenerate: Γ = [], and Δ has no let-in, so smash_context is the identity *)
Lemma spine_subst_smash_inst :
  spine_substE si_Σ [] [ti_F] [ti_F] ti_ΓP ×
  spine_substE si_Σ [] [ti_F] (List.rev [ti_F]) (smash_context [] ti_ΓP).
Proof.
  split; [exact (siS ti_spine_F)|].
  exact (siS (PCUICSpine.spine_subst_smash (Σ := si_Σ) (wfΣ := si_wf) ti_spine_F)).
Qed.

(* degenerate: Γ = [], and Δ has no let-in *)
Lemma spine_subst_inst_subst_inst :
  spine_substE si_Σ [] [ti_F] [ti_F] ti_ΓP ×
  subst_context [ti_F] 0 [vass si_na (tRel 0)] =
    subst_context (List.rev [ti_F]) 0 (expand_lets_ctx ti_ΓP [vass si_na (tRel 0)]).
Proof.
  split; [exact (siS ti_spine_F)|].
  exact (PCUICSR.spine_subst_inst_subst (Δ' := [vass si_na (tRel 0)]) ti_spine_F).
Qed.

Lemma ti_Rel0_ty : si_Σ ;;; [] ,,, ti_ΓP ,,, [] |- tRel 0 : si_P.
Proof. exact (type_Rel _ _ 0 (vass si_na si_P) ti_wf_ΓP eq_refl). Qed.

(* degenerate: Γ = [] and Δ = [] *)
Lemma substitution_inst :
  [× subsletE si_Σ [] [ti_F] ti_ΓP, si_Σ ;;; [] ,,, ti_ΓP ,,, [] |-E tRel 0 : si_P &
     si_Σ ;;; [] ,,, subst_context [ti_F] 0 [] |-E subst [ti_F] #|([] : context)| (tRel 0) :
       subst [ti_F] #|([] : context)| si_P].
Proof.
  split; [exact (ti_subslet si_Σ si_wf ti_subslet_F)|exact (siT ti_Rel0_ty)|].
  exact (siT (PCUICSubstitution.substitution (Σ := si_Σ) (wfΣ := si_wf) (Γ := []) (Γ' := ti_ΓP) (s := [ti_F])
                (Δ := []) ti_subslet_F ti_Rel0_ty)).
Qed.

(* degenerate: Γ = [] *)
Lemma substitution_wf_local_inst :
  [× subsletE si_Σ [] [ti_F] ti_ΓP, wf_localE si_Σ ([] ,,, ti_ΓP ,,, [vass si_na (tRel 0)]) &
     wf_localE si_Σ ([] ,,, subst_context [ti_F] 0 [vass si_na (tRel 0)])].
Proof.
  have hw : wf_local si_Σ ([] ,,, ti_ΓP ,,, [vass si_na (tRel 0)]) :=
    ti_wf_cons ti_ΓP si_na (tRel 0) sProp ti_wf_ΓP (type_Rel _ _ 0 (vass si_na si_P) ti_wf_ΓP eq_refl) eq_refl.
  split; [exact (ti_subslet si_Σ si_wf ti_subslet_F)|exact (siW hw)|].
  exact (siW (PCUICSubstitution.substitution_wf_local (Σ := si_Σ) (wfΣ := si_wf) (Γ := []) (Γ' := ti_ΓP)
                (s := [ti_F]) (Δ := [vass si_na (tRel 0)]) ti_subslet_F hw)).
Qed.

(* degenerate: Γ = [], Δ has no let-in (expand_lets is the identity), and T = Prop *)
Lemma typing_expand_lets_inst :
  si_Σ ;;; [] ,,, ti_ΓP |-E tRel 0 : si_P ×
  si_Σ ;;; [] ,,, smash_context [] ti_ΓP |-E expand_lets ti_ΓP (tRel 0) : expand_lets ti_ΓP si_P.
Proof.
  have h : si_Σ ;;; [] ,,, ti_ΓP |- tRel 0 : si_P := ti_Rel0_ty.
  split; [exact (siT h)|].
  exact (siT (PCUICContexts.typing_expand_lets (Σ := si_Σ) (wfΣ := si_wf) [] ti_ΓP (tRel 0) si_P h)).
Qed.

(* degenerate: Γ = [], and ind_type of I already is the it_mkProd_or_LetIn form *)
Lemma typing_spine_ind_type_inv_inst :
  [× declared_inductive si_Σ si_ind si_mdecl si_idecl, wf_localE si_Σ [],
     consistent_instance_ext si_Σ (ind_universes si_mdecl) [],
     typing_spineE si_Σ [] (ind_type si_idecl)@[[]] [ti_F] (tSort sProp) &
     typing_spineE si_Σ []
       (it_mkProd_or_LetIn (ind_params si_mdecl ,,, ind_indices si_idecl) (tSort (ind_sort si_idecl)))@[[]]
       [ti_F] (tSort sProp)].
Proof.
  split; [exact si_declared_inductive|constructor|exact ti_cons|exact (siTS ti_tspine_IF)|].
  exact (siTS (PCUICInductives.typing_spine_ind_type_inv (Σ := si_Σ) (wfΣ := si_wf) si_declared_inductive
                 [] [] [ti_F] (tSort sProp) ti_wf_nil ti_cons ti_tspine_IF)).
Qed.

(* degenerate: T' = T, and Γ = [] *)
Lemma typing_spine_strengthen_inst :
  [× typing_spineE si_Σ [] si_arity [ti_F] (tSort sProp), isTypeE si_Σ [] si_arity,
     si_Σ ;;; [] ⊢E si_arity ≤ si_arity & typing_spineE si_Σ [] si_arity [ti_F] (tSort sProp)].
Proof.
  have hs : PCUICArities.typing_spine si_Σ [] si_arity [ti_F] (tSort sProp) := ti_tspine_IF.
  have hT : isType si_Σ [] si_arity := has_sort_isType _ (ti_arity_ty [] ti_wf_nil).
  have hc : si_Σ ;;; [] ⊢ si_arity ≤ si_arity := ti_ws_refl [] si_arity eq_refl eq_refl.
  split; [exact (siTS hs)|exact (siI hT)|exact (siC hc)|].
  exact (siTS (PCUICSpine.typing_spine_strengthen (Σ := si_Σ) (wfΣ := si_wf) hs si_arity hT hc)).
Qed.

(* degenerate: Γ = [], and the subject t is Prop *)
Lemma typing_wf_sort_inst :
  [× wfE si_Σ, si_Σ ;;; [] |-E si_P : tSort (Sort.super sProp) & wf_sort si_Σ (Sort.super sProp)].
Proof.
  have h := ti_P_ty [] ti_wf_nil.
  split; [exact si_wfE|exact (siT h)|exact (PCUICWfUniverses.typing_wf_sort (Σ := si_Σ) si_wf h)].
Qed.

(* degenerate: Γ = [], and the subject t is Prop *)
Lemma typing_wf_universes_inst :
  [× wfE si_Σ, si_Σ ;;; [] |-E si_P : tSort (Sort.super sProp) &
     wf_universes si_Σ si_P && wf_universes si_Σ (tSort (Sort.super sProp))].
Proof.
  have h := ti_P_ty [] ti_wf_nil.
  split; [exact si_wfE|exact (siT h)|exact (PCUICWfUniverses.typing_wf_universes (Σ := si_Σ) si_wf h)].
Qed.

(* degenerate: Γ = [], and the subject t is Prop *)
Lemma weaken_ctx_inst :
  [× wfE si_Σ.1, wf_localE si_Σ ti_ΓP, si_Σ ;;; [] |-E si_P : tSort (Sort.super sProp) &
     si_Σ ;;; ti_ΓP ,,, [] |-E si_P : tSort (Sort.super sProp)].
Proof.
  have h := ti_P_ty [] ti_wf_nil.
  split; [exact si_wfE|exact (siW ti_wf_ΓP)|exact (siT h)|].
  exact (siT (PCUICWeakeningTyp.weaken_ctx (Σ := si_Σ) ti_ΓP si_wf ti_wf_ΓP h)).
Qed.

(* non-degenerate *)
Lemma weaken_wf_local_inst :
  [× wfE si_Σ.1, wf_localE si_Σ ti_ΓP, wf_localE si_Σ ti_ΓI & wf_localE si_Σ (ti_ΓP ,,, ti_ΓI)].
Proof.
  split; [exact si_wfE|exact (siW ti_wf_ΓP)|exact (siW ti_wf_ΓI)|].
  exact (siW (PCUICWeakeningTyp.weaken_wf_local (Σ := si_Σ) (Δ := ti_ΓI) ti_ΓP si_wf ti_wf_ΓP ti_wf_ΓI)).
Qed.

(* degenerate: Γ = [] *)
Lemma weakening_wf_local_inst :
  [× wf_localE si_Σ ([] ,,, ti_ΓI), wf_localE si_Σ ([] ,,, ti_ΓP) &
     wf_localE si_Σ ([] ,,, ti_ΓP ,,, lift_context #|ti_ΓP| 0 ti_ΓI)].
Proof.
  split; [exact (siW ti_wf_ΓI)|exact (siW ti_wf_ΓP)|].
  exact (siW (PCUICWeakeningTyp.weakening_wf_local (Σ := si_Σ) (wfΣ := si_wf) (Γ := []) (Γ' := ti_ΓI)
                (Γ'' := ti_ΓP) ti_wf_ΓI ti_wf_ΓP)).
Qed.

(* degenerate: Γ = [], A = Prop and B = Prop *)
Lemma welltyped_prod_codomain_inst :
  welltypedE si_Σ [] (tProd si_na si_P (tSort sProp)) × welltypedE si_Σ ([] ,, vass si_na si_P) (tSort sProp).
Proof.
  have h : welltyped si_Σ [] (tProd si_na si_P (tSort sProp)) := iswelltyped (ti_arity_ty [] ti_wf_nil).
  split; [exact (siWT h)|].
  exact (siWT (PCUICFixWitness.welltyped_prod_codomain (Σ := si_Σ) (wfΣ := si_wf) h)).
Qed.

(** A case on [I ti_F]: the predicate [fun (_ : I ti_F) => Prop] and the branch of [c]. *)
Definition ti_ci : case_info := {| ci_ind := si_ind; ci_npar := 1; ci_relevance := Relevant |}.
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

(* degenerate: Γ = [], args = [] (I has no indices), c has no arguments, and the return type is Prop *)
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

(* degenerate: Γ = [] and args = [] *)
Lemma wf_case_predicate_context_inst :
  [× declared_inductive si_Σ ti_ci si_mdecl si_idecl,
     isTypeE si_Σ [] (mkApps (tInd ti_ci (puinst ti_p)) (pparams ti_p ++ [])),
     wf_predicate si_mdecl si_idecl ti_p &
     let predctx := case_predicate_context ti_ci si_mdecl si_idecl ti_p in wf_localE si_Σ ([] ,,, predctx)].
Proof.
  split; [exact si_declared_inductive|exact (siI ti_isT_case)|exact ti_wfpred|].
  cbv zeta. exact (siW ti_wf_predctx).
Qed.

(* degenerate: Γ = [], and Δ has no let-in *)
Lemma wf_local_expand_lets_inst :
  wf_localE si_Σ ([] ,,, ti_ΓP ,,, ti_ΓI) ×
  wf_localE si_Σ ([] ,,, smash_context [] ti_ΓP ,,, expand_lets_ctx ti_ΓP ti_ΓI).
Proof.
  have hw : wf_local si_Σ ([] ,,, ti_ΓP ,,, ti_ΓI) := ti_wf_I ti_ΓP ti_wf_ΓP.
  split; [exact (siW hw)|].
  exact (siW (PCUICInductives.wf_local_expand_lets (Σ := si_Σ) (wfΣ := si_wf) (Γ := []) (Δ := ti_ΓP)
                (Γ' := ti_ΓI) hw)).
Qed.

(* degenerate: the context has no let-in, so smash_context is the identity *)
Lemma wf_local_smash_context_inst :
  wf_localE si_Σ (ti_ΓP ,,, ti_ΓI) × wf_localE si_Σ (smash_context [] (ti_ΓP ,,, ti_ΓI)).
Proof.
  have hw : wf_local si_Σ (ti_ΓP ,,, ti_ΓI) := ti_wf_I ti_ΓP ti_wf_ΓP.
  split; [exact (siW hw)|exact (siW (PCUICContexts.wf_local_smash_context (Σ := si_Σ) (wfΣ := si_wf) hw))].
Qed.

(* degenerate: Δ has no let-in, so smash_context is the identity *)
Lemma wf_local_smash_end_inst :
  wf_localE si_Σ (ti_ΓP ,,, ti_ΓI) × wf_localE si_Σ (ti_ΓP ,,, smash_context [] ti_ΓI).
Proof.
  have hw : wf_local si_Σ (ti_ΓP ,,, ti_ΓI) := ti_wf_I ti_ΓP ti_wf_ΓP.
  split; [exact (siW hw)|].
  exact (siW (PCUICContexts.wf_local_smash_end (Σ := si_Σ) (wfΣ := si_wf) ti_ΓP ti_ΓI hw)).
Qed.

(* degenerate: T = Prop *)
Lemma isType_weaken_inst :
  [× wf_localE si_Σ ti_ΓP, isTypeE si_Σ [] si_P & isTypeE si_Σ ti_ΓP si_P].
Proof.
  have h : isType si_Σ [] si_P := has_sort_isType _ (ti_P_ty [] ti_wf_nil).
  split; [exact (siW ti_wf_ΓP)|exact (siI h)|].
  exact (siI (PCUICArities.isType_weaken (Σ := si_Σ) (wfΣ := si_wf) ti_wf_ΓP h)).
Qed.

(* degenerate: Γ = [], and T = Prop *)
Lemma isType_it_mkProd_or_LetIn_inst :
  [× wfE si_Σ.1, isTypeE si_Σ ([] ,,, ti_ΓP) si_P & isTypeE si_Σ [] (it_mkProd_or_LetIn ti_ΓP si_P)].
Proof.
  have h : isType si_Σ ([] ,,, ti_ΓP) si_P := has_sort_isType _ (ti_P_ty _ ti_wf_ΓP).
  split; [exact si_wfE|exact (siI h)|].
  exact (siI (PCUICInductiveInversion.isType_it_mkProd_or_LetIn (Σ := si_Σ) (Γ := []) (Δ := ti_ΓP) si_wf h)).
Qed.

(* degenerate: Γ = [] *)
Lemma type_local_ctx_wf_inst :
  [× wfE si_Σ.1, type_local_ctx (lift_typing typingE) si_Σ [] ti_ΓF sProp & wf_sort si_Σ sProp].
Proof.
  have hj : lift_typing typing si_Σ [] (j_vass_s si_na ti_F sProp) :=
    ti_vass_s [] si_na ti_F sProp (ti_F_ty [] ti_wf_nil) eq_refl.
  have hb : type_local_ctx (lift_typing typing) si_Σ [] ti_ΓF sProp := (ti_wfs, hj).
  split; [exact si_wfE|exact (ti_wfs, siL hj)|].
  exact (PCUICInductives.type_local_ctx_wf (Σ := si_Σ) si_wf hb).
Qed.

(* degenerate: Γ = [], args = [] (I has no indices), c has no arguments, and the return type is Prop *)
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

(* degenerate: si_env declares no universe level, so l = Set, which is closed for every k *)
Lemma LSet_in_global_bounded_inst :
  [× wfE si_env, LevelSet.In Level.lzero (global_levels si_env) & closedu_level 0 Level.lzero].
Proof.
  have hin : LevelSet.In Level.lzero (global_levels si_env).
  { apply LevelSet.union_spec. right. apply LevelSet.singleton_spec. reflexivity. }
  split; [exact si_wfE|exact hin|].
  exact (PCUICInductiveInversion.LSet_in_global_bounded (Σ := si_env) 0 si_wf hin).
Qed.

(* non-degenerate *)
Lemma closed_red_from_empty_inst :
  [× on_free_vars_ctx xpred0 ti_ΓP, closed fi_beta, PCUICReduction.red si_Σ [] fi_beta fi_P &
     si_Σ ;;; ti_ΓP ⊢ fi_beta ⇝ fi_P].
Proof.
  split; [reflexivity|reflexivity|exact fi_red_beta|].
  exact (PCUICInductives.closed_red_from_empty (Σ := si_Σ) (wfΣ := si_wf) (Γ := ti_ΓP) (M := fi_beta) (N := fi_P)
           eq_refl eq_refl fi_red_beta).
Qed.

(* degenerate: Γ = [], and t is the let-bound variable itself *)
Lemma red_expand_let_inst :
  [× wf_localE si_Σ ([] ,,, [vdef si_na ti_F si_P]),
     on_free_vars (shiftnP #|[] ,,, [vdef si_na ti_F si_P]| (fun _ : nat => false)) (tRel 0) &
     si_Σ ;;; [] ,, vdef si_na ti_F si_P ⊢ tRel 0 ⇝ lift0 1 ((tRel 0) {0 := ti_F})].
Proof.
  have hw : wf_local si_Σ ([] ,,, [vdef si_na ti_F si_P]) := ti_wf_def.
  split; [exact (siW hw)|reflexivity|].
  exact (PCUICSpine.red_expand_let (Σ := si_Σ) (wfΣ := si_wf) (Γ := []) (t := tRel 0) hw eq_refl).
Qed.

(* degenerate: Γ = [], the reduction is reflexive, and ctx has no let-in *)
Lemma red_it_mkProd_or_LetIn_smash_inst :
  [× si_Σ ;;; [] ⊢ it_mkProd_or_LetIn ti_ΓP si_P ⇝ si_arity,
     nth_error (List.rev (smash_context [] ti_ΓP)) 0 = Some (vass si_na si_P) &
     ∑ (ctx' : context) (t' : term) (d : context_decl),
       [× decompose_prod_assum [] si_arity = (ctx', t'),
          nth_error (List.rev (smash_context [] ctx')) 0 = Some d &
          si_Σ ;;; [] ,,, skipn (#|smash_context [] ti_ΓP| - 0) (smash_context [] ti_ΓP) ⊢
            decl_type (vass si_na si_P) ⇝ decl_type d]].
Proof.
  have hr : si_Σ ;;; [] ⊢ it_mkProd_or_LetIn ti_ΓP si_P ⇝ si_arity := ti_cr_refl [] si_arity eq_refl eq_refl.
  split; [exact hr|reflexivity|].
  exact (PCUICInductives.red_it_mkProd_or_LetIn_smash (Σ := si_Σ) (wfΣ := si_wf) [] ti_ΓP si_P si_arity 0
           (vass si_na si_P) hr eq_refl).
Qed.

(** [let x : Prop := ti_F in I x], whose telescope has a let-in. *)
Definition ti_CLet : term := tLetIn si_na ti_F si_P (tApp (tInd si_ind []) (tRel 0)).

(* degenerate: Γ = [], and the reduction C ⇝ C is reflexive *)
Lemma red_mkApps_smash_witness_inst :
  si_Σ ;;; [] ⊢ ti_CLet ⇝ it_mkProd_or_LetIn [vdef si_na ti_F si_P] (mkApps (tInd si_ind []) [tRel 0]) ×
  ∑ l' : list term,
    si_Σ ;;; [] ⊢ ti_CLet ⇝ it_mkProd_or_LetIn (smash_context [] [vdef si_na ti_F si_P]) (mkApps (tInd si_ind []) l').
Proof.
  have hr : si_Σ ;;; [] ⊢ ti_CLet ⇝
              it_mkProd_or_LetIn [vdef si_na ti_F si_P] (mkApps (tInd si_ind []) [tRel 0]) :=
    ti_cr_refl [] ti_CLet eq_refl eq_refl.
  split; [exact hr|].
  exact (PCUICFixWitness.red_mkApps_smash_witness (Σ := si_Σ) (wfΣ := si_wf) hr).
Qed.

(* degenerate: Γ = [], and the reduction of the argument type is reflexive *)
Lemma red_rec_arg_check_one_fix_inst :
  [× on_free_vars (shiftnP #|([] : context)| xpred0) (dtype ti_d),
     decompose_prod_assum [] (dtype ti_d) = (ti_ΓI, si_P),
     nth_error (List.rev (smash_context [] ti_ΓI)) (rarg ti_d) = Some (vass si_na ti_IF),
     si_Σ ;;; [] ,,, skipn (#|smash_context [] ti_ΓI| - rarg ti_d) (smash_context [] ti_ΓI) ⊢
       decl_type (vass si_na ti_IF) ⇝ mkApps (tInd si_ind []) [ti_F] &
     has_rec_arg ti_d ×
     (∑ ty : term, si_Σ ;;; [] ⊢ dtype ti_d ⇝ ty × check_one_fix (def_with_type ti_d ty) = Some (inductive_mind si_ind))].
Proof.
  have hr : si_Σ ;;; [] ,,, skipn (#|smash_context [] ti_ΓI| - rarg ti_d) (smash_context [] ti_ΓI) ⊢
              decl_type (vass si_na ti_IF) ⇝ mkApps (tInd si_ind []) [ti_F] :=
    ti_cr_refl [] ti_IF eq_refl eq_refl.
  split; [reflexivity|reflexivity|reflexivity|exact hr|].
  exact (PCUICInductives.red_rec_arg_check_one_fix (Σ := si_Σ) (wfΣ := si_wf) [] ti_d ti_ΓI si_P
           (vass si_na ti_IF) si_ind [] [ti_F] eq_refl eq_refl eq_refl hr).
Qed.

(* degenerate: univs = Monomorphic_ctx, u = [], and t = Prop *)
Lemma wf_universes_inst_inst :
  [× wfE si_Σ, on_udecl_prop si_Σ.1 Monomorphic_ctx, wf_instance si_Σ [],
     wf_universes (si_Σ.1, Monomorphic_ctx) si_P & wf_universes si_Σ si_P@[[]]].
Proof.
  have hu : on_udecl_prop si_Σ.1 Monomorphic_ctx.
  { intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx. }
  have hi : wf_instance si_Σ [] by constructor.
  have hw : wf_universes (si_Σ.1, Monomorphic_ctx) si_P by reflexivity.
  split; [exact si_wfE|exact hu|exact hi|exact hw|].
  exact (PCUICWfUniverses.wf_universes_inst (Σ := si_Σ) Monomorphic_ctx si_P [] si_wf hu hi hw).
Qed.

(* degenerate: Γ = [], and one of the two reductions is reflexive *)
Lemma closed_red_confluence_inst :
  [× si_Σ ;;; [] ⊢ fi_beta ⇝ fi_P, si_Σ ;;; [] ⊢ fi_beta ⇝ fi_beta &
     ∑ v' : term, si_Σ ;;; [] ⊢ fi_P ⇝ v' × si_Σ ;;; [] ⊢ fi_beta ⇝ v'].
Proof.
  have hv : si_Σ ;;; [] ⊢ fi_beta ⇝ fi_beta := ti_cr_refl [] fi_beta eq_refl eq_refl.
  split; [exact fi_closed_red_beta|exact hv|].
  exact (PCUICContextConversion.closed_red_confluence (Σ := si_Σ) (wfΣ := si_wf) fi_closed_red_beta hv).
Qed.

(* degenerate: Γ = [], and t = t' = Prop *)
Lemma whnf_red_inv_inst :
  [× wfE si_Σ, whnf RedFlags.default si_Σ [] si_P, si_Σ ;;; [] ⊢ si_P ⇝ si_P & whnf_red si_Σ [] si_P si_P].
Proof.
  have hn : whnf RedFlags.default si_Σ [] si_P by apply whnf_sort.
  have hr : si_Σ ;;; [] ⊢ si_P ⇝ si_P := ti_cr_refl [] si_P eq_refl eq_refl.
  split; [exact si_wfE|exact hn|exact hr|].
  exact (PCUICNormal.whnf_red_inv (Σ := si_Σ) [] si_P si_P si_wf hn hr).
Qed.

(** ** Instances of [T1_facts]

  Each lemma [<field>_inst] states the premises and the conclusion of the field [<field>] of [T1_facts] at
  concrete arguments (in [si_Σ], or for the primitive operations in [Σ_po] of [PCUICEtaPrimOpInstance],
  which registers [int]; the premise [wfE] holds by [si_wfE] and [ti_po_wfE]), builds each typed premise
  from a base derivation lifted with [typing_incl_E], and proves the conclusion from the base lemma of the
  same name. (1) This instance shows that the hypothesis is consistent and about something real. (2) It
  does NOT discharge the hypothesis at [typingE]: the field remains a hypothesis until plan row T1 (subject
  reduction over [typingE]) lands. *)

(* degenerate: Γ = [] (the tags [int] and the type int → int are real) *)
Lemma isType_prim_arg_types_inst :
  [× wf_localE Σ_po [], (forall t : prim_tag, In t [primInt] -> t <> primArray),
     All (prim_op_tag_declared Σ_po) [primInt],
     PCUICPrimOpType.prim_arg_types (retroknowledge Σ_po.1) [primInt] (tConst po_int_kn []) =
       Some (tImpl (tConst po_int_kn []) (tConst po_int_kn [])),
     isTypeE Σ_po [] (tConst po_int_kn []) &
     isTypeE Σ_po [] (tImpl (tConst po_int_kn []) (tConst po_int_kn []))].
Proof.
  have hna : forall t : prim_tag, In t [primInt] -> t <> primArray by (intros t [<-|[]]; discriminate).
  have hall : All (prim_op_tag_declared Σ_po) [primInt] := All_cons ti_po_int_tag All_nil.
  have hres : isType Σ_po [] (tConst po_int_kn []) :=
    has_sort_isType _ (po_int_typed Σ_po [] ltac:(constructor) ti_po_int_declared).
  split; [constructor|exact hna|exact hall|reflexivity|exact (ti_isType Σ_po ti_po_wf hres)|].
  exact (ti_isType Σ_po ti_po_wf (PCUICSR.isType_prim_arg_types (Σ := Σ_po) (wfΣ := ti_po_wf) (Γ := [])
           ltac:(constructor) hna hall eq_refl hres)).
Qed.

(* degenerate: Γ = [] *)
Lemma isType_prim_shape_type_inst :
  [× wf_localE Σ_po [],
     PCUICPrimOpType.prim_shape_type (retroknowledge Σ_po.1) SInt = Some (tConst po_int_kn []),
     on_prim_op_result Σ_po SInt & isTypeE Σ_po [] (tConst po_int_kn [])].
Proof.
  have hres : on_prim_op_result Σ_po SInt := ti_po_int_tag.
  split; [constructor|reflexivity|exact hres|].
  exact (ti_isType Σ_po ti_po_wf (PCUICSR.isType_prim_shape_type (Σ := Σ_po) (wfΣ := ti_po_wf) (Γ := [])
           (s := SInt) (res := tConst po_int_kn []) ltac:(constructor) eq_refl hres)).
Qed.

(* degenerate: T = U = Prop (reflexive reduction), and Γ = [] *)
Lemma isType_red_inst :
  [× isTypeE si_Σ [] si_P, PCUICReduction.red si_Σ [] si_P si_P & isTypeE si_Σ [] si_P].
Proof.
  have h : isType si_Σ [] si_P := has_sort_isType _ (ti_P_ty [] ti_wf_nil).
  have hr : PCUICReduction.red si_Σ [] si_P si_P by apply rt_refl.
  split; [exact (siI h)|exact hr|].
  exact (siI (PCUICSR.isType_red (Σ := si_Σ) (wfΣ := si_wf) h hr)).
Qed.

(** [let x : Prop := ti_F in x] reduces (ζ) to [ti_F]. *)
Lemma ti_red_zeta : PCUICReduction.red si_Σ [] (tLetIn si_na ti_F si_P (tRel 0)) ti_F.
Proof. apply rt_step. exact (red_zeta _ _ si_na ti_F si_P (tRel 0)). Qed.

(* degenerate: Γ = [] (the ζ-reduction of let x := ∀ A : Prop. A in x is real) *)
Lemma subject_reduction_inst :
  [× wfE si_Σ, si_Σ ;;; [] |-E tLetIn si_na ti_F si_P (tRel 0) : tLetIn si_na ti_F si_P si_P,
     PCUICReduction.red si_Σ [] (tLetIn si_na ti_F si_P (tRel 0)) ti_F &
     si_Σ ;;; [] |-E ti_F : tLetIn si_na ti_F si_P si_P].
Proof.
  split; [exact si_wfE|exact (siT ti_LetIn_ty)|exact ti_red_zeta|].
  exact (siT (PCUICSR.subject_reduction si_Σ [] _ _ _ si_wf ti_LetIn_ty ti_red_zeta)).
Qed.

(* degenerate: Γ = [] (the ζ-reduction of the type is real) *)
Lemma type_reduction_closed_inst :
  [× si_Σ ;;; [] |-E tLetIn si_na ti_F si_P (tRel 0) : tLetIn si_na ti_F si_P si_P,
     si_Σ ;;; [] ⊢ tLetIn si_na ti_F si_P si_P ⇝ si_P &
     si_Σ ;;; [] |-E tLetIn si_na ti_F si_P (tRel 0) : si_P].
Proof.
  have hr : si_Σ ;;; [] ⊢ tLetIn si_na ti_F si_P si_P ⇝ si_P.
  { split; [reflexivity|reflexivity|]. apply rt_step. exact (red_zeta _ _ si_na ti_F si_P si_P). }
  split; [exact (siT ti_LetIn_ty)|exact hr|].
  exact (siT (PCUICSR.type_reduction_closed (Σ := si_Σ) (wfΣ := si_wf) ti_LetIn_ty hr)).
Qed.

(** ** Instances of [T2a_facts]

  Each lemma [<field>_inst] states the premises and the conclusion of the field [<field>] of [T2a_facts] at
  concrete arguments in [si_Σ] (the premise [wfE] holds there by [si_wfE]), builds each typed premise from
  a base derivation lifted with [typing_incl_E], and proves the conclusion from the base lemma of the same
  name. (1) This instance shows that the hypothesis is consistent and about something real. (2) It does
  NOT discharge the hypothesis at [typingE]: the field remains a hypothesis until plan row T2a (validity
  over [typingE]) lands. *)

(* degenerate: Γ = [] (the application I (∀ A : Prop. A) is real) *)
Lemma inversion_mkApps_inst :
  si_Σ ;;; [] |-E mkApps (tInd si_ind []) [ti_F] : tSort sProp ×
  ∑ A : term, si_Σ ;;; [] |-E tInd si_ind [] : A × typing_spineE si_Σ [] A [ti_F] (tSort sProp).
Proof.
  have h : si_Σ ;;; [] |- mkApps (tInd si_ind []) [ti_F] : tSort sProp := ti_IF_ty [] ti_wf_nil.
  split; [exact (siT h)|].
  destruct (PCUICValidity.inversion_mkApps (Σ := si_Σ) (wfΣ := si_wf) h) as [A [h1 h2]].
  exists A. split; [exact (siT h1)|exact (siTS h2)].
Qed.

(* degenerate: Γ = [], and the subject t is Prop *)
Lemma validity_inst :
  si_Σ ;;; [] |-E si_P : tSort (Sort.super sProp) × isTypeE si_Σ [] (tSort (Sort.super sProp)).
Proof.
  have h := ti_P_ty [] ti_wf_nil.
  split; [exact (siT h)|exact (siI (PCUICValidity.validity (Σ := si_Σ) (wfΣ := si_wf) h))].
Qed.

(** ** Instances of [T6_facts]

  The lemma [typing_spine_smash_inst] states the premises and the conclusion of the field
  [typing_spine_smash] of [T6_facts] at concrete arguments in [si_Σ] (the premise [wfE] holds there by
  [si_wfE]), builds the spine premise from a base spine lifted with [typing_incl_E], and proves the
  conclusion from the base lemma of the same name. (1) This instance shows that the hypothesis is
  consistent and about something real. (2) It does NOT discharge the hypothesis at [typingE]: the field
  remains a hypothesis until plan row T6 (inversion and classification over [typingE]) lands. *)

(* degenerate: Γ = [], and Δ has no let-in, so smash_context and expand_lets are the identity *)
Lemma typing_spine_smash_inst :
  [× wfE si_Σ.1, typing_spineE si_Σ [] (it_mkProd_or_LetIn ti_ΓP (tSort sProp)) [ti_F] (tSort sProp) &
     typing_spineE si_Σ [] (it_mkProd_or_LetIn (smash_context [] ti_ΓP) (expand_lets ti_ΓP (tSort sProp)))
       [ti_F] (tSort sProp)].
Proof.
  have hs : PCUICArities.typing_spine si_Σ [] (it_mkProd_or_LetIn ti_ΓP (tSort sProp)) [ti_F] (tSort sProp) :=
    ti_tspine_IF.
  split; [exact si_wfE|exact (siTS hs)|].
  exact (siTS (PCUICClassification.typing_spine_smash (Σ := si_Σ) si_wf [] ti_ΓP (tSort sProp) [ti_F]
                 (tSort sProp) hs)).
Qed.

(** *** Bidirectional derivations over E in [si_Σ], built with the E constructors *)

Lemma ti_bdP Γ : si_Σ ;;; Γ |-E si_P ▹ tSort (Sort.super sProp).
Proof. apply inferE_Sort. exact ti_wfs. Qed.

Lemma ti_bdsP Γ : si_Σ ;;; Γ |-E si_P ▹□ Sort.super sProp.
Proof. eapply inferE_sort_Sort; [exact (ti_bdP Γ)|apply rt_refl]. Qed.

Lemma ti_bdcP : si_Σ ;;; [] |-E si_P ◃ tSort (Sort.super sProp).
Proof. eapply checkE_Cumul; [exact (ti_bdP [])|exact (fi_ws Cumul [] (tSort (Sort.super sProp)) eq_refl eq_refl)]. Qed.

Lemma ti_lsP Γ : lift_sorting (checkingE si_Σ Γ) (infering_sortE si_Σ Γ) (j_vass si_na si_P).
Proof. split; [exact tt|]. exists (Sort.super sProp). split; [exact (ti_bdsP Γ)|split; [exact I|reflexivity]]. Qed.

Lemma ti_bdF : si_Σ ;;; [] |-E ti_F ▹ tSort (Sort.sort_of_product (Sort.super sProp) sProp).
Proof.
  apply inferE_Prod.
  - split; [exact tt|]. exists (Sort.super sProp). split; [exact (ti_bdsP [])|split; reflexivity].
  - eapply inferE_sort_Sort.
    + econstructor. reflexivity.
    + apply rt_refl.
Qed.

Lemma ti_bdcF : si_Σ ;;; [] |-E ti_F ◃ si_P.
Proof. eapply checkE_Cumul; [exact ti_bdF|exact (fi_ws Cumul [] si_P eq_refl eq_refl)]. Qed.

Lemma ti_bdsF : si_Σ ;;; [] |-E ti_F ▹□ sProp.
Proof. eapply inferE_sort_Sort; [exact ti_bdF|apply rt_refl]. Qed.

Lemma ti_bdInd Γ : si_Σ ;;; Γ |-E tInd si_ind [] ▹ (ind_type si_idecl)@[[]].
Proof. econstructor; [exact si_declared_inductive|exact ti_cons]. Qed.

Lemma ti_bdpInd Γ : si_Σ ;;; Γ |-E tInd si_ind [] ▹Π (si_na, si_P, tSort sProp).
Proof. eapply inferE_prod_Prod; [exact (ti_bdInd Γ)|apply rt_refl]. Qed.

Lemma ti_bdRel : si_Σ ;;; ti_ΓI |-E tRel 0 ▹ lift0 (S 0) (decl_type (vass si_na ti_IF)).
Proof. econstructor. reflexivity. Qed.

Lemma ti_bdiRel : si_Σ ;;; ti_ΓI |-E tRel 0 ▹{si_ind} ([], [ti_F]).
Proof. eapply inferE_ind_Ind; [exact ti_bdRel|apply rt_refl]. Qed.

Lemma ti_bdctx : wf_local_bd_relE si_Σ [] ti_ΓP.
Proof. constructor; [constructor|]. exact (ti_lsP _). Qed.

Lemma ti_relctx : wf_local_relE si_Σ [] ti_ΓP.
Proof. constructor; [constructor|]. exact (siL (ti_vass [] si_na si_P _ (ti_P_ty [] ti_wf_nil) eq_refl)). Qed.

(** In [ti_ΓP = [A : Prop]]: [A], [I A] and [c A]. *)
Lemma ti_bdA : si_Σ ;;; ti_ΓP |-E tRel 0 ▹ lift0 (S 0) (decl_type (vass si_na si_P)).
Proof. econstructor. reflexivity. Qed.

Lemma ti_bdcA : si_Σ ;;; ti_ΓP |-E tRel 0 ◃ si_P.
Proof. eapply checkE_Cumul; [exact ti_bdA|exact (fi_ws Cumul ti_ΓP si_P eq_refl eq_refl)]. Qed.

Lemma ti_bdIA : si_Σ ;;; ti_ΓP |-E ti_IA ▹ tSort sProp.
Proof.
  change (si_Σ ;;; ti_ΓP |-E tApp (tInd si_ind []) (tRel 0) ▹ ((tSort sProp) {0 := tRel 0})).
  eapply inferE_App; [exact (ti_bdpInd ti_ΓP)|exact ti_bdcA].
Qed.

Lemma ti_bdsIA : si_Σ ;;; ti_ΓP |-E ti_IA ▹□ sProp.
Proof. eapply inferE_sort_Sort; [exact ti_bdIA|apply rt_refl]. Qed.

Lemma ti_bdcIA : si_Σ ;;; ti_ΓP |-E ti_IA ◃ si_P.
Proof. eapply checkE_Cumul; [exact ti_bdIA|exact (fi_ws Cumul ti_ΓP si_P eq_refl eq_refl)]. Qed.

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
Proof. eapply checkE_Cumul; [exact ti_bdcAi|exact (fi_ws Cumul ti_ΓP ti_IA eq_refl eq_refl)]. Qed.

(** ** Instances of [T6BD_facts]

  Each lemma [<field>_inst] states the premises and the conclusion of the field [<field>] of [T6BD_facts]
  at concrete arguments in [si_Σ] (the premise [wfE] holds there by [si_wfE]); the bidirectional premises
  are built with the constructors of [PCUICTypingEtaDefs], and the conclusion from base derivations lifted
  with [typing_incl_E]. (1) This instance shows that the hypothesis is consistent and about something
  real. (2) It does NOT discharge the hypothesis at [typingE]: the field remains a hypothesis until plan
  row T6 (bidirectional soundness over E) lands. *)

(* degenerate: Γ = [], and the subject t is Prop *)
Lemma checking_typing_inst :
  [× wfE si_Σ, wf_localE si_Σ [], isTypeE si_Σ [] (tSort (Sort.super sProp)),
     si_Σ ;;; [] |-E si_P ◃ tSort (Sort.super sProp) & si_Σ ;;; [] |-E si_P : tSort (Sort.super sProp)].
Proof.
  split; [exact si_wfE|constructor|exact (siI (has_sort_isType _ (ti_P1_ty [] ti_wf_nil)))|exact ti_bdcP|].
  exact (siT (ti_P_ty [] ti_wf_nil)).
Qed.

(* degenerate: Γ = [] *)
Lemma ctx_inst_bd_typing_inst :
  [× wfE si_Σ, wf_localE si_Σ ([] ,,, ti_ΓP),
     PCUICTyping.ctx_inst (checkingE si_Σ) [] [ti_F] (List.rev ti_ΓP) &
     ctx_instE si_Σ [] [ti_F] (List.rev ti_ΓP)].
Proof.
  have hc : PCUICTyping.ctx_inst (checkingE si_Σ) [] [ti_F] (List.rev ti_ΓP).
  { cbn. econstructor; [exact ti_bdcF|cbn; constructor]. }
  split; [exact si_wfE|exact (siW ti_wf_ΓP)|exact hc|].
  exact (siCI (PCUICSpine.spine_subst_ctx_inst ti_spine_F)).
Qed.

(* non-degenerate *)
Lemma infering_ind_typing_inst :
  [× wfE si_Σ, wf_localE si_Σ ti_ΓI, si_Σ ;;; ti_ΓI |-E tRel 0 ▹{si_ind} ([], [ti_F]) &
     si_Σ ;;; ti_ΓI |-E tRel 0 : mkApps (tInd si_ind []) [ti_F]].
Proof.
  split; [exact si_wfE|exact (siW ti_wf_ΓI)|exact ti_bdiRel|].
  exact (siT (type_Rel _ _ 0 (vass si_na ti_IF) ti_wf_ΓI eq_refl)).
Qed.

(* degenerate: Γ = [] *)
Lemma infering_prod_typing_inst :
  [× wfE si_Σ, wf_localE si_Σ [], si_Σ ;;; [] |-E tInd si_ind [] ▹Π (si_na, si_P, tSort sProp) &
     si_Σ ;;; [] |-E tInd si_ind [] : tProd si_na si_P (tSort sProp)].
Proof. split; [exact si_wfE|constructor|exact (ti_bdpInd [])|exact (siT (ti_Ind_ty [] ti_wf_nil))]. Qed.

(* degenerate: Γ = [], and the subject t is Prop *)
Lemma infering_sort_isTypeRel_inst :
  [× wfE si_Σ, wf_localE si_Σ [], si_Σ ;;; [] |-E si_P ▹□ Sort.super sProp &
     isTypeRelE si_Σ [] si_P (relevance_of_sort (Sort.super sProp))].
Proof.
  split; [exact si_wfE|constructor|exact (ti_bdsP [])|].
  exact (siIR (has_sort_isTypeRel (Sort.super sProp) _ eq_refl (ti_P_ty [] ti_wf_nil))).
Qed.

(* degenerate: Γ = [], and the subject t is Prop *)
Lemma infering_sort_typing_inst :
  [× wfE si_Σ, wf_localE si_Σ [], si_Σ ;;; [] |-E si_P ▹□ Sort.super sProp &
     si_Σ ;;; [] |-E si_P : tSort (Sort.super sProp)].
Proof. split; [exact si_wfE|constructor|exact (ti_bdsP [])|exact (siT (ti_P_ty [] ti_wf_nil))]. Qed.

(* degenerate: Γ = [], and the subject t is Prop *)
Lemma infering_typing_inst :
  [× wfE si_Σ, wf_localE si_Σ [], si_Σ ;;; [] |-E si_P ▹ tSort (Sort.super sProp) &
     si_Σ ;;; [] |-E si_P : tSort (Sort.super sProp)].
Proof. split; [exact si_wfE|constructor|exact (ti_bdP [])|exact (siT (ti_P_ty [] ti_wf_nil))]. Qed.

(* degenerate: Γ = [], and the subject is Prop *)
Lemma lift_sorting_lift_typing_inst :
  [× wfE si_Σ, wf_localE si_Σ [], lift_sorting (checkingE si_Σ []) (infering_sortE si_Σ []) (j_vass si_na si_P) &
     lift_typing typingE si_Σ [] (j_vass si_na si_P)].
Proof.
  split; [exact si_wfE|constructor|exact (ti_lsP [])|].
  exact (siL (ti_vass [] si_na si_P _ (ti_P_ty [] ti_wf_nil) eq_refl)).
Qed.

(* degenerate: Γ = [] *)
Lemma wf_local_bd_rel_typing_inst :
  [× wfE si_Σ, wf_localE si_Σ [], wf_local_bd_relE si_Σ [] ti_ΓP & wf_local_relE si_Σ [] ti_ΓP].
Proof. split; [exact si_wfE|constructor|exact ti_bdctx|exact ti_relctx]. Qed.

(* non-degenerate *)
Lemma wf_rel_weak_inst :
  [× wfE si_Σ, wf_localE si_Σ ti_ΓP, wf_localE si_Σ ti_ΓI & wf_local_relE si_Σ ti_ΓP ti_ΓI].
Proof.
  split; [exact si_wfE|exact (siW ti_wf_ΓP)|exact (siW ti_wf_ΓI)|].
  constructor; [constructor|].
  exact (siL (ti_vass ti_ΓP si_na ti_IF sProp (ti_IF_ty ti_ΓP ti_wf_ΓP) eq_refl)).
Qed.

(** ** Instances of [T6BDu_facts]

  Each lemma [<field>_inst] states the premises and the conclusion of the field [<field>] of [T6BDu_facts]
  at concrete arguments in [si_Σ] (the premise [wfE] holds there by [si_wfE]); the bidirectional premises
  are built with the constructors of [PCUICTypingEtaDefs], and the conclusion (reductions to a common
  reduct, which are base [closed_red]) directly. (1) This instance shows that the hypothesis is consistent
  and about something real. (2) It does NOT discharge the hypothesis at [typingE]: the field remains a
  hypothesis until plan row T6 (bidirectional uniqueness over E) lands. *)

(* degenerate: Γ = [], the subject t is Prop, and T = T' *)
Lemma infering_checking_inst :
  [× wfE si_Σ, wf_localE si_Σ [], on_free_vars (shiftnP #|([] : context)| xpred0) (tSort (Sort.super sProp)),
     si_Σ ;;; [] |-E si_P ▹ tSort (Sort.super sProp), si_Σ ;;; [] |-E si_P ◃ tSort (Sort.super sProp) &
     si_Σ ;;; [] ⊢E tSort (Sort.super sProp) ≤ tSort (Sort.super sProp)].
Proof.
  split; [exact si_wfE|constructor|reflexivity|exact (ti_bdP [])|exact ti_bdcP|].
  exact (fi_ws Cumul [] (tSort (Sort.super sProp)) eq_refl eq_refl).
Qed.

(* degenerate: the two inferences are the same derivation (ind = ind', args = args'), and the reductions are reflexive *)
Lemma infering_ind_ind_inst :
  [× wfE si_Σ, wf_localE si_Σ ti_ΓI, si_Σ ;;; ti_ΓI |-E tRel 0 ▹{si_ind} ([], [ti_F]),
     si_Σ ;;; ti_ΓI |-E tRel 0 ▹{si_ind} ([], [ti_F]) &
     ∑ args'' : list term, [× si_ind = si_ind, ([] : Instance.t) = [], red_terms si_Σ ti_ΓI [ti_F] args'' &
                               red_terms si_Σ ti_ΓI [ti_F] args'']].
Proof.
  have hr : red_terms si_Σ ti_ΓI [ti_F] [ti_F] := All2_cons (ti_cr_refl ti_ΓI ti_F eq_refl eq_refl) All2_nil.
  split; [exact si_wfE|exact (siW ti_wf_ΓI)|exact ti_bdiRel|exact ti_bdiRel|].
  exists [ti_F]. split; [reflexivity|reflexivity|exact hr|exact hr].
Qed.

(* degenerate: the reductions are reflexive *)
Lemma infering_ind_infering_inst :
  [× wfE si_Σ, wf_localE si_Σ ti_ΓI, si_Σ ;;; ti_ΓI |-E tRel 0 ▹{si_ind} ([], [ti_F]),
     si_Σ ;;; ti_ΓI |-E tRel 0 ▹ lift0 (S 0) (decl_type (vass si_na ti_IF)) &
     ∑ args' : list term, si_Σ ;;; ti_ΓI ⊢ lift0 (S 0) (decl_type (vass si_na ti_IF)) ⇝ mkApps (tInd si_ind []) args' ×
       red_terms si_Σ ti_ΓI [ti_F] args'].
Proof.
  have hr : red_terms si_Σ ti_ΓI [ti_F] [ti_F] := All2_cons (ti_cr_refl ti_ΓI ti_F eq_refl eq_refl) All2_nil.
  split; [exact si_wfE|exact (siW ti_wf_ΓI)|exact ti_bdiRel|exact ti_bdRel|].
  exists [ti_F]. split; [exact (ti_cr_refl ti_ΓI ti_IF eq_refl eq_refl)|exact hr].
Qed.

(* degenerate: Γ = [], and the reductions are reflexive *)
Lemma infering_prod_infering_inst :
  [× wfE si_Σ, wf_localE si_Σ [], si_Σ ;;; [] |-E tInd si_ind [] ▹Π (si_na, si_P, tSort sProp),
     si_Σ ;;; [] |-E tInd si_ind [] ▹ (ind_type si_idecl)@[[]] &
     ∑ A' B' : term, [× si_Σ ;;; [] ⊢ (ind_type si_idecl)@[[]] ⇝ tProd si_na A' B', si_Σ ;;; [] ⊢ si_P ⇝ A' &
                        si_Σ ;;; [] ,, vass si_na si_P ⊢ tSort sProp ⇝ B']].
Proof.
  split; [exact si_wfE|constructor|exact (ti_bdpInd [])|exact (ti_bdInd [])|].
  exists si_P, (tSort sProp).
  split; [exact (ti_cr_refl [] si_arity eq_refl eq_refl)|exact (ti_cr_refl [] si_P eq_refl eq_refl)
         |exact (ti_cr_refl ti_ΓP (tSort sProp) eq_refl eq_refl)].
Qed.

(* degenerate: Γ = [], the two inferences are the same derivation, and the reductions are reflexive *)
Lemma infering_prod_prod_inst :
  [× wfE si_Σ, wf_localE si_Σ [], si_Σ ;;; [] |-E tInd si_ind [] ▹Π (si_na, si_P, tSort sProp),
     si_Σ ;;; [] |-E tInd si_ind [] ▹Π (si_na, si_P, tSort sProp) &
     ∑ A'' B'' : term, [× si_na = si_na, si_Σ ;;; [] ⊢ si_P ⇝ A'', si_Σ ;;; [] ⊢ si_P ⇝ A'',
                          si_Σ ;;; [] ,, vass si_na si_P ⊢ tSort sProp ⇝ B'' &
                          si_Σ ;;; [] ,, vass si_na si_P ⊢ tSort sProp ⇝ B'']].
Proof.
  have hA := ti_cr_refl [] si_P eq_refl eq_refl.
  have hB := ti_cr_refl ti_ΓP (tSort sProp) eq_refl eq_refl.
  split; [exact si_wfE|constructor|exact (ti_bdpInd [])|exact (ti_bdpInd [])|].
  exists si_P, (tSort sProp). split; [reflexivity|exact hA|exact hA|exact hB|exact hB].
Qed.

(* degenerate: Γ = [], and the subject t is Prop *)
Lemma infering_sort_infering_inst :
  [× wfE si_Σ, wf_localE si_Σ [], si_Σ ;;; [] |-E si_P ▹□ Sort.super sProp,
     si_Σ ;;; [] |-E si_P ▹ tSort (Sort.super sProp) &
     si_Σ ;;; [] ⊢ tSort (Sort.super sProp) ⇝ tSort (Sort.super sProp)].
Proof.
  split; [exact si_wfE|constructor|exact (ti_bdsP [])|exact (ti_bdP [])|].
  exact (ti_cr_refl [] (tSort (Sort.super sProp)) eq_refl eq_refl).
Qed.

(* degenerate: Γ = [], the subject t is Prop, and u = u' *)
Lemma infering_sort_sort_inst :
  [× wfE si_Σ, wf_localE si_Σ [], si_Σ ;;; [] |-E si_P ▹□ Sort.super sProp,
     si_Σ ;;; [] |-E si_P ▹□ Sort.super sProp & Sort.super sProp = Sort.super sProp].
Proof. split; [exact si_wfE|constructor|exact (ti_bdsP [])|exact (ti_bdsP [])|reflexivity]. Qed.

(* degenerate: Γ = [], the subject t is Prop, and T = T' *)
Lemma infering_unique_inst :
  [× wfE si_Σ, wf_localE si_Σ [], si_Σ ;;; [] |-E si_P ▹ tSort (Sort.super sProp),
     si_Σ ;;; [] |-E si_P ▹ tSort (Sort.super sProp) &
     ∑ T'' : term, si_Σ ;;; [] ⊢ tSort (Sort.super sProp) ⇝ T'' × si_Σ ;;; [] ⊢ tSort (Sort.super sProp) ⇝ T''].
Proof.
  have h := ti_cr_refl [] (tSort (Sort.super sProp)) eq_refl eq_refl.
  split; [exact si_wfE|constructor|exact (ti_bdP [])|exact (ti_bdP [])|].
  exists (tSort (Sort.super sProp)). split; [exact h|exact h].
Qed.

(* degenerate: Γ = [], T = Prop, and rel = rel' *)
Lemma isTypeRel_unique_inst :
  [× wfE si_Σ, isTypeRelE si_Σ [] si_P Relevant, isTypeRelE si_Σ [] si_P Relevant & Relevant = Relevant].
Proof.
  have h := siIR (has_sort_isTypeRel (Sort.super sProp) Relevant eq_refl (ti_P_ty [] ti_wf_nil)).
  split; [exact si_wfE|exact h|exact h|reflexivity].
Qed.

(** ** Instances of [T6BDc_facts]

  Each lemma [<field>_inst] states the premises and the conclusion of the field [<field>] of [T6BDc_facts]
  at concrete arguments in [si_Σ] (the premise [wfE] holds there by [si_wfE]), in the non-empty context
  [ti_ΓP = [A : Prop]] and on the terms [I A] and [c A]: applications whose head has a Π type, so that each
  inferred type goes through an [infering_prodE] step (the type of the head reduces to a [tProd]). The
  typing premises are base derivations lifted with [typing_incl_E], and the bidirectional conclusions are
  built with the constructors of [PCUICTypingEtaDefs]. (1) This instance shows that the hypothesis is
  consistent and about something real. (2) It does NOT discharge the hypothesis at [typingE]: the field
  remains a hypothesis until plan row T6 (bidirectional completeness over E) lands, and its E proof also
  needs T8 (a well-typed type E-convertible to a Π, a sort or an inductive reduces to one). *)

(* non-degenerate *)
Lemma ctx_inst_typing_bd_inst :
  [× wfE si_Σ, ctx_instE si_Σ ti_ΓP [ti_IA; ti_cA] ti_Δ2 &
     PCUICTyping.ctx_inst (checkingE si_Σ) ti_ΓP [ti_IA; ti_cA] ti_Δ2].
Proof.
  have hc : PCUICTyping.ctx_inst (checkingE si_Σ) ti_ΓP [ti_IA; ti_cA] ti_Δ2.
  { econstructor; [exact ti_bdcIA|].
    change (PCUICTyping.ctx_inst (checkingE si_Σ) ti_ΓP [ti_cA] [vass si_na ti_IA]).
    econstructor; [exact ti_bdccA|]. cbn. constructor. }
  split; [exact si_wfE|exact (siCI ti_ci2B)|exact hc].
Qed.

(* non-degenerate *)
Lemma lift_typing_lift_sorting_inst :
  [× wfE si_Σ, lift_typing typingE si_Σ ti_ΓP (Judge (Some ti_cA) ti_IA None (Some Relevant)) &
     lift_sorting (checkingE si_Σ ti_ΓP) (infering_sortE si_Σ ti_ΓP) (Judge (Some ti_cA) ti_IA None (Some Relevant))].
Proof.
  have hb : lift_typing typing si_Σ ti_ΓP (Judge (Some ti_cA) ti_IA None (Some Relevant)).
  { split; [exact ti_cA_ty|]. exists sProp. split; [exact ti_IA_ty|split; [exact I|reflexivity]]. }
  split; [exact si_wfE|exact (siL hb)|].
  split; [exact ti_bdccA|]. exists sProp. split; [exact ti_bdsIA|split; [exact I|reflexivity]].
Qed.

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
Proof.
  split; [exact si_wfE| |].
  - constructor; [constructor|]. exact (siL (ti_vass ti_ΓP si_na ti_IA sProp ti_IA_ty eq_refl)).
  - constructor; [constructor|]. split; [exact tt|].
    exists sProp. split; [exact ti_bdsIA|split; [exact I|reflexivity]].
Qed.

(** ** Instances of [A_facts]

  The lemma [ws_cumul_ctx_pb_rel_app_inst] states both sides of the field [ws_cumul_ctx_pb_rel_app] of
  [A_facts] and their equivalence at concrete arguments in [si_Σ] (the premise [wfE] holds there by
  [si_wfE]), each side built from [ws_cumul_pbE_refl]. (1) This instance shows that the hypothesis is
  consistent and about something real. (2) It does NOT discharge the hypothesis at [ws_cumul_pbE]: the
  field remains a hypothesis until its row (typed context conversion over [ws_cumul_pbE]) lands. *)

(* degenerate: Γ = [], and Δ = Δ' (the comparison is reflexive) *)
Lemma ws_cumul_ctx_pb_rel_app_inst :
  [× ws_cumul_ctx_pbE_rel Cumul si_Σ [] ti_ΓP ti_ΓP,
     ws_cumul_ctx_pbE Cumul si_Σ ([] ,,, ti_ΓP) ([] ,,, ti_ΓP) &
     ws_cumul_ctx_pbE_rel Cumul si_Σ [] ti_ΓP ti_ΓP <~> ws_cumul_ctx_pbE Cumul si_Σ ([] ,,, ti_ΓP) ([] ,,, ti_ΓP)].
Proof.
  have hl : ws_cumul_ctx_pbE_rel Cumul si_Σ [] ti_ΓP ti_ΓP.
  { split; [reflexivity|]. constructor; [constructor|].
    constructor; [reflexivity|exact (fi_ws Cumul ([] ,,, []) si_P eq_refl eq_refl)]. }
  have hr : ws_cumul_ctx_pbE Cumul si_Σ ([] ,,, ti_ΓP) ([] ,,, ti_ΓP).
  { constructor; [constructor|]. constructor; [reflexivity|exact (fi_ws Cumul [] si_P eq_refl eq_refl)]. }
  split; [exact hl|exact hr|split; intros _; [exact hr|exact hl]].
Qed.
