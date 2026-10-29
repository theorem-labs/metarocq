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
From MetaRocq.PCUIC Require PCUICInductives.
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
    A copy takes them as SQUASHED section premises ([Context (hT0 : ∥ T0_facts ∥)] …): Prop, so extraction
    erases them. When a row lands, its class gets an instance and the premise goes.
  - Facts that follow from what base already proves over E ([PCUICClosedTypEta], [PCUICTypingEtaInd],
    [PCUICEtaA6], [PCUICWsCumulEtaSubst], [PCUICWellScopedCumulativityEta]) or from the class fields are
    PROVED below the classes, under the base name ("Derived").
  - Instances. No field has a concrete satisfying instance yet; the vacuity pass is NOT passed. (The
    commit that lands the instances will state exactly which fields have one.) An instance will be a
    point of the field on the environment [si_Σ] of [PCUICCumulativitySpecEtaClosureInstances]
    (convention of [PCUICEtaFracInstances]); it shows only that the field's premises can hold at a real
    environment, and does NOT discharge the field at [typingE]: subject reduction over [typingE] (row T1),
    validity (T2a), the inversions and the bidirectional facts (T6, whose completeness part T6BDc is as
    strong as typed T8) and the infrastructure copies (T0) remain hypotheses until their rows land.

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
  mfix_body_on_red_unique :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {check : def term -> option kername} {shape : ShapeCheck check} {Γ : context} {d : def term} {m1 : kername} {m2 : kername}, on_def_type (lift_typing1 (typingE Σ)) Γ d -> mfix_body_on check (PCUICReduction.red Σ Γ) m1 d -> mfix_body_on check (PCUICReduction.red Σ Γ) m2 d -> m1 = m2 ;
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
  type_ws_cumul_pb :
    forall {Σ : global_env_ext} {pb : conv_pb} {Γ : context} {t : term} (T : term) {U : term}, Σ;;; Γ |-E t : T -> isTypeE Σ Γ U -> Σ ;;; Γ ⊢E T ≤[pb] U -> Σ;;; Γ |-E t : U ;
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
  type_Cumul_alt :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ : context) (t : term) (T : term) (T' : term), Σ;;; Γ |-E t : T -> isTypeE Σ Γ T' -> JoinE Σ Γ Cumul T T' -> Σ;;; Γ |-E t : T' ;
  type_reduction_closed :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t : term} {A : term} {B : term}, Σ;;; Γ |-E t : A -> Σ ;;; Γ ⊢ A ⇝ B -> Σ;;; Γ |-E t : B
}.

(** ** T2a (validity over [typingE], PCUICValidity) *)
Class T2a_facts {cf : checker_flags} := {
  inversion_mkApps :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ.1} {Γ : context} {f : term} {u : list term} {T : term}, Σ;;; Γ |-E mkApps f u : T -> ∑ A : term, Σ;;; Γ |-E f : A × typing_spineE Σ Γ A u T ;
  isType_Sort_inv :
    forall {Σ : global_env_ext} {Γ : context} {s : sort}, wfE Σ -> isTypeE Σ Γ (tSort s) -> wf_sort Σ s ;
  validity :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t : term} {T : term}, Σ;;; Γ |-E t : T -> isTypeE Σ Γ T
}.

(** ** T6 (inversion and classification over [typingE], PCUICInversion, PCUICClassification) *)
Class T6_facts {cf : checker_flags} := {
  inversion_Const :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ) {Γ : context} {c : kername} {u : Instance.t} {T : term}, Σ;;; Γ |-E tConst c u : T -> ∑ decl : constant_body, wf_localE Σ Γ × declared_constant Σ c decl × consistent_instance_ext Σ (cst_universes decl) u × Σ ;;; Γ ⊢E (cst_type decl)@[u] ≤ T ;
  inversion_LetIn :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ) {Γ : context} {na : aname} {b : term} {B : term} {t : term} {T : term}, Σ;;; Γ |-E tLetIn na b B t : T -> ∑ A : term, lift_typing typingE Σ Γ (j_vdef na b B) × Σ;;; Γ,, vdef na b B |-E t : A × Σ ;;; Γ ⊢E tLetIn na b B A ≤ T ;
  inversion_Prod :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ) {Γ : context} {na : aname} {A : term} {B : term} {T : term}, Σ;;; Γ |-E tProd na A B : T -> ∑ s1 s2 : sort, lift_typing typingE Σ Γ (j_vass_s na A s1) × Σ;;; Γ,, vass na A |-E B : tSort s2 × Σ ;;; Γ ⊢E tSort (Sort.sort_of_product s1 s2) ≤ T ;
  inversion_Rel :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ) {Γ : context} {n : nat} {T : term}, Σ;;; Γ |-E tRel n : T -> ∑ decl : context_decl, wf_localE Σ Γ × nth_error Γ n = Some decl × Σ ;;; Γ ⊢E lift0 (S n) (decl_type decl) ≤ T ;
  inversion_Sort :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ) {Γ : context} {s : sort} {T : term}, Σ;;; Γ |-E tSort s : T -> wf_localE Σ Γ × wf_sort Σ s × Σ ;;; Γ ⊢E tSort (Sort.super s) ≤ T ;
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

(** ** A (typed context conversion over [ws_cumul_pbE]) *)
Class A_facts {cf : checker_flags} := {
  ws_cumul_ctx_pb_rel_app :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {pb : conv_pb} {Γ : list context_decl} {Δ : list context_decl} {Δ' : list context_decl}, ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ' <~> ws_cumul_ctx_pbE pb Σ (Γ,,, Δ) (Γ,,, Δ')
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
