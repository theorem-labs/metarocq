(* Distributed under the terms of the MIT license. *)
(* The header is [PCUICTypingEtaHyps]'s ([PCUICTypingEtaHyps.v:2-24]), then the two files whose classes
   this file discharges, so that every field statement below is read in the context its class reads it. *)
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
From MetaRocq.PCUIC Require Import PCUICWsCumulEtaCtx.
From MetaRocq.PCUIC Require PCUICInductives PCUICSubstitution.
From Stdlib Require Import Program.Equality.
From MetaRocq.PCUIC Require Import PCUICTactics PCUICRenameDef PCUICEtaA6Ind PCUICEtaA6More PCUICGlobalEnvEta
     PCUICWeakeningTypEta PCUICRenameTypEta PCUICInstDefEta PCUICInstTypEta PCUICCasesWfTypEta PCUICGuardClosureEta
     PCUICInversionEta PCUICSREtaConv.
From MetaRocq.PCUIC Require PCUICSR PCUICInduction PCUICPositionEta PCUICInstConv PCUICContexts PCUICWeakeningConv.
From MetaRocq.SafeChecker Require Import PCUICTypingEtaDefs.
From MetaRocq.SafeChecker Require Import PCUICTypingEtaHyps PCUICEtaFactsCompose.
(* The proved E lemmas the fields are wired to: Required, never Imported, and named qualified (same-name
   rule C6). Their global hints take effect here on Require; the proofs below are [exact] terms, which use
   no proof search. *)
From MetaRocq.PCUIC Require PCUICValidityEta PCUICInductivesEta PCUICInductiveInversionEta PCUICAritiesEta
  PCUICInductiveInversionEtaB.
From MetaRocq.PCUIC.Typing Require PCUICContextConversionTypEta.
From MetaRocq.PCUIC Require PCUICPositionEtaTyping.
From MetaRocq.SafeChecker Require PCUICEtaWhnfRedInv PCUICEtaPrimOverapplied PCUICEtaWelltypedContext.

(** * ETAK discharge: the class fields of the η checker's root that are PROVED now

  BET-64 EtaCheckerLane, worker EtaTranscribe6, 2026-10-30. Rows of [lanes/eta/etak/eta51-sizing.md]
  (record: [lanes/eta/etak/discharge-transcriptions.md]). For each field below, a lemma [<field>_proved]
  whose statement is the field's text, copied verbatim from its class ([PCUICTypingEtaHyps.v],
  [PCUICEtaFactsCompose.v] @ [5eaad3d2]; the η stack names of [PCUICEtaFactsCompose] are written
  qualified, [PCUICPositionEta.*], because this file's header imports base [PCUICPosition]), proved by
  the E lemma named in its comment. The [_fits] definitions at the end check the COMPILED identity both
  ways ([<field>_fits]: the proved lemma at the field's projected type; [<field>_fits_rev]: the field at
  the proved lemma's type). Where a whole class is proved, an [Instance] of it ([<class>_discharged]) is
  built from the [_proved] lemmas; record construction checks every field at its declared type once more.
  - WIRING, rows proved on the K7 line (probe A of Eta51Sizing): T0 rows 1-3, 5-9, T2a rows 18-19, and
    row 52, EtaPosK4's section hypothesis [closed_context_conversionE] ([PCUICPositionEtaTyping], with its
    squashed form, the section hypothesis of [PCUICSafeConversionEta]).
  - WIRING, rows proved by copy 18b ([PCUICInductiveInversionEtaB], frac/eta 3e6b422d; probe C of
    Eta51Sizing): T0 rows 4, 10-12, and [ReduceTypedFactsCoreE] rows 45-46 (two-line wrappers).
  - TRANSCRIPTION: row 13, [U_facts.whnf_red_inv] ([PCUICEtaWhnfRedInv]); row 47,
    [ReduceTypedFactsCoreE.rtfc_prim_overapplied] ([PCUICEtaPrimOverapplied]); row 51,
    [WelltypedEContextE.welltypedE_context] ([PCUICEtaWelltypedContext]).
  - Classes proved whole: [T0_facts] (12 fields), [U_facts] (1), [T2a_facts] (2), [WelltypedEContextE] (1).
    [ReduceTypedFactsCoreE] is not: its rows 48-50 ([rtfc_fix_arg_whne], [rtfc_case_arg_whne],
    [rtfc_proj_arg_whne]) need E lemmas this tree does not have (the record names them).
  - The two section hypotheses of EtaPosK4 ([PCUICPositionEtaTyping], section [EtaTypingE]) have no
    constant; the [_fits_EtaTypingE] definitions apply a lemma of that section to the [_proved] lemma.
  No root binder is removed here: no existing file imports this one, and no statement elsewhere changes.
  No hypothesis (no [Context], no class field). *)

(** ** [T0_facts]: the eight fields proved on the K7 line, the four proved by copy 18b, and the class *)

(** Row 1: [PCUICContextConversionTypEta.closed_context_cumulativityE] (copy 9). *)
Lemma closed_context_cumulativity_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ.1} (Γ : context) {pb : conv_pb} {t : term} {T : term} {Γ' : context}, Σ;;; Γ |-E t : T -> wf_localE Σ Γ' -> ws_cumul_ctx_pbE pb Σ Γ' Γ -> Σ;;; Γ' |-E t : T.
Proof. exact (@PCUICContextConversionTypEta.closed_context_cumulativityE cf). Qed.

(** Row 2: [PCUICInductiveInversionEta.inductive_cumulative_indicesE] (copy 18a). *)
Lemma inductive_cumulative_indices_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {ind : inductive} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {u : Instance.t} {u' : Instance.t} {napp : nat}, declared_inductive Σ ind mdecl idecl -> consistent_instance_ext Σ (ind_universes mdecl) u -> consistent_instance_ext Σ (ind_universes mdecl) u' -> PCUICEquality.cmp_ind_universes Σ ind napp u u' -> forall (Γ : context) (pars : list term) (pars' : list term) (parsubst : list term) (parsubst' : list term), spine_substE Σ Γ pars parsubst (ind_params mdecl)@[u] -> spine_substE Σ Γ pars' parsubst' (ind_params mdecl)@[u'] -> ws_cumul_pbE_terms Σ Γ pars pars' -> let indctx := (ind_indices idecl)@[u] in let indctx' := (ind_indices idecl)@[u'] in let pindctx := subst_context parsubst 0 indctx in let pindctx' := subst_context parsubst' 0 indctx' in ws_cumul_ctx_pbE_rel Cumul Σ Γ (smash_context [] pindctx) (smash_context [] pindctx').
Proof. exact (@PCUICInductiveInversionEta.inductive_cumulative_indicesE cf). Qed.

(** Row 3: [PCUICInductivesEta.invert_type_mkApps_indE] (copy 16). *)
Lemma invert_type_mkApps_ind_proved {cf : checker_flags} :
    forall (Σ : global_env_ext) (Γ : context) (ind : inductive) (u : Instance.t) (args : list term) (T : term) (mdecl : mutual_inductive_body) (idecl : one_inductive_body), wfE Σ.1 -> declared_inductive Σ.1 ind mdecl idecl -> Σ;;; Γ |-E mkApps (tInd ind u) args : T -> typing_spineE Σ Γ (ind_type idecl)@[u] args T × consistent_instance_ext Σ (ind_universes mdecl) u.
Proof. exact (@PCUICInductivesEta.invert_type_mkApps_indE cf). Qed.

(** Row 5: [PCUICInductivesEta.isType_mkApps_IndE] (copy 16). *)
Lemma isType_mkApps_Ind_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {mdecl : mutual_inductive_body} {ind : inductive} {idecl : one_inductive_body} (decli : declared_inductive Σ ind mdecl idecl) {Γ : context} {puinst : Instance.t} {args : list term} {inst : list term}, consistent_instance_ext Σ (ind_universes mdecl) puinst -> spine_substE Σ Γ args inst (ind_params mdecl,,, ind_indices idecl)@[puinst] -> Σ;;; Γ |-E mkApps (tInd ind puinst) args : tSort (ind_sort idecl)@[puinst].
Proof. exact (@PCUICInductivesEta.isType_mkApps_IndE cf). Qed.

(** Row 6: [PCUICInductivesEta.isType_mkApps_Ind_invE] (copy 16). *)
Lemma isType_mkApps_Ind_inv_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {Γ : context} {ind : inductive} {u : Instance.t} {args : list term} (wfΣ : wfE Σ.1) {mdecl : mutual_inductive_body} {idecl : one_inductive_body} (declm : declared_inductive Σ.1 ind mdecl idecl), wf_localE Σ Γ -> isTypeE Σ Γ (mkApps (tInd ind u) args) -> ∑ parsubst argsubst : list term, let parctx := (ind_params mdecl)@[u] in let argctx := subst_context parsubst 0 (ind_indices idecl)@[u] in [× spine_substE Σ Γ (firstn (ind_npars mdecl) args) parsubst parctx, spine_substE Σ Γ (skipn (ind_npars mdecl) args) argsubst argctx, #|firstn (ind_npars mdecl) args| = ind_npars mdecl, #|skipn (ind_npars mdecl) args| = context_assumptions (ind_indices idecl) & consistent_instance_ext Σ (ind_universes mdecl) u].
Proof. exact (@PCUICInductivesEta.isType_mkApps_Ind_invE cf). Qed.

(** Row 7: [PCUICAritiesEta.on_minductive_wf_paramsE] (copy 14). *)
Lemma on_minductive_wf_params_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {ind : kername} {mdecl : mutual_inductive_body} {u : Instance.t}, declared_minductive Σ.1 ind mdecl -> consistent_instance_ext Σ (ind_universes mdecl) u -> wf_localE Σ (ind_params mdecl)@[u].
Proof. exact (@PCUICAritiesEta.on_minductive_wf_paramsE cf). Qed.

(** Row 8: [PCUICInductivesEta.on_minductive_wf_params_indices_instE] (copy 16). *)
Lemma on_minductive_wf_params_indices_inst_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {mdecl : mutual_inductive_body} {ind : inductive} {idecl : one_inductive_body} (decli : declared_inductive Σ ind mdecl idecl) (u : Instance.t), consistent_instance_ext Σ (ind_universes mdecl) u -> wf_localE Σ (ind_params mdecl,,, ind_indices idecl)@[u].
Proof. exact (@PCUICInductivesEta.on_minductive_wf_params_indices_instE cf). Qed.

(** Row 9: [PCUICInductivesEta.typing_spine_ind_type_invE] (copy 16). *)
Lemma typing_spine_ind_type_inv_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {mdecl : mutual_inductive_body} {ind : inductive} {idecl : one_inductive_body} (decli : declared_inductive Σ ind mdecl idecl) (Γ : context) (u : Instance.t) (args : list term) (T : term), wf_localE Σ Γ -> consistent_instance_ext Σ (ind_universes mdecl) u -> typing_spineE Σ Γ (ind_type idecl)@[u] args T -> typing_spineE Σ Γ (it_mkProd_or_LetIn (ind_params mdecl,,, ind_indices idecl) (tSort (ind_sort idecl)))@[u] args T.
Proof. exact (@PCUICInductivesEta.typing_spine_ind_type_invE cf). Qed.

(** Row 4: [PCUICInductiveInversionEtaB.isTypeRel_cstr_typeE] (copy 18b). *)
Lemma isTypeRel_cstr_type_proved {cf : checker_flags} :
    forall (Σ : global_env_ext) (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (cdecl : constructor_body) (n : nat), wfE Σ.1 -> nth_error (ind_bodies mdecl) n = Some idecl -> cstr_type cdecl = it_mkProd_or_LetIn (ind_params mdecl,,, cstr_args cdecl) (mkApps (tRel (#|ind_params mdecl,,, cstr_args cdecl| + (#|ind_bodies mdecl| - S n))) (to_extended_list_k (ind_params mdecl) #|cstr_args cdecl| ++ cstr_indices cdecl)) -> isTypeE Σ [] (ind_type idecl) -> PCUICReduction.red Σ.1 [] (ind_type idecl) (it_mkProd_or_LetIn (ind_params mdecl) (it_mkProd_or_LetIn (ind_indices idecl) (tSort (ind_sort idecl)))) -> isTypeE Σ [] (it_mkProd_or_LetIn (ind_params mdecl) (it_mkProd_or_LetIn (ind_indices idecl) (tSort (ind_sort idecl)))) -> isSortRel (ind_sort idecl) (ind_relevance idecl) -> ctx_instE Σ (arities_context (ind_bodies mdecl),,, ind_params mdecl,,, cstr_args cdecl) (cstr_indices cdecl) (List.rev (lift_context #|cstr_args cdecl| 0 (ind_indices idecl))) -> isTypeE Σ (arities_context (ind_bodies mdecl)) (cstr_type cdecl) -> isTypeRelE Σ (arities_context (ind_bodies mdecl)) (cstr_type cdecl) (ind_relevance idecl).
Proof. exact (@PCUICInductiveInversionEtaB.isTypeRel_cstr_typeE cf). Qed.

(** Row 10: [PCUICInductiveInversionEtaB.wf_case_branch_typeE] (copy 18b). *)
Lemma wf_case_branch_type_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {ci : case_info} {p : predicate term} (ps : sort) (args : list term), declared_inductive Σ ci mdecl idecl -> isTypeE Σ Γ (mkApps (tInd ci (puinst p)) (pparams p ++ args)) -> wf_predicate mdecl idecl p -> let predctx := case_predicate_context ci mdecl idecl p in Σ;;; Γ,,, predctx |-E preturn p : tSort ps -> let ptm := it_mkLambda_or_LetIn predctx (preturn p) in All2 PCUICEquality.eq_decl_upto_names (pcontext p) (ind_predicate_context ci mdecl idecl) -> forall (i : nat) (cdecl : constructor_body) (br : branch term), declared_constructor Σ (ci, i) mdecl idecl cdecl -> wf_branch cdecl br -> let cstr_br_ctx := case_branch_context_nopars ci mdecl (puinst p) cdecl in let brctx' := map2 set_binder_name (forget_types (bcontext br)) cstr_br_ctx in let brctxty := case_branch_type ci mdecl idecl p br ptm i cdecl in [× wf_branch cdecl br, wf_localE Σ (Γ,,, (ind_params mdecl)@[puinst p],,, cstr_br_ctx), wf_localE Σ (Γ,,, (ind_params mdecl)@[puinst p],,, brctx'), wf_localE Σ (Γ,,, brctxty.1) & Σ;;; Γ,,, brctxty.1 |-E brctxty.2 : tSort ps].
Proof. exact (@PCUICInductiveInversionEtaB.wf_case_branch_typeE cf). Qed.

(** Row 11: [PCUICInductiveInversionEtaB.wf_case_predicate_contextE] (copy 18b). *)
Lemma wf_case_predicate_context_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {ci : case_info} {p : predicate term} {args : list term}, declared_inductive Σ ci mdecl idecl -> isTypeE Σ Γ (mkApps (tInd ci (puinst p)) (pparams p ++ args)) -> wf_predicate mdecl idecl p -> let predctx := case_predicate_context ci mdecl idecl p in wf_localE Σ (Γ,,, predctx).
Proof. exact (@PCUICInductiveInversionEtaB.wf_case_predicate_contextE cf). Qed.

(** Row 12: [PCUICInductiveInversionEtaB.wf_case_branches_types'E] (copy 18b). *)
Lemma wf_case_branches_types'_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {ci : case_info} {p : predicate term} (ps : sort) (args : list term) (brs : list (branch term)), declared_inductive Σ ci mdecl idecl -> isTypeE Σ Γ (mkApps (tInd ci (puinst p)) (pparams p ++ args)) -> wf_predicate mdecl idecl p -> let predctx := case_predicate_context ci mdecl idecl p in Σ;;; Γ,,, predctx |-E preturn p : tSort ps -> let ptm := it_mkLambda_or_LetIn predctx (preturn p) in wf_branches idecl brs -> All2 PCUICEquality.eq_decl_upto_names (pcontext p) (ind_predicate_context ci mdecl idecl) -> All2i (fun (i : nat) (cdecl : constructor_body) (br : branch term) => let cstr_br_ctx := case_branch_context_nopars ci mdecl (puinst p) cdecl in let brctx' := map2 set_binder_name (forget_types (bcontext br)) cstr_br_ctx in let brctxty := case_branch_type ci mdecl idecl p br ptm i cdecl in [× wf_branch cdecl br, wf_localE Σ (Γ,,, (ind_params mdecl)@[puinst p],,, cstr_br_ctx), wf_localE Σ (Γ,,, (ind_params mdecl)@[puinst p],,, brctx'), wf_localE Σ (Γ,,, brctxty.1) & Σ;;; Γ,,, brctxty.1 |-E brctxty.2 : tSort ps]) 0 (ind_ctors idecl) brs.
Proof. exact (@PCUICInductiveInversionEtaB.wf_case_branches_types'E cf). Qed.

#[export] Instance T0_facts_discharged {cf : checker_flags} : T0_facts :=
  {| PCUICTypingEtaHyps.closed_context_cumulativity := @closed_context_cumulativity_proved cf;
     PCUICTypingEtaHyps.inductive_cumulative_indices := @inductive_cumulative_indices_proved cf;
     PCUICTypingEtaHyps.invert_type_mkApps_ind := @invert_type_mkApps_ind_proved cf;
     PCUICTypingEtaHyps.isTypeRel_cstr_type := @isTypeRel_cstr_type_proved cf;
     PCUICTypingEtaHyps.isType_mkApps_Ind := @isType_mkApps_Ind_proved cf;
     PCUICTypingEtaHyps.isType_mkApps_Ind_inv := @isType_mkApps_Ind_inv_proved cf;
     PCUICTypingEtaHyps.on_minductive_wf_params := @on_minductive_wf_params_proved cf;
     PCUICTypingEtaHyps.on_minductive_wf_params_indices_inst := @on_minductive_wf_params_indices_inst_proved cf;
     PCUICTypingEtaHyps.typing_spine_ind_type_inv := @typing_spine_ind_type_inv_proved cf;
     PCUICTypingEtaHyps.wf_case_branch_type := @wf_case_branch_type_proved cf;
     PCUICTypingEtaHyps.wf_case_predicate_context := @wf_case_predicate_context_proved cf;
     PCUICTypingEtaHyps.wf_case_branches_types' := @wf_case_branches_types'_proved cf |}.

(** ** [U_facts]: row 13, transcribed ([PCUICEtaWhnfRedInv]) *)

(** Row 13: [PCUICEtaWhnfRedInv.whnf_red_invE], the E twin of [PCUICNormal.whnf_red_inv]. *)
Lemma whnf_red_inv_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} (Γ : context) (t t' : term), wfE Σ -> whnf RedFlags.default Σ Γ t -> Σ ;;; Γ ⊢ t ⇝ t' -> whnf_red Σ Γ t t'.
Proof. intros Σ Γ t t' wfΣ. exact (@PCUICEtaWhnfRedInv.whnf_red_invE cf Σ Γ t t' wfΣ). Qed.

#[export] Instance U_facts_discharged {cf : checker_flags} : U_facts :=
  {| PCUICTypingEtaHyps.whnf_red_inv := @whnf_red_inv_proved cf |}.

(** ** [T2a_facts]: rows 18-19, both fields (E validity, [PCUICValidityEta]) *)

(** Row 18: [PCUICValidityEta.inversion_mkAppsE]. *)
Lemma inversion_mkApps_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ.1} {Γ : context} {f : term} {u : list term} {T : term}, Σ;;; Γ |-E mkApps f u : T -> ∑ A : term, Σ;;; Γ |-E f : A × typing_spineE Σ Γ A u T.
Proof. exact (@PCUICValidityEta.inversion_mkAppsE cf). Qed.

(** Row 19: [PCUICValidityEta.validityE]. *)
Lemma validity_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t : term} {T : term}, Σ;;; Γ |-E t : T -> isTypeE Σ Γ T.
Proof. exact (@PCUICValidityEta.validityE cf). Qed.

#[export] Instance T2a_facts_discharged {cf : checker_flags} : T2a_facts :=
  {| PCUICTypingEtaHyps.inversion_mkApps := @inversion_mkApps_proved cf;
     PCUICTypingEtaHyps.validity := @validity_proved cf |}.

(** ** [ReduceTypedFactsCoreE]: rows 45-46 from copy 18b, row 47 transcribed ([PCUICEtaPrimOverapplied]) *)

(** Row 45: [PCUICInductiveInversionEtaB.invert_Case_ConstructE] (copy 18b, the E twin of
    [PCUICInductiveInversion.invert_Case_Construct]); Eta51Sizing's wrapper of probe C. *)
Lemma rtfc_case_construct_proved {cf : checker_flags} : forall Σ Γ ci p ind' i u brs args, wf_extE Σ ->
    welltypedE Σ Γ (tCase ci p (mkApps (tConstruct ind' i u) args) brs) ->
    ci.(ci_ind) = ind' /\
    exists br, nth_error brs i = Some br /\
      (#|args| = ci.(ci_npar) + context_assumptions br.(bcontext))%nat.
Proof.
  intros Σ Γ ci p ind' i u brs args [wfΣ _] [T h].
  exact (PCUICInductiveInversionEtaB.invert_Case_ConstructE Σ (sq wfΣ) h).
Qed.

(** Row 46: [PCUICInductiveInversionEtaB.invert_Proj_ConstructE] (copy 18b, the E twin of
    [PCUICInductiveInversion.invert_Proj_Construct]); Eta51Sizing's wrapper of probe C. *)
Lemma rtfc_proj_construct_proved {cf : checker_flags} : forall Σ Γ p i' c u l, wf_extE Σ ->
    welltypedE Σ Γ (tProj p (mkApps (tConstruct i' c u) l)) ->
    p.(proj_ind) = i' /\ c = 0 /\ (p.(proj_npars) + p.(proj_arg) < #|l|)%nat.
Proof.
  intros Σ Γ p i' c u l [wfΣ _] [T h].
  exact (PCUICInductiveInversionEtaB.invert_Proj_ConstructE Σ (sq wfΣ) h).
Qed.

(** Row 47: [PCUICEtaPrimOverapplied.prim_app_overapplied_ill_typedE], the E twin of
    [PCUICSafeReduce.prim_app_overapplied_ill_typed]; [wf_extE Σ] gives its [wfE Σ]. *)
Lemma rtfc_prim_overapplied_proved {cf : checker_flags} : forall Σ Γ c u op args, wf_extE Σ ->
    prim_op_of Σ c = Some op -> (arity op < #|args|)%nat ->
    welltypedE Σ Γ (mkApps (tConst c u) args) -> False.
Proof.
  intros Σ Γ c u op args wfΣ hop hlt h.
  exact (@PCUICEtaPrimOverapplied.prim_app_overapplied_ill_typedE cf Σ (wf_extE_wfE Σ wfΣ) Γ c u op args
           hop hlt h).
Qed.

(** ** [WelltypedEContextE]: row 51, transcribed ([PCUICEtaWelltypedContext]), and the class *)

(** Row 51: [PCUICEtaWelltypedContext.welltypedE_contextE], the E twin of
    [PCUICPositionEta.welltyped_context]. *)
Lemma welltypedE_context_proved {cf : checker_flags} : forall (Σ : global_env_ext), wfE Σ.1 -> forall Γ t,
    PCUICPositionEta.no_Eta_arg (snd t) -> welltypedE Σ Γ (PCUICPositionEta.zip t) ->
    welltypedE Σ (Γ ,,, PCUICPositionEta.stack_context (snd t)) (fst t).
Proof.
  intros Σ wfΣ Γ t hna h. exact (@PCUICEtaWelltypedContext.welltypedE_contextE cf Σ wfΣ Γ t hna h).
Qed.

#[export] Instance WelltypedEContextE_discharged {cf : checker_flags} : WelltypedEContextE :=
  {| PCUICEtaFactsCompose.welltypedE_context := @welltypedE_context_proved cf |}.

(** ** EtaPosK4's section hypothesis [closed_context_conversionE] (row 52 of the sizing, EXISTS-PROVED) *)

(** Row 52: [PCUICContextConversionTypEta.closed_context_conversionE] (copy 9); the statement is the text of
    [PCUICPositionEtaTyping.v:662-663] (section [EtaTypingE]). The squashed form is the section hypothesis
    of [PCUICSafeConversionEta] ([:182-183]); [closed_context_conversionE_squashed] below is it, from this
    lemma. *)
Lemma closed_context_conversionE_proved {cf : checker_flags} : forall (Σ : global_env_ext), wfE Σ.1 -> forall Γ t T Γ',
    Σ ;;; Γ |-E t : T -> wf_localE Σ Γ' -> ws_cumul_ctx_pbE Conv Σ Γ Γ' -> Σ ;;; Γ' |-E t : T.
Proof. exact (@PCUICContextConversionTypEta.closed_context_conversionE cf). Qed.

Definition closed_context_conversionE_squashed {cf : checker_flags} :
  ∥ forall (Σ : global_env_ext), wfE Σ.1 -> forall Γ t T Γ',
    Σ ;;; Γ |-E t : T -> wf_localE Σ Γ' -> ws_cumul_ctx_pbE Conv Σ Γ Γ' -> Σ ;;; Γ' |-E t : T ∥ :=
  sq (@closed_context_conversionE_proved cf).

(** ** Compiled identity, both ways: each [_proved] lemma at its field's projected type ([_fits]), and the
    field at the [_proved] lemma's type ([_fits_rev]). Plain Definitions with the class as a binder, not a
    Section [Context], so that the hypothesis enumerator sees no new section binder. *)

Definition closed_context_cumulativity_fits {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@closed_context_cumulativity cf H0) in exact T) :=
  @closed_context_cumulativity_proved cf.
Definition closed_context_cumulativity_fits_rev {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@closed_context_cumulativity_proved cf) in exact T) :=
  @closed_context_cumulativity cf H0.

Definition inductive_cumulative_indices_fits {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@inductive_cumulative_indices cf H0) in exact T) :=
  @inductive_cumulative_indices_proved cf.
Definition inductive_cumulative_indices_fits_rev {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@inductive_cumulative_indices_proved cf) in exact T) :=
  @inductive_cumulative_indices cf H0.

Definition invert_type_mkApps_ind_fits {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@invert_type_mkApps_ind cf H0) in exact T) :=
  @invert_type_mkApps_ind_proved cf.
Definition invert_type_mkApps_ind_fits_rev {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@invert_type_mkApps_ind_proved cf) in exact T) :=
  @invert_type_mkApps_ind cf H0.

Definition isType_mkApps_Ind_fits {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@isType_mkApps_Ind cf H0) in exact T) :=
  @isType_mkApps_Ind_proved cf.
Definition isType_mkApps_Ind_fits_rev {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@isType_mkApps_Ind_proved cf) in exact T) :=
  @isType_mkApps_Ind cf H0.

Definition isType_mkApps_Ind_inv_fits {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@isType_mkApps_Ind_inv cf H0) in exact T) :=
  @isType_mkApps_Ind_inv_proved cf.
Definition isType_mkApps_Ind_inv_fits_rev {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@isType_mkApps_Ind_inv_proved cf) in exact T) :=
  @isType_mkApps_Ind_inv cf H0.

Definition on_minductive_wf_params_fits {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@on_minductive_wf_params cf H0) in exact T) :=
  @on_minductive_wf_params_proved cf.
Definition on_minductive_wf_params_fits_rev {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@on_minductive_wf_params_proved cf) in exact T) :=
  @on_minductive_wf_params cf H0.

Definition on_minductive_wf_params_indices_inst_fits {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@on_minductive_wf_params_indices_inst cf H0) in exact T) :=
  @on_minductive_wf_params_indices_inst_proved cf.
Definition on_minductive_wf_params_indices_inst_fits_rev {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@on_minductive_wf_params_indices_inst_proved cf) in exact T) :=
  @on_minductive_wf_params_indices_inst cf H0.

Definition typing_spine_ind_type_inv_fits {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@typing_spine_ind_type_inv cf H0) in exact T) :=
  @typing_spine_ind_type_inv_proved cf.
Definition typing_spine_ind_type_inv_fits_rev {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@typing_spine_ind_type_inv_proved cf) in exact T) :=
  @typing_spine_ind_type_inv cf H0.

Definition whnf_red_inv_fits {cf : checker_flags} (HU : U_facts) :
  ltac:(let T := type of (@whnf_red_inv cf HU) in exact T) :=
  @whnf_red_inv_proved cf.
Definition whnf_red_inv_fits_rev {cf : checker_flags} (HU : U_facts) :
  ltac:(let T := type of (@whnf_red_inv_proved cf) in exact T) :=
  @whnf_red_inv cf HU.

Definition inversion_mkApps_fits {cf : checker_flags} (H2 : T2a_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.inversion_mkApps cf H2) in exact T) :=
  @inversion_mkApps_proved cf.
Definition inversion_mkApps_fits_rev {cf : checker_flags} (H2 : T2a_facts) :
  ltac:(let T := type of (@inversion_mkApps_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.inversion_mkApps cf H2.

Definition validity_fits {cf : checker_flags} (H2 : T2a_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.validity cf H2) in exact T) :=
  @validity_proved cf.
Definition validity_fits_rev {cf : checker_flags} (H2 : T2a_facts) :
  ltac:(let T := type of (@validity_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.validity cf H2.

Definition rtfc_prim_overapplied_fits {cf : checker_flags} (C : ReduceTypedFactsCoreE) :
  ltac:(let T := type of (@rtfc_prim_overapplied cf C) in exact T) :=
  @rtfc_prim_overapplied_proved cf.
Definition rtfc_prim_overapplied_fits_rev {cf : checker_flags} (C : ReduceTypedFactsCoreE) :
  ltac:(let T := type of (@rtfc_prim_overapplied_proved cf) in exact T) :=
  @rtfc_prim_overapplied cf C.

Definition isTypeRel_cstr_type_fits {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@isTypeRel_cstr_type cf H0) in exact T) :=
  @isTypeRel_cstr_type_proved cf.
Definition isTypeRel_cstr_type_fits_rev {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@isTypeRel_cstr_type_proved cf) in exact T) :=
  @isTypeRel_cstr_type cf H0.

Definition wf_case_branch_type_fits {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@wf_case_branch_type cf H0) in exact T) :=
  @wf_case_branch_type_proved cf.
Definition wf_case_branch_type_fits_rev {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@wf_case_branch_type_proved cf) in exact T) :=
  @wf_case_branch_type cf H0.

Definition wf_case_predicate_context_fits {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@wf_case_predicate_context cf H0) in exact T) :=
  @wf_case_predicate_context_proved cf.
Definition wf_case_predicate_context_fits_rev {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@wf_case_predicate_context_proved cf) in exact T) :=
  @wf_case_predicate_context cf H0.

Definition wf_case_branches_types'_fits {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@wf_case_branches_types' cf H0) in exact T) :=
  @wf_case_branches_types'_proved cf.
Definition wf_case_branches_types'_fits_rev {cf : checker_flags} (H0 : T0_facts) :
  ltac:(let T := type of (@wf_case_branches_types'_proved cf) in exact T) :=
  @wf_case_branches_types' cf H0.

Definition rtfc_case_construct_fits {cf : checker_flags} (C : ReduceTypedFactsCoreE) :
  ltac:(let T := type of (@rtfc_case_construct cf C) in exact T) :=
  @rtfc_case_construct_proved cf.
Definition rtfc_case_construct_fits_rev {cf : checker_flags} (C : ReduceTypedFactsCoreE) :
  ltac:(let T := type of (@rtfc_case_construct_proved cf) in exact T) :=
  @rtfc_case_construct cf C.

Definition rtfc_proj_construct_fits {cf : checker_flags} (C : ReduceTypedFactsCoreE) :
  ltac:(let T := type of (@rtfc_proj_construct cf C) in exact T) :=
  @rtfc_proj_construct_proved cf.
Definition rtfc_proj_construct_fits_rev {cf : checker_flags} (C : ReduceTypedFactsCoreE) :
  ltac:(let T := type of (@rtfc_proj_construct_proved cf) in exact T) :=
  @rtfc_proj_construct cf C.

Definition welltypedE_context_fits {cf : checker_flags} (WC : WelltypedEContextE) :
  ltac:(let T := type of (@PCUICEtaFactsCompose.welltypedE_context cf WC) in exact T) :=
  @welltypedE_context_proved cf.
Definition welltypedE_context_fits_rev {cf : checker_flags} (WC : WelltypedEContextE) :
  ltac:(let T := type of (@welltypedE_context_proved cf) in exact T) :=
  @PCUICEtaFactsCompose.welltypedE_context cf WC.

(** The same statement is EtaPosK4's section hypothesis [welltypedE_context] of
    [PCUICPositionEtaTyping.EtaTypingE] ([PCUICPositionEtaTyping.v:670-671], same text). A section variable
    has no constant to name, so the check is one way: [wf_localE_push_real] takes it as its first argument
    after [cf] ([Proof using welltypedE_context]), and accepts [welltypedE_context_proved] there. *)
Definition welltypedE_context_fits_EtaTypingE {cf : checker_flags} :=
  @PCUICPositionEtaTyping.wf_localE_push_real cf (@welltypedE_context_proved cf).

(** Row 52, the same way: [PCUICPositionEtaTyping.wf_localE_eta_step] takes the section hypothesis
    [closed_context_conversionE] ([PCUICPositionEtaTyping.v:662-663]) as its first argument after [cf]
    ([Proof using closed_context_conversionE]), and accepts [closed_context_conversionE_proved] there. *)
Definition closed_context_conversionE_fits_EtaTypingE {cf : checker_flags} :=
  @PCUICPositionEtaTyping.wf_localE_eta_step cf (@closed_context_conversionE_proved cf).
