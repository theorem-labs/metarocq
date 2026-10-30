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
(* LAND3 (frac/eta 730e8c59): subject reduction, classification and the bidirectional copies; and the
   rows 48-50 transcriptions over them. *)
From MetaRocq.PCUIC Require PCUICSREta PCUICClassificationEta Bidirectional.BDToPCUICEta
  Bidirectional.BDUniqueEta Bidirectional.BDFromPCUICEta.
From MetaRocq.SafeChecker Require PCUICEtaWhneTyped PCUICSafeReduceEtaBridge.

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
  - WIRING, rows proved by LAND3 (frac/eta 730e8c59): T1 rows 14-17 ([PCUICSREta]), T6 row 20
    ([PCUICClassificationEta]), T6BD rows 21-29, T6BDu rows 30-38, T6BDc rows 39-44
    ([Bidirectional/BDToPCUICEta], [BDUniqueEta], [BDFromPCUICEta]).
  - TRANSCRIPTION over LAND3: rows 48-50, [ReduceTypedFactsCoreE.rtfc_{fix,case,proj}_arg_whne]
    ([PCUICEtaWhneTyped], with the canonical forms at a primitive type it needs).
  - Classes proved whole: all eight sub-classes of [EtaFacts] ([T0_facts] 12 fields, [U_facts] 1, [T1_facts] 4,
    [T2a_facts] 2, [T6_facts] 1, [T6BD_facts] 9, [T6BDu_facts] 9, [T6BDc_facts] 6), [ReduceTypedFactsCoreE] 6
    and [WelltypedEContextE] 1; hence [EtaFacts_discharged], and the closed
    [ReduceTypedFacts welltypedE wf_extE] through the existing builders ([reduce_typed_facts_discharged]).
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

(** Row 48: [PCUICEtaWhneTyped.whnf_fix_arg_whneE], the E twin of [PCUICSafeReduce.whnf_fix_arg_whne]
    (the base instance's proof of [rtf_fix_arg_whne], [PCUICSafeReduceEta.v:276-277]). *)
Lemma rtfc_fix_arg_whne_proved {cf : checker_flags} : forall flags Σ Γ mfix idx body t before args aftr, wf_extE Σ ->
    unfold_fix mfix idx = Some (#|before|, body) ->
    match t with
    | tConstruct _ _ _ => False
    | tApp _ _ => False
    | _ => True
    end ->
    whnf flags Σ Γ (mkApps t args) ->
    welltypedE Σ Γ (mkApps (tFix mfix idx) (before ++ mkApps t args :: aftr)) ->
    ∥ whne flags Σ Γ (mkApps t args) ∥.
Proof.
  intros flags Σ Γ mfix idx body t before args aftr [wfΣ _] hu hshape hwh [T h].
  constructor. exact (PCUICEtaWhneTyped.whnf_fix_arg_whneE flags mfix idx body Σ Γ t before args aftr T
                        wfΣ hu hshape hwh h).
Qed.

(** Row 49: [PCUICEtaWhneTyped.whnf_case_arg_whneE], the E twin of [PCUICSafeReduce.whnf_case_arg_whne]. *)
Lemma rtfc_case_arg_whne_proved {cf : checker_flags} : forall flags Σ Γ hd args ci p brs, wf_extE Σ ->
    match hd with
    | tApp _ _
    | tConstruct _ _ _
    | tCoFix _ _ => False
    | _ => True
    end ->
    whnf flags Σ Γ (mkApps hd args) ->
    welltypedE Σ Γ (tCase ci p (mkApps hd args) brs) ->
    ∥ whne flags Σ Γ (mkApps hd args) ∥.
Proof.
  intros flags Σ Γ hd args ci p brs [wfΣ _] hshape hwh [T h].
  constructor. exact (PCUICEtaWhneTyped.whnf_case_arg_whneE flags Σ Γ hd args ci p brs T wfΣ hshape hwh h).
Qed.

(** Row 50: [PCUICEtaWhneTyped.whnf_proj_arg_whneE], the E twin of [PCUICSafeReduce.whnf_proj_arg_whne]. *)
Lemma rtfc_proj_arg_whne_proved {cf : checker_flags} : forall flags Σ Γ hd args p, wf_extE Σ ->
    match hd with
    | tApp _ _
    | tCoFix _ _ => False
    | tConstruct _ c _ => c <> 0
    | _ => True
    end ->
    whnf flags Σ Γ (mkApps hd args) ->
    welltypedE Σ Γ (tProj p (mkApps hd args)) ->
    ∥ whne flags Σ Γ (mkApps hd args) ∥.
Proof.
  intros flags Σ Γ hd args p [wfΣ _] hshape hwh [T h].
  constructor. exact (PCUICEtaWhneTyped.whnf_proj_arg_whneE flags Σ Γ hd args p T wfΣ hshape hwh h).
Qed.

#[export] Instance ReduceTypedFactsCoreE_discharged {cf : checker_flags} : ReduceTypedFactsCoreE :=
  {| PCUICEtaFactsCompose.rtfc_case_construct := @rtfc_case_construct_proved cf;
     PCUICEtaFactsCompose.rtfc_proj_construct := @rtfc_proj_construct_proved cf;
     PCUICEtaFactsCompose.rtfc_prim_overapplied := @rtfc_prim_overapplied_proved cf;
     PCUICEtaFactsCompose.rtfc_fix_arg_whne := @rtfc_fix_arg_whne_proved cf;
     PCUICEtaFactsCompose.rtfc_case_arg_whne := @rtfc_case_arg_whne_proved cf;
     PCUICEtaFactsCompose.rtfc_proj_arg_whne := @rtfc_proj_arg_whne_proved cf |}.

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

(** ** [T1_facts]: subject reduction over [typingE] (LAND3, [PCUICSREta]) *)

(** Row 14: [PCUICSREta.isType_prim_shape_typeE]. *)
Lemma isType_prim_shape_type_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {s : PrimitiveOps.prim_shape} {res : term}, wf_localE Σ Γ -> PCUICPrimOpType.prim_shape_type (retroknowledge Σ.1) s = Some res -> on_prim_op_result Σ s -> isTypeE Σ Γ res.
Proof. exact (@PCUICSREta.isType_prim_shape_typeE cf). Qed.

(** Row 15: [PCUICSREta.isType_redE]. *)
Lemma isType_red_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {T : term} {U : term}, isTypeE Σ Γ T -> PCUICReduction.red Σ Γ T U -> isTypeE Σ Γ U.
Proof. exact (@PCUICSREta.isType_redE cf). Qed.

(** Row 16: [PCUICSREta.subject_reductionE]. *)
Lemma subject_reduction_proved {cf : checker_flags} :
    forall (Σ : global_env_ext) (Γ : context) (t : term) (u : term) (T : term), wfE Σ -> Σ;;; Γ |-E t : T -> PCUICReduction.red Σ Γ t u -> Σ;;; Γ |-E u : T.
Proof. exact (@PCUICSREta.subject_reductionE cf). Qed.

(** Row 17: [PCUICSREta.type_reduction_closedE]. *)
Lemma type_reduction_closed_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t : term} {A : term} {B : term}, Σ;;; Γ |-E t : A -> Σ ;;; Γ ⊢ A ⇝ B -> Σ;;; Γ |-E t : B.
Proof. exact (@PCUICSREta.type_reduction_closedE cf). Qed.

#[export] Instance T1_facts_discharged {cf : checker_flags} : T1_facts :=
  {| PCUICTypingEtaHyps.isType_prim_shape_type := @isType_prim_shape_type_proved cf;
     PCUICTypingEtaHyps.isType_red := @isType_red_proved cf;
     PCUICTypingEtaHyps.subject_reduction := @subject_reduction_proved cf;
     PCUICTypingEtaHyps.type_reduction_closed := @type_reduction_closed_proved cf |}.

(** ** [T6_facts]: classification over [typingE] (LAND3, [PCUICClassificationEta]) *)

(** Row 20: [PCUICClassificationEta.typing_spine_smashE]. *)
Lemma typing_spine_smash_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ.1) (Γ : context) (Δ : context) (T : term) (args : list term) (T' : term), typing_spineE Σ Γ (it_mkProd_or_LetIn Δ T) args T' -> typing_spineE Σ Γ (it_mkProd_or_LetIn (smash_context [] Δ) (expand_lets Δ T)) args T'.
Proof. exact (@PCUICClassificationEta.typing_spine_smashE cf). Qed.

#[export] Instance T6_facts_discharged {cf : checker_flags} : T6_facts :=
  {| PCUICTypingEtaHyps.typing_spine_smash := @typing_spine_smash_proved cf |}.

(** ** [T6BD_facts]: bidirectional soundness over E (LAND3, [Bidirectional/BDToPCUICEta]) *)

(** Row 21: [BDToPCUICEta.checking_typingE]. *)
Lemma checking_typing_proved {cf : checker_flags} :
    forall (Σ : global_env_ext) (Γ : context) (t : term) (T : term) (wfΣ : wfE Σ), wf_localE Σ Γ -> isTypeE Σ Γ T -> Σ;;; Γ |-E t ◃ T -> Σ;;; Γ |-E t : T.
Proof. exact (@BDToPCUICEta.checking_typingE cf). Qed.

(** Row 22: [BDToPCUICEta.ctx_inst_bd_typingE]. *)
Lemma ctx_inst_bd_typing_proved {cf : checker_flags} :
    forall (Σ : global_env_ext) (Γ : list context_decl) (l : list term) (Δ : list context_decl) (wfΣ : wfE Σ), wf_localE Σ (Γ,,, Δ) -> PCUICTyping.ctx_inst (checkingE Σ) Γ l (List.rev Δ) -> ctx_instE Σ Γ l (List.rev Δ).
Proof. exact (@BDToPCUICEta.ctx_inst_bd_typingE cf). Qed.

(** Row 23: [BDToPCUICEta.infering_ind_typingE]. *)
Lemma infering_ind_typing_proved {cf : checker_flags} :
    forall (Σ : global_env_ext) (Γ : context) (t : term) (ind : inductive) (u : Instance.t) (args : list term) (wfΣ : wfE Σ), wf_localE Σ Γ -> Σ;;; Γ |-E t ▹{ ind}(u, args) -> Σ;;; Γ |-E t : mkApps (tInd ind u) args.
Proof. exact (@BDToPCUICEta.infering_ind_typingE cf). Qed.

(** Row 24: [BDToPCUICEta.infering_prod_typingE]. *)
Lemma infering_prod_typing_proved {cf : checker_flags} :
    forall (Σ : global_env_ext) (Γ : context) (t : term) (na : aname) (A : term) (B : term) (wfΣ : wfE Σ), wf_localE Σ Γ -> Σ;;; Γ |-E t ▹Π (na, A, B) -> Σ;;; Γ |-E t : tProd na A B.
Proof. exact (@BDToPCUICEta.infering_prod_typingE cf). Qed.

(** Row 25: [BDToPCUICEta.infering_sort_isTypeRelE]. *)
Lemma infering_sort_isTypeRel_proved {cf : checker_flags} :
    forall (Σ : global_env_ext) (Γ : context) (t : term) (u : sort) (wfΣ : wfE Σ), wf_localE Σ Γ -> Σ;;; Γ |-E t ▹□ u -> isTypeRelE Σ Γ t (relevance_of_sort u).
Proof. exact (@BDToPCUICEta.infering_sort_isTypeRelE cf). Qed.

(** Row 26: [BDToPCUICEta.infering_sort_typingE]. *)
Lemma infering_sort_typing_proved {cf : checker_flags} :
    forall (Σ : global_env_ext) (Γ : context) (t : term) (u : sort) (wfΣ : wfE Σ), wf_localE Σ Γ -> Σ;;; Γ |-E t ▹□ u -> Σ;;; Γ |-E t : tSort u.
Proof. exact (@BDToPCUICEta.infering_sort_typingE cf). Qed.

(** Row 27: [BDToPCUICEta.infering_typingE]. *)
Lemma infering_typing_proved {cf : checker_flags} :
    forall (Σ : global_env_ext) (Γ : context) (t : term) (T : term) (wfΣ : wfE Σ), wf_localE Σ Γ -> Σ;;; Γ |-E t ▹ T -> Σ;;; Γ |-E t : T.
Proof. exact (@BDToPCUICEta.infering_typingE cf). Qed.

(** Row 28: [BDToPCUICEta.lift_sorting_lift_typingE]. *)
Lemma lift_sorting_lift_typing_proved {cf : checker_flags} :
    forall (Σ : global_env_ext) (Γ : context) (j : judgment) (wfΣ : wfE Σ), wf_localE Σ Γ -> lift_sorting (checkingE Σ Γ) (infering_sortE Σ Γ) j -> lift_typing typingE Σ Γ j.
Proof. exact (@BDToPCUICEta.lift_sorting_lift_typingE cf). Qed.

(** Row 29: [BDToPCUICEta.wf_local_bd_rel_typingE]. *)
Lemma wf_local_bd_rel_typing_proved {cf : checker_flags} :
    forall (Σ : global_env_ext) (Γ : context) (Γ' : context) (wfΣ : wfE Σ), wf_localE Σ Γ -> wf_local_bd_relE Σ Γ Γ' -> wf_local_relE Σ Γ Γ'.
Proof. exact (@BDToPCUICEta.wf_local_bd_rel_typingE cf). Qed.

#[export] Instance T6BD_facts_discharged {cf : checker_flags} : T6BD_facts :=
  {| PCUICTypingEtaHyps.checking_typing := @checking_typing_proved cf;
     PCUICTypingEtaHyps.ctx_inst_bd_typing := @ctx_inst_bd_typing_proved cf;
     PCUICTypingEtaHyps.infering_ind_typing := @infering_ind_typing_proved cf;
     PCUICTypingEtaHyps.infering_prod_typing := @infering_prod_typing_proved cf;
     PCUICTypingEtaHyps.infering_sort_isTypeRel := @infering_sort_isTypeRel_proved cf;
     PCUICTypingEtaHyps.infering_sort_typing := @infering_sort_typing_proved cf;
     PCUICTypingEtaHyps.infering_typing := @infering_typing_proved cf;
     PCUICTypingEtaHyps.lift_sorting_lift_typing := @lift_sorting_lift_typing_proved cf;
     PCUICTypingEtaHyps.wf_local_bd_rel_typing := @wf_local_bd_rel_typing_proved cf |}.

(** ** [T6BDu_facts]: bidirectional uniqueness over E (LAND3, [Bidirectional/BDUniqueEta]) *)

(** Row 30: [BDUniqueEta.infering_checkingE]. *)
Lemma infering_checking_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : context} (wfΓ : wf_localE Σ Γ) {t : term} {T : term} {T' : term}, on_free_vars (shiftnP #|Γ| xpred0) T' -> Σ;;; Γ |-E t ▹ T -> Σ;;; Γ |-E t ◃ T' -> Σ ;;; Γ ⊢E T ≤ T'.
Proof. exact (@BDUniqueEta.infering_checkingE cf). Qed.

(** Row 31: [BDUniqueEta.infering_ind_indE]. *)
Lemma infering_ind_ind_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : context} (wfΓ : wf_localE Σ Γ) {t : term} {ind : inductive} {ind' : inductive} {u : Instance.t} {u' : Instance.t} {args : list term} {args' : list term}, Σ;;; Γ |-E t ▹{ ind}(u, args) -> Σ;;; Γ |-E t ▹{ ind'}(u', args') -> ∑ args'' : list term, [× ind = ind', u = u', red_terms Σ Γ args args'' & red_terms Σ Γ args' args''].
Proof. exact (@BDUniqueEta.infering_ind_indE cf). Qed.

(** Row 32: [BDUniqueEta.infering_ind_inferingE]. *)
Lemma infering_ind_infering_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : context} (wfΓ : wf_localE Σ Γ) {t : term} {ind : inductive} {u : Instance.t} {args : list term} {T : term}, Σ;;; Γ |-E t ▹{ ind}(u, args) -> Σ;;; Γ |-E t ▹ T -> ∑ args' : list term, Σ ;;; Γ ⊢ T ⇝ mkApps (tInd ind u) args' × red_terms Σ Γ args args'.
Proof. exact (@BDUniqueEta.infering_ind_inferingE cf). Qed.

(** Row 33: [BDUniqueEta.infering_prod_inferingE]. *)
Lemma infering_prod_infering_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : context} (wfΓ : wf_localE Σ Γ) {t : term} {na : aname} {A : term} {B : term} {T : term}, Σ;;; Γ |-E t ▹Π (na, A, B) -> Σ;;; Γ |-E t ▹ T -> ∑ A' B' : term, [× Σ ;;; Γ ⊢ T ⇝ tProd na A' B', Σ ;;; Γ ⊢ A ⇝ A' & Σ ;;; Γ,, vass na A ⊢ B ⇝ B'].
Proof. exact (@BDUniqueEta.infering_prod_inferingE cf). Qed.

(** Row 34: [BDUniqueEta.infering_prod_prodE]. *)
Lemma infering_prod_prod_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : context} (wfΓ : wf_localE Σ Γ) {t : term} {na : aname} {na' : aname} {A : term} {A' : term} {B : term} {B' : term}, Σ;;; Γ |-E t ▹Π (na, A, B) -> Σ;;; Γ |-E t ▹Π (na', A', B') -> ∑ A'' B'' : term, [× na = na', Σ ;;; Γ ⊢ A ⇝ A'', Σ ;;; Γ ⊢ A' ⇝ A'', Σ ;;; Γ,, vass na A ⊢ B ⇝ B'' & Σ ;;; Γ,, vass na A' ⊢ B' ⇝ B''].
Proof. exact (@BDUniqueEta.infering_prod_prodE cf). Qed.

(** Row 35: [BDUniqueEta.infering_sort_inferingE]. *)
Lemma infering_sort_infering_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : context} {wfΓ : wf_localE Σ Γ} {t : term} {u : sort} {T : term}, Σ;;; Γ |-E t ▹□ u -> Σ;;; Γ |-E t ▹ T -> Σ ;;; Γ ⊢ T ⇝ tSort u.
Proof. exact (@BDUniqueEta.infering_sort_inferingE cf). Qed.

(** Row 36: [BDUniqueEta.infering_sort_sortE]. *)
Lemma infering_sort_sort_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : context} (wfΓ : wf_localE Σ Γ) {t : term} {u : sort} {u' : sort}, Σ;;; Γ |-E t ▹□ u -> Σ;;; Γ |-E t ▹□ u' -> u = u'.
Proof. exact (@BDUniqueEta.infering_sort_sortE cf). Qed.

(** Row 37: [BDUniqueEta.infering_uniqueE]. *)
Lemma infering_unique_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : context} (wfΓ : wf_localE Σ Γ) {t : term} {T : term} {T' : term}, Σ;;; Γ |-E t ▹ T -> Σ;;; Γ |-E t ▹ T' -> ∑ T'' : term, Σ ;;; Γ ⊢ T ⇝ T'' × Σ ;;; Γ ⊢ T' ⇝ T''.
Proof. exact (@BDUniqueEta.infering_uniqueE cf). Qed.

(** Row 38: [BDUniqueEta.isTypeRel_uniqueE]. *)
Lemma isTypeRel_unique_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : context} {T : term} {rel : relevance} {rel' : relevance}, isTypeRelE Σ Γ T rel -> isTypeRelE Σ Γ T rel' -> rel = rel'.
Proof. exact (@BDUniqueEta.isTypeRel_uniqueE cf). Qed.

#[export] Instance T6BDu_facts_discharged {cf : checker_flags} : T6BDu_facts :=
  {| PCUICTypingEtaHyps.infering_checking := @infering_checking_proved cf;
     PCUICTypingEtaHyps.infering_ind_ind := @infering_ind_ind_proved cf;
     PCUICTypingEtaHyps.infering_ind_infering := @infering_ind_infering_proved cf;
     PCUICTypingEtaHyps.infering_prod_infering := @infering_prod_infering_proved cf;
     PCUICTypingEtaHyps.infering_prod_prod := @infering_prod_prod_proved cf;
     PCUICTypingEtaHyps.infering_sort_infering := @infering_sort_infering_proved cf;
     PCUICTypingEtaHyps.infering_sort_sort := @infering_sort_sort_proved cf;
     PCUICTypingEtaHyps.infering_unique := @infering_unique_proved cf;
     PCUICTypingEtaHyps.isTypeRel_unique := @isTypeRel_unique_proved cf |}.

(** ** [T6BDc_facts]: bidirectional completeness over E (LAND3, [Bidirectional/BDFromPCUICEta]) *)

(** Row 39: [BDFromPCUICEta.ctx_inst_typing_bdE]. *)
Lemma ctx_inst_typing_bd_proved {cf : checker_flags} :
    forall (Σ : global_env_ext) (Γ : context) (l : list term) (Δ : context) (wfΣ : wfE Σ), ctx_instE Σ Γ l Δ -> PCUICTyping.ctx_inst (checkingE Σ) Γ l Δ.
Proof. exact (@BDFromPCUICEta.ctx_inst_typing_bdE cf). Qed.

(** Row 40: [BDFromPCUICEta.lift_typing_lift_sortingE]. *)
Lemma lift_typing_lift_sorting_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : context} {tm : option term} {ty : term} {rel : option relevance}, lift_typing typingE Σ Γ (Judge tm ty None rel) -> lift_sorting (checkingE Σ Γ) (infering_sortE Σ Γ) (Judge tm ty None rel).
Proof. exact (@BDFromPCUICEta.lift_typing_lift_sortingE cf). Qed.

(** Row 41: [BDFromPCUICEta.typing_checkingE]. *)
Lemma typing_checking_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t : term} {T : term}, Σ;;; Γ |-E t : T -> Σ;;; Γ |-E t ◃ T.
Proof. exact (@BDFromPCUICEta.typing_checkingE cf). Qed.

(** Row 42: [BDFromPCUICEta.typing_inferingE]. *)
Lemma typing_infering_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t : term} {T : term}, Σ;;; Γ |-E t : T -> ∑ T' : term, Σ;;; Γ |-E t ▹ T' × Σ ;;; Γ ⊢E T' ≤ T.
Proof. exact (@BDFromPCUICEta.typing_inferingE cf). Qed.

(** Row 43: [BDFromPCUICEta.typing_infering_sortE]. *)
Lemma typing_infering_sort_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t : term} {u : sort}, Σ;;; Γ |-E t : tSort u -> ∑ u' : sort, Σ;;; Γ |-E t ▹□ u' × leq_sort Σ u' u.
Proof. exact (@BDFromPCUICEta.typing_infering_sortE cf). Qed.

(** Row 44: [BDFromPCUICEta.wf_local_rel_wf_local_bdE]. *)
Lemma wf_local_rel_wf_local_bd_proved {cf : checker_flags} :
    forall {Σ : global_env_ext} (wfΣ : wfE Σ) {Γ : list context_decl} {Γ' : context}, wf_local_relE Σ Γ Γ' -> wf_local_bd_relE Σ Γ Γ'.
Proof. exact (@BDFromPCUICEta.wf_local_rel_wf_local_bdE cf). Qed.

#[export] Instance T6BDc_facts_discharged {cf : checker_flags} : T6BDc_facts :=
  {| PCUICTypingEtaHyps.ctx_inst_typing_bd := @ctx_inst_typing_bd_proved cf;
     PCUICTypingEtaHyps.lift_typing_lift_sorting := @lift_typing_lift_sorting_proved cf;
     PCUICTypingEtaHyps.typing_checking := @typing_checking_proved cf;
     PCUICTypingEtaHyps.typing_infering := @typing_infering_proved cf;
     PCUICTypingEtaHyps.typing_infering_sort := @typing_infering_sort_proved cf;
     PCUICTypingEtaHyps.wf_local_rel_wf_local_bd := @wf_local_rel_wf_local_bd_proved cf |}.

(** ** The whole bundle [EtaFacts] (all eight sub-classes proved), and the closed [ReduceTypedFacts] *)

#[export] Instance EtaFacts_discharged {cf : checker_flags} : EtaFacts :=
  {| PCUICTypingEtaHyps.eta_T0 := sq (@T0_facts_discharged cf);
     PCUICTypingEtaHyps.eta_U := sq (@U_facts_discharged cf);
     PCUICTypingEtaHyps.eta_T1 := sq (@T1_facts_discharged cf);
     PCUICTypingEtaHyps.eta_T2a := sq (@T2a_facts_discharged cf);
     PCUICTypingEtaHyps.eta_T6 := sq (@T6_facts_discharged cf);
     PCUICTypingEtaHyps.eta_T6BD := sq (@T6BD_facts_discharged cf);
     PCUICTypingEtaHyps.eta_T6BDu := sq (@T6BDu_facts_discharged cf);
     PCUICTypingEtaHyps.eta_T6BDc := sq (@T6BDc_facts_discharged cf) |}.

(** The root binder [reduce_factsE : ReduceTypedFacts welltypedE wf_extE], closed, through the existing
    builders [PCUICEtaFactsCompose.reduce_typed_facts_E_of_core] and
    [PCUICSafeReduceEtaBridge.reduce_typed_facts_E] at the three proved instances. *)
Definition reduce_typed_facts_discharged {cf : checker_flags} :
  PCUICSafeReduceEta.ReduceTypedFacts welltypedE wf_extE :=
  @PCUICSafeReduceEtaBridge.reduce_typed_facts_E cf
    (@reduce_typed_facts_E_of_core cf (@ReduceTypedFactsCoreE_discharged cf) (@EtaFacts_discharged cf)
       (@WelltypedEContextE_discharged cf)).

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

(** The LAND3 rows (T1, T6, T6BD, T6BDu, T6BDc) and rows 48-50, the same way. *)

Definition isType_prim_shape_type_fits {cf : checker_flags} (H1 : T1_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.isType_prim_shape_type cf H1) in exact T) :=
  @isType_prim_shape_type_proved cf.
Definition isType_prim_shape_type_fits_rev {cf : checker_flags} (H1 : T1_facts) :
  ltac:(let T := type of (@isType_prim_shape_type_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.isType_prim_shape_type cf H1.

Definition isType_red_fits {cf : checker_flags} (H1 : T1_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.isType_red cf H1) in exact T) :=
  @isType_red_proved cf.
Definition isType_red_fits_rev {cf : checker_flags} (H1 : T1_facts) :
  ltac:(let T := type of (@isType_red_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.isType_red cf H1.

Definition subject_reduction_fits {cf : checker_flags} (H1 : T1_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.subject_reduction cf H1) in exact T) :=
  @subject_reduction_proved cf.
Definition subject_reduction_fits_rev {cf : checker_flags} (H1 : T1_facts) :
  ltac:(let T := type of (@subject_reduction_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.subject_reduction cf H1.

Definition type_reduction_closed_fits {cf : checker_flags} (H1 : T1_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.type_reduction_closed cf H1) in exact T) :=
  @type_reduction_closed_proved cf.
Definition type_reduction_closed_fits_rev {cf : checker_flags} (H1 : T1_facts) :
  ltac:(let T := type of (@type_reduction_closed_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.type_reduction_closed cf H1.

Definition typing_spine_smash_fits {cf : checker_flags} (H6 : T6_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.typing_spine_smash cf H6) in exact T) :=
  @typing_spine_smash_proved cf.
Definition typing_spine_smash_fits_rev {cf : checker_flags} (H6 : T6_facts) :
  ltac:(let T := type of (@typing_spine_smash_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.typing_spine_smash cf H6.

Definition checking_typing_fits {cf : checker_flags} (HB : T6BD_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.checking_typing cf HB) in exact T) :=
  @checking_typing_proved cf.
Definition checking_typing_fits_rev {cf : checker_flags} (HB : T6BD_facts) :
  ltac:(let T := type of (@checking_typing_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.checking_typing cf HB.

Definition ctx_inst_bd_typing_fits {cf : checker_flags} (HB : T6BD_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.ctx_inst_bd_typing cf HB) in exact T) :=
  @ctx_inst_bd_typing_proved cf.
Definition ctx_inst_bd_typing_fits_rev {cf : checker_flags} (HB : T6BD_facts) :
  ltac:(let T := type of (@ctx_inst_bd_typing_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.ctx_inst_bd_typing cf HB.

Definition infering_ind_typing_fits {cf : checker_flags} (HB : T6BD_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.infering_ind_typing cf HB) in exact T) :=
  @infering_ind_typing_proved cf.
Definition infering_ind_typing_fits_rev {cf : checker_flags} (HB : T6BD_facts) :
  ltac:(let T := type of (@infering_ind_typing_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.infering_ind_typing cf HB.

Definition infering_prod_typing_fits {cf : checker_flags} (HB : T6BD_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.infering_prod_typing cf HB) in exact T) :=
  @infering_prod_typing_proved cf.
Definition infering_prod_typing_fits_rev {cf : checker_flags} (HB : T6BD_facts) :
  ltac:(let T := type of (@infering_prod_typing_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.infering_prod_typing cf HB.

Definition infering_sort_isTypeRel_fits {cf : checker_flags} (HB : T6BD_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.infering_sort_isTypeRel cf HB) in exact T) :=
  @infering_sort_isTypeRel_proved cf.
Definition infering_sort_isTypeRel_fits_rev {cf : checker_flags} (HB : T6BD_facts) :
  ltac:(let T := type of (@infering_sort_isTypeRel_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.infering_sort_isTypeRel cf HB.

Definition infering_sort_typing_fits {cf : checker_flags} (HB : T6BD_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.infering_sort_typing cf HB) in exact T) :=
  @infering_sort_typing_proved cf.
Definition infering_sort_typing_fits_rev {cf : checker_flags} (HB : T6BD_facts) :
  ltac:(let T := type of (@infering_sort_typing_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.infering_sort_typing cf HB.

Definition infering_typing_fits {cf : checker_flags} (HB : T6BD_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.infering_typing cf HB) in exact T) :=
  @infering_typing_proved cf.
Definition infering_typing_fits_rev {cf : checker_flags} (HB : T6BD_facts) :
  ltac:(let T := type of (@infering_typing_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.infering_typing cf HB.

Definition lift_sorting_lift_typing_fits {cf : checker_flags} (HB : T6BD_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.lift_sorting_lift_typing cf HB) in exact T) :=
  @lift_sorting_lift_typing_proved cf.
Definition lift_sorting_lift_typing_fits_rev {cf : checker_flags} (HB : T6BD_facts) :
  ltac:(let T := type of (@lift_sorting_lift_typing_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.lift_sorting_lift_typing cf HB.

Definition wf_local_bd_rel_typing_fits {cf : checker_flags} (HB : T6BD_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.wf_local_bd_rel_typing cf HB) in exact T) :=
  @wf_local_bd_rel_typing_proved cf.
Definition wf_local_bd_rel_typing_fits_rev {cf : checker_flags} (HB : T6BD_facts) :
  ltac:(let T := type of (@wf_local_bd_rel_typing_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.wf_local_bd_rel_typing cf HB.

Definition infering_checking_fits {cf : checker_flags} (HU : T6BDu_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.infering_checking cf HU) in exact T) :=
  @infering_checking_proved cf.
Definition infering_checking_fits_rev {cf : checker_flags} (HU : T6BDu_facts) :
  ltac:(let T := type of (@infering_checking_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.infering_checking cf HU.

Definition infering_ind_ind_fits {cf : checker_flags} (HU : T6BDu_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.infering_ind_ind cf HU) in exact T) :=
  @infering_ind_ind_proved cf.
Definition infering_ind_ind_fits_rev {cf : checker_flags} (HU : T6BDu_facts) :
  ltac:(let T := type of (@infering_ind_ind_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.infering_ind_ind cf HU.

Definition infering_ind_infering_fits {cf : checker_flags} (HU : T6BDu_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.infering_ind_infering cf HU) in exact T) :=
  @infering_ind_infering_proved cf.
Definition infering_ind_infering_fits_rev {cf : checker_flags} (HU : T6BDu_facts) :
  ltac:(let T := type of (@infering_ind_infering_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.infering_ind_infering cf HU.

Definition infering_prod_infering_fits {cf : checker_flags} (HU : T6BDu_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.infering_prod_infering cf HU) in exact T) :=
  @infering_prod_infering_proved cf.
Definition infering_prod_infering_fits_rev {cf : checker_flags} (HU : T6BDu_facts) :
  ltac:(let T := type of (@infering_prod_infering_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.infering_prod_infering cf HU.

Definition infering_prod_prod_fits {cf : checker_flags} (HU : T6BDu_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.infering_prod_prod cf HU) in exact T) :=
  @infering_prod_prod_proved cf.
Definition infering_prod_prod_fits_rev {cf : checker_flags} (HU : T6BDu_facts) :
  ltac:(let T := type of (@infering_prod_prod_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.infering_prod_prod cf HU.

Definition infering_sort_infering_fits {cf : checker_flags} (HU : T6BDu_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.infering_sort_infering cf HU) in exact T) :=
  @infering_sort_infering_proved cf.
Definition infering_sort_infering_fits_rev {cf : checker_flags} (HU : T6BDu_facts) :
  ltac:(let T := type of (@infering_sort_infering_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.infering_sort_infering cf HU.

Definition infering_sort_sort_fits {cf : checker_flags} (HU : T6BDu_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.infering_sort_sort cf HU) in exact T) :=
  @infering_sort_sort_proved cf.
Definition infering_sort_sort_fits_rev {cf : checker_flags} (HU : T6BDu_facts) :
  ltac:(let T := type of (@infering_sort_sort_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.infering_sort_sort cf HU.

Definition infering_unique_fits {cf : checker_flags} (HU : T6BDu_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.infering_unique cf HU) in exact T) :=
  @infering_unique_proved cf.
Definition infering_unique_fits_rev {cf : checker_flags} (HU : T6BDu_facts) :
  ltac:(let T := type of (@infering_unique_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.infering_unique cf HU.

Definition isTypeRel_unique_fits {cf : checker_flags} (HU : T6BDu_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.isTypeRel_unique cf HU) in exact T) :=
  @isTypeRel_unique_proved cf.
Definition isTypeRel_unique_fits_rev {cf : checker_flags} (HU : T6BDu_facts) :
  ltac:(let T := type of (@isTypeRel_unique_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.isTypeRel_unique cf HU.

Definition ctx_inst_typing_bd_fits {cf : checker_flags} (HC : T6BDc_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.ctx_inst_typing_bd cf HC) in exact T) :=
  @ctx_inst_typing_bd_proved cf.
Definition ctx_inst_typing_bd_fits_rev {cf : checker_flags} (HC : T6BDc_facts) :
  ltac:(let T := type of (@ctx_inst_typing_bd_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.ctx_inst_typing_bd cf HC.

Definition lift_typing_lift_sorting_fits {cf : checker_flags} (HC : T6BDc_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.lift_typing_lift_sorting cf HC) in exact T) :=
  @lift_typing_lift_sorting_proved cf.
Definition lift_typing_lift_sorting_fits_rev {cf : checker_flags} (HC : T6BDc_facts) :
  ltac:(let T := type of (@lift_typing_lift_sorting_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.lift_typing_lift_sorting cf HC.

Definition typing_checking_fits {cf : checker_flags} (HC : T6BDc_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.typing_checking cf HC) in exact T) :=
  @typing_checking_proved cf.
Definition typing_checking_fits_rev {cf : checker_flags} (HC : T6BDc_facts) :
  ltac:(let T := type of (@typing_checking_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.typing_checking cf HC.

Definition typing_infering_fits {cf : checker_flags} (HC : T6BDc_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.typing_infering cf HC) in exact T) :=
  @typing_infering_proved cf.
Definition typing_infering_fits_rev {cf : checker_flags} (HC : T6BDc_facts) :
  ltac:(let T := type of (@typing_infering_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.typing_infering cf HC.

Definition typing_infering_sort_fits {cf : checker_flags} (HC : T6BDc_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.typing_infering_sort cf HC) in exact T) :=
  @typing_infering_sort_proved cf.
Definition typing_infering_sort_fits_rev {cf : checker_flags} (HC : T6BDc_facts) :
  ltac:(let T := type of (@typing_infering_sort_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.typing_infering_sort cf HC.

Definition wf_local_rel_wf_local_bd_fits {cf : checker_flags} (HC : T6BDc_facts) :
  ltac:(let T := type of (@PCUICTypingEtaHyps.wf_local_rel_wf_local_bd cf HC) in exact T) :=
  @wf_local_rel_wf_local_bd_proved cf.
Definition wf_local_rel_wf_local_bd_fits_rev {cf : checker_flags} (HC : T6BDc_facts) :
  ltac:(let T := type of (@wf_local_rel_wf_local_bd_proved cf) in exact T) :=
  @PCUICTypingEtaHyps.wf_local_rel_wf_local_bd cf HC.

Definition rtfc_fix_arg_whne_fits {cf : checker_flags} (C : ReduceTypedFactsCoreE) :
  ltac:(let T := type of (@rtfc_fix_arg_whne cf C) in exact T) :=
  @rtfc_fix_arg_whne_proved cf.
Definition rtfc_fix_arg_whne_fits_rev {cf : checker_flags} (C : ReduceTypedFactsCoreE) :
  ltac:(let T := type of (@rtfc_fix_arg_whne_proved cf) in exact T) :=
  @rtfc_fix_arg_whne cf C.

Definition rtfc_case_arg_whne_fits {cf : checker_flags} (C : ReduceTypedFactsCoreE) :
  ltac:(let T := type of (@rtfc_case_arg_whne cf C) in exact T) :=
  @rtfc_case_arg_whne_proved cf.
Definition rtfc_case_arg_whne_fits_rev {cf : checker_flags} (C : ReduceTypedFactsCoreE) :
  ltac:(let T := type of (@rtfc_case_arg_whne_proved cf) in exact T) :=
  @rtfc_case_arg_whne cf C.

Definition rtfc_proj_arg_whne_fits {cf : checker_flags} (C : ReduceTypedFactsCoreE) :
  ltac:(let T := type of (@rtfc_proj_arg_whne cf C) in exact T) :=
  @rtfc_proj_arg_whne_proved cf.
Definition rtfc_proj_arg_whne_fits_rev {cf : checker_flags} (C : ReduceTypedFactsCoreE) :
  ltac:(let T := type of (@rtfc_proj_arg_whne_proved cf) in exact T) :=
  @rtfc_proj_arg_whne cf C.
