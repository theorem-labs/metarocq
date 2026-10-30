(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 CRelationClasses ProofIrrelevance.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICInduction
     PCUICLiftSubst PCUICUnivSubst
     PCUICTyping PCUICGlobalEnv
     PCUICWeakeningEnv PCUICWeakeningEnvTyp
     PCUICWeakeningConv PCUICWeakeningTyp
     PCUICSigmaCalculus
     PCUICSubstitution PCUICClosed PCUICClosedConv PCUICClosedTyp
     PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICEquality PCUICConfluence PCUICCasesContexts
     PCUICOnFreeVars PCUICContextConversion PCUICContextConversionTyp PCUICContextSubst
     PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
     PCUICConversion PCUICInversion PCUICContexts PCUICArities
     PCUICSpine PCUICInductives PCUICFixWitness
     PCUICWellScopedCumulativity PCUICValidity PCUICArityRed PCUICClosedBodies
     PCUICInductiveInversion
     PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
     PCUICTypingEtaNotions PCUICClosedTypEta PCUICWeakeningEnvTypEta PCUICRenameTypEta
     PCUICWeakeningTypEta PCUICUnivSubstitutionTypEta PCUICContextConversionTypEta
     PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta
     PCUICWellScopedCumulativityEta PCUICContextConversionEta PCUICConversionEtaCongr
     PCUICConversionEtaCongrFinst PCUICEtaFInst PCUICEtaFInstGlue
     PCUICWsCumulEtaSubst PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp PCUICEtaA6 PCUICEtaA6Ind
     PCUICEtaA6More PCUICEtaMkAppsTRel
     PCUICEtaI5 PCUICInversionEta PCUICSREtaConv PCUICSpineEta PCUICInductivesEta
     PCUICWsCumulEtaInstancesGlobal.
From MetaRocq.PCUIC Require PCUICWfUniversesEta PCUICEtaI5A2.

From Equations.Type Require Import Relation_Properties.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool.

(** * Inversion facts on inductive types over [typingE]: the cumulativity of projection types and
    of the indices

  The E copy of the part of [PCUICInductiveInversion] that [projection_cumulative_indicesE] and
  [ctx_inst_app_weakE] need: the declarations of their dependency closure that mention typing,
  [wf_local], [wf], [isType], the spines, [ctx_inst] or the cumulativity (in the statement, or
  through the [wf] variable of their section). The E name is the base name with the suffix [E];
  the statement is base's with only the relations renamed: [typing] → [typingE], [wf_local] →
  [wf_localE], [wf] → [wfE], [isType] → [isTypeE], [spine_subst] → [spine_substE], [ctx_inst] →
  [ctx_instE], [cumulSpec0] → [cumulSpecE0], [ws_cumul_pb_terms] → [ws_cumul_pbE_terms],
  [ws_cumul_ctx_pb_rel] → [ws_cumul_ctx_pbE_rel], [Σ ;;; Γ ⊢ t ≤[pb] u] → [Σ ;;; Γ ⊢E t ≤[pb] u].
  Reduction ([Σ ;;; Γ ⊢ t ⇝ u], [red]) is unchanged. Implicit status, binder names, binder types
  and positions are base's; section premises are base's.

  Three lemmas of the closure have E forms in other files, used here: [ws_cumul_pbE_mkApps_tRel]
  ([PCUICEtaMkAppsTRel]), [ws_cumul_pbE_LetIn_inv] and [ws_cumul_pbE_Prod_Prod_inv_l]
  ([PCUICEtaA6More]). Not copied: [ws_cumul_pb_terms_confl], whose E form is false (two terms
  related by one η step, [λx:Prop. f x] and [f], have no reducts that [compare_term] relates:
  [ws_cumul_pbE_red_false], [PCUICWsCumulEtaCtx]); and the declarations that mention none of the
  relations, used from base, which this file imports.

  Proof routes that differ from base (the statements are twins):
  - [ws_cumul_pb_mkApps_eqE] builds the join directly: each argument pair's join gives reducts
    ([PCUICEtaI5A2.All2_JoinE_ex]), and the head comparison [compare_term_napp] is U1' at the
    same [napp] ([eq_term_upto_univ_napp_finst], [PCUICEtaFInstGlue]), so the two spines over
    those reducts are compared by [PCUICEtaI5A2.RF_mkApps]. Base compares common reducts through
    [ws_cumul_pb_terms_confl].
  - [positive_cstr_arg_subst_nestedE] reads the universe clause of [invert_cumul_ind_indE]
    ([cmp_global_instance_finst] at the number of arguments) and rebuilds the conclusion with
    [ws_cumul_pbE_Ind_finst] ([PCUICConversionEtaCongrFinst]), which takes that clause.
  - [ctx_inst_app_weakE]: [isTypeE] of [mkApps (tInd ind u) args] makes [args] the full arity
    of the inductive, and there the clause of [invert_cumul_ind_indE] is base's
    [cmp_ind_universes] ([finst_ind_glue_full], [PCUICEtaFInstGlue]).
  - [on_constructor_substE] and [wt_ind_app_varianceE] split an application typed at a sort by
    [inversion_mkApps_directE] ([PCUICSpineEta]), where base uses [inversion_mkApps]
    ([PCUICValidity]).
  - [cumul_ctx_relSpec_AlgoE] scopes the specification by [into_ws_cumul_pbE_spec], and replaces
    base's [reflexivity] on the identical-prefix goal, which resolves to the instance
    [PCUICCumulativity.cumul_ctx_refl] at [Cumul], by an explicit [All2_fold_refl] with
    [JoinE_refl]: the E side twins base's [conv_ctx_refl] ([conv_ctx_reflE], at [Conv]) but not
    [cumul_ctx_refl], so no instance closes that goal.
  - [projection_cumulative_indicesE] builds the equal-instance case by [ws_cumul_pb_compare] and
    [ws_cumul_pb_incl_E].
  - [positive_cstr_arg_subst_closedE] and [positive_cstr_arg_substE] substitute by
    [untyped_substitution_ws_cumul_pbE] ([subslet_untyped_subsletE] of [subslet_indsE]).
  - [invert_red_mkApps_tRelE] is the corollary of [invert_red_mkApps_tRel_cb], through
    [wfE_ClosedBodies].

  [transitivity] on term lists ([positive_cstr_arg_subst_nestedE]) resolves to
  [ws_cumul_pbE_terms_trans] ([PCUICWsCumulEtaInstancesGlobal]), as base's resolves to
  [ws_cumul_pb_terms_trans].

  Names that are ambiguous in this file's context: every reference to a short name that, after
  this file's Requires, resolves to more than one distinct constant or abbreviation is written
  qualified, for instance [PCUICWsCumulEtaCtx.subst_instance_ws_cumul_ctx_pbE_rel] (the twin of
  [PCUICConversion.subst_instance_ws_cumul_ctx_pb_rel]; [Typing/PCUICUnivSubstitutionTypEta]
  declares a different lemma of that name), [PCUICWeakeningTypEta.weaken_wf_localE] and
  [PCUICSpine.closed_ctx_subst]. A reference that resolves to another object than the same name
  in the base twin is written qualified too: [PCUICCumulativitySpec.cumul_ctx_rel] (the context
  relation over a given comparison), where base's twins read [PCUICCumulativity.cumul_ctx_rel]. *)

Local Set SimplIsCbn.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Section OnConstructor.

  Context {cf:checker_flags} {Σ : global_env} {ind mdecl idecl cdecl}
    {wfΣ: wfE Σ} (declc : declared_constructor Σ ind mdecl idecl cdecl).

  Lemma on_constructor_wf_argsE :
    wf_localE (Σ, ind_universes mdecl)
    (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cstr_args cdecl).
  Proof using declc wfΣ.
    pose proof (on_declared_constructorE declc) as [[onmind oib] [cunivs [hnth onc]]].
    pose proof (on_cargs onc). simpl in X.
    eapply sorts_local_ctx_wf_localE in X => //. clear X.
    eapply PCUICWeakeningTypEta.weaken_wf_localE => //.
    eapply wf_arities_contextE; eauto. eapply declc.
    now eapply onParams in onmind.
  Qed.

  Lemma on_constructor_substE :
    wf_global_extE Σ (ind_universes mdecl) *
    wf_localE (Σ, ind_universes mdecl)
    (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cstr_args cdecl) *
    ∑ inst,
    spine_substE (Σ, ind_universes mdecl)
              (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,,
                cstr_args cdecl)
              ((to_extended_list_k (ind_params mdecl) #|cstr_args cdecl|) ++
                (cstr_indices cdecl)) inst
            (ind_params mdecl ,,, ind_indices idecl).
  Proof using declc wfΣ.
    pose proof (on_declared_constructorE declc) as [[onmind oib] [cunivs [hnth onc]]].
    pose proof (onc.(on_cargs)). simpl in X.
    split. split. split.
    2:{ eapply (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl)); tea.
        clear hnth. unshelve eapply declared_constructor_to_gen in declc; eauto. }
    red. apply wfΣ.
    eapply sorts_local_ctx_wf_localE in X => //. clear X.
    eapply PCUICWeakeningTypEta.weaken_wf_localE => //.
    eapply wf_arities_contextE; eauto; eapply declc.
    now eapply onParams in onmind.
    destruct (on_ctype onc) as (_ & s & Hs & _).
    rewrite onc.(cstr_eq) in Hs.
    rewrite -it_mkProd_or_LetIn_app in Hs.
    eapply inversion_it_mkProd_or_LetInE in Hs => //.
    unfold cstr_concl_head in Hs. simpl in Hs.
    pose proof (isType_SortE (PCUICWfUniversesEta.typing_wf_sortE (Σ := (Σ, ind_universes mdecl)) wfΣ Hs) (typingE_wf_local Hs)) as isS.
    eapply (inversion_mkApps_directE isS) in Hs as [A [sA [ta [_ sp]]]].
    eapply inversion_RelE in ta as [decl [wfΓ [nth cum']]].
    rewrite nth_error_app_ge in nth. len.
    len in nth.
    all:auto.
    assert ((#|ind_bodies mdecl| - Datatypes.S (inductive_ind ind.1) + #|ind_params mdecl| +
    #|cstr_args cdecl| -
    (#|cstr_args cdecl| + #|ind_params mdecl|)) = #|ind_bodies mdecl| - Datatypes.S (inductive_ind ind.1)) by lia.
    move: nth; rewrite H; clear H.
    case: nth_error_spec => // /= decl' Hdecl Hlen.
    intros [= ->].
    eapply (nth_errror_arities_context (Σ := (Σ, ind_universes mdecl)) declc) in Hdecl; eauto.
    rewrite Hdecl in cum'; clear Hdecl.
    assert(clT : closed (ind_type idecl)).
    { destruct (oib.(onArity)) as (_ & s' & Hs & _). now apply subject_closedE in Hs. }
    rewrite lift_closed in cum' => //.
    eapply typing_spine_strengthenE in sp; simpl.
    3:tea.
    (* [ind_type] reduces to the arity built from the parameters and the indices. *)
    have hred := closed_red_from_emptyE (Σ := (Σ, ind_universes mdecl))
      (wf_local_closed_contextE wfΓ) clT (declared_inductive_typeE (MRProd.proj1 declc)).
    eapply typing_spine_strengthenE in sp.
    3:{ now eapply red_ws_cumul_pbE_inv. }
    simpl in sp.
    apply (arity_typing_spineE (Σ := (Σ, ind_universes mdecl))) in sp as [Hlen' Hleq [inst Hinst]] => //.
    clear Hlen'.
    rewrite [_ ,,, _]app_context_assoc in Hinst.
    now exists inst.
    apply lift_typing_weaken_ctxE with (Γ := []); tas.
    eapply isTypeRelE_isTypeE.
    exact (declared_inductive_arity_isTypeRelE (MRProd.proj1 declc)).
    apply lift_typing_weaken_ctxE with (Γ := []); tas.
    eapply isTypeRelE_isTypeE.
    apply oib.(onArity).
  Qed.

End OnConstructor.

Section OnConstructorExt.

  Context {cf} {Σ} {wfΣ : wfE Σ} {ind mdecl idecl cdecl}
    (declc : declared_constructor Σ ind mdecl idecl cdecl).

  Lemma on_constructor_instE u :
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_localE Σ (subst_instance u
      (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cstr_args cdecl)) *
    ∑ inst,
    spine_substE Σ
            (subst_instance u
              (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,,
                cstr_args cdecl))
            (ListDef.map (subst_instance u)
              (to_extended_list_k (ind_params mdecl) #|cstr_args cdecl|) ++
            ListDef.map (subst_instance u) (cstr_indices cdecl)) inst
            (subst_instance u (ind_params mdecl) ,,,
            subst_instance u (ind_indices idecl)).
  Proof using declc wfΣ.
    intros cu.
    destruct (on_constructor_substE declc) as [[wfext wfl] [inst sp]].
    eapply wf_local_subst_instanceE in wfl; eauto. split=> //.
    eapply spine_subst_instE in sp; eauto.
    rewrite map_app in sp. rewrite -subst_instance_app_ctx.
    eexists ; eauto.
  Qed.

End OnConstructorExt.

Lemma invert_red_mkApps_tRelE {cf} {Σ} {wfΣ : wfE Σ} {Γ n d args t'} :
  nth_error Γ n = Some d -> decl_body d = None ->
  Σ ;;; Γ ⊢ mkApps (tRel n) args ⇝ t' ->
  ∑ args' : list term, t' = mkApps (tRel n) args' × red_terms Σ Γ args args'.
Proof.
  intros hnth db r. exact (invert_red_mkApps_tRel_cb hnth db r).
Qed.

Lemma closed_red_mkAppsE {cf} {Σ} {wfΣ : wfE Σ} Γ f u u' :
  is_closed_context Γ ->
  is_open_term Γ f ->
  red_terms Σ Γ u u' ->
  Σ ;;; Γ ⊢ mkApps f u ⇝ mkApps f u'.
Proof.
  intros onΓ ont red.
  eapply into_closed_red; auto.
  - apply red_mkApps; auto.
    solve_all. apply X.
  - rewrite PCUICOnFreeVars.on_free_vars_mkApps ont.
    eapply closed_red_terms_open_left in red; solve_all.
Qed.

Lemma ws_cumul_pb_mkApps_eqE {cf} {Σ} {wfΣ : wfE Σ} Γ f f' u u' :
  is_closed_context Γ ->
  is_open_term Γ f ->
  is_open_term Γ f' ->
  compare_term_napp Σ Σ Cumul #|u| f f' ->
  ws_cumul_pbE_terms Σ Γ u u' ->
  Σ ;;; Γ ⊢E mkApps f u ≤ mkApps f' u'.
Proof.
  intros onΓ onf onf' eqf equ.
  destruct (PCUICEtaI5A2.All2_JoinE_ex Σ Γ u u' (WT_join equ)) as (lx & ly & hlx & hly & hxy).
  constructor.
  - exact onΓ.
  - rewrite on_free_vars_mkApps onf (WT_open_left equ) //.
  - rewrite on_free_vars_mkApps onf' (WT_open_right equ) //.
  - apply (PCUICEtaI5A2.BE_JoinE Σ Γ Cumul _ _ (mkApps f lx) (mkApps f' ly)).
    + exact (PCUICEtaI5A2.BE_mkApps_args Σ Γ _ _ _ hlx).
    + exact (PCUICEtaI5A2.BE_mkApps_args Σ Γ _ _ _ hly).
    + rewrite !PCUICEtaI5A2.canon_mkApps.
      apply PCUICEtaI5A2.RF_mkApps; [|apply All2_map; exact hxy].
      rewrite Nat.add_0_l length_map -(All2_length hlx).
      apply PCUICEtaI5A2.RF_canon. exact (eq_term_upto_univ_napp_finst _ _ _ _ _ _ _ eqf).
Qed.

Lemma ws_cumul_pb_LetIn_substE {cf} {Σ} {wfΣ : wfE Σ} {le Γ na na' b b' ty ty' t t'} :
  is_open_term Γ (tLetIn na b ty t) ->
  is_open_term Γ (tLetIn na' b' ty' t') ->
  Σ ;;; Γ ⊢E t {0 := b} ≤[le] t' {0 := b'} ->
  Σ ;;; Γ ⊢E tLetIn na b ty t ≤[le] tLetIn na' b' ty' t'.
Proof.
  intros onl onr cum.
  transitivity (t {0 := b}).
  eapply red_ws_cumul_pbE. eapply into_closed_red; eauto.
  eapply red1_red. econstructor. eauto with fvs.
  transitivity (t' {0 := b'}) => //.
  eapply red_ws_cumul_pbE_inv.
  eapply into_closed_red; eauto.
  eapply red1_red; econstructor. eauto with fvs.
Qed.

(** A reduction that holds in every context survives the substitution of the
    inductives for the arities, in any context of the right length: the arities and
    [Γ] have no bodies. *)
Lemma red_subst_indsE {cf} {Σ} {wfΣ : wfE Σ} {ind mdecl Γ Δ a b u v} :
  assumption_context Γ ->
  closed_ctx (ind_arities mdecl ,,, Γ)@[u] ->
  #|Δ| = #|Γ| ->
  is_open_term Δ (subst (ind_subst mdecl ind v) #|Γ| a) ->
  (forall Ξ, red Σ Ξ a b) ->
  red Σ Δ (subst (ind_subst mdecl ind v) #|Γ| a) (subst (ind_subst mdecl ind v) #|Γ| b).
Proof.
  intros ass cl lenΔ op R.
  move: cl; rewrite closedn_subst_instance_context => cl.
  have r := R ([] ,,, ind_arities mdecl ,,, Γ).
  eapply (substitution_untyped_red_cb (s := ind_subst mdecl ind v)) in r.
  - rewrite app_context_nil_l in r.
    eapply PCUICRedTypeIrrelevance.context_pres_let_bodies_red; [|exact r].
    apply assumption_context_pres_let_bodies; [|len; lia].
    apply assumption_context_fold, ass.
  - apply untyped_subslet_assumption_context; [apply assumption_context_arities_context|].
    rewrite /ind_subst inds_length /ind_arities. len.
  - move: op. rewrite -!is_open_term_closed lenΔ => op.
    eapply closed_upwards; [exact (closedn_subst_eq' _ 0 #|Γ| _ op)|].
    rewrite /ind_subst inds_length. len; lia.
  - rewrite on_free_vars_ctx_on_ctx_free_vars -is_closed_ctx_closed app_context_nil_l.
    exact cl.
Qed.

Lemma ws_cumul_pb_red_stepE {cf} {Σ} {wfΣ : wfE Σ} {pb Δ a a' b b'} :
  is_closed_context Δ -> is_open_term Δ a -> is_open_term Δ b ->
  red Σ Δ a a' -> red Σ Δ b b' ->
  (is_open_term Δ a' -> is_open_term Δ b' -> Σ ;;; Δ ⊢E a' ≤[pb] b') ->
  Σ ;;; Δ ⊢E a ≤[pb] b.
Proof.
  intros clΔ opa opb ra rb IH.
  have ra' : Σ ;;; Δ ⊢ a ⇝ a' by eapply into_closed_red.
  have rb' : Σ ;;; Δ ⊢ b ⇝ b' by eapply into_closed_red.
  transitivity a'; [now eapply red_ws_cumul_pbE|].
  transitivity b'; [|now eapply red_ws_cumul_pbE_inv].
  apply IH; eapply closed_red_open_right_cb; eassumption.
Qed.

(** A step of [positive_inds_conv] through a reduction [t ⇝ t'] that holds in every
    context. *)
Lemma positive_inds_conv_red_stepE {cf} {Σ} {wfΣ : wfE Σ} {ind mdecl Γ Δ t t' u u'} :
  assumption_context Γ ->
  closed_ctx (ind_arities mdecl ,,, Γ)@[u] ->
  #|Δ| = #|Γ| -> closed_ctx Δ ->
  (forall Ξ, red Σ Ξ t@[u'] t'@[u']) ->
  is_open_term Δ (subst (ind_subst mdecl ind u) #|Γ| t@[u']) ->
  is_open_term Δ (subst (ind_subst mdecl ind u') #|Γ| t@[u']) ->
  (is_open_term Δ (subst (ind_subst mdecl ind u) #|Γ| t'@[u']) ->
   is_open_term Δ (subst (ind_subst mdecl ind u') #|Γ| t'@[u']) ->
   Σ ;;; Δ ⊢E subst (ind_subst mdecl ind u) #|Γ| t'@[u'] =
     subst (ind_subst mdecl ind u') #|Γ| t'@[u']) ->
  Σ ;;; Δ ⊢E subst (ind_subst mdecl ind u) #|Γ| t@[u'] =
    subst (ind_subst mdecl ind u') #|Γ| t@[u'].
Proof.
  intros ass cl lenΔ clΔ R onl onr IH.
  eapply ws_cumul_pb_red_stepE; [now rewrite -is_closed_ctx_closed|exact onl|exact onr| | |exact IH].
  - exact (red_subst_indsE ass cl lenΔ onl R).
  - exact (red_subst_indsE ass cl lenΔ onr R).
Qed.

(** The [pos_arg_ass_red] case of [positive_inds_conv]: both substituted domains
    reduce to the same closed term. *)
Lemma positive_inds_conv_ass_redE {cf} {Σ} {wfΣ : wfE Σ} {ind mdecl Γ Δ na ty ty' h l u u'} :
  assumption_context Γ ->
  closed_ctx (ind_arities mdecl ,,, Γ)@[u] ->
  #|Δ| = #|Γ| -> closed_ctx Δ ->
  whd_rel true Σ.1 (arities_context (ind_bodies mdecl) ,,, Γ) ty [] h l ->
  closedn #|Γ| (mkApps h l) ->
  is_open_term Δ (subst (ind_subst mdecl ind u) #|Γ| (tProd na ty ty')@[u']) ->
  is_open_term Δ (subst (ind_subst mdecl ind u') #|Γ| (tProd na ty ty')@[u']) ->
  (closed_ctx (ind_arities mdecl ,,, (vass na ty :: Γ))@[u] ->
   forall Δ', #|Δ'| = Datatypes.S #|Γ| -> closed_ctx Δ' ->
   is_open_term Δ' (subst (ind_subst mdecl ind u) (Datatypes.S #|Γ|) ty'@[u']) ->
   is_open_term Δ' (subst (ind_subst mdecl ind u') (Datatypes.S #|Γ|) ty'@[u']) ->
   assumption_context (vass na ty :: Γ) ->
   Σ ;;; Δ' ⊢E subst (ind_subst mdecl ind u) (Datatypes.S #|Γ|) ty'@[u'] =
     subst (ind_subst mdecl ind u') (Datatypes.S #|Γ|) ty'@[u']) ->
  Σ ;;; Δ ⊢E subst (ind_subst mdecl ind u) #|Γ| (tProd na ty ty')@[u'] =
    subst (ind_subst mdecl ind u') #|Γ| (tProd na ty ty')@[u'].
Proof.
  intros ass cl lenΔ clΔ wh clhl onl onr IH.
  have clΔ' : is_closed_context Δ by rewrite -is_closed_ctx_closed.
  cbn in onl, onr |- *.
  move/andP: onl => [onl onl']. move/andP: onr => [onr onr'].
  have clty : closedn (#|Γ| + #|ind_bodies mdecl|) ty.
  { move: onl. rewrite -is_open_term_closed lenΔ => onl0.
    move: (closedn_subst_eq' _ 0 #|Γ| _ onl0).
    rewrite closedn_subst_instance /ind_subst inds_length. intros h0; exact h0. }
  have R : forall Ξ, red Σ Ξ ty@[u'] (mkApps h l)@[u'].
  { intros Ξ. exact (whd_rel_red_inst u' Ξ ass wh). }
  eapply ws_cumul_pbE_Prod; [reflexivity| |].
  - eapply ws_cumul_pb_red_stepE; [exact clΔ'|exact onl|exact onr| | |].
    + exact (red_subst_indsE ass cl lenΔ onl R).
    + exact (red_subst_indsE ass cl lenΔ onr R).
    + intros _ _. rewrite !subst_closedn ?closedn_subst_instance //.
      apply ws_cumul_pbE_refl; [exact clΔ'|].
      rewrite -is_open_term_closed lenΔ closedn_subst_instance //.
  - apply IH.
    + cbn. apply andb_and; split; [exact cl|].
      rewrite closedn_subst_instance. eapply closed_upwards; [exact clty|]. len; lia.
    + cbn. now rewrite lenΔ.
    + rewrite /snoc closedn_ctx_cons clΔ /=.
      move: onl. rewrite -is_open_term_closed => onl0.
      try unfold closed_decl; cbn. by rewrite onl0.
    + rewrite /= shiftnP_S. exact onl'.
    + rewrite /= shiftnP_S. exact onr'.
    + now constructor.
Qed.

Lemma positive_inds_convE {cf} {Σ} {wfΣ : wfE Σ}
  {ind mdecl idecl NI Γ p u u' Δ} :
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  cmp_opt_variance (compare_universe Σ) Cumul
    (match ind_variance mdecl with Some var => Variance var | None => AllEqual end) u u' ->
  nested_variance_ok mdecl ->
  closed_ctx (ind_arities mdecl ,,, Γ)@[u] ->
  positive_cstr_arg Σ.1 mdecl NI Γ p ->
  NI = [] ->
  #|Δ| = #|Γ| ->
  closed_ctx Δ ->
  is_open_term Δ
    (subst (ind_subst mdecl ind u) #|Γ| p@[u']) ->
  is_open_term Δ
    (subst (ind_subst mdecl ind u') #|Γ| p@[u']) ->
  assumption_context Γ ->
  Σ ;;; Δ ⊢E
    subst (ind_subst mdecl ind u) #|Γ| p@[u'] =
    subst (ind_subst mdecl ind u') #|Γ| p@[u'].
Proof.
  intros decli cu ru nv cl pos eqNI lenΔ clΔ onl onr ass; pose proof (MRProd.proj1 decli) as declm.
  revert NI Γ p pos eqNI cl Δ lenΔ clΔ onl onr ass.
  apply (positive_cstr_arg_mrect Σ.1 mdecl
    (fun NI Γ t _ => NI = [] ->
      closed_ctx (ind_arities mdecl ,,, Γ)@[u] ->
      forall Δ, #|Δ| = #|Γ| -> closed_ctx Δ ->
      is_open_term Δ
        (subst (ind_subst mdecl ind u) #|Γ| t@[u']) ->
      is_open_term Δ
        (subst (ind_subst mdecl ind u') #|Γ| t@[u']) ->
      assumption_context Γ ->
      Σ ;;; Δ ⊢E
        subst (ind_subst mdecl ind u) #|Γ| t@[u'] =
        subst (ind_subst mdecl ind u') #|Γ| t@[u'])
    (fun NI Γ l _ => NI = [] ->
      closed_ctx (ind_arities mdecl ,,, Γ)@[u] ->
      forall Δ, #|Δ| = #|Γ| -> closed_ctx Δ ->
      forallb (is_open_term Δ)
        (ListDef.map (fun p => subst (ind_subst mdecl ind u) #|Γ| p@[u']) l) ->
      forallb (is_open_term Δ)
        (ListDef.map (fun p => subst (ind_subst mdecl ind u') #|Γ| p@[u']) l) ->
      assumption_context Γ ->
      ws_cumul_pbE_terms Σ Δ
        (ListDef.map (fun p => subst (ind_subst mdecl ind u) #|Γ| p@[u']) l)
        (ListDef.map (fun p => subst (ind_subst mdecl ind u') #|Γ| p@[u']) l))
    (fun _ _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ => True)); intros.
  - subst NI. rewrite !subst_closedn ?closedn_subst_instance //.
    eapply ws_cumul_pbE_refl; eauto with fvs.
    rewrite -is_closed_ctx_closed. exact H2.
    move: H3. now rewrite subst_closedn ?closedn_subst_instance.
  - subst NI.
    rewrite !subst_instance_mkApps !subst_mkApps /= /ind_subst.
    destruct m as [le [lt nth]].
    destruct (Nat.leb #|Γ| k) eqn:eqle; [|apply Nat.leb_nle in eqle; lia].
    rewrite !inds_spec !rev_mapi !nth_error_mapi nth /=.
    pose (clsub := H2).
    eapply ws_cumul_pbE_Ind.
    + unfold cumul_Ind_univ, cmp_global_instance, cmp_global_instance_gen. simpl.
      unshelve epose proof (declm' := declared_minductive_to_gen declm); eauto.
      assert (declared_inductive Σ
        {| inductive_mind := inductive_mind ind;
           inductive_ind := Nat.pred #|ind_bodies mdecl| - (k - #|Γ|) |} mdecl i).
      { split; auto. simpl. rewrite -nth MRList.nth_error_rev; lia_f_equal. }
      unshelve epose proof (decli' := declared_inductive_to_gen H); eauto.
      rewrite (declared_inductive_lookup_gen decli') //.
      len. rewrite e /ind_realargs. len.
      rewrite Nat.leb_refl.
      destruct (ind_variance mdecl) eqn:var => /=.
      * change (cmp_opt_variance (compare_universe Σ) Conv (Variance l0) u u').
        eapply (cmp_opt_variance_no_covariant (compare_universe Σ)); tea.
        move: nv. rewrite /nested_variance_ok var //.
      * exact ru.
    + rewrite -is_closed_ctx_closed. exact clsub.
    + do 2 eapply All2_map. eapply All_All2_refl. solve_all.
      rewrite !subst_closedn ?closedn_subst_instance //.
      eapply ws_cumul_pbE_refl; eauto with fvs.
      rewrite -is_closed_ctx_closed. exact clsub.
      rewrite -is_open_term_closed H1.
      now rewrite closedn_subst_instance.
  - subst NI. destruct n as [j [e [hnth _ _ _ _]]].
    rewrite MRList.nth_error_nil in hnth; discriminate.
  - subst NI.
    rewrite !subst_instance_mkApps !subst_mkApps in H4 H5 |- *.
    rewrite !on_free_vars_mkApps /= in H4 H5.
    rewrite !List.map_map in H4 H5.
    eapply ws_cumul_pbE_Ind.
    + eapply cmp_global_instance_refl; typeclasses eauto.
    + rewrite -is_closed_ctx_closed. exact H3.
    + rewrite -{1 2}(firstn_skipn k args) !map_app.
      eapply All2_app.
      * rewrite !List.map_map. eapply X; eauto.
        all: rewrite -MRList.firstn_map; eapply All_forallb, All_firstn, forallb_All; assumption.
      * do 2 eapply All2_map. eapply All_All2_refl. solve_all.
        rewrite !subst_closedn ?closedn_subst_instance //.
        eapply ws_cumul_pbE_refl; eauto with fvs.
        rewrite -is_closed_ctx_closed. exact H3.
        rewrite -is_open_term_closed H2.
        now rewrite closedn_subst_instance.
  - subst NI. cbn.
    eapply ws_cumul_pb_LetIn_substE; eauto with fvs.
    + rewrite !subst_instance_subst !distr_subst /= /subst1 in X.
      eapply X; eauto.
      * eapply closed_red_open_right_cb.
        eapply (into_closed_red
          (t := subst (ind_subst mdecl ind u) #|Γ| (tLetIn na b ty ty')@[u'])).
        { eapply red1_red; econstructor; eauto with fvs. }
        { rewrite -is_closed_ctx_closed. exact H2. }
        { exact H3. }
      * eapply closed_red_open_right_cb.
        eapply (into_closed_red
          (t := subst (ind_subst mdecl ind u') #|Γ| (tLetIn na b ty ty')@[u'])).
        { eapply red1_red; econstructor; eauto with fvs. }
        { rewrite -is_closed_ctx_closed. exact H2. }
        { exact H4. }
  - subst NI. cbn.
    eapply ws_cumul_pbE_Prod.
    + reflexivity.
    + rewrite !subst_closedn ?closedn_subst_instance //.
      eapply ws_cumul_pbE_refl; eauto with fvs.
      rewrite -is_closed_ctx_closed. exact H2.
      rewrite -is_open_term_closed H1.
      now rewrite closedn_subst_instance.
    + cbn -[closedn_ctx] in X.
      eapply X; eauto.
      all: try (apply assumption_context_vass; assumption).
      * cbn. apply andb_and; split.
        { exact H0. }
        { rewrite closedn_subst_instance. eapply closed_upwards; eauto. len; lia. }
      * cbn. lia.
      * cbn. rewrite H2 /=.
        move: H3. cbn. move/andP=> [h _].
        move: h. rewrite -is_open_term_closed. len.
      * move: H3. cbn. move/andP=> [_ h]. by rewrite /= shiftnP_S.
      * move: H4. cbn. move/andP=> [_ h]. by rewrite /= shiftnP_S.
  - eapply positive_inds_conv_red_stepE; try eassumption.
    + intros Ξ. eapply whd_rel_red_inst; eassumption.
    + intros. eapply X; eassumption.
  - eapply positive_inds_conv_ass_redE; try eassumption.
    intros. eapply X; eassumption.
  - eapply (positive_inds_conv_red_stepE (t' := mkApps (tRel k) l')); try eassumption.
    + intros Ξ. rewrite !subst_instance_mkApps. apply red_mkApps; [reflexivity|].
      eapply arg_whd_red_inst; eassumption.
    + intros. eapply X; eassumption.
  - constructor.
  - cbn in H3, H4 |- *.
    move/andP: H3 => [h3 h3']. move/andP: H4 => [h4 h4'].
    (* [ws_cumul_pbE_terms] is a Definition (base's is a notation): the tail goal is the
       [All2] underneath, which [eauto] does not match against the induction hypothesis. *)
    constructor; [eauto|eapply X0; eauto].
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
Qed.

Lemma positive_cstr_arg_subst_closedE {cf} {Σ} {wfΣ : wfE Σ} {ind mdecl idecl Γ t pb u u'} :
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  closedn #|Γ| t ->
  Σ ;;; (ind_arities mdecl)@[u] ,,, Γ@[u] ⊢E t@[u] ≤[pb] t@[u'] ->
  Σ ;;; subst_context (ind_subst mdecl ind u) 0 Γ@[u] ⊢E
    subst (ind_subst mdecl ind u) #|Γ| t@[u] ≤[pb] subst (ind_subst mdecl ind u') #|Γ| t@[u'].
Proof.
  intros decli cu clt cum.
  pose proof (MRProd.proj1 decli) as declm.
  rewrite -(app_context_nil_l (_ ,,, _)) app_context_assoc in cum.
  eapply untyped_substitution_ws_cumul_pbE in cum; eauto.
  2:{ eapply subslet_untyped_subsletE, subslet_indsE; eauto. }
  2:{ eapply inds_is_open_terms. }
  rewrite !subst_closedn ?closedn_subst_instance //.
  rewrite !subst_closedn ?closedn_subst_instance // in cum; len; auto.
  now rewrite app_context_nil_l in cum.
Qed.

(** A step of [positive_cstr_arg_subst] through a reduction [t ⇝ t'] that holds in
    every context and under every universe instance. *)
Lemma positive_cstr_arg_subst_red_stepE {cf} {Σ} {wfΣ : wfE Σ} {ind mdecl Γ t t' pb u u'} :
  assumption_context Γ ->
  closed_ctx (ind_arities mdecl ,,, Γ)@[u] ->
  (forall w Ξ, red Σ Ξ t@[w] t'@[w]) ->
  Σ ;;; (ind_arities mdecl)@[u] ,,, Γ@[u] ⊢E t@[u] ≤[pb] t@[u'] ->
  (Σ ;;; (ind_arities mdecl)@[u] ,,, Γ@[u] ⊢E t'@[u] ≤[pb] t'@[u'] ->
   Σ ;;; subst_context (ind_subst mdecl ind u) 0 Γ@[u] ⊢E
     subst (ind_subst mdecl ind u) #|Γ| t'@[u] ≤[pb] subst (ind_subst mdecl ind u') #|Γ| t'@[u']) ->
  Σ ;;; subst_context (ind_subst mdecl ind u) 0 Γ@[u] ⊢E
    subst (ind_subst mdecl ind u) #|Γ| t@[u] ≤[pb] subst (ind_subst mdecl ind u') #|Γ| t@[u'].
Proof.
  intros ass cl R cum IH.
  have clΓ := ws_cumul_pbE_is_closed_context cum.
  have opl := ws_cumul_pbE_is_open_term_left cum.
  have opr := ws_cumul_pbE_is_open_term_right cum.
  have lenΔ : #|subst_context (ind_subst mdecl ind u) 0 Γ@[u]| = #|Γ| by len.
  have opl' := is_open_term_subst_inds (ind := ind) (w := u) lenΔ opl.
  have opr' := is_open_term_subst_inds (ind := ind) (w := u') lenΔ opr.
  eapply ws_cumul_pb_red_stepE.
  - rewrite -is_closed_ctx_closed. now apply closed_ctx_subst_ind_arities.
  - exact opl'.
  - exact opr'.
  - exact (red_subst_indsE ass cl lenΔ opl' (R u)).
  - exact (red_subst_indsE ass cl lenΔ opr' (R u')).
  - intros _ _. apply IH.
    transitivity t@[u].
    { eapply red_ws_cumul_pbE_inv, into_closed_red; [apply R|exact clΓ|exact opl]. }
    transitivity t@[u']; [exact cum|].
    eapply red_ws_cumul_pbE, into_closed_red; [apply R|exact clΓ|exact opr].
Qed.

(** The nested case of [positive_cstr_arg_subst]: the arguments of the nested inductive
    are related by conversion, the block-free tail is untouched by both substitutions,
    and the positive prefix is moved from [inds u] to [inds u'] by [positive_inds_conv]. *)
Lemma positive_cstr_arg_subst_nestedE {cf} {Σ} {wfΣ : wfE Σ}
  {ind mdecl idecl NI Γ ind' ui args k u u'} :
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  cmp_opt_variance (compare_universe Σ) Cumul (match ind_variance mdecl with Some var => Variance var | None => AllEqual end) u u' ->
  nested_variance_ok mdecl ->
  closed_ctx (ind_arities mdecl ,,, Γ)@[u] ->
  NI = [] ->
  All (closedn #|Γ|) (skipn k args) ->
  positive_args Σ.1 mdecl NI Γ (firstn k args) ->
  Σ ;;; subst_instance u (ind_arities mdecl) ,,, subst_instance u Γ ⊢E
    subst_instance u (mkApps (tInd ind' ui) args) ≤ subst_instance u' (mkApps (tInd ind' ui) args) ->
  assumption_context Γ ->
  Σ ;;; subst_context (ind_subst mdecl ind u) 0 (subst_instance u Γ) ⊢E
    subst (ind_subst mdecl ind u) #|Γ| (subst_instance u (mkApps (tInd ind' ui) args)) ≤
    subst (ind_subst mdecl ind u') #|Γ| (subst_instance u' (mkApps (tInd ind' ui) args)).
Proof.
  intros decli cu ru nv cl eqNI hcl hpa cum ass.
  pose proof (MRProd.proj1 decli) as declm.
  subst NI. eapply positive_args_All in hpa.
  have clΔ : closed_ctx (subst_context (ind_subst mdecl ind u) 0 (subst_instance u Γ)).
  { now eapply closed_ctx_subst_ind_arities. }
  pose proof (ws_cumul_pbE_is_closed_context cum) as clctx.
  rewrite !subst_instance_mkApps !subst_mkApps /= in cum |- *.
  pose proof (ws_cumul_pbE_is_open_term_right cum) as opr.
  rewrite on_free_vars_mkApps /= in opr.
  eapply invert_cumul_ind_indE in cum as [[_ hu] hargs].
  eapply ws_cumul_pbE_Ind_finst.
  - rewrite !length_map in hu |- *. exact hu.
  - rewrite -is_closed_ctx_closed. exact clΔ.
  - rewrite -(app_context_nil_l (_ ,,, _)) app_context_assoc in hargs.
    eapply ws_cumul_pbE_terms_subst in hargs.
    3:{ eapply subslet_untyped_subsletE, (subslet_indsE (u:=u)); eauto. }
    3:{ eapply subslet_untyped_subsletE, (subslet_indsE (u:=u)); eauto. }
    2:{ rewrite app_context_nil_l; eauto with fvs.
        move: clctx. rewrite on_free_vars_ctx_app => /andP[] //. }
    2:{ pose proof (inds_is_open_terms [] ind mdecl u).
        solve_all. eapply All_All2; tea.
        cbn; intros. eapply ws_cumul_pbE_refl; eauto. }
    rewrite app_context_nil_l in hargs. len in hargs.
    etransitivity; [exact hargs|].
    rewrite -{1 2}(firstn_skipn k args) !map_app.
    eapply All2_app.
    + have opr' : All (fun p => is_open_term (subst_instance u (ind_arities mdecl) ,,, subst_instance u Γ)
        (subst_instance u' p)) (firstn k args).
      { move: opr. rewrite -{1}(firstn_skipn k args) map_app forallb_app => /andP[h _].
        eapply forallb_All in h. now eapply All_map_inv in h. }
      rewrite !List.map_map. eapply All2_map, All_All2_refl.
      eapply (All_mix hpa) in opr'. eapply All_impl; tea. cbn. intros p [pp op].
      eapply positive_inds_convE; tea.
      * reflexivity.
      * now len.
      * eapply is_open_term_subst_inds; [now len|exact op].
      * eapply is_open_term_subst_inds; [now len|exact op].
    + rewrite !List.map_map. eapply All2_map, All_All2_refl. solve_all.
      rewrite !subst_closedn ?closedn_subst_instance //.
      eapply ws_cumul_pbE_refl.
      * rewrite -is_closed_ctx_closed. exact clΔ.
      * rewrite -is_open_term_closed. len. now rewrite closedn_subst_instance.
Qed.

Lemma positive_cstr_arg_substE {cf} {Σ} {wfΣ : wfE Σ} {ind mdecl idecl Γ t u u'} :
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  cmp_opt_variance (compare_universe Σ) Cumul (match ind_variance mdecl with Some var => Variance var | None => AllEqual end) u u' ->
  closed_ctx (ind_arities mdecl ,,, Γ)@[u] ->
  Σ ;;; subst_instance u (ind_arities mdecl) ,,, subst_instance u Γ ⊢E (subst_instance u t) ≤ (subst_instance u' t) ->
  positive_cstr_arg Σ.1 mdecl [] Γ t ->
  assumption_context Γ ->
  (Σ ;;; subst_context (ind_subst mdecl ind u) 0 (subst_instance u Γ) ⊢E
    (subst (ind_subst mdecl ind u) #|Γ| (subst_instance u t)) ≤
     subst (ind_subst mdecl ind u') #|Γ| (subst_instance u' t)).
Proof.
  intros decli cu ru cl cum pos ass.
  pose proof (MRProd.proj1 decli) as declm.
  remember ([] : nested_insts) as NI eqn:eqNI in pos.
  induction pos.
  - eapply positive_cstr_arg_subst_closedE; tea.

  - epose proof (ws_cumul_pbE_is_closed_context cum).
    rewrite !subst_instance_mkApps !subst_mkApps in cum |- *.
    simpl in cum. eapply ws_cumul_pbE_mkApps_tRel in cum; eauto; cycle 1.
    { destruct m as [? [? ?]].
      rewrite nth_error_app_ge // subst_instance_length //
         nth_error_subst_instance.
      unfold ind_arities, arities_context.
      rewrite rev_map_spec -List.map_rev.
      rewrite MRList.nth_error_map e0 /=. reflexivity. }
    1:trivial.
    rewrite -(app_context_nil_l (_ ,,, _)) app_context_assoc in cum.
    eapply ws_cumul_pbE_terms_subst in cum.
    3:{ eapply subslet_untyped_subsletE, (subslet_indsE (u:=u)); eauto. }
    3:{ eapply subslet_untyped_subsletE, (subslet_indsE (u:=u)); eauto. }
    2:{ rewrite app_context_nil_l; eauto with fvs.
        move: H. rewrite on_free_vars_ctx_app => /andP[] //. }
    2:{ pose proof (inds_is_open_terms [] ind mdecl u).
        solve_all. eapply All_All2; tea.
        cbn; intros. eapply ws_cumul_pbE_refl; eauto. }
    rewrite app_context_nil_l // in cum. len in cum.
    rewrite /ind_subst.
    eapply ws_cumul_pb_mkApps_eqE => //; destruct m as [? [? ?]].
    * move: cl. rewrite -is_closed_ctx_closed => cl.
      apply (closedn_ctx_subst 0 0). cbn. len.
      rewrite !closedn_subst_instance_context. rewrite /ind_arities in cl.
      move: cl. rewrite closedn_subst_instance_context closedn_ctx_app. len. move/andP=> []//.
      eapply closed_inds.
    * cbn. destruct (leb_spec_Set #|Γ| k); try lia.
      destruct (nth_error (inds _ _ _) _) eqn:hnth.
      eapply inds_nth_error in hnth as [n ->]. now cbn.
      eapply nth_error_None in hnth. len in hnth; lia.
    * cbn. destruct (leb_spec_Set #|Γ| k); try lia.
      destruct (nth_error (inds _ _ _) _) eqn:hnth.
      eapply inds_nth_error in hnth as [n ->]. now cbn.
      eapply nth_error_None in hnth. len in hnth; lia.
    * rewrite !length_map.
      simpl. destruct (Nat.leb #|Γ| k) eqn:eqle.
      eapply Nat.leb_le in eqle.
      rewrite /ind_subst !inds_spec !rev_mapi !nth_error_mapi.
      unshelve epose proof (declm' := declared_minductive_to_gen declm); eauto.
      rewrite H2 /=. simpl. constructor. simpl.
      unfold cmp_global_instance, cmp_global_instance_gen. simpl.
      assert(declared_inductive Σ {|
      inductive_mind := inductive_mind ind;
      inductive_ind := Nat.pred #|ind_bodies mdecl| - (k - #|Γ|) |} mdecl i).
      { split; auto. simpl. rewrite -H2 MRList.nth_error_rev; lia_f_equal. }
      unfold lookup_inductive.
      unshelve epose proof (H0' := declared_inductive_to_gen H3); eauto.
      rewrite (declared_inductive_lookup_gen H0') //.
      rewrite e /ind_realargs.
      rewrite (Nat.leb_refl) //.
      eapply Nat.leb_nle in eqle. lia.
    * do 2 eapply All2_map. do 2 eapply All2_map_inv in cum.
      eapply All2_All in cum. apply All_All2_refl.
      solve_all.
      now rewrite !subst_closedn ?closedn_subst_instance // in b |- *.

  - subst NI.
    match goal with h : nested_inst_ok [] _ _ _ |- _ =>
      destruct h as [j [e [hnth _ _ _ _]]]; rewrite MRList.nth_error_nil in hnth; discriminate end.

  - eapply positive_cstr_arg_subst_nestedE; eauto.

  - simpl. simpl in cum.
    eapply ws_cumul_pb_LetIn_substE. eauto.
    { rewrite -(app_context_nil_l (_ ,,, _)) app_context_assoc in cum.
      eapply untyped_substitution_ws_cumul_pbE in cum.
      2:{ eapply subslet_untyped_subsletE, (subslet_indsE (u:=u)); eauto. }
      2:{ eapply inds_is_open_terms. }
      rewrite app_context_nil_l /= in cum.
      rewrite /ind_subst. eapply ws_cumul_pbE_is_open_term_left in cum.
      now rewrite subst_instance_length in cum. }
    { eapply ws_cumul_pbE_is_open_term_right in cum.
    { rewrite -(app_context_nil_l (_ ,,, _)) app_context_assoc in cum.
      eapply is_open_term_subst_gen in cum.
      2:{ rewrite // app_context_nil_l //.
          rewrite - !is_closed_ctx_closed.
          now rewrite subst_instance_app_ctx in cl. }
          (* eapply wf_local_closed_context in cl. eauto with fvs. } *)
      { cbn -[PCUICOnFreeVars.on_free_vars] in cum.
        rewrite subst_instance_length app_context_nil_l in cum. eapply cum. }
      1-2:eapply inds_is_open_terms. len. len. } }
    rewrite !subst_instance_subst /= in IHpos.
    rewrite !distr_subst /= in IHpos. rewrite /subst1.
    eapply IHpos => //.
    eapply ws_cumul_pbE_LetIn_inv in cum; eauto.

  - simpl in cum |- *.
    eapply ws_cumul_pbE_Prod_Prod_inv_l in cum as [eqna dom codom]; eauto.
    eapply ws_cumul_pbE_Prod; eauto.
    * rewrite -(app_context_nil_l (_ ,,, _)) app_context_assoc in dom.
      eapply untyped_substitution_ws_cumul_pbE in dom; rewrite ?app_context_nil_l; eauto.
      2:{ eapply subslet_untyped_subsletE, subslet_indsE; eauto. }
      2:{ eapply inds_is_open_terms. }
      rewrite ?app_context_nil_l ?closedn_subst_instance // in dom.
      rewrite !subst_closedn ?closedn_subst_instance // in dom; len; auto.
      now rewrite !subst_closedn ?closedn_subst_instance.
    * cbn -[closedn_ctx] in IHpos. rewrite subst_context_snoc in IHpos.
      rewrite length_map Nat.add_0_r in IHpos. eapply IHpos; eauto.
      all: try (apply assumption_context_vass; assumption).
      cbn. rewrite cl /=. len.
      rewrite closedn_subst_instance.
      eapply closed_upwards; eauto; lia.

  - eapply (positive_cstr_arg_subst_red_stepE (t' := mkApps h l)); tea.
    + intros w0 Ξ. eapply whd_rel_red_inst; tea.
    + intros cum'. eapply IHpos; eauto.

  - simpl in cum |- *.
    eapply ws_cumul_pbE_Prod_Prod_inv_l in cum as [eqna dom codom]; eauto.
    eapply ws_cumul_pbE_Prod; eauto.
    * eapply (positive_cstr_arg_subst_red_stepE (t' := mkApps h l)); tea.
      + intros w0 Ξ. eapply whd_rel_red_inst; tea.
      + intros dom'. eapply positive_cstr_arg_subst_closedE; tea.
    * have clty := ws_cumul_pbE_is_open_term_left dom.
      rewrite -is_open_term_closed closedn_subst_instance in clty. len in clty.
      cbn -[closedn_ctx] in IHpos. rewrite subst_context_snoc in IHpos.
      rewrite length_map Nat.add_0_r in IHpos. eapply IHpos; eauto.
      all: try (apply assumption_context_vass; assumption).
      cbn. rewrite cl /=. len.
      rewrite closedn_subst_instance.
      eapply closed_upwards; [exact clty|lia].

  - eapply (positive_cstr_arg_subst_red_stepE (t' := mkApps (tRel k) l')); tea.
    + intros w0 Ξ. rewrite !subst_instance_mkApps. apply red_mkApps; [reflexivity|].
      eapply arg_whd_red_inst; tea.
    + intros cum'. eapply IHpos; eauto.
Qed.

Lemma positive_cstr_closed_args_subst_aritiesE {cf} {Σ} {wfΣ : wfE Σ} {u u' Γ}
   {i ind mdecl idecl cdecl ind_indices cs} :
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  on_constructor cumulSpecE0 (PCUICTyping.lift_typing typingE) (Σ.1, ind_universes mdecl) mdecl i idecl ind_indices cdecl cs ->
  cmp_opt_variance (compare_universe Σ) Cumul (match ind_variance mdecl with Some var => Variance var | None => AllEqual end) u u' ->
  closed_ctx (subst_instance u (ind_params mdecl)) ->
  wf_localE Σ (subst_instance u (ind_arities mdecl ,,, smash_context [] (ind_params mdecl) ,,, Γ)) ->
  All_local_env (fun Γ j => positive_cstr_arg Σ.1 mdecl [] ([] ,,, (smash_context [] (ind_params mdecl) ,,, Γ)) (j_typ j)) Γ ->
  assumption_context Γ ->
  ws_cumul_ctx_pbE_rel Cumul Σ (subst_instance u (ind_arities mdecl) ,,,
      subst_instance u
        (smash_context [] (PCUICEnvironment.ind_params mdecl)))
   (subst_instance u Γ) (subst_instance u' Γ) ->
  ws_cumul_ctx_pbE_rel Cumul Σ (subst_instance u (smash_context [] (PCUICEnvironment.ind_params mdecl)))
    (subst_context (ind_subst mdecl ind u) (context_assumptions (ind_params mdecl)) (subst_instance u Γ))
    (subst_context (ind_subst mdecl ind u') (context_assumptions (ind_params mdecl)) (subst_instance u' Γ)).
Proof.
  intros * decli cu onc onv cl wf cpos ass.
  intros [clΓ cum].
  split.
  rewrite -is_closed_ctx_closed.
  rewrite subst_instance_smash.
  now apply closedn_smash_context.
  revert cum.
  induction cpos; simpl; rewrite ?subst_context_nil ?subst_context_snoc; try solve [constructor; auto].
  all:rewrite ?length_map; intros cv; depelim cv; depelim wf.
  eassert (isTypeRelE Σ
  (subst_instance u (ind_arities mdecl) ,,,
   subst_instance u (smash_context [] (ind_params mdecl) ,,, Γ))
  (subst_instance u t) _).
  { rewrite -subst_instance_app_ctx app_context_assoc //. eassumption. }
  depelim a.
  all:constructor.
  - eapply IHcpos. auto. now depelim ass. apply cv.
  - constructor; auto. cbn in *.
    eapply positive_cstr_arg_substE in t0; eauto. len.
    move: t0.
    rewrite app_context_nil_l subst_instance_app_ctx subst_context_app.
    rewrite PCUICSpine.closed_ctx_subst //.
    rewrite subst_instance_smash.
    now apply closedn_smash_context.
    len.
    rewrite app_context_nil_l !subst_instance_app_ctx // app_context_assoc //.
    eapply ws_cumul_pbE_is_closed_context in eqt.
    now rewrite is_closed_ctx_closed.
    rewrite app_context_nil_l !subst_instance_app_ctx // app_context_assoc //.
    all: try (rewrite app_context_nil_l; apply assumption_context_app_inv;
      [now depelim ass|apply smash_context_assumption_context; constructor]).
  - exfalso; now depelim ass.
  - exfalso; now depelim ass.
Qed.

Lemma positive_cstr_closed_argsE {cf} {Σ} {wfΣ : wfE Σ} {u u'}
  {ind mdecl idecl cdecl} :
  declared_constructor Σ ind mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  cmp_opt_variance (compare_universe Σ) Cumul (match ind_variance mdecl with Some var => Variance var | None => AllEqual end) u u' ->
 ws_cumul_ctx_pbE_rel Cumul Σ (subst_instance u (ind_arities mdecl) ,,,
    subst_instance u
      (smash_context [] (PCUICEnvironment.ind_params mdecl)))
 (smash_context []
    (subst_instance u
       (expand_lets_ctx (PCUICEnvironment.ind_params mdecl)
          (cstr_args cdecl))))
 (smash_context []
    (subst_instance u'
       (expand_lets_ctx (PCUICEnvironment.ind_params mdecl)
          (cstr_args cdecl)))) ->

  ws_cumul_ctx_pbE_rel Cumul Σ (subst_instance u (smash_context [] (PCUICEnvironment.ind_params mdecl)))
      (subst_context (inds (inductive_mind ind.1) u (ind_bodies mdecl)) (context_assumptions (ind_params mdecl))
       (smash_context []
          (subst_instance u
             (expand_lets_ctx (PCUICEnvironment.ind_params mdecl)
                (cstr_args cdecl)))))
       (subst_context (inds (inductive_mind ind.1) u' (ind_bodies mdecl)) (context_assumptions (ind_params mdecl))
           ((smash_context []
          (subst_instance u'
             (expand_lets_ctx (PCUICEnvironment.ind_params mdecl)
                (cstr_args cdecl)))))).
Proof.
  intros * declc cu Ru cx.
  pose proof (on_declared_constructorE declc) as [[onmind oib] [cs [? onc]]].
  pose proof (onc.(on_ctype_positive)) as cpos.
  rewrite onc.(cstr_eq) in cpos. unf_env.
  rewrite -it_mkProd_or_LetIn_app in cpos.
  eapply positive_cstr_it_mkProd_or_LetIn in cpos as [hpars _].
  rewrite smash_context_app_expand in hpars.
  eapply All_local_env_app_inv in hpars as [_hpars hargs].
  rewrite expand_lets_smash_context /= expand_lets_k_ctx_nil /= in hargs.
  eapply positive_cstr_closed_args_subst_aritiesE in hargs; eauto.
  split.
  - rewrite !subst_instance_smash /ind_subst /= in hargs |- *.
    eapply hargs; eauto.
  - destruct hargs as [hargs hwf]. now rewrite !subst_instance_smash in hwf |- *.
  - eapply declc.
  - eapply closed_wf_localE; eauto; eapply on_minductive_wf_paramsE; eauto; eapply declc.
  - rewrite -app_context_assoc. rewrite -(expand_lets_smash_context _ []).
    rewrite -smash_context_app_expand subst_instance_app_ctx subst_instance_smash.
    eapply wf_local_smash_endE; eauto.
    rewrite -subst_instance_app_ctx app_context_assoc.
    now epose proof (on_constructor_instE declc _ cu) as [wfarpars _].
  - eapply smash_context_assumption_context. constructor.
  - now rewrite !(subst_instance_smash _ (expand_lets_ctx _ _)).
Qed.

Lemma consistent_instance_poly_lengthE {cf} {Σ} {wfΣ : wfE Σ} {inst cstrs u} :
  consistent_instance_ext Σ (Polymorphic_ctx (inst, cstrs)) u ->
  #|u| = #|inst|.
Proof.
  rewrite /consistent_instance_ext /consistent_instance.
  intuition auto.
Qed.

Lemma consistent_instance_validE {cf} {Σ} {wfΣ : wfE Σ} {inst cstrs u} :
  consistent_instance_ext Σ (Polymorphic_ctx (inst, cstrs)) u ->
  check_univs ->
  forall v, Universes.satisfies v (global_ext_constraints Σ) -> Universes.satisfies v (subst_instance_cstrs u cstrs).
Proof. rewrite /consistent_instance_ext /=; intros [_ [_ v]] cu.
    red in v. now rewrite cu in v.
Qed.

Lemma LSet_in_global_boundedE {cf:checker_flags} {Σ : global_env} {l} k :
  wfE Σ -> LevelSet.In l (global_levels Σ) ->
  closedu_level k l.
Proof.
  simpl.
  intros wf. eapply not_var_global_levelsE in wf.
  intros hin. specialize (wf _ hin). simpl in wf.
  destruct l; simpl in *; congruence.
Qed.

Lemma on_udecl_prop_poly_boundedE {cf:checker_flags} Σ inst cstrs :
  wfE Σ ->
  on_udecl_prop Σ (Polymorphic_ctx (inst, cstrs)) ->
  closedu_cstrs #|inst| cstrs.
Proof.
  rewrite /on_udecl_prop.
  intros wfΣ nlevs.
  red.
  rewrite /closedu_cstrs.
  intros x incstrs.
  specialize (nlevs x incstrs).
  destruct x as [[l1 p] l2].
  destruct nlevs.
  apply LevelSetProp.Dec.F.union_1 in H.
  apply LevelSetProp.Dec.F.union_1 in H0.
  destruct H. eapply LSet_in_poly_bounded in H.
  destruct H0. eapply LSet_in_poly_bounded in H0. simpl. now rewrite H H0.
  eapply (LSet_in_global_boundedE #|inst|) in H0 => //. simpl.
  now rewrite H H0.
  eapply (LSet_in_global_boundedE #|inst|) in H => //. simpl.
  destruct H0. eapply LSet_in_poly_bounded in H0. simpl. now rewrite H H0.
  eapply (LSet_in_global_boundedE #|inst|) in H0 => //. simpl.
  now rewrite H H0.
Qed.

Lemma ws_cumul_pb_inst_varianceE {cf} {le} {Σ} {wfΣ : wfE Σ} {mdecl l v i i' u u' Γ} :
  on_udecl_prop Σ (ind_universes mdecl) ->
  on_variance Σ (ind_universes mdecl) (Some l) ->
  variance_universes (PCUICEnvironment.ind_universes mdecl) l = Some (v, i, i') ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  cmp_universe_instance_variance (compare_universe Σ) Cumul l u u' ->
  forall t t',
  (Σ.1, v) ;;; Γ@[i] ⊢E t@[i] ≤[le] t'@[i'] ->
  Σ ;;; Γ@[u] ⊢E t@[u] ≤[le] t'@[u'].
Proof.
  intros onu onv vari cu cu' Ru t t'.
  intros cum.
  destruct Σ as [Σ univs].
  pose proof (variance_universes_insts onv) as (v' & ui & ui' & [hv cstrs cui cui' len0 len1 eqi']).
  rewrite vari in hv; noconf hv.
  subst i.
  pose proof (consistent_instance_length cu).
  pose proof (consistent_instance_length cu').
  rewrite -eqi' in H, H0.
  rewrite -H0 in cum.
  assert (subst_instance (u' ++ u) (lift_instance #|u'| i') = u) as subsu.
  { rewrite closedu_subst_instance_lift //.
    now rewrite H. rewrite eqi'.
    erewrite subst_instance_id_mdecl => //. eauto. }
  assert (subst_instance (u' ++ u) i' = u') as subsu'.
  { rewrite closedu_subst_instance_app //.
    rewrite H0 //. rewrite eqi' //.
    erewrite subst_instance_id_mdecl => //. eauto. }
  eapply (subst_instance_ws_cumul_pbE (Σ := (Σ, v)) _ (u' ++ u)) in cum; auto.
  rewrite !subst_instance_two in cum.
  rewrite subst_instance_two_context in cum.
  now rewrite subsu subsu' in cum.
  unfold valid_constraints. destruct check_univs eqn:checku => //.
  unfold valid_constraints0.
  intros v0 sat.
  rewrite satisfies_subst_instance_ctr //.
  simpl in sat.
  generalize sat.
  unfold global_ext_constraints.
  rewrite satisfies_union /= => [[satcstrs satglob]].
  rewrite satisfies_union. split; auto.
  2:{ rewrite -satisfies_subst_instance_ctr //.
      rewrite equal_subst_instance_cstrs_mono //.
      red; apply monomorphic_global_constraintE; auto. }
  destruct (ind_universes mdecl) as [|[inst cstrs']].
  { simpl in vari => //. }
  cbn in cstrs. subst v; cbn.
  rewrite !satisfies_union. len.
  len in len1.
  intuition auto.
  - rewrite -satisfies_subst_instance_ctr //.
    assert(ConstraintSet.Equal (subst_instance_cstrs u' cstrs')
        (subst_instance_cstrs (u' ++ u) cstrs')) as <-.
    { rewrite closedu_subst_instance_cstrs_app //.
      rewrite (consistent_instance_poly_lengthE cu').
      eapply on_udecl_prop_poly_boundedE; eauto. }
    eapply consistent_instance_validE in cu'; eauto.
  - rewrite -satisfies_subst_instance_ctr // -H0.
    assert(ConstraintSet.Equal (subst_instance_cstrs u cstrs')
        (subst_instance_cstrs (u' ++ u) (lift_constraints #|u'| cstrs'))) as <-.
    { rewrite closedu_subst_instance_cstrs_lift //.
      rewrite H -H0 (consistent_instance_poly_lengthE cu').
      eapply on_udecl_prop_poly_boundedE; eauto. }
    eapply consistent_instance_validE in cu; eauto.
  - rewrite -satisfies_subst_instance_ctr //.
    rewrite subst_instance_variance_cstrs //.
    rewrite -H0 subsu subsu'.
    assert (#|u| = #|u'|) as lenu by lia.
    assert (#|l| = #|u|) as lenlu. now rewrite len1 H.
    clear -checku Ru sat lenu lenlu.
    induction l in u, u', Ru, lenu, lenlu |- *. simpl in *. destruct u, u';
    intro; rewrite ConstraintSetFact.empty_iff //.
    destruct u, u' => //; simpl in *.
    depelim Ru. rename H into Ra.
    specialize (IHl u u' Ru). do 2 forward IHl by lia.
    destruct a => //; intros x; rewrite ConstraintSetFact.add_iff;
    intros [<-|inx]; auto.
    + do 5 red in Ra; rewrite checku in Ra;
      specialize (Ra _ sat); simpl in Ra.
      constructor. lia.
    + do 4 red in Ra. rewrite checku in Ra.
      specialize  (Ra _ sat).
      constructor. now rewrite !Universes.Universe.val_make in Ra.
Qed.

(* [Γ' Γ] typed as base's compiled binders ([list (context_decl term)]; inference gives [context]) *)
Lemma All2_fold_instE {cf} {le} {Σ} {wfΣ : wfE Σ} mdecl l v i i' u u' (Γ' Γ : list PCUICEnvironment.context_decl) :
  on_udecl_prop Σ (ind_universes mdecl) ->
  on_variance Σ (ind_universes mdecl) (Some l) ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  variance_universes (PCUICEnvironment.ind_universes mdecl) l = Some (v, i, i') ->
  cmp_universe_instance_variance (compare_universe Σ) Cumul l u u' ->
  ws_cumul_ctx_pbE_rel le (Σ.1, v) (subst_instance i Γ') (subst_instance i Γ) (subst_instance i' Γ) ->
  ws_cumul_ctx_pbE_rel le Σ (subst_instance u Γ') (subst_instance u Γ) (subst_instance u' Γ).
Proof.
  unfold PCUICCumulativitySpec.cumul_ctx_rel.
  intros onu onv cu cu' vari Ru.
  induction Γ as [|[na [b|] ty] tl]; simpl.
  - constructor. destruct X.
    now rewrite !is_closed_subst_inst in i0 *.
    constructor.
  - intros H; depelim H.
    econstructor; auto.
    now rewrite !is_closed_subst_inst in i0 *.
    depelim a. simpl.
    rewrite -subst_instance_app_ctx in a, a0. simpl in a0 |- *.
    depelim a0.
    constructor; auto. apply IHtl; auto.
    red. split. 2:apply a. auto. constructor; try reflexivity.
    rewrite -subst_instance_app_ctx.
    eapply ws_cumul_pb_inst_varianceE; eauto.
    rewrite -subst_instance_app_ctx.
    cbn.
    eapply ws_cumul_pb_inst_varianceE; eauto.
  - intros H; depelim H; simpl in *. depelim a.
    constructor; auto.
    rewrite !is_closed_subst_inst // in i0 *.
    constructor; auto.
    now apply IHtl.
    rewrite -subst_instance_app_ctx in a0.
    rewrite -subst_instance_app_ctx.
    rewrite /map_decl /= in a0 *.
    depelim a0; constructor; eauto using ws_cumul_pb_inst_varianceE.
Qed.

Lemma cumul_ctx_relSpec_AlgoE {cf} {Σ} {wfΣ : wfE Σ} {Γ Δ Δ'}
  (c : PCUICCumulativitySpec.cumul_ctx_rel cumulSpecE0 Σ Γ Δ Δ') :
  is_closed_context (Γ ,,, Δ) ->
  is_closed_context (Γ ,,, Δ') ->
  ws_cumul_ctx_pbE_rel Cumul Σ Γ Δ Δ'.
Proof.
  intros wf wf'.
  eapply ws_cumul_ctx_pbE_rel_app.
  apply into_ws_cumul_ctx_pbE; eauto with fvs.
  apply All2_fold_app; auto.
  (* base's [reflexivity] resolves to [cumul_ctx_refl], at [Cumul]; that instance has no [JoinE]
     twin (the instance [conv_ctx_reflE] is at [Conv]) *)
  { eapply PCUICConfluence.All2_fold_refl. intros ? [na [b|] ty]; constructor; try reflexivity; apply JoinE_refl. }
  induction c; try solve[constructor; auto].
  move: wf; rewrite /= on_free_vars_ctx_snoc => /andP[] h0 h1.
  move: wf'; rewrite /= on_free_vars_ctx_snoc => /andP[] h2 h3.
  destruct p; constructor; inv_on_free_vars; auto.
  - eapply into_ws_cumul_pbE_spec in eqt; fvs.
    constructor; auto. now eapply ws_cumul_pbE_forget in eqt.
    len. rewrite (All2_fold_length c). now len in h3.
  - eapply into_ws_cumul_pbE_spec in eqt; eauto.
    eapply into_ws_cumul_pbE_spec in eqb; eauto; fvs.
    constructor; auto.
    now apply ws_cumul_pbE_forget in eqb.
    now apply ws_cumul_pbE_forget in eqt.
    len. rewrite (All2_fold_length c) //. now len in H.
    len. rewrite (All2_fold_length c) //. now len in H0.
Qed.

Lemma cmp_global_instance_ind_invE {cf} {Σ} {wfΣ : wfE Σ} cmp_universe pb ind mdecl idecl napp u u' :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  declared_inductive Σ ind mdecl idecl ->
  cmp_global_instance Σ cmp_universe pb (IndRef ind) napp u u' ->
  ((context_assumptions (ind_indices idecl) + context_assumptions (ind_params mdecl) <= napp ×
    ∑ l, ind_variance mdecl = Some l ×
      cmp_universe_instance_variance cmp_universe pb l u u') +
  cmp_universe_instance (cmp_universe Conv) u u')%type.
Proof.
  intros Hsub decli.
  destruct (on_declared_inductiveE decli) as [onmind oib].
  unshelve epose proof (decli' := declared_inductive_to_gen decli); eauto.
  unfold cmp_global_instance, cmp_global_instance_gen, global_variance.
  rewrite (declared_inductive_lookup_gen decli').
  simpl. rewrite context_assumptions_app.
  elim: leb_spec_Set => // comp. 2: now right.
  destruct ind_variance eqn:indv => //. 2: now right.
  move/cmp_opt_variance_var_dec => [|H]. 1: now right.
  left.
  now repeat eexists.
Qed.

Lemma inductive_cumulative_indicesE {cf} {Σ} {wfΣ : wfE Σ} :
  forall {ind mdecl idecl u u' napp},
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  cmp_ind_universes Σ ind napp u u' ->
  forall Γ pars pars' parsubst parsubst',
  spine_substE Σ Γ pars parsubst (subst_instance u (ind_params mdecl)) ->
  spine_substE Σ Γ pars' parsubst' (subst_instance u' (ind_params mdecl)) ->
  ws_cumul_pbE_terms Σ Γ pars pars' ->
  let indctx := subst_instance u idecl.(ind_indices) in
  let indctx' := subst_instance u' idecl.(ind_indices) in
  let pindctx := subst_context parsubst 0 indctx in
  let pindctx' := subst_context parsubst' 0 indctx' in
  ws_cumul_ctx_pbE_rel Cumul Σ Γ (smash_context [] pindctx) (smash_context [] pindctx').
Proof.
  intros * decli.
  destruct (on_declared_inductiveE decli) as [onmind oib].
  intros cu cu' Ru Γ * spu spu' cpars *.
  unshelve epose proof (decli' := declared_inductive_to_gen decli); eauto.
  assert (onu : on_udecl_prop Σ (ind_universes mdecl)).
  { eapply (weaken_lookup_on_global_env' _ _ _ wfΣ (MRProd.proj1 decli')). }
  unfold cmp_global_instance, cmp_global_instance_gen.
  assert (closed_ctx
    (subst_instance u
      (PCUICEnvironment.ind_params mdecl))) as clpu.
  { eapply closed_wf_localE; eauto; eapply on_minductive_wf_paramsE; eauto.
    destruct decli; eauto. }
  assert (closed_ctx
  (subst_instance u'
    (PCUICEnvironment.ind_params mdecl)))  as clpu'.
  {  eapply closed_wf_localE; eauto; eapply on_minductive_wf_paramsE; eauto.
     destruct decli; eauto. }
  assert (closed_ctx
    (subst_instance u
      (smash_context [] (PCUICEnvironment.ind_params mdecl)))) as clspu.
  { rewrite subst_instance_smash. now eapply closedn_smash_context. }
  assert (wf_localE Σ
  (smash_context []
     (subst_instance u (PCUICEnvironment.ind_params mdecl)) ,,,
   smash_context []
     (subst_instance u
        (expand_lets_ctx (PCUICEnvironment.ind_params mdecl)
           (ind_indices idecl))))).
  { pose proof (on_minductive_wf_params_indices_instE decli _ cu) as wf.
    eapply wf_local_smash_contextE in wf; auto.
    rewrite subst_instance_app_ctx smash_context_app_expand in wf.
    rewrite expand_lets_smash_context expand_lets_k_ctx_nil in wf.
    now rewrite PCUICInductiveInversion.subst_instance_expand_lets_ctx. }
  have clu' : is_closed_context (Γ,,, (ind_params mdecl)@[u']).
  { rewrite -is_closed_ctx_closed.
    rewrite closedn_ctx_app /=.
    rewrite (closed_wf_localE _ (spine_dom_wfE _ _ _ _ _ spu)) /=.
    eapply closedn_ctx_upwards; tea. lia. }
  eapply cmp_global_instance_ind_invE in Ru as [(comp & l & indv & Ru) | Ru]; tea; tc.
  { pose proof (oib.(onIndices)) as respv.
    rewrite indv in respv.
    simpl in respv.
    unfold ind_respects_variance in respv.
    destruct variance_universes as [[[v i] i']|] eqn:vu => //.
    pose proof (onVariance onmind) as onvari.
    rewrite indv in onvari.
    eapply cumul_ctx_relSpec_AlgoE in respv.
    2:{ move/wf_local_closed_contextE: X.
        rewrite - !(subst_instance_smash _ _ []).
        rewrite - !subst_instance_app_ctx !is_closed_subst_inst //.
        now rewrite expand_lets_smash_context. }
    2:{ move/wf_local_closed_contextE: X.
        rewrite - !(subst_instance_smash _ _ []).
        rewrite - !subst_instance_app_ctx !is_closed_context_subst_instance !is_closed_subst_inst //.
        rewrite !on_free_vars_ctx_app is_closed_subst_inst.
        rewrite expand_lets_smash_context /= //. len. }
    eapply All2_fold_instE in respv.
    7:eauto. all:eauto. move: respv.
    rewrite !expand_lets_smash_context.
    autorewrite with pcuic.
    rewrite !subst_instance_smash /= => args. cbn in args.
    eapply (weaken_ws_cumul_ctx_pbE_rel (Γ := Γ)) in args => //; eauto with fvs.
    2:{ eapply wf_local_closed_contextE. apply spu. }
    pose proof (spine_subst_smashE spu) as sspu.
    pose proof (spine_subst_smashE spu') as sspu'.
    eapply (substitution_ws_cumul_ctx_pbE_subst_conv (Γ := Γ) (Γ'' := []) (s := List.rev pars) (s' := List.rev pars')) in args.
    2:{ eapply All2_rev => //. }
    2:{ eapply subslet_untyped_subsletE, sspu. }
    2:{ eapply subslet_untyped_subsletE, sspu'. }
    2:{ eapply is_closed_context_smash_end => //. }
    move: args.
    rewrite subst_context_nil /= - !smash_context_subst /= subst_context_nil; len.
    rewrite !subst_instance_subst_context.
    rewrite !PCUICUnivSubstitutionConv.subst_instance_extended_subst.
    rewrite (subst_context_subst_context (List.rev pars)) /=; len.
    rewrite -(spine_subst_extended_substE spu).
    rewrite !subst_instance_lift_context. len.
    rewrite subst_context_lift_context_cancel.
    len. rewrite (context_subst_length2 spu); len; lia.
    rewrite (subst_context_subst_context (List.rev pars')) /=; len.
    rewrite -(spine_subst_extended_substE spu').
    len. rewrite subst_context_lift_context_cancel.
    len. rewrite (context_subst_length2 spu'); len; lia.
    now rewrite subst_context_nil. }
  simpl. intros.
  { rewrite /pindctx /pindctx' /indctx /indctx'.
    rewrite !(smash_context_subst []).
    eapply (substitution_ws_cumul_ctx_pbE_subst_conv (Γ'' := [])); eauto.
    3:eapply subslet_untyped_subsletE, spu.
    3:eapply subslet_untyped_subsletE, spu'.
    2:{ eapply spine_subst_convE; eauto.
        eapply (weaken_ws_cumul_ctx_pbE_rel (Γ' := [])).
        eapply spine_dom_wfE in spu. eauto with fvs.
        eapply PCUICWsCumulEtaCtx.subst_instance_ws_cumul_ctx_pbE_rel => //.
        rewrite app_context_nil_l //.
        rewrite closedn_subst_instance_context in clpu.
        now rewrite -is_closed_ctx_closed. }
    simpl.
    rewrite -(subst_instance_smash u _ []).
    rewrite -(subst_instance_smash u' _ []).
    eapply PCUICWsCumulEtaCtx.subst_instance_ws_cumul_ctx_pbE_rel => //.
    rewrite -app_context_assoc.
    rewrite is_closed_context_weaken //.
    eapply spine_dom_wfE in spu. eauto with fvs.
    rewrite -(is_closed_context_subst_instance _ _ u).
    rewrite -subst_instance_app_ctx.
    rewrite is_closed_subst_inst.
    eapply is_closed_context_smash_end.
    epose proof (declared_inductive_closed_pars_indicesE decli).
    now rewrite -is_closed_ctx_closed. }
Qed.

Lemma subslet_projs_smashE {cf:checker_flags} (Σ : global_env_ext) i mdecl idecl :
  forall (wfΣ : wfE Σ.1)
  (Hdecl : declared_inductive Σ.1 i mdecl idecl),
  match ind_ctors idecl return Type with
  | [cdecl] =>
    on_projections mdecl (inductive_mind i) (inductive_ind i)
     idecl (ind_indices idecl) cdecl ->
     forall Γ t u,
     let indsubst := inds (inductive_mind i) u (ind_bodies mdecl) in
     untyped_subslet Γ
     (projs_inst i (ind_npars mdecl) (context_assumptions (cstr_args cdecl)) t)
     (lift_context 1 0 (subst_context (inds (inductive_mind i) u (ind_bodies mdecl))
        (context_assumptions (ind_params mdecl))
        (subst_instance u (expand_lets_ctx (ind_params mdecl) (smash_context [] (cstr_args cdecl))))))
  | _ => True
  end.
Proof.
  intros wfΣ Hdecl.
  destruct ind_ctors as [|cdecl []] eqn:hcdecl => //.
  intros onp. simpl. intros Γ t u.
  destruct onp.
  assert (#|PCUICEnvironment.ind_projs idecl| >=
  PCUICEnvironment.context_assumptions (cstr_args cdecl)). lia.
  clear on_projs_all.
  induction (cstr_args cdecl) as [|[? [] ?] ?].
  - simpl. constructor.
  - simpl. apply IHc. now simpl in H.
  - simpl. rewrite smash_context_acc /=. simpl.
    rewrite /subst_decl {2}/map_decl /=.
    rewrite /expand_lets_ctx {1}/map_decl /= /expand_lets_k_ctx.
    rewrite !lift_context_snoc /= subst_context_snoc /=; len.
    rewrite !subst_context_snoc.
    rewrite lift_context_snoc.
    constructor. apply IHc. simpl in H. lia.
Qed.

Lemma projection_cumulative_indicesE {cf} {Σ} {wfΣ : wfE Σ} :
  forall {mdecl idecl cdecl p pdecl u u' },
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  on_udecl_prop Σ (ind_universes mdecl) ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  cmp_ind_universes Σ p.(proj_ind) (ind_npars mdecl) u u' ->
  Σ ;;; projection_context p.(proj_ind) mdecl idecl u ⊢E
    subst_instance u pdecl.(proj_type) ≤ subst_instance u' pdecl.(proj_type).
Proof.
  intros * declp onudecl cu cu' Ru.
  unshelve epose proof (declp' := declared_projection_to_gen declp); eauto.
  epose proof (declared_projection_constructor declp') as declc.
  unshelve epose proof (declc' := declared_constructor_from_gen declc); eauto.
  destruct (on_declared_constructorE declc') as [_ [sort onc]].
  destruct declc'.
  unshelve epose proof (d' := declared_inductive_to_gen d); eauto.
  pose proof (declared_inductive_unique d' (let (x, _) := declp' in let (x, _) := x in x)).
  subst d'.
  epose proof (declared_projection_type_and_eqE wfΣ declp).
  destruct (on_declared_projectionE declp).
  set (oib := declared_inductive_invE _ _ _ _) in p1. simpl in p1, X.
  destruct X as [[? ?] ?].
  destruct p1 as [[[H onps] onidx] onproj].
  simpl in *.
  destruct (ind_cunivs oib) as [|? []] eqn:cseq => //.
  destruct onc as []. noconf e1.
  simpl in *.
  destruct s as [idecl' [idecl'nth _ _ pty pty']].
  rewrite -pty.
  destruct declp' as [[[? ?] ?] ?]. red in H0.
  destruct p0 as [p0 _].
  epose proof (declared_projection_closedE declp).
  pose proof (wf_projection_contextE _ _ declp cu) as wfpctx.
  eapply cmp_global_instance_ind_invE in Ru as [(comp & l & eqv & Ru) | Ru]; eauto; tc; revgoals.
  { (* equal instances: the syntactic comparison, through the inclusion of the base relation *)
    apply ws_cumul_pb_incl_E. eapply ws_cumul_pb_compare.
    { eauto with fvs. }
    { rewrite -is_open_term_closed.
      all:rewrite closedn_subst_instance /projection_context; len; cbn; len.
      all:now rewrite -(declared_minductive_ind_nparsE declp). }
    { rewrite -is_open_term_closed.
      all:rewrite closedn_subst_instance /projection_context; len; cbn; len.
      all:now rewrite -(declared_minductive_ind_nparsE declp). }
    eapply eq_term_leq_term.
      eapply eq_term_upto_univ_subst_instance; eauto. all:tc. }
  simpl in Ru.
  pose proof (on_ctype_variance o _ eqv); eauto.
  red in X.
  destruct variance_universes as [[[udecl inst] inst']|] eqn:vu => //.
  destruct X as [onctx _]. simpl in onctx.
  assert (wf_localE Σ
  ((ind_arities mdecl)@[u],,, smash_context []
      (subst_instance u (PCUICEnvironment.ind_params mdecl)) ,,,
    smash_context []
      (subst_instance u
        (expand_lets_ctx (PCUICEnvironment.ind_params mdecl)
            (cstr_args cdecl))))).
  { pose proof (on_constructor_wf_argsE declp).
    eapply (wf_local_subst_instanceE _ _ _ u) in X; tea.
    2:{ apply (declared_inductive_wf_global_extE _ _ _ _ declp). }
    rewrite PCUICInductiveInversion.subst_instance_expand_lets_ctx.
    rewrite -(expand_lets_smash_context _ []).
    rewrite -app_context_assoc -(smash_context_app_expand []).
    eapply wf_local_smash_endE.
    rewrite - !subst_instance_app_ctx app_context_assoc //. }
  eapply cumul_ctx_relSpec_AlgoE in onctx; auto.
  2:{ move/wf_local_closed_contextE: X.
      rewrite - !(subst_instance_smash _ _ []).
      rewrite - !subst_instance_app_ctx !is_closed_subst_inst //.
      now rewrite expand_lets_smash_context. }
  2:{ move/wf_local_closed_contextE: X.
      rewrite - !(subst_instance_smash _ _ []).
      rewrite - !subst_instance_app_ctx !is_closed_context_subst_instance !is_closed_subst_inst //.
      rewrite !on_free_vars_ctx_app is_closed_subst_inst !on_free_vars_ctx_app.
      rewrite expand_lets_smash_context /= //. len. }
  eapply (All2_fold_instE  _ _ _ _ _ u u') in onctx; eauto.
  2:{ rewrite -eqv.
      eapply (onVariance p0). }
  rewrite subst_instance_app_ctx in onctx.
  epose proof (positive_cstr_closed_argsE declp cu) as hpos.
  rewrite eqv in hpos; simpl in hpos.
  forward hpos. 1: now right.
  rewrite - !(subst_instance_smash _ _ []) in hpos.
  rewrite - !(expand_lets_smash_context _ []) in hpos.
  apply hpos in onctx. clear hpos.
  destruct onctx as [onctx wfctx].
  eapply PCUICRedTypeIrrelevance.All2_fold_nth_ass in wfctx.
  2:{ rewrite nth_error_subst_context; len.
    simpl. rewrite MRList.nth_error_map nth_error_expand_lets.
    erewrite idecl'nth. simpl. reflexivity. }
  2:pcuic.
  move:wfctx => [decl' []].
  destruct idecl' as [na [b|] ty]; simpl => //.
  intros Hd [[] Hd'']; discriminate. simpl.
  rewrite nth_error_subst_context MRList.nth_error_map nth_error_expand_lets idecl'nth.
  rewrite !subst_instance_length !expand_lets_ctx_length !smash_context_length /=.
  simpl. move=> [= <-]. simpl.
  move=> [[Hd _] Hty].
  depelim Hty; simpl in *.
  move: eqt.
  rewrite subst_instance_smash. len. simpl.
  epose proof (subslet_projs_smashE _ _ _ _ _ declp). rewrite e0 in X0.
  unfold projection_context.
  set (ind_decl := vass _ _).
  specialize (X0 onps (smash_context [] (subst_instance u (ind_params mdecl)) ,, ind_decl) (tRel 0) u).
  simpl in X0.
  eapply untyped_subslet_skipn in X0.
  rewrite skipn_lift_context in X0.
  move => Hty.
  eapply (weakening_ws_cumul_pbE (Γ'' := [ind_decl])) in Hty; auto.
  simpl in Hty.
  eapply (untyped_substitution_ws_cumul_pbE (Γ'' := [])) in Hty. 2:eapply X0.
  2:{ clear Hty.
      rewrite forallb_skipn //.
      clear. cbn. len. clear.
      induction (context_assumptions (cstr_args cdecl)); cbn => //. }
  2:{ clear Hty.
      rewrite -is_closed_ctx_closed.
      rewrite closedn_ctx_app /=; len.
      apply/andP; split. eapply closedn_smash_context.
      rewrite closedn_subst_instance_context.
      eapply (declared_inductive_closed_paramsE declp).
      rewrite /ind_decl. cbn. rewrite closedn_mkApps /= //.
      relativize (context_assumptions _); [eapply closedn_to_extended_list|]. len. }
  move: Hty; rewrite subst_context_nil /=.
  rewrite MRList.length_skipn. len. simpl. len.
  rewrite /projection_type /=.
  fold (expand_lets_k (ind_params mdecl) p.(proj_arg) ty).
  rewrite projs_inst_skipn.
  assert (context_assumptions (cstr_args cdecl) -
    Datatypes.S (context_assumptions (cstr_args cdecl) - Datatypes.S p.(proj_arg)) = p.(proj_arg)) as -> by lia.
  clear X.
  rewrite subst_instance_subst.
  rewrite (subst_instance_subst u').
  rewrite !subst_instance_subst [subst_instance _ (projs _ _ _)]subst_instance_projs.
  rewrite - !subst_instance_subst.
  fold (expand_lets_k (ind_params mdecl) p.(proj_arg) ty).
  rewrite commut_lift_subst_rec => /lens.
  rewrite commut_lift_subst_rec => /lens.
  rewrite distr_subst projs_subst_above. lia.
  rewrite (instantiate_indsE declp cu).
  rewrite subst_instance_subst.
  rewrite (instantiate_indsE declp cu').
  rewrite subst_instance_subst.
  rewrite ![subst_instance _ (projs _ _ _)]subst_instance_projs.
  rewrite distr_subst projs_subst_above. lia.
  rewrite projs_length !Nat.add_succ_r Nat.add_0_r /= //.
  rewrite !subst_instance_lift // projs_inst_0 //.
  rewrite p0.(onNpars) //.
Qed.

Lemma wt_ind_app_varianceE {cf} {Σ} {wfΣ : wfE Σ} {Γ ind u l}:
  isTypeE Σ Γ (mkApps (tInd ind u) l) ->
  ∑ mdecl, (lookup_inductive Σ ind = Some mdecl) *
  (global_variance Σ (IndRef ind) #|l| = match ind_variance (fst mdecl) with Some var => Variance var | None => AllEqual end).
Proof.
  intros (_ & s & wat & _).
  pose proof (isType_SortE (PCUICWfUniversesEta.typing_wf_sortE (Σ := Σ) wfΣ wat) (typingE_wf_local wat)) as isS.
  eapply (inversion_mkApps_directE isS) in wat as [ty [sty [Hind [_ Hargs]]]]; auto. clear isS.
  eapply inversion_IndE in Hind as [mdecl [idecl [wfΓ [decli [cu cum]]]]]; auto.
  eapply typing_spine_strengthenE in Hargs; eauto. clear cum.
  2: now eapply isTypeRelE_isTypeE, (declared_inductive_valid_typeE decli).
  exists (mdecl, idecl).
  assert (lookup_inductive Σ ind = Some (mdecl, idecl)).
  { destruct decli as [decli declmi].
    unshelve eapply declared_minductive_to_gen in decli; eauto.
    rewrite /lookup_inductive /lookup_inductive_gen. red in decli.
    rewrite /lookup_minductive /lookup_minductive_gen decli.
    now rewrite declmi. }
  split; auto.
  simpl. unfold lookup_inductive in H; rewrite H.
  simpl.
  eapply (typing_spine_ind_type_invE decli) in Hargs; tea.
  rewrite subst_instance_it_mkProd_or_LetIn subst_instance_app_ctx in Hargs.
  eapply arity_typing_spineE in Hargs; auto.
  destruct Hargs as [Hl Hleq ?]. rewrite Hl.
  len. now rewrite Nat.leb_refl.
Qed.

Lemma ctx_inst_app_weakE `{checker_flags} Σ (wfΣ : wfE Σ.1) ind mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl)Γ (wfΓ : wf_localE Σ Γ) params args u v:
  isTypeE Σ Γ (mkApps (tInd ind u) args) ->
  consistent_instance_ext Σ (ind_universes mdecl) v ->
  ctx_instE Σ Γ params (List.rev (subst_instance v (ind_params mdecl))) ->
  Σ ;;; Γ ⊢E mkApps (tInd ind u) args ≤ mkApps (tInd ind v) (params ++ skipn (ind_npars mdecl) args) ->
  ctx_instE Σ Γ (params ++ skipn (ind_npars mdecl) args)
    (List.rev (subst_instance v (ind_params mdecl ,,, ind_indices idecl))).
Proof.
  intros isTy ? cparams cum.
  pose proof (wt_ind_app_varianceE isTy) as [mdecl' [idecl' gv]].
  unfold lookup_inductive in idecl'.
  unshelve epose proof (isdecl' := declared_inductive_to_gen isdecl); eauto.
  rewrite (declared_inductive_lookup_gen isdecl') in idecl'. noconf idecl'.
  destruct isTy as (_ & ? & ty_args & _).
  eapply invert_type_mkApps_indE in ty_args as [ty_args ?] ; eauto.
  eapply (typing_spine_ind_type_invE isdecl) in ty_args; tea.
  rewrite it_mkProd_or_LetIn_app in ty_args.

  assert (#|args| = ind_npars mdecl + context_assumptions (ind_indices idecl)).
  {
    repeat rewrite PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn in ty_args.
    rewrite -it_mkProd_or_LetIn_app in ty_args.
    apply arity_typing_spineE in ty_args as [eq _ _] ; auto.
    rewrite context_assumptions_app !context_assumptions_subst_instance in eq.
    erewrite declared_minductive_ind_nparsE.
    2: eapply declared_minductive_from_gen; eapply declared_inductive_minductive ; eauto.
    Unshelve. all:eauto. lia.
  }

  assert (cindices : ctx_instE Σ Γ (skipn (ind_npars mdecl) args) (subst_telescope (ctx_inst_subE cparams) 0
    (List.rev (subst_instance v (ind_indices idecl))))).
  {
    rewrite PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn in ty_args.
    erewrite <- (firstn_skipn _ args) in ty_args.
    apply typing_spine_ctx_instE in ty_args as [cparargs ty_indices] ; auto.
    2:{ rewrite firstn_length_le.
        2:{ rewrite context_assumptions_subst_instance.
            symmetry.
            eapply onNpars.
            eapply on_declared_inductiveE ; eauto.

        }
        lia.
    }

    pose proof (declared_minductive_ind_nparsE isdecl).
    eapply invert_cumul_ind_indE in cum as [[_ Ruv0] conv].
    (* [isTypeE] makes [args] the full arity, where the clause of [invert_cumul_ind_indE] is
       base's ([finst_ind_glue_full]). *)
    have Ruv : cmp_ind_universes Σ ind #|args| u v.
    { eapply finst_ind_glue_full; [|exact Ruv0].
      rewrite (head_arity_ind _ _ _ _ isdecl') context_assumptions_app. lia. }
    rewrite -{1}(firstn_skipn (ind_npars mdecl) args) in conv.
    eapply All2_app_inv in conv as [convpars _].
    2:{ apply ctx_inst_length in cparams.
        rewrite context_assumptions_rev in cparams. len in cparams.
        rewrite List.length_firstn. lia. }
    unshelve epose proof (inductive_cumulative_indicesE isdecl c H0 Ruv Γ).
    specialize (X (firstn (ind_npars mdecl) args) params).
    unshelve epose proof (ctx_inst_spine_substE _ cparams); tea.
    { eapply PCUICWeakeningTypEta.weaken_wf_localE; tea. eapply (on_minductive_wf_paramsE isdecl); tea. }
    unshelve epose proof (ctx_inst_spine_substE _ cparargs); tea.
    { eapply PCUICWeakeningTypEta.weaken_wf_localE; tea. eapply (on_minductive_wf_paramsE isdecl); tea. }
    specialize (X _ _ X1 X0 convpars). simpl in X.
    rewrite subst_telescope_subst_context.
    eapply ctx_inst_smashE.
    rewrite subst_instance_it_mkProd_or_LetIn in ty_indices.
    rewrite subst_it_mkProd_or_LetIn in ty_indices.
    rewrite -(app_nil_r (skipn (ind_npars mdecl) args)) in ty_indices.
    eapply typing_spine_ctx_instE in ty_indices as [argsi sp]; tea.
    - eapply ctx_inst_cumulE; tea.
      apply (ctx_inst_smashE.1 argsi).
      { apply All_local_env_app_inv. apply wf_local_smash_endE; tea.
        eapply substitution_wf_localE; tea. eapply X1.
        rewrite -app_context_assoc -subst_instance_app_ctx.
        eapply PCUICWeakeningTypEta.weaken_wf_localE; tea.
        eapply (on_minductive_wf_params_indices_instE isdecl _ c). }
      { apply All_local_env_app_inv. apply wf_local_smash_endE; tea.
        eapply substitution_wf_localE; tea. eapply X0.
        rewrite -app_context_assoc -subst_instance_app_ctx.
        eapply PCUICWeakeningTypEta.weaken_wf_localE; tea.
        eapply (on_minductive_wf_params_indices_instE isdecl _ H0). }
    - len. rewrite List.length_skipn. lia.
  }

  rewrite subst_instance_app_ctx List.rev_app_distr.
  now eapply (ctx_inst_appE cparams).
Qed.

(** Base registers its [isType_is_open_term] on [pcuic] in this file
    ([PCUICInductiveInversion.v:4044]); the twin is registered here, in the twin file, so
    that the set of files the hint reaches is the same on both sides. *)
#[global] Hint Immediate isType_is_open_termE : pcuic.
