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
     PCUICEquality PCUICConfluence PCUICCasesContexts PCUICCasesWfTyp
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
     PCUICConversionEtaCongrFinst PCUICEtaFInst PCUICEtaFInstGlue PCUICEtaJoinSpec
     PCUICWsCumulEtaSubst PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp PCUICEtaA6 PCUICEtaA6Ind
     PCUICEtaA6More PCUICEtaMkAppsTRel
     PCUICEtaI5 PCUICInversionEta PCUICSREtaConv PCUICSpineEta PCUICInductivesEta
     PCUICWsCumulEtaInstancesGlobal PCUICInductiveInversionEta.
From MetaRocq.PCUIC Require PCUICWfUniversesEta PCUICEtaI5A2 PCUICGenerationEta.

From Equations.Type Require Import Relation_Properties.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool.

(** * Inversion facts on inductive types over [typingE], second part

  The E copy of the declarations of [PCUICInductiveInversion] that [PCUICInductiveInversionEta]
  does not hold: the case-predicate and case-branch well-formedness facts and their dependency
  closure inside that file. The E name is the base name with the suffix [E]; the statement is
  base's with only the relations renamed: [typing] -> [typingE], [wf_local] -> [wf_localE],
  [wf] -> [wfE], [isType] -> [isTypeE], [isWfArity] -> [isWfArityE], [spine_subst] ->
  [spine_substE], [subslet] -> [subsletE], [ctx_inst] -> [ctx_instE], [typing_spine] ->
  [PCUICAritiesEta.typing_spineE], [arity_spine] -> [arity_spineE], [convSpec]/[cumulSpec] ->
  [convSpecE]/[cumulSpecE], [Σ ;;; Γ |- t : T] -> [Σ ;;; Γ |-E t : T]. Reduction is unchanged.
  Implicit status, binder names, binder types and positions are base's; section premises are
  base's. Declarations of the base file that mention none of the relations are used from base,
  which this file imports.

  Proof routes that differ from base (the statements are twins):
  - [isType_it_mkProd_or_LetInE] closes the let-binder step with the constructor
    [typeE_Cumul] and [typeE_Sort], where base uses the derived [PCUICTyping.type_Cumul'],
    whose E form is not among the landed definitions; the three arguments are base's three
    goals, with the sort typing in place of base's [isType] of the sort.

  Names that are ambiguous in this file's context are written qualified:
  [PCUICGenerationEta.type_it_mkLambda_or_LetInE] (its file is required, never imported, so
  [PCUICGenerationEta.typing_spineE] does not shadow [PCUICAritiesEta.typing_spineE]), and
  [PCUICWfUniversesEta.typing_wf_sortE]. The own name [isType_it_mkProd_or_LetInE] is a third
  object of that name, as base's [isType_it_mkProd_or_LetIn] is a third object beside
  [PCUICArities]'s and [PCUICInductives]'s; a reference to it in this file resolves to this
  file's, as base's resolves to base's. *)

Local Set SimplIsCbn.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Lemma isType_of_constructorE {cf : checker_flags} Σ mdecl idecl cdecl cstr u Γ :
  wfE Σ.1 -> wf_localE Σ Γ -> declared_constructor Σ.1 cstr mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  isTypeRelE Σ Γ (type_of_constructor mdecl cdecl cstr u) idecl.(ind_relevance).
Proof.
  intros wfΣ wfΓ isdecl h_cuu.
  pose proof (PCUICWeakeningEnvTypEta.on_declared_constructorE isdecl) as ((? & []) & ? & _ & []).
  unshelve eapply declared_constructor_to_gen in isdecl as isdeclgen; tea.
  eapply @lift_sorting_fu_it_impl with (f := fun x => _ (_ x)) (fu := fun x => x@[u]) (tu := on_ctype) => //=.
  1: apply relevance_subst.
  intro Hty.
  replace Γ with ([] ,,, Γ) by apply app_context_nil_l.
  replace (subst0 _ _) with (lift0 #|Γ| (type_of_constructor mdecl cdecl cstr u)).
  2: { rewrite PCUICLiftSubst.lift_closed //. eapply (PCUICClosedTypEta.declared_constructor_closed_typeE isdecl). }
  change (tSort _@[u]) with (lift0 #|Γ| (tSort on_ctype.2.π1)@[u]).
  eapply @weakeningE with (Γ := []) => //.
  rewrite app_context_nil_l => //.
  destruct Σ as (Σ & φ).
  eapply typing_subst_instance'E in Hty => //=; tea.
  change ((tSort _)@[u]) with (subst0 (inds (inductive_mind cstr.1) u (ind_bodies mdecl)) (tSort on_ctype.2.π1)@[u]).
  eapply @PCUICSubstitutionEta.substitutionE with (Δ := []); tea.
  2: rewrite app_context_nil_l; apply Hty.
  2: { epose proof (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl) wfΣ _); eauto. now split. Unshelve. 2: apply isdeclgen.p1.p1. }
  eapply subslet_indsE; tea. exact isdecl.
Qed.

Lemma declared_constructor_valid_tyE {cf:checker_flags} Σ Γ mdecl idecl i n cdecl u :
  wfE Σ.1 ->
  wf_localE Σ Γ ->
  declared_constructor Σ.1 (i, n) mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  isTypeE Σ Γ (type_of_constructor mdecl cdecl (i, n) u).
Proof.
  move=> wfΣ wfΓ declc Hu.
  eapply lift_sorting_forget_rel, isType_of_constructorE; tea.
Qed.

Lemma isType_mkApps_Ind_smashE {cf:checker_flags} {Σ Γ ind u params args} {wfΣ : wfE Σ} {mdecl idecl} :
  declared_inductive Σ.1 ind mdecl idecl ->
  isTypeE Σ Γ (mkApps (tInd ind u) (params ++ args)) ->
  #|params| = ind_npars mdecl ->
  let parctx := subst_instance u mdecl.(ind_params) in
  let argctx := subst_instance u idecl.(ind_indices) in
  spine_substE Σ Γ params (List.rev params) (smash_context [] parctx) ×
  spine_substE Σ Γ args (List.rev args) (smash_context [] (subst_context_let_expand (List.rev params) parctx argctx)) ×
  consistent_instance_ext Σ (ind_universes mdecl) u.
Proof.
  move=> isdecl isty hpars.
  pose proof (isType_wf_localE isty).
  destruct isty as (_ & s & Hs & _).
  eapply invert_type_mkApps_indE in Hs as [sp cu]; tea.
  move=> parctx argctx.
  eapply (typing_spine_ind_type_invE isdecl) in sp; tea.
  rewrite subst_instance_it_mkProd_or_LetIn subst_instance_app_ctx /= in sp.
  eapply arity_typing_spineE in sp as [hle hs [insts sp]]; tea.
  eapply spine_subst_smashE in sp; tea.
  rewrite smash_context_app_expand in sp.
  rewrite List.rev_app_distr in sp.
  pose proof (declared_minductive_ind_nparsE isdecl) as hnpars.
  eapply spine_subst_app_invE in sp as [sppars spargs]; tea.
  2:{ rewrite context_assumptions_smash_context /=. len. }
  len in sppars. len in hle. len in spargs.
  simpl in *.
  assert (context_assumptions (ind_indices idecl) = #|List.rev args|) by (len; lia).
  rewrite H skipn_all_app in sppars, spargs.
  split => //. split => //.
  rewrite -(Nat.add_0_r #|List.rev args|) firstn_app_2 firstn_0 // app_nil_r in spargs.
  rewrite (smash_context_subst []).
  rewrite -(expand_lets_smash_context _ []).
  exact spargs.
Qed.

Lemma positive_cstr_closed_indicesE {cf} {Σ} {wfΣ : wfE Σ} :
  forall {i mdecl idecl cdecl},
  declared_constructor Σ.1 i mdecl idecl cdecl ->
  All (closedn (context_assumptions (cstr_args cdecl) + #|ind_params mdecl|))
    (map (expand_lets (cstr_args cdecl)) (cstr_indices cdecl)).
Proof.
  intros.
  pose proof (on_declared_constructorE H) as [[onmind oib] [cs [hnth onc]]].
  pose proof (onc.(on_ctype_positive)).
  rewrite onc.(cstr_eq) in X. unf_env.
  rewrite -it_mkProd_or_LetIn_app in X.
  eapply positive_cstr_it_mkProd_or_LetIn in X as [hpars hpos].
  rewrite app_context_nil_l in hpos.
  rewrite expand_lets_mkApps in hpos.
  unfold cstr_concl_head in hpos.
  have subsrel := expand_lets_tRel (#|ind_bodies mdecl| - S (inductive_ind i.1))
    (ind_params mdecl ,,, cstr_args cdecl). len in subsrel.
  rewrite (Nat.add_comm #|cstr_args cdecl|) Nat.add_assoc in subsrel.
  rewrite {}subsrel in hpos.
  depelim hpos; solve_discr.
  eapply All_map_inv in a.
  eapply All_app in a as [ _ a].
  eapply All_map; eapply (All_impl a); intros x; len.
  rewrite closedn_expand //.
  exact (declared_inductive_closed_paramsE H).
Qed.

Lemma isType_it_mkProd_or_LetInE {cf:checker_flags} {Σ Γ Δ T} :
  wfE Σ.1 ->
  isTypeE Σ (Γ ,,, Δ) T ->
  isTypeE Σ Γ (it_mkProd_or_LetIn Δ T).
Proof.
  intros wfΣ. revert T.
  induction Δ as [|[na [b|] ty] Δ].
  - now simpl.
  - intros T Hty.
    rewrite /= /mkProd_or_LetIn /=.
    eapply IHΔ.
    apply lift_sorting_it_impl_gen with Hty => // Hs.
    have wf := typingE_wf_local Hs.
    depelim wf.
    eapply typeE_Cumul.
    + econstructor; eauto.
    + eapply typeE_Sort; eauto.
      now eapply PCUICWfUniversesEta.typing_wf_sortE in Hs.
    + eapply convSpecE_cumulSpecE, red1_cumulSpecE.
      repeat constructor.
  - intros T (_ & s & Hs & _).
    apply IHΔ.
    red.
    have wf := typingE_wf_local Hs.
    depelim wf.
    pose proof (lift_sorting_extract l).
    eapply has_sort_isTypeE with (s := Sort.sort_of_product _ s).
    econstructor; eauto.
Qed.

Lemma wf_set_binder_nameE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ} {nas Δ} :
  All2 (fun x y => eq_binder_annot x y.(decl_name)) nas Δ ->
  wf_localE Σ (Γ ,,, Δ) ->
  wf_localE Σ (Γ ,,, map2 set_binder_name nas Δ).
Proof.
  intros ha wf.
  apply All_local_env_app_inv in wf as [wfΓ wfΔ].
  eapply All_local_env_app => //.
  induction wfΔ using All_local_rel_ind1 in nas, ha |- *; depelim ha; cbn. constructor.
  specialize (IHwfΔ _ ha).
  apply All_local_rel_snoc; tas.
  unfold set_binder_name at 2. cbn. rewrite e.
  apply lift_typing_impl with (1 := X) => // ?? Hs.
  eapply context_conversionE; tea.
  1: now eapply All_local_env_app.
  eapply eq_binder_annots_eq_ctx in ha.
  eapply eq_context_upto_names_conv_contextE.
  eapply All2_app.
  2: reflexivity.
  symmetry; apply ha.
Qed.

Lemma WfArity_build_case_predicate_typeE {cf:checker_flags} {Σ Γ ci args mdecl idecl p ps} :
  wfE Σ.1 ->
  declared_inductive Σ.1 ci.(ci_ind) mdecl idecl ->
  isTypeE Σ Γ (mkApps (tInd ci p.(puinst)) (pparams p ++ args)) ->
  let params := firstn (ind_npars mdecl) args in
  wf_sort Σ ps ->
  wf_predicate mdecl idecl p ->
  isWfArityE Σ Γ (it_mkProd_or_LetIn (case_predicate_context ci mdecl idecl p) (tSort ps)).
Proof.
  intros wfΣ isdecl X params wfps wfp.
  split.
  2:{ eexists _, _. rewrite destArity_it_mkProd_or_LetIn. reflexivity. }
  rewrite /case_predicate_context /case_predicate_context_gen.
  have wfΓ := typingE_wf_local X.2.π2.1.
  eapply isType_mkApps_Ind_invE in X; tea.
  destruct X as [parsubst [argsubst [sppars spargs parslen argslen cu]]].
  epose proof (isType_case_predicateE (puinst p) (pparams p) ps wfΓ isdecl cu wfps).
  rewrite (firstn_app_left) /= ?app_nil_r in sppars.
  now rewrite (wf_predicate_length_pars wfp).
  eapply spine_subst_smashE in sppars;tea. specialize (X sppars).
  eapply isType_it_mkProd_or_LetInE; eauto.
  eapply isType_SortE; auto.
  eapply wf_set_binder_nameE.
  now eapply wf_pre_case_predicate_context_gen.
  now eapply isType_it_mkProd_or_LetIn_wf_localE in X.
Qed.

Lemma isType_is_open_termE {cf} {Σ} {wfΣ : wfE Σ} Γ T : isTypeE Σ Γ T -> is_open_term Γ T.
Proof.
  intros (_ & s & hs & _). now apply subject_is_open_termE in hs.
Qed.
#[global] Hint Immediate isType_is_open_termE : pcuic.

Lemma arity_spine_to_extended_listE {cf} {Σ} {wfΣ : wfE Σ} {Γ Δ} T :
  wf_localE Σ (Γ ,,, Δ) ->
  isTypeE Σ (Γ ,,, Δ) T ->
  arity_spineE Σ (Γ ,,, Δ) (lift0 #|Δ| (it_mkProd_or_LetIn Δ T)) (to_extended_list Δ)
    T.
Proof.
  intros hty wf.
  rewrite lift_it_mkProd_or_LetIn Nat.add_0_r.
  pose proof (@all_rels_subst_liftE _ _ _ Δ Γ [] T hty (wf_local_closed_contextE hty)).
  rewrite lift0_id in X. simpl in X.
  rewrite Nat.add_0_r in X.
  rewrite -(app_nil_r (to_extended_list Δ)).
  eapply arity_spine_it_mkProd_or_LetInE; tea.
  rewrite /to_extended_list /to_extended_list_k.
  eapply spine_subst_to_extended_list_kE; tea.
  constructor => //.
  eapply ws_cumul_pbE_eq_le. symmetry. apply X => //. eauto with pcuic.
Qed.

Lemma typing_spine_to_extended_list_k_appE {cf} {Σ} {wfΣ : wfE Σ} {Γ Δ Δ'} {T s T'} :
  isTypeE Σ (Γ ,,, Δ) T ->
  typing_spineE Σ (Γ ,,, Δ ,,, Δ') (lift0 #|Δ'| T) s T' ->
  typing_spineE Σ (Γ ,,, Δ ,,, Δ') (lift0 (#|Δ| + #|Δ'|) (it_mkProd_or_LetIn Δ T))
    (to_extended_list_k Δ #|Δ'| ++ s) T'.
Proof.
  intros isty sp.
  have wf := (typing_spine_wf_localE sp).
  rewrite !lift_it_mkProd_or_LetIn Nat.add_0_r.
  eapply typing_spine_it_mkProd_or_LetIn'E; tea.
  rewrite /to_extended_list /to_extended_list_k.
  rewrite -{1}(Nat.add_0_r #|Δ'|) reln_lift.
  rewrite -Nat.add_comm lift_context_add.
  eapply spine_subst_weakeningE;tea.
  eapply spine_subst_to_extended_list_kE; tea.
  now apply All_local_env_app_inv in wf.
  destruct (All_local_env_app_inv wf) as [].
  epose proof (@all_rels_subst_liftE _ _ _ _ _ Δ' T a).
  eapply typing_spine_strengthenE; tea; revgoals.
  eapply ws_cumul_pbE_eq_le; symmetry.
  rewrite -all_rels_lift Nat.add_comm.
  eapply X. 2:pcuic. eauto with fvs.

  clear X.
  apply lift_sorting_f_it_impl with (f := fun t => _ (_ t)) (tu := isty) => // Hs.
  eapply (weakening_typingE) in Hs; tea.
  eapply (substitutionE (Δ := [])) in Hs.
  2:{ epose proof (spine_subst_to_extended_list_kE a). apply X. }
  eapply (weakening_typingE) in Hs; tea. len in Hs.
  rewrite distr_lift_subst in Hs. len in Hs.
  rewrite all_rels_length in Hs.
  rewrite simpl_lift in Hs; try lia.
  now rewrite Nat.add_comm.
  rewrite -(Nat.add_0_r #|Δ|) -lift_it_mkProd_or_LetIn Nat.add_0_r.
  rewrite -length_app.
  replace #|Δ ++ Δ'| with (#|Δ ,,, Δ'|).
  2:now len.
  eapply isType_liftE; tea. now len.
  rewrite -app_context_assoc.
  rewrite skipn_app List.skipn_all /= Nat.sub_diag skipn_0.
  now eapply isType_it_mkProd_or_LetInE.
Qed.

Lemma wf_case_predicate_contextE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
  {Γ mdecl idecl ci p } {args : list term} :
  declared_inductive Σ ci.(ci_ind) mdecl idecl ->
  isTypeE Σ Γ (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ args)) ->
  wf_predicate mdecl idecl p ->
  let predctx := case_predicate_context ci mdecl idecl p in
  wf_localE Σ (Γ ,,, predctx).
Proof.
  intros isdecl Hc wfp predctx.
  epose proof (WfArity_build_case_predicate_typeE wfΣ isdecl Hc
    (PCUICWfUniverses.wf_sort_type1 Σ) wfp).
  destruct X.
  eapply isType_it_mkProd_or_LetIn_invE in i; tea.
  now eapply isType_wf_localE in i.
Qed.

Lemma case_predicate_context_alphaE {cf : checker_flags}	{Σ : global_env_ext} {wfΣ : wfE Σ} {ind mdecl idecl p Γ} :
  declared_inductive Σ.1 ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) p.(puinst) ->
  let parctx := subst_instance (puinst p) mdecl.(ind_params) in
  spine_substE Σ Γ p.(pparams) (List.rev p.(pparams)) (smash_context [] parctx) ->
  All2 (fun x y => eq_binder_annot x y.(decl_name))
     (forget_types (pcontext p))
    (idecl_binder idecl :: ind_indices idecl) ->
  eq_context_upto_names (case_predicate_context' ind mdecl idecl p)
    (case_predicate_context ind mdecl idecl p).
Proof.
  intros decli cu parctx sp.
  rewrite /case_predicate_context /case_predicate_context_gen /case_predicate_context'.
  rewrite /pre_case_predicate_context_gen.
  fold (ind_binder ind idecl p).
  intros a; depelim a.
  destruct (pcontext p) eqn:pctx => //. simpl.
  rewrite /ind_predicate_context /= /inst_case_context.
  rewrite subst_instance_cons.
  rewrite /= subst_context_snoc /=.
  constructor.
  { rewrite /= /subst_decl /map_decl /= /set_binder_name /=. relativize (subst _ _ _).
    1: constructor. red. simpl. simpl in e. red in e. simpl in e.
    rewrite -e. simpl in H. noconf H. reflexivity.
    simpl. rewrite subst_instance_mkApps subst_mkApps /=.
    f_equal. f_equal.
    now rewrite [subst_instance_instance _ _](subst_instance_id_mdecl _ _ _ cu).
    rewrite /to_extended_list to_extended_list_k_app.
    rewrite !map_app. f_equal.
    rewrite subst_instance_to_extended_list_k. len.
    erewrite subst_to_extended_list_k => //.
    eapply make_context_subst_spec_inv. rewrite List.rev_involutive.
    rewrite subst_instance_smash.
    apply sp.
    rewrite subst_instance_to_extended_list_k.
    rewrite /expand_lets_ctx /expand_lets_k_ctx.
    rewrite subst_instance_subst_context subst_instance_lift_context.
    rewrite to_extended_list_k_subst /= to_extended_list_k_lift_context.
    rewrite -to_extended_list_k_map_subst. len.
    now rewrite PCUICLiftSubst.map_subst_instance_to_extended_list_k. }
  eapply All2_symP. intros ? ? []; constructor; auto; now symmetry.
  eapply All2_map2_left_All3.
  simpl in H. noconf H.
  revert a. move: (map _ l0) => l a.
  induction a. constructor.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  rewrite !lift_context_snoc /=.
  rewrite subst_context_snoc /= subst_instance_cons subst_context_snoc.
  constructor; auto.
  destruct y as [na [b|] ty]; constructor; simpl; auto; reflexivity.
Qed.

Lemma pre_case_branch_context_eqE {cf}	{Σ} {wfΣ : wfE Σ} {ind mdecl idecl params puinst bctx cdecl} :
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) puinst ->
  wf_branch_gen cdecl bctx ->
  eq_context_upto_names
    (pre_case_branch_context ind mdecl params puinst cdecl)
    (case_branch_context_gen ind mdecl params puinst bctx cdecl).
Proof.
  intros decli cu.
  unfold wf_branch_gen. intros wf%Forall2_All2.
  rewrite /pre_case_branch_context /case_branch_context_gen.
  symmetry. etransitivity.
  eapply eq_binder_annots_eq.
  rewrite /pre_case_branch_context_gen /inst_case_context /cstr_branch_context.
  eapply All2_eq_binder_subst_context_inst.
  now eapply All2_eq_binder_subst_context.
  rewrite /pre_case_branch_context_gen /inst_case_context /cstr_branch_context.
  eapply alpha_eq_subst_context.
  rewrite subst_instance_expand_lets_ctx subst_instance_subst_context.
  now rewrite (instantiate_indsE decli cu) //.
Qed.

Lemma wf_case_branch_typeE {cf : checker_flags}	{Σ : global_env_ext} {wfΣ : wfE Σ}
  {Γ mdecl idecl} {ci : case_info} {p} ps (args : list term) :
  declared_inductive Σ ci mdecl idecl ->
  isTypeE Σ Γ (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ args)) ->
  wf_predicate mdecl idecl p ->
  let predctx := case_predicate_context ci mdecl idecl p in
  Σ;;; Γ ,,, predctx |-E p.(preturn) : tSort ps ->
  let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
  eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
  forall i cdecl br,
    declared_constructor Σ (ci.(ci_ind), i) mdecl idecl cdecl ->
    wf_branch cdecl br ->
    let cstr_br_ctx := case_branch_context_nopars ci mdecl p.(puinst) cdecl in
    let brctx' := map2 set_binder_name (forget_types (bcontext br)) cstr_br_ctx in
    let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
    [× wf_branch cdecl br,
       (* The branch context before substitution of parameters *)
       wf_localE Σ (Γ ,,, (ind_params mdecl)@[puinst p] ,,, cstr_br_ctx),
       wf_localE Σ (Γ ,,, (ind_params mdecl)@[puinst p] ,,, brctx'),
       wf_localE Σ (Γ ,,, brctxty.1) &
       Σ ;;; Γ ,,, brctxty.1 |-E brctxty.2 : tSort ps].
Proof.
  intros isdecl Hc wfp bc Hp ptm wfpctx.
  unshelve epose proof (isdecl' := declared_inductive_to_gen isdecl); eauto.
  destruct (WfArity_build_case_predicate_typeE wfΣ isdecl Hc (PCUICWfUniversesEta.typing_wf_sortE _ Hp) wfp) as [wfty _].
  set wfcpc := wf_case_predicate_contextE isdecl Hc wfp. simpl in wfcpc. clearbody wfcpc.
  have clipars : closed_ctx (subst_instance (puinst p) (ind_params mdecl)).
  { rewrite closedn_subst_instance_context.
    eapply (declared_inductive_closed_paramsE isdecl). }
  have wfΓ : (wf_localE Σ Γ).
  { now apply isType_wf_localE in Hc. }
  have lenpars : #|pparams p| =
      context_assumptions (subst_instance (puinst p) (ind_params mdecl)).
  { len. rewrite (wf_predicate_length_pars wfp) //.
    apply (declared_minductive_ind_nparsE isdecl). }
  eapply isType_mkApps_Ind_smashE in Hc; tea.
  2:{ rewrite (declared_minductive_ind_nparsE isdecl). now len in lenpars. }
  destruct Hc as [sppars [spargs cu]].
  intros n cdecl br nth wfbr.
  set (brctxty := case_branch_type _ _ _ _ _ _ _ _).
  destruct (on_declared_constructorE nth) as [[onind oib] [cs [nthc onc]]].
  simpl in *.
  subst brctxty.
  unfold case_branch_type, case_branch_type_gen => /=.
  rewrite -/(case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl).

  assert (wfargs : wf_localE (Σ.1, ind_universes mdecl)
  (arities_context (ind_bodies mdecl),,, ind_params mdecl,,, cstr_args cdecl)).
  { destruct onc. apply sorts_local_ctx_All_local_env in on_cargs => //.
    eapply weaken_wf_localE => //.
    eapply (wf_arities_context'E onind) => //.
    apply onind.(onParams). }
  assert (wfparscd : wf_localE Σ
  (Γ,,, subst_instance (puinst p) (ind_params mdecl),,,
   case_branch_context_nopars ci mdecl (puinst p) cdecl)). {
    rewrite -app_context_assoc.
    eapply weaken_wf_localE; tea.
    eapply (@wf_local_instantiateE _ _ (InductiveDecl mdecl) _ p.(puinst)) in wfargs; tea.
    2:eapply isdecl'.
    rewrite !subst_instance_app in wfargs.
    rewrite - !/(app_context _ _) in wfargs.
    rewrite -(app_context_nil_l (_ ,,, _)) -app_context_assoc app_context_assoc in wfargs.
    eapply substitution_wf_localE in wfargs; tea.
    2:eapply subslet_indsE; tea.
    rewrite app_context_nil_l subst_context_app in wfargs.
    rewrite closed_ctx_subst in wfargs => //.
    rewrite /case_branch_context_nopars.
    now rewrite subst_instance_length Nat.add_0_r in wfargs. }
  assert (wf_localE Σ (Γ ,,, case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl)).
  { rewrite /case_branch_context /case_branch_context_gen.
    eapply wf_set_binder_nameE.
    { eapply wf_pre_case_branch_context_gen; tea. }
    eapply substitution_wf_localE; tea. eapply sppars.
    rewrite /cstr_branch_context.
    rewrite subst_instance_expand_lets_ctx.
    eapply wf_local_expand_letsE => //.
    rewrite subst_instance_subst_context.
    rewrite (instantiate_indsE nth cu) //. }
  split => //.
  { eapply wf_set_binder_nameE => //.
    eapply All2_eq_binder_subst_context.
    eapply All2_eq_binder_subst_instance.
    now eapply Forall2_All2 in wfbr. }
  assert (wfparsargs : wf_localE Σ
    (Γ,,, subst_instance (puinst p) (ind_params mdecl),,,
      subst_context (inds (inductive_mind ci) (puinst p) (ind_bodies mdecl))
        #|ind_params mdecl| (subst_instance (puinst p) (cstr_args cdecl)))). {
    rewrite -app_context_assoc.
    eapply weaken_wf_localE; tea.
    eapply (@wf_local_instantiateE _ _ (InductiveDecl mdecl) _ p.(puinst)) in wfargs; tea.
    2:eapply isdecl'.
    rewrite !subst_instance_app in wfargs.
    rewrite - !/(app_context _ _) in wfargs.
    rewrite -(app_context_nil_l (_ ,,, _)) -app_context_assoc app_context_assoc in wfargs.
    eapply substitution_wf_localE in wfargs; tea.
    2:eapply subslet_indsE; tea.
    rewrite app_context_nil_l subst_context_app in wfargs.
    rewrite closed_ctx_subst in wfargs => //.
    now rewrite subst_instance_length Nat.add_0_r in wfargs. }
  assert (wfbrctx : wf_localE Σ (Γ ,,, pre_case_branch_context ci mdecl p.(pparams) p.(puinst) cdecl)).
  { rewrite /case_branch_context /case_branch_context_gen.
    eapply substitution_wf_localE; tea. eapply sppars.
    eapply wf_local_expand_letsE => //. }
  eapply type_mkAppsE.
  relativize #|cstr_args cdecl|.
  eapply weakeningE; tea. rewrite /ptm.
  eapply PCUICGenerationEta.type_it_mkLambda_or_LetInE. tea.
  rewrite case_branch_context_length //.
  now rewrite -(wf_branch_length wfbr).
  eapply wf_arity_spine_typing_spineE; tea.
  split.
  { apply isType_liftE => //. rewrite length_app; lia.
    rewrite skipn_all_app //. }
  rewrite /bc.
  rewrite lift_it_mkProd_or_LetIn /=.
  rewrite -(app_nil_r (_ ++ [_])).
  eapply arity_spine_it_mkProd_or_LetIn_smashE => //.
  2:constructor.
  rewrite /bc.
  *eapply subslet_eq_context_alphaE.
  { instantiate (1 := smash_context []
    (lift_context #|case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl| 0
      (case_predicate_context' ci mdecl idecl p))).
    apply alpha_eq_smash_context, alpha_eq_lift_context.
    epose proof (wf_pre_case_predicate_context_gen (ci:=ci) wfp).
    rewrite /inst_case_predicate_context.
    eapply All2_trans. tc.
    eapply case_predicate_context_alphaE; tea.
    destruct wfp. apply Forall2_All2 in H0. tea.
    now eapply inst_case_predicate_context_eq in wfpctx. }
  rewrite map_map_compose.
  fold (subst_let_expand_k (List.rev (pparams p)) (subst_instance (puinst p) (ind_params mdecl)) #|cstr_args cdecl|).
  set (indices := map (subst (inds _ _ _) _) _).
  rewrite /case_predicate_context' lift_context_snoc.
  rewrite subst_context_length subst_instance_length expand_lets_ctx_length.
  rewrite (smash_context_app_expand _ _ [_]).
  cbn. rewrite List.rev_app_distr; cbn.
  rewrite expand_lets_ctx_tip; cbn.
  rewrite /lift_decl compose_map_decl; cbn.
  eapply (subslet_eq_context_alpha_domE (Γ:=  (Γ ,,, pre_case_branch_context ci.(ci_ind) mdecl p.(pparams) p.(puinst) cdecl))).
  { eapply All2_app.
    rewrite /case_branch_context //.
    eapply (pre_case_branch_context_eqE (ind:=ci) nth cu wfbr).
    reflexivity. }
  pose proof (on_cindices onc).
  eapply ctx_inst_impl in X0. 2: intros ??; apply unlift_TermTyp.
  assert (spindices :
  spine_substE Σ
  (Γ,,, pre_case_branch_context ci mdecl (pparams p) (puinst p) cdecl)
  (map (subst (List.rev (pparams p)) #|cstr_args cdecl|)
     (map
        (expand_lets_k (subst_instance (puinst p) (ind_params mdecl))
           #|cstr_args cdecl|) indices))
  (map (subst (List.rev (pparams p)) #|cstr_args cdecl|)
     (map
        (expand_lets_k (subst_instance (puinst p) (ind_params mdecl))
           #|cstr_args cdecl|)
        (map
           (subst
              (inds (inductive_mind ci) (puinst p) (ind_bodies mdecl))
              (#|ind_params mdecl| + #|cstr_args cdecl|))
           (map (subst_instance (puinst p)) (ctx_inst_subE X0)))))
  (subst_context (List.rev (pparams p)) #|cstr_args cdecl|
     (expand_lets_k_ctx (subst_instance (puinst p) (ind_params mdecl))
        #|cstr_args cdecl|
        (subst_instance (puinst p)
           (lift_context #|cstr_args cdecl| 0 (ind_indices idecl)))))).
  { unshelve epose proof (ctx_inst_spine_substE _ X0) as sp.
    { eapply weakening_wf_localE => //.
      rewrite -app_context_assoc. apply weaken_wf_localE => //.
      eapply (wf_arities_contextE isdecl).
      apply (on_minductive_wf_params_indicesE isdecl). }
    eapply spine_subst_instE in sp; tea.
    2:{ exact (declared_inductive_wf_global_extE _ _ _ _ isdecl). }
    rewrite !subst_instance_app_ctx in sp.
    rewrite -app_context_assoc in sp.
    eapply spine_subst_subst_firstE in sp; tea.
    2:eapply subslet_indsE; tea.
    rewrite app_context_length !subst_instance_length in sp.
    rewrite subst_context_app subst_instance_length /= Nat.add_0_r in sp.
    rewrite closed_ctx_subst // in sp.
    eapply spine_subst_weakenE in sp. 2:eapply wfΓ. all:tea.
    rewrite app_context_assoc in sp.
    rewrite Nat.add_comm in sp; fold indices in sp.
    eapply spine_subst_expand_letsE in sp.
    rewrite subst_context_length subst_instance_length in sp.
    eapply spine_subst_substE in sp; tea.
    2:exact sppars.
    rewrite expand_lets_ctx_length subst_context_length subst_instance_length in sp.
    rewrite /subst_context_let_expand.
    rewrite (closed_ctx_subst (inds _ _ _) (#|ind_params mdecl| + _)) in sp.
    { rewrite closedn_subst_instance_context.
      rewrite Nat.add_comm; apply closedn_ctx_lift.
      pose proof (declared_inductive_closed_pars_indicesE isdecl).
      rewrite closedn_ctx_app in H.
      now move/andb_and: H => []. }
    exact sp. }
  constructor.
  - rewrite case_branch_context_length_args //.
    rewrite /indices.
    eapply spine_subst_smashE in spindices; tea.
    rewrite subst_instance_expand_lets_ctx.
    rewrite lift_context_subst_context lift_context_expand_lets_ctx
      -subst_instance_lift_context.
    eapply inst_subsletE in spindices.
    rewrite /subst_let_expand_k.
    rewrite /indices in spindices.
    now rewrite map_map_compose in spindices.
  - cbn [decl_type ind_binder].
    rewrite lift_mkApps expand_lets_mkApps.
    rewrite subst_mkApps. simpl.
    rewrite map_subst_let_expand_k.
    rewrite case_branch_context_length_args //.
    eapply meta_convE.
    { eapply type_mkAppsE.
      { econstructor; tea. }
      eapply wf_arity_spine_typing_spineE; tea.
      split. { eapply declared_constructor_valid_tyE; tea. }
      replace (type_of_constructor mdecl cdecl (ci.(ci_ind), n) (puinst p))
        with (lift0 #|cstr_args cdecl| (type_of_constructor mdecl cdecl (ci.(ci_ind), n) (puinst p))).
      2:{ rewrite lift_closed //. eapply (declared_constructor_closed_typeE nth). }
      unfold type_of_constructor.
      rewrite onc.(cstr_eq).
      simpl.
      rewrite subst_instance_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
      rewrite lift_it_mkProd_or_LetIn.
      rewrite closed_ctx_lift.
      { rewrite closed_ctx_subst //. }
      eapply arity_spine_it_mkProd_or_LetIn_smashE; tea.
      + rewrite closed_ctx_subst.
        rewrite closedn_subst_instance_context.
        eapply (declared_inductive_closed_paramsE isdecl).
        rewrite -[smash_context [] _](closed_ctx_lift #|cstr_args cdecl| 0).
        { now apply closedn_smash_context. }
        rewrite -map_rev.
        relativize #|cstr_args cdecl|.
        eapply subslet_liftE; tea. eapply sppars.
        now apply pre_case_branch_context_length_args.
      + rewrite subst_context_length Nat.add_0_r.
        rewrite subst_instance_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
        rewrite -map_rev.
        relativize #|subst_instance (puinst p) (ind_params mdecl)|.
        erewrite subst_let_expand_closed_ctx_lift.
        2:{ now rewrite List.length_rev context_assumptions_subst_context. }
        3:now rewrite subst_context_length.
        2:{ rewrite closed_ctx_subst => //. }
        rewrite subst_let_expand_it_mkProd_or_LetIn.
        rewrite !subst_context_length !subst_instance_length.
        rewrite closed_ctx_subst //.
        set (cstr_ctx := subst_context_let_expand _ _ _).
        change cstr_ctx with
          (pre_case_branch_context ci mdecl (pparams p) (puinst p) cdecl).
        clear cstr_ctx.
        rewrite -{1}(@pre_case_branch_context_length_args ci mdecl (pparams p) (puinst p) cdecl).
        rewrite /to_extended_list /to_extended_list_k.
        relativize (reln [] 0 (cstr_args cdecl)).
        eapply arity_spine_to_extended_listE => //.
        2:{ rewrite -/(to_extended_list_k _ 0) /pre_case_branch_context.
            rewrite /expand_lets_ctx /expand_lets_k_ctx /to_extended_list !to_extended_list_k_subst
              !to_extended_list_k_lift_context to_extended_list_k_subst
              PCUICLiftSubst.map_subst_instance_to_extended_list_k //. }
        rewrite /pre_case_branch_context /subst_let_expand_k.
        eapply has_sort_isTypeE with (s := subst_instance p.(puinst) (ind_sort idecl)).
        relativize #|cstr_args cdecl|.
        eapply (substitutionE (s := List.rev (pparams p)) (T := tSort _)); tea.
        eapply sppars.
        all:rewrite expand_lets_ctx_length.
        2:rewrite subst_context_length subst_instance_length //.
        eapply (typing_expand_lets_genE (T:=tSort _)).
        rewrite subst_context_length subst_instance_length.
        rewrite -/(to_extended_list_k _ _).
        rewrite subst_cstr_concl_head.
        destruct isdecl. now eapply nth_error_Some_length in H0.
        eapply type_mkAppsE.
        econstructor; tea.
        eapply (typing_spine_ind_typeE isdecl); tea.
        rewrite -[subst_instance _ (it_mkProd_or_LetIn _ _)](lift_closed (#|ind_params mdecl| + #|cstr_args cdecl|) 0).
        { rewrite closedn_subst_instance closedn_it_mkProd_or_LetIn /= andb_true_r.
          exact (declared_inductive_closed_pars_indicesE isdecl). }
        rewrite subst_instance_it_mkProd_or_LetIn subst_instance_app
          it_mkProd_or_LetIn_app.
        have wfs : wf_sort Σ (subst_instance_sort (puinst p) (ind_sort idecl)).
          by eapply (on_inductive_sort_instE isdecl _ cu).
        have wfparinds : wf_localE Σ
            (Γ,,, subst_instance (puinst p) (ind_params mdecl),,,
              subst_instance (puinst p) (ind_indices idecl)).
        { rewrite -app_context_assoc -subst_instance_app_ctx.
          eapply weaken_wf_localE; tea.
          eapply (on_minductive_wf_params_indices_instE isdecl _ cu). }
        relativize (#|ind_params mdecl| + #|cstr_args cdecl|).
        relativize (to_extended_list_k _ #|cstr_args cdecl|).
        eapply typing_spine_to_extended_list_k_appE; tea.
        eapply isType_it_mkProd_or_LetInE; tea. simpl.
        eapply isType_SortE; tea.
        2:{ len. now rewrite PCUICLiftSubst.map_subst_instance_to_extended_list_k. }
        2:{ now len. }
        rewrite subst_context_length subst_instance_length lift_it_mkProd_or_LetIn /=.
        eapply typing_spine_it_mkProd_or_LetIn_closeE; tea.
        3:{ reflexivity. }
        2:{ eapply isType_it_mkProd_or_LetInE; tea.
            eapply isType_SortE.
            eapply (on_inductive_sort_instE isdecl _ cu).
            relativize #|cstr_args cdecl|.
            eapply weakening_wf_localE => //. now len. }
        clear spindices.
        unshelve epose proof (ctx_inst_spine_substE _ X0) as sp.
        { eapply weakening_wf_localE => //.
          rewrite -app_context_assoc. apply weaken_wf_localE => //.
          eapply (wf_arities_contextE isdecl).
          apply (on_minductive_wf_params_indicesE isdecl). }
        eapply spine_subst_instE in sp; tea.
        2:{ exact (declared_inductive_wf_global_extE _ _ _ _ isdecl). }
        rewrite !subst_instance_app_ctx in sp.
        rewrite -app_context_assoc in sp.
        eapply spine_subst_subst_firstE in sp; tea.
        2:eapply subslet_indsE; tea.
        rewrite app_context_length !subst_instance_length in sp.
        rewrite subst_context_app subst_instance_length /= Nat.add_0_r in sp.
        rewrite closed_ctx_subst // in sp.
        eapply spine_subst_weakenE in sp. 2:eapply wfΓ. all:tea.
        rewrite app_context_assoc in sp.
        rewrite Nat.add_comm in sp |- *; fold indices in sp |- *.
        rewrite subst_instance_lift_context in sp.
        rewrite (closed_ctx_subst _ _ (lift_context #|cstr_args cdecl| _ _)) in sp.
        rewrite Nat.add_comm; eapply closedn_ctx_lift => //.
        epose proof (declared_inductive_closed_pars_indicesE isdecl).
        rewrite closedn_ctx_app in H. move/andb_and: H => [].
        now rewrite closedn_subst_instance_context.
        exact sp. }
    { rewrite Nat.add_0_r.
      rewrite subst_cstr_concl_head.
      { destruct isdecl. now eapply nth_error_Some_length in H0. }
      rewrite subst_let_expand_k_mkApps. cbn. f_equal.
      rewrite !map_app. f_equal.
      { rewrite -(PCUICLiftSubst.map_subst_instance_to_extended_list_k p.(puinst)).
        erewrite map_subst_let_expand_k_to_extended_list_liftE.
        2:{ eapply sppars. }
        rewrite !map_map_compose.
        apply map_ext => t.
        rewrite simpl_lift; try lia.
        rewrite (Nat.add_comm #|cstr_args cdecl|).
        rewrite subst_let_expand_k_lift //.
        len => //. len.
        { clear spindices. apply ctx_inst_length in X0.
          rewrite context_assumptions_rev in X0. len in X0.
           } }
      { pose proof (positive_cstr_closed_indicesE nth).
        rewrite map_map_compose.
        rewrite -(Nat.add_0_r #|ind_indices idecl|) -to_extended_list_map_lift.
        relativize (to_extended_list (ind_indices idecl)).
        erewrite map_subst_let_expand_k_to_extended_list_liftE.
        3:{ rewrite /expand_lets_ctx /expand_lets_k_ctx
              !to_extended_list_k_lift_context
              !to_extended_list_k_subst
              PCUICLiftSubst.map_subst_instance_to_extended_list_k
              !to_extended_list_k_subst to_extended_list_k_lift_context //. }
        2:{ eapply spine_subst_smashE; tea.
            rewrite subst_instance_expand_lets_ctx.
            rewrite lift_context_subst_context lift_context_expand_lets_ctx
              -subst_instance_lift_context.
            rewrite /subst_let_expand_k -map_map_compose.
            now exact spindices. }
        rewrite {2}/subst_let_expand_k.
        rewrite map_lift0. rewrite /indices.
        rewrite !map_map_compose.
        rewrite Nat.add_comm.
        now rewrite /subst_let_expand_k. }
    }
Qed.

Lemma wf_case_branches_types'E {cf : checker_flags}	{Σ : global_env_ext} {wfΣ : wfE Σ}
  {Γ mdecl idecl} {ci : case_info} {p} ps (args : list term) brs :
  declared_inductive Σ ci mdecl idecl ->
  isTypeE Σ Γ (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ args)) ->
  wf_predicate mdecl idecl p ->
  let predctx := case_predicate_context ci mdecl idecl p in
  Σ;;; Γ ,,, predctx |-E p.(preturn) : tSort ps ->
  let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
  wf_branches idecl brs ->
  eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
  All2i (fun i cdecl br =>
    let cstr_br_ctx := case_branch_context_nopars ci mdecl p.(puinst) cdecl in
    let brctx' := map2 set_binder_name (forget_types (bcontext br)) cstr_br_ctx in
    let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
    [× wf_branch cdecl br, (* The branch context before substitution of parameters *)
      wf_localE Σ (Γ ,,, (ind_params mdecl)@[puinst p] ,,, cstr_br_ctx),
      wf_localE Σ (Γ ,,, (ind_params mdecl)@[puinst p] ,,, brctx'),
       (* The branch context after substitution of parameters *)
       wf_localE Σ (Γ ,,, brctxty.1) &
       Σ ;;; Γ ,,, brctxty.1 |-E brctxty.2 : tSort ps])
    0 (ind_ctors idecl) brs.
Proof.
  intros isdecl Hc wfp bc Hp ptm wfbrs conv.
  destruct (WfArity_build_case_predicate_typeE wfΣ isdecl Hc (PCUICWfUniversesEta.typing_wf_sortE _ Hp) wfp) as [wfty _].
  set wfcpc := wf_case_predicate_contextE isdecl Hc wfp. simpl in wfcpc. clearbody wfcpc.
  have clipars : closed_ctx (subst_instance (puinst p) (ind_params mdecl)).
  { rewrite closedn_subst_instance_context.
    eapply (declared_inductive_closed_paramsE isdecl). }
  have wfΓ : (wf_localE Σ Γ).
  { now apply isType_wf_localE in Hc. }
  have lenpars : #|pparams p| =
      context_assumptions (subst_instance (puinst p) (ind_params mdecl)).
  { len. rewrite (wf_predicate_length_pars wfp) //.
    apply (declared_minductive_ind_nparsE isdecl). }
  eapply forall_nth_error_All2i.
  now rewrite (Forall2_length wfbrs).
  intros n cdecl br nth nth'.
  red in wfbrs. eapply Forall2_All2 in wfbrs.
  eapply All2_nth_error in wfbrs; tea.
  eapply wf_case_branch_typeE; tea.
  split; eauto.
Qed.
