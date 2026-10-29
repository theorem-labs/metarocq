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

  NOT COPIED (t0-plan §6, risk 5): [ws_cumul_pb_terms_confl] and [wf_cofixpoint_all], whose E
  forms are FALSE (refuted in Coq: [ws_cumul_pbE_red_false] / [ws_cumul_pbE_alt_closed_false] and
  [PCUICFixWitnessEtaCounter.wf_cofixpoint_allE_false]); [isLambda_red1] and
  [case_branch_context_nopars], which mention none of the relations and are used from base.

  DELIBERATE SHADOWING (C6 'New names'). This file declares [isType_it_mkProd_or_LetInE], a
  name that two imported modules already carry ([PCUICAritiesEta], the twin of
  [PCUICArities.isType_it_mkProd_or_LetIn], and [PCUICInductivesEta], the twin of
  [PCUICInductives.isType_it_mkProd_or_LetIn]). Base has exactly the same three objects of the
  name, and the two landed E constants have DIFFERENT compiled types: neither stands for the
  type of this file's twin (each ascription is refused by the type checker), so neither can be
  reused. Every reference to the name inside this file is written qualified. The second name of
  that class, [isType_is_open_termE], is NOT declared here: the landed
  [Typing/PCUICClosedTypEta.isType_is_open_termE] has the identical compiled type, so this file
  only adds base's [pcuic] registration of it.

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

Lemma conv_eq_ctxE {cf:checker_flags} Σ Γ Γ' T U : JoinE Σ Γ Conv T U -> Γ = Γ' -> JoinE Σ Γ' Conv T U.
Proof. now intros H ->. Qed.

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

Lemma typing_spine_it_mkProd_Ind_invE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
  {Γ T l U} :
  typing_spineE Σ Γ T l U ->
  forall ctx ind u args ind' u' args',
  Σ ;;; Γ ⊢E it_mkProd_or_LetIn ctx (mkApps (tInd ind u) args) ≤ T ->
  U = mkApps (tInd ind' u') args' ->
  ind = ind'.
Proof.
  induction 1 as [ty ty' ity ity' cum|ty hd tl na A B B' ity ityp cum tyhd sp IH];
    intros ctx I ui iargs ind' u' args' hcum heq; subst.
  - have hc : Σ ;;; Γ ⊢E it_mkProd_or_LetIn ctx (mkApps (tInd I ui) iargs) ≤
      mkApps (tInd ind' u') args' by etransitivity; tea.
    have hΓ := wsE_ctx hc. have hol := wsE_left hc.
    eapply ws_cumul_pbE_Ind_r_inv in hc as [ui' [l' [r _ _]]].
    destruct (chain_it_mkProd_or_LetIn_mkApps_Ind Γ ctx I ui iargs _ hΓ hol r)
      as [ctx' [args'' eq]].
    symmetry. now eapply mkApps_tInd_eq_it_mkProd_Ind.
  - have hc : Σ ;;; Γ ⊢E it_mkProd_or_LetIn ctx (mkApps (tInd I ui) iargs) ≤ tProd na A B
      by etransitivity; tea.
    have hΓ := wsE_ctx hc. have hol := wsE_left hc.
    eapply ws_cumul_pbE_Prod_r_inv in hc as [na1 [A1 [B1 [r eqna cdom ccod]]]].
    destruct (chain_it_mkProd_or_LetIn_mkApps_Ind Γ ctx I ui iargs _ hΓ hol r)
      as [ctx1 [args1 eq]].
    eapply tProd_eq_it_mkProd_Ind in eq as [ctx0 [_ ->]].
    eapply (substitution0_ws_cumul_pbE (t:=hd)) in ccod; tea.
    rewrite /subst1 subst_it_mkProd_or_LetIn subst_mkApps /= Nat.add_0_r in ccod.
    eapply (IH _ I ui _ ind' u' args'); [exact ccod|reflexivity].
    (* the scoping side condition of [substitution0_ws_cumul_pbE] on the substituted term *)
    exact (subject_is_open_termE tyhd).
Qed.

Lemma type_tFix_invE {cf:checker_flags} (Σ : global_env_ext) Γ mfix idx T : wfE Σ ->
  Σ ;;; Γ |-E tFix mfix idx : T ->
  { T' & { rarg & {f & (unfold_fix mfix idx = Some (rarg, f))  *
    wf_fixpointE Σ Γ mfix
  * (Σ ;;; Γ |-E f : T') * (Σ ;;; Γ ⊢E T' ≤ T) }}}%type.
Proof.
  intros wfΣ H. depind H.
  - unfold unfold_fix. rewrite e.
    specialize (nth_error_all e a0) as (_ & s & Hs & _).
    specialize (nth_error_all e a1) as (Hb & _). cbn in Hb, Hs.
    simpl.
    destruct decl as [name ty body rarg]; simpl in *.
    clear e.
    eexists _, _, _. split.
    + split.
      * eauto.
      * eapply (substitutionE (Δ :=  [])); simpl; eauto with wf.
        (* [simpl in *] above unfolds [fix_guard] to [guard_cl Fix] now that the
           guard is a concrete instance rather than an axiom. *)
        match goal with
        | H : fix_guard _ _ _ |- _ => rename H into hguard
        | H : guard_cl Fix _ _ _ |- _ => rename H into hguard
        end.
        match goal with H : wf_fixpointE _ _ _ |- _ => rename H into hwffix end.
        clear -a a0 a1 hguard hwffix.
        pose proof a1 as a1'. apply All_rev in a1'.
        unfold fix_subst, fix_context. simpl.
        revert a1'. rewrite <- (@List.length_rev _ mfix).
        rewrite rev_mapi. unfold mapi.
        assert (#|mfix| >= #|List.rev mfix|) by (rewrite List.length_rev; lia).
        assert (He :0 = #|mfix| - #|List.rev mfix|) by (rewrite List.length_rev; auto with arith).
        rewrite {2}He. clear He. revert H.
        assert (forall i, i < #|List.rev mfix| -> nth_error (List.rev mfix) i = nth_error mfix (#|List.rev mfix| - S i)).
        { intros. rewrite nth_error_rev. 1: auto.
          now rewrite List.length_rev List.rev_involutive. }
        revert H.
        generalize (List.rev mfix).
        intros l Hi Hlen H.
        induction H.
        ++ simpl. constructor.
        ++ simpl. constructor.
          ** unfold mapi in IHAll.
              simpl in Hlen. replace (S (#|mfix| - S #|l|)) with (#|mfix| - #|l|) by lia.
              apply IHAll.
              --- intros. simpl in Hi. specialize (Hi (S i)). apply Hi. lia.
              --- lia.
          ** clear IHAll.
              simpl in Hlen. assert ((Nat.pred #|mfix| - (#|mfix| - S #|l|)) = #|l|) by lia.
              rewrite H0. rewrite simpl_subst_k.
              --- clear. induction l; simpl; auto with arith.
              --- eapply typeE_Fix; auto.
                  simpl in Hi. specialize (Hi 0). forward Hi.
                  +++ lia.
                  +++ simpl in Hi.
                      rewrite Hi. f_equal. lia.

    + rewrite simpl_subst_k.
      * now rewrite fix_context_length fix_subst_length.
      * eapply isType_ws_cumul_pbE_refl; pcuic.
  - destruct (IHtypingE1 wfΣ) as [T' [rarg [f [[unf fty] Hcumul]]]].
    exists T', rarg, f. intuition auto.
    etransitivity; eauto.
    (* I5: the specification enters [ws_cumul_pbE] through [into_ws_cumul_pbE_spec], where base
       uses [PCUICConversion.cumulSpec_cumulAlgo_curry] *)
    eapply into_ws_cumul_pbE_spec in c; eauto; fvs.
Qed.

Lemma subslet_cofixE {cf:checker_flags} (Σ : global_env_ext) Γ mfix :
  wf_localE Σ Γ ->
  cofix_guard Σ Γ mfix ->
  All (on_def_type (lift_typing typingE Σ) Γ) mfix ->
  All (on_def_body (lift_typing typingE Σ) (fix_context mfix) Γ) mfix ->
  wf_cofixpointE Σ Γ mfix -> subsletE Σ Γ (cofix_subst mfix) (fix_context mfix).
Proof.
  intros wfΓ hguard types bodies wfcofix.
  pose proof bodies as X1. apply All_rev in X1.
  unfold cofix_subst, fix_context. simpl.
  revert X1. rewrite <- (@List.length_rev _ mfix).
  rewrite rev_mapi. unfold mapi.
  assert (#|mfix| >= #|List.rev mfix|) by (rewrite List.length_rev; lia).
  assert (He :0 = #|mfix| - #|List.rev mfix|) by (rewrite List.length_rev; auto with arith).
  rewrite {2}He. clear He. revert H.
  assert (forall i, i < #|List.rev mfix| -> nth_error (List.rev mfix) i = nth_error mfix (#|List.rev mfix| - S i)).
  { intros. rewrite nth_error_rev. 1: auto.
    now rewrite List.length_rev List.rev_involutive. }
  revert H.
  generalize (List.rev mfix).
  intros l Hi Hlen H.
  induction H.
  ++ simpl. constructor.
  ++ simpl. constructor.
    ** unfold mapi in IHAll.
        simpl in Hlen. replace (S (#|mfix| - S #|l|)) with (#|mfix| - #|l|) by lia.
        apply IHAll.
        --- intros. simpl in Hi. specialize (Hi (S i)). apply Hi. lia.
        --- lia.
    ** clear IHAll.
        simpl in Hlen. assert ((Nat.pred #|mfix| - (#|mfix| - S #|l|)) = #|l|) by lia.
        rewrite H0. rewrite simpl_subst_k.
        --- clear. induction l; simpl; auto with arith.
        --- eapply typeE_CoFix; auto.
            simpl in Hi. specialize (Hi 0). forward Hi.
            +++ lia.
            +++ simpl in Hi.
                rewrite Hi. f_equal. lia.
Qed.

Lemma type_tCoFix_invE {cf:checker_flags} (Σ : global_env_ext) Γ mfix idx T : wfE Σ ->
  Σ ;;; Γ |-E tCoFix mfix idx : T ->
  ∑ d, (nth_error mfix idx = Some d) *
    wf_cofixpointE Σ Γ mfix *
    (Σ ;;; Γ |-E subst0 (cofix_subst mfix) (dbody d) : (dtype d)) *
    (Σ ;;; Γ ⊢E dtype d ≤ T).
Proof.
  intros wfΣ H.
  apply typingE_wf_local in H as wfΓ.
  apply inversion_CoFixE in H as (decl & Hguard & Hnth & Htys & Hbods & Hwf & Hty); tas.
  exists decl. repeat (split; tea).
  eapply All_nth_error in Hbods as Hbod; tea.
  apply unlift_TermTyp in Hbod.
  eapply (substitutionE (s := cofix_subst mfix) (Δ := [])) in Hbod.
  2: now apply subslet_cofixE; auto.
  simpl in Hbod.
  rewrite subst_context_nil /= in Hbod.
  eapply meta_convE; eauto.
  rewrite simpl_subst_k //. len.
Qed.

Section OnConstructorExtB.

  Context {cf} {Σ} {wfΣ : wfE Σ} {ind mdecl idecl cdecl}
    (declc : declared_constructor Σ ind mdecl idecl cdecl).

    Lemma on_constructor_inst_wf_argsE u :
      consistent_instance_ext Σ (ind_universes mdecl) u ->
      wf_localE Σ ((ind_params mdecl)@[u] ,,, subst_context (ind_subst mdecl (fst ind) u) #|ind_params mdecl| (cstr_args cdecl)@[u]).
    Proof using declc wfΣ.
      intros cu.
      pose proof (on_constructor_wf_argsE declc).
      eapply wf_local_subst_instanceE in X; tea.
      rewrite -[X in X ,,, _]app_context_nil_l - !app_context_assoc app_context_assoc in X.
      rewrite !subst_instance_app_ctx /= in X.
      eapply substitution_wf_localE in X.
      2:eapply (subslet_indsE declc); tea.
      2:{ eapply (declared_inductive_wf_global_extE Σ.1 _ _ _ declc). }
      cbn in X. rewrite app_context_nil_l in X.
      rewrite subst_context_app Nat.add_0_r in X.
      rewrite closed_ctx_subst in X.
      rewrite closedn_subst_instance_context.
      eapply (declared_inductive_closed_paramsE declc).
      now len in X.
    Qed.

End OnConstructorExtB.

Lemma on_constructor_inst_pars_indicesE {cf:checker_flags} {Σ ind u mdecl idecl cdecl Γ pars parsubst} :
  wfE Σ.1 ->
  declared_constructor Σ.1 ind mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  spine_substE Σ Γ pars parsubst (subst_instance u (ind_params mdecl)) ->
  wf_localE Σ (subst_instance u (ind_params mdecl) ,,,
    subst_context (inds (inductive_mind ind.1) u (ind_bodies mdecl)) #|ind_params mdecl|
    (subst_instance u (cstr_args cdecl))) *
  ∑ inst,
  spine_substE Σ
          (Γ ,,, subst_context parsubst 0 (subst_context (ind_subst mdecl ind.1 u) #|ind_params mdecl|
            (subst_instance u (cstr_args cdecl))))
          (map (subst parsubst #|cstr_args cdecl|)
            (map (subst (ind_subst mdecl ind.1 u) (#|cstr_args cdecl| + #|ind_params mdecl|))
              (map (subst_instance u) (cstr_indices cdecl))))
          inst
          (lift_context #|cstr_args cdecl| 0
          (subst_context parsubst 0 (subst_instance u (ind_indices idecl)))).
Proof.
  move=> wfΣ declc cext sp.
  (* destruct (on_declared_constructor declc) as []. .declm oi oib onc *)
  destruct (on_constructor_instE declc u) as [wfl [inst sp']]; auto.
  rewrite !subst_instance_app in sp'.
  eapply spine_subst_app_invE in sp' as [spl spr]; auto.
  rewrite (spine_subst_extended_substE spl) in spr.
  rewrite subst_context_map_subst_expand_lets in spr; try now len.
  rewrite subst_instance_to_extended_list_k in spr.
  2:now len.
  rewrite lift_context_subst_context.
  rewrite app_assoc in spr.
  eapply spine_subst_subst_firstE in spr; eauto.
  2:eapply subslet_indsE; eauto; eapply declc.
  len in spr.
  rewrite subst_context_app in spr.
  assert (closed_ctx (subst_instance u (ind_params mdecl)) /\ closedn_ctx #|ind_params mdecl| (subst_instance u (ind_indices idecl)))
  as [clpars clinds].
  { pose proof (on_minductive_wf_params_indicesE declc).
    eapply closed_wf_localE in X => //.
    rewrite closedn_ctx_app in X; simpl; eauto;
    move/andb_and: X; intuition auto;
    now rewrite closedn_subst_instance_context. }
  assert (closedn_ctx (#|ind_params mdecl| + #|cstr_args cdecl|) (subst_instance u (ind_indices idecl)))
    as clinds'.
  { eapply closedn_ctx_upwards; eauto. lia. }
  rewrite closed_ctx_subst // in spr.
  rewrite (closed_ctx_subst (inds (inductive_mind ind.1) u (ind_bodies mdecl)) _ (subst_context (List.rev _) _ _)) in spr.
  { len.
    rewrite -(Nat.add_0_r (#|cstr_args cdecl| + #|ind_params mdecl|)).
    eapply closedn_ctx_subst. len.
    rewrite -(context_assumptions_subst_instance u).
    eapply closedn_ctx_expand_lets. eapply closedn_ctx_upwards; eauto. lia.
    len. eapply closedn_ctx_upwards; eauto. lia.
    rewrite forallb_rev.
    rewrite PCUICLiftSubst.map_subst_instance_to_extended_list_k.
    eapply closedn_to_extended_list_k. }
  len in spr. split => //. apply spr.
  eapply spine_subst_weakenE in spr.
  2:eapply (spine_dom_wfE _ _ _ _ _ sp); eauto.
  rewrite app_context_assoc in spr.
  eapply spine_subst_substE in spr; eauto. 2:eapply sp.
  len in spr.
  rewrite {4}(spine_subst_extended_substE sp) in spr.
  rewrite subst_context_map_subst_expand_lets_k in spr; try now len.
  rewrite List.length_rev. now rewrite -(context_subst_length2 sp).
  rewrite expand_lets_k_ctx_subst_id' in spr. now len. now len.
  rewrite -subst_context_map_subst_expand_lets_k in spr; try len.
  rewrite subst_subst_context in spr. len in spr.
  rewrite subst_extended_lift // in spr.
  rewrite lift_extended_subst in spr.
  rewrite (map_map_compose _ _ _ _ (subst (List.rev pars) _)) in spr.
  assert (map
              (fun x : term =>
               subst (List.rev pars) #|cstr_args cdecl|
                 (lift0 #|cstr_args cdecl| x))
              (extended_subst (subst_instance u (ind_params mdecl)) 0) =
              (map
              (fun x : term =>
              (lift0 #|cstr_args cdecl|
                (subst (List.rev pars) 0 x)))
              (extended_subst (subst_instance u (ind_params mdecl)) 0))
              ).
  eapply map_ext => x.
  now rewrite -(commut_lift_subst_rec _ _ _ 0).
  rewrite H in spr. clear H.
  rewrite -(map_map_compose  _ _  _ _ (lift0 #|cstr_args cdecl|)) in spr.
  rewrite -(spine_subst_extended_substE sp) in spr.
  rewrite subst_map_lift_lift_context in spr.
  rewrite -(context_subst_length sp).
  len.
  rewrite closed_ctx_subst //.
  rewrite (closed_ctx_subst (List.rev pars)) // in spr.
  eexists. eauto.
Qed.

Lemma wf_cofixpoint_typing_spineE {cf:checker_flags} (Σ : global_env_ext) Γ ind u mfix idx d args args' :
  wfE Σ.1 -> wf_localE Σ Γ ->
  wf_cofixpointE Σ Γ mfix ->
  nth_error mfix idx = Some d ->
  isTypeE Σ Γ (dtype d) ->
  typing_spineE Σ Γ (dtype d) args (mkApps (tInd ind u) args') ->
  check_recursivity_kind (lookup_env Σ) (inductive_mind ind) CoFinite.
Proof.
  intros wfΣ wfΓ wfcofix Hnth wat sp.
  (* Route (A): the conversion witness of [wf_cofixpointE] is used as it stands. Base turns it
     into a REDUCT of the declared type ([mfix_on_ind_inv]); the closed-only E form of that step
     is false (PCUICFixWitnessEtaCounter), so the witness enters [ws_cumul_pbE] directly, through
     [into_ws_cumul_pbE_spec] and [ws_cumul_pbE_sym_pb]. *)
  destruct wfcofix as [mind [ne [hall hck]]].
  eapply nth_error_all in hall; tea.
  destruct hall as [ty [hc [opty cv]]].
  eapply check_one_cofix_inv in hc as [ctx [i [u0 [l eqty]]]]. subst ty.
  have hcum : Σ ;;; Γ ⊢E it_mkProd_or_LetIn ctx
      (mkApps (tInd {| inductive_mind := mind; inductive_ind := i |} u0) l) ≤ dtype d.
  { eapply ws_cumul_pbE_sym_pb.
    eapply into_ws_cumul_pbE_spec;
      [exact cv|exact (wf_local_closed_contextE wfΓ)|exact (isType_is_open_termE wat)|exact opty]. }
  have heq : {| inductive_mind := mind; inductive_ind := i |} = ind.
  { eapply (typing_spine_it_mkProd_Ind_invE sp); [exact hcum|reflexivity]. }
  now subst ind.
Qed.

Notation "⋆" := ltac:(solve [pcuic]) (only parsing).

Notation decl_ws_cumul_pbE Σ Γ := (All_decls_alpha_pb Conv
  (fun pb (x0 y0 : term) => Σ ;;; Γ ⊢E x0 ≤[pb] y0)).

Lemma conv_decls_fix_context_genE {cf:checker_flags} Σ Γ mfix mfix1 :
  wfE Σ.1 ->
  All2 (fun d d' => Σ ;;; Γ ⊢E d.(dtype) = d'.(dtype) × eq_binder_annot d.(dname) d'.(dname)) mfix mfix1 ->
  forall Γ' Γ'',
  ws_cumul_ctx_pbE Conv Σ (Γ ,,, Γ') (Γ ,,, Γ'') ->
  ws_cumul_ctx_pbE_rel Conv Σ (Γ ,,, Γ') (fix_context_gen #|Γ'| mfix) (fix_context_gen #|Γ''| mfix1).
Proof.
  intros wfΣ a Γ' Γ'' convctx.
  split. eauto with fvs.
  induction a in Γ', Γ'', convctx |- *. constructor. simpl.
  destruct r as [r eqann].

  assert(decl_ws_cumul_pbE Σ (Γ ,,, Γ' ,,, [])
    (vass (dname x) (lift0 #|Γ'| (dtype x)))
    (vass (dname y) (lift0 #|Γ''| (dtype y)))).
  { constructor; tas.
    pose proof (All2_fold_length convctx).
    rewrite !length_app in H. assert(#|Γ'|  = #|Γ''|) by lia.
    rewrite -H0.
    apply (weakening_ws_cumul_pbE (Γ' := [])); eauto with fvs. }

  apply All2_fold_app.
  constructor => //. constructor.
  eapply (All2_fold_impl (P:= (fun Δ Δ' : context =>
  decl_ws_cumul_pbE Σ
    (Γ ,,, (vass (dname x) (lift0 #|Γ'| (dtype x)) :: Γ') ,,, Δ)))).
  eapply (IHa (vass _ _ :: Γ') (vass _ _ :: Γ'')).
  cbn; constructor => //. constructor; eauto.
  depelim X. eauto.
  intros. red.
  now rewrite ![_ ,,, _]app_context_assoc.
Qed.

Lemma conv_decls_fix_contextE {cf:checker_flags} {Σ} {wfΣ : wfE Σ} {Γ mfix mfix1} :
  wf_localE Σ Γ ->
  All2 (fun d d' => Σ ;;; Γ ⊢E d.(dtype) = d'.(dtype) × eq_binder_annot d.(dname) d'.(dname)) mfix mfix1 ->
  All2_fold (fun Δ Δ' : context => decl_ws_cumul_pbE Σ (Γ ,,, Δ))
    (fix_context mfix) (fix_context mfix1).
Proof.
  intros wfΓ a.
  apply (conv_decls_fix_context_genE _ _  _ _ wfΣ a [] []).
  eapply ws_cumul_ctx_pbE_refl. eauto with fvs.
Qed.

Notation "!! t" := ltac:(refine t) (at level 200, only parsing).

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

Lemma instantiate_subsletE {cf Σ} {Γ s Δ} {c} {decl : global_decl} {u : Instance.t} {wfΣ : wfE Σ.1} :
  lookup_env Σ.1 c = Some decl ->
	subsletE (Σ.1, universes_decl_of_decl decl) Γ s Δ ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  subsletE Σ Γ@[u] s@[u] Δ@[u].
Proof.
  intros hl subs cu.
  induction subs.
  - constructor.
  - cbn. constructor; auto.
    cbn. rewrite -subst_instance_subst. eapply typing_subst_instance_declE; tea.
  - cbn. rewrite subst_instance_subst. constructor; auto.
    cbn. rewrite - !subst_instance_subst.
    eapply typing_subst_instance_declE; tea.
Qed.

Lemma instantiate_wf_subsletE {cf Σ} {Γ s Δ} {c} {decl : global_decl} {u : Instance.t} {wfΣ : wfE Σ.1} :
  lookup_env Σ.1 c = Some decl ->
	wf_subsletE (Σ.1, universes_decl_of_decl decl) Γ s Δ ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  wf_subsletE Σ Γ@[u] s@[u] Δ@[u].
Proof.
  intros hl [wf subs] cu.
  split.
  rewrite -subst_instance_app_ctx. eapply wf_local_instantiateE; tea.
  now eapply instantiate_subsletE.
Qed.

Lemma substitution_subsletE {cf:checker_flags} {Σ} {wfΣ : wfE Σ} {Γ Γ' Δ s s' Δ'} :
  subsletE Σ Γ s Δ ->
  wf_subsletE Σ (Γ ,,, Δ ,,, Γ') s' Δ' ->
  wf_subsletE Σ (Γ ,,, subst_context s 0 Γ') (map (subst s #|Γ'|) s') (subst_context s #|Γ'| Δ').
Proof.
  intros subl [wf subs].
  split.
  { rewrite -app_context_assoc.
    relativize #|Γ'|.
    erewrite <-subst_context_app. 2:lia.
    eapply substitution_wf_localE; tea.
    now rewrite app_context_assoc. }
  clear wf.
  induction subs in s, subl |- *.
  * cbn. intros. constructor.
  * cbn. rewrite subst_context_snoc. constructor; auto.
    eapply substitutionE in t0; tea.
    cbn. rewrite -(subslet_lengthE subs).
    now rewrite -distr_subst.
  * cbn. rewrite subst_context_snoc.
    eapply substitutionE in t0; tea.
    specialize (IHsubs _ subl).
    epose proof (cons_let_defE _ _ _ _ _ _ _ IHsubs).
    rewrite !distr_subst in t0.
    specialize (X t0).
    rewrite -(subslet_lengthE subs).
    now rewrite -distr_subst in X.
Qed.

Lemma weaken_wf_subsletE {cf Σ} {wfΣ : wfE Σ} s (Δ Γ Γ' : context) :
  wf_localE Σ Γ →
  wf_subsletE Σ Γ' s Δ →
  wf_subsletE Σ (Γ,,, Γ') s Δ.
Proof.
  intros wfΓ [wf subs]. split.
  rewrite -app_context_assoc.
  eapply weaken_wf_localE => //.
  eapply weaken_subsletE; tea.
  now eapply All_local_env_app_inv in wf.
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

Lemma into_ws_cumul_pb_termsE {cf} {Σ} {wfΣ : wfE Σ} {Γ l l'} :
  All2 (convSpecE Σ Γ) l l' ->
  is_closed_context Γ ->
  forallb (is_open_term Γ) l ->
  forallb (is_open_term Γ) l' ->
  ws_cumul_pbE_terms Σ Γ l l'.
Proof.
  (* [ws_cumul_pbE_terms] is a Definition where base's [ws_cumul_pb_terms] is a Notation *)
  unfold ws_cumul_pbE_terms.
  solve_all.
  (* I5: the specification enters [ws_cumul_pbE] through [into_ws_cumul_pbE_spec],
     where base uses [PCUICConversion.convSpec_convAlgo_curry] *)
  eapply into_ws_cumul_pbE_spec; tea.
Qed.

Lemma on_constructor_closed_indicesE {cf} {Σ} {wfΣ : wfE Σ} :
  forall {i mdecl idecl cdecl},
  declared_constructor Σ.1 i mdecl idecl cdecl ->
  All (is_open_term (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cstr_args cdecl)) (cstr_indices cdecl).
Proof.
  intros.
  pose proof (on_declared_constructorE H) as [[onmind oib] [cs [hnth onc]]].
  pose proof (onc.(on_cindices)).
  eapply ctx_inst_impl in X. 2: intros ??; apply unlift_TermTyp.
  now eapply ctx_inst_open_termsE in X.
Qed.

Lemma positive_cstr_closed_indices'E {cf} {Σ} {wfΣ : wfE Σ} :
  forall {i mdecl idecl cdecl},
  declared_constructor Σ.1 i mdecl idecl cdecl ->
  All (closedn (context_assumptions (cstr_args cdecl) + context_assumptions (ind_params mdecl)))
    (map (expand_lets (ind_params mdecl ,,, cstr_args cdecl)) (cstr_indices cdecl)).
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
Qed.

Lemma ws_cumul_ctx_pb_wf_localE {cf:checker_flags} {Σ} {wfΣ : wfE Σ.1} Γ Γ' Δ :
  wf_localE Σ (Γ ,,, Δ) ->
  wf_localE Σ Γ' ->
  ws_cumul_ctx_pbE Conv Σ (Γ) (Γ') ->
  wf_localE Σ (Γ' ,,, Δ).
Proof.
  intros wf wf' e.
  eapply All_local_env_app => //.
  eapply All_local_env_app_inv in wf as [].
  eapply All_local_env_impl_ind; eauto.
  intros.
  rewrite -/(All_local_rel (lift_typing1 (typingE Σ)) Γ' Γ0) /= in X, X0.
  apply lift_typing_impl with (1 := X0); intros ?? Hs.
  eapply closed_context_cumulativityE; tea.
  eapply All_local_env_app=> //.
  eapply ws_cumul_ctx_pbE_app_same; tea. 2:now symmetry.
  eapply All_local_env_app in X; tea.
  eauto with fvs.
Qed.

Lemma subst_inds_smash_paramsE {cf} {Σ} {wfΣ : wfE Σ} {mdecl ind idecl u} :
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  subst_context (inds (inductive_mind ind) u (ind_bodies mdecl)) 0
    (subst_instance u (smash_context [] (PCUICEnvironment.ind_params mdecl))) =
    (subst_instance u (smash_context [] (PCUICEnvironment.ind_params mdecl))).
Proof.
  intros decli cu.
  rewrite closed_ctx_subst //.
  eapply closed_wf_localE; eauto.
  rewrite subst_instance_smash /= //.
  eapply wf_local_smash_contextE; auto.
  destruct decli. eapply on_minductive_wf_paramsE; pcuic.
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
  eapply PCUICInductiveInversionEtaB.isType_it_mkProd_or_LetInE; eauto.
  eapply isType_SortE; auto.
  eapply wf_set_binder_nameE.
  now eapply wf_pre_case_predicate_context_gen.
  now eapply isType_it_mkProd_or_LetIn_wf_localE in X.
Qed.

Lemma arity_spine_eqE {cf:checker_flags} {Σ Γ T T'} : T = T' -> arity_spineE Σ Γ T [] T'.
Proof.
  intros ->; constructor.
Qed.

(** Base declares a second [isType_is_open_term] here ([PCUICInductiveInversion.v:4040], beside
    [Typing/PCUICClosedTyp]'s) and registers it [Hint Immediate] on [pcuic]. The landed
    [Typing/PCUICClosedTypEta.isType_is_open_termE] has the IDENTICAL compiled type (each stands
    for the other under an ascription, both ways); only the implicit status of [Γ] and [T]
    differs, which is not part of the type. So no second E constant is declared: the landed one
    is registered on [pcuic], which is what base's second declaration adds. *)
(* REMOVED AT THE MERGE of fork/frac/eta >= 3953e0f5, which adds this same registration at the
   end of PCUICInductiveInversionEta.v; two registrations of one hint must not land. *)
#[global] Hint Immediate PCUICClosedTypEta.isType_is_open_termE : pcuic.

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

Lemma isType_subst_all_relsE {cf} {Σ} {wfΣ : wfE Σ} {Γ Δ} {T} :
  isTypeE Σ (Γ ,,, Δ) T ->
  isTypeE Σ (Γ ,,, Δ) (subst0 (all_rels Δ 0 #|Δ|) (lift #|Δ| #|Δ| T)).
Proof.
  intros Hty.
  apply lift_sorting_it_impl_gen with Hty => // Hs.
  pose proof (typingE_wf_local Hs).
  eapply weakening_typingE in Hs; tea.
  rewrite -(app_nil_l (lift_context _ _ _)) -/(app_context _ _) app_context_assoc in Hs.
  eapply substitutionE in Hs; tea.
  eapply spine_subst_to_extended_list_kE; tea.
Qed.

Lemma isType_all_rels_subst_liftE {cf} {Σ} {wfΣ : wfE Σ} {Γ Δ} {T} :
  isTypeE Σ (Γ ,,, Δ) T ->
  Σ ;;; Γ,,, Δ  ⊢E T = subst0 (all_rels Δ 0 #|Δ|) (lift #|Δ| #|Δ| T).
Proof.
  intros isty.
  have wf := (isType_wf_localE isty).
  epose proof (@all_rels_subst_liftE _ _ _ Δ Γ [] T wf (wf_local_closed_contextE wf)
  ltac:(eauto with pcuic)).
  now rewrite lift0_id /= Nat.add_0_r in X.
Qed.

Lemma arity_spine_to_extended_list_appE {cf} {Σ} {wfΣ : wfE Σ} {Γ Δ} {T s T'} :
  wf_localE Σ (Γ ,,, Δ) ->
  isTypeE Σ (Γ ,,, Δ) T ->
  arity_spineE Σ (Γ ,,, Δ) (subst0 (all_rels Δ 0 #|Δ|) (lift #|Δ| #|Δ| T)) s T' ->
  arity_spineE Σ (Γ ,,, Δ) (lift0 #|Δ| (it_mkProd_or_LetIn Δ T)) (to_extended_list Δ ++ s) T'.
Proof.
  intros isty wf.
  rewrite lift_it_mkProd_or_LetIn Nat.add_0_r.
  pose proof (isType_all_rels_subst_liftE wf).
  intros sp.
  eapply arity_spine_it_mkProd_or_LetInE; tea.
  rewrite /to_extended_list /to_extended_list_k.
  eapply spine_subst_to_extended_list_kE; tea.
Qed.

Lemma typing_spine_to_extended_list_appE {cf} {Σ} {wfΣ : wfE Σ} {Γ Δ} {T s T'} :
  typing_spineE Σ (Γ ,,, Δ) T s T' ->
  typing_spineE Σ (Γ ,,, Δ) (lift0 #|Δ| (it_mkProd_or_LetIn Δ T)) (to_extended_list Δ ++ s) T'.
Proof.
  rewrite lift_it_mkProd_or_LetIn Nat.add_0_r.
  intros sp.
  have isty := (typing_spine_isType_domE sp).
  eapply typing_spine_it_mkProd_or_LetIn'E; tea.
  rewrite /to_extended_list /to_extended_list_k.
  eapply spine_subst_to_extended_list_kE; tea.
  pcuic.
  eapply typing_spine_strengthenE; tea.
  now eapply isType_subst_all_relsE.
  eapply ws_cumul_pbE_eq_le. symmetry.
  exact (isType_all_rels_subst_liftE isty).
  rewrite -[X in lift _ X _](Nat.add_0_r #|Δ|).
  rewrite -lift_it_mkProd_or_LetIn.
  eapply isType_liftE; tea. now len.
  pcuic.
  rewrite skipn_app List.skipn_all /= Nat.sub_diag skipn_0.
  now eapply PCUICInductiveInversionEtaB.isType_it_mkProd_or_LetInE.
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
  now eapply PCUICInductiveInversionEtaB.isType_it_mkProd_or_LetInE.
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

Lemma inst_case_predicate_context_alpha_eqE {cf : checker_flags}	{Σ : global_env_ext} {wfΣ : wfE Σ}
  {mdecl idecl ci p} :
  eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
  eq_context_upto_names
    (map2 set_binder_name (forget_types (pcontext p))
      (inst_case_context (pparams p) (puinst p)
          (ind_predicate_context ci mdecl idecl)))
    (subst_context (List.rev (pparams p)) 0 (pcontext p)@[puinst p]).
Proof.
  intros a.
  eapply All2_trans. tc.
  { eapply eq_binder_annots_eq.
    rewrite /inst_case_context.
    apply All2_eq_binder_subst_context, All2_eq_binder_subst_instance.
    eapply All2_map_left, All2_impl; tea. intros x y []; auto. }
  { apply alpha_eq_subst_context, alpha_eq_subst_instance.
    now symmetry. }
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
        eapply PCUICInductiveInversionEtaB.isType_it_mkProd_or_LetInE; tea. simpl.
        eapply isType_SortE; tea.
        2:{ len. now rewrite PCUICLiftSubst.map_subst_instance_to_extended_list_k. }
        2:{ now len. }
        rewrite subst_context_length subst_instance_length lift_it_mkProd_or_LetIn /=.
        eapply typing_spine_it_mkProd_or_LetIn_closeE; tea.
        3:{ reflexivity. }
        2:{ eapply PCUICInductiveInversionEtaB.isType_it_mkProd_or_LetInE; tea.
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

Lemma ind_arity_relevantE {cf : checker_flags} (Σ : global_env_ext) mdecl idecl :
  wfE Σ.1 ->
  let ind_type := it_mkProd_or_LetIn (ind_params mdecl) (it_mkProd_or_LetIn (ind_indices idecl) (tSort (ind_sort idecl))) in
  isTypeE Σ [] ind_type ->
  isTypeRelE Σ [] ind_type rel_of_Type.
Proof.
  intros wfΣ ind_type (_ & s & Hs & _ & _).
  repeat (eexists; tea). cbn in Hs |- *.
  rewrite /ind_type in Hs.
  rewrite -it_mkProd_or_LetIn_app in Hs.
  eapply inversion_it_mkProd_or_LetInE in Hs.
  apply inversion_SortE in Hs as (_ & _ & le); tea.
  apply ws_cumul_pbE_Sort_inv in le.
  eapply leq_relevance; tea.
  eapply relevance_super.
Qed.
