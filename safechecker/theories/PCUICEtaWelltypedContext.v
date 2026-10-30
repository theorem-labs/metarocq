(* Distributed under the terms of the MIT license. *)
(* The header is base [PCUICPositionEta]'s ([PCUICPositionEta.v:23-49], with its [ssreflect] import of
   [:1941], which precedes the copied lemmas there), so that the copied scripts run with the same
   tactics; then the E modules whose lemmas replace base's. *)
From Stdlib Require Import RelationClasses ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.Common Require Import PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICInduction
     PCUICReflect PCUICEquality PCUICLiftSubst PCUICSigmaCalculus PCUICCases
     PCUICAstUtils PCUICUnivSubst PCUICTyping
     PCUICCasesContexts PCUICGlobalEnv
     PCUICAlpha PCUICInversion PCUICSubstitution
     PCUICContextConversion PCUICContextConversionTyp PCUICValidity PCUICArities
     PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
     PCUICOnFreeVars PCUICSpine PCUICInductives PCUICReduction
     PCUICWellScopedCumulativity PCUICCumulativity PCUICSR
     PCUICWeakeningTyp PCUICContexts PCUICInductiveInversion.
Import MonadNotation.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
Local Set Keyed Unification.
Set Default Goal Selector "!".
From Stdlib Require Import ssreflect.
(* The E side. [PCUICAritiesEta]'s [typing_spineE] is the canonical one (C6). *)
From MetaRocq.PCUIC Require Import PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
     PCUICTypingEtaNotions PCUICClosedBodies PCUICClosedTypEta PCUICWellScopedCumulativityEta
     PCUICContextConversionEta PCUICWsCumulEtaCtx PCUICWsCumulEtaInstancesGlobal PCUICInversionEta
     PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICSpineEta PCUICInductivesEta
     PCUICValidityEta.
From MetaRocq.PCUIC.Typing Require Import PCUICContextConversionTypEta.
From MetaRocq.PCUIC Require PCUICWeakeningTypEta PCUICInductiveInversionEtaB PCUICConversion PCUICConfluence.
(* The η stack (zip, stack_context, no_Eta_arg); base [PCUICPosition] is not imported (C6). *)
From MetaRocq.PCUIC Require Import PCUICPositionEta.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(** * ETAK discharge, row 51: [welltypedE_context] (the field of [WelltypedEContextE])

  BET-64 EtaCheckerLane, worker EtaTranscribe6, 2026-10-30. Row 51 of
  [lanes/eta/etak/eta51-sizing.md] (TRANSCRIPTION). The E twins of base [PCUICPositionEta]'s
  [wf_inst_case_context] ([PCUICPositionEta.v:2540]), [wf_case_inst_case_context] ([:2561]) and
  [welltyped_context] ([:2599], the η stack, base typing). Each is base's statement with [typing] →
  [typingE], [welltyped] → [welltypedE], [wf] → [wfE], [wf_local] → [wf_localE], [isType] → [isTypeE],
  [spine_subst] → [spine_substE], [wf_local_rel] → [wf_local_relE], and the context relation
  [Σ ⊢ Γ = Γ'] → [ws_cumul_ctx_pbE Conv Σ Γ Γ']. Base's script, each lemma replaced by its landed E twin:
  the E inversions ([PCUICInversionEta]); [validityE], [inversion_mkAppsE] ([PCUICValidityEta]);
  [context_conversionE], [closed_context_conversionE] ([Typing/PCUICContextConversionTypEta]);
  [typingE_wf_local] ([PCUICTypingEtaInd]); [isTypeRelE_welltypedE] ([PCUICTypingEtaNotions]);
  [substitution_wf_localE] ([PCUICSubstitutionEta]); [wf_local_smash_endE] ([PCUICContextsEta]);
  [PCUICWeakeningTypEta.weaken_wf_localE] (the twin of [PCUICWeakeningTyp.weaken_wf_local]; C6 names
  two); [ctx_inst_spine_substE], [ctx_inst_subE], [spine_subst_app_invE], [spine_subst_smashE],
  [wf_local_alphaE] ([PCUICSpineEta], copy 15); [on_minductive_wf_params_indices_instE],
  [wf_ind_predicateE] ([PCUICInductivesEta], copy 16); [declared_minductive_ind_nparsE]
  ([Typing/PCUICClosedTypEta]); [eq_context_upto_names_conv_contextE] ([PCUICWsCumulEtaCtx]);
  [ws_cumul_ctx_pbE_refl] ([PCUICContextConversionEta]); and from copy 18b
  ([PCUICInductiveInversionEtaB], frac/eta 3e6b422d): [wf_case_branch_typeE], [isType_mkApps_Ind_smashE].
  Three script changes besides the renaming: in [wf_case_inst_case_contextE], base's [pcuic] search for
  [wf_local Σ Γ] is [isType_wf_localE] ([PCUICSubstitutionEta]) and base's [fvs] search for the closedness
  of the branch context is [wf_local_closed_contextE] ([Typing/PCUICClosedTypEta]), named explicitly;
  and [PCUICAlpha.inst_case_predicate_context_eq], whose [wf Σ] binder is unused, is
  [inst_case_predicate_context_eq_untyped] below. The other untyped lemmas
  ([PCUICCasesContexts.inst_case_branch_context_eq], [alpha_eq_subst_instance],
  [wf_predicate_length_pars], ...) are base's. No hypothesis. *)

(** Base [PCUICAlpha.inst_case_predicate_context_eq] ([PCUICAlpha.v:302]) without its binders
    [{Σ : global_env_ext} {wfΣ : wf Σ}], which its statement does not mention and its proof does not use
    ([Proof using Type]); over E there is no [wf Σ] to give it. Proof unchanged (bullets added for the
    goal selector [!] of this file). *)
Lemma inst_case_predicate_context_eq_untyped {ind mdecl idecl p} :
  wf_predicate mdecl idecl p ->
  eq_context_upto_names (ind_predicate_context ind mdecl idecl) (pcontext p) ->
  eq_context_upto_names (case_predicate_context ind mdecl idecl p) (inst_case_predicate_context p).
Proof.
  intros wfp eq.
  rewrite /case_predicate_context /case_predicate_context_gen.
  epose proof (wf_pre_case_predicate_context_gen wfp).
  etransitivity.
  - now apply eq_binder_annots_eq_ctx.
  - rewrite /pre_case_predicate_context_gen /inst_case_predicate_context.
    rewrite /inst_case_context.
    eapply PCUICConversion.eq_context_upto_names_subst_context.
    now eapply PCUICConfluence.eq_context_upto_names_univ_subst_preserved.
Qed.

(** Base [wf_inst_case_context] ([PCUICPositionEta.v:2540]). *)
Lemma wf_inst_case_contextE {cf Σ} {wfΣ : wfE Σ} {Γ} {ci : case_info}
  {mdecl idecl} {uinst params} ctx :
  declared_inductive Σ ci mdecl idecl ->
  wf_localE Σ Γ ->
  consistent_instance_ext Σ (ind_universes mdecl) uinst ->
  spine_substE Σ Γ params (List.rev params) (smash_context [] (subst_instance uinst (ind_params mdecl))) ->
  wf_local_relE Σ (Γ,,, smash_context [] (ind_params mdecl)@[uinst]) ctx@[uinst] ->
  wf_localE Σ (Γ ,,, inst_case_context params uinst ctx).
Proof.
  move=> isdecl wfΓ cu sp wfr.
  rewrite /pre_case_predicate_context_gen /inst_case_context /ind_predicate_context /=.
  eapply substitution_wf_localE.
  * eapply sp.
  * unshelve epose proof (on_minductive_wf_params_indices_instE isdecl _ cu).
  rewrite PCUICUnivSubstitutionConv.subst_instance_app_ctx in X.
  eapply All_local_env_app_inv in X as [].
  eapply All_local_env_app => //.
  eapply wf_local_smash_endE.
  now eapply PCUICWeakeningTypEta.weaken_wf_localE; tea.
Qed.

(** Base [wf_case_inst_case_context] ([PCUICPositionEta.v:2561]). *)
Lemma wf_case_inst_case_contextE {cf Σ} {wfΣ : wfE Σ}
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
    eq_context_upto_names (bcontext br) (cstr_branch_context ci mdecl cdecl) ->
    wf_localE Σ (Γ ,,, inst_case_context (pparams p) (puinst p) br.(bcontext)) ×
     ws_cumul_ctx_pbE Conv Σ (Γ ,,, inst_case_context (pparams p) (puinst p) br.(bcontext))
         (Γ ,,, case_branch_context ci mdecl p (forget_types br.(bcontext)) cdecl).
Proof.
  intros isdecl Hc wfp bc Hp ptm wfpctx.
  intros i cdecl br declc wfbr onctx.
  destruct (PCUICInductiveInversionEtaB.wf_case_branch_typeE ps args isdecl Hc wfp Hp wfpctx _ _ _ declc wfbr)
    as []; auto.
  have wfΓ : wf_localE Σ Γ by exact (isType_wf_localE Hc).
  eapply PCUICInductiveInversionEtaB.isType_mkApps_Ind_smashE in Hc as [? []]; tea.
  2:{ now rewrite (wf_predicate_length_pars wfp). }
  have wfctx : wf_localE Σ (Γ,,, inst_case_branch_context p br).
  { erewrite <- PCUICCasesContexts.inst_case_branch_context_eq; tea. apply a1. }
  split => //.
  rewrite PCUICCasesContexts.inst_case_branch_context_eq //.
  pose proof (wfE_ClosedBodies Σ.1) as cbΣ.
  eapply ws_cumul_ctx_pbE_refl. exact (wf_local_closed_contextE wfctx).
Qed.

(* Base's section [EtaWelltyped] ([Context (Σ) (hΣ : wf Σ)]) is written as the lemma's own binders here,
   so that no new section binder appears to the hypothesis enumerator; the compiled statement is the
   one the section would give ([forall {cf} (Σ) (hΣ : wfE Σ), ...]). *)

  (** Base [welltyped_context] ([PCUICPositionEta.v:2599]), over [typingE]: the field
      [welltypedE_context] of [WelltypedEContextE] (row 51). *)
  Lemma welltypedE_contextE {cf : checker_flags} (Σ : global_env_ext) (hΣ : wfE Σ) :
    forall Γ t, no_Eta_arg (snd t) ->
      welltypedE Σ Γ (zip t) ->
      welltypedE Σ (Γ ,,, stack_context (snd t)) (fst t).
  Proof.
    intros Γ [t π] hna h. simpl in *.
    destruct h as [T h].
    induction π as [|a π IHπ] in Γ, t, T, h, hna |- *.
    1: { econstructor; eauto. }
    cbn in hna. move: hna => /andP [ha hπ].
    destruct a; cbn in ha; try discriminate ha; simpl in *.
    all: apply (IHπ _ _ hπ) in h as (?&typ).
    all: try apply inversion_AppE in typ as (?&?&?&?&?&?); auto.
    all: try apply inversion_ProjE in typ as (?&?&?&?&?&?&?&?&?); auto.
    all: try apply inversion_ProdE in typ as (?&?&?&?&?); auto.
    all: try apply inversion_LambdaE in typ as (?&?&?&?); auto.
    all: try apply inversion_LetInE in typ as (?&?&?&?); auto.
    all: try solve [econstructor; eauto].
    - apply inversion_FixE in typ as (?&?&?&?&?&?&?); eauto.
      destruct mfix as ((?&[])&?); simpl in *.
      + eapply All_app in a as (_&a).
        depelim a.
        eauto using isTypeRelE_welltypedE.
      + eapply All_app in a0 as (_&a0).
        depelim a0. destruct o as (t0 & _); cbn in t0.
        rewrite fix_context_fix_context_alt in t0.
        rewrite map_app in t0.
        simpl in t0.
        rewrite app_context_assoc.
        econstructor; eauto.
    - apply inversion_CoFixE in typ as (?&?&?&?&?&?&?); eauto.
      destruct mfix as ((?&[])&?); simpl in *.
      + eapply All_app in a as (_&a).
        depelim a.
        eauto using isTypeRelE_welltypedE.
      + eapply All_app in a0 as (_&a0).
        depelim a0. destruct o as (t0 & _); cbn in t0.
        rewrite fix_context_fix_context_alt in t0.
        rewrite map_app in t0.
        simpl in t0.
        rewrite app_context_assoc.
        econstructor; eauto.
    - apply inversion_CaseE in typ as (?&?&?&?&[]&?); auto.
      rewrite app_context_assoc.
      destruct p.
      + apply validityE in scrut_ty as (_ & ? & typ & _).
        clear brs_ty.
        apply inversion_mkAppsE in typ as (?&_&spine); auto; simpl in *.
        clear -spine.
        rewrite -app_assoc -app_comm_cons in spine.
        revert spine; generalize (tSort x3); intros t' spine.
        induction params1 in spine, x4, t' |- *; cbn in *.
        * depelim spine.
          econstructor; eauto.
        * depelim spine; eauto.
      + cbn. exists (tSort ps).
        cbn. move: pret_ty. cbn [fill_predicate_hole preturn].
        move=> Ht.
        cbn [fill_predicate_hole preturn] in predctx.
        eapply context_conversionE; tea.
        * unfold predctx in Ht.
          eapply typingE_wf_local in scrut_ty.
          eapply wf_inst_case_contextE; tea.
          ** cbn in ind_inst.
             unshelve epose proof (ctx_inst_spine_substE _ ind_inst).
             { eapply PCUICWeakeningTypEta.weaken_wf_localE; tea.
               eapply (on_minductive_wf_params_indices_instE x1); tas. }
              move: X. generalize (ctx_inst_subE ind_inst).
              intros l.
              rewrite subst_instance_app => X.
              unshelve epose proof (spine_subst_app_invE _ X) as [sp _].
              { rewrite (wf_predicate_length_pars wf_pred). len.
                eapply (declared_minductive_ind_nparsE x1). }
              now eapply spine_subst_smashE in sp.
          ** cbn in conv_pctx.
             eapply All_local_env_app_inv. eapply wf_local_alphaE.
             ++ instantiate (1 := (Γ,,, stack_context π,,, smash_context [] (ind_params x)@[puinst],,, (ind_predicate_context ci x x0)@[puinst])).
                eapply All2_app => //.
                { eapply alpha_eq_subst_instance. now symmetry. }
                reflexivity.
             ++ eapply wf_ind_predicateE; tea.

        * rewrite /predctx.
          cbn in conv_pctx.
          rewrite /case_predicate_context /= /case_predicate_context_gen.
          rewrite /pre_case_predicate_context_gen.
          rewrite /inst_case_context.
          apply eq_context_upto_names_conv_contextE.
          eapply All2_app. 2:{ reflexivity. }
          apply (inst_case_predicate_context_eq_untyped (ind:=ci) wf_pred).
          cbn. now symmetry.

    - apply inversion_CaseE in typ as (?&?&?&?&[]&?); auto.
      econstructor; eauto.
    - apply inversion_CaseE in typ as (mdecl&idecl&decli&args&[]&?); auto.
      destruct brs as ((?&?)&?).
      simpl fill_branches_hole in brs_ty.
      destruct b; cbn in *.
      set (br := {| bcontext := bcontext; bbody := t |}) in *.
      apply All2i_app_inv_r in brs_ty as (?&?&?&?&a).
      eapply All2i_length in a0.
      depelim a. clear a.
      destruct p0 as (wfl&(cc&typ&r)). clear r.
      rewrite -app_assoc.
      eexists.
      pose proof (typingE_wf_local scrut_ty).
      eapply validityE in scrut_ty.
      have declc : declared_constructor Σ (ci, #|x|) mdecl idecl x1.
      { split; auto. rewrite e /= nth_error_app_ge // Nat.sub_diag //. }
      have wf_branch : wf_branch x1 {| bcontext := bcontext; bbody := t |}.
      { eapply Forall2_All2 in wf_brs. eapply All2_nth_error with (n := #|x|) in wf_brs; tea.
        * rewrite e /= nth_error_app_ge // Nat.sub_diag //.
        * rewrite a0 /= nth_error_app_ge // Nat.sub_diag //. }
      destruct (wf_case_inst_case_contextE ps args decli scrut_ty wf_pred pret_ty conv_pctx
        _ _ _ declc wf_branch wfl).
      cbn in *.
      eapply closed_context_conversionE; tea.
      now symmetry.
    - apply unlift_TypUniv in l. now econstructor.
    - now eapply isTypeRelE_welltypedE.
    - apply unlift_TermTyp in l. now econstructor.
    - apply lift_sorting_forget_body in l. now eapply isTypeRelE_welltypedE.
    - eapply inversion_PrimE in typ as (?&?&[]); eauto.
      depelim p0. now eexists.
    - eapply inversion_PrimE in typ as (?&?&[]); eauto.
      depelim p0. now eexists.
    - eapply inversion_PrimE in typ as (?&?&[]); eauto.
      depelim p0. cbn in *.
      eapply All_app in hvalue as [_ hvalue]. depelim hvalue.
      now eexists.
  Qed.
