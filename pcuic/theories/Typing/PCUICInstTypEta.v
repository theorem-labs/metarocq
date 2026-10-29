(* Distributed under the terms of the MIT license. *)
(** * [Typing/PCUICInstTyp] over [typingE]

  Type preservation of σ-calculus instantiation for [typingE]: [type_instE],
  [typing_instE]. The base file copied over [typingE], [wf_localE], [wfE] and
  [cumulSpecE0], with the substitution well typed in [typingE] ([well_substE],
  [Syntax/PCUICInstDefEta]). Each lemma that mentions typing or the well-formedness of
  the environment takes the suffix [E] and states its base twin with the relations
  renamed. It also copies the lemmas of [Conversion/PCUICInstConv] that read typing or
  [wf]: [inst_case_predicate_contextE], [closedn_ctx_cstr_branch_contextE],
  [inst_case_branch_context_genE], [inst_case_branch_typeE] and the [well_subst] lemmas
  [well_subst_extE] to [wf_local_app_instE].

  - The conversion rule and the guard's conversion witnesses go through
    [cumulSpecE_instP] and [convSpecE_instP] ([PCUICCumulativitySpecEtaClosure]), whose
    environment premise is [ClosedBodies]; [wfE] gives it ([wfE_ClosedBodies]). So
    [inst_mfix_on_indE] takes [ClosedBodies Σ.1] where its base twin takes [wf Σ].
  - The guard goes through [fix_guard_instE] and [cofix_guard_instE]
    ([PCUICGuardClosureEta]); their syntactic premises come from
    [typingE_closedn_mfix] and [well_substE_wf_cases] ([Typing/PCUICCasesWfTypEta]).
  - Going under a binder weakens the images of the substitution by
    [weakening_rename_typingE] ([Typing/PCUICWeakeningTypEta]).
  - The syntactic lemmas of the base files are used as they are.

  The proofs are base's. *)
From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst
  PCUICTyping PCUICReduction PCUICCumulativity
  PCUICEquality PCUICGlobalEnv PCUICClosed PCUICClosedConv PCUICClosedTyp PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICSigmaCalculus PCUICRenameDef PCUICRenameConv PCUICWeakeningConv PCUICWeakeningTyp PCUICInstDef PCUICInstConv
  PCUICGuardCondition PCUICUnivSubstitutionConv PCUICOnFreeVars PCUICOnFreeVarsConv PCUICCasesWfTyp
  PCUICInstTyp PCUICClosedBodies PCUICGuardClosure
  PCUICCumulativitySpecEta PCUICCumulativitySpecEtaClosure PCUICTypingEta PCUICTypingEtaInd
  PCUICClosedTypEta PCUICInstDefEta PCUICGuardClosureEta PCUICRenameTypEta PCUICWeakeningTypEta
  PCUICCasesWfTypEta.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
Set Equations With UIP.
Set Keyed Unification.
Set Default Goal Selector "!".
Implicit Types cf : checker_flags.

Local Open Scope sigma_scope.

(** ** The lemmas of [Conversion/PCUICInstConv] that read [wf] *)

Lemma inst_case_predicate_contextE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {ind mdecl idecl f p} :
  declared_inductive Σ ind mdecl idecl ->
  wf_predicate mdecl idecl p ->
  inst_context f (case_predicate_context ind mdecl idecl p) =
  case_predicate_context ind mdecl idecl (inst_predicate f p).
Proof.
  intros decli wfp.
  unfold case_predicate_context. simpl.
  unfold id. unfold case_predicate_context_gen.
  rewrite /inst_context.
  rewrite -map2_set_binder_name_fold //.
  - len. len.
    now rewrite -(wf_predicate_length_pcontext wfp).
  - f_equal. rewrite -/(inst_context f _).
    rewrite /pre_case_predicate_context_gen /inst_case_context.
    rewrite /ind_predicate_context /= !subst_instance_cons !subst_context_snoc inst_context_snoc.
    rewrite inst_context_subst map_rev. f_equal.
    * rewrite /map_decl /=. f_equal.
      len. rewrite inst_closedn_ctx //.
      epose proof (closedn_ctx_expand_lets 0 (ind_params mdecl) (ind_indices idecl)
      (declared_inductive_closed_pars_indicesE decli)).
      simpl in H.
      rewrite closedn_subst_instance_context.
      rewrite (wf_predicate_length_pars wfp).
      now rewrite (declared_minductive_ind_nparsE decli).
    * rewrite /map_decl /= /subst_decl /map_decl /=.
      f_equal. len. rewrite -map_rev.
      rewrite subst_instance_mkApps.
      rewrite !subst_inst inst_assoc.
      eapply (inst_ext_closed _ _ (context_assumptions (ind_params mdecl) + #|ind_indices idecl|)).
      + intros x hx.
        rewrite Upn_compose subst_consn_compose. sigma.
        rewrite Upn_subst_consn_lt; len.
        { rewrite ?(wf_predicate_length_pars wfp).
          rewrite (declared_minductive_ind_nparsE decli). lia. }
        rewrite Upn_subst_consn_lt //; len.
        { rewrite ?(wf_predicate_length_pars wfp).
          rewrite (declared_minductive_ind_nparsE decli). lia. }
      + rewrite closedn_mkApps /=.
        rewrite subst_instance_to_extended_list.
        relativize (_ + _); [eapply closedn_to_extended_list|].
        now len.
Qed.

Lemma closedn_ctx_cstr_branch_contextE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {c mdecl idecl cdecl} :
  declared_constructor Σ c mdecl idecl cdecl ->
  closedn_ctx (context_assumptions (ind_params mdecl)) (cstr_branch_context c.1 mdecl cdecl).
Proof.
  intros cl.
  rewrite /cstr_branch_context.
  apply (closedn_ctx_expand_lets 0).
  rewrite closedn_ctx_app.
  rewrite (declared_inductive_closed_paramsE cl) /=.
  eapply (closedn_ctx_subst 0) => /=; len.
  { rewrite Nat.add_comm (declared_constructor_closed_argsE cl) //. }
  eapply closed_inds.
Qed.

Lemma inst_case_branch_context_genE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {ind i idecl mdecl f p bctx cdecl} :
  declared_constructor Σ (ind, i) mdecl idecl cdecl ->
  #|bctx| = #|cstr_args cdecl| ->
  #|pparams p| = context_assumptions (ind_params mdecl) ->
  inst_context f (case_branch_context ind mdecl p bctx cdecl) =
  case_branch_context ind mdecl (inst_predicate f p) bctx
    (inst_constructor_body mdecl f cdecl).
Proof.
  intros declc hlen hlen'.
  unfold case_branch_context, case_branch_context_gen, pre_case_branch_context_gen.
  rewrite inst_context_set_binder_name; len => //. f_equal.
  rewrite inst_inst_case_context_wf.
  { rewrite test_context_k_closed_on_free_vars_ctx.
    rewrite -closedn_ctx_on_free_vars hlen'.
    apply (closedn_ctx_cstr_branch_contextE declc). }
  f_equal. f_equal.
  rewrite inst_closed_constructor_body //.
  apply (declared_constructor_closedE declc).
Qed.

Lemma inst_case_branch_typeE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} f (ci : case_info) i mdecl idecl p br cdecl :
  declared_constructor Σ (ci.(ci_ind), i) mdecl idecl cdecl ->
  wf_predicate mdecl idecl p ->
  wf_branch cdecl br ->
  let pctx := case_predicate_context ci mdecl idecl p in
  let ptm := it_mkLambda_or_LetIn pctx (preturn p) in
  let p' := inst_predicate f p in
  let pctx' := case_predicate_context ci mdecl idecl p' in
  let ptm' := it_mkLambda_or_LetIn pctx' (preturn p') in
  case_branch_type ci mdecl idecl
     (inst_predicate f p)
     (inst_branch f br)
     ptm' i (inst_constructor_body mdecl f cdecl) =
  map_pair (inst_context f) (inst (up #|bcontext br| f))
  (case_branch_type ci mdecl idecl p br ptm i cdecl).
Proof.
  intros decli wfp wfb ptm p' ptm'.
  rewrite /case_branch_type /case_branch_type_gen /map_pair /=.
  rewrite (inst_case_branch_context_genE decli) //.
  - len. apply (wf_branch_length wfb).
  - rewrite -(declared_minductive_ind_nparsE decli).
    apply (wf_predicate_length_pars wfp).
  - f_equal.
    rewrite inst_mkApps map_app map_map_compose.
    rewrite (wf_branch_length wfb).
    f_equal.
    * rewrite /ptm' /ptm !lift_it_mkLambda_or_LetIn !inst_it_mkLambda_or_LetIn.
      rewrite !lift_rename. f_equal.
      ++ rewrite /p'. len.
        epose proof (inst_context_lift f #|cstr_args cdecl| 0).
        rewrite Nat.add_0_r in H.
        rewrite H.
        rewrite /ptm. rewrite up_0.
        rewrite (inst_case_predicate_contextE decli) //.
      ++ rewrite /p' case_predicate_context_length //.
         { now apply inst_wf_predicate. }
        rewrite Nat.add_0_r. simpl.
        len. rewrite !up_Upn -Upn_Upn. rewrite - !lift_rename.
        rewrite Nat.add_comm inst_lift.
        rewrite /ptm case_predicate_context_length //.
    * rewrite /= inst_mkApps /=. f_equal.
      ++ rewrite !map_map_compose /id.
        generalize (declared_constructor_closed_indicesE decli).
        apply forallb_map_spec => t clt.
        rewrite !up_Upn.
        rewrite /expand_lets /expand_lets_k.
        rewrite -inst_subst_instance. len.
        rewrite inst_subst map_rev List.length_rev. f_equal.
        rewrite inst_subst. rewrite (wf_predicate_length_pars wfp).
        rewrite (declared_minductive_ind_nparsE decli).
        rewrite -{2}(context_assumptions_subst_instance (puinst p) (ind_params mdecl)).
        setoid_rewrite <- up_Upn at 1.
        rewrite inst_closed_extended_subst.
        { rewrite closedn_subst_instance_context.
          apply (declared_inductive_closed_paramsE decli). }
        f_equal. len. rewrite - !Upn_Upn.
        rewrite (Nat.add_comm _ (context_assumptions _)) inst_lift.
        f_equal. rewrite Nat.add_comm inst_subst.
        rewrite inst_inds. f_equal.
        rewrite - Upn_Upn. len.
        rewrite inst_closed ?closedn_subst_instance //.
        { eapply closed_upwards; tea; lia. }
        etransitivity.
        { eapply inst_ext. intros x.
          rewrite -(Upn_subst_instance _ _ _ _). reflexivity. }
        rewrite inst_closed ?closedn_subst_instance //.
        { eapply closed_upwards; tea; lia. }
      ++ unfold id. f_equal. f_equal.
        rewrite map_app map_map_compose.
        rewrite map_map_compose.
        setoid_rewrite up_Upn. len.
        f_equal.
        { apply map_ext. intros. now sigma. }
        rewrite inst_to_extended_list.
        now rewrite /to_extended_list /to_extended_list_k reln_fold.
Qed.

(** ** Well-typed substitutions in [typingE] *)

Section SigmaE.

Context `{cf: checker_flags}.

Lemma well_subst_extE Σ Δ σ σ' Γ :
  well_substE Σ Γ σ Δ ->
  σ =1 σ' ->
  well_substE Σ Γ σ' Δ.
Proof using Type.
  intros Hσ eq. destruct Hσ as [typed_σ Hσ]. split.
  - intros n decl hnth. rewrite -(eq n).
    eapply meta_convE. 2:now rewrite -eq. eapply typed_σ; eauto.
  - eapply usubst_ext; eauto.
Qed.

Lemma well_subst_UpE {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Δ σ na A} :
  wf_localE Σ (Δ ,, vass na A.[σ]) ->
  well_substE Σ Γ σ Δ ->
  well_substE Σ (Γ ,, vass na A) (⇑ σ) (Δ ,, vass na A.[σ]).
Proof using Type.
  intros hΔ h. split.
  - intros [|n] decl e.
    + simpl in *. inversion e. subst. clear e. simpl.
      eapply meta_convE.
      * econstructor ; auto.
        reflexivity.
      * simpl. now autorewrite with sigma.
    + sigma. specialize (h.1 _ _ e) as h1. sigma in h1.
      eapply meta_convE.
      * epose proof (weakening_rename_typingE (Γ' := []) (Γ'' := [_]) hΔ h1).
        simpl in X.
        sigma in X. eapply X.
      * eapply inst_ext. rewrite ren_lift_renaming.
        now sigma.
  - eapply usubst_Up; eauto; intuition auto with *.
Qed.

Lemma well_subst_Up'E {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Δ σ na t A} :
  wf_localE Σ (Δ ,, vdef na t.[σ] A.[σ]) ->
  well_substE Σ Γ σ Δ ->
  well_substE Σ (Γ ,, vdef na t A) (⇑ σ) (Δ ,, vdef na t.[σ] A.[σ]).
Proof using Type.
  intros wf h. split.
  - intros [|n] decl e.
    * simpl in *. inversion e. subst. clear e. simpl.
    rewrite lift_rename. rewrite rename_inst.
    autorewrite with sigma.
    eapply meta_convE.
      + econstructor; auto; reflexivity.
      + rewrite lift0_inst /=.
        now autorewrite with sigma.
   * cbn -[rshiftk] in *.
      specialize (h.1 _ _ e).
     sigma. sigma in h. intro.
      eapply meta_convE.
      + epose proof (weakening_rename_typingE (Γ' := []) (Γ'' := [_]) wf X).
        simpl in X0.
        sigma in X0. eapply X0.
      + eapply inst_ext. rewrite ren_lift_renaming.
        now sigma.
  - eapply usubst_Up'; eauto; intuition auto with *.
Qed.

Lemma well_subst_appE {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Δ σ Δ'} :
  wf_localE Σ (Δ ,,, inst_context σ Δ') ->
  well_substE Σ Γ σ Δ ->
  well_substE Σ (Γ ,,, Δ') (⇑^#|Δ'| σ) (Δ ,,, inst_context σ Δ').
Proof using Type.
  induction Δ' as [|[na [b|] ty] Δ']; simpl => hwf hsub.
  - eapply well_subst_extE; eauto.
    now rewrite Upn_0.
  - rewrite inst_context_snoc.
    eapply well_subst_extE.
    2:now rewrite Upn_S. simpl.
    apply well_subst_Up'E.
    * rewrite inst_context_snoc in hwf.
      apply hwf.
    * rewrite inst_context_snoc in hwf.
      depelim hwf. apply IHΔ' => //.
  - rewrite inst_context_snoc.
    eapply well_subst_extE.
    2:now rewrite Upn_S. simpl.
    apply well_subst_UpE.
    * rewrite inst_context_snoc in hwf.
      apply hwf.
    * rewrite inst_context_snoc in hwf.
      depelim hwf. apply IHΔ' => //.
Qed.

Lemma well_subst_app_upE {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Δ σ Δ'} :
  wf_localE Σ (Δ ,,, inst_context σ Δ') ->
  well_substE Σ Γ σ Δ ->
  well_substE Σ (Γ ,,, Δ') (up #|Δ'| σ) (Δ ,,, inst_context σ Δ').
Proof using Type.
  intros wf Hσ.
  eapply well_subst_extE.
  2:now rewrite up_Upn.
  now apply well_subst_appE.
Qed.

Lemma wf_local_app_instE (Σ : global_env_ext) {wfΣ : wfE Σ} Γ Δ :
  All_local_rel (fun Γ j =>
    forall Δ σ,
    wf_localE Σ Δ ->
    well_substE Σ Γ σ Δ ->
    lift_typing0 (fun t T => Σ ;;; Δ |-E t.[σ] : T.[σ]) j) Γ Δ ->
  forall Δ' σ,
  well_substE Σ Γ σ Δ' ->
  wf_localE Σ Δ' ->
  wf_localE Σ (Δ' ,,, inst_context σ Δ).
Proof using Type.
  intros.
  induction X using All_local_rel_ind1.
  - now simpl.
  - rewrite inst_context_snoc /=.
    apply All_local_env_snoc; auto.
    apply lift_typing_map with (j := j_decl _) => //.
    eapply X; tas.
    eapply well_subst_appE; auto.
Qed.

End SigmaE.

(** ** Type preservation *)

Definition well_subst_usubstE {cf} (Σ:global_env_ext) (wfΣ : wfE Σ) Γ σ Δ :
  is_closed_context Δ ->
  well_substE Σ Γ σ Δ ->
  usubst Γ σ Δ.
Proof.
  intuition eauto with *.
Defined.

Definition well_subst_closed_substE {cf} (Σ:global_env_ext) (wfΣ : wfE Σ) Γ σ Δ :
  is_closed_context Δ ->
  well_substE Σ Γ σ Δ ->
  closed_subst Γ σ Δ.
Proof.
  intros hΔ [typed_σ hσ]. repeat split; tea.
  intros x decl hnth. specialize (typed_σ x decl hnth) as htype.
  pose proof (typingE_wf_local htype). pose (wf_local_closed_contextE X).
  apply closedn_on_free_vars. eapply subject_closedE; eauto.
Defined.

(** Instantiation carries the witness of every body; [check] is one of
    [check_one_fix] and [check_one_cofix] ([inst_check_one_fix],
    [inst_check_one_cofix]). *)
Lemma inst_mfix_on_indE {cf : checker_flags} {Σ : global_env_ext} {cb : ClosedBodies Σ.1} {Γ Δ σ check ok mfix} :
  (forall d m, check d = Some m ->
    check (map_def (inst σ) (inst (up #|mfix| σ)) d) = Some m) ->
  closed_subst Γ σ Δ ->
  is_closed_context Γ ->
  All (fun d => is_open_term Γ (dtype d)) mfix ->
  mfix_on_ind check (conv_witnessE Σ Γ) ok mfix ->
  mfix_on_ind check (conv_witnessE Σ Δ) ok (map (map_def (inst σ) (inst (up #|mfix| σ))) mfix).
Proof.
  intros hc hσ hΓ hop.
  eapply mfix_on_ind_map; [exact hop| |easy].
  intros d m hopd [ty [hcd [hty hconv]]].
  exists ty.[σ]; split; [|split].
  - rewrite map_def_with_type. now apply hc.
  - now eapply inst_is_open_term.
  - now eapply convSpecE_instP.
Qed.

Lemma type_instE {cf : checker_flags} : env_propE
  (fun Σ Γ t A =>
    forall Δ σ,
    wf_localE Σ Δ ->
    well_substE Σ Γ σ Δ ->
    Σ ;;; Δ |-E t.[σ] : A.[σ])
  (fun Σ Γ j =>
    forall Δ σ,
    wf_localE Σ Δ ->
    well_substE Σ Γ σ Δ ->
    lift_typing0 (fun t T => Σ ;;; Δ |-E t.[σ] : T.[σ]) j)
  (fun Σ Γ =>
    All_local_env (fun Γ j =>
    forall Δ σ,
    wf_localE Σ Δ ->
    well_substE Σ Γ σ Δ ->
    (lift_typing0 (fun (t T : term) => Σ ;;; Δ |-E t.[σ] : T.[σ])) j) Γ).
Proof.
  apply typingE_ind_env.

  - intros Σ wfΣ Γ j H Δ σ wfΔ Hσ.
    apply lift_typing_impl with (1 := H) => t T [_ IH].
    now apply IH.

  - intros Σ wfΣ Γ wfΓ _ X. assumption.
  - intros Σ wfΣ Γ wfΓ n decl e X Δ σ hΔ hσ. simpl.
    eapply hσ. assumption.
  - intros Σ wfΣ Γ wfΓ l X H0 Δ σ hΔ hσ. simpl.
    econstructor. all: assumption.
  - intros Σ wfΣ Γ wfΓ na A B s1 s2 X hA ihA hB ihB Δ σ hΔ hσ.
    autorewrite with sigma. simpl.
    assert (ihA' : lift_typing0 (typingE Σ Δ) (j_vass_s na A.[σ] s1)) by now eapply ihA.
    econstructor; tas.
    apply lift_sorting_forget_univ in ihA'.
    eassert (wf_localE Σ (Δ ,, _)) by (constructor; eassumption).
    eapply ihB; tea.
    eapply well_subst_UpE ; assumption.
  - intros Σ wfΣ Γ wfΓ na A t bty X hA ihA ht iht Δ σ hΔ hσ.
    autorewrite with sigma.
    assert (ihA' : lift_typing0 (typingE Σ Δ) (j_vass na A.[σ])) by now eapply ihA.
    econstructor; tas.
    eassert (wf_localE Σ (Δ ,, _)) by (constructor; eassumption).
    eapply iht; tea.
    eapply well_subst_UpE ; assumption.
  - intros Σ wfΣ Γ wfΓ na b B t A X hbB ihbB ht iht Δ σ hΔ hσ.
    autorewrite with sigma.
    assert (ihbB' : lift_typing0 (typingE Σ Δ) (j_vdef na b.[σ] B.[σ])) by now eapply ihbB.
    econstructor; tas.
    eassert (wf_localE Σ (Δ ,, _)) by (constructor; eassumption).
    eapply iht; tea.
    eapply well_subst_Up'E; try assumption.
  - intros Σ wfΣ Γ wfΓ t na A B s u X hty ihty ht iht hu ihu Δ σ hΔ hσ.
    autorewrite with sigma.
    econstructor.
    * specialize (ihty _ _ hΔ hσ).
      simpl in ihty. eapply meta_conv_termE; [eapply ihty|].
      now rewrite up_Up.
    * specialize (iht _ _ hΔ hσ).
      simpl in iht. eapply meta_convE; [eapply iht|].
      now rewrite up_Up.
    * eapply ihu; auto.
  - intros Σ wfΣ Γ wfΓ cst u decl X X0 isdecl hconst Δ σ hΔ hσ.
    autorewrite with sigma. simpl.
    eapply meta_convE; [econstructor; eauto|].
    eapply declared_constant_closed_typeE in isdecl; eauto.
    rewrite inst_closed0; auto.
    now rewrite closedn_subst_instance.
  - intros Σ wfΣ Γ wfΓ ind u mdecl idecl isdecl X X0 hconst Δ σ hΔ hσ.
    eapply meta_convE; [econstructor; eauto|].
    eapply declared_inductive_closed_typeE in isdecl; eauto.
    rewrite inst_closed0; auto.
    now rewrite closedn_subst_instance.
  - intros Σ wfΣ Γ wfΓ ind i u mdecl idecl cdecl isdecl X X0 hconst Δ σ hΔ hσ.
    eapply meta_convE; [econstructor; eauto|].
    eapply declared_constructor_closed_typeE in isdecl; eauto.
    rewrite inst_closed0; eauto.
  - intros Σ wfΣ Γ wfΓ ci p c brs indices ps mdecl idecl isdecl HΣ.
    intros IHΔ ci_npar eqpctx predctx wfp cup Hpctx Hpret
      IHpret IHpredctx isallowed Her.
    intros IHctxi Hc IHc iscof ptm wfbrs Hbrs Δ f HΔ Hf.
    assert (iscof' : (isCoFinite (ind_finite mdecl) ==>
      on_free_vars (strengthenP 0 1 xpredT) (preturn (inst_predicate f p))) = true).
    { apply/implyP => hcof. move/implyP: iscof => /(_ hcof) h.
      rewrite -inst_predicate_preturn.
      eapply (on_free_vars_nondep_inst _ (shiftnP #|Γ| xpred0)); [| | |exact h].
      - rewrite (wf_predicate_length_pcontext wfp). lia.
      - intros i. rewrite /shiftnP => /orP [/Nat.ltb_spec0 hi|hi]; [|now cbv in hi].
        destruct (nth_error Γ i) as [decl|] eqn:hnth.
        2:{ apply nth_error_None in hnth. lia. }
        eapply on_free_vars_impl; [|exact (subject_is_open_termE (Hf.1 _ _ hnth))]. done.
      - pose proof (subject_is_open_termE Hpret) as hop.
        rewrite app_context_length -shiftnP_add in hop.
        now rewrite /predctx case_predicate_context_length in hop. }
    autorewrite with sigma. simpl.
    rewrite map_app. simpl.
    rewrite /ptm. rewrite inst_it_mkLambda_or_LetIn.
    relativize #|predctx|.
    * erewrite inst_predicate_preturn.
      rewrite /predctx.
      rewrite inst_case_predicate_contextE //.
      eapply typeE_Case; eauto;
       rewrite - ?inst_case_predicate_contextE //.
      3,4 : constructor; eauto;
        rewrite - ?inst_case_predicate_contextE //.
      + apply All_local_env_app_inv in Hpctx as [].
        apply All_local_env_app_inv in IHpredctx as [].
        eapply IHpret.
        ++ eapply wf_local_app_instE; eauto.
        ++ relativize #|pcontext p|; [eapply well_subst_app_upE|] => //; rewrite /predctx; len.
           2:{ rewrite case_predicate_context_length //. }
           eapply wf_local_app_instE; eauto.
      + simpl. unfold id.
        specialize (IHc _ _ HΔ Hf).
        now rewrite inst_mkApps map_app in IHc.
      + now eapply inst_wf_predicate.
      + simpl.
        apply All_local_env_app_inv in Hpctx as [].
        eapply wf_local_app_instE; eauto.
        apply All_local_env_app_inv in IHpredctx as [].
        apply a2.
      + revert IHctxi.
        rewrite /= /id -map_app.
        rewrite -{2}[subst_instance _ _](inst_closedn_ctx f 0).
        { pose proof (declared_inductive_closed_pars_indicesE isdecl).
          now rewrite closedn_subst_instance_context. }
        rewrite inst_context_telescope.
        rewrite inst_telescope_upn0.
        clear -Δ f HΔ Hf.
        induction 1.
        { constructor; auto. }
        { destruct t0; simpl. rewrite inst_telescope_cons.
          constructor; cbn; eauto.
          now rewrite inst_subst_telescope /= in IHIHctxi. }
        { simpl. rewrite inst_telescope_cons.
          constructor; cbn; eauto.
          now rewrite inst_subst_telescope /= in IHIHctxi. }
      + now eapply inst_wf_branches.
      + eapply Forall2_All2 in wfbrs.
        eapply All2i_All2_mix_left in Hbrs; eauto.
        eapply All2i_nth_hyp in Hbrs.
        eapply All2i_map_right, (All2i_impl Hbrs) => i cdecl br.
        set (brctxty := case_branch_type _ _ _ _ _ _ _ _).
        intros (Hnth & wfbr & Hconv & Hbrctx & (Hbr & IHbr) & Hbty & IHbty).
        split => //.
        rewrite -(inst_closed_constructor_body mdecl cdecl f).
        { eapply (declared_constructor_closedE (c:=(ci.(ci_ind),i))); eauto.
          split; eauto. }
        rewrite inst_case_predicate_contextE //.
        rewrite inst_case_branch_typeE //.
        rewrite -/brctxty. intros brctx'.
        assert (wf_localE Σ (Δ,,, brctx'.1)).
        { rewrite /brctx'. cbn.
          apply All_local_env_app_inv in Hbrctx as [].
          eapply wf_local_app_instE; tea. }
        split => //. split.
        ++ eapply IHbr => //.
          rewrite /brctx' /brctxty; cbn.
          relativize #|bcontext br|.
          { eapply well_subst_app_upE => //. }
          rewrite /case_branch_type /=.
          rewrite case_branch_context_length //.
        ++ eapply IHbty=> //.
          rewrite /brctx'; cbn.
          relativize #|bcontext br|.
          { eapply well_subst_app_upE => //. }
          rewrite /brctxty /= case_branch_context_length //.
    * rewrite /predctx case_predicate_context_length //.
  - intros Σ wfΣ Γ wfΓ p c u mdecl idecl cdecl pdecl isdecl args X X0 hc ihc e
           Δ σ hΔ hσ.
    simpl.
    eapply meta_convE; [econstructor|].
    * eauto.
    * specialize (ihc _ _ hΔ hσ).
      rewrite inst_mkApps in ihc. eapply ihc.
    * now rewrite length_map.
    * autorewrite with sigma.
      eapply declared_projection_closedE in isdecl; auto.
      move: isdecl.
      rewrite -(closedn_subst_instance _ _ u).
      eapply inst_ext_closed.
      intros x Hx.
      rewrite subst_consn_lt /=; len; try lia.
      rewrite Upn_comp; cbn; try now repeat len.
      rewrite subst_consn_lt /=; cbn; len; try lia.
      now rewrite map_rev.
  - intros Σ wfΣ Γ wfΓ mfix n decl types hguard hnth htypes hmfixt ihmfixt hmfixb ihmfixb wffix Δ σ hΔ hσ.
    simpl. eapply meta_convE; [econstructor;eauto|].
    * eapply fix_guard_instE.
      + exact hσ.
      + eapply typingE_closedn_mfix; tea.
      + now eapply well_substE_wf_cases.
      + exact hguard.
    * now rewrite nth_error_map hnth.
    * apply All_map, (All_impl ihmfixt).
      intros x t. eapply t; eauto.
    * pose proof (inst_fix_context mfix σ).
      setoid_rewrite <-up_Upn at 1 in H. rewrite H.
      apply All_map, (All_impl ihmfixb).
      unfold on_def_body.
      intros x t. relativize (lift0 _ _).
      1: eenough (wf_localE Σ (Δ ,,, _)).
      1: eapply t; eauto.
      + rewrite -(fix_context_length mfix).
        eapply well_subst_app_upE => //.
      + eapply wf_local_app_instE; eauto.
        now eapply All_local_env_app_inv in htypes as [].
      + cbn [j_typ]. rewrite lift0_inst /types inst_context_length fix_context_length.
        now sigma.
    * destruct wffix as (isl & hra & hon). split; [|split].
      1: rewrite forallb_map; refine (forallb_impl _ _ _ _ isl); intros x _ h.
      1: now eapply isLambda_inst.
      1: rewrite forallb_map; refine (forallb_impl _ _ _ _ hra); intros x _ h.
      1: now eapply inst_has_rec_arg.
      eapply (inst_mfix_on_indE (cb := @wfE_ClosedBodies _ Σ.1 wfΣ)); tea.
      1: exact (inst_check_one_fix σ mfix).
      1: eapply well_subst_closed_substE; tea; eapply wf_local_closed_contextE; tea.
      1: eapply wf_local_closed_contextE; tea.
      eapply (All_impl hmfixt) => d hd.
      now eapply isTypeRel_is_open_termE, hd.
    * reflexivity.

  - intros Σ wfΣ Γ wfΓ mfix n decl types hguard hnth htypes hmfixt ihmfixt hmfixb ihmfixb wffix Δ σ hΔ hσ.
    simpl. eapply meta_convE; [econstructor;eauto|].
    * eapply cofix_guard_instE.
      + exact hσ.
      + eapply typingE_closedn_mfix; tea.
      + now eapply well_substE_wf_cases.
      + exact hguard.
    * now rewrite nth_error_map hnth.
    * apply All_map, (All_impl ihmfixt).
      intros x t. eapply t; eauto.
    * pose proof (inst_fix_context mfix σ).
      setoid_rewrite <-up_Upn at 1 in H. rewrite H.
      apply All_map, (All_impl ihmfixb).
      unfold on_def_body.
      intros x t. relativize (lift0 _ _).
      1: eenough (wf_localE Σ (Δ ,,, _)).
      1: eapply t; eauto.
      + rewrite -(fix_context_length mfix).
        eapply well_subst_app_upE => //.
      + eapply wf_local_app_instE; eauto.
        now eapply All_local_env_app_inv in htypes as [].
      + cbn [j_typ]. rewrite lift0_inst /types inst_context_length fix_context_length.
        now sigma.
    * eapply (inst_mfix_on_indE (cb := @wfE_ClosedBodies _ Σ.1 wfΣ)); tea.
      1: exact (inst_check_one_cofix σ mfix).
      1: eapply well_subst_closed_substE; tea; eapply wf_local_closed_contextE; tea.
      1: eapply wf_local_closed_contextE; tea.
      eapply (All_impl hmfixt) => d hd.
      now eapply isTypeRel_is_open_termE, hd.
    * reflexivity.

  - intros Σ wfΣ Γ wfΓ p pty cdecl _ hp hdecl pinv hty hind Δ σ hΔ hσ.
    cbn. rewrite inst_prim_type. econstructor; tea.
    1-2:now rewrite prim_val_tag_map.
    depelim hind; constructor; cbn; eauto. solve_all.

  - intros Σ wfΣ Γ wfΓ t A B X hwf ht iht hB ihB hcum Δ σ hΔ hσ.
    eapply typeE_Cumul.
    + eapply iht. all: auto.
    + eapply ihB. all: auto.
    + eapply cumulSpecE_instP => //.
      * exact (@wfE_ClosedBodies _ Σ.1 wfΣ).
      * eapply well_subst_closed_substE; tea. eapply wf_local_closed_contextE; tea.
      * eapply wf_local_closed_contextE; tea.
      * eapply type_closedE in ht.
        now eapply closedn_on_free_vars.
      * eapply subject_closedE in hB.
        now eapply closedn_on_free_vars.
      * apply hcum.
Qed.

Lemma typing_instE {cf : checker_flags} Σ Γ t A Δ σ {wfΣ : wfE Σ.1} :
  wf_localE Σ Δ ->
  well_substE Σ Γ σ Δ ->
  Σ ;;; Γ |-E t : A ->
  Σ ;;; Δ |-E t.[σ] : A.[σ].
Proof.
  intros a b c; revert a b. eapply type_instE; eauto.
Qed.
