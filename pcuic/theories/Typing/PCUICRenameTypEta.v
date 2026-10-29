(* Distributed under the terms of the MIT license. *)
(** * [Typing/PCUICRenameTyp] over [typingE]

  Type preservation of renaming for [typingE]: [typing_rename_propE],
  [typing_rename_PE], [typing_renameE]. The base file copied over [typingE],
  [wf_localE], [wfE] and [cumulSpecE0]; each lemma that mentions typing or the
  well-formedness of the environment takes the suffix [E] and states its base twin
  with the relations renamed. [renamingE] is base [renaming] ([PCUICRenameDef]) with
  [wf_localE] for [wf_local].

  - The conversion rule and the guard's conversion witnesses go through
    [cumulSpecE_renameP] and [convSpecE_renameP] ([PCUICCumulativitySpecEtaClosure]),
    whose environment premise is [ClosedBodies]; [wfE] gives it
    ([wfE_ClosedBodies]). So [rename_mfix_on_indE] takes [ClosedBodies Σ.1] where its
    base twin takes [wf Σ.1].
  - The guard goes through base [fix_guard_rename] and [cofix_guard_rename], which
    mention no typing.
  - The syntactic lemmas of the base file are used as they are.

  The proofs are base's. *)
From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICCumulativity
  PCUICTyping PCUICReduction PCUICGlobalEnv PCUICClosed PCUICEquality PCUICRenameDef
  PCUICSigmaCalculus PCUICOnFreeVars PCUICOnFreeVarsConv PCUICGuardCondition
  PCUICWeakeningEnvConv PCUICWeakeningEnvTyp PCUICClosedConv PCUICClosedTyp PCUICRenameConv
  PCUICRenameTyp PCUICClosedBodies
  PCUICCumulativitySpecEta PCUICCumulativitySpecEtaClosure PCUICTypingEta PCUICTypingEtaInd
  PCUICClosedTypEta.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
Set Equations With UIP.

Local Open Scope sigma_scope.
Set Keyed Unification.

Set Default Goal Selector "!".
Set Default Proof Using "Type*".

(** The copies of [meta_conv], [meta_conv_term] and [meta_conv_all] ([PCUICTyping]):
    rewriting a [typingE] judgement along equalities of its components. *)
Lemma meta_convE {cf : checker_flags} {Σ Γ t A B} :
    Σ ;;; Γ |-E t : A ->
    A = B ->
    Σ ;;; Γ |-E t : B.
Proof. now intros h []. Qed.

Lemma meta_conv_termE {cf : checker_flags} {Σ Γ t t' A} :
    Σ ;;; Γ |-E t : A ->
    t = t' ->
    Σ ;;; Γ |-E t' : A.
Proof. now intros h []. Qed.

Lemma meta_conv_allE {cf : checker_flags} {Σ Γ t A Γ' t' A'} :
    Σ ;;; Γ |-E t : A ->
    Γ = Γ' -> t = t' -> A = A' ->
    Σ ;;; Γ' |-E t' : A'.
Proof. now intros h [] [] []. Qed.

Section RenamingE.

Context `{cf : checker_flags}.

(** Base [renaming] with [wf_localE] for [wf_local]. *)
Definition renamingE P Σ Γ Δ f :=
  wf_localE Σ Δ × urenaming P Γ Δ f.

Lemma renamingE_extP P P' Σ Γ Δ f :
  P =1 P' ->
  renamingE P Σ Γ Δ f -> renamingE P' Σ Γ Δ f.
Proof using Type.
  intros hP; rewrite /renamingE.
  intros []; split; eauto.
  eapply urenaming_ext; eauto. reflexivity.
Qed.

Lemma renaming_vassE :
  forall P Σ Γ Δ na A f,
    wf_localE Σ (Δ ,, vass na (rename f A)) ->
    renamingE P Σ Γ Δ f ->
    renamingE (shiftnP 1 P) Σ (Γ ,, vass na A) (Δ ,, vass na (rename f A)) (shiftn 1 f).
Proof.
  intros P Σ Γ Δ na A f hΓ [? h].
  split. 1: auto.
  eapply urenaming_vass; assumption.
Qed.

Lemma renaming_vdefE :
  forall P Σ Γ Δ na b B f,
    wf_localE Σ (Δ ,, vdef na (rename f b) (rename f B)) ->
    renamingE P Σ Γ Δ f ->
    renamingE (shiftnP 1 P) Σ (Γ ,, vdef na b B) (Δ ,, vdef na (rename f b) (rename f B)) (shiftn 1 f).
Proof.
  intros P Σ Γ Δ na b B f hΓ [? h].
  split. 1: auto.
  eapply urenaming_vdef; assumption.
Qed.

Lemma rename_ind_predicate_contextE {Σ : global_env_ext} {wfΣ : wfE Σ} {f ind mdecl idecl} :
  declared_inductive Σ ind mdecl idecl ->
  rename_context (shiftn (context_assumptions (ind_params mdecl)) f) (ind_predicate_context ind mdecl idecl) =
  ind_predicate_context ind mdecl idecl.
Proof.
  intros isdecl.
  generalize (declared_inductive_closed_pars_indicesE isdecl).
  rewrite closedn_ctx_app => /andP [] clpars /= clinds.
  rewrite /ind_predicate_context.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  rewrite !rename_context_snoc /= /map_decl /= /snoc. f_equal.
  - f_equal. len.
    rewrite rename_mkApps /=. f_equal.
    rewrite shiftn_add.
    relativize (#|_| + _).
    1:now erewrite -> rename_to_extended_list.
    now len.
  - rewrite rename_context_subst.
    rewrite rename_closed_extended_subst //. f_equal.
    rewrite shiftn_add Nat.add_comm. len.
    rewrite rename_context_lift. f_equal.
    rewrite rename_closedn_ctx //.
Qed.

Lemma rename_case_predicate_contextE {Σ : global_env_ext} {wfΣ : wfE Σ} {ind mdecl idecl f p} :
  declared_inductive Σ ind mdecl idecl ->
  wf_predicate mdecl idecl p ->
  rename_context f (case_predicate_context ind mdecl idecl p) =
  case_predicate_context ind mdecl idecl (rename_predicate f p).
Proof.
  intros decli wfp.
  unfold case_predicate_context. simpl.
  unfold id. unfold case_predicate_context_gen.
  rewrite rename_context_set_binder_name.
  - len.
    now rewrite -(wf_predicate_length_pcontext wfp).
  - f_equal. rewrite /pre_case_predicate_context_gen.
    rewrite rename_inst_case_context.
    rewrite (wf_predicate_length_pars wfp) (declared_minductive_ind_nparsE decli).
    now rewrite (rename_ind_predicate_contextE decli).
Qed.

Lemma rename_case_branch_typeE {Σ : global_env_ext} {wfΣ : wfE Σ} f (ci : case_info) mdecl idecl p br i cdecl :
  declared_inductive Σ ci mdecl idecl ->
  wf_predicate mdecl idecl p ->
  wf_branch cdecl br ->
  let ptm := it_mkLambda_or_LetIn (case_predicate_context ci mdecl idecl p) (preturn p) in
  let p' := rename_predicate f p in
  let ptm' := it_mkLambda_or_LetIn (case_predicate_context ci mdecl idecl p') (preturn p') in
  case_branch_type ci mdecl idecl
     (rename_predicate f p)
     (map_branch_shift rename shiftn f br)
     ptm' i (rename_constructor_body mdecl f cdecl) =
  map_pair (rename_context f) (rename (shiftn #|bcontext br| f))
  (case_branch_type ci mdecl idecl p br ptm i cdecl).
Proof.
  intros decli wfp wfb ptm p' ptm'.
  rewrite /case_branch_type /case_branch_type_gen /map_pair /=.
  rewrite rename_case_branch_context_gen //.
  { eapply (declared_inductive_closed_paramsE decli). }
  { len; now apply wf_branch_length. }
  { rewrite -(declared_minductive_ind_nparsE decli).
    apply (wf_predicate_length_pars wfp). }
  f_equal.
  rewrite rename_mkApps map_app map_map_compose.
  rewrite (wf_branch_length wfb).
  f_equal.
  * rewrite /ptm' /ptm !lift_it_mkLambda_or_LetIn !rename_it_mkLambda_or_LetIn.
    rewrite !lift_rename. f_equal.
    ++ rewrite /p'. len.
      epose proof (rename_context_lift f #|cstr_args cdecl| 0).
        rewrite Nat.add_0_r in H.
        rewrite H. len.
        rewrite shiftn0 //. f_equal.
        rewrite rename_case_predicate_contextE //.
    ++ rewrite /p'. rewrite Nat.add_0_r. simpl. len.
      rewrite map2_length //. 1:{ len. now rewrite (wf_predicate_length_pcontext wfp). }
      rewrite - !lift_rename; len. rewrite case_predicate_context_length // shiftn_add.
      now rewrite -rename_shiftnk Nat.add_comm.
  * rewrite /= rename_mkApps /=. f_equal.
    ++ rewrite !map_map_compose /id. apply map_ext => t.
      rewrite /expand_lets /expand_lets_k.
      rewrite -rename_subst_instance. len.
      rewrite -shiftn_add -shiftn_add.
      rewrite rename_subst map_rev. f_equal.
      rewrite List.length_rev rename_subst.
      rewrite (wf_predicate_length_pars wfp).
      rewrite (declared_minductive_ind_nparsE decli).
      rewrite -{2}(context_assumptions_subst_instance (puinst p) (ind_params mdecl)).
      rewrite rename_closed_extended_subst.
      { rewrite closedn_subst_instance_context.
        apply (declared_inductive_closed_paramsE decli). }
      f_equal. len. rewrite !shiftn_add.
      rewrite (Nat.add_comm _ (context_assumptions _)) rename_shiftnk.
      f_equal. rewrite Nat.add_comm rename_subst.
      rewrite rename_inds. f_equal.
      rewrite shiftn_add. now len.
    ++ unfold id. f_equal. f_equal.
       rewrite map_app map_map_compose.
       rewrite map_map_compose.
       setoid_rewrite rename_shiftn. len. f_equal.
       rewrite rename_to_extended_list.
       now rewrite /to_extended_list /to_extended_list_k reln_fold.
Qed.

Lemma wf_local_app_renamingE P Σ Γ Δ :
  All_local_rel (fun (Γ : context) j =>
    forall P Δ (f : nat -> nat),
    renamingE (shiftnP #|Γ| P) Σ Γ Δ f ->
    lift_typing0 (fun t T => Σ ;;; Δ |-E rename f t : rename f T) j)
    Γ Δ ->
  forall Δ' f,
  renamingE (shiftnP #|Γ| P) Σ Γ Δ' f ->
  wf_localE Σ (Δ' ,,, rename_context f Δ).
Proof.
  intros. destruct X0.
  induction X using All_local_rel_ind1.
  1: now apply a.
  rewrite rename_context_snoc /=. apply All_local_env_snoc; auto.
  eapply lift_typing_map with (j := j_decl _) => //.
  eapply X.
  split; auto.
  eapply urenaming_ext.
  { now rewrite length_app -shiftnP_add. }
  { reflexivity. } now eapply urenaming_context.
Qed.

(** Renaming carries the witness of every body; [check] is one of
    [check_one_fix] and [check_one_cofix] ([rename_check_one_fix],
    [rename_check_one_cofix]). *)
Lemma rename_mfix_on_indE {Σ : global_env_ext} {cb : ClosedBodies Σ.1} P Γ Δ f check ok mfix :
  (forall d m, check d = Some m ->
    check (map_def (rename f) (rename (shiftn #|mfix| f)) d) = Some m) ->
  urenaming (shiftnP #|Γ| P) Γ Δ f ->
  is_closed_context Γ -> is_closed_context Δ ->
  All (fun d => is_open_term Γ (dtype d)) mfix ->
  mfix_on_ind check (conv_witnessE Σ Γ) ok mfix ->
  mfix_on_ind check (conv_witnessE Σ Δ) ok
    (map (map_def (rename f) (rename (shiftn #|mfix| f))) mfix).
Proof.
  intros hc hf hΓ hΔ hop.
  eapply mfix_on_ind_map; [exact hop| |easy].
  intros d m hopd [ty [hcd [hty hconv]]].
  exists (rename f ty); split; [|split].
  - rewrite map_def_with_type. now apply hc.
  - eapply urename_is_open_term; tea.
  - eapply convSpecE_renameP; tea.
Qed.

(** For an unconditional renaming defined on all variables in the source context *)
Lemma typing_rename_propE :
  let Pj := (fun Σ Γ j =>
    forall P Δ f,
    renamingE (shiftnP #|Γ| P) Σ Γ Δ f ->
    lift_typing (fun Σ Γ t T => Σ ;;; Δ |-E rename f t : rename f T) Σ Γ j)
  in
  env_propE
  (fun Σ Γ t A =>
    forall P Δ f,
    renamingE (shiftnP #|Γ| P) Σ Γ Δ f ->
    Σ ;;; Δ |-E rename f t : rename f A)
  Pj
  (fun Σ Γ => All_local_env (Pj Σ) Γ).
Proof.
  apply typingE_ind_env.

  - intros Σ wfΣ Γ j H P Δ f Hr.
    apply lift_typing_impl with (1 := H) => t T [_ IH].
    now eapply IH.

  - intros Σ wfΣ Γ _ _ HΓ. assumption.

  - intros Σ wfΣ Γ wfΓ n decl isdecl ihΓ P Δ f hf.
    simpl in *.
    eapply hf in isdecl as h => //.
    2:{ rewrite /shiftnP. eapply nth_error_Some_length in isdecl. now nat_compare_specs. }
    destruct h as [decl' [isdecl' [? [h1 h2]]]].
    rewrite lift0_rename rename_compose h1 -lift0_rename.
    econstructor. all: auto. apply hf.

  - intros Σ wfΣ Γ wfΓ l X H0 P Δ f [hΔ hf].
    simpl. constructor. all: auto.

  - intros Σ wfΣ Γ wfΓ na A B s1 s2 X hA ihA hB ihB P Δ f hf.
    assert (lift_typing0 (typingE Σ Δ) (j_vass_s na (rename f A) s1)).
    + eapply ihA; eauto.
    + rewrite /=. econstructor; tas.
      eapply ihB; eauto.
      simpl.
      eapply renamingE_extP. { now rewrite -(shiftnP_add 1). }
      eapply renaming_vassE. 2: eauto.
      constructor.
      * destruct hf as [hΔ hf]. assumption.
      * eapply lift_sorting_forget_univ, X0.
  - intros Σ wfΣ Γ wfΓ na A t B X hA ihA ht iht P Δ f hf.
    assert (lift_typing0 (typingE Σ Δ) (j_vass na (rename f A))).
    + eapply ihA; eauto.
    + simpl. econstructor; tas.
      eapply iht; eauto; simpl.
      eapply renamingE_extP. { now rewrite -(shiftnP_add 1). }
      eapply renaming_vassE. 2: eauto.
      constructor; tas.
      destruct hf as [hΔ hf]. assumption.
  - intros Σ wfΣ Γ wfΓ na b B t A X hbB ihbB ht iht P Δ f hf.
    assert (lift_typing0 (typingE Σ Δ) (j_vdef na (rename f b) (rename f B))).
    + eapply ihbB; tea.
    + simpl. econstructor; tas.
      eapply iht; tea.
      eapply renamingE_extP. { now rewrite -(shiftnP_add 1). }
      eapply renaming_vdefE. 2: eauto.
      constructor; tas.
      destruct hf as [hΔ hf]. assumption.
  - intros Σ wfΣ Γ wfΓ t na A B s u X hty ihty ht iht hu ihu P Δ f hf.
    simpl. eapply meta_convE.
    + eapply typeE_App.
      * simpl in ihty. eapply ihty; tea.
      * simpl in iht. eapply iht. eassumption.
      * eapply ihu. eassumption.
    + autorewrite with sigma. rewrite !subst1_inst. sigma.
      eapply inst_ext => i.
      unfold subst_cons, ren, shiftn, subst_compose. simpl.
      destruct i.
      * simpl. reflexivity.
      * simpl. f_equal. f_equal. lia.
  - intros Σ wfΣ Γ wfΓ cst u decl X X0 isdecl hconst P Δ f hf.
    simpl. eapply meta_convE.
    + constructor. all: eauto. apply hf.
    + rewrite rename_subst_instance. f_equal.
      rewrite rename_closed. 2: auto.
      eapply declared_constant_closed_typeE. all: eauto.
  - intros Σ wfΣ Γ wfΓ ind u mdecl idecl isdecl X X0 hconst P Δ σ hf.
    simpl. eapply meta_convE.
    + econstructor. all: eauto. apply hf.
    + rewrite rename_subst_instance. f_equal.
      rewrite rename_closed. 2: auto.
      eapply declared_inductive_closed_typeE. all: eauto.
  - intros Σ wfΣ Γ wfΓ ind i u mdecl idecl cdecl isdecl X X0 hconst P Δ f hf.
    simpl. eapply meta_convE.
    + econstructor. all: eauto. apply hf.
    + rewrite rename_closed. 2: reflexivity.
      eapply declared_constructor_closed_typeE. all: eauto.
  - intros Σ wfΣ Γ wfΓ ci p c brs indices ps mdecl idecl isdecl HΣ.
    intros IHΔ ci_npar eqpctx predctx wfp cup wfpctx Hpret IHpret IHpredctx isallowed Her.
    intros IHctxi Hc IHc iscof ptm wfbrs Hbrs P Δ f Hf.
    simpl.
    assert (iscof' : (isCoFinite (ind_finite mdecl) ==>
      (ci.(ci_cofix_nondep) ==>
       on_free_vars (strengthenP 0 1 xpredT) (preturn (rename_predicate f p)))) = true).
    { apply/implyP => hcof. apply/implyP => hnd.
      move/implyP: iscof => /(_ hcof) /implyP /(_ hnd) h.
      rewrite -rename_predicate_preturn. apply on_free_vars_nondep_rename => //.
      rewrite (wf_predicate_length_pcontext wfp). lia. }
    rewrite rename_mkApps.
    rewrite map_app. simpl.
    rewrite /ptm. rewrite rename_it_mkLambda_or_LetIn.
    relativize #|predctx|.
    * erewrite rename_predicate_preturn.
      rewrite rename_case_predicate_contextE //.
      eapply typeE_Case; eauto; tea; rewrite - ?rename_case_predicate_contextE.
      7,10: constructor; eauto; tea; rewrite - ?rename_case_predicate_contextE.
      all:tea.
      + simpl. eapply IHpret.
        split.
        ++ apply All_local_env_app_inv in IHpredctx as [].
          eapply wf_local_app_renamingE; eauto.
        ++ rewrite /predctx length_app.
           eapply urenaming_ext.
           { now rewrite -shiftnP_add. }
           { reflexivity. }
          relativize #|pcontext p|; [eapply urenaming_context|].
          { apply Hf. }
          now rewrite case_predicate_context_length.
      + simpl. unfold id.
        specialize (IHc _ _ _ Hf).
        now rewrite rename_mkApps map_app in IHc.
      + now eapply rename_wf_predicate.
      + simpl. eauto.
        apply All_local_env_app_inv in IHpredctx as [].
        eapply wf_local_app_renamingE; eauto.
      + revert IHctxi.
        rewrite /= /id -map_app.
        rewrite -{2}[subst_instance _ _](rename_closedn_ctx f 0).
        { pose proof (declared_inductive_closed_pars_indicesE isdecl).
          now rewrite closedn_subst_instance_context. }
        rewrite rename_context_telescope.
        rewrite rename_telescope_shiftn0.
        clear -P Δ f Hf.
        induction 1.
        { constructor; auto. }
        { destruct t0; simpl. rewrite rename_telescope_cons.
          constructor; cbn; eauto.
          now rewrite rename_subst_telescope /= in IHIHctxi. }
        { simpl. rewrite rename_telescope_cons.
          constructor; cbn; eauto.
          now rewrite rename_subst_telescope /= in IHIHctxi. }
      + now eapply rename_wf_branches.
      + eapply Forall2_All2 in wfbrs.
        eapply All2i_All2_mix_left in Hbrs; eauto.
        eapply All2i_nth_hyp in Hbrs.
        eapply All2i_map_right, (All2i_impl Hbrs) => i cdecl br.
        set (brctxty := case_branch_type _ _ _ _ _ _ _ _).
        intros (Hnth & wfbr & eqbctx & IHbctx & (Hbod & IHbod) & Hbty & IHbty).
        rewrite -(rename_closed_constructor_body mdecl cdecl f).
        { eapply (declared_constructor_closedE (c:=(ci.(ci_ind),i))); eauto.
          split; eauto. }
        split; auto.
        { simpl. rewrite -rename_cstr_branch_context //.
          1:eapply (declared_inductive_closed_paramsE isdecl).
          rewrite rename_closedn_ctx //.
          eapply closed_cstr_branch_contextE. split; tea. }
        cbn -[case_branch_type].
        rewrite case_branch_type_fst.
        rewrite -rename_case_branch_context_gen //.
        2-3:len.
        1:exact (declared_inductive_closed_paramsE isdecl).
        1:rewrite (wf_branch_length wfbr) //.
        1:rewrite (wf_predicate_length_pars wfp).
        1:now rewrite (declared_minductive_ind_nparsE isdecl).
        set (brctx' := rename_context f _).
        assert (wf_localE Σ (Δ ,,, brctx')).
        { apply All_local_env_app_inv in IHbctx as [].
          eapply wf_local_app_renamingE; tea. }
        split => //.
        rewrite rename_case_predicate_contextE // rename_case_branch_typeE //.
        split.
        { eapply IHbod => //.
          split => //.
          * eapply urenaming_ext.
          { now rewrite app_context_length -shiftnP_add. }
          { reflexivity. }
          relativize #|bcontext br|; [eapply urenaming_context|].
          1:apply Hf. rewrite case_branch_context_length //. }
        { eapply IHbty. split=> //.
          rewrite /brctx' case_branch_type_fst.
          rewrite (wf_branch_length wfbr).
          eapply urenaming_ext.
          { now rewrite app_context_length -shiftnP_add. }
          { reflexivity. }
          rewrite -(wf_branch_length wfbr).
          rewrite -/(rename_context f _).
          relativize #|bcontext br|; [eapply urenaming_context, Hf|len].
          now rewrite case_branch_context_length. }
    * rewrite /predctx case_predicate_context_length //.
  - intros Σ wfΣ Γ wfΓ p c u mdecl idecl cdecl pdecl isdecl args X X0 hc ihc e
           P Δ f hf.
    simpl. eapply meta_convE.
    + econstructor.
      * eassumption.
      * eapply meta_convE.
        -- eapply ihc; tea.
        -- rewrite rename_mkApps. simpl. reflexivity.
      * rewrite length_map. assumption.
    + rewrite rename_subst0. simpl. rewrite map_rev. f_equal.
      rewrite rename_subst_instance. f_equal.
      rewrite rename_closedn. 2: reflexivity.
      eapply declared_projection_closed_typeE in isdecl.
      rewrite List.length_rev. rewrite e. assumption.

  - intros Σ wfΣ Γ wfΓ mfix n decl types H1 hdecl X hmfixt ihmfixt hmfixb ihmfixb wffix P Δ f hf.
    apply All_local_env_app_inv in X as [_ X].
    eapply wf_local_app_renamingE in X; tea.
    simpl. eapply meta_convE.
    + eapply typeE_Fix.
      * apply hf.
      * destruct hf; eapply fix_guard_rename; eauto.
      * rewrite nth_error_map. rewrite hdecl. simpl. reflexivity.
      * apply All_map, (All_impl ihmfixt).
        intros x t. eapply t. eauto.
      * apply All_map, (All_impl ihmfixb).
        unfold on_def_body. rewrite fix_context_length length_map {2}/map_def /=.
        intros x t.
        relativize (lift0 _ _).
        1: eapply t; eauto.
        2: cbn [j_typ]; try rewrite /types; len; apply rename_shiftn.
        rewrite rename_fix_context.
        split; auto.
        subst types. rewrite -(fix_context_length mfix).
        eapply urenaming_ext.
        { now rewrite app_context_length -shiftnP_add. }
        { reflexivity. }
        apply urenaming_context; auto. apply hf.
      * destruct wffix as (isl & hra & hon). split; [|split].
        1: rewrite forallb_map; refine (forallb_impl _ _ _ _ isl); intros x _ h.
        1: now eapply isLambda_rename.
        1: rewrite forallb_map; refine (forallb_impl _ _ _ _ hra); intros x _ h.
        1: now eapply rename_has_rec_arg.
        eapply (rename_mfix_on_indE (cb := @wfE_ClosedBodies _ Σ.1 wfΣ)); tea.
        1: exact (rename_check_one_fix f mfix).
        1: apply hf.
        1: now eapply wf_local_closed_contextE.
        1: destruct hf as [hΔ _]; now eapply wf_local_closed_contextE.
        eapply (All_impl hmfixt) => d hd.
        now eapply isTypeRel_is_open_termE, hd.
    + reflexivity.

  - intros Σ wfΣ Γ wfΓ mfix n decl types guard hdecl X hmfixt ihmfixt hmfixb ihmfixb wfcofix P Δ f hf.
    apply All_local_env_app_inv in X as [_ X].
    eapply wf_local_app_renamingE in X; eauto.
    simpl. eapply meta_convE.
    + eapply typeE_CoFix; auto.
      * apply hf.
      * destruct hf; eapply cofix_guard_rename; eauto.
      * rewrite nth_error_map. rewrite hdecl. simpl. reflexivity.
      * apply All_map, (All_impl ihmfixt).
        intros x t. eapply t. eauto.
      * apply All_map, (All_impl ihmfixb).
        unfold on_def_body. rewrite fix_context_length length_map {2}/map_def /=.
        intros x t.
        relativize (lift0 _ _).
        1: eapply t; eauto.
        2: cbn [j_typ]; try rewrite /types; len; apply rename_shiftn.
        rewrite rename_fix_context.
        split; auto.
        subst types. rewrite -(fix_context_length mfix).
        eapply urenaming_ext.
        { now rewrite app_context_length -shiftnP_add. }
        { reflexivity. }
        apply urenaming_context; auto. apply hf.
      * eapply (rename_mfix_on_indE (cb := @wfE_ClosedBodies _ Σ.1 wfΣ)); tea.
        1: exact (rename_check_one_cofix f mfix).
        1: apply hf.
        1: now eapply wf_local_closed_contextE.
        1: destruct hf as [hΔ _]; now eapply wf_local_closed_contextE.
        eapply (All_impl hmfixt) => d hd.
        now eapply isTypeRel_is_open_termE, hd.
    + reflexivity.

  - intros Σ wfΣ Γ wfΓ p pty cdecl _ hp hdecl pinv ptyp IH P Δ f hf.
    cbn. rewrite rename_prim_type /=. econstructor; tea.
    * apply hf.
    * rewrite prim_val_tag_map //.
    * rewrite prim_val_tag_map //.
    * depelim IH; eauto; cbn; constructor; cbn; eauto. solve_all.

  - intros Σ wfΣ Γ wfΓ t A B X hwf ht iht htB ihB cum P Δ f hf.
    pose proof (@wfE_ClosedBodies _ Σ.1 wfΣ) as cb.
    eapply typeE_Cumul.
    + eapply iht; tea.
    + eapply ihB; tea.
    + eapply cumulSpecE_renameP.  all: try eassumption.
      * apply hf.
      * apply wf_local_closed_contextE; eauto.
      * pose proof (type_closedE ht).
        now eapply closedn_on_free_vars in H.
      * pose proof (subject_closedE htB).
        now eapply closedn_on_free_vars in H.
      * pose proof (closed_ctx_on_free_vars P _ (closed_wf_localE _ (typingE_wf_local ht))).
        destruct hf as [HΔ _]. apply wf_local_closed_contextE; eauto.
Qed.

Lemma typing_rename_PE {P Σ Γ Δ f t A} {wfΣ : wfE Σ.1} :
  renamingE (shiftnP #|Γ| P) Σ Γ Δ f ->
  Σ ;;; Γ |-E t : A ->
  Σ ;;; Δ |-E rename f t : rename f A.
Proof.
  intros hf h.
  revert Σ wfΣ Γ t A h P Δ f hf.
  apply typing_rename_propE.
Qed.

Lemma typing_renameE {Σ Γ Δ f t A} :
  wfE Σ.1 -> wf_localE Σ Δ ->
  renaming_closed Γ Δ f ->
  Σ ;;; Γ |-E t : A ->
  Σ ;;; Δ |-E rename f t : rename f A.
Proof.
  intros ? ? hf h. eapply (typing_rename_PE (P:=fun _ => false)) ; eauto; split; eauto.
Qed.

End RenamingE.
