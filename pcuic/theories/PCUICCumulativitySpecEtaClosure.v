(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICCumulativity
  PCUICTyping PCUICReduction PCUICGlobalEnv PCUICClosed PCUICEquality PCUICRenameDef
  PCUICSigmaCalculus PCUICClosed PCUICOnFreeVars PCUICOnFreeVarsConv PCUICGuardCondition
  PCUICWeakeningEnvConv PCUICWeakeningEnvTyp PCUICClosedConv PCUICClosedTyp PCUICRenameConv
  PCUICWeakeningConv PCUICCumulativitySpec PCUICCumulativitySpecEta.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
Set Equations With UIP.

(** * Closure of [cumulSpecE0] under renaming, and the lift/weakening fragment (plan S3).

  [cumulSpecE_renameP] is the E analogue of [cumulSpec_renameP]
  (`Typing/PCUICRenameTyp.v:155-163`): a direct induction on the specification, with
  one extra case for [cumul_eta_l]. The lift/weakening lemma is then that lemma
  composed with [lift0_rename] (`PCUICSigmaCalculus.v:346`) over the base [urenaming]
  instance [weakening_renaming] (`Conversion/PCUICWeakeningConv.v:71-73`); it does not
  go through the algorithmic relation, so it needs neither the bridge nor confluence. *)

Open Scope sigma_scope.
Set Keyed Unification.

Set Default Goal Selector "!".
Set Default Proof Using "Type*".

Section RenamingEta.

Context `{cf : checker_flags}.

Lemma cumulSpecE_renameP pb P Σ Γ Δ f A B : let sP := shiftnP #|Γ| P in
    wf Σ.1 ->
    urenaming sP Γ Δ f ->
    is_closed_context Γ ->
    is_open_term Γ A ->
    is_open_term Γ B ->
    is_closed_context Δ ->
    Σ ;;; Γ ⊢ A ≤sE[pb] B ->
    Σ ;;; Δ ⊢ rename f A ≤sE[pb] rename f B.
Proof.
  intros sP wfΣ Hren HfreeA HfreeB HΓ HΔ e.
  revert pb Γ A B e sP Δ f wfΣ Hren HfreeA HfreeB HΓ HΔ.
  induction 1; intros; cbn.
  all: lazymatch goal with
       | [ H : cumul_predicate_dep _ _ _ |- _ ] => apply cumul_predicate_undep in H
       | _ => idtac
       end.
  all: repeat match goal with
         | [ H : All2_dep _ _ |- _ ] => apply All2_undep in H
         end.
  - rewrite rename_subst10. solve [econstructor].
  - rewrite rename_subst10. solve [econstructor].
  - rename Hren into hf. unfold urenaming in hf.
    destruct (nth_error Γ i) eqn:hnth; noconf pf.
    assert (hav : sP i).
    { unfold sP, shiftnP in *. cbn in *. rewrite orb_false_r in HfreeB. intuition auto with *. }
    clear HfreeB.
    specialize hf with (1 := hav) (2 := hnth).
    destruct hf as [decl' [e' [eqann [hr hbo]]]].
    rewrite H /= in hbo.
    rewrite lift0_rename.
    destruct (decl_body decl') eqn:hdecl => //. noconf hbo.
    let H0 := match goal with H : rename _ _ = rename _ _ |- _ => H end in
    sigma in H0; sigma; rewrite H0.
    relativize (t.[_]).
    2:{ setoid_rewrite rshiftk_S. rewrite -rename_inst.
        now rewrite -(lift0_rename (S (f i)) _). }
     eapply cumulE_rel. now rewrite e' /= hdecl.
   - rewrite rename_mkApps. simpl.
     rewrite rename_iota_red //.
    * rewrite length_skipn; lia.
    * change (bcontext br) with (bcontext (rename_branch f br)).
     move/and5P: HfreeB => [_ _ _ _ hbrs].
     eapply nth_error_forallb in hbrs; tea. simpl in hbrs.
     move/andP: hbrs => [] clbctx clbod.
     rewrite closedn_ctx_on_free_vars.
     now rewrite test_context_k_closed_on_free_vars_ctx in clbctx.
   * eapply cumulE_iota.
     + rewrite nth_error_map Hbrs /= //.
     + simpl. now len.
   - rewrite 2!rename_mkApps. simpl.
     eapply cumulE_fix.
     + eapply rename_unfold_fix. eassumption.
     + rewrite -is_constructor_rename. assumption.
   - rewrite 2!rename_mkApps. simpl.
     eapply cumulE_cofix_case.
     eapply rename_unfold_cofix. eassumption.
   - rewrite 2!rename_mkApps. simpl.
     eapply cumulE_cofix_proj.
     eapply rename_unfold_cofix. eassumption.
   - rewrite rename_subst_instance.
     eapply cumulE_delta.
     + eassumption.
     + rewrite rename_closed. 2: assumption.
       eapply declared_constant_closed_body. all: eauto.
   - rewrite rename_mkApps. simpl.
     eapply cumulE_proj. rewrite nth_error_map. rewrite Hargs. reflexivity.
   - eapply cumulE_Trans; try apply X0; try apply X2; eauto. eapply urename_is_open_term; eauto.
   - eapply cumulE_Sym; intuition; eauto.
   - eapply cumulE_Refl; intuition; eauto.
   - eapply cumulE_Evar. cbn in *.
     apply forallb_All in HfreeB, HΓ.
     repeat toAll. eapply All2_impl. 1:tea. cbn; intros.
     eapply X0.1.2; intuition.
   - cbn in *. rtoProp.
     eapply cumulE_App; try apply X0; try apply X2; eauto.
   - cbn in HfreeB, HΓ; rtoProp.
     eapply cumulE_Lambda; try apply IHe1; try apply IHe2; eauto;
     try rewrite shiftnP_S; eauto.
     * eapply urenaming_impl. 1: intro; rewrite shiftnP_S; eauto. apply urenaming_vass; eauto.
     * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
     * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
       cbn. eapply urename_is_open_term; eauto.
   - cbn in HfreeB, HΓ. rtoProp.
     eapply cumulE_Prod; try apply IHe1; try apply IHe2; eauto;
     try rewrite shiftnP_S; eauto.
     * eapply urenaming_impl. 1: intro; rewrite shiftnP_S; eauto. apply urenaming_vass; eauto.
     * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
     * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
       cbn. eapply urename_is_open_term; eauto.
   - cbn in HfreeB, HΓ; rtoProp.
     eapply cumulE_LetIn; try apply IHe1; try apply IHe2; eauto; try apply IHe3;
     try rewrite shiftnP_S; eauto.
     * eapply urenaming_impl. 1: intro; rewrite shiftnP_S; eauto. apply urenaming_vdef; eauto.
     * rewrite on_free_vars_ctx_snoc_def; eauto.
     * rewrite on_free_vars_ctx_snoc_def; eauto.
       all: eapply urename_is_open_term; eauto.
   - cbn in HfreeB, HΓ.
     rename Hp into Hpold, HΓ into H'; rename HfreeB into H.
     apply andb_andI in H; apply andb_andI in H'; destruct H as [Hp H]; destruct H' as [Hp' H'].
     apply andb_andI in H; apply andb_andI in H'; destruct H as [Hreturn H]; destruct H' as [Hreturn' H'].
     apply andb_andI in H; apply andb_andI in H'; destruct H as [Hcontext H]; destruct H' as [Hcontext' H'].
     apply andb_andI in H; apply andb_andI in H'; destruct H as [Hc Hbrs]; destruct H' as [Hc' Hbrs'].
     eapply cumulE_Case.
     * unfold cumul_predicate in *; destruct_head'_prod.
       repeat split; eauto.
       + eapply All2_map. apply forallb_All in Hp, Hp'. repeat toAll.
         eapply All2_impl. 1: tea. cbn; intros. destruct X as [[X [X''' X']] X'']. apply X'; eauto.
       + unfold preturn. cbn. unshelve erewrite (All2_length _ : #|pcontext _| = #|pcontext _|); shelve_unifiable; tea.
         exactly_once (idtac; multimatch goal with H : _ |- _ => eapply H end); eauto.
         ++ rewrite app_context_length.
            eapply urenaming_ext; try apply shiftnP_add; try reflexivity.
            unshelve erewrite <- (All2_length _ : #|pcontext _| = #|pcontext _|); shelve_unifiable; tea.
            rewrite <- inst_case_predicate_context_length.
            rewrite test_context_k_closed_on_free_vars_ctx in Hcontext.
            rewrite inst_case_predicate_context_rename; eauto.
            apply urenaming_context; eauto.
         ++ rewrite test_context_k_closed_on_free_vars_ctx in Hcontext.
            unfold inst_case_predicate_context.
            apply on_free_vars_ctx_inst_case_context; eauto.
         ++ unfold inst_case_predicate_context.
            unfold is_open_term. rewrite length_app.
            rewrite <- shiftnP_add.
            rewrite inst_case_predicate_context_length.
            eassumption.
         ++ unfold inst_case_predicate_context.
            unfold is_open_term. rewrite length_app.
            rewrite <- shiftnP_add.
            rewrite inst_case_predicate_context_length.
            unshelve erewrite (All2_length _ : #|pcontext _| = #|pcontext _|); shelve_unifiable; tea.
         ++ rewrite test_context_k_closed_on_free_vars_ctx in Hcontext.
            unfold inst_case_predicate_context. apply on_free_vars_ctx_inst_case_context; eauto.
            +++ eapply All_forallb. apply All_map. apply forallb_All in Hp; eapply All_impl. 1: tea.
                cbn; intros. eapply urename_is_open_term; eauto.
            +++ unfold pparams. cbn. rewrite length_map. exact Hcontext.
     * eauto.
     * unfold cumul_branches, cumul_branch in *.
       let X2 := match goal with H : All2 _ brs brs' |- _ => H end in
       rename X2 into Hbrsbrs'.
       apply forallb_All in Hbrs, Hbrs'. apply (All2_All_mix_left Hbrs) in Hbrsbrs'. clear Hbrs.
       apply (All2_All_mix_right Hbrs') in Hbrsbrs'. clear Hbrs'.
       apply All2_map. repeat toAll. eapply All2_impl. 1: tea. cbn; intros; destruct_head'_prod.
       unshelve erewrite (All2_length _ : #|bcontext _| = #|bcontext _|); shelve_unifiable; tea.
       split; eauto.
       repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
       exactly_once (idtac; multimatch goal with H : _ |- _ => apply H end); eauto.
       + rewrite app_context_length.
       eapply urenaming_ext; try apply shiftnP_add; try reflexivity.
       unshelve erewrite <- (All2_length _ : #|bcontext _| = #|bcontext _|); shelve_unifiable; tea.
       rewrite <- (inst_case_branch_context_length p).
       rewrite -> test_context_k_closed_on_free_vars_ctx in *.
       rewrite inst_case_branch_context_rename; eauto.
       apply urenaming_context; eauto.
       + rewrite -> test_context_k_closed_on_free_vars_ctx in *.
         unfold inst_case_predicate_context.
         apply on_free_vars_ctx_inst_case_context; eauto.
         repeat toAll; eauto.
      + unfold inst_case_predicate_context.
         unfold is_open_term. rewrite length_app.
        rewrite <- shiftnP_add.
        rewrite inst_case_branch_context_length.
        eassumption.
      + unfold inst_case_predicate_context.
        unfold is_open_term. rewrite length_app.
        rewrite <- shiftnP_add.
        rewrite inst_case_branch_context_length.
       unshelve erewrite (All2_length _ : #|bcontext _| = #|bcontext _|); shelve_unifiable; tea.
      + rewrite test_context_k_closed_on_free_vars_ctx in Hcontext.
        unfold inst_case_predicate_context. apply on_free_vars_ctx_inst_case_context; eauto.
       ++ eapply All_forallb. apply All_map. repeat toAll. eapply All_impl. 1: tea.
           cbn; intros. eapply urename_is_open_term; eauto.
       ++ unfold pparams. rewrite -> test_context_k_closed_on_free_vars_ctx in *.
        cbn. rewrite length_map. eassumption.
  - cbn in *. eapply cumulE_Proj; try apply X0; eauto.
  - rewrite (All2_length X).
    eapply cumulE_Fix. cbn in *.
    apply forallb_All in HfreeB, HΓ.
    apply (All2_All_mix_left HfreeB) in X. clear HfreeB.
    apply (All2_All_mix_right HΓ) in X. clear HΓ.
    apply All2_map. repeat toAll. eapply All2_impl. 1: tea. cbn; intros.
    destruct_head'_prod.
    repeat split; eauto.
    * exactly_once (idtac; multimatch goal with H : _ |- _ => apply H end); eauto.
      all: cbv [test_def] in *; cbn in *.
      all: repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
      all: tea.
    * exactly_once (idtac; multimatch goal with H : _ |- _ => apply H end); eauto.
      all: unfold test_def in *.
      all: repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
      + rewrite app_context_length.
      eapply urenaming_ext; try apply shiftnP_add; try reflexivity.
      rewrite <- (All2_length X).
      rewrite rename_fix_context.
      rewrite <- fix_context_length.
      apply urenaming_context; eauto.
      + rewrite on_free_vars_ctx_app.
        apply andb_and; split; eauto.
        apply on_free_vars_fix_context.
        eapply All2_All_left. 1: tea. cbn; intros.
        destruct_head'_prod; eauto.
      + unfold is_open_term. rewrite length_app.
        rewrite <- shiftnP_add.
        rewrite fix_context_length. eauto.
      + unfold is_open_term. rewrite length_app.
        rewrite <- shiftnP_add.
        rewrite fix_context_length.
        rewrite (All2_length X). eauto.
      + rewrite on_free_vars_ctx_app.
        apply andb_and; split; eauto.
        apply on_free_vars_fix_context.
        repeat toAll.
        eapply All2_All_left. 1: tea. cbn ; intros.
        destruct_head'_prod.
        unfold test_def in *.
        repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
        apply andb_and. cbn. split.
        ++ eapply urename_is_open_term; eauto.
        ++ rewrite length_map. rewrite <-(All2_length X).
           rewrite <- fix_context_length.
           eapply urename_on_free_vars_shift; eauto.
           rewrite fix_context_length; eauto.
  - rewrite (All2_length X).
    eapply cumulE_CoFix. cbn in *.
    apply forallb_All in HfreeB, HΓ.
    apply (All2_All_mix_left HfreeB) in X. clear HfreeB.
    apply (All2_All_mix_right HΓ) in X. clear HΓ.
    apply All2_map. repeat toAll. eapply All2_impl. 1: tea. cbn; intros.
    destruct_head'_prod.
    repeat split; eauto.
    * exactly_once (idtac; multimatch goal with H : _ |- _ => apply H end); eauto.
      all: unfold test_def in *.
      all: repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
      all: tea.
    * exactly_once (idtac; multimatch goal with H : _ |- _ => apply H end); eauto.
      all: unfold test_def in *.
      all: repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
      + rewrite app_context_length.
      eapply urenaming_ext; try apply shiftnP_add; try reflexivity.
      rewrite <- (All2_length X).
      rewrite rename_fix_context.
      rewrite <- fix_context_length.
      apply urenaming_context; eauto.
      + rewrite on_free_vars_ctx_app.
        apply andb_and; split; eauto.
        apply on_free_vars_fix_context.
        eapply All2_All_left. 1: tea. cbn; intros.
        destruct_head'_prod; eauto.
      + unfold is_open_term. rewrite length_app.
        rewrite <- shiftnP_add.
        rewrite fix_context_length. eauto.
      + unfold is_open_term. rewrite length_app.
        rewrite <- shiftnP_add.
        rewrite fix_context_length.
        rewrite (All2_length X). eauto.
      + rewrite on_free_vars_ctx_app.
        apply andb_and; split; eauto.
        apply on_free_vars_fix_context.
        apply All_map. repeat toAll.
        eapply All2_All_left. 1: tea. cbn ; intros.
        unfold test_def in *.
        destruct_head'_prod.
        repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
        apply andb_and. cbn. split.
        ++ eapply urename_is_open_term; eauto.
        ++ rewrite length_map. rewrite <-(All2_length X).
           rewrite <- fix_context_length.
           eapply urename_on_free_vars_shift; eauto.
           rewrite fix_context_length; eauto.
  - eapply cumulE_Prim. depelim X; cbn; cbn in HfreeB, HΓ; rtoProp; constructor; cbn; eauto. solve_all.
  - repeat rewrite rename_mkApps. eapply cumulE_Ind.
    * repeat rewrite length_map; eauto.
    * inv_on_free_vars.
      eapply forallb_All in b, b0.
      apply (All2_All_mix_left b0) in X. clear b0.
      apply (All2_All_mix_right b) in X. clear b.
      apply All2_map. repeat toAll. eapply All2_impl. 1: tea. cbn; intros.
      destruct_head'_prod.
      eauto.
  - repeat rewrite rename_mkApps. eapply cumulE_Construct.
    * repeat rewrite length_map; eauto.
    * inv_on_free_vars. repeat toAll.
      eapply All2_impl. 1: tea. cbn; intros.
      destruct_head'_prod; eauto.
  - eapply cumulE_Sort; eauto.
  - eapply cumulE_Const; eauto.
  - (* function eta: the only case absent from the base lemma *)
    cbn in HfreeB. move/andP: HfreeB => [onA ont].
    apply cumul_eta_l.
    assert (Hr : rename (shiftn 1 f) (tApp (lift0 1 u) (tRel 0))
                 = tApp (lift0 1 (rename f u)) (tRel 0)).
    { cbn [rename]. rewrite rename_shiftn. reflexivity. }
    rewrite -Hr.
    eapply IHe.
    * assumption.
    * eapply urenaming_impl. 1: intro; rewrite shiftnP_S; eauto.
      apply urenaming_vass; eauto.
    * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
    * replace #|Γ ,, vass na A| with (S #|Γ|) by reflexivity.
      rewrite shiftnP_S. exact ont.
    * cbn [on_free_vars]. apply andb_and. split.
      + eapply on_free_vars_lift0. eapply on_free_vars_impl; [| exact HΓ].
        intros i. rewrite /addnP /shiftnP /=. now repeat nat_compare_specs.
      + rewrite /shiftnP /=. reflexivity.
    * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
      cbn. eapply urename_is_open_term; eauto.
Defined.

Lemma convSpecE_renameP P Σ Γ Δ f A B : let sP := shiftnP #|Γ| P in
    wf Σ.1 ->
    urenaming sP Γ Δ f ->
    is_closed_context Γ ->
    is_open_term Γ A ->
    is_open_term Γ B ->
    is_closed_context Δ ->
    Σ ;;; Γ ⊢ A ≤sE[Conv] B ->
    Σ ;;; Δ ⊢ rename f A ≤sE[Conv] rename f B.
Proof.
  apply cumulSpecE_renameP.
Qed.

(** The lift/weakening fragment of S3, by the renaming route: [weakening_renaming]
    instantiated at the empty inner context gives [urenaming] for [rshiftk n], and
    [lift0_rename] turns [lift0 n] into that renaming. No bridge to the algorithmic
    relation, hence no dependence on A4 or C4. *)

Lemma urenaming_lift0 P Γ Γ'' :
  urenaming P Γ (Γ ,,, Γ'') (rshiftk #|Γ''|).
Proof.
  exact (weakening_renaming P Γ [] Γ'').
Qed.

Lemma weakening_cumulSpecE0 pb Σ Γ Γ'' M N n :
  wf Σ.1 ->
  n = #|Γ''| ->
  is_closed_context Γ ->
  is_open_term Γ M ->
  is_open_term Γ N ->
  is_closed_context (Γ ,,, Γ'') ->
  Σ ;;; Γ ⊢ M ≤sE[pb] N ->
  Σ ;;; Γ ,,, Γ'' ⊢ lift0 n M ≤sE[pb] lift0 n N.
Proof.
  intros wfΣ -> clΓ onM onN clΓ'' H.
  rewrite (lift0_rename #|Γ''| M) (lift0_rename #|Γ''| N).
  eapply (cumulSpecE_renameP pb xpred0 Σ Γ (Γ ,,, Γ'') (rshiftk #|Γ''|)); eauto.
  apply urenaming_lift0.
Qed.

Lemma weakening_convSpecE0 Σ Γ Γ'' M N n :
  wf Σ.1 ->
  n = #|Γ''| ->
  is_closed_context Γ ->
  is_open_term Γ M ->
  is_open_term Γ N ->
  is_closed_context (Γ ,,, Γ'') ->
  Σ ;;; Γ ⊢ M ≤sE[Conv] N ->
  Σ ;;; Γ ,,, Γ'' ⊢ lift0 n M ≤sE[Conv] lift0 n N.
Proof.
  apply weakening_cumulSpecE0.
Qed.

(** The form S4's under-applied lemmas consume: the hypothesis of [cumulE_Ind] /
    [cumulE_Construct] transported, argumentwise, under [k] new binders. *)

Lemma weakening_cumulSpecE0_All2 Σ Γ Γ'' args args' n :
  wf Σ.1 ->
  n = #|Γ''| ->
  is_closed_context Γ ->
  forallb (is_open_term Γ) args ->
  forallb (is_open_term Γ) args' ->
  is_closed_context (Γ ,,, Γ'') ->
  All2 (fun a a' => Σ ;;; Γ ⊢ a ≤sE[Conv] a') args args' ->
  All2 (fun a a' => Σ ;;; Γ ,,, Γ'' ⊢ a ≤sE[Conv] a')
       (map (lift0 n) args) (map (lift0 n) args').
Proof.
  intros wfΣ hn clΓ onargs onargs' clΓ'' H.
  apply All2_map.
  apply forallb_All in onargs, onargs'.
  apply (All2_All_mix_left onargs) in H.
  apply (All2_All_mix_right onargs') in H.
  eapply All2_impl. 1: tea. cbn; intros x y [[onx Hxy] ony].
  now eapply weakening_cumulSpecE0.
Qed.

End RenamingEta.
