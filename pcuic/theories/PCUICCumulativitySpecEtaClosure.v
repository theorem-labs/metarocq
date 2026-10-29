(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICCumulativity
  PCUICTyping PCUICReduction PCUICGlobalEnv PCUICClosed PCUICEquality PCUICRenameDef
  PCUICSigmaCalculus PCUICClosed PCUICOnFreeVars PCUICOnFreeVarsConv PCUICGuardCondition
  PCUICWeakeningEnvConv PCUICWeakeningEnvTyp PCUICClosedConv PCUICClosedTyp PCUICRenameConv
  PCUICWeakeningConv PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICWeakeningEnv PCUICClosedBodies
  PCUICInstDef PCUICInstConv PCUICInstTyp PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp.

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
    ClosedBodies Σ.1 ->
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
       eapply closed_bodies. all: eauto.
   - (* cumulE_prim_op: renaming fixes the ground head arguments and reduct
        (trunk's cumul_prim_op case of PCUICRenameTyp) *)
     rewrite rename_mkApps; cbn [rename].
     rewrite (map_prim_ground (rename f) _ (prim_ground_rename f)).
     rewrite (prim_ground_rename f v (prim_ground_readback Hreadback)).
     eapply cumulE_prim_op; eassumption.
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
            unfold PCUICCases.inst_case_predicate_context.
            apply on_free_vars_ctx_inst_case_context; eauto.
         ++ unfold PCUICCases.inst_case_predicate_context.
            unfold is_open_term. rewrite length_app.
            rewrite <- shiftnP_add.
            rewrite inst_case_predicate_context_length.
            eassumption.
         ++ unfold PCUICCases.inst_case_predicate_context.
            unfold is_open_term. rewrite length_app.
            rewrite <- shiftnP_add.
            rewrite inst_case_predicate_context_length.
            unshelve erewrite (All2_length _ : #|pcontext _| = #|pcontext _|); shelve_unifiable; tea.
         ++ rewrite test_context_k_closed_on_free_vars_ctx in Hcontext.
            unfold PCUICCases.inst_case_predicate_context. apply on_free_vars_ctx_inst_case_context; eauto.
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
         unfold PCUICCases.inst_case_predicate_context.
         apply on_free_vars_ctx_inst_case_context; eauto.
         repeat toAll; eauto.
      + unfold PCUICCases.inst_case_predicate_context.
         unfold is_open_term. rewrite length_app.
        rewrite <- shiftnP_add.
        rewrite inst_case_branch_context_length.
        eassumption.
      + unfold PCUICCases.inst_case_predicate_context.
        unfold is_open_term. rewrite length_app.
        rewrite <- shiftnP_add.
        rewrite inst_case_branch_context_length.
       unshelve erewrite (All2_length _ : #|bcontext _| = #|bcontext _|); shelve_unifiable; tea.
      + rewrite test_context_k_closed_on_free_vars_ctx in Hcontext.
        unfold PCUICCases.inst_case_predicate_context. apply on_free_vars_ctx_inst_case_context; eauto.
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
  - (* function eta: the case that base's lemma does not have *)
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
    ClosedBodies Σ.1 ->
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
  ClosedBodies Σ.1 ->
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
  ClosedBodies Σ.1 ->
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
  ClosedBodies Σ.1 ->
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

(** * The under-applied inductive / constructor lemmas

    For heads applied below their cumulativity arity [n], the kernel η-expands both
    sides to full arity before comparing instances; in [cumulSpecE0] the same is
    done with [cumul_eta_l]/[cumulSpecE_eta_contract], the η-expansion domains
    being irrelevant. [cumulSpecE_ind_underapplied_gen] is the [Conv]-only
    induction on the number [k] of missing arguments;
    [cumulSpecE_ind_underapplied] wraps it with one [pb]-level η step. The lifted
    argument hypotheses are transported under the new binders by
    [weakening_cumulSpecE0_All2] (the lift/weakening fragment above).
    [ClosedBodies Σ.1] and the scoping premises are those of the closure lemmas
    above and of [cumul_Trans]. *)

(** Scoping helpers for the fresh eta binder. *)
Lemma is_open_term_snoc_lift (Γ : context) (d : context_decl) a :
  is_open_term Γ a -> is_open_term (Γ ,, d) (lift0 1 a).
Proof.
  intro Ha.
  replace #|Γ ,, d| with (S #|Γ|) by (cbn; lia).
  apply on_free_vars_lift0.
  eapply on_free_vars_impl; [|exact Ha].
  intros x. rewrite /addnP /shiftnP /=. now repeat nat_compare_specs.
Qed.

Lemma is_open_term_tRel0 (Γ : context) (d : context_decl) : is_open_term (Γ ,, d) (tRel 0).
Proof. reflexivity. Qed.

Lemma is_open_term_tLambda_eta (Γ : context) na w :
  is_open_term Γ w ->
  is_open_term Γ (tLambda na (tSort sProp) (tApp (lift0 1 w) (tRel 0))).
Proof.
  intro Hw. cbn [on_free_vars].
  apply/andP; split; [done|].
  apply/andP; split; [|done].
  apply on_free_vars_lift0.
  eapply on_free_vars_impl; [|exact Hw].
  intros x. rewrite /addnP /shiftnP /=. now repeat nat_compare_specs.
Qed.

Lemma forallb_is_open_snoc_lift (Γ : context) (d : context_decl) args :
  forallb (is_open_term Γ) args ->
  forallb (is_open_term (Γ ,, d)) (map (lift0 1) args).
Proof.
  induction args as [|a args IH]; cbn [map forallb]; [done|].
  move=> /andP [Ha Hrest]. apply/andP; split.
  - now apply is_open_term_snoc_lift.
  - now apply IH.
Qed.

Lemma forallb_is_open_snoc_lift_app (Γ : context) (d : context_decl) args :
  forallb (is_open_term Γ) args ->
  forallb (is_open_term (Γ ,, d)) (map (lift0 1) args ++ [tRel 0]).
Proof.
  intro H. rewrite forallb_app. apply/andP; split.
  - now apply forallb_is_open_snoc_lift.
  - cbn [forallb]. rewrite is_open_term_tRel0. reflexivity.
Qed.

(** One eta-expansion turns an under-applied head into the same head with its
    arguments lifted and one extra [tRel 0]. *)
Lemma tApp_lift_mkApps_Ind i u args :
  tApp (lift0 1 (mkApps (tInd i u) args)) (tRel 0)
  = mkApps (tInd i u) (map (lift0 1) args ++ [tRel 0]).
Proof. rewrite lift_mkApps mkApps_app. reflexivity. Qed.

Lemma tApp_lift_mkApps_Construct i k u args :
  tApp (lift0 1 (mkApps (tConstruct i k u) args)) (tRel 0)
  = mkApps (tConstruct i k u) (map (lift0 1) args ++ [tRel 0]).
Proof. rewrite lift_mkApps mkApps_app. reflexivity. Qed.

(** Inductive heads. *)
Lemma cumulSpecE_ind_underapplied_gen (Σ : global_env_ext) i u u' n :
  ClosedBodies Σ.1 ->
  cumul_Ind_univ Σ Conv i n u u' ->
  forall k Γ args args',
  #|args| = #|args'| ->
  #|args| + k = n ->
  is_closed_context Γ ->
  forallb (is_open_term Γ) args ->
  forallb (is_open_term Γ) args' ->
  All2 (fun a a' => Σ ;;; Γ ⊢ a ≤sE[Conv] a') args args' ->
  Σ ;;; Γ ⊢ mkApps (tInd i u) args ≤sE[Conv] mkApps (tInd i u') args'.
Proof.
  intros wfΣ Huniv k.
  induction k as [|k IHk]; intros Γ args args' Hlen Hsum HclΓ Hoa Hoa' Hall.
  - assert (Hn : #|args| = n) by lia.
    apply cumulE_Ind; [rewrite Hn; exact Huniv | exact Hall].
  - eapply cumulE_Trans with
      (u := tLambda (mkBindAnn nAnon Relevant) (tSort sProp)
              (tApp (lift0 1 (mkApps (tInd i u') args')) (tRel 0))).
    + exact HclΓ.
    + apply is_open_term_tLambda_eta.
      rewrite on_free_vars_mkApps. apply/andP; split; [reflexivity|exact Hoa'].
    + apply cumul_eta_r. rewrite !tApp_lift_mkApps_Ind.
      assert (clΓA : is_closed_context (Γ ,, vass (mkBindAnn nAnon Relevant) (tSort sProp))).
      { rewrite on_free_vars_ctx_snoc HclΓ /=. reflexivity. }
      apply IHk.
      * len; lia.
      * len; lia.
      * exact clΓA.
      * now apply forallb_is_open_snoc_lift_app.
      * now apply forallb_is_open_snoc_lift_app.
      * apply All2_app.
        -- eapply (weakening_cumulSpecE0_All2 Σ Γ
                     [vass (mkBindAnn nAnon Relevant) (tSort sProp)] args args' 1);
             [exact wfΣ|reflexivity|exact HclΓ|exact Hoa|exact Hoa'|exact clΓA|exact Hall].
        -- constructor; [apply cumulE_Refl|constructor].
    + apply cumulSpecE_eta_contract.
Qed.

Lemma cumulSpecE_ind_underapplied (Σ : global_env_ext) Γ pb i mdecl idecl u u' args args' :
  ClosedBodies Σ.1 ->
  declared_inductive Σ i mdecl idecl ->
  is_closed_context Γ ->
  is_open_term Γ (mkApps (tInd i u) args) ->
  is_open_term Γ (mkApps (tInd i u') args') ->
  #|args| = #|args'| ->
  #|args| < context_assumptions (ind_params mdecl ,,, ind_indices idecl) ->
  cumul_Ind_univ Σ Conv i (context_assumptions (ind_params mdecl ,,, ind_indices idecl)) u u' ->
  All2 (fun a a' => Σ ;;; Γ ⊢ a ≤sE[Conv] a') args args' ->
  Σ ;;; Γ ⊢ mkApps (tInd i u) args ≤sE[pb] mkApps (tInd i u') args'.
Proof.
  intros wfΣ _ HclΓ HoW HoW' Hlen Hlt Huniv Hall.
  set (n := context_assumptions (ind_params mdecl ,,, ind_indices idecl)) in *.
  assert (Hoa : forallb (is_open_term Γ) args).
  { move: HoW. rewrite on_free_vars_mkApps => /andP [] _ h. exact h. }
  assert (Hoa' : forallb (is_open_term Γ) args').
  { move: HoW'. rewrite on_free_vars_mkApps => /andP [] _ h. exact h. }
  assert (clΓA : is_closed_context (Γ ,, vass (mkBindAnn nAnon Relevant) (tSort sProp))).
  { rewrite on_free_vars_ctx_snoc HclΓ /=. reflexivity. }
  eapply cumulE_Trans with
    (u := tLambda (mkBindAnn nAnon Relevant) (tSort sProp)
            (tApp (lift0 1 (mkApps (tInd i u') args')) (tRel 0))).
  - exact HclΓ.
  - apply is_open_term_tLambda_eta. exact HoW'.
  - apply cumul_eta_r. rewrite !tApp_lift_mkApps_Ind.
    eapply (cumulSpecE_ind_underapplied_gen Σ i u u' n wfΣ Huniv
              (n - #|args| - 1) (Γ ,, vass (mkBindAnn nAnon Relevant) (tSort sProp))
              (map (lift0 1) args ++ [tRel 0]) (map (lift0 1) args' ++ [tRel 0])).
    + len; lia.
    + len; lia.
    + exact clΓA.
    + now apply forallb_is_open_snoc_lift_app.
    + now apply forallb_is_open_snoc_lift_app.
    + apply All2_app.
      * eapply (weakening_cumulSpecE0_All2 Σ Γ
                  [vass (mkBindAnn nAnon Relevant) (tSort sProp)] args args' 1);
          [exact wfΣ|reflexivity|exact HclΓ|exact Hoa|exact Hoa'|exact clΓA|exact Hall].
      * constructor; [apply cumulE_Refl|constructor].
  - apply cumulSpecE_eta_contract.
Qed.

(** Constructor heads. *)
Lemma cumulSpecE_construct_underapplied_gen (Σ : global_env_ext) i c u u' n :
  ClosedBodies Σ.1 ->
  cumul_Construct_univ Σ Conv i c n u u' ->
  forall k Γ args args',
  #|args| = #|args'| ->
  #|args| + k = n ->
  is_closed_context Γ ->
  forallb (is_open_term Γ) args ->
  forallb (is_open_term Γ) args' ->
  All2 (fun a a' => Σ ;;; Γ ⊢ a ≤sE[Conv] a') args args' ->
  Σ ;;; Γ ⊢ mkApps (tConstruct i c u) args ≤sE[Conv] mkApps (tConstruct i c u') args'.
Proof.
  intros wfΣ Huniv k.
  induction k as [|k IHk]; intros Γ args args' Hlen Hsum HclΓ Hoa Hoa' Hall.
  - assert (Hn : #|args| = n) by lia.
    apply cumulE_Construct; [rewrite Hn; exact Huniv | exact Hall].
  - eapply cumulE_Trans with
      (u := tLambda (mkBindAnn nAnon Relevant) (tSort sProp)
              (tApp (lift0 1 (mkApps (tConstruct i c u') args')) (tRel 0))).
    + exact HclΓ.
    + apply is_open_term_tLambda_eta.
      rewrite on_free_vars_mkApps. apply/andP; split; [reflexivity|exact Hoa'].
    + apply cumul_eta_r. rewrite !tApp_lift_mkApps_Construct.
      assert (clΓA : is_closed_context (Γ ,, vass (mkBindAnn nAnon Relevant) (tSort sProp))).
      { rewrite on_free_vars_ctx_snoc HclΓ /=. reflexivity. }
      apply IHk.
      * len; lia.
      * len; lia.
      * exact clΓA.
      * now apply forallb_is_open_snoc_lift_app.
      * now apply forallb_is_open_snoc_lift_app.
      * apply All2_app.
        -- eapply (weakening_cumulSpecE0_All2 Σ Γ
                     [vass (mkBindAnn nAnon Relevant) (tSort sProp)] args args' 1);
             [exact wfΣ|reflexivity|exact HclΓ|exact Hoa|exact Hoa'|exact clΓA|exact Hall].
        -- constructor; [apply cumulE_Refl|constructor].
    + apply cumulSpecE_eta_contract.
Qed.

Lemma cumulSpecE_construct_underapplied (Σ : global_env_ext) Γ pb i c mdecl idecl cdecl u u' args args' :
  ClosedBodies Σ.1 ->
  declared_constructor Σ (i, c) mdecl idecl cdecl ->
  is_closed_context Γ ->
  is_open_term Γ (mkApps (tConstruct i c u) args) ->
  is_open_term Γ (mkApps (tConstruct i c u') args') ->
  #|args| = #|args'| ->
  #|args| < ind_npars mdecl + context_assumptions (cstr_args cdecl) ->
  cumul_Construct_univ Σ Conv i c (ind_npars mdecl + context_assumptions (cstr_args cdecl)) u u' ->
  All2 (fun a a' => Σ ;;; Γ ⊢ a ≤sE[Conv] a') args args' ->
  Σ ;;; Γ ⊢ mkApps (tConstruct i c u) args ≤sE[pb] mkApps (tConstruct i c u') args'.
Proof.
  intros wfΣ _ HclΓ HoW HoW' Hlen Hlt Huniv Hall.
  set (n := ind_npars mdecl + context_assumptions (cstr_args cdecl)) in *.
  assert (Hoa : forallb (is_open_term Γ) args).
  { move: HoW. rewrite on_free_vars_mkApps => /andP [] _ h. exact h. }
  assert (Hoa' : forallb (is_open_term Γ) args').
  { move: HoW'. rewrite on_free_vars_mkApps => /andP [] _ h. exact h. }
  assert (clΓA : is_closed_context (Γ ,, vass (mkBindAnn nAnon Relevant) (tSort sProp))).
  { rewrite on_free_vars_ctx_snoc HclΓ /=. reflexivity. }
  eapply cumulE_Trans with
    (u := tLambda (mkBindAnn nAnon Relevant) (tSort sProp)
            (tApp (lift0 1 (mkApps (tConstruct i c u') args')) (tRel 0))).
  - exact HclΓ.
  - apply is_open_term_tLambda_eta. exact HoW'.
  - apply cumul_eta_r. rewrite !tApp_lift_mkApps_Construct.
    eapply (cumulSpecE_construct_underapplied_gen Σ i c u u' n wfΣ Huniv
              (n - #|args| - 1) (Γ ,, vass (mkBindAnn nAnon Relevant) (tSort sProp))
              (map (lift0 1) args ++ [tRel 0]) (map (lift0 1) args' ++ [tRel 0])).
    + len; lia.
    + len; lia.
    + exact clΓA.
    + now apply forallb_is_open_snoc_lift_app.
    + now apply forallb_is_open_snoc_lift_app.
    + apply All2_app.
      * eapply (weakening_cumulSpecE0_All2 Σ Γ
                  [vass (mkBindAnn nAnon Relevant) (tSort sProp)] args args' 1);
          [exact wfΣ|reflexivity|exact HclΓ|exact Hoa|exact Hoa'|exact clΓA|exact Hall].
      * constructor; [apply cumulE_Refl|constructor].
  - apply cumulSpecE_eta_contract.
Qed.

End RenamingEta.

(** * Environment weakening of [cumulSpecE0]

  The copy of base [weakening_env_cumulSpec0] ([Conversion/PCUICWeakeningEnvConv]),
  generic in the environment's [Pcmp]/[P] as base's is, plus the [cumul_eta_l] case
  (its premise is the induction hypothesis) and the [cumulE_prim_op] case (the
  operation table, the declaration and the readback transport along [extends], as
  in base's [red_prim_op] case of [weakening_env_red1]). *)
Section ExtendsWfE.
  Context {cf : checker_flags}.
  Context {Pcmp: global_env_ext -> context -> conv_pb -> term -> term -> Type}.
  Context {P: global_env_ext -> context -> judgment -> Type}.

  Let wf := on_global_env Pcmp P.

  Local Hint Resolve extends_prim_op_of extends_readback : extends.

Lemma weakening_env_cumulSpecE0 Σ Σ' φ Γ pb M N :
  wf Σ' ->
  extends Σ Σ' ->
  cumulSpecE0 (Σ, φ) Γ pb M N ->
  cumulSpecE0 (Σ', φ) Γ pb M N.
Proof.
  intros HΣ' Hextends Ind.
  revert pb Γ M N Ind Σ' HΣ' Hextends.
  induction 1 using cumulSpecE0_rect.
  all:intros; try solve [econstructor; eauto with extends; intuition auto].
  all: lazymatch goal with
       | [ H : cumul_predicate_dep _ _ _ |- _ ] => apply cumul_predicate_undep in H
       | _ => idtac
       end.
  - eapply cumulE_Evar. solve_all.
  - eapply cumulE_Case.
    * cbv [cumul_predicate] in *; destruct_head'_prod. clear c0. repeat split; tas.
      + solve_all.
      + eapply cmp_universe_instance_impl'; tea. tc.
      + eauto.
    * eauto.
    * unfold cumul_branches, cumul_branch in *. solve_all.
  - eapply cumulE_Fix; unfold cumul_mfixpoint in *; solve_all.
  - eapply cumulE_CoFix; unfold cumul_mfixpoint in *; solve_all.
  - eapply cumulE_Prim; solve_all.
    destruct X; constructor; eauto.
    * eapply subrel_extends_cmp_universe; tea.
    * solve_all.
  - eapply cumulE_Ind; eauto. 2:solve_all.
    eapply @cmp_global_instance_weaken_env. 1,2,5:eauto. all: tc.
  - eapply cumulE_Construct; eauto. 2:solve_all.
    eapply @cmp_global_instance_weaken_env. 1,2,5:eauto. all: tc.
  - eapply cumulE_Sort. eapply subrelations_compare_extends; tea.
  - eapply cumulE_Const. eapply cmp_universe_instance_impl'; eauto; tc.
Defined.

Lemma weakening_env_convSpecE Σ Σ' φ Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  convSpecE (Σ, φ) Γ M N ->
  convSpecE (Σ', φ) Γ M N.
Proof using P Pcmp. apply weakening_env_cumulSpecE0 with (pb := Conv). Qed.

Lemma weakening_env_cumulSpecE Σ Σ' φ Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  cumulSpecE (Σ, φ) Γ M N ->
  cumulSpecE (Σ', φ) Γ M N.
Proof using P Pcmp. apply weakening_env_cumulSpecE0 with (pb := Cumul). Qed.

End ExtendsWfE.

(** * Instantiation, universe substitution and configuration weakening of [cumulSpecE0]

  The remainder of the specification's syntactic closure, beside [cumulSpecE_renameP]
  and [weakening_env_cumulSpecE0] above. Each lemma is its base twin's induction with
  two more cases:
  - [cumul_eta_l]: each map commutes with [lift0 1] and fixes [tRel 0], so the eta
    rule applies again to the mapped terms, with the mapped domain;
  - [cumulE_prim_op]: the head's literal arguments and its reduct are ground, so each
    map fixes them, exactly as in the base twins' own [cumul_prim_op] cases.
  [cumulSpecE_instP] takes [ClosedBodies Σ.1] where base [inst_cumulSpec] takes
  [wf Σ]: the only use of the environment is the δ case's closed constant body, and
  [closed_bodies] gives it. *)

Section InstEta.

Context `{cf : checker_flags}.

Lemma cumulSpecE_instP pb (Σ : global_env_ext) Γ Δ σ A B :
  ClosedBodies Σ.1 ->
  closed_subst Γ σ Δ ->
  is_closed_context Γ ->
  is_open_term Γ A ->
  is_open_term Γ B ->
  Σ ;;; Γ ⊢ A ≤sE[pb] B ->
  Σ ;;; Δ ⊢ A.[σ] ≤sE[pb] B.[σ].
Proof.
  intros cb hσ HΓ HfreeA HfreeB e.
  revert pb Γ A B e Δ σ hσ HΓ HfreeA HfreeB e.
  induction 1; intros.
  all: repeat inv_on_free_vars.
  all: lazymatch goal with
       | [ H : cumul_predicate_dep _ _ _ |- _ ] => apply cumul_predicate_undep in H
       | _ => idtac
       end.
  all: repeat match goal with
         | [ H : All2_dep _ _ |- _ ] => apply All2_undep in H
         end.
  (* cumulE_prim_op: instantiation fixes the ground head arguments and reduct. *)
  all: try (rewrite inst_mkApps; cbn [inst];
    rewrite (map_prim_ground (inst σ) _ (prim_ground_inst σ));
    match goal with H : PCUICPrimitiveRed.readback _ _ _ = Some ?w |- _ =>
      rewrite (prim_ground_inst σ w (prim_ground_readback H)) end;
    eapply cumulE_prim_op; eassumption).
  - rewrite subst10_inst. sigma. solve [econstructor].
  - rewrite subst10_inst. sigma. solve [econstructor].
  - destruct (nth_error Γ i) eqn:hnth; noconf pf.
    red in hσ. destruct hσ as [_ [_ hσ]]. specialize (hσ _ _ hnth) as IH.
    specialize IH with (1:=H) as [[x' [decl' [hi [hnth' eqbod]]]]|eqr].
    * rewrite /= hi. sigma.
      destruct (decl_body decl') eqn:hdecl => //. noconf eqbod.
      let H1 := match goal with H : rename _ _ = _ |- _ => H end in
      rewrite -H1. sigma.
      relativize (t.[_]); [eapply cumulE_rel|].
      { now rewrite hnth' /= hdecl. }
      rewrite lift0_inst. now sigma.
    * rewrite /= eqr. sigma. reflexivity.
  - cbn. rewrite inst_mkApps. simpl.
    rewrite inst_iota_red //.
    * rewrite length_skipn; lia.
    * change (bcontext br) with (bcontext (inst_branch σ br)).
      rewrite closedn_ctx_on_free_vars.
      eapply nth_error_forallb in p4; tea. simpl in p4.
      move/andP: p4 => [] clbctx clbod.
      now rewrite test_context_k_closed_on_free_vars_ctx in clbctx.
    * eapply cumulE_iota.
      + rewrite nth_error_map Hbrs /= //.
      + simpl. now len.
    - rewrite 2!inst_mkApps. simpl.
      eapply cumulE_fix.
      + eapply inst_unfold_fix. eassumption.
      + eapply is_constructor_inst. assumption.
    - simpl. rewrite !inst_mkApps. simpl.
      eapply cumulE_cofix_case.
      eapply inst_unfold_cofix. eassumption.
    - simpl. rewrite 2!inst_mkApps. simpl.
      eapply cumulE_cofix_proj.
      eapply inst_unfold_cofix. eassumption.
    - simpl.
      rewrite inst_closed0.
      * rewrite closedn_subst_instance.
        eapply closed_bodies. all: eauto.
      * eapply cumulE_delta; eauto.
    - simpl. rewrite inst_mkApps. simpl.
      eapply cumulE_proj; rewrite nth_error_map. rewrite Hargs. reflexivity.
    - pose proof hσ.1.
      eapply cumulE_Trans; try eapply X0; try eapply X2; eauto.
      eapply inst_is_open_term; eauto.
    - eapply cumulE_Sym; try eapply X0; eauto.
    - eapply cumulE_Refl; eauto.
  - cbn. eapply cumulE_Evar. cbn in *.
    repeat toAll. eapply All2_impl. 1:tea. cbn; intros.
    eapply X0.1.2; intuition.
  - eapply cumulE_App; try apply IHe1; try apply IHe2; eauto.
  - pose proof hσ.1. cbn; eapply cumulE_Lambda; try apply IHe1; try apply IHe2; eauto;
    try rewrite shiftnP_S; eauto.
    * eapply closed_subst_up_vass; eauto. eapply inst_is_open_term; eauto.
    * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
  - eapply cumulE_Prod; try apply IHe1; try apply IHe2; eauto;
    try rewrite shiftnP_S; eauto.
    * eapply closed_subst_up_vass; eauto. eapply inst_is_open_term; eauto.
    * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
  - eapply cumulE_LetIn; try apply IHe1; try apply IHe2; eauto; try apply IHe3;
    try rewrite shiftnP_S; eauto.
    * eapply closed_subst_up_vdef; eauto; eapply inst_is_open_term; eauto.
    * rewrite on_free_vars_ctx_snoc_def; eauto.
  - rename p0 into Hp'; rename p1 into Hreturn'; rename p2 into Hcontext'; rename p3 into Hc'; rename p4 into Hbrs'.
    rename Hp into Hpold.
    rename p5 into Hp; rename p6 into Hreturn; rename p7 into Hcontext; rename p8 into Hc; rename p9 into Hbrs.
    eapply cumulE_Case; fold inst.
    * unfold cumul_predicate in *; destruct_head'_prod.
      repeat split; eauto.
      + eapply All2_map. repeat toAll.
        eapply All2_impl. 1: tea. cbn; intros. destruct_head'_prod; eauto.
      + unfold preturn. cbn.
        unshelve erewrite (All2_length _ : #|pcontext _| = #|pcontext _|); shelve_unifiable; tea.
        exactly_once (idtac; multimatch goal with H : _ |- _ => eapply H end); eauto.
        ++ unshelve erewrite <- (All2_length _ : #|pcontext _| = #|pcontext _|); shelve_unifiable; tea.
           rewrite <- inst_case_predicate_context_length.
            rewrite inst_case_predicate_context_inst; eauto.
            eapply closed_subst_ext. 2: symmetry; apply up_Upn.
            eapply closed_subst_app; eauto. rewrite inst_inst_case_context; eauto.
            rewrite on_free_vars_ctx_inst_case_context_nil; eauto.
            +++ rewrite forallb_map. eapply forallb_impl. 2:tea. cbn; intros.
                eapply inst_is_open_term; eauto.
            +++ rewrite length_map. rewrite inst_context_on_free_vars ; eauto.
        ++ unfold PCUICCases.inst_case_predicate_context.
            apply on_free_vars_ctx_inst_case_context; eauto.
        ++ unfold PCUICCases.inst_case_predicate_context.
            unfold is_open_term. rewrite length_app.
            rewrite <- shiftnP_add.
            rewrite inst_case_predicate_context_length.
            eassumption.
        ++ unfold PCUICCases.inst_case_predicate_context.
            unfold is_open_term. rewrite length_app.
            rewrite <- shiftnP_add.
            rewrite inst_case_predicate_context_length.
            unshelve erewrite (All2_length _ : #|pcontext _| = #|pcontext _|); shelve_unifiable; tea.
    * eauto.
    * rename Hbody into Hbrsbrs'. unfold cumul_branches, cumul_branch in *.
      repeat toAll.
      eapply All2_impl. 1: tea. cbn; intros; destruct_head'_prod.
      unshelve erewrite (All2_length _ : #|bcontext _| = #|bcontext _|); shelve_unifiable; tea.
      split; eauto.
      repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
      rewrite -> test_context_k_closed_on_free_vars_ctx in *.
      exactly_once (idtac; multimatch goal with H : _ |- _ => eapply H end); eauto.
      + unshelve erewrite <- (All2_length _ : #|bcontext _| = #|bcontext _|); shelve_unifiable; tea.
      rewrite <- (inst_case_branch_context_length p).
      rewrite inst_case_branch_context_inst; eauto.
      eapply closed_subst_ext. 2: symmetry; apply up_Upn.
      eapply closed_subst_app; eauto.
      rewrite inst_inst_case_context_wf; eauto.
        ++ rewrite test_context_k_closed_on_free_vars_ctx; tea.
        ++  rewrite on_free_vars_ctx_inst_case_context_nil; eauto.
          +++ repeat toAll. eapply All_impl; tea. simpl; intros.
              eapply inst_is_open_term; eauto.
          +++ rewrite length_map. tea.
      + unfold PCUICCases.inst_case_predicate_context.
        apply on_free_vars_ctx_inst_case_context; eauto.
        repeat toAll; eauto.
      + unfold PCUICCases.inst_case_predicate_context.
        unfold is_open_term. rewrite length_app.
        rewrite <- shiftnP_add.
        rewrite inst_case_branch_context_length.
        eassumption.
      + unfold PCUICCases.inst_case_predicate_context.
        unfold is_open_term. rewrite length_app.
        rewrite <- shiftnP_add.
        rewrite inst_case_branch_context_length.
        unshelve erewrite (All2_length _ : #|bcontext _| = #|bcontext _|); shelve_unifiable; tea.
   - eapply cumulE_Proj; try apply X0; eauto.
   - cbn. eapply cumulE_Fix. cbn in HfreeA, HfreeB. unfold cumul_mfixpoint in *.
     repeat toAll. eapply All2_impl. 1: tea. cbn; intros.
     destruct_head'_prod.
     repeat split; eauto.
     * exactly_once (idtac; multimatch goal with H : _ |- _ => eapply H end); eauto.
       all: cbv [test_def] in *; cbn in *.
       all: repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
       all: tea.
     * rewrite <- (All2_length X).
       exactly_once (idtac; multimatch goal with H : _ |- _ => eapply H end); eauto.
       all: cbv [test_def] in *; cbn in *.
       all: repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
       + rewrite inst_fix_context_up.
       rewrite <- fix_context_length.
       eapply closed_subst_ext. 2: symmetry; apply up_Upn.
       apply closed_subst_app; eauto. rewrite <- inst_fix_context.
        apply on_free_vars_fix_context.
         apply All_map.
         eapply All2_All_left. 1: tea. cbn ; intros.
         destruct X0 as [[Hx0 _] _].
         unfold test_def. unfold test_def in Hx0.
         apply andb_and in Hx0. destruct Hx0 as [Hx0type Hx0body].
         apply andb_and. cbn. split.
         ++ eapply inst_is_open_term; eauto.
         ++ rewrite length_map.
            rewrite <- fix_context_length. rewrite <- up_Upn.
            eapply usubst_on_free_vars_shift; eauto.
            rewrite fix_context_length; eauto.
        + rewrite on_free_vars_ctx_app.
         apply andb_and; split; eauto.
         apply on_free_vars_fix_context.
         eapply All2_All_left. 1: tea. cbn; intros.
         apply X0.1.
         + unfold is_open_term. rewrite length_app.
         rewrite <- shiftnP_add.
         rewrite fix_context_length. eauto.
         + unfold is_open_term. rewrite length_app.
         rewrite <- shiftnP_add.
         rewrite fix_context_length.
         rewrite (All2_length X). eauto.
   - cbn. rewrite (All2_length X).
     eapply cumulE_CoFix. cbn in HfreeA, HfreeB. unfold cumul_mfixpoint in *.
     repeat toAll.
     eapply All2_impl. 1: tea. cbn; intros.
     destruct_head'_prod.
     repeat split; eauto.
     * exactly_once (idtac; multimatch goal with H : _ |- _ => eapply H end); eauto.
       all: cbv [test_def] in *; cbn in *.
       all: repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
       all: eauto.
     * rewrite <- (All2_length X).
       exactly_once (idtac; multimatch goal with H : _ |- _ => eapply H end); eauto.
       all: cbv [test_def] in *; cbn in *.
       all: repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
       + rewrite inst_fix_context_up.
       rewrite <- fix_context_length.
       eapply closed_subst_ext. 2: symmetry; apply up_Upn.
       apply closed_subst_app; eauto. rewrite <- inst_fix_context.
        apply on_free_vars_fix_context.
         apply All_map.
         eapply All2_All_left. 1: tea. cbn ; intros.
         destruct X0 as [[Hx0 _] _].
         unfold test_def. unfold test_def in Hx0.
         apply andb_and in Hx0. destruct Hx0 as [Hx0type Hx0body].
         apply andb_and. cbn. split.
         ++ eapply inst_is_open_term; eauto.
         ++ rewrite length_map.
            rewrite <- fix_context_length. rewrite <- up_Upn.
            eapply usubst_on_free_vars_shift; eauto.
            rewrite fix_context_length; eauto.
        + rewrite on_free_vars_ctx_app.
         apply andb_and; split; eauto.
         apply on_free_vars_fix_context.
         eapply All2_All_left. 1: tea. cbn; intros.
         apply X0.1.
         + unfold is_open_term. rewrite length_app.
         rewrite <- shiftnP_add.
         rewrite fix_context_length. eauto.
         + unfold is_open_term. rewrite length_app.
         rewrite <- shiftnP_add.
         rewrite fix_context_length.
         rewrite (All2_length X). eauto.
   - cbn. eapply cumulE_Prim. depelim X; cbn in HfreeA, HfreeB; rtoProp; constructor; cbn; eauto. solve_all.
   - cbn. repeat rewrite inst_mkApps. eapply cumulE_Ind.
     * repeat rewrite length_map; eauto.
     * repeat toAll.
       eapply All2_impl. 1: tea. cbn; intros.
       destruct_head'_prod.
       eauto.
   - cbn. repeat rewrite inst_mkApps. eapply cumulE_Construct.
     * repeat rewrite length_map; eauto.
     * repeat toAll.
       eapply All2_impl. 1: tea. cbn; intros.
       destruct_head'_prod.
       eauto.
   - eapply cumulE_Sort; eauto.
   - eapply cumulE_Const; eauto.
  - (* function eta: the case base's lemma does not have. [tRel 0] is fixed by
       [⇑ σ], and [lift0 1] commutes with it. *)
    assert (Hlift : (lift0 1 u).[⇑ σ] = lift0 1 u.[σ]).
    { rewrite !lift0_inst !inst_assoc. apply inst_ext.
      first [ reflexivity | apply shift_Up_comm ]. }
    assert (Hr : (tApp (lift0 1 u) (tRel 0)).[⇑ σ] = tApp (lift0 1 u.[σ]) (tRel 0)).
    { cbn [inst]. now rewrite Hlift. }
    rewrite inst_lam. apply cumul_eta_l.
    rewrite -Hr.
    eapply IHe.
    * eapply closed_subst_ext; [|apply up_Up].
      eapply closed_subst_up_vass; eauto. eapply inst_is_open_term; eauto.
    * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
    * replace #|Γ ,, vass na A| with (S #|Γ|) by reflexivity.
      rewrite shiftnP_S. assumption.
    * cbn [on_free_vars]. apply andb_and. split.
      + eapply on_free_vars_lift0. eapply on_free_vars_impl; [| exact HfreeB].
        intros i. rewrite /addnP /shiftnP /=. now repeat nat_compare_specs.
      + rewrite /shiftnP /=. reflexivity.
    * exact e.
Defined.

Lemma convSpecE_instP (Σ : global_env_ext) Γ Δ σ A B :
  ClosedBodies Σ.1 ->
  closed_subst Γ σ Δ ->
  is_closed_context Γ ->
  is_open_term Γ A ->
  is_open_term Γ B ->
  Σ ;;; Γ ⊢ A ≤sE[Conv] B ->
  Σ ;;; Δ ⊢ A.[σ] ≤sE[Conv] B.[σ].
Proof. apply cumulSpecE_instP. Qed.

End InstEta.

Section SubstInstanceEta.

Context `{cf : checker_flags}.

(** The E analogue of [cumulSpec_subst_instance] ([Typing/PCUICUnivSubstitutionTyp.v]).
    No environment premise: the δ case is [subst_instance_two], not closedness. *)
Lemma cumulSpecE_subst_instance (Σ : global_env_ext) Γ u A B pb univs :
  valid_constraints (global_ext_constraints (Σ.1, univs))
                    (subst_instance_cstrs u Σ) ->
  Σ ;;; Γ ⊢ A ≤sE[pb] B ->
  (Σ.1,univs) ;;; subst_instance u Γ ⊢ subst_instance u A ≤sE[pb] subst_instance u B.
Proof.
  intros e H.
  induction H; intros; cbn.
  (* function eta: the case base's lemma does not have, and the one case the
     congruence solver below cannot close, because [subst_instance] commutes with
     [lift] only by [subst_instance_lift] and not by conversion. *)
  all: try lazymatch goal with
       | [ H : context [ subst_instance _ (tApp (lift0 1 _) (tRel 0)) ] |- _ ] =>
         apply cumul_eta_l; cbn in H; rewrite subst_instance_lift in H; exact H
       end.
  all: try solve [econstructor; intuition eauto].
  all: lazymatch goal with
       | [ H : cumul_predicate_dep _ _ _ |- _ ] => apply cumul_predicate_undep in H
       | _ => idtac
       end.
  - rewrite subst_instance_subst. solve [econstructor].
  - rewrite subst_instance_subst. solve [econstructor].
  - rewrite subst_instance_lift. eapply cumulE_rel.
    unfold subst_instance.
    cbv [option_map subst_instance_context map_context map_decl] in *.
    rewrite nth_error_map; cbv [option_map].
    repeat destruct ?; inversion pf; clear pf; try congruence.
    match goal with H : Some _ = Some _ |- _ => inversion H; clear H end.
    subst; cbn.
    reflexivity.
  - rewrite subst_instance_mkApps. cbn.
    rewrite iota_red_subst_instance.
    change (bcontext br) with (bcontext (map_branch (subst_instance u) br)).
    eapply cumulE_iota; eauto with pcuic.
    * rewrite nth_error_map Hbrs //.
    * simpl. now len.
  - rewrite !subst_instance_mkApps. cbn.
    eapply cumulE_fix.
    + unfold unfold_fix in *. destruct (nth_error mfix idx) eqn:E.
      * match goal with H : Some _ = Some _ |- _ => inversion H; clear H end.
        rewrite nth_error_map E. cbn.
        destruct d. cbn in *. cbn in *; try congruence.
        f_equal. f_equal.
        now rewrite subst_instance_subst fix_subst_instance_subst.
      * congruence.
    + unfold is_constructor in *.
      destruct (nth_error args narg) eqn:E; try congruence.
      rewrite nth_error_map E; cbn.
      now rewrite isConstruct_app_subst_instance.
  - rewrite !subst_instance_mkApps.
    unfold unfold_cofix in *. destruct (nth_error mfix idx) eqn:E; try congruence.
    match goal with H : Some _ = Some _ |- _ => inversion H; clear H end.
    eapply cumulE_cofix_case.  fold subst_instance_constr.
    unfold unfold_cofix.
    rewrite nth_error_map E. cbn.
    rewrite subst_instance_subst.
    now rewrite cofix_subst_instance_subst.
  - unfold unfold_cofix in *.
    destruct nth_error eqn:E; try congruence.
    match goal with H : Some _ = Some _ |- _ => inversion H; clear H end.
    rewrite !subst_instance_mkApps.
    eapply cumulE_cofix_proj. fold subst_instance.
    unfold unfold_cofix.
    rewrite nth_error_map. destruct nth_error; cbn.
     1: rewrite subst_instance_subst cofix_subst_instance_subst.
    all: now inversion E.
  - rewrite subst_instance_two. solve [econstructor; eauto].
  - (* cumulE_prim_op: the head keeps its constant, and the literal arguments
       and the reduct are ground, so the instance substitution fixes them *)
    rewrite subst_instance_mkApps /=.
    rewrite (map_prim_ground (subst_instance u) ls (prim_ground_subst_instance u)).
    rewrite (prim_ground_subst_instance u v (prim_ground_readback Hreadback)).
    eapply cumulE_prim_op; eassumption.
  - rewrite !subst_instance_mkApps.
    eapply cumulE_proj. now rewrite nth_error_map Hargs.
  - eapply cumulE_Trans; intuition eauto.
    * rewrite on_free_vars_ctx_subst_instance; eauto.
    * rewrite on_free_vars_subst_instance. unfold is_open_term.
      replace #|Γ@[u]| with #|Γ|; eauto. rewrite length_map; eauto.
  - eapply cumulE_Evar. eapply All2_map.
    repeat toAll.
    eapply All2_impl.  1: tea. cbn; intros. eapply X0.2; eauto.
  - eapply cumulE_Case; try solve [intuition eauto; eauto].
    * cbv [cumul_predicate] in *; destruct_head'_prod. repeat split; eauto; cbn.
      + apply All2_map. repeat toAll. eapply All2_impl. 1: tea. cbn; intros. destruct_head'_prod; eauto.
      + apply precompose_subst_instance. eapply cmp_universe_instance_impl.
        1:now apply eq_universe_subst_instance.
        eauto.
      + rewrite -> subst_instance_app, inst_case_predicate_context_subst_instance in *.
        eauto.
    * unfold cumul_branches, cumul_branch in *.
      eapply All2_map. repeat toAll. eapply All2_impl. 1: tea. cbn; intros.
      repeat split; intuition eauto.
      rewrite -> subst_instance_app, inst_case_branch_context_subst_instance in *; eauto.
  - eapply cumulE_Fix. apply All2_map. repeat toAll. eapply All2_impl. 1: tea.
    cbn; intros; intuition eauto.
    rewrite -> subst_instance_app, fix_context_subst_instance in *; eauto.
  - eapply cumulE_CoFix. apply All2_map. repeat toAll. eapply All2_impl. 1: tea.
    cbn; intros; intuition eauto.
    rewrite -> subst_instance_app, fix_context_subst_instance in *; eauto.
  - eapply cumulE_Prim. depelim e0; depelim X; cbn in H; cbn; noconf H; cbn in H; constructor; cbn -[Universe.make]; eauto.
    + rewrite -!subst_instance_universe_make.
      eapply eq_universe_subst_instance; tea.
    + solve_all.
 - repeat rewrite subst_instance_mkApps. eapply cumulE_Ind.
    * apply precompose_subst_instance_global.
      rewrite length_map. eapply cmp_global_instance_impl_same_napp; try eapply H; eauto.
      { now apply eq_universe_subst_instance. }
      { now apply compare_universe_subst_instance. }
    * eapply All2_map. repeat toAll. eapply All2_impl. 1: tea. cbn; intros.
      eapply X0.2; eauto.
 - repeat rewrite subst_instance_mkApps. eapply cumulE_Construct.
    * apply precompose_subst_instance_global. cbn.
      rewrite length_map. eapply cmp_global_instance_impl_same_napp; try eapply H; eauto.
      { now apply eq_universe_subst_instance. }
      { now apply compare_universe_subst_instance. }
    * eapply All2_map. repeat toAll. eapply All2_impl. 1: tea. cbn; intros.
      eapply X0.2; eauto.
  - eapply cumulE_Sort. now apply compare_sort_subst_instance.
  - eapply cumulE_Const. apply precompose_subst_instance.
    eapply cmp_universe_instance_impl; eauto.
    now apply compare_universe_subst_instance.
Defined.

Lemma convSpecE_subst_instance (Σ : global_env_ext) Γ u A B univs :
  valid_constraints (global_ext_constraints (Σ.1, univs))
                    (subst_instance_cstrs u Σ) ->
  Σ ;;; Γ ⊢ A ≤sE[Conv] B ->
  (Σ.1,univs) ;;; subst_instance u Γ ⊢ subst_instance u A ≤sE[Conv] subst_instance u B.
Proof. apply cumulSpecE_subst_instance. Qed.

End SubstInstanceEta.

(** * Configuration weakening of [cumulSpecE0]

  The E analogue of [weakening_config_cumulSpec0] ([Conversion/PCUICWeakeningConfigConv.v]).
  A weaker configuration changes no term, so both new cases are the rule re-applied to
  the same terms: the eta case is its own induction hypothesis, and the primitive
  operation case transports its premises unchanged. *)

Lemma weakening_config_cumulSpecE0 {cf1 cf2} Σ Γ pb M N :
  config.impl cf1 cf2 ->
  @cumulSpecE0 cf1 Σ Γ pb M N ->
  @cumulSpecE0 cf2 Σ Γ pb M N.
Proof.
  intros Hcf.
  induction 1.
  all: intros.
  (* function eta: the induction hypothesis is the premise of the same rule. *)
  all: try lazymatch goal with
       | [ H : @cumulSpecE0 _ _ _ Conv _ (tApp (lift0 1 _) (tRel 0)) |- _ ] =>
         apply cumul_eta_l; exact H
       end.
  all: try solve [econstructor; try eassumption; intuition auto].
  all: lazymatch goal with
       | [ H : cumul_predicate_dep _ _ _ |- _ ] => apply cumul_predicate_undep in H
       | _ => idtac
       end.
  - eapply cumulE_Evar. solve_all.
  - eapply cumulE_Case.
    * cbv [cumul_predicate] in *; destruct_head'_prod. repeat split; tas.
      eapply cmp_universe_instance_impl';
        [ hnf; intros * ?; eapply (@cmp_universe_config_impl cf1 cf2) | ];
        eassumption.
    * assumption.
    * unfold cumul_branches, cumul_branch in *. solve_all.
  - eapply cumulE_Fix. unfold cumul_mfixpoint in *. solve_all.
  - eapply cumulE_CoFix. unfold cumul_mfixpoint in *. solve_all.
  - eapply cumulE_Prim; solve_all.
    destruct X; constructor; eauto.
    * now eapply (@cmp_universe_config_impl cf1 cf2).
    * solve_all.
  - eapply cumulE_Ind; eauto. 2:solve_all.
    eapply @cmp_global_instance_impl; [ .. | eassumption ].
    3: auto with arith. all: intros ??; now apply (@cmp_universe_config_impl cf1 cf2).
  - eapply cumulE_Construct; eauto. 2:solve_all.
    eapply @cmp_global_instance_impl; [ .. | eassumption ].
    3: auto with arith. all: intros ??; now apply (@cmp_universe_config_impl cf1 cf2).
  - eapply cumulE_Sort. eapply (@cmp_sort_config_impl cf1 cf2); eassumption.
  - eapply cumulE_Const. eapply cmp_universe_instance_impl'; eauto; tc.
    hnf; intros *; eapply (@cmp_universe_config_impl cf1 cf2); eassumption.
Defined.

Lemma weakening_config_convSpecE {cf1 cf2} Σ Γ M N :
  config.impl cf1 cf2 ->
  @cumulSpecE0 cf1 Σ Γ Conv M N ->
  @cumulSpecE0 cf2 Σ Γ Conv M N.
Proof. apply weakening_config_cumulSpecE0 with (pb := Conv). Qed.

Lemma weakening_config_cumulSpecE {cf1 cf2} Σ Γ M N :
  config.impl cf1 cf2 ->
  @cumulSpecE0 cf1 Σ Γ Cumul M N ->
  @cumulSpecE0 cf2 Σ Γ Cumul M N.
Proof. apply weakening_config_cumulSpecE0 with (pb := Cumul). Qed.
