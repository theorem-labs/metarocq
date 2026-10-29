(* Distributed under the terms of the MIT license. *)
(** * [Typing/PCUICContextConversionTyp] over [typingE]

  Context conversion and context cumulativity of [typingE] derivations
  ([context_cumulativity_propE], [context_cumulativityE], [closed_context_cumulativityE],
  [context_conversionE], [closed_context_conversionE]) and the lemmas they use. The base
  file copied over [typingE], [wf_localE], [wfE], [cumulSpecE0], [ws_cumul_pbE] and
  [ws_cumul_ctx_pbE]; the unscoped algorithmic relation [cumulAlgo_gen] of base becomes
  the canonical join [JoinE] ([PCUICEtaI5]), so the unscoped context relations are
  [cumul_pb_context JoinE pb Σ]. Every lemma takes the suffix [E] and states its base
  twin with the relations renamed. The purely syntactic lemmas of the base file
  ([lift0_open], [split_closed_context], [nth_error_closed_context],
  [on_free_vars_decl_lift], [on_free_vars_decl_lift_impl], [nth_error_Some_add],
  [nth_error_closed_context_lift]) are used from base.

  Where base moves between the specification and the algorithmic relation, the copy
  uses [into_ws_cumul_pbE_spec] (for base's [cumulSpec_cumulAlgo] and
  [convSpec_convAlgo_curry]) and [ws_cumul_pbE_forget_spec] (for base's
  [cumulAlgo_cumulSpec]), both in [PCUICWellScopedCumulativityEta]. A conversion moves
  along a context cumulativity by [ws_cumul_pbE_ws_cumul_ctx_pb] ([PCUICWsCumulEtaCtx]);
  the guard moves by [fix_guard_context_cumulativityE] and
  [cofix_guard_context_cumulativityE] ([PCUICGuardClosureEta]).

  ** What is not as in base

  [cumul_context_Algo_SpecE] assumes [ClosedBodies Σ]; base's [cumul_context_Algo_Spec]
  assumes nothing. Base's [cumulAlgo_cumulSpec] needs no premise, but its E counterpart
  [ws_cumul_pbE_forget_spec] is the join-to-specification direction [I5_join_to_spec],
  which needs closed constant bodies. Its only use here holds [wfE Σ], which gives
  [ClosedBodies Σ] ([wfE_ClosedBodies]).

  **The hypotheses are satisfiable:** [wfE Σ] and [ClosedBodies Σ] by any well-formed
  environment ([wf_incl_E], [wfE_ClosedBodies]); the context premises by two well-formed
  contexts that differ by an η-step. Instances: [PCUICTypingEtaCopy9Instances]. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils
     PCUICLiftSubst PCUICTyping PCUICCases PCUICCumulativity PCUICCumulativitySpec
     PCUICReduction PCUICEquality PCUICOnFreeVars PCUICWellScopedCumulativity
     PCUICGuardCondition PCUICConfluence PCUICConversion PCUICContextConversion PCUICClosedTyp
     PCUICContextConversionTyp
     PCUICCumulativitySpecEta PCUICCumulativitySpecEtaClosure PCUICClosedBodies
     PCUICTypingEta PCUICTypingEtaInd PCUICClosedTypEta PCUICWeakeningTypEta
     PCUICEtaI5 PCUICWellScopedCumulativityEta PCUICContextConversionEta
     PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp PCUICGuardClosureEta.

From Stdlib Require Import CRelationClasses ssreflect ssrbool.
From Equations Require Import Equations.

(** Hypothesis names for [typingE], as base [PCUICContextConversion.my_rename_hyp]
    gives for [typing]: the copied proofs refer to them. *)
Ltac my_rename_hypE h th :=
  match th with
    | (typingE _ _ ?t _) => fresh "type" t
    | (All_local_env (@typingE _) _ ?G) => fresh "wf" G
    | (All_local_env (@typingE _) _ _) => fresh "wf"
    | (All_local_env _ _ ?G) => fresh "H" G
    | context [typingE _ _ (_ ?t) _] => fresh "IH" t
  end.

#[local] Ltac rename_hyp h ht ::= my_rename_hypE h ht.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Local Ltac intuition_solver ::= auto with *.

(** Base's [pcuic] closes [cumul_decls cumulAlgo_gen Σ Γ Γ' d d] by its reflexivity hints;
    over [JoinE] the reflexivity is [cumul_decls_reflE]. *)
#[local] Hint Extern 4 (All_decls_alpha_pb Cumul (JoinE _ _) _ _) => apply cumul_decls_reflE : pcuic.

Lemma weakening_cumulSpec0E {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : closed_context} {Γ'' : open_context Γ}
  {M N : open_term Γ} n :
  n = #|Γ''| ->
  cumulSpecE Σ Γ M N ->
  cumulSpecE Σ (Γ ,,, Γ'') (lift0 n M) (lift0 n N).
Proof.
  intros e H.
  have hcl : is_closed_context (Γ ,,, Γ'').
  { rewrite on_free_vars_ctx_app (proj2_sig Γ) /=. exact (proj2_sig Γ''). }
  exact (weakening_cumulSpecE0 Cumul Σ Γ Γ'' M N n (wfE_ClosedBodies Σ) e
           (proj2_sig Γ) (proj2_sig M) (proj2_sig N) hcl H).
Defined.

Lemma wt_cum_ws_cumul_pbE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t A B : term} {s} :
  Σ ;;; Γ |-E t : A ->
  Σ ;;; Γ |-E B : tSort s ->
  JoinE Σ Γ Cumul A B ->
  ws_cumul_pbE Cumul Σ Γ A B.
Proof.
  move=> a; move: a (typingE_wf_local a).
  move/type_closedE/(@closedn_on_free_vars xpred0) => clA.
  move/wf_local_closed_contextE => clΓ.
  move/subject_closedE/(@closedn_on_free_vars xpred0) => clB cum.
  now apply into_ws_cumul_pbE.
Qed.

Lemma wt_cum_ws_cumul_ctx_pbE {cf:checker_flags} {Σ:global_env_ext} {wfΣ : wfE Σ} {Γ Δ : context} pb :
  wf_localE Σ Γ ->
  wf_localE Σ Δ ->
  cumul_pb_context (@JoinE cf) pb Σ Γ Δ ->
  ws_cumul_ctx_pbE pb Σ Γ Δ.
Proof.
  move/wf_local_closed_contextE => wfΓ.
  move/wf_local_closed_contextE => wfΔ.
  now eapply into_ws_cumul_ctx_pbE.
Qed.

Lemma All2_conv_over_reflE {cf:checker_flags} {Σ : global_env_ext} {Γ Γ' Δ} :
  All2_fold (All_over (conv_decls (@JoinE cf) Σ) Γ Γ') Δ Δ.
Proof.
  eapply All2_fold_refl. intros ? [na [b|] ty]; constructor; try reflexivity; apply JoinE_refl.
Qed.

Lemma All2_cumul_over_reflE {cf:checker_flags} {Σ : global_env_ext} {Γ Γ' Δ} :
  All2_fold (All_over (cumul_decls (@JoinE cf) Σ) Γ Γ') Δ Δ.
Proof.
  eapply All2_fold_refl. intros ? [na [b|] ty]; constructor; try reflexivity; apply JoinE_refl.
Qed.

Lemma eq_context_cumul_SpecE {cf:checker_flags} Σ pb Γ Δ :
  compare_context Σ pb Γ Δ -> PCUICCumulativitySpec.cumul_pb_context cumulSpecE0 pb Σ Γ Δ.
Proof.
  intros e.
  eapply All2_fold_impl. 1: tea. cbn; intros.
  destruct X.
  - econstructor 1; eauto. eapply eq_term_upto_univ_cumulSpecE; eauto.
  - econstructor 2; eauto.
    all: eapply eq_term_upto_univ_cumulSpecE; eauto.
Defined.

Lemma eq_context_cumul_Spec_relE {cf:checker_flags} Σ Ξ0 Γ Δ :
  compare_context Σ Cumul Γ Δ -> cumul_ctx_rel cumulSpecE0 Σ Ξ0 Γ Δ.
Proof.
  intros e.
  eapply All2_fold_impl. 1: tea. cbn; intros.
  destruct X.
  - econstructor 1; eauto. eapply eq_term_upto_univ_cumulSpecE; eauto.
  - econstructor 2; eauto.
    all: eapply eq_term_upto_univ_cumulSpecE; eauto.
Defined.

(** Base [cumul_context_Algo_Spec] assumes nothing; this assumes [ClosedBodies Σ], the
    premise of [ws_cumul_pbE_forget_spec] (see the file header). *)
Lemma cumul_context_Algo_SpecE {cf:checker_flags} Σ {cb : ClosedBodies Σ} pb Γ' Γ :
  ws_cumul_ctx_pbE pb Σ Γ' Γ -> PCUICCumulativitySpec.cumul_pb_context cumulSpecE0 pb Σ Γ' Γ.
Proof.
  intros e.
  eapply All2_fold_impl. 1: tea. cbn; intros.
  destruct X.
  - econstructor 1; eauto. eapply ws_cumul_pbE_forget_spec; eauto.
  - econstructor 2; eauto.
    all: eapply ws_cumul_pbE_forget_spec; eauto.
Defined.

Lemma mfix_on_ind_context_cumulativityE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Γ' check ok mfix} :
  wf_localE Σ Γ -> wf_localE Σ Γ' ->
  cumul_context (@JoinE cf) Σ Γ' Γ ->
  All (fun d => is_open_term Γ (dtype d)) mfix ->
  mfix_on_ind check (conv_witnessE Σ Γ) ok mfix -> mfix_on_ind check (conv_witnessE Σ Γ') ok mfix.
Proof.
  intros wfΓ wfΓ' hctx hop h.
  pose proof (wfE_ClosedBodies Σ.1) as cbΣ.
  have hlen : #|Γ'| = #|Γ| by apply (All2_fold_length hctx).
  have hcc : ws_cumul_ctx_pbE Cumul Σ Γ' Γ by eapply (wt_cum_ws_cumul_ctx_pbE Cumul).
  refine (mfix_on_ind_All2 _ (fun _ hk => hk) h).
  eapply All_All2_refl, (All_impl hop).
  intros d hopd m [ty [hc [hty hconv]]].
  exists ty. split; [exact hc|]. split.
  - move: hty. now rewrite hlen.
  - eapply into_ws_cumul_pbE_spec in hconv; tea.
    2: now eapply wf_local_closed_contextE.
    eapply (ws_cumul_pbE_ws_cumul_ctx_pb hcc) in hconv.
    exact (ws_cumul_pbE_forget_spec hconv).
Qed.

Lemma context_cumulativity_propE {cf:checker_flags} :
  env_propE
    (fun Σ Γ t T =>
       forall Γ', cumul_context (@JoinE cf) Σ Γ' Γ -> wf_localE Σ Γ' -> Σ ;;; Γ' |-E t : T)
    (fun Σ Γ j =>
       forall Γ', cumul_context (@JoinE cf) Σ Γ' Γ -> wf_localE Σ Γ' ->
       lift_typing0 (fun t T => Σ ;;; Γ' |-E t : T) j)
    (fun Σ Γ =>
    All_local_env (fun Γ j =>
       forall Γ' : context, cumul_context (@JoinE cf) Σ Γ' Γ -> wf_localE Σ Γ' ->
       (lift_typing0 (fun t T => Σ;;; Γ' |-E t : T) j)) Γ).
Proof.
  apply typingE_ind_env; intros Σ wfΣ Γ wfΓ; intros **; rename_all_hyps;
    try solve [econstructor; eauto].

  - apply lift_typing_impl with (1 := X) => ?? [_ IH].
    now apply IH.

  - assumption.

  - pose proof heq_nth_error.
    eapply (All2_fold_nth_r X0) in H as [d' [Hnth [Hrel Hconv]]].
    eapply All_local_env_nth_error in X; tea.
    red in X. specialize (X _ Hrel).
    forward X by now eapply All_local_env_skipn.
    destruct X as (_ & s & Hty & _).
    eapply typeE_Cumul with _ s.
    * econstructor. auto. eauto.
    * rewrite -(firstn_skipn (S n) Γ').
      change (tSort s) with (lift0 (S n) (tSort s)).
      eapply weakening_lengthE. auto.
      rewrite firstn_length_le. eapply nth_error_Some_length in Hnth. lia. auto.
      now rewrite /app_context firstn_skipn.
      assumption.
    * destruct (split_closed_context (S n) (wf_local_closed_contextE X1)) as [Δ [Δ' [eqΔ eqΔ' -> hn]]].
      eapply nth_error_Some_length in Hnth. lia.
      rewrite -eqΔ in Hty, Hrel.
      eapply subject_closedE in Hty.
      eapply (@closedn_on_free_vars xpred0) in Hty.
      assert (is_open_term Δ (decl_type d') × JoinE Σ Δ Cumul (decl_type d') (decl_type decl)) as [H H']. {
        eapply nth_error_closed_context in Hnth. 2: eauto with fvs.
        rewrite -eqΔ in Hnth.
        depelim Hconv; simpl in *.
        all: rewrite -eqΔ in eqt.
        all: now move/andP: Hnth => [].
      }
      eapply (weakening_cumulSpec0E (Γ := Δ) (Γ'' := Δ') (M := exist (decl_type d') H) (N := exist (decl_type decl) Hty)); cbn. lia.
      pose proof (wfE_ClosedBodies Σ.1) as cbΣ.
      exact (ws_cumul_pbE_forget_spec (into_ws_cumul_pbE H' (proj2_sig Δ) H Hty)).
  - constructor; pcuic.
    eapply forall_Γ'0; constructor; pcuic. eapply lift_sorting_forget_univ. now eapply forall_Γ'.
  - econstructor; pcuic.
    eapply forall_Γ'0; repeat (constructor; pcuic).
  - econstructor; pcuic.
    eapply forall_Γ'0; repeat (constructor; pcuic).
  - econstructor; eauto. 2,3: constructor; eauto.
    * eapply IHp0. rewrite /predctx.
      eapply All2_fold_app => //.
      apply All2_cumul_over_reflE.
      eapply context_cumulativity_wf_appE; tea.
    * eapply context_cumulativity_wf_appE; tea.
    * revert X5.
      clear -Γ' X9 X10. induction 1; constructor; eauto. now destruct t0.
    * eapply All2i_impl; tea => i cdecl br. cbv beta.
      set (brctxty := case_branch_type _ _ _ _ _ _ _ _). cbn.
      move=> [] hbctx [] ihbctxty [] [] hbody IHbody [] hbty IHbty.
      intuition eauto; solve_all.
      eapply context_cumulativity_wf_appE; tea.
      eapply IHbody. eapply All2_fold_app => //. apply All2_cumul_over_reflE.
      eauto using context_cumulativity_wf_appE.
      eapply IHbty.
      eapply All2_fold_app => //. apply All2_cumul_over_reflE.
      eapply context_cumulativity_wf_appE; tea.
  - pose proof (wfE_ClosedBodies Σ.1) as cbΣ.
    econstructor.
    all:pcuic.
    * eapply fix_guard_context_cumulativityE; eauto.
      eapply cumul_context_Algo_SpecE; eauto. eapply into_ws_cumul_ctx_pbE; eauto.
      + apply wf_local_closed_contextE; eauto.
      + apply wf_local_closed_contextE; eauto.
    * eapply (All_impl X1).
      intros d Ht. now apply Ht.
    * eapply (All_impl X3).
      intros d Hb. apply Hb.
      1: now apply cumul_context_app_sameE.
      eapply (All_mfix_wfE); auto.
      apply (All_impl X1); simpl.
      intros d' Ht. now apply Ht.
    * match goal with h : wf_fixpointE _ _ _ |- _ => destruct h as (isl & hra & hon) end.
      split; [exact isl|split; [exact hra|]].
      eapply (mfix_on_ind_context_cumulativityE wfΓ X6 X5); tea.
      eapply (All_impl X0) => d hd.
      now eapply isTypeRel_is_open_termE, hd.
  - pose proof (wfE_ClosedBodies Σ.1) as cbΣ.
    econstructor.
    all:pcuic.
    * eapply cofix_guard_context_cumulativityE; eauto.
      eapply cumul_context_Algo_SpecE; eauto. eapply into_ws_cumul_ctx_pbE; eauto.
      + apply wf_local_closed_contextE; eauto.
      + apply wf_local_closed_contextE; eauto.
    * eapply (All_impl X1).
      intros d Ht. now apply Ht.
    * eapply (All_impl X3).
      intros d Hb. apply Hb.
      1: now apply cumul_context_app_sameE.
      eapply (All_mfix_wfE); auto.
      apply (All_impl X1); simpl.
      intros d' Ht. now apply Ht.
    * eapply (mfix_on_ind_context_cumulativityE wfΓ X6 X5); tea.
      eapply (All_impl X0) => d hd.
      now eapply isTypeRel_is_open_termE, hd.
  - econstructor; tea.
    depelim X1; constructor; eauto. solve_all.
  - econstructor; eauto. pose proof (wf_local_closed_contextE wfΓ).
    pose proof (type_closedE (forall_Γ' _ X5 X6)). eapply (@closedn_on_free_vars xpred0) in H0.
    pose proof (subject_closedE (forall_Γ'0 _ X5 X6)). eapply (@closedn_on_free_vars xpred0) in H1.
    pose proof (type_closedE typet). eapply (@closedn_on_free_vars xpred0) in H2.
    pose proof (subject_closedE typeB). eapply (@closedn_on_free_vars xpred0) in H3.
    pose proof (wfE_ClosedBodies Σ.1) as cbΣ.
    eapply ws_cumul_pbE_forget_spec.
    apply into_ws_cumul_pbE; eauto.
    * eapply into_ws_cumul_pbE_spec in X4; eauto.
      apply ws_cumul_pbE_forget in X4. eapply wt_cum_ws_cumul_pbE in X4; tea.
      apply (wt_cum_ws_cumul_ctx_pbE Cumul) in X5; tea.
      eapply (ws_cumul_pbE_ws_cumul_ctx_pb X5) in X4.
      now eapply ws_cumul_pbE_forget in X4.
    * eapply wf_local_closed_contextE; eauto.
Qed.

Lemma closed_context_cumul_cumulE {cf} {Σ} {wfΣ : wfE Σ} {Γ Γ'} :
  ws_cumul_ctx_pbE Cumul Σ Γ Γ' -> cumul_context (@JoinE cf) Σ Γ Γ'.
Proof.
  now move/ws_cumul_ctx_pbE_forget.
Qed.
#[global] Hint Resolve closed_context_cumul_cumulE : pcuic.

Lemma closed_context_conv_convE {cf} {Σ} {wfΣ : wfE Σ} {Γ Γ'} :
  ws_cumul_ctx_pbE Conv Σ Γ Γ' -> conv_context (@JoinE cf) Σ Γ Γ'.
Proof.
  now move/ws_cumul_ctx_pbE_forget.
Qed.
#[global] Hint Resolve closed_context_conv_convE : pcuic.

Lemma closed_context_cumulativityE {cf:checker_flags} {Σ} {wfΣ : wfE Σ.1} Γ {pb t T Γ'} :
  Σ ;;; Γ |-E t : T ->
  wf_localE Σ Γ' ->
  ws_cumul_ctx_pbE pb Σ Γ' Γ ->
  Σ ;;; Γ' |-E t : T.
Proof.
  intros h hΓ' e.
  pose proof (ws_cumul_ctx_pbE_forget e).
  eapply context_cumulativity_propE; eauto.
  destruct pb; tas.
  eapply conv_cumul_contextE in e; tea.
  eapply (ws_cumul_ctx_pbE_forget e).
Qed.

Lemma context_cumulativityE {cf:checker_flags} {Σ} {wfΣ : wfE Σ.1} Γ {t T Γ'} :
  Σ ;;; Γ |-E t : T ->
  wf_localE Σ Γ' ->
  cumul_context (@JoinE cf) Σ Γ' Γ ->
  Σ ;;; Γ' |-E t : T.
Proof.
  intros h hΓ' e.
  eapply context_cumulativity_propE; eauto.
Qed.

#[global] Hint Resolve wf_local_closed_contextE : fvs.

Lemma wf_conv_context_closedE {cf:checker_flags} {Σ} {wfΣ : wfE Σ.1} {Γ Γ'} :
  conv_context (@JoinE cf) Σ Γ Γ' ->
  wf_localE Σ Γ ->
  wf_localE Σ Γ' ->
  ws_cumul_ctx_pbE Conv Σ Γ Γ'.
Proof.
  move=> a wf wf'.
  eapply into_ws_cumul_ctx_pbE; eauto with fvs.
Qed.

Lemma wf_cumul_context_closedE {cf:checker_flags} {Σ} {wfΣ : wfE Σ.1} {Γ Γ'} :
  cumul_context (@JoinE cf) Σ Γ Γ' ->
  wf_localE Σ Γ ->
  wf_localE Σ Γ' ->
  ws_cumul_ctx_pbE Cumul Σ Γ Γ'.
Proof.
  move=> a wf wf'.
  eapply into_ws_cumul_ctx_pbE; eauto with fvs.
Qed.

Lemma context_conversionE {cf:checker_flags} {Σ} {wfΣ : wfE Σ.1} Γ {t T Γ'} :
  Σ ;;; Γ |-E t : T ->
  wf_localE Σ Γ' ->
  conv_context (@JoinE cf) Σ Γ Γ' ->
  Σ ;;; Γ' |-E t : T.
Proof.
  intros h hΓ' e.
  pose proof (wfE_ClosedBodies Σ.1) as cbΣ.
  eapply wf_conv_context_closedE in e; [|exact (typingE_wf_local h)|exact hΓ'].
  apply ws_cumul_ctx_pbE_sym in e.
  now eapply closed_context_cumulativityE in e.
Qed.

(* For ease of application, avoiding to add a call to symmetry *)
Lemma closed_context_conversionE {cf:checker_flags} {Σ} {wfΣ : wfE Σ.1} Γ {t T Γ'} :
  Σ ;;; Γ |-E t : T ->
  wf_localE Σ Γ' ->
  ws_cumul_ctx_pbE Conv Σ Γ Γ' ->
  Σ ;;; Γ' |-E t : T.
Proof.
  intros h hΓ' e.
  pose proof (wfE_ClosedBodies Σ.1) as cbΣ.
  apply ws_cumul_ctx_pbE_sym in e.
  now eapply closed_context_cumulativityE in e.
Qed.
