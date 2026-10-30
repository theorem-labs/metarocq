(* Distributed under the terms of the MIT license. *)

(** * Weak-head and weak call-by-value normalization over [typingE]: the E copy of
      [PCUICNormalization]

  The E twin of every declaration of base [PCUICNormalization] whose statement mentions typing:
  [typing] → [typingE], [wf] → [wfE], [welltyped] → [welltypedE] ([PCUICTypingEta]),
  [NormalizationIn] → [NormalizationInE] ([PCUICSNEta]). [eval], [value], [red], [whnf],
  [closed_red], [ws_term], [axiom_free], [firstorder_ind] and [Acc (cored Σ [])] are unchanged:
  they are untyped, and the E side uses base's. Each name takes the suffix [E].

  Map, base → E: [wh_normalization] → [wh_normalizationE]; [SN_to_WN] → [SN_to_WNE];
  [wcbv_normalization] → [wcbv_normalizationE]; [firstorder_value_irred] →
  [firstorder_value_irredE] (over [PCUICFirstorderEta.firstorder_valueE]);
  [ws_wcbv_standardization] → [ws_wcbv_standardizationE]; [ws_wcbv_standardization_fst] →
  [ws_wcbv_standardization_fstE]; [wcbv_standardization] → [wcbv_standardizationE];
  [wcbv_standardization_fst] → [wcbv_standardization_fstE].

  Imported from base, not copied (they mention no relation and base's compiled forms take no
  environment premise): [ws_empty] ([:79]) and [irred_equal] ([:86], base reduction only).
  [firstorder_value_irred] ([:64]) IS copied, because its statement mentions
  [PCUICFirstorder.firstorder_value], an inductive indexed by base typing
  ([PCUICFirstorder.v:109], whose constructor carries [Σ ;;; Γ |- mkApps (tConstruct i n ui)
  args : mkApps (tInd i u) pandi]); its twin is over [firstorder_valueE].

  ** Proof routes that differ from base (statements do not)

  - [wh_normalizationE] and [wcbv_normalizationE]: base's [PCUICSN.normalization_in] on
    [welltyped] → [PCUICSNEta.normalization_inE] on [welltypedE]. Both conclude the SAME
    [Acc (cored Σ [])], so the induction that follows is base's.
  - [progress_env_prop] → [PCUICProgressEta.progress_env_propE]; [subject_reduction] →
    [PCUICSREta.subject_reductionE]; [subject_reduction_eval] →
    [PCUICClassificationEta.subject_reduction_evalE]; [subject_closed] →
    [PCUICClosedTypEta.subject_closedE]; [subject_is_open_term] →
    [PCUICClosedTypEta.subject_is_open_termE]; [PCUICClassification.value_whnf] →
    [PCUICClassificationEta.value_whnfE]; [PCUICClassification.wcbveval_red] →
    [PCUICClassificationEta.wcbveval_redE]; [PCUICFirstorder.firstorder_value_spec] →
    [firstorder_value_specE]; [PCUICFirstorder.firstorder_value_inds] →
    [firstorder_value_indsE]; [PCUICContextConversion.closed_red_confluence] →
    [PCUICPrincipalityEta.closed_red_confluence_cb].
  - [PCUICWcbvEval.wcbv_red1_eval] takes base [wf Σ], which no η environment has, so this file
    proves [wcbv_red1_evalE] instead: base's statement with [wf] → [wfE], and base's script.
  - [wcbv_red1_red1], [value_final], [red1_mkApps_tConstruct_inv] and [irred_equal] are base's:
    their statements are untyped.

  ** No forecast hypothesis

  This file declares no class and takes none: every file it uses ([PCUICSREta],
  [PCUICClassificationEta], [PCUICProgressEta], [PCUICFirstorderEta]) states its lemmas with no
  forecast premise, so these statements have none either.

  The single field [wh_normalizationE] of the forecast class [CanonForecastCopy20] of the E
  copy of [PCUICCanonicity] is this file's [wh_normalizationE]: the two types accept each
  other, so that class is discharged by this lemma when that copy lands. *)

From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICTyping PCUICEquality PCUICAst PCUICAstUtils
  PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICGeneration PCUICArities
  PCUICWcbvEval PCUICSR PCUICInversion
  PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
  PCUICElimination PCUICSigmaCalculus PCUICContextConversion
  PCUICUnivSubst PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICCumulativity PCUICConfluence
  PCUICInduction PCUICLiftSubst PCUICContexts PCUICSpine
  PCUICConversion PCUICValidity PCUICInductives PCUICConversion
  PCUICInductiveInversion PCUICNormal PCUICSafeLemmata
  PCUICParallelReductionConfluence
  PCUICWcbvEval PCUICClosed PCUICClosedTyp
  PCUICReduction PCUICCSubst PCUICOnFreeVars PCUICWellScopedCumulativity
  PCUICWcbvEval PCUICClassification PCUICProgress PCUICSN PCUICNormalization.
From MetaRocq.PCUIC Require Import PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
  PCUICTypingEtaNotions PCUICClosedBodies PCUICClosedTypEta PCUICWellScopedCumulativityEta
  PCUICSNEta PCUICValidityEta PCUICSREta PCUICClassificationEta PCUICProgressEta
  PCUICFirstorderEta.

From Equations Require Import Equations.

From MetaRocq.PCUIC Require Import PCUICSN PCUICFirstorder.


From MetaRocq.PCUIC Require PCUICPrincipalityEta.

(** Route lemma, no base twin in [PCUICNormalization]: base
    [PCUICWcbvEval.wcbv_red1_eval] ([:1399]) takes [wf Σ], which no η environment has. Base
    reads [wf] only through [declared_constant_to_gen], [declared_constructor_to_gen] and
    [declared_minductive_ind_npars], all three stated for an arbitrary [on_global_env], so the
    same script runs with [wfE]. The statement is base's with [wf] → [wfE]. *)
Lemma wcbv_red1_evalE {cf : checker_flags} {Σ : global_env_ext} t t' v : wfE Σ ->
  closed t ->
  Σ ⊢ t ⇝ᵥ t' -> MetaRocq.PCUIC.PCUICWcbvEval.eval Σ t' v -> MetaRocq.PCUIC.PCUICWcbvEval.eval Σ t v.
Proof.
  intros wfΣ Hty Hred Heval.
  induction Hred in Heval, v, Hty |- *; eauto with wcbv.
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. 1-3,6:now econstructor; eauto with wcbv.
    eapply eval_construct; tea. eauto. eapply eval_app_cong; eauto with wcbv.
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. 1-3,6: now econstructor; eauto with wcbv.
    eapply eval_construct; tea. eauto. eapply eval_app_cong; eauto with wcbv.
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. all: now econstructor; eauto with wcbv.
  - unshelve eapply declared_constant_to_gen in isdecl; eauto.
    inversion Heval; subst. all:cbn in Hty; solve_all. all: try now econstructor; eauto with wcbv.
  - inversion Heval; subst. all:cbn in Hty; solve_all. all: try now econstructor; eauto with wcbv.
  - eapply eval_iota. eapply eval_mkApps_Construct; tea.
    unshelve eapply declared_constructor_to_gen; eauto.
    now econstructor. unfold MetaRocq.PCUIC.PCUICWcbvEval.cstr_arity. rewrite e0.
    rewrite (declared_minductive_ind_nparsE (MetaRocq.Utils.MRProd.proj1 (MetaRocq.Utils.MRProd.proj1 d))).
    now rewrite -(declared_minductive_ind_nparsE (MetaRocq.Utils.MRProd.proj1 (MetaRocq.Utils.MRProd.proj1 d))) /MetaRocq.PCUIC.PCUICWcbvEval.cstr_arity.
    all:tea. eapply All_All2_refl. solve_all. now eapply value_final.
    unshelve eapply declared_constructor_to_gen; eauto.
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. all: now econstructor; eauto with wcbv.
  - all:cbn in Hty; solve_all. eapply eval_proj; tea.
    eapply value_final. eapply value_app; auto. econstructor; tea. eapply d.
    rewrite e; lia.
  - eapply eval_fix; eauto.
    + eapply value_final. eapply value_app; auto. econstructor.
      rewrite <- closed_unfold_fix_cunfold_eq, e. reflexivity. 2:eauto.
      cbn in Hty. rewrite MetaRocq.PCUIC.PCUICClassification.closedn_mkApps in Hty. solve_all.
    + eapply value_final; eauto.
    + rewrite <- closed_unfold_fix_cunfold_eq, e. reflexivity.
      cbn in Hty. rewrite MetaRocq.PCUIC.PCUICClassification.closedn_mkApps in Hty. solve_all.
      Unshelve. all: now econstructor.
  - destruct p as [[] ?]. eapply eval_cofix_proj; tea.
    eapply value_final, value_app. now constructor. auto.
  - eapply eval_cofix_case; tea.
    eapply value_final, value_app. now constructor. auto.
  - cbn in Hty. rtoProp; intuition auto.
    depelim Heval; eapply eval_prim.
    depelim e.
    + subst a0 a'; cbn in *. destruct a; eapply evalPrimArray; cbn in *; eauto.
    + destruct a; eapply evalPrimArray; cbn in *; eauto.
  - cbn in Hty. rtoProp; intuition auto.
    depelim Heval; eapply eval_prim.
    depelim e0.
    + subst a1 a'; cbn in *. destruct a; eapply evalPrimArray; cbn in *; eauto.
      eapply All2_app_inv_l in ev as [r1 [r2 [? []]]]. subst v'0.
      depelim a1. specialize (IHHred y). forward IHHred. toAll. eapply All_nth_error in H; tea; eauto.
      rewrite -(firstn_skipn n array_value). eapply All2_app; eauto.
      move: (skipn_nth_error array_value n). rewrite e => ->.
      constructor; eauto.
    + now cbn in i.
Qed.

(** Base [wh_normalization] ([:24]). This is the statement of the field [wh_normalizationE] of
    the forecast class [CanonForecastCopy20] of the E copy of [PCUICCanonicity]. *)
Lemma wh_normalizationE {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationInE Σ} {t} : wfE Σ -> axiom_free Σ ->
{A & Σ ;;; [] |-E t : A}  -> { v & whnf RedFlags.default Σ [] v * red Σ [] t v}.
Proof.
intros Hwf Hax [A HA].
assert (welltypedE Σ [] t) as Hwt. { econstructor; eauto. }
eapply PCUICSNEta.normalization_inE in Hwt as HSN; eauto. clear Hwt.
induction HSN as [t H IH].
edestruct progress_env_propE as [_ [_ [[t' Ht'] | Hval]]]; eauto.
- eapply wcbv_red1_red1 in Ht' as Hred. 2:{ change 0 with (#|@Corelib.Init.Datatypes.nil MetaRocq.PCUIC.PCUICAst.PCUICEnvironment.context_decl|). eapply subject_closedE. eauto. }
  edestruct IH as [v Hv]. econstructor. eauto.
  eapply subject_reductionE; eauto.
  exists v. sq. destruct Hv. split; eauto. eapply red_step; eauto.
- exists t. sq. split; eauto. eapply value_whnfE; eauto.
  eapply @subject_closedE with (Γ := []); eauto.
Defined.

(** Base [SN_to_WN] ([:40]). *)
Lemma SN_to_WNE {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationInE Σ} {A t} : wfE Σ -> axiom_free Σ ->
  Acc (cored Σ []) t -> Σ ;;; [] |-E t : A -> { v & MetaRocq.PCUIC.PCUICWcbvEval.eval Σ t v}.
  intros Hwf Hax HSN HA.
  induction HSN as [t H IH].
  edestruct progress_env_propE as [_ [_ [[t' Ht'] | Hval]]]; eauto.
  - eapply wcbv_red1_red1 in Ht' as Hred. 2:{ change 0 with (#|@Corelib.Init.Datatypes.nil MetaRocq.PCUIC.PCUICAst.PCUICEnvironment.context_decl|). eapply subject_closedE. eauto. }
    edestruct IH as [v Hv]. econstructor. eauto.
    eapply subject_reductionE; eauto.
    exists v. sq. eapply (wcbv_red1_evalE t t' v Hwf); eauto.
    exact (@subject_closedE _ _ _ [] _ _ HA).
  - exists t. sq. eapply value_final; eauto.
Qed.

(** Base [wcbv_normalization] ([:53]). *)
Lemma wcbv_normalizationE {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationInE Σ} {A t} : wfE Σ -> axiom_free Σ ->
  Σ ;;; [] |-E t : A -> { v & MetaRocq.PCUIC.PCUICWcbvEval.eval Σ t v}.
Proof.
  intros Hwf Hax HA.
  assert (welltypedE Σ [] t) as Hwt. { econstructor; eauto. }
  eapply PCUICSNEta.normalization_inE in Hwt as HSN; eauto. clear Hwt.
  eapply SN_to_WNE; eauto.
Qed.

(** Base [firstorder_value_irred] ([:64]). *)
Lemma firstorder_value_irredE {cf:checker_flags} Σ t t' :
  firstorder_valueE Σ [] t ->
  PCUICReduction.red1 Σ [] t t' -> False.
Proof.
  intros H.
  revert t'. pattern t. revert t H.
  eapply firstorder_value_indsE.
  intros i n ui u args pandi Hty Hargs IH Hprop t' Hred.
  eapply red1_mkApps_tConstruct_inv in Hred as (x & -> & Hone).
  solve_all.
  clear - IH Hone. induction IH as [ | ? ? []] in x, Hone |- *.
  - invs Hone.
  - invs Hone; eauto.
Qed.

(** Base [ws_wcbv_standardization] ([:99]). *)
Lemma ws_wcbv_standardizationE {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationInE Σ} {T} {t v : ws_term (fun _ => false)} : wfE Σ -> axiom_free Σ ->
  Σ ;;; [] |-E t : T ->
  closed_red Σ [] t v ->
  ¬ { t' & Σ ;;; [] |- v ⇝ t'} ->
  {v' & MetaRocq.PCUIC.PCUICWcbvEval.eval Σ t v' * (Σ ;;; [] ⊢ v' ⇝ v)}.
Proof.
  intros Hwf Hax Hty Hred Hirred.
  destruct (@wcbv_normalizationE _ no Σ normalization T t) as (v' & Hv'); eauto.
  assert (Σ;;; [] |- t ⇝* v') as Hred' by now eapply (wcbveval_redE _ T).
  eapply (PCUICPrincipalityEta.closed_red_confluence_cb
            (cbΣ := wfE_ClosedBodies Σ (wfΣ := Hwf))) in Hred as Hred_.
  destruct Hred_ as (v'' & H1 & H2).
  2:{ econstructor; eauto. eapply subject_is_open_termE. eauto. }
  destruct v as [v Hv].
  assert (v = v'') as <- by (eapply irred_equal; eauto).
  exists v'; split; eauto.
Qed.

(** Base [ws_wcbv_standardization_fst] ([:115]). *)
Lemma ws_wcbv_standardization_fstE {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationInE Σ} {i u args mind} {t v : ws_term (fun _ => false)} : wfE Σ -> axiom_free Σ ->
  Σ ;;; [] |-E t : mkApps (tInd i u) args ->
  lookup_env Σ (i.(inductive_mind)) = Some (InductiveDecl mind) ->
  @firstorder_ind Σ (firstorder_env Σ) i ->
  closed_red Σ [] t v ->
  ¬ { t' & Σ ;;; [] |- v ⇝ t'} ->
  MetaRocq.PCUIC.PCUICWcbvEval.eval Σ t v.
Proof.
  intros Hwf Hax Hty Hdecl Hfo Hred Hirred.
  destruct (ws_wcbv_standardizationE Hwf Hax Hty Hred Hirred) as [v' [H H']].
  assert (firstorder_valueE Σ [] v'). {
    eapply (firstorder_value_specE Σ v' i u args Hwf localenv_nil).
    - eapply subject_reduction_evalE; eauto.
    - eapply eval_to_value. eauto.
    - exact Hfo.
  }
  enough (v' = v) as -> by eauto.
  eapply irred_equal. eauto.
  intros. eapply firstorder_value_irredE; eauto.
  Unshelve.
Qed.

(** Base [wcbv_standardization] ([:136]). *)
Lemma wcbv_standardizationE {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationInE Σ} {T t v : term} : wfE Σ -> axiom_free Σ ->
  Σ ;;; [] |-E t : T ->
  Σ ;;; [] |- t ⇝ v ->
  ¬ { t' & Σ ;;; [] |- v ⇝ t'} ->
  {v' & MetaRocq.PCUIC.PCUICWcbvEval.eval Σ t v' * (Σ ;;; [] ⊢ v' ⇝ v)}.
Proof.
  intros Hwf Hax Hty Hred Hirred.
  unshelve eapply @ws_wcbv_standardizationE with (T := T) (t := (exist t _)) (v := (exist v _)).
  all: sq; eauto; cbn.
  1-2: shelve.
  econstructor; eauto.
  eapply subject_is_open_termE. eauto.
  Unshelve.
  all: rewrite -closed_on_free_vars_none.
  - now eapply subject_closedE in Hty.
  - eapply @subject_closedE with (Γ := []); eauto.
    eapply subject_reductionE; eauto.
Qed.

(** Base [wcbv_standardization_fst] ([:155]). *)
Lemma wcbv_standardization_fstE {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationInE Σ} {i u args mind} {t v : term} : wfE Σ -> axiom_free Σ ->
  Σ ;;; [] |-E t : mkApps (tInd i u) args ->
  lookup_env Σ (i.(inductive_mind)) = Some (InductiveDecl mind) ->
  @firstorder_ind Σ (firstorder_env Σ) i ->
  red Σ [] t v ->
  ¬ { t' & Σ ;;; [] |- v ⇝ t'} ->
  MetaRocq.PCUIC.PCUICWcbvEval.eval Σ t v.
Proof.
  intros Hwf Hax Hty Hdecl Hfo Hred Hirred.
  unshelve eapply @ws_wcbv_standardization_fstE with (t := (exist t _)) (v := (exist v _)).
  all: sq; eauto; cbn.
  1-2: shelve.
  econstructor; eauto.
  eapply subject_is_open_termE. eauto.
  Unshelve.
  all: rewrite -closed_on_free_vars_none.
  - now eapply subject_closedE in Hty.
  - eapply @subject_closedE with (Γ := []); eauto.
    eapply subject_reductionE; eauto.
Qed.

