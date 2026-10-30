(* Distributed under the terms of the MIT license. *)

(** * Weak-head and weak call-by-value normalization over [typingE] (row T6): the E copy of
      [PCUICNormalization]

  The E twin of every declaration of base [PCUICNormalization] whose statement mentions typing:
  [typing] → [typingE], [wf] → [wfE], [welltyped] → [welltypedE] ([PCUICTypingEta]),
  [NormalizationIn] → [NormalizationInE] ([PCUICSNEta]). [eval], [value], [red], [whnf],
  [closed_red], [ws_term], [axiom_free], [firstorder_ind] and [Acc (cored Σ [])] are unchanged:
  they are untyped, and the E side uses base's. Each name takes the suffix [E] (plan
  [t0-plan.md] §2, D1).

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
    [PCUICSREta.subject_reductionE]; [subject_closed] → [PCUICClosedTypEta.subject_closedE];
    [subject_is_open_term] → [PCUICClosedTypEta.subject_is_open_termE];
    [PCUICClassification.value_whnf] → [PCUICClassificationEta.value_whnfE].
  - [wcbv_red1_red1], [wcbv_red1_eval], [value_final], [closed_red_confluence] and
    [irred_equal] are base's: their statements are untyped.

  ** The forecast block

  This file declares no class. Its section takes the two forecast classes that the files it
  uses still have — T1's [SRForecastCopy18] ([PCUICSREta], through [PCUICClassificationEta],
  [PCUICProgressEta] and [PCUICFirstorderEta]) and [ProgForecastCopy18] ([PCUICProgressEta])
  — as section premises, so that each disappears from these statements when its copy lands
  and the class is deleted. Copy 16 has landed, so [ValForecastCopy16], [SRForecastCopy16] and
  [ClassifForecastCopy16] no longer exist.

  [PCUICCanonicityEta.v] carries [wh_normalizationE] as the single field of its forecast class
  [CanonForecastCopy20]; the lemma proved here is that field's statement, and the two
  ascriptions that check it both ways are in [PCUICTypingEtaCopy20Instances.v]. *)

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

Section NormalizationEta.

(* FORECAST-ONLY: one premise per class of the files this one uses; delete each when its copy
   lands. *)
Context {F18 : SRForecastCopy18} {P18 : ProgForecastCopy18}.

(** Base [wh_normalization] ([:24]). The statement is the field [wh_normalizationE] of
    [PCUICCanonicityEta.CanonForecastCopy20]. *)
Lemma wh_normalizationE {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationInE Σ} {t} : wfE Σ -> axiom_free Σ ->
{A & Σ ;;; [] |-E t : A}  -> { v & whnf RedFlags.default Σ [] v * red Σ [] t v}.
Proof.
intros Hwf Hax [A HA].
assert (welltypedE Σ [] t) as Hwt. { econstructor; eauto. }
eapply PCUICSNEta.normalization_inE in Hwt as HSN; eauto. clear Hwt.
induction HSN as [t H IH].
edestruct progress_env_propE as [_ [_ [[t' Ht'] | Hval]]]; eauto.
- eapply wcbv_red1_red1 in Ht' as Hred. 2:{ change 0 with (#|@nil context_decl|). eapply subject_closedE. eauto. }
  edestruct IH as [v Hv]. econstructor. eauto.
  eapply subject_reductionE; eauto.
  exists v. sq. destruct Hv. split; eauto. eapply red_step; eauto.
- exists t. sq. split; eauto. eapply value_whnfE; eauto.
  eapply @subject_closedE with (Γ := []); eauto.
Defined.

(** Base [SN_to_WN] ([:40]). *)
Lemma SN_to_WNE {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationInE Σ} {A t} : wfE Σ -> axiom_free Σ ->
  Acc (cored Σ []) t -> Σ ;;; [] |-E t : A -> { v & eval Σ t v}.
  intros Hwf Hax HSN HA.
  induction HSN as [t H IH].
  edestruct progress_env_propE as [_ [_ [[t' Ht'] | Hval]]]; eauto.
  - eapply wcbv_red1_red1 in Ht' as Hred. 2:{ change 0 with (#|@nil context_decl|). eapply subject_closedE. eauto. }
    edestruct IH as [v Hv]. econstructor. eauto.
    eapply subject_reductionE; eauto.
    exists v. sq. eapply wcbv_red1_eval; eauto.
    now eapply subject_closedE in HA.
  - exists t. sq. eapply value_final; eauto.
Qed.

(** Base [wcbv_normalization] ([:53]). *)
Lemma wcbv_normalizationE {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationInE Σ} {A t} : wfE Σ -> axiom_free Σ ->
  Σ ;;; [] |-E t : A -> { v & eval Σ t v}.
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
  {v' & eval Σ t v' * (Σ ;;; [] ⊢ v' ⇝ v)}.
Proof.
  intros Hwf Hax Hty Hred Hirred.
  destruct (@wcbv_normalizationE _ no Σ normalization T t) as (v' & Hv'); eauto.
  assert (Σ;;; [] |- t ⇝* v') as Hred' by now eapply wcbveval_red.
  eapply closed_red_confluence in Hred as Hred_. destruct Hred_ as (v'' & H1 & H2).
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
  eval Σ t v.
Proof.
  intros Hwf Hax Hty Hdecl Hfo Hred Hirred.
  destruct (ws_wcbv_standardizationE Hwf Hax Hty Hred Hirred) as [v' [H H']].
  assert (firstorder_valueE Σ [] v'). {
    eapply firstorder_value_specE; eauto. exact localenv_nil.
    eapply subject_reduction_evalE; eauto.
    eapply eval_to_value. eauto.
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
  {v' & eval Σ t v' * (Σ ;;; [] ⊢ v' ⇝ v)}.
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
  eval Σ t v.
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

End NormalizationEta.
