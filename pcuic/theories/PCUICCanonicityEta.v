(* Distributed under the terms of the MIT license. *)

(** * Canonicity over [typingE] (row T6): the E copy of [PCUICCanonicity]

  The E twin of base [pcuic_canonicity] ([PCUICCanonicity.v:20]): [typing] → [typingE], [wf] →
  [wfE], [NormalizationIn] → [NormalizationInE] ([PCUICSNEta]), the conversion [Σ ;;; [] |- t =s
  t'] ([convSpec]) → [convSpecE Σ [] t t']. Nothing else changes; the name takes the suffix [E].

  Proof route: base's, with [PCUICNormalizationEta.wh_normalizationE] (copy 20, ArityLane) in
  place of base [wh_normalization] ([PCUICNormalization.v:24]), [subject_reductionE],
  [PCUICClassificationEta.whnf_classificationE], and [ws_cumul_pbE_forget_spec] in place of base
  [cumulAlgo_cumulSpec].

  This file takes no forecast class. Until copy 20 (bfe54de2), it declared the class
  [CanonForecastCopy20], whose single field was the statement of [wh_normalizationE]; the class
  was deleted after a compiled-form identity check of that field against copy 20's lemma,
  in both directions. T1's [SRForecastCopy18] was a second section class until copy 18b landed
  (frac/eta 3e6b422d); it was deleted after the same check of each field.

  ** BET-339 (integ-all8 [1a92b56c]; F0 forecast [wip/eta-meta-f0-land45-2026-10-30])

  Base integ-all8 restates [pcuic_canonicity]: a closed well-typed term of an inductive type is
  convertible to a term whose head is a constructor or a cofixpoint, OR to a case blocked on a
  cofixpoint ([+ stuck_cofix_case t'], base [PCUICClassification]). [pcuic_canonicityE] takes the
  same conclusion, only the relation renamed; its proof is unchanged, because
  [whnf_classificationE] (restated the same way in the LAND3 forecast) gives the sum. *)

From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICTyping PCUICEquality PCUICAst PCUICAstUtils
  PCUICReduction PCUICOnFreeVars PCUICWcbvEval PCUICNormal PCUICSafeLemmata PCUICSN
  PCUICConversion PCUICViews PCUICClassification PCUICCanonicity.
From MetaRocq.PCUIC Require Import PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
  PCUICTypingEtaNotions PCUICClosedBodies PCUICClosedTypEta PCUICWellScopedCumulativityEta
  PCUICSNEta PCUICValidityEta PCUICSREta PCUICClassificationEta.
From MetaRocq.PCUIC Require PCUICNormalizationEta.

(** Base [pcuic_canonicity] (integ-all8 [:22]): a closed well-typed term of an inductive type is
    convertible to a term whose head is a constructor or a cofixpoint, unless it is blocked by a
    case on a cofixpoint. *)
Lemma pcuic_canonicityE {cf:checker_flags} {nor : normalizing_flags} Σ {normalization_in: NormalizationInE Σ} t i u args :
     axiom_free Σ -> wfE Σ ->
     Σ ;;; [] |-E t : mkApps (tInd i u) args ->
     { t':term & (Σ ;;; [] |-E t' : mkApps (tInd i u) args) * (convSpecE Σ [] t t') *
       (construct_cofix_discr (head t') + stuck_cofix_case t')}.
Proof.
  intros axΣ wfΣ typ_ind. pose proof (_ ; typ_ind) as wt.
  have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).
  eapply PCUICNormalizationEta.wh_normalizationE in wt ; eauto.
  destruct wt as [t' [Hnormal Ht']].
  pose proof (Ht'_ := Ht').
  pose proof (typ_ind' := typ_ind).
  eapply subject_reductionE in typ_ind; eauto.
  eapply whnf_classificationE with (args := args) in typ_ind as ctor; auto.
  exists t'; repeat split; eauto.
  eapply ws_cumul_pbE_forget_spec.
  eapply red_ws_cumul_pbE. split; eauto.
  now eapply subject_is_open_termE.
Qed.
