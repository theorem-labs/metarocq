(* Distributed under the terms of the MIT license. *)

(** * Consistency over [typingE] (row T9): the E copy of [PCUICConsistency]

  The E twin of base [pcuic_consistent] ([PCUICConsistency.v:40]): [typing] → [typingE],
  [wf_ext] → [wf_extE], [NormalizationIn] → [NormalizationInE] ([PCUICSNEta]). Nothing else
  changes; the name takes the suffix [E]. Base's [False_oib] and [False_mib] mention no
  relation and are used from base ([PCUICConsistency] is imported).

  Proof route: base's, with [pcuic_canonicityE] ([PCUICCanonicityEta]),
  [PCUICValidityEta.inversion_mkAppsE] (written qualified, as base writes
  [PCUICValidity.inversion_mkApps]: [PCUICProgressEta] declares a second [inversion_mkAppsE]),
  [inversion_ConstructE] ([PCUICInversionEta]), [Construct_Ind_ind_eqE] (copy 18b,
  [PCUICInductiveInversionEtaB], written qualified) and [typing_cofix_coindE] ([PCUICClassificationEta]). Base
  destructs [on_declared_constructor d] (:59-62) and clears every component it produces at :64
  ([clear -Hdecl d wfΣ]); the E proof does not take it.

  ** Premises

  - [NormalizationInE Σ] is base's [NormalizationIn Σ] premise over [welltypedE]: a PREMISE,
    as in base, not a forecast. Nothing proves it (strong normalization; [PCUICSNEta]'s header).
  - No forecast class. [PCUICCanonicityEta]'s [CanonForecastCopy20] (base [wh_normalization],
    copy 20) was a section class here until copy 20 (bfe54de2) and the class was
    deleted; T1's [SRForecastCopy18] was a second one until copy 18b landed (frac/eta 3e6b422d)
    and was deleted. This file adds no class.
    Instances: [PCUICConsistencyEtaInstances]. *)

From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICTyping PCUICEquality PCUICAst PCUICAstUtils
  PCUICReduction PCUICWcbvEval PCUICNormal PCUICSN PCUICViews PCUICClassification PCUICCanonicity
  PCUICConsistency.
From MetaRocq.PCUIC Require Import PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
  PCUICTypingEtaNotions PCUICWellScopedCumulativityEta PCUICSNEta PCUICInversionEta
  PCUICValidityEta PCUICSREta PCUICClassificationEta PCUICCanonicityEta.
From MetaRocq.PCUIC Require PCUICInductiveInversionEtaB.

From Equations Require Import Equations.

(** Base [pcuic_consistent] ([:40]). *)
Theorem pcuic_consistentE {cf:checker_flags} {nor : normalizing_flags} Σ
  {normalization_in: NormalizationInE Σ} t False_pcuic :
  declared_inductive Σ False_pcuic False_mib False_oib ->
  wf_extE Σ -> axiom_free Σ ->
  Σ ;;; [] |-E t : tInd False_pcuic []  -> False.
Proof.
  intros Hdecl wfΣ axΣ typ_false.
  have wfΣ' : wfE Σ := wfΣ.1.
  destruct (pcuic_canonicityE Σ t False_pcuic [] []) as [t' [[typ_false' eqtt'] ctor]]; eauto.
  destruct Hdecl as [Hdecl Hidecl].
  destruct False_pcuic as [kn n]. destruct n; cbn in *; [| now rewrite nth_error_nil in Hidecl].
  rewrite /construct_cofix_discr /head in ctor.
  destruct decompose_app eqn:decomp.
  apply decompose_app_inv in decomp; subst.
  destruct t0; try discriminate ctor.
  - apply (PCUICValidityEta.inversion_mkAppsE (wfΣ := wfΣ')) in typ_false' as H.
    destruct H as (?&typ_ctor&_).
    apply inversion_ConstructE in typ_ctor as (?&?&?&?&?&?&?); auto.
    eapply PCUICInductiveInversionEtaB.Construct_Ind_ind_eqE with (args' := []) in typ_false'; tea.
    destruct typ_false' as (((((->&_)&_)&_)&_)&_).
    clear -Hdecl d wfΣ. destruct wfΣ.
    cbn in *.
    destruct d as ((?&?)&?).
    unshelve eapply declared_minductive_to_gen in Hdecl; eauto.
    unshelve eapply declared_minductive_to_gen in H; eauto.
    red in H, Hdecl. cbn in *. rewrite Hdecl in H; noconf H.
    cbn in H0. noconf H0.
    cbn in H1. rewrite nth_error_nil in H1.
    discriminate.
  - eapply @typing_cofix_coindE with (indargs := []) in typ_false'; eauto.
    unfold check_recursivity_kind in typ_false'. destruct wfΣ.
    unshelve eapply declared_minductive_to_gen in Hdecl; eauto.
    red in Hdecl. rewrite Hdecl in typ_false'.
    cbn in typ_false'. inversion typ_false'.
Qed.
