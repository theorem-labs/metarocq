(* Distributed under the terms of the MIT license. *)

(** * Canonicity over [typingE] (row T6): the E copy of [PCUICCanonicity]

  The E twin of base [pcuic_canonicity] ([PCUICCanonicity.v:20]): [typing] → [typingE], [wf] →
  [wfE], [NormalizationIn] → [NormalizationInE] ([PCUICSNEta]), the conversion [Σ ;;; [] |- t =s
  t'] ([convSpec]) → [convSpecE Σ [] t t']. Nothing else changes; the name takes the suffix [E].

  Proof route: base's, with [subject_reductionE], [PCUICClassificationEta.whnf_classificationE],
  and [ws_cumul_pbE_forget_spec] in place of base [cumulAlgo_cumulSpec].

  ** The forecast block

  Section premises: the classes of [PCUICClassificationEta] (T2a's [ValForecastCopy16], T1's
  [SRForecastCopy16]/[SRForecastCopy18], [ClassifForecastCopy16]), imported, and one new class,
  [CanonForecastCopy20]: base [wh_normalization] ([PCUICNormalization.v:24]), whose E copy is
  copy 20 ([PCUICNormalizationEta], ArityLane), built on [PCUICProgressEta]. *)

From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICTyping PCUICEquality PCUICAst PCUICAstUtils
  PCUICReduction PCUICOnFreeVars PCUICWcbvEval PCUICNormal PCUICSafeLemmata PCUICSN
  PCUICConversion PCUICViews PCUICClassification PCUICCanonicity.
From MetaRocq.PCUIC Require Import PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
  PCUICTypingEtaNotions PCUICClosedBodies PCUICClosedTypEta PCUICWellScopedCumulativityEta
  PCUICSNEta PCUICValidityEta PCUICSREta PCUICClassificationEta.

(** ** FORECAST BLOCK *)

Local Set Warnings "-unexpected-implicit-declaration".

(* FORECAST-ONLY: proved by copy 20 (PCUICNormalizationEta, ArityLane; needs PCUICProgressEta);
   delete when it lands. *)
Class CanonForecastCopy20 := {
  (* PCUICNormalization.v:24 wh_normalization; base twin's statement with the relations
     renamed. *)
  wh_normalizationE :
    forall {cf : checker_flags} {no : normalizing_flags} {Σ : global_env_ext}
      {normalization : NormalizationInE Σ} {t : term},
    wfE Σ -> axiom_free Σ ->
    {A & Σ ;;; [] |-E t : A} -> { v & whnf RedFlags.default Σ [] v * red Σ [] t v}
}.

Local Set Warnings "unexpected-implicit-declaration".

(** ** End of the FORECAST BLOCK *)

Section CanonicityEta.

(* FORECAST-ONLY: the classes of [PCUICClassificationEta] and this file's one; delete each when
   its copy lands. *)
Context {V16 : ValForecastCopy16} {F16 : SRForecastCopy16} {F18 : SRForecastCopy18}
  {C16 : ClassifForecastCopy16} {N20 : CanonForecastCopy20}.

(** Base [pcuic_canonicity] ([:20]). *)
Lemma pcuic_canonicityE {cf:checker_flags} {nor : normalizing_flags} Σ {normalization_in: NormalizationInE Σ} t i u args :
     axiom_free Σ -> wfE Σ ->
     Σ ;;; [] |-E t : mkApps (tInd i u) args ->
     { t':term & (Σ ;;; [] |-E t' : mkApps (tInd i u) args) * (convSpecE Σ [] t t') * construct_cofix_discr (head t')}.
Proof.
  intros axΣ wfΣ typ_ind. pose proof (_ ; typ_ind) as wt.
  have cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).
  eapply wh_normalizationE in wt ; eauto.
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

End CanonicityEta.
