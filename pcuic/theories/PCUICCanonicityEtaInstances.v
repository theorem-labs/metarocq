(* Distributed under the terms of the MIT license. *)

(** * Satisfying instance of [PCUICCanonicityEta.pcuic_canonicityE] (row T6)

  **Section variables.** The forecast classes of [PCUICCanonicityEta] (the four of
  [PCUICClassificationEta] and [CanonForecastCopy20], base [wh_normalization] over E) and the
  normalization hypothesis [NormalizationInE si_Σ]. [NormalizationInE] is base's
  [NormalizationIn] over [welltypedE] ([PCUICSNEta]): a premise unprovable by design (strong
  normalization), inherited from base's [pcuic_canonicity], which takes [NormalizationIn Σ]; it
  is not a forecast and is never discharged.

  **Non-degeneracy.** The instance runs on [c (∀P:Prop. P) : I (∀P:Prop. P)] in [si_Σ]
  ([sri_cF_typed]), with [axiom_free si_Σ] ([cli_axiom_free]) and [wfE si_Σ] proved. The
  normal form, its conversion with [t] and the constructor head come from the lemma; the
  normalization they rest on is the section variable above. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICSN PCUICClassification
     PCUICTypingEta PCUICCumulativitySpecEtaClosureInstances PCUICInversionEtaInstances
     PCUICSREtaInstances PCUICSNEta PCUICValidityEta PCUICSREta PCUICClassificationEta
     PCUICClassificationEtaInstances PCUICCanonicityEta.

#[local] Existing Instance default_checker_flags.

Section CanonicityEtaInstances.

(* FORECAST-ONLY: the classes of [PCUICCanonicityEta]; delete each when its copy lands. *)
Context {F18 : SRForecastCopy18} {N20 : CanonForecastCopy20}.

(* Base's normalization premise (by design, never discharged). *)
Context {nor : normalizing_flags} {nin : NormalizationInE si_Σ}.

Definition pcuic_canonicityE_inst :=
  pcuic_canonicityE si_Σ sri_cF si_ind [] [iv_False] cli_axiom_free si_wfE sri_cF_typed.

End CanonicityEtaInstances.
