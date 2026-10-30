(* Distributed under the terms of the MIT license. *)

(** * Satisfying instance of [PCUICCanonicityEta.pcuic_canonicityE] (row T6)

  **Section variables.** The normalization hypothesis [NormalizationInE si_Σ] only.
  [NormalizationInE] is base's [NormalizationIn] over [welltypedE] ([PCUICSNEta]): a premise
  unprovable by design (strong normalization), inherited from base's [pcuic_canonicity], which
  takes [NormalizationIn Σ]; it is not a forecast and is never discharged. (The forecast class
  [CanonForecastCopy20] was a second section variable until copy 20 (bfe54de2) and the class was
  deleted; T1's [SRForecastCopy18] was deleted when copy 18b landed.)

  **Non-degeneracy.** The instance runs on the fixpoint application
  [t = mkApps (tFix iv_mfix 0) [c (∀P:Prop. P)] : I (∀P:Prop. P)] in [si_Σ]
  ([PCUICSREtaInstances.sri_fix_app_typed]), with [axiom_free si_Σ] ([cli_axiom_free]) and
  [wfE si_Σ] proved. [t] is not a canonical form: its head is a [tFix], neither a constructor nor
  a cofixpoint, so the lemma must reduce it (one fixpoint unfolding and one β step,
  [PCUICSREtaInstances.sri_fix_red]). [pcuic_canonicityE_inst_moves] proves that the [t'] the
  lemma returns is not [t]. The normalization that the reduction rests on is the section variable
  above. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICSN PCUICClassification
     PCUICTypingEta PCUICCumulativitySpecEtaClosureInstances PCUICInversionEtaInstances
     PCUICSREtaInstances PCUICSNEta PCUICValidityEta PCUICSREta PCUICClassificationEta
     PCUICClassificationEtaInstances PCUICCanonicityEta.

#[local] Existing Instance default_checker_flags.

Section CanonicityEtaInstances.

(* Base's normalization premise (by design, never discharged). *)
Context {nor : normalizing_flags} {nin : NormalizationInE si_Σ}.

(** [t] is a fixpoint application, not a constructor application, so [t' ≠ t]
    ([pcuic_canonicityE_inst_moves]). *)
Definition pcuic_canonicityE_inst :=
  pcuic_canonicityE si_Σ (mkApps (tFix iv_mfix 0) [sri_cF]) si_ind [] [iv_False] cli_axiom_free
    si_wfE sri_fix_app_typed.

(** The canonical form returned differs from [t]: its head is a constructor or a cofixpoint, or
    it is a case blocked on a cofixpoint (BET-339); [t]'s head is [tFix iv_mfix 0], and [t] is
    not blocked, because the recursive argument [c (∀P:Prop. P)] is a constructor application. *)
Lemma pcuic_canonicityE_inst_moves :
  projT1 pcuic_canonicityE_inst <> mkApps (tFix iv_mfix 0) [sri_cF].
Proof.
  destruct pcuic_canonicityE_inst as [t' [[ty conv] hd]]; cbn [projT1]; clear ty conv.
  intros ->. destruct hd as [hd|st].
  - vm_compute in hd. discriminate hd.
  - apply (stuck_cofix_case_mkApps_inv (tFix iv_mfix 0) [sri_cF] eq_refl) in st
      as [st|(mfix & idx & d & a & e & hnth & harg & sta)].
    + remember (tFix iv_mfix 0) as t0 eqn:e0. destruct st; try discriminate e0.
      destruct args using rev_case.
      * match goal with H : nth_error [] _ = Some _ |- _ => now rewrite nth_error_nil in H end.
      * rewrite mkApps_app in e0. discriminate e0.
    + injection e as <- <-. cbn in hnth. injection hnth as <-. cbn in harg. injection harg as <-.
      apply stuck_cofix_case_head in sta. vm_compute in sta. discriminate sta.
Qed.

End CanonicityEtaInstances.
