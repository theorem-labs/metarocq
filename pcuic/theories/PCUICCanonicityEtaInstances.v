(* Distributed under the terms of the MIT license. *)

(* NONDEGEN tags: an INSTANCE NONDEGEN tag is a reader judgment backed by a compiled nontriviality
   lemma, not a mechanical guarantee.
   Measured reader miss rate: at least 17 of 60 sampled instances (28.3%, 95% upper bound 39.4%), seed 202610301905: the union of the verdicts held by two independent reviews (Opus 5: 10 of 60; Opus 5.5: 15 of 60, 6 of its verdicts borderline at confidence 0.5-0.6). The 17 sampled misses are corrected at this head, but the sample estimates the rate over ALL instance tags: a comparable share of the unsampled instances is expected to be wrong and is NOT corrected. *)

(** * Satisfying instance of [PCUICCanonicityEta.pcuic_canonicityE] (row T6)

  **Section variables.** The normalization hypothesis [NormalizationInE si_Σ] only.
  [NormalizationInE] is base's [NormalizationIn] over [welltypedE] ([PCUICSNEta]): a premise
  unprovable by design (strong normalization), inherited from base's [pcuic_canonicity], which
  takes [NormalizationIn Σ]; it is not a forecast and is never discharged. (The forecast class
  [CanonForecastCopy20] was a second section variable until copy 20 (bfe54de2) and the class was
  deleted; T1's [SRForecastCopy18] was deleted when copy 18b landed.)

  **Non-degeneracy.** The instance runs on the application
  [t = (λx:Prop. c x) (∀P:Prop. P) : I (∀P:Prop. P)] in [si_Σ]
  ([PCUICClassificationEtaInstances.cli_lam_c_app_typed]), with [axiom_free si_Σ]
  ([cli_axiom_free]) and [wfE si_Σ] proved. Neither [t] (its head is an abstraction) nor its
  argument [∀P:Prop. P] (a product) is a canonical form; the β step builds [c (∀P:Prop. P)], the
  body [c x], which uses [x], with the argument for [x]. The lemma returns a [t'] convertible to
  [t] whose head is a constructor or a cofixpoint or, since BET-339 (F0, integ-all8), which is a
  case blocked on a cofixpoint ([stuck_cofix_case]); [pcuic_canonicityE_inst_moves] proves that
  this [t'] is neither [t] nor the argument, neither of which is such a blocked case. The
  normalization that the lemma rests on is the section
  variable above. *)

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

(** [t] is the application [(λx:Prop. c x) (∀P:Prop. P)]: neither [t] nor its argument is a
    canonical form, so [t'] is neither ([pcuic_canonicityE_inst_moves]).
    INSTANCE NONDEGEN PCUICCanonicityEtaInstances.pcuic_canonicityE_inst_moves *)
Definition pcuic_canonicityE_inst :=
  pcuic_canonicityE si_Σ cli_lam_c_app si_ind [] [iv_False] cli_axiom_free si_wfE cli_lam_c_app_typed.

(** [t = (λx:Prop. c x) (∀P:Prop. P)]: its body [c x] uses [x], and the β step substitutes the
    argument for [x], giving the canonical form [c (∀P:Prop. P)]. Neither [t] (head: an
    abstraction) nor the argument [∀P:Prop. P] (head: a product) is canonical, so the canonical
    form [t'] returned is neither [t] nor the argument. *)
Lemma pcuic_canonicityE_inst_moves :
  cli_lam_c_app = tApp (tLambda si_na si_P (tApp (tConstruct si_ind 0 []) (tRel 0))) iv_False /\
  noccur_between 0 1 (tApp (tConstruct si_ind 0 []) (tRel 0)) = false /\
  subst1 iv_False 0 (tApp (tConstruct si_ind 0 []) (tRel 0)) = sri_cF /\
  PCUICViews.construct_cofix_discr (head cli_lam_c_app) = false /\
  PCUICViews.construct_cofix_discr (head iv_False) = false /\
  PCUICViews.construct_cofix_discr (head sri_cF) = true /\
  projT1 pcuic_canonicityE_inst <> cli_lam_c_app /\
  projT1 pcuic_canonicityE_inst <> iv_False.
Proof.
  do 6 (split; [reflexivity|]).
  destruct pcuic_canonicityE_inst as [t' [[ty conv] hd]]; cbn [projT1]; clear ty conv.
  (* BET-339: [t'] may also be a case blocked on a cofixpoint ([stuck_cofix_case t']). Neither
     [t] (an application of an abstraction) nor the argument (a product) is one: no constructor
     of [stuck_cofix_case] concludes on an abstraction or a product. *)
  split; intros ->; destruct hd as [hd|st]; try (vm_compute in hd; discriminate hd).
  - change (stuck_cofix_case (mkApps (tLambda si_na si_P (tApp (tConstruct si_ind 0 []) (tRel 0)))
                                     [iv_False])) in st.
    apply (stuck_cofix_case_mkApps_inv (tLambda si_na si_P (tApp (tConstruct si_ind 0 []) (tRel 0)))
             [iv_False] eq_refl) in st as [st|(? & ? & ? & ? & e & _)];
      [|discriminate e].
    remember (tLambda si_na si_P (tApp (tConstruct si_ind 0 []) (tRel 0))) as t0 eqn:e0.
    destruct st; try discriminate e0.
    destruct args using rev_case; [cbn in e0; discriminate e0|].
    rewrite mkApps_app in e0. cbn in e0. discriminate e0.
  - unfold iv_False in st. remember (tProd _ _ _) as t0 eqn:e0.
    destruct st; try discriminate e0.
    destruct args using rev_case; [cbn in e0; discriminate e0|].
    rewrite mkApps_app in e0. cbn in e0. discriminate e0.
Qed.

End CanonicityEtaInstances.
