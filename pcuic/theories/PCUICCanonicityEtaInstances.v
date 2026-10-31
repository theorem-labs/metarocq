(* Distributed under the terms of the MIT license. *)

(* NONDEGEN tags: an INSTANCE NONDEGEN tag is a reader judgment backed by a compiled nontriviality
   lemma, not a mechanical guarantee.
   Measured reader miss rate: at least 20 of 60 instances sampled (seed 202610301905) from the 323 that the focused review of 11092806 had not covered (33.3%, 95% upper bound 44.6%, one-sided Clopper-Pearson): 17 from the union of the verdicts held by two independent reviews (Opus 5: 10; Opus 5.5: 15, 6 of its verdicts borderline at confidence 0.5-0.6), plus three further rows that both reviews had passed and root rulings made by 2026-10-31T03:30Z reclassified under the same standard (S12, S31, S36). 18 of the 20 sampled misses are corrected at frac/eta c825ec02 (S31 and S36 are not), but the sample estimates the rate over ALL instance tags: a comparable share of the unsampled instances is expected to be wrong and is NOT corrected.
   P4 at frac/eta c825ec02: 313 lemmas with a base twin are accounted for: 229 demonstrated (at least one NONDEGEN instance; this count includes 6 targets whose only NONDEGEN instance is judged false (as of 2026-10-31T03:30Z) and uncorrected at frac/eta c825ec02: PCUICClassificationEta.wf_fixpoint_spineE, wf_cofixpoint_spineE, whnf_classificationE, whnf_classification'E, ind_whnf_classificationE and ind_whnf_classification'E), 70 undemonstrable by their own statements (IMPOSSIBLE-only), and 14 with no working instance (NOT-BUILT-only): BDToPCUICEta.wf_rel_weakE; PCUICAlphaEta.eq_context_conversionE, isType_eq_context_conversionE, typing_alpha_propE, wf_local_alphaE; PCUICClassificationEta.typing_spine_nth_errorE, typing_spine_nth_error_NoneE, typing_spine_nth_error_None_prodE (non-degenerate instances for these 3 were built, unlanded and unreviewed as of 2026-10-31T03:30Z); PCUICInversionEta.into_ws_cumulE; PCUICPrincipalityEta.typing_leq_termE; PCUICSREta.prim_app_typing_invE, sr_prim_opE, typing_spine_prim_arg_typesE, typing_spine_prim_argsE. The demonstrated count rests on NONDEGEN tags with the measured miss rate above. As of 2026-10-31T03:30Z, 15 NONDEGEN tags are judged false, and at frac/eta c825ec02 they are uncorrected. 11 are conv → red cases whose input conversion was built from a reduction (for wf_fixpoint_spineE_inst the conv → red step sits inside its target's proof): 7 in BDFromPCUICEtaInstances (red_fix_witnessE_inst, mfix_body_on_conv_redE_fix_inst, red_cofix_witnessE_inst, mfix_body_on_conv_redE_cofix_inst, mfix_on_ind_conv_redE_cofix_inst, wf_fixpointE_wf_fixpoint_red_typed_inst, and sampled row S36 = wf_cofixpointE_wf_cofixpoint_red_inst) and PCUICPrincipalityEtaInstances.T8_Prod_l_plug_inst and T8_Prod_l_of_r_inst, whose targets are outside P4's input set, and PCUICClassificationEtaInstances.wf_fixpoint_spineE_inst and wf_cofixpoint_spineE_inst, whose targets are 2 of the 6 above. 4 are undemonstrable by their own statements (the conclusion is read off the head of the instance's own weak-head-normal witness): PCUICClassificationEtaInstances.whnf_classificationE_inst (sampled row S31), whnf_classification'E_inst, ind_whnf_classificationE_inst and ind_whnf_classification'E_inst, whose targets are the other 4 of the 6. Context of the demonstrations (context = a judgment argument of type list (context_decl term), empty or not by computing its length, not the lemma's Γ parameter): 79 use a non-empty context; 23 have the context as their subject; 20 have a non-empty context that no term or type mentions; 4 undecided; 70 work only at the empty context (10 forced by the statement, 60 by the instance's choice; up to 89 under stricter readings); 33 have no context argument, which is not the same as the empty context. A mechanical sweep flagged at least 31 of the 338 NONDEGEN instances at 0bf9899a, before the retags of LAND8a (eede40b7, 86d983ce), LAND9 (016ec167, 727d49e9) and LAND11-A (6568a017), whose conclusion is convertible to an input sub-derivation (3 of the 31 match the instance itself or its helper rather than an input); of its 9 non-equation flags, 9 were judged bad by 2026-10-31T03:30Z, with the kind-label correct in 6 of 9; it cannot see a cancellation inside the target lemma's own proof or a conclusion that is one part of a pair, and it does not discriminate the 22 closed equations (of the 3 sampled ones judged, S29 is weak only, S44 is not degenerate, and S31 is undemonstrable by its statement). Prose overclaims were not mechanically enumerated, because that detector failed its controls. Root rulings made by 2026-10-31T03:30Z reclassified three sampled rows that both reviews had passed, S36 (the red → conv → red class), S12 (its conclusion is the input's own cumulativity) and S31 (undemonstrable by its statement), raising the sampled rate from at least 17 to at least 20 of 60; the 45-row marker census had 2 reopened as of 2026-10-31T03:30Z. *)

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
  [t] whose head is a constructor or a cofixpoint; [pcuic_canonicityE_inst_moves] proves that this
  [t'] is neither [t] nor the argument. The normalization that the lemma rests on is the section
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
  split; intros ->; vm_compute in hd; discriminate hd.
Qed.

End CanonicityEtaInstances.
