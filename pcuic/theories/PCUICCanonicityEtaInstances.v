(* Distributed under the terms of the MIT license. *)

(* NONDEGEN tags: an INSTANCE NONDEGEN tag is a reader judgment backed by a compiled nontriviality
   lemma, not a mechanical guarantee.
   Measured reader miss rate, a FLOOR (a ruling made after 2026-10-31T09:00Z can only raise it): at least 24 of 60 instances sampled (seed 202610301905) from the 323 that the focused review of 11092806 had not covered (40.0%, 95% upper bound 51.4%, one-sided Clopper-Pearson): 17 from the union of the verdicts held by two independent reviews (Opus 5: 10; Opus 5.5: 15, 6 of its verdicts borderline at confidence 0.5-0.6), plus seven further rows that both reviews had passed and root rulings made between 2026-10-31T01:29Z and 05:41Z reclassified under the same standard (S12, S13, S19, S31, S36, S51, S57), which raised the count from at least 17 to at least 24. 22 of the 24 are false NONDEGEN tags (22 of the 52 sampled NONDEGEN instances, 42.3%); 2 are false prose under a correct tag. All 24 are corrected at frac/eta 6978492e, but the sample estimates the rate over ALL instance tags: a comparable share of the unsampled instances is expected to be wrong and is NOT corrected.
   P4 at frac/eta 6978492e: 313 lemmas with a base twin are accounted for: 208 have at least one NONDEGEN instance, 83 are undemonstrable by their own statements (IMPOSSIBLE-only), and 22 have no working instance (NOT-BUILT-only): BDStrengtheningEta.on_free_vars_typeE; BDToPCUICEta.wf_rel_weakE; PCUICAlphaEta.eq_context_conversionE, isType_eq_context_conversionE, typing_alpha_propE, wf_local_alphaE; PCUICClassificationEta.eval_whneE, fix_app_is_constructorE, invert_cumul_arity_lE, invert_cumul_arity_l_genE, invert_cumul_arity_rE, invert_cumul_arity_r_genE, isArity_typing_spineE, typing_cofix_coindE, value_whnfE, wf_cofixpoint_spineE, wf_fixpoint_spineE; PCUICInversionEta.into_ws_cumulE; PCUICSREta.prim_app_typing_invE, sr_prim_opE, typing_spine_prim_arg_typesE, typing_spine_prim_argsE. No NONDEGEN tag at frac/eta 6978492e is judged false by a root ruling made by 2026-10-31T09:00Z. The 208 is a CEILING, not a count of sound demonstrations: every root ruling made between 2026-10-31T01:29Z and 07:30Z that re-examined NONDEGEN tags in place found more false ones (the next, at 08:29Z, judged its one row weak, not false); retags from those rulings moved 25 targets out between frac/eta c825ec02 (229) and 6978492e, and rebuilt instances moved 4 in. The miss rate above (a floor) and this ceiling measure the same thing two ways. Combined at frac/eta 6978492e (the sample's false-tag rate, 22 of 52, applied to every NONDEGEN instance outside the sample, including the 36 that root rulings judged sound; the instances of one file counted as one cluster), they give an expected 131 of the 208 with at least one sound instance, 90% interval 89 to 170; about 77 of the 208 are expected to have none. Corrections pull in both directions (90% intervals with the rate fixed): counting the 36 root-judged instances as sound gives 147 (137 to 156); the 38 false instances found in the sampled frame outside the sample, between the sample's head 39ff4f31 and frac/eta 6978492e, lower the rate that remains, giving 143 (133 to 154); and sampled rows judged sound are not certain (S12, S13, S19, S31, S36, S51 and S57 were each passed by both reviews and judged false), which gives 127 (115 to 138). Context of the 208 (context = a judgment argument of type list (context_decl term), empty or not by computing its length, not the lemma's Γ parameter): 84 use a non-empty context (in 2 of them, typing_eq_termE and typing_leq_termE, it occurs but does no work); 23 have the context as their subject; 19 have a non-empty context that no term or type mentions; 4 undecided; 58 work only at the empty context (7 forced by the statement, 51 by the instance's choice; up to 77 under stricter readings); 20 have no context argument, which is not the same as the empty context. A mechanical detector run over all 413 instances at frac/eta 2e26fc93 (does an input sub-derivation inhabit the conclusion, at any depth and through squash, existential and pair packages; does the conclusion close by computation alone) finds 30 of the 56 blocks (53 instances) that root rulings had judged false, 11 of the 22 such tags in the sample; it finds none of the reflexive-step, identity-only or translation cases and 7 of 16 round trips (it cannot see a round trip inside the target lemma's own proof), and on closed equations it flags every row, sound or not; root rulings made by 2026-10-31T08:29Z judged its 20 flags on unruled NONDEGEN tags (8 false). A first mechanical sweep flagged at least 31 of the 338 NONDEGEN instances at 0bf9899a, before the tag changes of LAND8a (eede40b7, 86d983ce), LAND9 (016ec167, 727d49e9), LAND11-A (6568a017), LAND12 (07786120, e2c9c6b2), LAND13-A (af1fa399), LAND10 (fc8627b8), GAMMA9 (1f0c66a6, 201d23cc) and LAND13-C (46b62a8a to 8c0b7bcd), whose conclusion is convertible to an input sub-derivation (3 of the 31 match the instance itself or its helper rather than an input); all 31 were judged by 2026-10-31T08:29Z: its 9 non-equation flags 9 bad, with the kind-label correct in 6 of 9; its 22 closed-equation flags, which it cannot discriminate, 10 bad, 4 weak only, 8 not degenerate. Prose overclaims were not mechanically enumerated, because that detector failed its controls. The 45-row marker census had 2 reopened as of 2026-10-31T03:30Z. *)

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
