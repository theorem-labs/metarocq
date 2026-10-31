(* Distributed under the terms of the MIT license. *)

(* NONDEGEN tags: an INSTANCE NONDEGEN tag is a reader judgment backed by a compiled nontriviality
   lemma, not a mechanical guarantee.
   Measured reader miss rate, a FLOOR (a ruling made after 2026-10-31T09:00Z can only raise it): at least 24 of 60 instances sampled (seed 202610301905) from the 323 that the focused review of 11092806 had not covered (40.0%, 95% upper bound 51.4%, one-sided Clopper-Pearson): 17 from the union of the verdicts held by two independent reviews (Opus 5: 10; Opus 5.5: 15, 6 of its verdicts borderline at confidence 0.5-0.6), plus seven further rows that both reviews had passed and root rulings made between 2026-10-31T01:29Z and 05:41Z reclassified under the same standard (S12, S13, S19, S31, S36, S51, S57), which raised the count from at least 17 to at least 24. 22 of the 24 are false NONDEGEN tags (22 of the 52 sampled NONDEGEN instances, 42.3%); 2 are false prose under a correct tag. All 24 are corrected at frac/eta 6978492e, but the sample estimates the rate over ALL instance tags: a comparable share of the unsampled instances is expected to be wrong and is NOT corrected.
   P4 at frac/eta 6978492e: 313 lemmas with a base twin are accounted for: 208 have at least one NONDEGEN instance, 83 are undemonstrable by their own statements (IMPOSSIBLE-only), and 22 have no working instance (NOT-BUILT-only): BDStrengtheningEta.on_free_vars_typeE; BDToPCUICEta.wf_rel_weakE; PCUICAlphaEta.eq_context_conversionE, isType_eq_context_conversionE, typing_alpha_propE, wf_local_alphaE; PCUICClassificationEta.eval_whneE, fix_app_is_constructorE, invert_cumul_arity_lE, invert_cumul_arity_l_genE, invert_cumul_arity_rE, invert_cumul_arity_r_genE, isArity_typing_spineE, typing_cofix_coindE, value_whnfE, wf_cofixpoint_spineE, wf_fixpoint_spineE; PCUICInversionEta.into_ws_cumulE; PCUICSREta.prim_app_typing_invE, sr_prim_opE, typing_spine_prim_arg_typesE, typing_spine_prim_argsE. No NONDEGEN tag at frac/eta 6978492e is judged false by a root ruling made by 2026-10-31T09:00Z. The 208 is a CEILING, not a count of sound demonstrations: every root ruling made between 2026-10-31T01:29Z and 07:30Z that re-examined NONDEGEN tags in place found more false ones (the next, at 08:29Z, judged its one row weak, not false); retags from those rulings moved 25 targets out between frac/eta c825ec02 (229) and 6978492e, and rebuilt instances moved 4 in. The miss rate above (a floor) and this ceiling measure the same thing two ways. Combined at frac/eta 6978492e (the sample's false-tag rate, 22 of 52, applied to every NONDEGEN instance outside the sample, including the 36 that root rulings judged sound; the instances of one file counted as one cluster), they give an expected 131 of the 208 with at least one sound instance, 90% interval 89 to 170; about 77 of the 208 are expected to have none. Corrections pull in both directions (90% intervals with the rate fixed): counting the 36 root-judged instances as sound gives 147 (137 to 156); the 38 false instances found in the sampled frame outside the sample, between the sample's head 39ff4f31 and frac/eta 6978492e, lower the rate that remains, giving 143 (133 to 154); and sampled rows judged sound are not certain (S12, S13, S19, S31, S36, S51 and S57 were each passed by both reviews and judged false), which gives 127 (115 to 138). Context of the 208 (context = a judgment argument of type list (context_decl term), empty or not by computing its length, not the lemma's Γ parameter): 84 use a non-empty context (in 2 of them, typing_eq_termE and typing_leq_termE, it occurs but does no work); 23 have the context as their subject; 19 have a non-empty context that no term or type mentions; 4 undecided; 58 work only at the empty context (7 forced by the statement, 51 by the instance's choice; up to 77 under stricter readings); 20 have no context argument, which is not the same as the empty context. A mechanical detector run over all 413 instances at frac/eta 2e26fc93 (does an input sub-derivation inhabit the conclusion, at any depth and through squash, existential and pair packages; does the conclusion close by computation alone) finds 30 of the 56 blocks (53 instances) that root rulings had judged false, 11 of the 22 such tags in the sample; it finds none of the reflexive-step, identity-only or translation cases and 7 of 16 round trips (it cannot see a round trip inside the target lemma's own proof), and on closed equations it flags every row, sound or not; root rulings made by 2026-10-31T08:29Z judged its 20 flags on unruled NONDEGEN tags (8 false). A first mechanical sweep flagged at least 31 of the 338 NONDEGEN instances at 0bf9899a, before the tag changes of LAND8a (eede40b7, 86d983ce), LAND9 (016ec167, 727d49e9), LAND11-A (6568a017), LAND12 (07786120, e2c9c6b2), LAND13-A (af1fa399), LAND10 (fc8627b8), GAMMA9 (1f0c66a6, 201d23cc) and LAND13-C (46b62a8a to 8c0b7bcd), whose conclusion is convertible to an input sub-derivation (3 of the 31 match the instance itself or its helper rather than an input); all 31 were judged by 2026-10-31T08:29Z: its 9 non-equation flags 9 bad, with the kind-label correct in 6 of 9; its 22 closed-equation flags, which it cannot discriminate, 10 bad, 4 weak only, 8 not degenerate. Prose overclaims were not mechanically enumerated, because that detector failed its controls. The 45-row marker census had 2 reopened as of 2026-10-31T03:30Z. *)

(** * Satisfying instances of the lemmas of [Bidirectional/BDUniqueEta] (row T6)

  **No forecast class.** Every lemma of [BDUniqueEta] uses soundness, validity or
  completeness, so it took the class of [BDToPCUICEta] as a premise until copy 18b landed
  (frac/eta 3e6b422d); the class is deleted. The instances below are applied in section
  [BDUniqueClassInstances] (which held it). Every derivation they need is built here, in
  [PCUICInversionEtaInstances], [BDTypingEtaInstances] or [BDToPCUICEtaInstances].

  **The environment** is [si_Σ] ([PCUICCumulativitySpecEtaClosureInstances]:
  [Inductive I (A : Prop) : Prop := c : I A], with [si_wfE]).

  **Non-degeneracy.** The uniqueness lemmas compare two derivations of one term. Each instance
  tagged NONDEGEN below that takes two derivations takes two different ones, and the conclusion
  relates what they give: two different types, or two different products or argument lists
  reached from one type; [BDUniqueEta.principal_typeE] takes one typing. The two instances
  tagged IMPOSSIBLE pass one derivation twice. The comment above each instance carries its tag
  of the instance degeneracy gate; the declarations that are not instances are registered on the
  witness line after the imports.
  - in [bu_ΓQ = [f : Π P : Prop. bu_dup P]], with [bu_dup := λ x : Prop. x → x], [f ▹Π] keeps
    the codomain [bu_dup P] or contracts it to [P → P] ([bu_f_prod1], [bu_f_prod2]), so
    [f (∀P.P)] infers the two different types [bu_dup (∀P.P)] and [(∀P.P) → (∀P.P)]
    ([bu_app_infer1], [bu_app_infer2], [bu_app_types_differ]: the body of [bu_dup] uses its
    variable, and the contractum is neither the argument nor the body), for the main theorem,
    [infering_uniqueE] and [infering_unique'E]. [infering_checkingE] takes the first inference
    and the check of [f (∀P.P)] at [(∀P.P) → (∀P.P)] built on the second ([bu_app_check2]);
    [infering_prod_inferingE] takes the first inference and the [▹Π] built on the second
    ([bu_app_prod2]); the first type is not a product ([infering_prod_inferingE_inst_nondeg]);
  - [X := (λ x : Prop. x → x) ((λ y : Prop. y) (∀P.P))] reduces in one step to
    [X1 := (λ y. y) (∀P.P) → (λ y. y) (∀P.P)] and to [X2 := (λ x. x → x) (∀P.P)] ([bu_X],
    [bu_X1], [bu_X2]; [bu_X_red1], [bu_X_red2]). In [bu_ΓX = [f : X → X]], [f ▹Π] has the two
    derivations [(_, X1, X1)] and [(_, X2, X2)] ([bu_fX_prod1], [bu_fX_prod2]), for
    [infering_prod_prodE] and [infering_prod_prod'E]; in [bu_Γg = [g : I X]], [g ▹{I}] has the
    argument lists [[X1]] and [[X2]] ([bu_gX_ind1], [bu_gX_ind2]), for [infering_ind_indE] and
    [infering_ind_ind'E]. Every type inferred for [f] is [X → X], every type inferred for [g] is
    [I X], and [X], [X1], [X2] are pairwise different ([infering_prod_prodE_inst_nondeg],
    [infering_ind_indE_inst_nondeg]);
  - in [bu_ΓI = [g : Π P : Prop. bu_dupI P]], with [bu_dupI := λ x : Prop. I (x → x)],
    [g (∀P.P)] infers [bu_dupI (∀P.P)] and [I ((∀P.P) → (∀P.P))] ([bu_gF_infer1],
    [bu_gF_infer2]); [infering_ind_inferingE] takes the first inference and the [▹{I}] built on
    the second ([bu_gF_ind2]); the first type is not an application of an inductive type
    ([infering_ind_inferingE_inst_nondeg]);
  - in [bu_Γf = [h : Π _ : Prop. d; d := Prop : Type]], [h (∀P.P)] infers [d] and [Prop]
    ([bu_hF_infer1], [bu_hF_infer2]); [infering_sort_inferingE] takes the first inference and the
    [▹□] built on the second ([bu_hF_sort2]); [d] is not a sort and reduces to [Prop] in one step
    ([infering_sort_inferingE_inst_nondeg]);
  - [BDUniqueEta.principal_typeE] is applied to the typing [x : G F] of
    [checking_typingE_eta_inst]; every type inferred for [x] in [bd_Γη] is [G (λ y. F y)], which
    is not [G F] and η-contracts to it in one step ([BDToPCUICEtaInstances.bdi_eta_pair]).
  The two rows whose every instance is degenerate by the statement, [infering_sort_sortE] and
  [isTypeRel_uniqueE], are tagged at their instance. The reduction facts the proofs use:
  [PCUICPrincipalityEta.closed_red_confluence_cb] and [invert_red_sort_cb], with their instances
  in [PCUICPrincipalityEtaInstances]; [PCUICSREta.closed_red_red_subst0_cb], with its instance in
  [PCUICSREtaInstances]; and [invert_red_prod_cb], [invert_red_mkApps_tInd_cb],
  [closed_red_untyped_substitution_cb] ([PCUICConversion]) and [red_red_ctx_inv'_cb]
  ([PCUICContextConversion]), [ClosedBodies] lemmas of base files, with no instance in the lane's
  instance files. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICReduction PCUICWellScopedCumulativity PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICClosedBodies PCUICTypingEta
     PCUICTypingEtaNotions PCUICCumulativitySpecEtaClosureInstances PCUICEtaDefs PCUICEtaI5
     PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICWfUniversesEta
     PCUICInversionEtaInstances
     PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICSpineEta PCUICValidityEta PCUICSREta
     BDTyping BDTypingEta BDTypingEtaInstances BDToPCUICEta BDToPCUICEtaInstances BDFromPCUICEta
     BDUniqueEta.
From Equations.Type Require Import Relation.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

(** The declarations that are not instances: the contexts, derivations and non-degeneracy
    facts the instances are built from or name.
    WITNESSES: bu_* *)

(** ** Derivations, without any class *)

(** [bu_dup := λ x : Prop. x → x]: its body uses its variable twice. *)
Definition bu_dup : term := tLambda si_na si_P (tProd si_na (tRel 0) (tRel 1)).

Lemma bu_dup_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E bu_dup : iv_PP.
Proof.
  intros h. have w := iv_wf_P si_Σ Γ h.
  have hx : si_Σ ;;; Γ ,, vass si_na si_P |-E tRel 0 : tSort sProp :=
    typeE_Rel _ _ 0 (vass si_na si_P) w eq_refl.
  have w2 := iv_wf_vass si_Σ _ si_na (tRel 0) sProp w hx eq_refl.
  have hx2 : si_Σ ;;; Γ ,, vass si_na si_P ,, vass si_na (tRel 0) |-E tRel 1 : tSort sProp :=
    typeE_Rel _ _ 1 (vass si_na si_P) w2 eq_refl.
  exact (typeE_Lambda _ _ si_na si_P (tProd si_na (tRel 0) (tRel 1)) si_P
           (iv_vass si_Σ Γ si_na si_P _ (iv_P_typed si_Σ Γ h) eq_refl)
           (typeE_Prod _ _ si_na (tRel 0) (tRel 1) sProp sProp
              (iv_vass_s si_Σ _ si_na (tRel 0) sProp hx eq_refl) hx2)).
Qed.

(** [Q := Π P : Prop. bu_dup P] and the context [f : Q]. *)
Definition bu_Q : term := tProd si_na si_P (tApp bu_dup (tRel 0)).
Definition bu_ΓQ : context := [vass si_na bu_Q].

Lemma bu_dupP_typed (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ ,, vass si_na si_P |-E tApp bu_dup (tRel 0) : si_P.
Proof.
  intros h. have w := iv_wf_P si_Σ Γ h.
  exact (typeE_App _ _ bu_dup si_na si_P si_P _ (tRel 0) (iv_PP_typed si_Σ _ w) (bu_dup_typed _ w)
           (typeE_Rel _ _ 0 (vass si_na si_P) w eq_refl)).
Qed.

Lemma bu_Q_typed (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ |-E bu_Q : tSort (Sort.sort_of_product (Sort.super sProp) sProp).
Proof.
  intros h. unfold bu_Q. apply typeE_Prod.
  - exact (iv_vass_s si_Σ Γ si_na si_P _ (iv_P_typed si_Σ Γ h) eq_refl).
  - exact (bu_dupP_typed Γ h).
Qed.

Lemma bu_wf_ΓQ : wf_localE si_Σ bu_ΓQ.
Proof. exact (iv_wf_vass si_Σ [] si_na bu_Q _ localenv_nil (bu_Q_typed [] localenv_nil) eq_refl). Qed.

Lemma bu_f_infer : si_Σ ;;; bu_ΓQ |-E tRel 0 ▹ bu_Q.
Proof. exact (inferE_Rel _ bu_ΓQ 0 (vass si_na bu_Q) eq_refl). Qed.

(** [f ▹Π] keeping the β-redex [bu_dup P] of the codomain, and contracting it to [P → P]. *)
Lemma bu_f_prod1 : si_Σ ;;; bu_ΓQ |-E tRel 0 ▹Π (si_na, si_P, tApp bu_dup (tRel 0)).
Proof. econstructor; [exact bu_f_infer|apply rt_refl]. Qed.

Lemma bu_f_prod2 : si_Σ ;;; bu_ΓQ |-E tRel 0 ▹Π (si_na, si_P, tProd si_na (tRel 0) (tRel 1)).
Proof.
  econstructor; [exact bu_f_infer|].
  apply rt_step. unfold bu_Q. apply prod_red_r.
  exact (red_beta si_Σ _ si_na si_P (tProd si_na (tRel 0) (tRel 1)) (tRel 0)).
Qed.

(** [∀P:Prop. P ◃ Prop], in any context. *)
Lemma bu_False_check (Γ : context) : si_Σ ;;; Γ |-E iv_False ◃ si_P.
Proof.
  eapply checkE_Cumul.
  - unfold iv_False. apply inferE_Prod.
    + exact (bd_vass_s Γ si_na si_P _ (bd_P_sort Γ) eq_refl).
    + econstructor; [exact (inferE_Rel _ (Γ ,, vass si_na si_P) 0 (vass si_na si_P) eq_refl)|apply rt_refl].
  - apply JoinE_refl.
Qed.

Lemma bu_app_infer1 : si_Σ ;;; bu_ΓQ |-E tApp (tRel 0) iv_False ▹ tApp bu_dup iv_False.
Proof. exact (inferE_App _ _ _ _ _ _ _ bu_f_prod1 (bu_False_check _)). Qed.

(** [F → F], with [F := ∀P:Prop. P]: the contractum of [bu_dup F]. *)
Definition bu_FF : term := tProd si_na iv_False iv_False.

Lemma bu_app_infer2 : si_Σ ;;; bu_ΓQ |-E tApp (tRel 0) iv_False ▹ bu_FF.
Proof. exact (inferE_App _ _ _ _ _ _ _ bu_f_prod2 (bu_False_check _)). Qed.

(** The two types [bu_dup F] and [F → F] differ; the body [x → x] of [bu_dup] is not a bare
    variable, and its contractum [F → F] is neither the argument [F] nor the body. *)
Lemma bu_app_types_differ :
  [/\ (forall k, tProd si_na (tRel 0) (tRel 1) <> tRel k), tApp bu_dup iv_False <> bu_FF,
      bu_FF <> iv_False & bu_FF <> tProd si_na (tRel 0) (tRel 1)].
Proof.
  split; [intros k; discriminate| | |].
  - intros e. vm_compute in e. discriminate e.
  - intros e. vm_compute in e. discriminate e.
  - intros e. vm_compute in e. discriminate e.
Qed.

(** [f (∀P.P) ◃ F → F], on the inference [bu_app_infer2], with a reflexive join. *)
Lemma bu_app_check2 : si_Σ ;;; bu_ΓQ |-E tApp (tRel 0) iv_False ◃ bu_FF.
Proof. eapply checkE_Cumul; [exact bu_app_infer2|apply JoinE_refl]. Qed.

(** [f (∀P.P) ▹Π (_ : F, F)], on the inference [bu_app_infer2]: [F → F] is a product. *)
Lemma bu_app_prod2 : si_Σ ;;; bu_ΓQ |-E tApp (tRel 0) iv_False ▹Π (si_na, iv_False, iv_False).
Proof. econstructor; [exact bu_app_infer2|apply rt_refl]. Qed.

(** The type [bu_dup F] of [bu_app_infer1] is not a product; the body [x → x] of [bu_dup] is not a
    bare variable, and the product [F → F] it contracts to is not the argument [F]. *)
Lemma infering_prod_inferingE_inst_nondeg :
  [/\ (forall na A B, tApp bu_dup iv_False <> tProd na A B),
      (forall k, tProd si_na (tRel 0) (tRel 1) <> tRel k) &
      bu_FF <> iv_False].
Proof.
  split; [intros na A B; discriminate|intros k; discriminate|].
  intros e. vm_compute in e. discriminate e.
Qed.

Definition bu_idF : term := tApp iv_id iv_False.

(** [X := bu_dup ((λ y : Prop. y) (∀P.P))], and the two terms
    [X1 := (λ y. y) (∀P.P) → (λ y. y) (∀P.P)] and [X2 := bu_dup (∀P.P)] that [bu_X_red1] and
    [bu_X_red2] reduce it to. *)
Definition bu_X : term := tApp bu_dup bu_idF.
Definition bu_X1 : term := tProd si_na bu_idF bu_idF.
Definition bu_X2 : term := tApp bu_dup iv_False.

Lemma bu_X_red1 (Γ : context) : red1 si_Σ Γ bu_X bu_X1.
Proof. exact (red_beta si_Σ Γ si_na si_P (tProd si_na (tRel 0) (tRel 1)) bu_idF). Qed.

Lemma bu_X_red2 (Γ : context) : red1 si_Σ Γ bu_X bu_X2.
Proof. exact (app_red_r si_Σ Γ bu_idF iv_False bu_dup (red_beta si_Σ Γ si_na si_P (tRel 0) iv_False)). Qed.

Lemma bu_X_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E bu_X : si_P.
Proof.
  intros h.
  exact (typeE_App _ _ bu_dup si_na si_P si_P _ bu_idF (iv_PP_typed si_Σ Γ h) (bu_dup_typed Γ h)
           (iv_app_typed si_Σ Γ h)).
Qed.

(** [f : X → X], and its two [▹Π] derivations: [X → X] reduced to [X1 → X1] and to [X2 → X2]. *)
Definition bu_ΓX : context := [vass si_na (tProd si_na bu_X bu_X)].

Lemma bu_wf_ΓX : wf_localE si_Σ bu_ΓX.
Proof.
  have w := iv_wf_vass si_Σ [] si_na bu_X sProp localenv_nil (bu_X_typed [] localenv_nil) eq_refl.
  exact (iv_wf_vass si_Σ [] si_na (tProd si_na bu_X bu_X) (Sort.sort_of_product sProp sProp) localenv_nil
           (typeE_Prod _ _ si_na bu_X bu_X sProp sProp
              (iv_vass_s si_Σ [] si_na bu_X sProp (bu_X_typed [] localenv_nil) eq_refl) (bu_X_typed _ w))
           eq_refl).
Qed.

Lemma bu_fX_infer : si_Σ ;;; bu_ΓX |-E tRel 0 ▹ tProd si_na bu_X bu_X.
Proof. exact (inferE_Rel _ bu_ΓX 0 (vass si_na (tProd si_na bu_X bu_X)) eq_refl). Qed.

Lemma bu_fX_prod1 : si_Σ ;;; bu_ΓX |-E tRel 0 ▹Π (si_na, bu_X1, bu_X1).
Proof.
  econstructor; [exact bu_fX_infer|].
  eapply rt_trans; apply rt_step.
  - exact (prod_red_l si_Σ bu_ΓX si_na bu_X bu_X bu_X1 (bu_X_red1 bu_ΓX)).
  - exact (prod_red_r si_Σ bu_ΓX si_na bu_X bu_X1 bu_X1 (bu_X_red1 _)).
Qed.

Lemma bu_fX_prod2 : si_Σ ;;; bu_ΓX |-E tRel 0 ▹Π (si_na, bu_X2, bu_X2).
Proof.
  econstructor; [exact bu_fX_infer|].
  eapply rt_trans; apply rt_step.
  - exact (prod_red_l si_Σ bu_ΓX si_na bu_X bu_X bu_X2 (bu_X_red2 bu_ΓX)).
  - exact (prod_red_r si_Σ bu_ΓX si_na bu_X bu_X2 bu_X2 (bu_X_red2 _)).
Qed.

(** Every type inferred for [f] in [bu_ΓX] is [X → X]; [X] is neither [X1] nor [X2], and [X1] is
    not [X2]. *)
Lemma infering_prod_prodE_inst_nondeg :
  [/\ (forall T', si_Σ ;;; bu_ΓX |-E tRel 0 ▹ T' -> T' = tProd si_na bu_X bu_X),
      bu_X <> bu_X1, bu_X <> bu_X2 & bu_X1 <> bu_X2].
Proof.
  split.
  - intros T' h. inversion h; subst.
    match goal with hn : nth_error _ _ = Some _ |- _ => vm_compute in hn; injection hn as hd; subst end.
    reflexivity.
  - intros e. vm_compute in e. discriminate e.
  - intros e. vm_compute in e. discriminate e.
  - intros e. vm_compute in e. discriminate e.
Qed.

(** [g : I X], and its two [▹{I}] derivations: [I X] reduced to [I X1] and to [I X2]. *)
Definition bu_Γg : context := [vass si_na (tApp (tInd si_ind []) bu_X)].

Lemma bu_wf_Γg : wf_localE si_Σ bu_Γg.
Proof.
  exact (iv_wf_vass si_Σ [] si_na (tApp (tInd si_ind []) bu_X) sProp localenv_nil
           (iv_IX_typed [] bu_X localenv_nil (bu_X_typed [] localenv_nil)) eq_refl).
Qed.

Lemma bu_gX_infer : si_Σ ;;; bu_Γg |-E tRel 0 ▹ tApp (tInd si_ind []) bu_X.
Proof. exact (inferE_Rel _ bu_Γg 0 (vass si_na (tApp (tInd si_ind []) bu_X)) eq_refl). Qed.

Lemma bu_gX_ind1 : si_Σ ;;; bu_Γg |-E tRel 0 ▹{si_ind} ([], [bu_X1]).
Proof.
  econstructor; [exact bu_gX_infer|].
  apply rt_step. exact (app_red_r si_Σ bu_Γg bu_X bu_X1 (tInd si_ind []) (bu_X_red1 bu_Γg)).
Qed.

Lemma bu_gX_ind2 : si_Σ ;;; bu_Γg |-E tRel 0 ▹{si_ind} ([], [bu_X2]).
Proof.
  econstructor; [exact bu_gX_infer|].
  apply rt_step. exact (app_red_r si_Σ bu_Γg bu_X bu_X2 (tInd si_ind []) (bu_X_red2 bu_Γg)).
Qed.

(** Every type inferred for [g] in [bu_Γg] is [I X]; [X] is neither [X1] nor [X2], and [X1] is not
    [X2]. *)
Lemma infering_ind_indE_inst_nondeg :
  [/\ (forall T', si_Σ ;;; bu_Γg |-E tRel 0 ▹ T' -> T' = tApp (tInd si_ind []) bu_X),
      bu_X <> bu_X1, bu_X <> bu_X2 & bu_X1 <> bu_X2].
Proof.
  split.
  - intros T' h. inversion h; subst.
    match goal with hn : nth_error _ _ = Some _ |- _ => vm_compute in hn; injection hn as hd; subst end.
    reflexivity.
  - intros e. vm_compute in e. discriminate e.
  - intros e. vm_compute in e. discriminate e.
  - intros e. vm_compute in e. discriminate e.
Qed.

(** [bu_dupI := λ x : Prop. I (x → x)]: its body uses its variable inside the argument of [I];
    [QI := Π P : Prop. bu_dupI P] and the context [g : QI]. *)
Definition bu_dupI : term := tLambda si_na si_P (tApp (tInd si_ind []) (tProd si_na (tRel 0) (tRel 1))).
Definition bu_QI : term := tProd si_na si_P (tApp bu_dupI (tRel 0)).
Definition bu_ΓI : context := [vass si_na bu_QI].

Lemma bu_dupI_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E bu_dupI : iv_PP.
Proof.
  intros h. have w := iv_wf_P si_Σ Γ h.
  have hx : si_Σ ;;; Γ ,, vass si_na si_P |-E tRel 0 : tSort sProp :=
    typeE_Rel _ _ 0 (vass si_na si_P) w eq_refl.
  have w2 := iv_wf_vass si_Σ _ si_na (tRel 0) sProp w hx eq_refl.
  have hx2 : si_Σ ;;; Γ ,, vass si_na si_P ,, vass si_na (tRel 0) |-E tRel 1 : tSort sProp :=
    typeE_Rel _ _ 1 (vass si_na si_P) w2 eq_refl.
  have hxx : si_Σ ;;; Γ ,, vass si_na si_P |-E tProd si_na (tRel 0) (tRel 1) : si_P :=
    typeE_Prod _ _ si_na (tRel 0) (tRel 1) sProp sProp
      (iv_vass_s si_Σ _ si_na (tRel 0) sProp hx eq_refl) hx2.
  exact (typeE_Lambda _ _ si_na si_P (tApp (tInd si_ind []) (tProd si_na (tRel 0) (tRel 1))) si_P
           (iv_vass si_Σ Γ si_na si_P _ (iv_P_typed si_Σ Γ h) eq_refl)
           (iv_IX_typed _ (tProd si_na (tRel 0) (tRel 1)) w hxx)).
Qed.

Lemma bu_QI_typed (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ |-E bu_QI : tSort (Sort.sort_of_product (Sort.super sProp) sProp).
Proof.
  intros h. have w := iv_wf_P si_Σ Γ h. unfold bu_QI. apply typeE_Prod.
  - exact (iv_vass_s si_Σ Γ si_na si_P _ (iv_P_typed si_Σ Γ h) eq_refl).
  - exact (typeE_App _ _ bu_dupI si_na si_P si_P _ (tRel 0) (iv_PP_typed si_Σ _ w)
             (bu_dupI_typed _ w) (typeE_Rel _ _ 0 (vass si_na si_P) w eq_refl)).
Qed.

Lemma bu_wf_ΓI : wf_localE si_Σ bu_ΓI.
Proof. exact (iv_wf_vass si_Σ [] si_na bu_QI _ localenv_nil (bu_QI_typed [] localenv_nil) eq_refl). Qed.

Lemma bu_g_infer : si_Σ ;;; bu_ΓI |-E tRel 0 ▹ bu_QI.
Proof. exact (inferE_Rel _ bu_ΓI 0 (vass si_na bu_QI) eq_refl). Qed.

(** [g ▹Π] keeping the β-redex [bu_dupI P] of the codomain, and contracting it to [I (P → P)]. *)
Lemma bu_g_prod1 : si_Σ ;;; bu_ΓI |-E tRel 0 ▹Π (si_na, si_P, tApp bu_dupI (tRel 0)).
Proof. econstructor; [exact bu_g_infer|apply rt_refl]. Qed.

Lemma bu_g_prod2 :
  si_Σ ;;; bu_ΓI |-E tRel 0 ▹Π (si_na, si_P, tApp (tInd si_ind []) (tProd si_na (tRel 0) (tRel 1))).
Proof.
  econstructor; [exact bu_g_infer|].
  apply rt_step. unfold bu_QI. apply prod_red_r.
  exact (red_beta si_Σ _ si_na si_P (tApp (tInd si_ind []) (tProd si_na (tRel 0) (tRel 1))) (tRel 0)).
Qed.

(** [g (∀P.P)] infers [bu_dupI (∀P.P)] and [I (F → F)]; on the second, [▹{I} ([], [F → F])]. *)
Lemma bu_gF_infer1 : si_Σ ;;; bu_ΓI |-E tApp (tRel 0) iv_False ▹ tApp bu_dupI iv_False.
Proof. exact (inferE_App _ _ _ _ _ _ _ bu_g_prod1 (bu_False_check _)). Qed.

Lemma bu_gF_infer2 : si_Σ ;;; bu_ΓI |-E tApp (tRel 0) iv_False ▹ tApp (tInd si_ind []) bu_FF.
Proof. exact (inferE_App _ _ _ _ _ _ _ bu_g_prod2 (bu_False_check _)). Qed.

Lemma bu_gF_ind2 : si_Σ ;;; bu_ΓI |-E tApp (tRel 0) iv_False ▹{si_ind} ([], [bu_FF]).
Proof. econstructor; [exact bu_gF_infer2|apply rt_refl]. Qed.

(** The type [bu_dupI F] of [bu_gF_infer1] is not an application of an inductive type (its head
    is a λ); the body [I (x → x)] of [bu_dupI] is not a bare variable, and the term [I (F → F)] it
    contracts to is neither the argument [F] nor the body. *)
Lemma infering_ind_inferingE_inst_nondeg :
  [/\ (forall ind u args, tApp bu_dupI iv_False <> mkApps (tInd ind u) args),
      (forall k, tApp (tInd si_ind []) (tProd si_na (tRel 0) (tRel 1)) <> tRel k),
      tApp (tInd si_ind []) bu_FF <> iv_False &
      tApp (tInd si_ind []) bu_FF <> tApp (tInd si_ind []) (tProd si_na (tRel 0) (tRel 1))].
Proof.
  split.
  - intros ind u args e.
    have hdec : decompose_app (mkApps (tInd ind u) args) = (tInd ind u, args) by apply decompose_app_mkApps.
    rewrite -e in hdec. vm_compute in hdec. discriminate hdec.
  - intros k. discriminate.
  - intros e. vm_compute in e. discriminate e.
  - intros e. vm_compute in e. discriminate e.
Qed.

(** [d := Prop : Type, y : d]: [y ▹ d] ([bu_y_infer]) and [y ▹□ Prop] ([bu_y_sort]). *)
Definition bu_Γd : context := [vass si_na (tRel 0); vdef si_na si_P (tSort (Sort.super sProp))].

Lemma bu_wf_Γd : wf_localE si_Σ bu_Γd.
Proof.
  pose proof (typing_wf_sortE (Σ := si_Σ) si_wfE (iv_P_typed si_Σ [] localenv_nil)) as ws.
  pose proof (@typeE_Sort default_checker_flags si_Σ [] (Sort.super sProp) localenv_nil ws) as hT.
  assert (w1 : wf_localE si_Σ [vdef si_na si_P (tSort (Sort.super sProp))]).
  { apply localenv_cons_def; [constructor|].
    exact (iv_vdef si_Σ [] si_na si_P _ _ (iv_P_typed si_Σ [] localenv_nil) hT eq_refl). }
  exact (iv_wf_vass si_Σ _ si_na (tRel 0) (Sort.super sProp) w1
           (typeE_Rel _ _ 0 (vdef si_na si_P (tSort (Sort.super sProp))) w1 eq_refl) eq_refl).
Qed.

Lemma bu_y_infer : si_Σ ;;; bu_Γd |-E tRel 0 ▹ tRel 1.
Proof. exact (inferE_Rel _ bu_Γd 0 (vass si_na (tRel 0)) eq_refl). Qed.

Lemma bu_y_sort : si_Σ ;;; bu_Γd |-E tRel 0 ▹□ sProp.
Proof.
  econstructor; [exact bu_y_infer|].
  apply rt_step. exact (red_rel si_Σ bu_Γd 1 si_P eq_refl).
Qed.

(** [d := Prop : Type, h : Π _ : Prop. d]: [h ▹Π] keeping the let-variable [d] in the codomain,
    and unfolding it. *)
Definition bu_Γf : context :=
  [vass si_na (tProd si_na si_P (tRel 1)); vdef si_na si_P (tSort (Sort.super sProp))].

Lemma bu_wf_Γf : wf_localE si_Σ bu_Γf.
Proof.
  pose proof (typing_wf_sortE (Σ := si_Σ) si_wfE (iv_P_typed si_Σ [] localenv_nil)) as ws.
  pose proof (@typeE_Sort default_checker_flags si_Σ [] (Sort.super sProp) localenv_nil ws) as hT.
  assert (w1 : wf_localE si_Σ [vdef si_na si_P (tSort (Sort.super sProp))]).
  { apply localenv_cons_def; [constructor|].
    exact (iv_vdef si_Σ [] si_na si_P _ _ (iv_P_typed si_Σ [] localenv_nil) hT eq_refl). }
  have w2 := iv_wf_P si_Σ _ w1.
  have hd : si_Σ ;;; [vass si_na si_P; vdef si_na si_P (tSort (Sort.super sProp))] |-E tRel 1
      : tSort (Sort.super sProp) :=
    typeE_Rel _ _ 1 (vdef si_na si_P (tSort (Sort.super sProp))) w2 eq_refl.
  exact (iv_wf_vass si_Σ _ si_na (tProd si_na si_P (tRel 1))
           (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) w1
           (typeE_Prod _ _ si_na si_P (tRel 1) (Sort.super sProp) (Sort.super sProp)
              (iv_vass_s si_Σ _ si_na si_P _ (iv_P_typed si_Σ _ w1) eq_refl) hd) eq_refl).
Qed.

Lemma bu_h_infer : si_Σ ;;; bu_Γf |-E tRel 0 ▹ tProd si_na si_P (tRel 2).
Proof. exact (inferE_Rel _ bu_Γf 0 (vass si_na (tProd si_na si_P (tRel 1))) eq_refl). Qed.

Lemma bu_h_prod1 : si_Σ ;;; bu_Γf |-E tRel 0 ▹Π (si_na, si_P, tRel 2).
Proof. econstructor; [exact bu_h_infer|apply rt_refl]. Qed.

Lemma bu_h_prod2 : si_Σ ;;; bu_Γf |-E tRel 0 ▹Π (si_na, si_P, si_P).
Proof.
  econstructor; [exact bu_h_infer|].
  apply rt_step. apply prod_red_r. exact (red_rel si_Σ (bu_Γf ,, vass si_na si_P) 2 si_P eq_refl).
Qed.

(** [h (∀P.P)] infers [d] ([tRel 1]) and [Prop]; on the second, [▹□ Prop]. *)
Lemma bu_hF_infer1 : si_Σ ;;; bu_Γf |-E tApp (tRel 0) iv_False ▹ tRel 1.
Proof. exact (inferE_App _ _ _ _ _ _ _ bu_h_prod1 (bu_False_check _)). Qed.

Lemma bu_hF_infer2 : si_Σ ;;; bu_Γf |-E tApp (tRel 0) iv_False ▹ tSort sProp.
Proof. exact (inferE_App _ _ _ _ _ _ _ bu_h_prod2 (bu_False_check _)). Qed.

Lemma bu_hF_sort2 : si_Σ ;;; bu_Γf |-E tApp (tRel 0) iv_False ▹□ sProp.
Proof. econstructor; [exact bu_hF_infer2|apply rt_refl]. Qed.

(** In [bu_Γf], [d] ([tRel 1]), the type [bu_hF_infer1] gives [h (∀P.P)], is not a sort, and it
    reduces to [Prop] in one step (it is the let-variable of [d := Prop]). *)
Lemma infering_sort_inferingE_inst_nondeg :
  (forall u, tRel 1 <> tSort u) /\ ∥ red1 si_Σ bu_Γf (tRel 1) si_P ∥.
Proof.
  split; [intros u; discriminate|].
  exact (sq (red_rel si_Σ bu_Γf 1 si_P eq_refl)).
Qed.

(** ** The lemmas, applied (they took a forecast class until copy 18b landed) *)

Section BDUniqueClassInstances.

  (** The main theorem's inference component; the two types it relates, [bu_dup (∀P.P)] and
      [(∀P.P) → (∀P.P)], differ, and the second is the contractum of the first through a body
      that uses its variable ([bu_app_types_differ]).
      INSTANCE NONDEGEN BDUniqueEtaInstances.bu_app_types_differ *)
  Definition bidirectional_uniqueE_inst :
    ∑ T'', si_Σ ;;; bu_ΓQ ⊢ tApp bu_dup iv_False ⇝ T'' × si_Σ ;;; bu_ΓQ ⊢ bu_FF ⇝ T'' :=
    fst (snd (snd (snd (snd (bidirectional_uniqueE si_Σ si_wfE))))) bu_ΓQ (tApp (tRel 0) iv_False)
      (tApp bu_dup iv_False) bu_app_infer1 bu_wf_ΓQ bu_FF bu_app_infer2.

  (** INSTANCE NONDEGEN BDUniqueEtaInstances.bu_app_types_differ *)
  Definition infering_uniqueE_inst :
    ∑ T'', si_Σ ;;; bu_ΓQ ⊢ tApp bu_dup iv_False ⇝ T'' × si_Σ ;;; bu_ΓQ ⊢ bu_FF ⇝ T'' :=
    infering_uniqueE (Σ := si_Σ) si_wfE bu_wf_ΓQ (T := tApp bu_dup iv_False) (T' := bu_FF)
      bu_app_infer1 bu_app_infer2.

  (** INSTANCE NONDEGEN BDUniqueEtaInstances.bu_app_types_differ *)
  Definition infering_unique'E_inst : si_Σ ;;; bu_ΓQ ⊢E tApp bu_dup iv_False = bu_FF :=
    infering_unique'E (Σ := si_Σ) si_wfE bu_wf_ΓQ (T := tApp bu_dup iv_False) (T' := bu_FF)
      bu_app_infer1 bu_app_infer2.

  (** The comparison concluded is [bu_dup (∀P.P) ≤ (∀P.P) → (∀P.P)]: the type of [bu_app_infer1]
      against the type [bu_app_check2] checks [f (∀P.P)] at; the two differ
      ([bu_app_types_differ]).
      INSTANCE NONDEGEN BDUniqueEtaInstances.bu_app_types_differ *)
  Definition infering_checkingE_inst : si_Σ ;;; bu_ΓQ ⊢E tApp bu_dup iv_False ≤ bu_FF :=
    infering_checkingE (Σ := si_Σ) si_wfE bu_wf_ΓQ (T := tApp bu_dup iv_False) (T' := bu_FF) eq_refl
      bu_app_infer1 bu_app_check2.

  (** INSTANCE IMPOSSIBLE: the conclusion [u = u'] equates the sorts of two [▹□] derivations of one term; the two inferred types have a common reduct ([bidirectional_uniqueE], as in the proof of [infering_sort_sortE]), so by confluence the two sorts [tSort u] and [tSort u'] have one, and a sort has no reduct; so in every environment and context, whatever its [wfE], [u = u'] (here [sProp = sProp], for [bu_y_sort] twice). *)
  Definition infering_sort_sortE_inst : sProp = sProp :=
    infering_sort_sortE (Σ := si_Σ) si_wfE bu_wf_Γd bu_y_sort bu_y_sort.

  (** [h (∀P.P) ▹ d] ([bu_hF_infer1]) and [h (∀P.P) ▹□ Prop] ([bu_hF_sort2]): [d] is not a sort,
      and it reduces to [Prop] in one step ([infering_sort_inferingE_inst_nondeg]).
      INSTANCE NONDEGEN BDUniqueEtaInstances.infering_sort_inferingE_inst_nondeg *)
  Definition infering_sort_inferingE_inst : si_Σ ;;; bu_Γf ⊢ tRel 1 ⇝ tSort sProp :=
    infering_sort_inferingE (Σ := si_Σ) si_wfE (Γ := bu_Γf) (wfΓ := bu_wf_Γf) bu_hF_sort2 bu_hF_infer1.

  (** The two [▹Π] derivations of [f] in [bu_ΓX] ([bu_fX_prod1], [bu_fX_prod2]): every type
      inferred for [f] is [X → X], which is neither product, and the products [X1 → X1] and
      [X2 → X2] differ in domain and in codomain ([infering_prod_prodE_inst_nondeg]).
      INSTANCE NONDEGEN BDUniqueEtaInstances.infering_prod_prodE_inst_nondeg *)
  Definition infering_prod_prodE_inst :=
    infering_prod_prodE (Σ := si_Σ) si_wfE bu_wf_ΓX (A := bu_X1) (A' := bu_X2) (B := bu_X1) (B' := bu_X2)
      bu_fX_prod1 bu_fX_prod2.

  (** The same two derivations: the conclusion relates [X1] with [X2] as domains and as codomains
      ([infering_prod_prodE_inst_nondeg]).
      INSTANCE NONDEGEN BDUniqueEtaInstances.infering_prod_prodE_inst_nondeg *)
  Definition infering_prod_prod'E_inst :
    [× si_na = si_na, si_Σ ;;; bu_ΓX ⊢E bu_X1 = bu_X2 &
       si_Σ ;;; bu_ΓX ,, vass si_na bu_X1 ⊢E bu_X1 = bu_X2] :=
    infering_prod_prod'E (Σ := si_Σ) si_wfE bu_wf_ΓX (A := bu_X1) (A' := bu_X2) (B := bu_X1) (B' := bu_X2)
      bu_fX_prod1 bu_fX_prod2.

  (** [f (∀P.P) ▹ bu_dup (∀P.P)] ([bu_app_infer1]) and [f (∀P.P) ▹Π (_ : F, F)]
      ([bu_app_prod2]): [bu_dup (∀P.P)] is not a product
      ([infering_prod_inferingE_inst_nondeg]).
      INSTANCE NONDEGEN BDUniqueEtaInstances.infering_prod_inferingE_inst_nondeg *)
  Definition infering_prod_inferingE_inst :=
    infering_prod_inferingE (Σ := si_Σ) si_wfE bu_wf_ΓQ (T := tApp bu_dup iv_False) bu_app_prod2 bu_app_infer1.

  (** The two [▹{I}] derivations of [g] in [bu_Γg] ([bu_gX_ind1], [bu_gX_ind2]): every type
      inferred for [g] is [I X], whose argument is neither [X1] nor [X2], and the argument lists
      [[X1]] and [[X2]] differ ([infering_ind_indE_inst_nondeg]).
      INSTANCE NONDEGEN BDUniqueEtaInstances.infering_ind_indE_inst_nondeg *)
  Definition infering_ind_indE_inst :=
    infering_ind_indE (Σ := si_Σ) si_wfE bu_wf_Γg (args := [bu_X1]) (args' := [bu_X2]) bu_gX_ind1 bu_gX_ind2.

  (** The same two derivations: the conclusion relates [[X1]] with [[X2]]
      ([infering_ind_indE_inst_nondeg]).
      INSTANCE NONDEGEN BDUniqueEtaInstances.infering_ind_indE_inst_nondeg *)
  Definition infering_ind_ind'E_inst :
    [× si_ind = si_ind, ([] : Instance.t) = [] & ws_cumul_pbE_terms si_Σ bu_Γg [bu_X1] [bu_X2]] :=
    infering_ind_ind'E (Σ := si_Σ) si_wfE bu_wf_Γg (args := [bu_X1]) (args' := [bu_X2]) bu_gX_ind1 bu_gX_ind2.

  (** [g (∀P.P) ▹ bu_dupI (∀P.P)] ([bu_gF_infer1]) and [g (∀P.P) ▹{I} ([], [F → F])]
      ([bu_gF_ind2]): [bu_dupI (∀P.P)] is not an application of an inductive type
      ([infering_ind_inferingE_inst_nondeg]).
      INSTANCE NONDEGEN BDUniqueEtaInstances.infering_ind_inferingE_inst_nondeg *)
  Definition infering_ind_inferingE_inst :=
    infering_ind_inferingE (Σ := si_Σ) si_wfE bu_wf_ΓI (T := tApp bu_dupI iv_False)
      bu_gF_ind2 bu_gF_infer1.

  (** The typing [x : G F] in [bd_Γη] ([checking_typingE_eta_inst]): every type inferred for [x]
      there is [G (λ y. F y)], which is not [G F] and η-contracts to it in one step
      ([BDToPCUICEtaInstances.bdi_eta_pair]).
      INSTANCE NONDEGEN BDToPCUICEtaInstances.bdi_eta_pair
      TARGET BDUniqueEta.principal_typeE *)
  Definition principal_typeE_inst :=
    BDUniqueEta.principal_typeE (Σ := si_Σ) si_wfE (Γ := bd_Γη) checking_typingE_eta_inst.

  (** INSTANCE IMPOSSIBLE: the conclusion [rel = rel'] equates the relevances of two [isTypeRelE] judgments of one type; each relevance is that of a sort above the type's inferred sort ([typing_infering_sortE]), relevance is preserved along [leq_sort] ([leq_relevance_eq]) and the inferred sort is unique ([infering_sort_sortE]), as in the proof of [isTypeRel_uniqueE]; so in every environment and context, whatever its [wfE], [rel = rel'] (here [Relevant = Relevant]). *)
  Definition isTypeRel_uniqueE_inst : Relevant = Relevant :=
    isTypeRel_uniqueE (Σ := si_Σ) si_wfE (Γ := []) (T := iv_PP)
      (iv_vass si_Σ [] si_na iv_PP _ (iv_PP_typed si_Σ [] localenv_nil) eq_refl)
      (iv_vass si_Σ [] si_na iv_PP _ (iv_PP_typed si_Σ [] localenv_nil) eq_refl).

End BDUniqueClassInstances.
