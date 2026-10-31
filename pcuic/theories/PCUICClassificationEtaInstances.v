(* Distributed under the terms of the MIT license. *)

(* NONDEGEN tags: an INSTANCE NONDEGEN tag is a reader judgment backed by a compiled nontriviality
   lemma, not a mechanical guarantee.
   Measured reader miss rate: at least 20 of 60 instances sampled (seed 202610301905) from the 323 that the focused review of 11092806 had not covered (33.3%, 95% upper bound 44.6%, one-sided Clopper-Pearson): 17 from the union of the verdicts held by two independent reviews (Opus 5: 10; Opus 5.5: 15, 6 of its verdicts borderline at confidence 0.5-0.6), plus three further rows that both reviews had passed and root rulings made by 2026-10-31T03:30Z reclassified under the same standard (S12, S31, S36). 18 of the 20 sampled misses are corrected at frac/eta c825ec02 (S31 and S36 are not), but the sample estimates the rate over ALL instance tags: a comparable share of the unsampled instances is expected to be wrong and is NOT corrected.
   P4 at frac/eta c825ec02: 313 lemmas with a base twin are accounted for: 229 demonstrated (at least one NONDEGEN instance; this count includes 6 targets whose only NONDEGEN instance is judged false (as of 2026-10-31T03:30Z) and uncorrected at frac/eta c825ec02: PCUICClassificationEta.wf_fixpoint_spineE, wf_cofixpoint_spineE, whnf_classificationE, whnf_classification'E, ind_whnf_classificationE and ind_whnf_classification'E), 70 undemonstrable by their own statements (IMPOSSIBLE-only), and 14 with no working instance (NOT-BUILT-only): BDToPCUICEta.wf_rel_weakE; PCUICAlphaEta.eq_context_conversionE, isType_eq_context_conversionE, typing_alpha_propE, wf_local_alphaE; PCUICClassificationEta.typing_spine_nth_errorE, typing_spine_nth_error_NoneE, typing_spine_nth_error_None_prodE (non-degenerate instances for these 3 were built, unlanded and unreviewed as of 2026-10-31T03:30Z); PCUICInversionEta.into_ws_cumulE; PCUICPrincipalityEta.typing_leq_termE; PCUICSREta.prim_app_typing_invE, sr_prim_opE, typing_spine_prim_arg_typesE, typing_spine_prim_argsE. The demonstrated count rests on NONDEGEN tags with the measured miss rate above. As of 2026-10-31T03:30Z, 15 NONDEGEN tags are judged false, and at frac/eta c825ec02 they are uncorrected. 11 are conv → red cases whose input conversion was built from a reduction (for wf_fixpoint_spineE_inst the conv → red step sits inside its target's proof): 7 in BDFromPCUICEtaInstances (red_fix_witnessE_inst, mfix_body_on_conv_redE_fix_inst, red_cofix_witnessE_inst, mfix_body_on_conv_redE_cofix_inst, mfix_on_ind_conv_redE_cofix_inst, wf_fixpointE_wf_fixpoint_red_typed_inst, and sampled row S36 = wf_cofixpointE_wf_cofixpoint_red_inst) and PCUICPrincipalityEtaInstances.T8_Prod_l_plug_inst and T8_Prod_l_of_r_inst, whose targets are outside P4's input set, and PCUICClassificationEtaInstances.wf_fixpoint_spineE_inst and wf_cofixpoint_spineE_inst, whose targets are 2 of the 6 above. 4 are undemonstrable by their own statements (the conclusion is read off the head of the instance's own weak-head-normal witness): PCUICClassificationEtaInstances.whnf_classificationE_inst (sampled row S31), whnf_classification'E_inst, ind_whnf_classificationE_inst and ind_whnf_classification'E_inst, whose targets are the other 4 of the 6. Context of the demonstrations (context = a judgment argument of type list (context_decl term), empty or not by computing its length, not the lemma's Γ parameter): 79 use a non-empty context; 23 have the context as their subject; 20 have a non-empty context that no term or type mentions; 4 undecided; 70 work only at the empty context (10 forced by the statement, 60 by the instance's choice; up to 89 under stricter readings); 33 have no context argument, which is not the same as the empty context. A mechanical sweep flagged at least 31 of the 338 NONDEGEN instances at 0bf9899a, before the retags of LAND8a (eede40b7, 86d983ce), LAND9 (016ec167, 727d49e9) and LAND11-A (6568a017), whose conclusion is convertible to an input sub-derivation (3 of the 31 match the instance itself or its helper rather than an input); of its 9 non-equation flags, 9 were judged bad by 2026-10-31T03:30Z, with the kind-label correct in 6 of 9; it cannot see a cancellation inside the target lemma's own proof or a conclusion that is one part of a pair, and it does not discriminate the 22 closed equations (of the 3 sampled ones judged, S29 is weak only, S44 is not degenerate, and S31 is undemonstrable by its statement). Prose overclaims were not mechanically enumerated, because that detector failed its controls. Root rulings made by 2026-10-31T03:30Z reclassified three sampled rows that both reviews had passed, S36 (the red → conv → red class), S12 (its conclusion is the input's own cumulativity) and S31 (undemonstrable by its statement), raising the sampled rate from at least 17 to at least 20 of 60; the 45-row marker census had 2 reopened as of 2026-10-31T03:30Z. *)

(** * Satisfying instances of the lemmas of [PCUICClassificationEta] (row T6)

  **No forecast class.** The lemmas of [PCUICClassificationEta] took T1's [SRForecastCopy18]
  (copy 18b) as a premise until copy 18b landed (frac/eta 3e6b422d); the class is deleted, so the
  instances below, in section [ClassificationEtaInstances] (which held it), apply the lemmas with
  no class. Every derivation each instance needs is built here or taken from the landed instance
  files.

  **The environments** are [si_Σ] ([PCUICCumulativitySpecEtaClosureInstances]:
  [Inductive I (A : Prop) : Prop := c : I A]) and [iv_Σ] ([PCUICInversionEtaInstances]: the
  [CoFinite] record [R]).

  **Non-degeneracy.** The tag at each instance names the lemma that states why it is more than
  a trivial case, the reason it cannot be (IMPOSSIBLE), or why the instance is degenerate while no
  non-degenerate witness is built yet (NOT-BUILT).
  - The arity corollaries (Class A' rows) and [isArity_typing_spineE] run on the type
    [cli_T := Π _ : Prop. z] in the context [z := Prop : Type] ([cli_Γz]): [cli_T] is not an
    arity ([cli_T_not_arity]; its codomain is the variable [z]), and unfolding [z] reduces it in
    one step to the arity [Prop → Prop] ([cli_T_red], [cli_T_closed_red]). i20
    ([invert_cumul_arity_rE_inst]) and i21 ([invert_cumul_arity_lE_inst]) take [cli_T] with a
    cumulativity to or from [Prop → Prop] ([cli_ws_r], [cli_ws_l]); x2, x3 and
    [isArity_typing_spineE] take it the same way. All five are tagged NOT-BUILT: [cli_ws_r] and
    [cli_ws_l] are the reduction [cli_T_closed_red] forgotten, so each conclusion
    [Is_conv_to_Arity si_Σ cli_Γz cli_T] is inhabited by [Prop → Prop] with that reduction (a
    round trip red → cumul → red, under the squash), and the T8 sites of i20's proof ([Prod_r]
    on [cli_T], [Sort_r] on [z]) and of i21's ([PCUICPrincipalityEta.T8_Prod_l_plug],
    [T8_Sort_l_plug], the [_l] forms derived from the proved [_r] ones) only recover the δ step
    of [z] that the input was built from; no non-degenerate witness is built yet.
  - The (co)fixpoint witness lemmas run on declared types on which the check FAILS:
    [bdf_fxty 0] (domain the β-redex [(λ B. I B) A], [bdf_check_fix_dtypeβ]) and [bdf_RFβ]
    (the β-redex [(λ B. R B) (∀P. P)], [bdf_check_cofix_dtypeβ]); the typed-reduct route
    finds the reduct on which it passes. [wf_fixpoint_spineE_inst] and
    [wf_cofixpoint_spineE_inst] are tagged NOT-BUILT: the conversions of [bdf_wf_fix] and
    [bdf_wf_cofix] are reductions of the declared types, forgotten, so the reduct each obtains is
    that reduction (inside the proof, for wf_fixpoint_spineE_inst) (a round trip), and the rest
    of each conclusion is carried from the input (the argument [cli_cA], typed at the β-redex
    domain by a forgotten β step from [I A], is typed back at [I A]; the cofixpoint's spine is
    empty).
  - [typing_cofix_coindE_inst], tagged NOT-BUILT: a cofixpoint whose declared type is the
    β-redex [bdf_RFβ], typed at [R (∀P. P)] by a forgotten reduction ([cli_cofix_typed_R]); its
    [wf_cofixpointE] is [bdf_wf_cofix], built from the same reduction, so the cumulativity the
    target inverts cancels and its conclusion is the [ok] field of [bdf_wf_cofix].
  - [typing_spine_all_invE_inst] runs on the empty spine of [let z := ∀P:Prop. P in z → z]
    ([cli_let_arrow]) at itself: the substitution [z := ∀P. P] into [z → z] gives
    [(∀P. P) → (∀P. P)], which is neither the substituted [∀P. P], nor the body, nor the compared
    let-in ([cli_all_inv_let_nondeg]).
    [typing_spine_nth_errorE_inst] reads the type of the second argument [c (∀P. P)] of
    [Π x : Prop. Π y : I x. I x] ([cli_depI_ty]) applied to [(λx:Prop. x) (∀P. P)]: its declared
    type [I x] at that [x] is [I ((λx:Prop. x) (∀P. P))], while the spine ([cli_depI_sp_fwd])
    types [c (∀P. P)] only at its own type [I (∀P. P)] and reduces the type it reaches there
    forward to the product [Π y : I (∀P. P). I (∀P. P)]; the lemma applies that conversion,
    turned around, to the argument ([cli_depI_nth_fwd_nondeg]). The two [None] spine lemmas end
    at the let-in [let z := I (∀P. P) in Π y : z. z] ([cli_dep_let]), not a product, after one
    argument [I (∀P. P)]. [typing_spine_nth_error_NoneE_inst] runs on
    [Π x : Prop. Π y : x. (λw:Prop. w) x] ([cli_dep_ty_id]); its spine ([cli_dep_id_sp_let]) reduces
    [cli_dep_ty_id] forward to [Π x : Prop. Π y : x. x] ([cli_dep_ty]) and relates its tail
    [Π y : I (∀P. P). I (∀P. P)] to [cli_dep_let] by the ζ step; the lemma composes the two steps
    into [Π y : I (∀P. P). (λw:Prop. w) (I (∀P. P)) ≤ cli_dep_let], which no premise states
    ([cli_dep_id_none_nondeg]). [typing_spine_nth_error_None_prodE_inst] runs on
    [Π x : Prop. Π y : (λw:Prop. w) x. (λw:Prop. w) ((λw:Prop. w) x)] ([cli_idx_ty]), whose spine
    ([cli_idx_sp_let]) relates no product to [cli_dep_let]: its tail starts at the let-in
    [let z := (λw:Prop. w) (I (∀P. P)) : Prop in Π y : z. z] and reaches [cli_dep_let] by the β step
    in the definiens; the product the lemma returns below [cli_dep_let] comes only from its
    composition with the cons step ([cli_idx_prod_nondeg]).
    [typing_spine_smashE_inst] runs on the empty spine of [cli_dep_let] at
    itself: smashing drops the let and substitutes [z := I (∀P. P)] into [Π y : z. z], giving
    [Π y : I (∀P. P). I (∀P. P)], neither the substituted term, nor the body, nor [cli_dep_let]
    ([cli_smash_dep_nondeg]). [cumul_it_mkProd_or_LetIn_smashE_inst] relates the same smashed type
    [Π y : I (∀P. P). I (∀P. P)] to [cli_dep_let] ([cli_smash_dep_nondeg]).
  - [arity_spine_len_subst_inst] substitutes [∀P. P] for the free variable [x] of the arity
    [let z := x : Prop in Π _ : x. Prop] ([cli_open_arity]), which changes the term
    ([cli_open_arity_subst_differs]); [x] occurs in the let body and in the product domain.
  - Evaluation: [subject_reduction_evalE_inst], [eval_closed_cb_inst], [eval_whneE_inst] and
    [wcbveval_redE_inst] run on [cli_eval_xx], the evaluation of [(λx:Prop. x → x) (∀P. P)] to
    [(∀P. P) → (∀P. P)], whose body uses its variable ([PCUICSREtaInstances.sri_xx_nondeg],
    [cli_eval_xx_nondeg]). [eval_whneE_inst] is tagged NOT-BUILT: the value of that result is a
    product, so [value_whnfE] takes its atom branch and the closedness from [eval_closed_cb] is
    unused.
  - [value_whnfE_inst] is tagged NOT-BUILT (on [c (∀P. P)] the value derivation is translated
    constructor by constructor; only a stuck fixpoint application uses the closedness premise),
    and [value_classificationE_inst] and [eval_classificationE_inst] are tagged IMPOSSIBLE (the
    conclusion is computed from the head of the instance's own value or evaluation result;
    everything else in their proofs refutes). [fix_app_is_constructorE_inst] is tagged NOT-BUILT:
    its recursive argument is present ([cli_fix_rarg_present]), so its conclusion is the branch
    whose left disjunct [isConstruct_app (c (∀P. P))] computes to [true]. The four whnf
    classification rows on the same term
    ([whnf_classificationE_inst], [whnf_classification'E_inst], [ind_whnf_classificationE_inst],
    [ind_whnf_classification'E_inst]) are tagged IMPOSSIBLE: on every instance whose premises
    hold, the conclusion is read off the instance's own [wh_normal] derivation: the head by
    computation, or, for a neutral term, its [whne] derivation translated into [stuck_cofix_case]
    ([wh_neutral_emptyE]).
  - The rows whose conclusion is [False] (the lemma states that its premises cannot hold
    together; as in base) and the rows whose conclusion relates a term to itself
    ([check_recursivity_kind_injE]: [rk = rk']; [wt_closed_red_reflE]: [Σ ;;; Γ ⊢ t ⇝ t], whose
    closedness side conditions compute on any concrete context and term and are not a
    non-degeneracy) have instances tagged IMPOSSIBLE, with the reason in the tag.
    [wh_neutral_empty_genE] and [wh_neutral_emptyE] are no longer in that row: since BET-339
    they conclude [stuck_cofix_case t]; their instances are in
    [PCUICEtaF0Land3Instances] (reason at the place their instances stood).

  - BET-339: the disjunct [stuck_cofix_case] that [whnf_classification'E],
    [whnf_classificationE], [ind_whnf_classification'E], [ind_whnf_classificationE] and
    [fix_app_is_constructorE] gained is reached by [PCUICEtaF0Land3Instances]
    ([g_whnf_classification_stuck], on a closed case blocked on a cofixpoint); the instances
    here land in the constructor disjunct: their subject [c (∀P. P)] is no blocked case
    ([PCUICEtaF0Land3Instances.l6_cF_not_stuck]).

  **Rows without an instance.**
  - Refutations ([invert_cumul_arity_lE_untyped_false], [invert_cumul_arity_rE_untyped_false]):
    theorems, not hypotheses; no instance applies.
  - Helpers run by the instances above: [T8_Sort_l_plug], [PCUICPrincipalityEta.T8_Prod_l_plug]
    and [PCUICPrincipalityEta.chain_ws_cumul_pbE_Conv] (inside i21's instance; their own
    instances are in [PCUICPrincipalityEtaInstances]), [arity_spine_len] and
    [arity_spine_len_subst] (inside i20's and i21's; [arity_spine_len_subst_inst] too). *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICReduction PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICClosedBodies PCUICTypingEta
     PCUICTypingEtaInd PCUICTypingEtaNotions PCUICCumulativitySpecEtaClosureInstances PCUICEtaDefs
     PCUICEtaI5 PCUICWellScopedCumulativity PCUICWellScopedCumulativityEta PCUICEtaA6 PCUICEquality
     PCUICConversionEtaCongr PCUICEtaFInst PCUICClosedTypEta PCUICWsCumulEtaCtxTyp
     PCUICInversionEtaInstances PCUICWcbvEval PCUICNormal PCUICConversion PCUICContextConversion
     PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICSpineEta PCUICValidityEta PCUICSREta
     PCUICSREtaInstances BDTypingEtaInstances BDFromPCUICEtaInstances PCUICClassification PCUICClassificationEta.
From MetaRocq.PCUIC Require PCUICWfUniverses PCUICEtaI5A2.
From Equations.Type Require Import Relation.

(* The derivations the instances use, and the facts their tags name.
   WITNESSES: cli_* *)

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.
#[local] Existing Instance si_wfE.
#[local] Existing Instance iv_wfE.
#[local] Instance cli_iv_cb : ClosedBodies iv_env := @wfE_ClosedBodies _ iv_env iv_wfE.

(** ** Derivations, without any class *)

(** The context [z := Prop : Type]. *)
Definition cli_Γz : context := [vdef si_na si_P (tSort (Sort.super sProp))].

Lemma cli_Type_typed (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ |-E tSort (Sort.super sProp) : tSort (Sort.super (Sort.super sProp)).
Proof. intros h. apply typeE_Sort; [exact h|apply PCUICWfUniverses.wf_sort_super; cbn; trivial]. Qed.

Lemma cli_wf_Γz : wf_localE si_Σ cli_Γz.
Proof.
  apply localenv_cons_def; [constructor|].
  exact (iv_vdef si_Σ [] si_na si_P (tSort (Sort.super sProp)) _ (iv_P_typed si_Σ [] localenv_nil)
           (cli_Type_typed [] localenv_nil) eq_refl).
Qed.

(** [Π _ : Prop. z]: not an arity; it reduces to the arity [Prop → Prop] by unfolding [z]. *)
Definition cli_T : term := tProd si_na si_P (tRel 1).

Lemma cli_T_typed :
  si_Σ ;;; cli_Γz |-E cli_T : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)).
Proof.
  apply typeE_Prod.
  - exact (iv_vass_s si_Σ cli_Γz si_na si_P _ (iv_P_typed si_Σ cli_Γz cli_wf_Γz) eq_refl).
  - exact (typeE_Rel _ _ 1 (vdef si_na si_P (tSort (Sort.super sProp))) (iv_wf_P si_Σ cli_Γz cli_wf_Γz) eq_refl).
Qed.

Lemma cli_T_isType : isTypeE si_Σ cli_Γz cli_T.
Proof. exact (has_sort_isTypeE _ cli_T_typed). Qed.

Lemma cli_PP_isType : isTypeE si_Σ cli_Γz iv_PP.
Proof. exact (has_sort_isTypeE _ (iv_PP_typed si_Σ cli_Γz cli_wf_Γz)). Qed.

Lemma cli_T_not_arity : isArity cli_T = false.
Proof. reflexivity. Qed.

Lemma cli_T_red : red1 si_Σ cli_Γz cli_T iv_PP.
Proof. apply prod_red_r. exact (red_rel si_Σ (cli_Γz ,, vass si_na si_P) 1 si_P eq_refl). Qed.

Lemma cli_T_closed_red : si_Σ ;;; cli_Γz ⊢ cli_T ⇝ iv_PP.
Proof. exact (closed_red_of (Σ := si_Σ) (Γ := cli_Γz) (t := cli_T) eq_refl eq_refl (red1_red _ _ _ _ cli_T_red)). Qed.

Lemma cli_ws_r : ws_cumul_pbE Cumul si_Σ cli_Γz cli_T iv_PP.
Proof. exact (red_ws_cumul_pbE (Σ := si_Σ) cli_T_closed_red). Qed.

Lemma cli_ws_l : ws_cumul_pbE Cumul si_Σ cli_Γz iv_PP cli_T.
Proof. exact (red_ws_cumul_pbE_inv (Σ := si_Σ) cli_T_closed_red). Qed.

Lemma cli_PP_conv : Is_conv_to_Arity si_Σ cli_Γz iv_PP.
Proof.
  exists iv_PP. split; [|reflexivity]. sq.
  exact (closed_red_refl (Σ := si_Σ) cli_Γz iv_PP eq_refl eq_refl).
Qed.

(** [∀P:Prop. P] is a type, and is below itself. *)
Lemma cli_False_isType (Γ : context) : wf_localE si_Σ Γ -> isTypeE si_Σ Γ iv_False.
Proof. intros h. exact (has_sort_isTypeE _ (iv_False_typed si_Σ Γ h)). Qed.

Lemma cli_False_refl (Γ : context) : wf_localE si_Σ Γ -> ws_cumul_pbE Cumul si_Σ Γ iv_False iv_False.
Proof. intros h. exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) Γ iv_False (cli_False_isType Γ h)). Qed.

(** [let z := ∀P:Prop. P : Prop in z → z]: the let-bound [z] occurs in the domain and the codomain
    of the body. *)
Definition cli_let_arrow : term := tLetIn si_na iv_False si_P (tProd si_na (tRel 0) (tRel 1)).

Lemma cli_zF_typed : si_Σ ;;; [vdef si_na iv_False si_P] |-E tRel 0 : si_P.
Proof. exact (typeE_Rel _ _ 0 (vdef si_na iv_False si_P) (iv_wf_vdef si_Σ [] localenv_nil) eq_refl). Qed.

Lemma cli_wf_zFy : wf_localE si_Σ [vass si_na (tRel 0); vdef si_na iv_False si_P].
Proof. exact (iv_wf_vass si_Σ _ si_na (tRel 0) sProp (iv_wf_vdef si_Σ [] localenv_nil) cli_zF_typed eq_refl). Qed.

Lemma cli_let_arrow_typed : si_Σ ;;; [] |-E cli_let_arrow : tSort sProp.
Proof.
  eapply (typeE_Cumul _ _ cli_let_arrow (tLetIn si_na iv_False si_P si_P) si_P (Sort.super sProp)).
  - apply typeE_LetIn.
    + exact (iv_vdef si_Σ [] si_na iv_False si_P _ (iv_False_typed si_Σ [] localenv_nil)
               (iv_P_typed si_Σ [] localenv_nil) eq_refl).
    + exact (typeE_Prod _ _ si_na (tRel 0) (tRel 1) sProp sProp
               (iv_vass_s si_Σ _ si_na (tRel 0) sProp cli_zF_typed eq_refl)
               (typeE_Rel _ _ 1 (vdef si_na iv_False si_P) cli_wf_zFy eq_refl)).
  - exact (iv_P_typed si_Σ [] localenv_nil).
  - apply (ws_cumul_pbE_forget_spec (pb := Cumul)).
    apply (red_ws_cumul_pbE (Σ := si_Σ)).
    exact (closed_red_of (Σ := si_Σ) (Γ := []) (t := tLetIn si_na iv_False si_P si_P) eq_refl eq_refl
             (red1_red _ _ _ _ (red_zeta _ _ si_na iv_False si_P si_P))).
Qed.

Lemma cli_let_arrow_isType : isTypeE si_Σ [] cli_let_arrow.
Proof. exact (has_sort_isTypeE _ cli_let_arrow_typed). Qed.

(** The empty spine of [cli_let_arrow] at itself (reflexive: it holds no ζ step). *)
Lemma cli_let_arrow_sp_nil : PCUICAritiesEta.typing_spineE si_Σ [] cli_let_arrow [] cli_let_arrow.
Proof.
  econstructor; [exact cli_let_arrow_isType|exact cli_let_arrow_isType|].
  exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) [] cli_let_arrow cli_let_arrow_isType).
Qed.

(** [typing_spine_all_invE] on [cli_let_arrow] ([Δ = [z := ∀P. P : Prop]], [T = z → z], no
    argument): the substitution [z := ∀P. P] into [z → z] gives [(∀P. P) → (∀P. P)], which is not
    the substituted [∀P. P], not the body [z → z], and not the compared type [cli_let_arrow]. *)
Lemma cli_all_inv_let_nondeg :
  #|@nil term| = context_assumptions [vdef si_na iv_False si_P] /\
  subst (List.rev (@nil term)) 0 (expand_lets [vdef si_na iv_False si_P] (tProd si_na (tRel 0) (tRel 1))) =
    tProd si_na iv_False iv_False /\
  tProd si_na iv_False iv_False <> iv_False /\
  tProd si_na iv_False iv_False <> tProd si_na (tRel 0) (tRel 1) /\
  tProd si_na iv_False iv_False <> cli_let_arrow.
Proof.
  split; [reflexivity|]. split; [vm_compute; reflexivity|].
  split; [|split]; intros h; vm_compute in h; discriminate h.
Qed.

(** The dependent type [Π x : Prop. Π y : x. x] ([it_mkProd_or_LetIn cli_dep_Δ (tRel 1)]): the
    declared type of its second argument is the first argument. *)
Definition cli_dep_Δ : context := [vass si_na (tRel 0); vass si_na si_P].
Definition cli_dep_ty : term := tProd si_na si_P (tProd si_na (tRel 0) (tRel 1)).

Lemma cli_dep_x_typed : si_Σ ;;; [vass si_na si_P] |-E tRel 0 : si_P.
Proof. exact (typeE_Rel _ _ 0 (vass si_na si_P) (iv_wf_P si_Σ [] localenv_nil) eq_refl). Qed.

Lemma cli_wf_dep : wf_localE si_Σ cli_dep_Δ.
Proof. exact (iv_wf_vass si_Σ [vass si_na si_P] si_na (tRel 0) sProp (iv_wf_P si_Σ [] localenv_nil) cli_dep_x_typed eq_refl). Qed.

Lemma cli_dep_ass : assumption_context cli_dep_Δ.
Proof. repeat constructor. Qed.

Lemma cli_dep_ty_typed : si_Σ ;;; [] |-E cli_dep_ty : si_P.
Proof.
  exact (typeE_Prod _ _ si_na si_P (tProd si_na (tRel 0) (tRel 1)) (Sort.super sProp) sProp
           (iv_vass_s si_Σ [] si_na si_P _ (iv_P_typed si_Σ [] localenv_nil) eq_refl)
           (typeE_Prod _ _ si_na (tRel 0) (tRel 1) sProp sProp
              (iv_vass_s si_Σ [vass si_na si_P] si_na (tRel 0) sProp cli_dep_x_typed eq_refl)
              (typeE_Rel _ _ 1 (vass si_na si_P) cli_wf_dep eq_refl))).
Qed.

Lemma cli_dep_isType : isTypeE si_Σ [] cli_dep_ty.
Proof. exact (has_sort_isTypeE _ cli_dep_ty_typed). Qed.

Lemma cli_IF_isType : isTypeE si_Σ [] iv_IF.
Proof. exact (has_sort_isTypeE _ (iv_IF_typed [] localenv_nil)). Qed.

Lemma cli_fixty_isType : isTypeE si_Σ [] iv_fix_ty.
Proof. exact (has_sort_isTypeE _ (iv_fix_ty_typed [] localenv_nil)). Qed.

(** [Π x : Prop. Π y : I x. I x] ([it_mkProd_or_LetIn cli_depI_Δ (iv_Ix 1)]): the declared type
    [I x] of its second argument mentions the first. *)
Definition cli_depI_Δ : context := [vass si_na (iv_Ix 0); vass si_na si_P].
Definition cli_depI_ty : term := tProd si_na si_P (tProd si_na (iv_Ix 0) (iv_Ix 1)).

Lemma cli_Ix_typed : si_Σ ;;; [vass si_na si_P] |-E iv_Ix 0 : si_P.
Proof. exact (iv_IX_typed [vass si_na si_P] (tRel 0) (iv_wf_P si_Σ [] localenv_nil) cli_dep_x_typed). Qed.

Lemma cli_wf_depI : wf_localE si_Σ cli_depI_Δ.
Proof.
  exact (iv_wf_vass si_Σ [vass si_na si_P] si_na (iv_Ix 0) sProp (iv_wf_P si_Σ [] localenv_nil) cli_Ix_typed
           eq_refl).
Qed.

Lemma cli_depI_ass : assumption_context cli_depI_Δ.
Proof. repeat constructor. Qed.

Lemma cli_depI_ty_typed : si_Σ ;;; [] |-E cli_depI_ty : si_P.
Proof.
  exact (typeE_Prod _ _ si_na si_P (tProd si_na (iv_Ix 0) (iv_Ix 1)) (Sort.super sProp) sProp
           (iv_vass_s si_Σ [] si_na si_P _ (iv_P_typed si_Σ [] localenv_nil) eq_refl)
           (typeE_Prod _ _ si_na (iv_Ix 0) (iv_Ix 1) sProp sProp
              (iv_vass_s si_Σ [vass si_na si_P] si_na (iv_Ix 0) sProp cli_Ix_typed eq_refl)
              (iv_IX_typed cli_depI_Δ (tRel 1) cli_wf_depI
                 (typeE_Rel _ _ 1 (vass si_na si_P) cli_wf_depI eq_refl)))).
Qed.

Lemma cli_depI_isType : isTypeE si_Σ [] cli_depI_ty.
Proof. exact (has_sort_isTypeE _ cli_depI_ty_typed). Qed.

(** [I ((λx:Prop. x) (∀P. P))]: the inductive applied to a β-redex; it β-reduces to [I (∀P. P)]. *)
Definition cli_IidF : term := tApp (tInd si_ind []) (tApp iv_id iv_False).

Lemma cli_IidF_typed : si_Σ ;;; [] |-E cli_IidF : si_P.
Proof. exact (iv_IX_typed [] (tApp iv_id iv_False) localenv_nil (iv_app_typed si_Σ [] localenv_nil)). Qed.

Lemma cli_IidF_red1 : red1 si_Σ [] cli_IidF iv_IF.
Proof. exact (app_red_r _ _ _ _ _ (red_beta _ _ si_na si_P (tRel 0) iv_False)). Qed.

(** [Π y : I ((λx:Prop. x) (∀P. P)). I ((λx:Prop. x) (∀P. P))]: [Π y : I x. I x] at
    [x := (λx:Prop. x) (∀P. P)], the type [cli_depI_ty] reaches after its first argument. *)
Definition cli_IidF_arr : term := tProd si_na cli_IidF cli_IidF.

Lemma cli_IidF_arr_isType : isTypeE si_Σ [] cli_IidF_arr.
Proof.
  have w := iv_wf_vass si_Σ [] si_na cli_IidF sProp localenv_nil cli_IidF_typed eq_refl.
  apply has_sort_isTypeE with (s := Sort.sort_of_product sProp sProp).
  apply typeE_Prod.
  - exact (iv_vass_s si_Σ [] si_na cli_IidF sProp cli_IidF_typed eq_refl).
  - exact (iv_IX_typed _ (tApp iv_id iv_False) w (iv_app_typed si_Σ _ w)).
Qed.

(** [cli_IidF_arr] reduces FORWARD to [Π y : I (∀P. P). I (∀P. P)] ([iv_fix_ty]): the β step
    [cli_IidF_red1] in the domain, then the same β-redex in the codomain. *)
Lemma cli_IidF_arr_red : red si_Σ [] cli_IidF_arr iv_fix_ty.
Proof.
  unfold cli_IidF_arr, iv_fix_ty.
  apply (red_trans _ _ _ (tProd si_na iv_IF cli_IidF)); apply red1_red.
  - apply prod_red_l. exact cli_IidF_red1.
  - apply prod_red_r. exact (app_red_r _ _ _ _ _ (red_beta _ _ si_na si_P (tRel 0) iv_False)).
Qed.

(** [cli_IidF_arr ≤ iv_fix_ty], from the forward reduction [cli_IidF_arr_red]: not reflexive, and
    no step taken backwards. *)
Lemma cli_IidF_arr_ws : ws_cumul_pbE Cumul si_Σ [] cli_IidF_arr iv_fix_ty.
Proof.
  apply (red_ws_cumul_pbE (Σ := si_Σ)).
  exact (closed_red_of (Σ := si_Σ) (Γ := []) (t := cli_IidF_arr) eq_refl eq_refl cli_IidF_arr_red).
Qed.

(** [cli_depI_ty] applied to [(λx:Prop. x) (∀P. P)] and [c (∀P. P)]. At the second argument the
    spine reaches [cli_IidF_arr], reduces it forward to the product [iv_fix_ty] ([cli_IidF_arr_ws]),
    and takes [c (∀P. P)] at that product's domain [I (∀P. P)] by [sri_cF_typed], the typing of
    [c] applied to [∀P. P], with no cumulativity. *)
Lemma cli_depI_sp_fwd :
  PCUICAritiesEta.typing_spineE si_Σ [] cli_depI_ty [tApp iv_id iv_False; sri_cF] iv_IF.
Proof.
  eapply (@PCUICAritiesEta.type_spine_consE _ _ _ cli_depI_ty (tApp iv_id iv_False) [sri_cF] si_na si_P
            (tProd si_na (iv_Ix 0) (iv_Ix 1)) iv_IF).
  - exact cli_depI_isType.
  - exact cli_depI_isType.
  - exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) [] cli_depI_ty cli_depI_isType).
  - exact (iv_app_typed si_Σ [] localenv_nil).
  - eapply (@PCUICAritiesEta.type_spine_consE _ _ _ cli_IidF_arr sri_cF [] si_na iv_IF iv_IF iv_IF).
    + exact cli_IidF_arr_isType.
    + exact cli_fixty_isType.
    + exact cli_IidF_arr_ws.
    + exact sri_cF_typed.
    + econstructor; [exact cli_IF_isType|exact cli_IF_isType|].
      exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) [] iv_IF cli_IF_isType).
Qed.

(** [typing_spine_nth_errorE] at the second argument [c (∀P. P)] of [cli_depI_ty] applied to
    [(λx:Prop. x) (∀P. P)]. The lemma concludes [c (∀P. P) : I ((λx:Prop. x) (∀P. P))]: the declared
    type [I x] at [x := (λx:Prop. x) (∀P. P)] ([cli_IidF]). The spine [cli_depI_sp_fwd] types
    [c (∀P. P)] only at [I (∀P. P)] ([sri_cF_typed]: the codomain [I A] of the type of [c] at
    [A := ∀P. P]), which is not [cli_IidF] and does not reduce to it: the concluded typing is in
    no premise, at any depth, and no reduction of a premise's type gives it.
    At that argument the spine reaches [Π y : I x. I x] at the same [x] ([cli_IidF_arr]) and its
    cumulativity reduces that type FORWARD to the product [iv_fix_ty] whose domain types the
    argument: no step of the spine is taken backwards. The lemma inverts that product cumulativity
    and applies the domain conversion, turned around, to [sri_cF_typed]: a β-expansion of a typing
    that was not built from the conclusion, so the composition does not cancel. *)
Lemma cli_depI_nth_fwd_nondeg :
  nth_error (List.rev cli_depI_Δ) 1 = Some (vass si_na (iv_Ix 0)) /\
  subst (List.rev (firstn 1 [tApp iv_id iv_False; sri_cF])) 0 (iv_Ix 0) = cli_IidF /\
  subst10 iv_False (iv_Ix 0) = iv_IF /\
  cli_IidF <> iv_IF /\ ((si_Σ ;;; [] ⊢ iv_IF ⇝ cli_IidF) -> False) /\
  subst10 (tApp iv_id iv_False) (tProd si_na (iv_Ix 0) (iv_Ix 1)) = cli_IidF_arr /\
  cli_IidF_arr <> iv_fix_ty /\ ∥ red si_Σ [] cli_IidF_arr iv_fix_ty ∥.
Proof.
  split; [reflexivity|]. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [intros h; vm_compute in h; discriminate h|].
  split.
  { intros r.
    destruct (invert_red_mkApps_tInd_cb (ind := si_ind) (u := []) [iv_False] _ r) as [args' [e _ a]].
    apply (f_equal decompose_app) in e.
    rewrite (decompose_app_mkApps (tInd si_ind []) args' eq_refl) in e.
    vm_compute in e. injection e. intros; subst.
    inversion a; subst.
    match goal with c : closed_red _ _ _ _ |- _ =>
      destruct (invert_red_prod_cb c) as [d [cd [e2 _ _]]]; discriminate e2 end. }
  split; [vm_compute; reflexivity|].
  split; [intros h; vm_compute in h; discriminate h|].
  constructor; exact cli_IidF_arr_red.
Qed.

(** [let z := I (∀P. P) : Prop in Π y : z. z]: it ζ-reduces to [Π y : I (∀P. P). I (∀P. P)]
    ([iv_fix_ty]), and is not a product. *)
Definition cli_dep_let : term := tLetIn si_na iv_IF si_P (tProd si_na (tRel 0) (tRel 1)).

Lemma cli_wf_z : wf_localE si_Σ [vdef si_na iv_IF si_P].
Proof.
  apply localenv_cons_def; [constructor|].
  exact (iv_vdef si_Σ [] si_na iv_IF si_P _ (iv_IF_typed [] localenv_nil) (iv_P_typed si_Σ [] localenv_nil) eq_refl).
Qed.

Lemma cli_z_typed : si_Σ ;;; [vdef si_na iv_IF si_P] |-E tRel 0 : si_P.
Proof. exact (typeE_Rel _ _ 0 (vdef si_na iv_IF si_P) cli_wf_z eq_refl). Qed.

Lemma cli_wf_zy : wf_localE si_Σ [vass si_na (tRel 0); vdef si_na iv_IF si_P].
Proof. exact (iv_wf_vass si_Σ _ si_na (tRel 0) sProp cli_wf_z cli_z_typed eq_refl). Qed.

Lemma cli_dep_let_typed : si_Σ ;;; [] |-E cli_dep_let : tSort sProp.
Proof.
  eapply (typeE_Cumul _ _ cli_dep_let (tLetIn si_na iv_IF si_P si_P) si_P (Sort.super sProp)).
  - apply typeE_LetIn.
    + exact (iv_vdef si_Σ [] si_na iv_IF si_P _ (iv_IF_typed [] localenv_nil) (iv_P_typed si_Σ [] localenv_nil) eq_refl).
    + exact (typeE_Prod _ _ si_na (tRel 0) (tRel 1) sProp sProp
               (iv_vass_s si_Σ _ si_na (tRel 0) sProp cli_z_typed eq_refl)
               (typeE_Rel _ _ 1 (vdef si_na iv_IF si_P) cli_wf_zy eq_refl)).
  - exact (iv_P_typed si_Σ [] localenv_nil).
  - apply (ws_cumul_pbE_forget_spec (pb := Cumul)).
    apply (red_ws_cumul_pbE (Σ := si_Σ)).
    exact (closed_red_of (Σ := si_Σ) (Γ := []) (t := tLetIn si_na iv_IF si_P si_P) eq_refl eq_refl
             (red1_red _ _ _ _ (red_zeta _ _ si_na iv_IF si_P si_P))).
Qed.

Lemma cli_dep_let_isType : isTypeE si_Σ [] cli_dep_let.
Proof. exact (has_sort_isTypeE _ cli_dep_let_typed). Qed.

Lemma cli_dep_let_ws : ws_cumul_pbE Cumul si_Σ [] iv_fix_ty cli_dep_let.
Proof.
  apply (red_ws_cumul_pbE_inv (Σ := si_Σ)).
  exact (closed_red_of (Σ := si_Σ) (Γ := []) (t := cli_dep_let) eq_refl eq_refl
           (red1_red _ _ _ _ (red_zeta _ _ si_na iv_IF si_P (tProd si_na (tRel 0) (tRel 1))))).
Qed.

(** [Π x : Prop. Π y : x. (λw:Prop. w) x]: [cli_dep_ty] with its codomain under a β-redex. *)
Definition cli_dep_ty_id : term := tProd si_na si_P (tProd si_na (tRel 0) (tApp iv_id (tRel 1))).

Lemma cli_dep_ty_id_typed : si_Σ ;;; [] |-E cli_dep_ty_id : si_P.
Proof.
  exact (typeE_Prod _ _ si_na si_P (tProd si_na (tRel 0) (tApp iv_id (tRel 1))) (Sort.super sProp) sProp
           (iv_vass_s si_Σ [] si_na si_P _ (iv_P_typed si_Σ [] localenv_nil) eq_refl)
           (typeE_Prod _ _ si_na (tRel 0) (tApp iv_id (tRel 1)) sProp sProp
              (iv_vass_s si_Σ [vass si_na si_P] si_na (tRel 0) sProp cli_dep_x_typed eq_refl)
              (typeE_App _ _ iv_id si_na si_P si_P _ (tRel 1) (iv_PP_typed si_Σ _ cli_wf_dep)
                 (iv_id_typed si_Σ _ cli_wf_dep) (typeE_Rel _ _ 1 (vass si_na si_P) cli_wf_dep eq_refl)))).
Qed.

Lemma cli_dep_ty_id_isType : isTypeE si_Σ [] cli_dep_ty_id.
Proof. exact (has_sort_isTypeE _ cli_dep_ty_id_typed). Qed.

Lemma cli_dep_ty_id_red1 : red1 si_Σ [] cli_dep_ty_id cli_dep_ty.
Proof.
  unfold cli_dep_ty_id, cli_dep_ty. apply prod_red_r. apply prod_red_r.
  exact (red_beta _ _ si_na si_P (tRel 0) (tRel 1)).
Qed.

(** [cli_dep_ty_id ≤ cli_dep_ty]: the β step [cli_dep_ty_id_red1] in the codomain, FORWARD; not
    reflexive. *)
Lemma cli_dep_ty_id_ws : ws_cumul_pbE Cumul si_Σ [] cli_dep_ty_id cli_dep_ty.
Proof.
  apply (red_ws_cumul_pbE (Σ := si_Σ)).
  exact (closed_red_of (Σ := si_Σ) (Γ := []) (t := cli_dep_ty_id) eq_refl eq_refl
           (red1_red _ _ _ _ cli_dep_ty_id_red1)).
Qed.

(** [Π y : I (∀P. P). (λw:Prop. w) (I (∀P. P))]: the codomain of [cli_dep_ty_id] at [x := I (∀P. P)]. *)
Definition cli_fixty_id : term := tProd si_na iv_IF (tApp iv_id iv_IF).

(** [cli_dep_ty_id] ([it_mkProd_or_LetIn cli_dep_Δ ((λw:Prop. w) x)]) applied to [I (∀P. P)] only,
    at [cli_dep_let]. The cons step reduces [cli_dep_ty_id] forward to the product [cli_dep_ty]
    ([cli_dep_ty_id_ws]); the empty tail starts at [Π y : I (∀P. P). I (∀P. P)] ([iv_fix_ty]) and
    relates it to [cli_dep_let] by the ζ step of [cli_dep_let] ([cli_dep_let_ws]). *)
Lemma cli_dep_id_sp_let : PCUICAritiesEta.typing_spineE si_Σ [] cli_dep_ty_id [iv_IF] cli_dep_let.
Proof.
  eapply (@PCUICAritiesEta.type_spine_consE _ _ _ cli_dep_ty_id iv_IF [] si_na si_P
            (tProd si_na (tRel 0) (tRel 1)) cli_dep_let).
  - exact cli_dep_ty_id_isType.
  - exact cli_dep_isType.
  - exact cli_dep_ty_id_ws.
  - exact (iv_IF_typed [] localenv_nil).
  - econstructor; [exact cli_fixty_isType|exact cli_dep_let_isType|exact cli_dep_let_ws].
Qed.

(** [typing_spine_nth_error_NoneE] on [cli_dep_id_sp_let]. The returned left side, the remaining
    telescope [Π y : x. (λw:Prop. w) x] at [x := I (∀P. P)], computes to [cli_fixty_id], and the
    conclusion is [cli_fixty_id ≤ cli_dep_let]. [cli_fixty_id] is none of the four types the spine
    relates (the telescope [cli_dep_ty_id], the cons product [cli_dep_ty], the start [iv_fix_ty] of
    the empty tail, the end [cli_dep_let]), so the conclusion is in no premise, at any depth; and
    neither side of it reduces to the other, so it is no single step, forward or backward, of any
    premise. The lemma builds it from two different steps: the cons step, a β step of
    [(λw:Prop. w) x] taken FORWARD from the telescope to the product, which the lemma inverts and
    substitutes; and the tail, the ζ step of [cli_dep_let], which no step of the cons undoes. *)
Lemma cli_dep_id_none_nondeg :
  subst0 (List.rev [iv_IF])
    (it_mkProd_or_LetIn (firstn (#|cli_dep_Δ| - #|[iv_IF]|) cli_dep_Δ) (tApp iv_id (tRel 1))) =
    cli_fixty_id /\
  subst10 iv_IF (tProd si_na (tRel 0) (tRel 1)) = iv_fix_ty /\
  cli_fixty_id <> cli_dep_ty_id /\ cli_fixty_id <> cli_dep_ty /\
  cli_fixty_id <> iv_fix_ty /\ cli_fixty_id <> cli_dep_let /\
  ((si_Σ ;;; [] ⊢ cli_fixty_id ⇝ cli_dep_let) -> False) /\
  ((si_Σ ;;; [] ⊢ cli_dep_let ⇝ cli_fixty_id) -> False) /\
  ∥ red1 si_Σ [] cli_dep_ty_id cli_dep_ty ∥ /\ ∥ red1 si_Σ [] cli_dep_let iv_fix_ty ∥.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [intros h; vm_compute in h; discriminate h|].
  split; [intros h; vm_compute in h; discriminate h|].
  split; [intros h; vm_compute in h; discriminate h|].
  split; [intros h; vm_compute in h; discriminate h|].
  split.
  { intros r. destruct (invert_red_prod_cb r) as [d [cd [e _ _]]].
    unfold cli_dep_let in e. discriminate e. }
  split.
  { intros r. destruct (invert_red_letin_cb r) as [[d' [ty' [b' [e _ _ _]]]]|r'].
    - unfold cli_fixty_id in e. discriminate e.
    - destruct (invert_red_prod_cb r') as [d [cd [e _ rc]]].
      vm_compute in e. injection e. intros; subst.
      destruct (invert_red_mkApps_tInd_cb (ind := si_ind) (u := []) [iv_False] _ rc) as [args' [e2 _ _]].
      apply (f_equal decompose_app) in e2.
      rewrite (decompose_app_mkApps (tInd si_ind []) args' eq_refl) in e2.
      vm_compute in e2. discriminate e2. }
  split; [constructor; exact cli_dep_ty_id_red1|].
  constructor; exact (red_zeta _ _ si_na iv_IF si_P (tProd si_na (tRel 0) (tRel 1))).
Qed.

(** [(λw:Prop. w) x] in the context [x : Prop]. *)
Definition cli_idx : term := tApp iv_id (tRel 0).

Lemma cli_idx_typed : si_Σ ;;; [vass si_na si_P] |-E cli_idx : si_P.
Proof.
  have w := iv_wf_P si_Σ [] localenv_nil.
  exact (typeE_App _ _ iv_id si_na si_P si_P _ (tRel 0) (iv_PP_typed si_Σ _ w) (iv_id_typed si_Σ _ w)
           cli_dep_x_typed).
Qed.

(** The telescope [Π x : Prop. Π y : (λw:Prop. w) x. (λw:Prop. w) ((λw:Prop. w) x)]
    ([it_mkProd_or_LetIn cli_idx_Δ cli_idx_body]). *)
Definition cli_idx_Δ : context := [vass si_na cli_idx; vass si_na si_P].
Definition cli_idx_body : term := tApp iv_id (tApp iv_id (tRel 1)).
Definition cli_idx_ty : term := tProd si_na si_P (tProd si_na cli_idx cli_idx_body).

Lemma cli_wf_idx : wf_localE si_Σ cli_idx_Δ.
Proof.
  exact (iv_wf_vass si_Σ [vass si_na si_P] si_na cli_idx sProp (iv_wf_P si_Σ [] localenv_nil) cli_idx_typed
           eq_refl).
Qed.

Lemma cli_idx_ass : assumption_context cli_idx_Δ.
Proof. repeat constructor. Qed.

Lemma cli_idx_ty_typed : si_Σ ;;; [] |-E cli_idx_ty : si_P.
Proof.
  have hx := typeE_Rel _ _ 1 (vass si_na si_P) cli_wf_idx eq_refl.
  have hidx := typeE_App _ _ iv_id si_na si_P si_P _ (tRel 1) (iv_PP_typed si_Σ _ cli_wf_idx)
                 (iv_id_typed si_Σ _ cli_wf_idx) hx.
  exact (typeE_Prod _ _ si_na si_P (tProd si_na cli_idx cli_idx_body) (Sort.super sProp) sProp
           (iv_vass_s si_Σ [] si_na si_P _ (iv_P_typed si_Σ [] localenv_nil) eq_refl)
           (typeE_Prod _ _ si_na cli_idx cli_idx_body sProp sProp
              (iv_vass_s si_Σ [vass si_na si_P] si_na cli_idx sProp cli_idx_typed eq_refl)
              (typeE_App _ _ iv_id si_na si_P si_P _ (tApp iv_id (tRel 1)) (iv_PP_typed si_Σ _ cli_wf_idx)
                 (iv_id_typed si_Σ _ cli_wf_idx) hidx))).
Qed.

Lemma cli_idx_isType : isTypeE si_Σ [] cli_idx_ty.
Proof. exact (has_sort_isTypeE _ cli_idx_ty_typed). Qed.

(** [let z := (λw:Prop. w) x : Prop in Π y : z. z] in the context [x : Prop]: the codomain of the
    cons product of [cli_idx_sp_let]. It is a let-in, not a product. *)
Definition cli_idx_let : term := tLetIn si_na cli_idx si_P (tProd si_na (tRel 0) (tRel 1)).

Lemma cli_wf_idx_z : wf_localE si_Σ [vdef si_na cli_idx si_P; vass si_na si_P].
Proof.
  have w := iv_wf_P si_Σ [] localenv_nil.
  apply localenv_cons_def; [exact w|].
  exact (iv_vdef si_Σ [vass si_na si_P] si_na cli_idx si_P _ cli_idx_typed (iv_P_typed si_Σ _ w) eq_refl).
Qed.

Lemma cli_idx_z_typed : si_Σ ;;; [vdef si_na cli_idx si_P; vass si_na si_P] |-E tRel 0 : si_P.
Proof. exact (typeE_Rel _ _ 0 (vdef si_na cli_idx si_P) cli_wf_idx_z eq_refl). Qed.

Lemma cli_wf_idx_zy : wf_localE si_Σ [vass si_na (tRel 0); vdef si_na cli_idx si_P; vass si_na si_P].
Proof. exact (iv_wf_vass si_Σ _ si_na (tRel 0) sProp cli_wf_idx_z cli_idx_z_typed eq_refl). Qed.

Lemma cli_idx_let_typed : si_Σ ;;; [vass si_na si_P] |-E cli_idx_let : tSort sProp.
Proof.
  have w := iv_wf_P si_Σ [] localenv_nil.
  eapply (typeE_Cumul _ _ cli_idx_let (tLetIn si_na cli_idx si_P si_P) si_P (Sort.super sProp)).
  - apply typeE_LetIn.
    + exact (iv_vdef si_Σ [vass si_na si_P] si_na cli_idx si_P _ cli_idx_typed (iv_P_typed si_Σ _ w) eq_refl).
    + exact (typeE_Prod _ _ si_na (tRel 0) (tRel 1) sProp sProp
               (iv_vass_s si_Σ _ si_na (tRel 0) sProp cli_idx_z_typed eq_refl)
               (typeE_Rel _ _ 1 (vdef si_na cli_idx si_P) cli_wf_idx_zy eq_refl)).
  - exact (iv_P_typed si_Σ _ w).
  - apply (ws_cumul_pbE_forget_spec (pb := Cumul)).
    apply (red_ws_cumul_pbE (Σ := si_Σ)).
    exact (closed_red_of (Σ := si_Σ) (Γ := [vass si_na si_P]) (t := tLetIn si_na cli_idx si_P si_P) eq_refl
             eq_refl (red1_red _ _ _ _ (red_zeta _ _ si_na cli_idx si_P si_P))).
Qed.

Lemma cli_idx_let_prod_isType : isTypeE si_Σ [] (tProd si_na si_P cli_idx_let).
Proof.
  apply has_sort_isTypeE with (s := Sort.sort_of_product (Sort.super sProp) sProp).
  apply typeE_Prod.
  - exact (iv_vass_s si_Σ [] si_na si_P _ (iv_P_typed si_Σ [] localenv_nil) eq_refl).
  - exact cli_idx_let_typed.
Qed.

(** [Π y : (λw:Prop. w) x. (λw:Prop. w) x] in the context [x : Prop]: the valley of the cons step
    of [cli_idx_sp_let]. *)
Definition cli_idx_arr : term := tProd si_na cli_idx (tApp iv_id (tRel 1)).

(** The telescope reaches the valley by the OUTER β step of its codomain
    [(λw:Prop. w) ((λw:Prop. w) x)]. *)
Lemma cli_idx_ty_red1 : red1 si_Σ [] cli_idx_ty (tProd si_na si_P cli_idx_arr).
Proof.
  unfold cli_idx_ty, cli_idx_arr, cli_idx_body. apply prod_red_r. apply prod_red_r.
  exact (red_beta _ _ si_na si_P (tRel 0) (tApp iv_id (tRel 1))).
Qed.

(** The cons product reaches the valley by the ζ step of [cli_idx_let]. *)
Lemma cli_idx_let_prod_red1 : red1 si_Σ [] (tProd si_na si_P cli_idx_let) (tProd si_na si_P cli_idx_arr).
Proof.
  unfold cli_idx_let, cli_idx_arr. apply prod_red_r.
  exact (red_zeta _ _ si_na cli_idx si_P (tProd si_na (tRel 0) (tRel 1))).
Qed.

(** [cli_idx_ty ≤ Π x : Prop. cli_idx_let]: ONE join of the two different steps above at the valley
    [Π x : Prop. cli_idx_arr]; no transitivity, and neither step is the inverse of the other. *)
Lemma cli_idx_ws : ws_cumul_pbE Cumul si_Σ [] cli_idx_ty (tProd si_na si_P cli_idx_let).
Proof.
  apply (into_ws_cumul_pbE (Σ := si_Σ)); [|reflexivity|reflexivity|reflexivity].
  apply (PCUICEtaI5A2.BE_JoinE si_Σ [] Cumul cli_idx_ty (tProd si_na si_P cli_idx_let)
           (tProd si_na si_P cli_idx_arr) (tProd si_na si_P cli_idx_arr)).
  - apply BE_red. apply red1_red. exact cli_idx_ty_red1.
  - apply BE_red. apply red1_red. exact cli_idx_let_prod_red1.
  - apply PCUICEtaI5A2.RF_refl.
Qed.

(** [(λw:Prop. w) (I (∀P. P))], and [let z := (λw:Prop. w) (I (∀P. P)) : Prop in Π y : z. z], the
    start of the empty tail of [cli_idx_sp_let] ([cli_idx_let] at [x := I (∀P. P)]). *)
Definition cli_idIF : term := tApp iv_id iv_IF.
Definition cli_idIF_let : term := tLetIn si_na cli_idIF si_P (tProd si_na (tRel 0) (tRel 1)).

Lemma cli_idIF_typed : si_Σ ;;; [] |-E cli_idIF : si_P.
Proof.
  exact (typeE_App _ _ iv_id si_na si_P si_P _ iv_IF (iv_PP_typed si_Σ _ localenv_nil)
           (iv_id_typed si_Σ _ localenv_nil) (iv_IF_typed [] localenv_nil)).
Qed.

Lemma cli_wf_idIF_z : wf_localE si_Σ [vdef si_na cli_idIF si_P].
Proof.
  apply localenv_cons_def; [constructor|].
  exact (iv_vdef si_Σ [] si_na cli_idIF si_P _ cli_idIF_typed (iv_P_typed si_Σ [] localenv_nil) eq_refl).
Qed.

Lemma cli_idIF_z_typed : si_Σ ;;; [vdef si_na cli_idIF si_P] |-E tRel 0 : si_P.
Proof. exact (typeE_Rel _ _ 0 (vdef si_na cli_idIF si_P) cli_wf_idIF_z eq_refl). Qed.

Lemma cli_wf_idIF_zy : wf_localE si_Σ [vass si_na (tRel 0); vdef si_na cli_idIF si_P].
Proof. exact (iv_wf_vass si_Σ _ si_na (tRel 0) sProp cli_wf_idIF_z cli_idIF_z_typed eq_refl). Qed.

Lemma cli_idIF_let_typed : si_Σ ;;; [] |-E cli_idIF_let : tSort sProp.
Proof.
  eapply (typeE_Cumul _ _ cli_idIF_let (tLetIn si_na cli_idIF si_P si_P) si_P (Sort.super sProp)).
  - apply typeE_LetIn.
    + exact (iv_vdef si_Σ [] si_na cli_idIF si_P _ cli_idIF_typed (iv_P_typed si_Σ [] localenv_nil) eq_refl).
    + exact (typeE_Prod _ _ si_na (tRel 0) (tRel 1) sProp sProp
               (iv_vass_s si_Σ _ si_na (tRel 0) sProp cli_idIF_z_typed eq_refl)
               (typeE_Rel _ _ 1 (vdef si_na cli_idIF si_P) cli_wf_idIF_zy eq_refl)).
  - exact (iv_P_typed si_Σ [] localenv_nil).
  - apply (ws_cumul_pbE_forget_spec (pb := Cumul)).
    apply (red_ws_cumul_pbE (Σ := si_Σ)).
    exact (closed_red_of (Σ := si_Σ) (Γ := []) (t := tLetIn si_na cli_idIF si_P si_P) eq_refl eq_refl
             (red1_red _ _ _ _ (red_zeta _ _ si_na cli_idIF si_P si_P))).
Qed.

Lemma cli_idIF_let_isType : isTypeE si_Σ [] cli_idIF_let.
Proof. exact (has_sort_isTypeE _ cli_idIF_let_typed). Qed.

(** The tail start reduces FORWARD to [cli_dep_let] by the β step in the let's definiens. *)
Lemma cli_idIF_let_red1 : red1 si_Σ [] cli_idIF_let cli_dep_let.
Proof.
  unfold cli_idIF_let, cli_dep_let, cli_idIF. apply letin_red_def.
  exact (red_beta _ _ si_na si_P (tRel 0) iv_IF).
Qed.

Lemma cli_idIF_let_ws : ws_cumul_pbE Cumul si_Σ [] cli_idIF_let cli_dep_let.
Proof.
  apply (red_ws_cumul_pbE (Σ := si_Σ)).
  exact (closed_red_of (Σ := si_Σ) (Γ := []) (t := cli_idIF_let) eq_refl eq_refl
           (red1_red _ _ _ _ cli_idIF_let_red1)).
Qed.

(** [cli_idx_ty] applied to [I (∀P. P)] only, at [cli_dep_let]. The cons step is the join
    [cli_idx_ws] at the valley [Π x : Prop. cli_idx_arr]; the empty tail starts at the let-in
    [cli_idIF_let] and reaches [cli_dep_let] by one forward β step ([cli_idIF_let_ws]). *)
Lemma cli_idx_sp_let : PCUICAritiesEta.typing_spineE si_Σ [] cli_idx_ty [iv_IF] cli_dep_let.
Proof.
  eapply (@PCUICAritiesEta.type_spine_consE _ _ _ cli_idx_ty iv_IF [] si_na si_P cli_idx_let cli_dep_let).
  - exact cli_idx_isType.
  - exact cli_idx_let_prod_isType.
  - exact cli_idx_ws.
  - exact (iv_IF_typed [] localenv_nil).
  - econstructor; [exact cli_idIF_let_isType|exact cli_dep_let_isType|exact cli_idIF_let_ws].
Qed.

(** [Π y : (λw:Prop. w) (I (∀P. P)). (λw:Prop. w) ((λw:Prop. w) (I (∀P. P)))]: the remaining
    telescope of [cli_idx_ty] at [x := I (∀P. P)], the product [typing_spine_nth_error_None_prodE]
    returns on [cli_idx_sp_let]. *)
Definition cli_idIF_arr : term := tProd si_na cli_idIF (tApp iv_id cli_idIF).

(** [typing_spine_nth_error_None_prodE] on [cli_idx_sp_let] returns a product below [cli_dep_let],
    and NO INPUT HAS A PRODUCT BELOW [cli_dep_let]:
    - [cli_dep_let] is not a product, and the only type the spine relates to it, the start
      [cli_idIF_let] of the empty tail ([cli_idx_let] at [x := I (∀P. P)]), is not a product
      either; the cons step relates the telescope to [Π x : Prop. cli_idx_let], not to
      [cli_dep_let];
    - that relation is one forward β step from [cli_idIF_let] to [cli_dep_let], so no input reduces
      [cli_dep_let] at all.
    The product the lemma returns is [cli_idIF_arr] ([cli_idx_body] substituted), found only through
    the composition [cli_idIF_arr ≤ cli_idIF_let ≤ cli_dep_let] that the lemma builds (through
    [typing_spine_nth_error_NoneE]): it is none of the types the spine relates, not the ζ step of
    [cli_idIF_let], and neither it nor [cli_dep_let] reduces to the other. Nothing in that
    composition cancels: the cons step is a join of two different steps (the outer β of the
    telescope's codomain, the ζ of [cli_idx_let]), neither of them reflexive, and the tail is a
    third (the β in the let's definiens); none is the inverse of another. *)
Lemma cli_idx_prod_nondeg :
  subst0 (List.rev [iv_IF])
    (it_mkProd_or_LetIn (firstn (#|cli_idx_Δ| - #|[iv_IF]|) cli_idx_Δ) cli_idx_body) = cli_idIF_arr /\
  (forall na dom codom, cli_dep_let <> tProd na dom codom) /\
  subst10 iv_IF cli_idx_let = cli_idIF_let /\
  (forall na dom codom, cli_idIF_let <> tProd na dom codom) /\
  tProd si_na si_P cli_idx_let <> cli_dep_let /\
  ∥ red1 si_Σ [] cli_idIF_let cli_dep_let ∥ /\
  ∥ red1 si_Σ [] cli_idx_ty (tProd si_na si_P cli_idx_arr) ∥ /\
  ∥ red1 si_Σ [] (tProd si_na si_P cli_idx_let) (tProd si_na si_P cli_idx_arr) ∥ /\
  cli_idx_ty <> tProd si_na si_P cli_idx_arr /\ tProd si_na si_P cli_idx_let <> tProd si_na si_P cli_idx_arr /\
  cli_idIF_arr <> cli_idx_ty /\ cli_idIF_arr <> tProd si_na si_P cli_idx_let /\
  cli_idIF_arr <> cli_idIF_let /\ cli_idIF_arr <> cli_dep_let /\
  cli_idIF_arr <> subst10 cli_idIF (tProd si_na (tRel 0) (tRel 1)) /\
  ((si_Σ ;;; [] ⊢ cli_idIF_arr ⇝ cli_dep_let) -> False) /\
  ((si_Σ ;;; [] ⊢ cli_dep_let ⇝ cli_idIF_arr) -> False).
Proof.
  split; [vm_compute; reflexivity|].
  split; [intros na dom codom h; unfold cli_dep_let in h; discriminate h|].
  split; [vm_compute; reflexivity|].
  split; [intros na dom codom h; unfold cli_idIF_let in h; discriminate h|].
  split; [intros h; vm_compute in h; discriminate h|].
  split; [constructor; exact cli_idIF_let_red1|].
  split; [constructor; exact cli_idx_ty_red1|].
  split; [constructor; exact cli_idx_let_prod_red1|].
  do 7 (split; [intros h; vm_compute in h; discriminate h|]).
  split.
  { intros r. destruct (invert_red_prod_cb r) as [d [cd [e _ _]]].
    unfold cli_dep_let in e. discriminate e. }
  intros r. destruct (invert_red_letin_cb r) as [[d' [ty' [b' [e _ _ _]]]]|r'].
  - unfold cli_idIF_arr in e. discriminate e.
  - destruct (invert_red_prod_cb r') as [d [cd [e rd _]]].
    vm_compute in e. injection e. intros; subst.
    destruct (invert_red_mkApps_tInd_cb (ind := si_ind) (u := []) [iv_False] _ rd) as [args' [e2 _ _]].
    apply (f_equal decompose_app) in e2.
    rewrite (decompose_app_mkApps (tInd si_ind []) args' eq_refl) in e2.
    vm_compute in e2. discriminate e2.
Qed.

(** The empty spine of [cli_dep_let] at itself (reflexive: it holds no ζ step). *)
Lemma cli_dep_let_sp_nil : PCUICAritiesEta.typing_spineE si_Σ [] cli_dep_let [] cli_dep_let.
Proof.
  econstructor; [exact cli_dep_let_isType|exact cli_dep_let_isType|].
  exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) [] cli_dep_let cli_dep_let_isType).
Qed.

(** [typing_spine_smashE] on [cli_dep_let] ([Δ = [z := I (∀P. P) : Prop]], [T = Π y : z. z]):
    smashing drops the let, and the substitution [z := I (∀P. P)] into [Π y : z. z] gives
    [iv_fix_ty = Π y : I (∀P. P). I (∀P. P)], which is not the substituted [I (∀P. P)], not the
    body, and not the spine's result type [cli_dep_let]. *)
Lemma cli_smash_dep_nondeg :
  it_mkProd_or_LetIn [vdef si_na iv_IF si_P] (tProd si_na (tRel 0) (tRel 1)) = cli_dep_let /\
  smash_context [] [vdef si_na iv_IF si_P] = [] /\
  expand_lets [vdef si_na iv_IF si_P] (tProd si_na (tRel 0) (tRel 1)) = iv_fix_ty /\
  iv_fix_ty <> iv_IF /\ iv_fix_ty <> tProd si_na (tRel 0) (tRel 1) /\ iv_fix_ty <> cli_dep_let.
Proof.
  split; [reflexivity|]. split; [reflexivity|]. split; [vm_compute; reflexivity|].
  split; [|split]; intros h; vm_compute in h; discriminate h.
Qed.

(** The fixpoint [bdf_fmfix] applied to [c A], typed at its β-redex domain [(λ B. I B) A]. *)
Definition cli_cA : term := tApp (tConstruct si_ind 0 []) (tRel 0).

Lemma cli_cA_typed_I : si_Σ ;;; bd_Γ1 |-E cli_cA : tApp (tInd si_ind []) (tRel 0).
Proof.
  exact (typeE_App _ _ (tConstruct si_ind 0 []) si_na si_P (tApp (tInd si_ind []) (tRel 0)) _ (tRel 0)
           (iv_cstr_prod_typed bd_Γ1 bd_wfE_Γ1) (iv_cstr_typed bd_Γ1 bd_wfE_Γ1)
           (typeE_Rel _ _ 0 (vass si_na si_P) bd_wfE_Γ1 eq_refl)).
Qed.

Lemma cli_cA_typed : si_Σ ;;; bd_Γ1 |-E cli_cA : bdf_Dk 0.
Proof.
  eapply (typeE_Cumul _ _ cli_cA (tApp (tInd si_ind []) (tRel 0)) _ sProp).
  - exact cli_cA_typed_I.
  - exact (bdf_dom_typed bd_Γ1 0 bd_wfE_Γ1 eq_refl).
  - apply (ws_cumul_pbE_forget_spec (pb := Cumul)).
    apply (red_ws_cumul_pbE_inv (Σ := si_Σ)).
    exact (closed_red_of (Σ := si_Σ) (Γ := bd_Γ1) (t := bdf_Dk 0) eq_refl eq_refl
             (red1_red _ _ _ _ (red_beta _ _ si_na si_P (tApp (tInd si_ind []) (tRel 0)) (tRel 0)))).
Qed.

Lemma cli_fxty_isType : isTypeE si_Σ bd_Γ1 (bdf_fxty 0).
Proof. exact (has_sort_isTypeE _ (bdf_fxty_typed bd_Γ1 0 bd_wfE_Γ1 eq_refl)). Qed.

Lemma cli_IA_isType : isTypeE si_Σ bd_Γ1 (tApp (tInd si_ind []) (tRel 0)).
Proof.
  exact (has_sort_isTypeE _ (iv_IX_typed bd_Γ1 (tRel 0) bd_wfE_Γ1
                               (typeE_Rel _ _ 0 (vass si_na si_P) bd_wfE_Γ1 eq_refl))).
Qed.

Lemma cli_fix_sp_nil : PCUICAritiesEta.typing_spineE si_Σ bd_Γ1 (bdf_fxty 0) [] (bdf_fxty 0).
Proof.
  econstructor; [exact cli_fxty_isType|exact cli_fxty_isType|].
  exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) bd_Γ1 (bdf_fxty 0) cli_fxty_isType).
Qed.

Lemma cli_fix_sp_cA :
  PCUICAritiesEta.typing_spineE si_Σ bd_Γ1 (bdf_fxty 0) [cli_cA] (tApp (tInd si_ind []) (tRel 0)).
Proof.
  eapply (@PCUICAritiesEta.type_spine_consE _ _ _ (bdf_fxty 0) cli_cA [] si_na (bdf_Dk 0)
            (tApp (tInd si_ind []) (tRel 1)) (tApp (tInd si_ind []) (tRel 0))).
  - exact cli_fxty_isType.
  - exact cli_fxty_isType.
  - exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) bd_Γ1 (bdf_fxty 0) cli_fxty_isType).
  - exact cli_cA_typed.
  - econstructor; [exact cli_IA_isType|exact cli_IA_isType|].
    exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) bd_Γ1 _ cli_IA_isType).
Qed.

(** The cofixpoint [bdf_cmfix] of [iv_Σ]; its declared type is the β-redex [bdf_RFβ]. *)
Lemma cli_RFβ_isType : isTypeE iv_Σ iv_Γc bdf_RFβ.
Proof. exact (has_sort_isTypeE _ (bdf_RFβ_typed iv_Γc iv_wf_Γc)). Qed.

Lemma cli_cofix_sp_nil : PCUICAritiesEta.typing_spineE iv_Σ iv_Γc bdf_RFβ [] bdf_RFβ.
Proof.
  econstructor; [exact cli_RFβ_isType|exact cli_RFβ_isType|].
  exact (isType_ws_cumul_pbE_refl (Σ := iv_Σ) iv_Γc bdf_RFβ cli_RFβ_isType).
Qed.

Lemma cli_cofix_typed_R : iv_Σ ;;; iv_Γc |-E mkApps (tCoFix bdf_cmfix 0) [] : mkApps (tInd iv_ind []) [iv_False].
Proof.
  eapply (typeE_Cumul _ _ _ bdf_RFβ _ sProp).
  - exact bdf_cofix_typed.
  - exact (iv_RF_typed iv_Γc iv_wf_Γc).
  - apply (ws_cumul_pbE_forget_spec (pb := Cumul)).
    apply (red_ws_cumul_pbE (Σ := iv_Σ)).
    exact (closed_red_of (Σ := iv_Σ) (Γ := iv_Γc) (t := bdf_RFβ) eq_refl eq_refl (bdf_RFβ_red iv_Γc)).
Qed.

(** The cofixpoint [bdf_cofix_dβ] of [typing_cofix_coindE_inst]: [check_one_cofix] fails on it;
    its declared type, the β-redex [bdf_RFβ], is not [R (∀P. P)] and β-reduces to it in one
    step. *)
Lemma cli_cofix_dtype_nondeg :
  check_one_cofix bdf_cofix_dβ = None /\
  dtype bdf_cofix_dβ <> mkApps (tInd iv_ind []) [iv_False] /\
  ∥ red1 iv_Σ iv_Γc (dtype bdf_cofix_dβ) (mkApps (tInd iv_ind []) [iv_False]) ∥.
Proof.
  split; [exact bdf_check_cofix_dtypeβ|]. split; [intros h; vm_compute in h; discriminate h|].
  constructor. exact (red_beta _ _ si_na si_P (iv_R (tRel 0)) iv_False).
Qed.

(** Evaluation: [(λx:Prop. x → x) (∀P:Prop. P) ⇓ (∀P:Prop. P) → (∀P:Prop. P)]
    ([PCUICSREtaInstances.sri_xx_redex], [PCUICSREtaInstances.sri_xx_reduct]). *)
Lemma cli_eval_xx : eval si_Σ sri_xx_redex sri_xx_reduct.
Proof.
  eapply eval_beta; [apply eval_atom; reflexivity|apply eval_atom; reflexivity|].
  apply eval_atom; reflexivity.
Qed.

(** The value [(∀P:Prop. P) → (∀P:Prop. P)] of [cli_eval_xx] is not a subterm of the argument
    [∀P:Prop. P] (whose subterms are itself, [Prop] and [tRel 0]), nor the function
    [λx:Prop. x → x], nor the redex. The closedness of the redex is the closedness of the function
    and of the argument; the value is the body [x → x] with the argument for [x], and that body is
    not closed. *)
Lemma cli_eval_xx_nondeg :
  sri_xx_redex = tApp sri_xx_lam iv_False /\ sri_xx_lam = tLambda si_na si_P sri_x_to_x /\
  closedn 0 sri_xx_redex = closedn 0 sri_xx_lam && closedn 0 iv_False /\
  sri_xx_reduct <> iv_False /\ sri_xx_reduct <> si_P /\ sri_xx_reduct <> tRel 0 /\
  sri_xx_reduct <> sri_xx_lam /\ sri_xx_reduct <> sri_xx_redex /\
  closedn 0 sri_x_to_x = false /\ subst1 iv_False 0 sri_x_to_x = sri_xx_reduct.
Proof. repeat split; try reflexivity; intros h; vm_compute in h; discriminate h. Qed.

(** [c (∀P:Prop. P)] is a value, and evaluates to itself. *)
Lemma cli_cF_value : value si_Σ sri_cF.
Proof.
  change sri_cF with (mkApps (tConstruct si_ind 0 []) [iv_False]).
  eapply value_app_nonnil; [|discriminate|constructor; [|constructor]].
  - eapply value_head_cstr with (mdecl := si_mdecl) (idecl := si_idecl) (cdecl := si_cdecl); [|cbn; lia].
    exact (declared_constructor_to_gen (wfΣ := si_wf) si_declared_constructor).
  - apply value_atomic, atomic_atom. reflexivity.
Qed.

Lemma cli_cF_eval : eval si_Σ sri_cF sri_cF.
Proof.
  change sri_cF with (tApp (tConstruct si_ind 0 []) iv_False) at 1.
  change sri_cF with (mkApps (tConstruct si_ind 0 []) ([] ++ [iv_False])).
  eapply eval_construct with (mdecl := si_mdecl) (idecl := si_idecl) (cdecl := si_cdecl);
    [| |cbn; lia|apply eval_atom; reflexivity].
  - exact (declared_constructor_to_gen (wfΣ := si_wf) si_declared_constructor).
  - apply eval_atom; reflexivity.
Qed.

Lemma cli_axiom_free : axiom_free si_Σ.
Proof.
  intros c decl h. exfalso. red in h. cbn in h.
  destruct h as [h|h]; [discriminate h|exact h].
Qed.

Lemma cli_notCoInductive : notCoInductive si_Σ si_ind.
Proof. intros h. vm_compute in h. discriminate h. Qed.

(** [c (∀P:Prop. P)] is an application: its head is not the term itself. *)
Lemma cli_cF_head_differs : head sri_cF <> sri_cF.
Proof. vm_compute. discriminate. Qed.

(** [λx:Prop. c x] applied to [∀P:Prop. P], at [I (∀P:Prop. P)]: the body [c x] uses its variable,
    so the β step builds the value [c (∀P:Prop. P)]. *)
Definition cli_lam_c : term := tLambda si_na si_P (tApp (tConstruct si_ind 0 []) (tRel 0)).
Definition cli_lam_c_app : term := tApp cli_lam_c iv_False.

Lemma cli_lam_c_typed : si_Σ ;;; [] |-E cli_lam_c : tProd si_na si_P (tApp (tInd si_ind []) (tRel 0)).
Proof.
  have w := iv_wf_P si_Σ [] localenv_nil.
  exact (typeE_Lambda _ _ si_na si_P (tApp (tConstruct si_ind 0 []) (tRel 0)) (tApp (tInd si_ind []) (tRel 0))
           (iv_vass si_Σ [] si_na si_P _ (iv_P_typed si_Σ [] localenv_nil) eq_refl)
           (typeE_App _ _ (tConstruct si_ind 0 []) si_na si_P (tApp (tInd si_ind []) (tRel 0)) _ (tRel 0)
              (iv_cstr_prod_typed _ w) (iv_cstr_typed _ w) (typeE_Rel _ _ 0 (vass si_na si_P) w eq_refl))).
Qed.

Lemma cli_lam_c_app_typed : si_Σ ;;; [] |-E cli_lam_c_app : iv_IF.
Proof.
  exact (typeE_App _ _ cli_lam_c si_na si_P (tApp (tInd si_ind []) (tRel 0)) _ iv_False
           (iv_cstr_prod_typed [] localenv_nil) cli_lam_c_typed (iv_False_typed si_Σ [] localenv_nil)).
Qed.

(** [(λx:Prop. c x) (∀P:Prop. P) ⇓ c (∀P:Prop. P)]: one β step, then [eval_construct]. *)
Lemma cli_lam_c_eval : eval si_Σ cli_lam_c_app sri_cF.
Proof.
  eapply eval_beta; [apply eval_atom; reflexivity|apply eval_atom; reflexivity|exact cli_cF_eval].
Qed.

(** The application [(λx:Prop. c x) (∀P:Prop. P)] is not a canonical form (its head is an
    abstraction). Its value [c (∀P:Prop. P)] is the body [c x], which uses [x], with the argument
    for [x]; it is neither the argument, nor the function, nor the application. *)
Lemma cli_lam_c_nondeg :
  PCUICViews.construct_cofix_discr (head cli_lam_c_app) = false /\
  noccur_between 0 1 (tApp (tConstruct si_ind 0 []) (tRel 0)) = false /\
  subst1 iv_False 0 (tApp (tConstruct si_ind 0 []) (tRel 0)) = sri_cF /\
  sri_cF <> iv_False /\ sri_cF <> cli_lam_c /\ sri_cF <> cli_lam_c_app.
Proof. repeat split; try reflexivity; intros h; vm_compute in h; discriminate h. Qed.

(** The recursive argument of [tFix iv_mfix 0] is present in [[c (∀P. P)]]. *)
Lemma cli_fix_rarg_present :
  match unfold_fix iv_mfix 0 with
  | Some (narg, _) => nth_error [sri_cF] narg = Some sri_cF
  | None => False
  end.
Proof. exact eq_refl. Qed.

Section ClassificationEtaInstances.

(** ** The arity corollaries, Class A' *)

(** INSTANCE NOT-BUILT: degenerate, a round trip red → cumul → red hidden under the squash: the conclusion [Is_conv_to_Arity si_Σ cli_Γz cli_T] is inhabited by [iv_PP] (Prop → Prop) with [sq cli_T_closed_red] and [eq_refl], and [cli_T_closed_red] is the δ step of [z] that the input [cli_ws_r] is built from ([red_ws_cumul_pbE]), a sub-derivation of it at depth 1; the proof of [invert_cumul_arity_rE] applies T8 [Prod_r] to [cli_T] and T8 [Sort_r] to [z ≤ Prop], which only recover that step; a cumulativity from [cli_T] to an arity whose derivation contains an expansion (a peak, as [PCUICSREtaConvInstances.sc_A] reduces to both [sc_ty] and [sc_tw]), so that the T8 sites need confluence, would make [invert_cumul_arity_rE] run; no non-degenerate witness built yet *)
Definition invert_cumul_arity_rE_inst : Is_conv_to_Arity si_Σ cli_Γz cli_T :=
  invert_cumul_arity_rE (Σ := si_Σ) (wfΣ := si_wfE) cli_Γz cli_T iv_PP eq_refl cli_ws_r cli_T_isType.

(** INSTANCE NOT-BUILT: degenerate, a round trip red → cumul → red hidden under the squash: the conclusion [Is_conv_to_Arity si_Σ cli_Γz cli_T] is inhabited by [iv_PP] (Prop → Prop) with [sq cli_T_closed_red] and [eq_refl], and [cli_T_closed_red] is the δ step of [z] that the input [cli_ws_l] is built from ([red_ws_cumul_pbE_inv]), a sub-derivation of it at depth 1; the proof of [invert_cumul_arity_lE] applies [PCUICPrincipalityEta.T8_Prod_l_plug] to [cli_T] and [T8_Sort_l_plug] to [Prop ≤ z], which only recover that step; a cumulativity from an arity to [cli_T] whose derivation contains an expansion (a peak, as [PCUICSREtaConvInstances.sc_A] reduces to both [sc_ty] and [sc_tw]), so that the T8 sites need confluence, would make [invert_cumul_arity_lE] run; no non-degenerate witness built yet *)
Definition invert_cumul_arity_lE_inst : Is_conv_to_Arity si_Σ cli_Γz cli_T :=
  invert_cumul_arity_lE (Σ := si_Σ) (wfΣ := si_wfE) cli_Γz iv_PP cli_T eq_refl cli_ws_l cli_T_isType.

(** INSTANCE NOT-BUILT: degenerate, a round trip red → cumul → red hidden under the squash: the conclusion [Is_conv_to_Arity si_Σ cli_Γz cli_T] is inhabited by [iv_PP] (Prop → Prop) with [sq cli_T_closed_red] and [eq_refl], and [cli_T_closed_red] is the δ step of [z] that the input [cli_ws_l] is built from ([red_ws_cumul_pbE_inv]); [cli_PP_conv] is reflexive, so [ws_cumul_pbE_red_l_inv] leaves [cli_ws_l] as it is and the proof is [invert_cumul_arity_lE] on [cli_ws_l], whose T8 sites only recover that step; a cumulativity from an arity to [cli_T] whose derivation contains an expansion (a peak, as [PCUICSREtaConvInstances.sc_A] reduces to both [sc_ty] and [sc_tw]), so that the T8 sites need confluence, would make [invert_cumul_arity_l_genE] run; no non-degenerate witness built yet *)
Definition invert_cumul_arity_l_genE_inst : Is_conv_to_Arity si_Σ cli_Γz cli_T :=
  invert_cumul_arity_l_genE (Σ := si_Σ) (wfΣ := si_wfE) cli_Γz iv_PP cli_T cli_PP_conv cli_ws_l cli_T_isType.

(** INSTANCE NOT-BUILT: degenerate, a round trip red → cumul → red hidden under the squash: the conclusion [Is_conv_to_Arity si_Σ cli_Γz cli_T] is inhabited by [iv_PP] (Prop → Prop) with [sq cli_T_closed_red] and [eq_refl], and [cli_T_closed_red] is the δ step of [z] that the input [cli_ws_r] is built from ([red_ws_cumul_pbE]); [cli_PP_conv] is reflexive, so [ws_cumul_pbE_red_r_inv] leaves [cli_ws_r] as it is and the proof is [invert_cumul_arity_rE] on [cli_ws_r], whose T8 sites only recover that step; a cumulativity from [cli_T] to an arity whose derivation contains an expansion (a peak, as [PCUICSREtaConvInstances.sc_A] reduces to both [sc_ty] and [sc_tw]), so that the T8 sites need confluence, would make [invert_cumul_arity_r_genE] run; no non-degenerate witness built yet *)
Definition invert_cumul_arity_r_genE_inst : Is_conv_to_Arity si_Σ cli_Γz cli_T :=
  invert_cumul_arity_r_genE (Σ := si_Σ) (wfΣ := si_wfE) cli_Γz iv_PP cli_T cli_PP_conv cli_ws_r cli_T_isType.

(** INSTANCE NOT-BUILT: degenerate, a round trip red → cumul → red hidden under the squash: the conclusion [Is_conv_to_Arity si_Σ cli_Γz cli_T] is inhabited by [iv_PP] (Prop → Prop) with [sq cli_T_closed_red] and [eq_refl], and [cli_T_closed_red] is the δ step of [z] that [cli_ws_l] is built from ([red_ws_cumul_pbE_inv]); the spine is [type_spine_nilE] with the nil step [cli_ws_l], and [cli_PP_conv] is reflexive, so the cumulativity [w'] of the proof is the transitivity of the reflexive one with [cli_ws_l] and the proof is [invert_cumul_arity_lE] on it, whose T8 sites only recover that step; a nil step from an arity to [cli_T] whose derivation contains an expansion (a peak, as [PCUICSREtaConvInstances.sc_A] reduces to both [sc_ty] and [sc_tw]), so that the T8 sites need confluence, would make [isArity_typing_spineE] run; no non-degenerate witness built yet *)
Definition isArity_typing_spineE_inst : Is_conv_to_Arity si_Σ cli_Γz cli_T :=
  isArity_typing_spineE (Σ := si_Σ) (wfΣ := si_wfE) cli_wf_Γz
    (PCUICAritiesEta.type_spine_nilE _ _ iv_PP cli_T cli_PP_isType cli_T_isType cli_ws_l) cli_PP_conv.

(** INSTANCE IMPOSSIBLE: the conclusion is False: an inductive application reduces only to inductive applications, never to an arity; here I (∀P. P), its Is_conv_to_Arity premise left as a hypothesis. *)
Definition Is_conv_to_Arity_indE_inst :
  Is_conv_to_Arity si_Σ [] (mkApps (tInd si_ind []) [iv_False]) -> False :=
  Is_conv_to_Arity_indE (Σ := si_Σ) [] si_ind [] [iv_False].

(** INSTANCE IMPOSSIBLE: the conclusion is False: a spine of a type convertible to an arity never ends at an inductive application; here the arity Prop → Prop in cli_Γz (cli_PP_conv), the spine to I (∀P. P) left as a hypothesis. *)
Definition typing_spine_arity_mkApps_IndE_inst :
  forall l, PCUICAritiesEta.typing_spineE si_Σ cli_Γz iv_PP l (mkApps (tInd si_ind []) [iv_False]) -> False :=
  fun l sp => typing_spine_arity_mkApps_IndE (Σ := si_Σ) cli_Γz iv_PP l si_ind [] [iv_False] cli_wf_Γz sp
    cli_PP_conv.

(** [let z := x : Prop in Π _ : x. Prop], with [x] free (de Bruijn index 0 outside the let):
    an arity whose let body and product domain mention [x] (index 0 in the let body, index 1
    under the let, in the product domain). The substitution [x := ∀P. P] changes the term
    ([cli_open_arity_subst_differs]). *)
Definition cli_open_arity : term := tLetIn si_na (tRel 0) si_P (tProd si_na (tRel 1) (tSort sProp)).

Lemma cli_open_arity_subst_differs : subst [iv_False] 0 cli_open_arity <> cli_open_arity.
Proof. discriminate. Qed.

(** INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_open_arity_subst_differs *)
Definition arity_spine_len_subst_inst :
  arity_spine_len (subst [iv_False] 0 cli_open_arity) = arity_spine_len cli_open_arity :=
  arity_spine_len_subst [iv_False] 0 cli_open_arity eq_refl.

(** ** The (co)fixpoint witness, at declared types on which the check fails *)

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_check_fix_dtypeβ *)
Definition mfix_on_ind_spine_witnessE_fix_inst :=
  mfix_on_ind_spine_witnessE_fix (Σ := si_Σ) si_wfE (ok := fun mind => check_recursivity_kind (lookup_env si_Σ) mind Finite)
    bd_Γ1 bdf_fmfix 0 bdf_fix_dβ [] (bdf_fxty 0) bdf_wf_fix.2.2 eq_refl cli_fxty_isType cli_fix_sp_nil.

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_check_cofix_dtypeβ *)
Definition mfix_on_ind_spine_witnessE_cofix_inst :=
  mfix_on_ind_spine_witnessE_cofix (Σ := iv_Σ) iv_wfE
    (ok := fun mind => check_recursivity_kind (lookup_env iv_Σ) mind CoFinite)
    iv_Γc bdf_cmfix 0 bdf_cofix_dβ [] bdf_RFβ bdf_wf_cofix eq_refl cli_RFβ_isType cli_cofix_sp_nil.

(** INSTANCE NOT-BUILT: degenerate, a round trip and a cancelling composition: the conversion of [bdf_wf_fix] is [red_ws_cumul_pbE] of a β step of the declared type [bdf_fxty 0], so the reduct its proof obtains through mfix_on_ind_spine_witnessE_fix is that step; the spine [cli_fix_sp_cA] types [cli_cA] at the β-redex domain [bdf_Dk 0] through [cli_cA_typed], which is [typeE_Cumul] over [cli_cA_typed_I] by a forgotten β step, and the conclusion types [cli_cA] back at [I A], the type of [cli_cA_typed_I]; the [Finite] check is carried from the input; an argument typed directly at the redex domain and a conversion that is not a forgotten reduction would make [wf_fixpoint_spineE] run; no non-degenerate witness built yet *)
Definition wf_fixpoint_spineE_inst :=
  wf_fixpoint_spineE (Σ := si_Σ) si_wfE bd_Γ1 bdf_fmfix 0 bdf_fix_dβ [cli_cA] _
    bdf_wf_fix eq_refl cli_fxty_isType cli_fix_sp_cA.

(** INSTANCE NOT-BUILT: degenerate, a round trip: the conversion of [bdf_wf_cofix] is [red_ws_cumul_pbE] of [bdf_RFβ_red], the reduction of the declared type [bdf_RFβ] to [iv_RF], and the spine [cli_cofix_sp_nil] is the reflexive empty spine, so the target returns that reduction, the shape of [iv_RF] and [0 = 0] computed on concrete terms, the [CoFinite] check carried from the input, and [iv_RF ≤ bdf_RFβ], the same reduction forgotten again; a conversion that is not a forgotten reduction and a non-empty spine would make [wf_cofixpoint_spineE] run; no non-degenerate witness built yet *)
Definition wf_cofixpoint_spineE_inst :=
  wf_cofixpoint_spineE (Σ := iv_Σ) iv_wfE iv_Γc bdf_cmfix 0 bdf_cofix_dβ [] bdf_RFβ
    bdf_wf_cofix eq_refl cli_RFβ_isType cli_cofix_sp_nil.

(** The cofixpoint [[bdf_cofix_dβ]] ([bdf_cmfix]), typed at [R (∀P. P)]: [check_one_cofix] fails
    on it, and its declared type, the β-redex [bdf_RFβ], is not [R (∀P. P)] and β-reduces to it
    in one step ([cli_cofix_dtype_nondeg]).
    INSTANCE NOT-BUILT: degenerate, the S36 round trip: the witness [cli_cofix_typed_R] types the cofixpoint at [R (∀P. P)] by [typeE_Cumul] over [bdf_cofix_typed] with [red_ws_cumul_pbE] of [bdf_RFβ_red], and its [wf_cofixpointE] is [bdf_wf_cofix], built from the same [bdf_RFβ_red]; so the cumulativity [typing_cofix_coindE] inverts is [R F ≤ bdf_RFβ ≤ R F], a composition that cancels between identical terms, the witness type and the typed type are both [iv_RF], and the conclusion is the [ok] field of [bdf_wf_cofix]; a conversion witness that is not a forgotten reduction, with the cofixpoint typed at a different application of [R] (e.g. [R ((λx. x) F)]), would make [invert_cumul_ind_indE] compare different terms; no non-degenerate witness built yet *)
Definition typing_cofix_coindE_inst :
  check_recursivity_kind (lookup_env iv_Σ) (inductive_mind iv_ind) CoFinite :=
  typing_cofix_coindE (Σ := iv_Σ) (wfΣ := iv_wfE) (mfix := [bdf_cofix_dβ]) cli_cofix_typed_R.

(** ** Spines and smashing *)

(** [let z := I (∀P. P) in Π y : z. z] ([cli_dep_let]) against its smashed form: smashing drops the
    let and substitutes [z := I (∀P. P)] into both positions of [Π y : z. z], giving
    [Π y : I (∀P. P). I (∀P. P)], neither the substituted term, nor the body, nor [cli_dep_let]
    ([cli_smash_dep_nondeg]).
    INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_smash_dep_nondeg *)
Definition cumul_it_mkProd_or_LetIn_smashE_inst :=
  cumul_it_mkProd_or_LetIn_smashE (Σ := si_Σ) si_wfE [] [vdef si_na iv_IF si_P] (tProd si_na (tRel 0) (tRel 1))
    eq_refl eq_refl.

(** The empty spine of [let z := I (∀P. P) in Π y : z. z] ([cli_dep_let]) at itself, smashed: the
    smashed type is [Π y : I (∀P. P). I (∀P. P)], the substitution of [I (∀P. P)] into both
    positions of [Π y : z. z], neither the substituted term, nor the body, nor [cli_dep_let]
    ([cli_smash_dep_nondeg]).
    INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_smash_dep_nondeg *)
Definition typing_spine_smashE_inst :=
  typing_spine_smashE (Σ := si_Σ) si_wfE [] [vdef si_na iv_IF si_P] (tProd si_na (tRel 0) (tRel 1)) []
    cli_dep_let cli_dep_let_sp_nil.

(** The second argument [c (∀P. P)] of [Π x : Prop. Π y : I x. I x] ([cli_depI_ty]) applied to
    [(λx:Prop. x) (∀P. P)], at its declared type [I x] instantiated by the first argument:
    [I ((λx:Prop. x) (∀P. P))] ([cli_IidF]). The spine [cli_depI_sp_fwd] types the argument only
    at its own type [I (∀P. P)] ([sri_cF_typed]) and reduces the type it reaches there forward to
    the product [Π y : I (∀P. P). I (∀P. P)]; the lemma inverts that product cumulativity and
    applies the domain conversion to the argument, so the concluded typing is in no premise
    ([cli_depI_nth_fwd_nondeg]).
    INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_depI_nth_fwd_nondeg
    TARGET PCUICClassificationEta.typing_spine_nth_errorE *)
Definition typing_spine_nth_errorE_inst :=
  PCUICClassificationEta.typing_spine_nth_errorE (Σ := si_Σ) si_wfE [] cli_depI_Δ (iv_Ix 1)
    [tApp iv_id iv_False; sri_cF] iv_IF 1 sri_cF (vass si_na (iv_Ix 0)) cli_depI_ass cli_wf_depI
    cli_depI_sp_fwd eq_refl eq_refl.

(** The empty spine of [let z := ∀P. P in z → z] ([cli_let_arrow]) at itself: the substituted
    codomain [(∀P. P) → (∀P. P)] is neither the substituted [∀P. P], nor the body [z → z], nor the
    compared [cli_let_arrow] ([cli_all_inv_let_nondeg]).
    INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_all_inv_let_nondeg *)
Definition typing_spine_all_invE_inst :=
  typing_spine_all_invE (Σ := si_Σ) si_wfE [] [vdef si_na iv_False si_P] (tProd si_na (tRel 0) (tRel 1)) []
    cli_let_arrow cli_let_arrow_sp_nil eq_refl.

(** The partial spine [Π x : Prop. Π y : x. (λw:Prop. w) x] ([cli_dep_ty_id]) applied to
    [I (∀P. P)] only, at [cli_dep_let] ([cli_dep_id_sp_let]): its cons step reduces the telescope
    forward to [cli_dep_ty] and its tail is the ζ step of [cli_dep_let]. The lemma composes the
    substituted cons step with the tail into [Π y : I (∀P. P). (λw:Prop. w) (I (∀P. P))
    ≤ cli_dep_let], which no premise states ([cli_dep_id_none_nondeg]).
    INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_dep_id_none_nondeg *)
Definition typing_spine_nth_error_NoneE_inst :=
  typing_spine_nth_error_NoneE (Σ := si_Σ) si_wfE [] cli_dep_Δ (tApp iv_id (tRel 1)) [iv_IF] cli_dep_let
    cli_dep_ass cli_wf_dep cli_dep_id_sp_let eq_refl.

(** The partial spine [Π x : Prop. Π y : (λw:Prop. w) x. (λw:Prop. w) ((λw:Prop. w) x)]
    ([cli_idx_ty]) applied to [I (∀P. P)] only, at the let-in [cli_dep_let] ([cli_idx_sp_let]). No
    input relates a product to [cli_dep_let]: the only type the spine relates to it is the let-in
    [let z := (λw:Prop. w) (I (∀P. P)) : Prop in Π y : z. z], by one forward β step. The lemma finds
    the product [Π y : (λw:Prop. w) (I (∀P. P)). (λw:Prop. w) ((λw:Prop. w) (I (∀P. P)))] below
    [cli_dep_let] only by composing the cons step, a join of two different steps, with that β step
    ([cli_idx_prod_nondeg]).
    INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_idx_prod_nondeg *)
Definition typing_spine_nth_error_None_prodE_inst :=
  typing_spine_nth_error_None_prodE (Σ := si_Σ) si_wfE [] cli_idx_Δ cli_idx_body [iv_IF] cli_dep_let 1
    (vass si_na cli_idx) cli_idx_ass cli_wf_idx cli_idx_sp_let eq_refl eq_refl.

(** INSTANCE IMPOSSIBLE: the conclusion is False: a spine of Π Δ. I args never takes more arguments than Δ has assumptions; here Π A : Prop. I A (the type of c) applied to two arguments, the spine left as a hypothesis. *)
Definition typing_spine_more_invE_inst :
  forall T', PCUICAritiesEta.typing_spineE si_Σ []
    (it_mkProd_or_LetIn [vass si_na si_P] (mkApps (tInd si_ind []) [tRel 0])) [iv_False; iv_False] T' -> False :=
  fun T' sp => typing_spine_more_invE (Σ := si_Σ) si_wfE [] [vass si_na si_P] si_ind [] [tRel 0]
    [iv_False; iv_False] T' sp (le_n 2).

(** ** Classification and evaluation *)

(** Run at [Finite], the [ind_finite] of [I] in [si_Σ].
    INSTANCE IMPOSSIBLE: the conclusion is rk = rk' and in every environment Σ (the section premise wfE Σ included) both premises check the field ind_finite of the same declaration mind of lookup_env Σ, so rk and rk' are both that field. *)
Definition check_recursivity_kind_injE_inst : Finite = Finite :=
  check_recursivity_kind_injE (Σ := si_Σ) (wfΣ := si_wfE) (mind := si_kn) (rk := Finite) (rk' := Finite)
    eq_refl eq_refl.

(** The variable [x : (λ B. I B) A] in the context [bdf_Γβ].
    INSTANCE IMPOSSIBLE: the conclusion Σ ;;; Γ ⊢ t ⇝ t relates the premise's one term t to itself, for every premise and environment: its reduction is the reflexive one, and its other parts (Γ closed, t open in Γ) are side conditions that compute on any concrete context and term, so no instance relates two different terms. *)
Definition wt_closed_red_reflE_inst := wt_closed_red_reflE (Σ := si_Σ) (wfΣ := si_wfE) bdf_x_ind_typed.

(** INSTANCE IMPOSSIBLE: the conclusion is False: no derivation types a variable tVar; the typing premise left as a hypothesis. *)
Definition typing_varE_inst : forall ty, si_Σ ;;; [] |-E tVar "x" : ty -> False :=
  fun ty h => typing_varE (Σ := si_Σ) h.

(** INSTANCE IMPOSSIBLE: the conclusion is False: no derivation types an existential variable tEvar; the typing premise left as a hypothesis. *)
Definition typing_evarE_inst : forall ty, si_Σ ;;; [] |-E tEvar 0 [] : ty -> False :=
  fun ty h => typing_evarE (Σ := si_Σ) h.

(** INSTANCE IMPOSSIBLE: the conclusion is False: an inductive type (its type is an arity) is never typed at an inductive application; here I (∀P. P) at itself, the typing premise left as a hypothesis. *)
Definition invert_ind_indE_inst :
  si_Σ ;;; [] |-E mkApps (tInd si_ind []) [iv_False] : mkApps (tInd si_ind []) [iv_False] -> False :=
  invert_ind_indE (Σ := si_Σ) [] si_ind [] [iv_False] si_ind [] [iv_False].

(** INSTANCE IMPOSSIBLE: the conclusion is False: a fixpoint applied to no argument at its recursive index has a product type, never an inductive application; here tFix iv_mfix 0 unapplied at I (∀P. P), the typing premise left as a hypothesis. *)
Definition invert_fix_indE_inst :
  si_Σ ;;; [] |-E mkApps (tFix iv_mfix 0) [] : mkApps (tInd si_ind []) [iv_False] -> False :=
  invert_fix_indE (Σ := si_Σ) [] iv_mfix 0 [] si_ind [] [iv_False] eq_refl.

(* [wh_neutral_empty_genE] and [wh_neutral_emptyE]: no instance in this file since BET-339.
   They conclude [stuck_cofix_case t], not [False], and the former instance here (on
   an open term typed in the empty context) has no derivation of its premise. On every instance
   whose premises hold, the conclusion is the instance's own [whne] derivation translated into
   [stuck_cofix_case]; a typed blocked
   case needs a coinductive block, which [si_Σ] does not have
   ([PCUICEtaF0Land3Instances.l6_si_no_stuck]). Their instances, tagged IMPOSSIBLE, are
   [PCUICEtaF0Land3Instances.wh_neutral_empty_genE_inst] and
   [PCUICEtaF0Land3Instances.wh_neutral_emptyE_inst], in [iv_Σ] (coinductive [R]). *)

(** INSTANCE NOT-BUILT: degenerate, the instance's own derivation translated: value_whnfE is an induction on the value derivation, and on c (∀P. P) it maps value_app_nonnil with value_head_cstr to whnf_cstrapp, as for every value whose head is not a fixpoint, without the closedness premise; only a stuck fixpoint application (value_head_fix) makes it run, where closedness turns cunfold_fix into unfold_fix (closed_unfold_fix_cunfold_eq); a closed fixpoint with recursive argument index at least 1 applied to fewer arguments would; no non-degenerate witness built yet *)
Definition value_whnfE_inst := value_whnfE (Σ := si_Σ) (wfΣ := si_wfE) sri_cF eq_refl cli_cF_value.

(** The value [(∀P:Prop. P) → (∀P:Prop. P)] of [cli_eval_xx], the evaluation of the closed redex
    [(λx:Prop. x → x) (∀P:Prop. P)], is weak-head normal; that value is the body [x → x] with the
    argument for [x], neither the argument, nor the function, nor the redex.
    INSTANCE NOT-BUILT: degenerate, the evaluation result's value translated: eval_whneE runs eval_closed_cb, eval_to_value and value_whnfE; on cli_eval_xx the value of (∀P. P) → (∀P. P) is read off the last premise eval_atom, and value_whnfE takes its atom branch (whnf of a product), so the closedness from eval_closed_cb is never used; only a closed stuck fixpoint application as the result (value_head_fix, a fixpoint with recursive argument index at least 1) consumes it; no non-degenerate witness built yet *)
Definition eval_whneE_inst :=
  eval_whneE (Σ := si_Σ) (wfΣ := si_wfE) sri_xx_redex sri_xx_reduct eq_refl cli_eval_xx.

(** The closedness of the value [(∀P:Prop. P) → (∀P:Prop. P)] of [cli_eval_xx], from the
    closedness of the redex [(λx:Prop. x → x) (∀P:Prop. P)].
    INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_eval_xx_nondeg *)
Definition eval_closed_cb_inst : closed sri_xx_reduct :=
  eval_closed_cb si_Σ sri_xx_redex sri_xx_reduct eq_refl cli_eval_xx.

(** INSTANCE IMPOSSIBLE: the proof splits on wh_normal; at whnf_cstrapp and whnf_cofixapp the left disjunct is computed from the head, and at whnf_ne the right disjunct stuck_cofix_case t is the instance's own whne derivation translated constructor by constructor (wh_neutral_emptyE); every other branch, and every neutral leaf but a case on a cofixpoint, is refuted from the typing and axiom_free premises, so reaching one needs an uninhabited conclusion *)
Definition whnf_classification'E_inst :=
  whnf_classification'E (Σ := si_Σ) (wfΣ := si_wfE) sri_cF si_ind [] [iv_False] eq_refl
    (whnf_cstrapp _ _ _ _ _ _ [iv_False]) sri_cF_typed.

(** INSTANCE IMPOSSIBLE: the proof splits on wh_normal; at whnf_cstrapp and whnf_cofixapp the left disjunct is computed from the head, and at whnf_ne the right disjunct stuck_cofix_case t is the instance's own whne derivation translated constructor by constructor (wh_neutral_emptyE); every other branch, and every neutral leaf but a case on a cofixpoint, is refuted from the typing and axiom_free premises, so reaching one needs an uninhabited conclusion *)
Definition whnf_classificationE_inst :=
  whnf_classificationE (Σ := si_Σ) (wfΣ := si_wfE) sri_cF si_ind [] [iv_False] cli_axiom_free
    (whnf_cstrapp _ _ _ _ _ _ [iv_False]) sri_cF_typed.

(** INSTANCE IMPOSSIBLE: the proof calls whnf_classification'E, whose satisfiable branches read the conclusion off the instance's own wh_normal derivation (the head by computation, or the whne derivation translated into stuck_cofix_case, passed through as the right disjunct, CE:1043); the cofixpoint head is refuted by typing_cofix_coindE against notCoInductive; reaching a refuted branch needs an uninhabited conclusion *)
Definition ind_whnf_classification'E_inst :=
  ind_whnf_classification'E (Σ := si_Σ) (wfΣ := si_wfE) sri_cF si_ind [] [iv_False] eq_refl
    cli_notCoInductive sri_cF_typed (whnf_cstrapp _ _ _ _ _ _ [iv_False]).

(** INSTANCE IMPOSSIBLE: the proof calls whnf_classification'E, whose satisfiable branches read the conclusion off the instance's own wh_normal derivation (the head by computation, or the whne derivation translated into stuck_cofix_case, passed through as the right disjunct, CE:1043); the cofixpoint head is refuted by typing_cofix_coindE against notCoInductive; reaching a refuted branch needs an uninhabited conclusion *)
Definition ind_whnf_classificationE_inst :=
  ind_whnf_classificationE (Σ := si_Σ) (wfΣ := si_wfE) sri_cF si_ind [] [iv_False] cli_axiom_free
    cli_notCoInductive sri_cF_typed (whnf_cstrapp _ _ _ _ _ _ [iv_False]).

(** The fixpoint applied to [c (∀P. P)]: its recursive argument is present
    ([cli_fix_rarg_present]), so the conclusion is the branch for a present argument (an
    axiom-free normal value there is a constructor application or, since BET-339, a case blocked
    on a cofixpoint), not the product of the absent case.
    INSTANCE NOT-BUILT: degenerate, the statement holds without the lemma: with the recursive argument present ([cli_fix_rarg_present]) the instance's type is the branch [axiom_free_value sri_cF → wh_normal sri_cF → isConstruct_app sri_cF + stuck_cofix_case sri_cF], whose left disjunct [isConstruct_app (c (∀P. P))] computes to [true], [c (∀P. P)] being a constructor application; the proof of [fix_app_is_constructorE] runs [wf_fixpoint_spineE] and then [ind_whnf_classification'E] (IMPOSSIBLE) on that argument, which reaches the constructor branch and computes the left disjunct (its right disjunct is reached only by a case blocked on a cofixpoint, where it is the argument's own whne derivation translated), so neither part shows anything in the instance's type; an instance whose recursive argument is absent would conclude the other branch, a product below the type, which [fix_app_is_constructorE] must find through [wf_fixpoint_spineE], on a spine whose tail does not already relate a product to the type; no non-degenerate witness built yet *)
Definition fix_app_is_constructorE_inst :=
  fix_app_is_constructorE (Σ := si_Σ) (wfΣ := si_wfE) (mfix := iv_mfix) (idx := 0) (args := [sri_cF])
    sri_fix_app_typed eq_refl.

(** The evaluation [cli_eval_xx] of [(λx:Prop. x → x) (∀P:Prop. P)], typed by
    [sri_xx_redex_typed], as a reduction to [(∀P:Prop. P) → (∀P:Prop. P)].
    INSTANCE NONDEGEN PCUICSREtaInstances.sri_xx_nondeg *)
Definition wcbveval_redE_inst : red si_Σ [] sri_xx_redex sri_xx_reduct :=
  wcbveval_redE (Σ := si_Σ) (wfΣ := si_wfE) sri_xx_redex si_P sri_xx_reduct
    (sri_xx_redex_typed [] localenv_nil) cli_eval_xx.

(** The evaluation [cli_eval_xx] of [(λx:Prop. x → x) (∀P:Prop. P)], typed by
    [sri_xx_redex_typed].
    INSTANCE NONDEGEN PCUICSREtaInstances.sri_xx_nondeg *)
Definition subject_reduction_evalE_inst : si_Σ ;;; [] |-E sri_xx_reduct : si_P :=
  subject_reduction_evalE (Σ := si_Σ) (wfΣ := si_wfE) (t := sri_xx_redex) (u := sri_xx_reduct)
    (sri_xx_redex_typed [] localenv_nil) cli_eval_xx.

(** INSTANCE IMPOSSIBLE: on every instance whose premises hold, construct_cofix_discr (head t) is computed from the head of the instance's own value: the proof turns it into wh_normal (value_final then eval_to_value, a round trip; value_whnfE, constructor by constructor), and whnf_classification'E reads the head at whnf_cstrapp or whnf_cofixapp; at whnf_ne it returns its stuck_cofix_case disjunct (wh_neutral_emptyE), which the proof refutes by value_not_stuck_cofix_case, a value being no case blocked on a cofixpoint, and every other branch, a stuck fixpoint included, is refuted from the typing at an inductive type; so reaching any branch but the head's needs an uninhabited conclusion *)
Definition value_classificationE_inst :=
  value_classificationE (Σ := si_Σ) (wfΣ := si_wfE) (t := sri_cF) (i := si_ind) (u := []) (args := [iv_False])
    sri_cF_typed cli_cF_value.

(** The application [(λx:Prop. c x) (∀P:Prop. P)], not a canonical form, evaluated to
    [c (∀P:Prop. P)] by a β step that builds the value from the body [c x].
    INSTANCE IMPOSSIBLE: on every instance whose premises hold, construct_cofix_discr (head t') is computed from the head of the instance's own evaluation result t': the typing of t' by subject reduction along the evaluation is used only by whnf_classification'E to refute the heads other than a constructor or a cofixpoint, and at whnf_cstrapp and whnf_cofixapp the head is read by computation; at whnf_ne whnf_classification'E returns its stuck_cofix_case disjunct (wh_neutral_emptyE), which the proof refutes by value_not_stuck_cofix_case, t' being a value (eval_to_value); so reaching any branch but the head's needs an uninhabited conclusion *)
Definition eval_classificationE_inst :=
  eval_classificationE (Σ := si_Σ) (wfΣ := si_wfE) (i := si_ind) (u := []) (args := [iv_False])
    cli_lam_c_app_typed sri_cF cli_lam_c_eval.

End ClassificationEtaInstances.
