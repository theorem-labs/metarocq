(* Distributed under the terms of the MIT license. *)

(* NONDEGEN tags: an INSTANCE NONDEGEN tag is a reader judgment backed by a compiled nontriviality
   lemma, not a mechanical guarantee.
   Measured reader miss rate: at least 19 of 60 instances sampled (seed 202610301905) from the 323 that an earlier focused review had not covered (31.7%, 95% upper bound 42.9%, one-sided Clopper-Pearson): 17 from the union of the verdicts held by two independent reviews (Opus 5: 10; Opus 5.5: 15, 6 of its verdicts borderline at confidence 0.5-0.6), plus two further rows that both reviews had passed and later root rulings reclassified under the same standard (S12, S36). 18 of the 19 sampled misses are corrected at this head (S36 is not yet), but the sample estimates the rate over ALL instance tags: a comparable share of the unsampled instances is expected to be wrong and is NOT corrected.
   P4 at this head: 313 lemmas with a base twin are accounted for: 229 demonstrated (at least one NONDEGEN instance; this count still includes 2 targets whose only NONDEGEN instance is already judged false and not yet corrected: PCUICClassificationEta.wf_fixpoint_spineE and wf_cofixpoint_spineE), 70 undemonstrable by their own statements (IMPOSSIBLE-only), and 14 with no working instance (NOT-BUILT-only): BDToPCUICEta.wf_rel_weakE; PCUICAlphaEta.eq_context_conversionE, isType_eq_context_conversionE, typing_alpha_propE, wf_local_alphaE; PCUICClassificationEta.typing_spine_nth_errorE, typing_spine_nth_error_NoneE, typing_spine_nth_error_None_prodE (non-degenerate instances of these 3 are built and under review, not yet landed); PCUICInversionEta.into_ws_cumulE; PCUICPrincipalityEta.typing_leq_termE; PCUICSREta.prim_app_typing_invE, sr_prim_opE, typing_spine_prim_arg_typesE, typing_spine_prim_argsE. The demonstrated count rests on NONDEGEN tags with the measured miss rate above. As of 2026-10-31T02:35Z, 11 NONDEGEN tags are judged false and not yet corrected, all conv → red cases whose input conversion was built from a reduction (for wf_fixpoint_spineE_inst the conv → red step sits inside its target's proof): 7 in BDFromPCUICEtaInstances (red_fix_witnessE_inst, mfix_body_on_conv_redE_fix_inst, red_cofix_witnessE_inst, mfix_body_on_conv_redE_cofix_inst, mfix_on_ind_conv_redE_cofix_inst, wf_fixpointE_wf_fixpoint_red_typed_inst, and sampled row S36 = wf_cofixpointE_wf_cofixpoint_red_inst) and PCUICPrincipalityEtaInstances.T8_Prod_l_plug_inst and T8_Prod_l_of_r_inst, whose targets are outside P4's input set, and PCUICClassificationEtaInstances.wf_fixpoint_spineE_inst and wf_cofixpoint_spineE_inst, whose targets are the 2 above. Context of the demonstrations (context = a judgment argument of type list (context_decl term), empty or not by computing its length, not the lemma's Γ parameter): 79 use a non-empty context; 23 have the context as their subject; 20 have a non-empty context that no term or type mentions; 4 undecided; 70 work only at the empty context (10 forced by the statement, 60 by the instance's choice; up to 89 under stricter readings); 33 have no context argument, which is not the same as the empty context. A mechanical sweep flagged at least 31 of the 338 NONDEGEN instances at 0bf9899a, before the later retags, whose conclusion is convertible to an input sub-derivation (3 of the 31 match the instance itself or its helper rather than an input); of its 9 non-equation flags, 9 were judged bad, with the kind-label correct in 6 of 9; it cannot see a cancellation inside the target lemma's own proof or a conclusion that is one part of a pair, and it does not discriminate the 22 closed equations. Prose overclaims were not mechanically enumerated, because that detector failed its controls. Later root rulings reclassified two sampled rows that both reviews had passed, S36 (the red → conv → red class) and S12 (its conclusion is the input's own cumulativity), raising the sampled rate from at least 17 to at least 19 of 60; the 45-row marker census stayed at 2 reopened. *)

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
    one step to the arity [Prop → Prop] ([cli_T_red]). i20 ([invert_cumul_arity_rE_inst]) and
    i21 ([invert_cumul_arity_lE_inst]) take [cli_T] with a cumulativity to or from
    [Prop → Prop] ([cli_ws_r], [cli_ws_l]); x2, x3 and [isArity_typing_spineE] take it the same
    way. The input is chosen for the T8 sites of i20's proof ([Prod_r] on [cli_T], [Sort_r] on
    [z]) and of i21's ([PCUICPrincipalityEta.T8_Prod_l_plug], [T8_Sort_l_plug], the [_l] forms
    derived from the proved [_r] ones); no lemma here states which site a run reaches.
  - The (co)fixpoint witness lemmas run on declared types on which the check FAILS:
    [bdf_fxty 0] (domain the β-redex [(λ B. I B) A], [bdf_check_fix_dtypeβ]) and [bdf_RFβ]
    (the β-redex [(λ B. R B) (∀P. P)], [bdf_check_cofix_dtypeβ]); the typed-reduct route
    finds the reduct on which it passes. [wf_fixpoint_spineE_inst] applies the fixpoint to the
    argument [c A], typed at the β-redex domain, and reads back its type at the inductive.
  - [typing_cofix_coindE_inst]: a cofixpoint whose declared type is the β-redex [bdf_RFβ],
    typed at [R (∀P. P)], which is not that declared type and is its one-step β-reduct
    ([cli_cofix_dtype_nondeg]).
  - [typing_spine_all_invE_inst] runs on the empty spine of [let z := ∀P:Prop. P in z → z]
    ([cli_let_arrow]) at itself: the substitution [z := ∀P. P] into [z → z] gives
    [(∀P. P) → (∀P. P)], which is neither the substituted [∀P. P], nor the body, nor the compared
    let-in ([cli_all_inv_let_nondeg]).
    [typing_spine_nth_errorE_inst] reads the type of the second argument [c (∀P. P)] of
    [Π x : Prop. Π y : I x. I x] ([cli_depI_ty]) applied to [∀P. P];
    [typing_spine_nth_error_NoneE_inst] and [typing_spine_nth_error_None_prodE_inst] read the
    remaining telescope of the dependent type [Π x : Prop. Π y : x. x] ([cli_dep_ty]) applied to
    [I (∀P. P)] only, at the let-in [let z := I (∀P. P) in Π y : z. z] ([cli_dep_let]), not a
    product ([cli_dep_let_not_prod]). All three are tagged NOT-BUILT: a β step that their spine
    ([cli_depI_sp_two], [cli_dep_sp_let]) takes backwards is taken forward again, so each
    conclusion states what a sub-derivation of the input spine states (the reasons are in the
    tags); no non-degenerate witness is built yet.
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
    [cli_eval_xx_nondeg]);
    [eval_classificationE_inst] evaluates the application [(λx:Prop. c x) (∀P. P)], not a
    canonical form, to [c (∀P. P)] ([cli_lam_c_eval]: one β step that builds the value from the
    body [c x], then [eval_construct]; [cli_lam_c_nondeg]).
  - The whnf and value lemmas run on the application [c (∀P. P)], whose head is not the term
    itself ([cli_cF_head_differs]); the conclusion of [fix_app_is_constructorE_inst] is its
    branch for a present recursive argument ([cli_fix_rarg_present]).
  - The rows whose conclusion is [False] (the lemma states that its premises cannot hold
    together; as in base) and the rows whose conclusion relates a term to itself
    ([check_recursivity_kind_injE]: [rk = rk']; [wt_closed_red_reflE]: [Σ ;;; Γ ⊢ t ⇝ t], whose
    closedness side conditions compute on any concrete context and term and are not a
    non-degeneracy) have instances tagged IMPOSSIBLE, with the reason in the tag.

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
From MetaRocq.PCUIC Require PCUICWfUniverses.
From Equations.Type Require Import Relation.

(* The derivations the instances use, and the facts their tags name.
   WITNESSES: cli_* cli_depI_nth_subst_nondeg cli_dep_none_differs cli_dep_let_not_prod *)

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

(** [c (∀P. P) : I ((λx:Prop. x) (∀P. P))], through the β step backwards. *)
Lemma cli_cF_IidF_typed : si_Σ ;;; [] |-E sri_cF : cli_IidF.
Proof.
  refine (typeE_Cumul _ _ sri_cF iv_IF cli_IidF sProp sri_cF_typed cli_IidF_typed _).
  apply (ws_cumul_pbE_forget_spec (pb := Cumul)).
  apply (red_ws_cumul_pbE_inv (Σ := si_Σ)).
  exact (closed_red_of (Σ := si_Σ) (Γ := []) (t := cli_IidF) eq_refl eq_refl (red1_red _ _ _ _ cli_IidF_red1)).
Qed.

(** [Π y : I ((λx:Prop. x) (∀P. P)). I (∀P. P)]: [iv_fix_ty] with its domain under a β-redex. *)
Lemma cli_IidF_ty_isType : isTypeE si_Σ [] (tProd si_na cli_IidF iv_IF).
Proof.
  apply has_sort_isTypeE with (s := Sort.sort_of_product sProp sProp).
  apply typeE_Prod.
  - exact (iv_vass_s si_Σ [] si_na cli_IidF sProp cli_IidF_typed eq_refl).
  - exact (iv_IF_typed _ (iv_wf_vass si_Σ [] si_na cli_IidF sProp localenv_nil cli_IidF_typed eq_refl)).
Qed.

Lemma cli_IidF_ty_red1 : red1 si_Σ [] (tProd si_na cli_IidF iv_IF) iv_fix_ty.
Proof. unfold iv_fix_ty. apply prod_red_l. exact cli_IidF_red1. Qed.

(** [Π y : I (∀P. P). I (∀P. P) ≤ Π y : I ((λx:Prop. x) (∀P. P)). I (∀P. P)]: one β step backwards
    in the domain, not a reflexive cumulativity. *)
Lemma cli_fixty_IidF_ws : ws_cumul_pbE Cumul si_Σ [] iv_fix_ty (tProd si_na cli_IidF iv_IF).
Proof.
  apply (red_ws_cumul_pbE_inv (Σ := si_Σ)).
  exact (closed_red_of (Σ := si_Σ) (Γ := []) (t := tProd si_na cli_IidF iv_IF) eq_refl eq_refl
           (red1_red _ _ _ _ cli_IidF_ty_red1)).
Qed.

(** [cli_depI_ty] applied to [∀P. P] and [c (∀P. P)]. At the second argument the spine relates
    [Π y : I (∀P. P). I (∀P. P)] to the product [Π y : I ((λx:Prop. x) (∀P. P)). I (∀P. P)] by
    [cli_fixty_IidF_ws] (not reflexive), and takes [c (∀P. P)] at that product's domain
    ([cli_cF_IidF_typed]). *)
Lemma cli_depI_sp_two : PCUICAritiesEta.typing_spineE si_Σ [] cli_depI_ty [iv_False; sri_cF] iv_IF.
Proof.
  eapply (@PCUICAritiesEta.type_spine_consE _ _ _ cli_depI_ty iv_False [sri_cF] si_na si_P
            (tProd si_na (iv_Ix 0) (iv_Ix 1)) iv_IF).
  - exact cli_depI_isType.
  - exact cli_depI_isType.
  - exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) [] cli_depI_ty cli_depI_isType).
  - exact (iv_False_typed si_Σ [] localenv_nil).
  - eapply (@PCUICAritiesEta.type_spine_consE _ _ _ iv_fix_ty sri_cF [] si_na cli_IidF iv_IF iv_IF).
    + exact cli_fixty_isType.
    + exact cli_IidF_ty_isType.
    + exact cli_fixty_IidF_ws.
    + exact cli_cF_IidF_typed.
    + econstructor; [exact cli_IF_isType|exact cli_IF_isType|].
      exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) [] iv_IF cli_IF_isType).
Qed.

(** [typing_spine_nth_errorE] at the second argument [c (∀P. P)] of [cli_depI_ty]: its declared
    type [I x], with [x := ∀P. P] substituted, is [I (∀P. P)], which is not the substituted
    [∀P. P] and not the declared type [I x]. The domain [I ((λx:Prop. x) (∀P. P))] at which the
    spine [cli_depI_sp_two] takes the argument is not [I (∀P. P)] and β-reduces to it in one
    step, and the product with that domain is not [Π y : I (∀P. P). I (∀P. P)] and β-reduces to it
    in one step. *)
Lemma cli_depI_nth_subst_nondeg :
  nth_error (List.rev cli_depI_Δ) 1 = Some (vass si_na (iv_Ix 0)) /\
  subst (List.rev (firstn 1 [iv_False; sri_cF])) 0 (iv_Ix 0) = iv_IF /\
  iv_IF <> iv_False /\ iv_IF <> iv_Ix 0 /\
  cli_IidF <> iv_IF /\ ∥ red1 si_Σ [] cli_IidF iv_IF ∥ /\
  tProd si_na cli_IidF iv_IF <> iv_fix_ty /\ ∥ red1 si_Σ [] (tProd si_na cli_IidF iv_IF) iv_fix_ty ∥.
Proof.
  split; [reflexivity|]. split; [vm_compute; reflexivity|].
  split; [intros h; vm_compute in h; discriminate h|].
  split; [intros h; vm_compute in h; discriminate h|].
  split; [intros h; vm_compute in h; discriminate h|].
  split; [constructor; exact cli_IidF_red1|].
  split; [intros h; vm_compute in h; discriminate h|].
  constructor; exact cli_IidF_ty_red1.
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

(** [cli_dep_ty ≤ cli_dep_ty_id]: one β step backwards in the codomain, not reflexive. *)
Lemma cli_dep_ty_ws : ws_cumul_pbE Cumul si_Σ [] cli_dep_ty cli_dep_ty_id.
Proof.
  apply (red_ws_cumul_pbE_inv (Σ := si_Σ)).
  exact (closed_red_of (Σ := si_Σ) (Γ := []) (t := cli_dep_ty_id) eq_refl eq_refl
           (red1_red _ _ _ _ cli_dep_ty_id_red1)).
Qed.

(** [Π y : I (∀P. P). (λw:Prop. w) (I (∀P. P))]: the codomain of [cli_dep_ty_id] at [x := I (∀P. P)]. *)
Definition cli_fixty_id : term := tProd si_na iv_IF (tApp iv_id iv_IF).

Lemma cli_fixty_id_isType : isTypeE si_Σ [] cli_fixty_id.
Proof.
  have w := iv_wf_IF [] localenv_nil.
  apply has_sort_isTypeE with (s := Sort.sort_of_product sProp sProp).
  apply typeE_Prod.
  - exact (iv_vass_s si_Σ [] si_na iv_IF sProp (iv_IF_typed [] localenv_nil) eq_refl).
  - exact (typeE_App _ _ iv_id si_na si_P si_P _ iv_IF (iv_PP_typed si_Σ _ w) (iv_id_typed si_Σ _ w)
             (iv_IF_typed _ w)).
Qed.

Lemma cli_fixty_id_red1 : red1 si_Σ [] cli_fixty_id iv_fix_ty.
Proof. unfold cli_fixty_id, iv_fix_ty. apply prod_red_r. exact (red_beta _ _ si_na si_P (tRel 0) iv_IF). Qed.

(** [cli_fixty_id ≤ cli_dep_let]: a β step in the codomain, then [cli_dep_let_ws]. *)
Lemma cli_fixty_id_ws : ws_cumul_pbE Cumul si_Σ [] cli_fixty_id cli_dep_let.
Proof.
  refine (ws_cumul_pbE_trans (Σ := si_Σ) _ _ _ _ cli_dep_let_ws).
  apply (red_ws_cumul_pbE (Σ := si_Σ)).
  exact (closed_red_of (Σ := si_Σ) (Γ := []) (t := cli_fixty_id) eq_refl eq_refl
           (red1_red _ _ _ _ cli_fixty_id_red1)).
Qed.

(** [cli_dep_ty] applied to [I (∀P. P)] only, at [cli_dep_let]. The cons step relates [cli_dep_ty]
    to the product [cli_dep_ty_id] by [cli_dep_ty_ws] (not reflexive); the empty tail starts at
    [cli_fixty_id], not at [Π y : I (∀P. P). I (∀P. P)]. *)
Lemma cli_dep_sp_let : PCUICAritiesEta.typing_spineE si_Σ [] cli_dep_ty [iv_IF] cli_dep_let.
Proof.
  eapply (@PCUICAritiesEta.type_spine_consE _ _ _ cli_dep_ty iv_IF [] si_na si_P
            (tProd si_na (tRel 0) (tApp iv_id (tRel 1))) cli_dep_let).
  - exact cli_dep_isType.
  - exact cli_dep_ty_id_isType.
  - exact cli_dep_ty_ws.
  - exact (iv_IF_typed [] localenv_nil).
  - econstructor; [exact cli_fixty_id_isType|exact cli_dep_let_isType|exact cli_fixty_id_ws].
Qed.

(** [typing_spine_nth_error_NoneE] on [cli_dep_sp_let]: the returned left side, the substituted
    remaining telescope, computes to [Π y : I (∀P. P). I (∀P. P)] ([iv_fix_ty]), which is not the
    unsubstituted telescope and not [cli_dep_let]. The cons product of [cli_dep_sp_let],
    [cli_dep_ty_id], is not [cli_dep_ty] and β-reduces to it in one step, and the tail type of
    [cli_dep_sp_let], [cli_fixty_id], is not [iv_fix_ty] and β-reduces to it in one step. *)
Lemma cli_dep_none_differs :
  subst0 (List.rev [iv_IF]) (it_mkProd_or_LetIn (firstn (#|cli_dep_Δ| - #|[iv_IF]|) cli_dep_Δ) (tRel 1)) <>
    it_mkProd_or_LetIn (firstn (#|cli_dep_Δ| - #|[iv_IF]|) cli_dep_Δ) (tRel 1) /\
  subst0 (List.rev [iv_IF]) (it_mkProd_or_LetIn (firstn (#|cli_dep_Δ| - #|[iv_IF]|) cli_dep_Δ) (tRel 1)) <>
    cli_dep_let /\
  subst0 (List.rev [iv_IF]) (it_mkProd_or_LetIn (firstn (#|cli_dep_Δ| - #|[iv_IF]|) cli_dep_Δ) (tRel 1)) =
    iv_fix_ty /\
  cli_dep_ty_id <> cli_dep_ty /\ ∥ red1 si_Σ [] cli_dep_ty_id cli_dep_ty ∥ /\
  cli_fixty_id <> iv_fix_ty /\ ∥ red1 si_Σ [] cli_fixty_id iv_fix_ty ∥.
Proof.
  split; [vm_compute; discriminate|]. split; [vm_compute; discriminate|].
  split; [vm_compute; reflexivity|].
  split; [intros h; vm_compute in h; discriminate h|].
  split; [constructor; exact cli_dep_ty_id_red1|].
  split; [intros h; vm_compute in h; discriminate h|].
  constructor; exact cli_fixty_id_red1.
Qed.

Lemma cli_dep_let_not_prod : forall na dom codom, cli_dep_let <> tProd na dom codom.
Proof. intros na dom codom h. unfold cli_dep_let in h. discriminate h. Qed.

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

(** INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_T_not_arity *)
Definition invert_cumul_arity_rE_inst : Is_conv_to_Arity si_Σ cli_Γz cli_T :=
  invert_cumul_arity_rE (Σ := si_Σ) (wfΣ := si_wfE) cli_Γz cli_T iv_PP eq_refl cli_ws_r cli_T_isType.

(** INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_T_not_arity *)
Definition invert_cumul_arity_lE_inst : Is_conv_to_Arity si_Σ cli_Γz cli_T :=
  invert_cumul_arity_lE (Σ := si_Σ) (wfΣ := si_wfE) cli_Γz iv_PP cli_T eq_refl cli_ws_l cli_T_isType.

(** INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_T_not_arity *)
Definition invert_cumul_arity_l_genE_inst : Is_conv_to_Arity si_Σ cli_Γz cli_T :=
  invert_cumul_arity_l_genE (Σ := si_Σ) (wfΣ := si_wfE) cli_Γz iv_PP cli_T cli_PP_conv cli_ws_l cli_T_isType.

(** INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_T_not_arity *)
Definition invert_cumul_arity_r_genE_inst : Is_conv_to_Arity si_Σ cli_Γz cli_T :=
  invert_cumul_arity_r_genE (Σ := si_Σ) (wfΣ := si_wfE) cli_Γz iv_PP cli_T cli_PP_conv cli_ws_r cli_T_isType.

(** INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_T_not_arity *)
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

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_check_fix_dtypeβ *)
Definition wf_fixpoint_spineE_inst :=
  wf_fixpoint_spineE (Σ := si_Σ) si_wfE bd_Γ1 bdf_fmfix 0 bdf_fix_dβ [cli_cA] _
    bdf_wf_fix eq_refl cli_fxty_isType cli_fix_sp_cA.

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_check_cofix_dtypeβ *)
Definition wf_cofixpoint_spineE_inst :=
  wf_cofixpoint_spineE (Σ := iv_Σ) iv_wfE iv_Γc bdf_cmfix 0 bdf_cofix_dβ [] bdf_RFβ
    bdf_wf_cofix eq_refl cli_RFβ_isType cli_cofix_sp_nil.

(** The cofixpoint [[bdf_cofix_dβ]] ([bdf_cmfix]), typed at [R (∀P. P)]: [check_one_cofix] fails
    on it, and its declared type, the β-redex [bdf_RFβ], is not [R (∀P. P)] and β-reduces to it
    in one step ([cli_cofix_dtype_nondeg]).
    INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_cofix_dtype_nondeg *)
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
    [∀P. P], at its declared type [I x] instantiated by the first argument: [I (∀P. P)].
    INSTANCE NOT-BUILT: degenerate, a composition that cancels: the spine [cli_depI_sp_two] takes [c (∀P. P)] by [cli_cF_IidF_typed], which wraps the instance's own input [sri_cF_typed] (its first premise) in the β step [cli_IidF_red1] taken backwards, and the proof of the target (through [PCUICSpineEta.typing_spine_nth_errorE]) inverts the product cumulativity [cli_fixty_IidF_ws], built from that same step, and re-applies its domain conversion, so the conclusion [sri_cF : iv_IF] is the judgment of [sri_cF_typed], a piece of an input; no non-degenerate witness built yet
    TARGET PCUICClassificationEta.typing_spine_nth_errorE *)
Definition typing_spine_nth_errorE_inst :=
  PCUICClassificationEta.typing_spine_nth_errorE (Σ := si_Σ) si_wfE [] cli_depI_Δ (iv_Ix 1)
    [iv_False; sri_cF] iv_IF 1 sri_cF (vass si_na (iv_Ix 0)) cli_depI_ass cli_wf_depI cli_depI_sp_two
    eq_refl eq_refl.

(** The empty spine of [let z := ∀P. P in z → z] ([cli_let_arrow]) at itself: the substituted
    codomain [(∀P. P) → (∀P. P)] is neither the substituted [∀P. P], nor the body [z → z], nor the
    compared [cli_let_arrow] ([cli_all_inv_let_nondeg]).
    INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_all_inv_let_nondeg *)
Definition typing_spine_all_invE_inst :=
  typing_spine_all_invE (Σ := si_Σ) si_wfE [] [vdef si_na iv_False si_P] (tProd si_na (tRel 0) (tRel 1)) []
    cli_let_arrow cli_let_arrow_sp_nil eq_refl.

(** The partial spine [Π x : Prop. Π y : x. x] applied to [I (∀P. P)] only, at [cli_dep_let]
    ([cli_dep_sp_let]).
    INSTANCE NOT-BUILT: degenerate, a composition that cancels: the conclusion [iv_fix_ty ≤ cli_dep_let] (the substituted remaining telescope computes to [iv_fix_ty], [cli_dep_none_differs]) is the statement of [cli_dep_let_ws], the second argument of the transitivity that builds the tail step [cli_fixty_id_ws] of [cli_dep_sp_let], and the β step of [(λw:Prop. w) x] goes back in the cons step [cli_dep_ty_ws] and, at [x := I (∀P. P)], forward in [cli_fixty_id_ws] ([cli_fixty_id_red1]); no non-degenerate witness built yet *)
Definition typing_spine_nth_error_NoneE_inst :=
  typing_spine_nth_error_NoneE (Σ := si_Σ) si_wfE [] cli_dep_Δ (tRel 1) [iv_IF] cli_dep_let
    cli_dep_ass cli_wf_dep cli_dep_sp_let eq_refl.

(** The same partial spine [cli_dep_sp_let], at its type [cli_dep_let], a let-in and not a product
    ([cli_dep_let_not_prod]).
    INSTANCE NOT-BUILT: degenerate, a composition that cancels: the proof of the target calls [typing_spine_nth_error_NoneE] on the same spine [cli_dep_sp_let] and returns that cumulativity unchanged as its ∑ witness (the product is the substituted remaining telescope, [iv_fix_ty] by [cli_dep_none_differs]), the β step of [(λw:Prop. w) x] goes back in the cons step [cli_dep_ty_ws] and, at [x := I (∀P. P)], forward in [cli_fixty_id_ws] ([cli_fixty_id_red1]), and [cli_dep_let_ws], already in the input spine, proves the conclusion; no non-degenerate witness built yet *)
Definition typing_spine_nth_error_None_prodE_inst :=
  typing_spine_nth_error_None_prodE (Σ := si_Σ) si_wfE [] cli_dep_Δ (tRel 1) [iv_IF] cli_dep_let 1
    (vass si_na (tRel 0)) cli_dep_ass cli_wf_dep cli_dep_sp_let eq_refl eq_refl.

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

(** INSTANCE IMPOSSIBLE: the conclusion is False: an axiom-free weak-head neutral term is not typable in the empty context; here the neutral application x (∀P. P) of a variable, the typing premise left as a hypothesis. *)
Definition wh_neutral_empty_genE_inst : forall ty, si_Σ ;;; [] |-E tApp (tVar "x") iv_False : ty -> False :=
  fun ty h => wh_neutral_empty_genE (Σ := si_Σ) [] [] (tApp (tVar "x") iv_False) ty eq_refl
    (whne_app _ _ _ _ _ (whne_var _ _ _ "x")) h eq_refl.

(** INSTANCE IMPOSSIBLE: the conclusion is False: an axiom-free weak-head neutral term is not typable in the empty context; here the fixpoint tFix iv_mfix 0 stuck on the variable x at its recursive argument, the typing premise left as a hypothesis. *)
Definition wh_neutral_emptyE_inst : forall ty, si_Σ ;;; [] |-E mkApps (tFix iv_mfix 0) [tVar "x"] : ty -> False :=
  fun ty h => wh_neutral_emptyE (Σ := si_Σ) (mkApps (tFix iv_mfix 0) [tVar "x"]) ty eq_refl
    (whne_fixapp _ _ _ iv_mfix 0 [tVar "x"] _ (tVar "x") eq_refl eq_refl (whne_var _ _ _ "x")) h.

(** INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_cF_head_differs *)
Definition value_whnfE_inst := value_whnfE (Σ := si_Σ) (wfΣ := si_wfE) sri_cF eq_refl cli_cF_value.

(** The value [(∀P:Prop. P) → (∀P:Prop. P)] of [cli_eval_xx], the evaluation of the closed redex
    [(λx:Prop. x → x) (∀P:Prop. P)], is weak-head normal; that value is the body [x → x] with the
    argument for [x], neither the argument, nor the function, nor the redex.
    INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_eval_xx_nondeg *)
Definition eval_whneE_inst :=
  eval_whneE (Σ := si_Σ) (wfΣ := si_wfE) sri_xx_redex sri_xx_reduct eq_refl cli_eval_xx.

(** The closedness of the value [(∀P:Prop. P) → (∀P:Prop. P)] of [cli_eval_xx], from the
    closedness of the redex [(λx:Prop. x → x) (∀P:Prop. P)].
    INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_eval_xx_nondeg *)
Definition eval_closed_cb_inst : closed sri_xx_reduct :=
  eval_closed_cb si_Σ sri_xx_redex sri_xx_reduct eq_refl cli_eval_xx.

(** INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_cF_head_differs *)
Definition whnf_classification'E_inst :=
  whnf_classification'E (Σ := si_Σ) (wfΣ := si_wfE) sri_cF si_ind [] [iv_False] eq_refl
    (whnf_cstrapp _ _ _ _ _ _ [iv_False]) sri_cF_typed.

(** INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_cF_head_differs *)
Definition whnf_classificationE_inst :=
  whnf_classificationE (Σ := si_Σ) (wfΣ := si_wfE) sri_cF si_ind [] [iv_False] cli_axiom_free
    (whnf_cstrapp _ _ _ _ _ _ [iv_False]) sri_cF_typed.

(** INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_cF_head_differs *)
Definition ind_whnf_classification'E_inst :=
  ind_whnf_classification'E (Σ := si_Σ) (wfΣ := si_wfE) sri_cF si_ind [] [iv_False] eq_refl
    cli_notCoInductive sri_cF_typed (whnf_cstrapp _ _ _ _ _ _ [iv_False]).

(** INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_cF_head_differs *)
Definition ind_whnf_classificationE_inst :=
  ind_whnf_classificationE (Σ := si_Σ) (wfΣ := si_wfE) sri_cF si_ind [] [iv_False] cli_axiom_free
    cli_notCoInductive sri_cF_typed (whnf_cstrapp _ _ _ _ _ _ [iv_False]).

(** The fixpoint applied to [c (∀P. P)]: its recursive argument is present
    ([cli_fix_rarg_present]), so the conclusion is the branch for a present argument (an
    axiom-free normal value there is a constructor application), not the product of the absent
    case.
    INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_fix_rarg_present *)
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

(** INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_cF_head_differs *)
Definition value_classificationE_inst :=
  value_classificationE (Σ := si_Σ) (wfΣ := si_wfE) (t := sri_cF) (i := si_ind) (u := []) (args := [iv_False])
    sri_cF_typed cli_cF_value.

(** The application [(λx:Prop. c x) (∀P:Prop. P)], not a canonical form, evaluated to
    [c (∀P:Prop. P)] by a β step that builds the value from the body [c x].
    INSTANCE NONDEGEN PCUICClassificationEtaInstances.cli_lam_c_nondeg *)
Definition eval_classificationE_inst :=
  eval_classificationE (Σ := si_Σ) (wfΣ := si_wfE) (i := si_ind) (u := []) (args := [iv_False])
    cli_lam_c_app_typed sri_cF cli_lam_c_eval.

End ClassificationEtaInstances.
