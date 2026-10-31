(* Distributed under the terms of the MIT license. *)

(* NONDEGEN tags: an INSTANCE NONDEGEN tag is a reader judgment backed by a compiled nontriviality
   lemma, not a mechanical guarantee.
   Measured reader miss rate: at least 20 of 60 instances sampled (seed 202610301905) from the 323 that the focused review of 11092806 had not covered (33.3%, 95% upper bound 44.6%, one-sided Clopper-Pearson): 17 from the union of the verdicts held by two independent reviews (Opus 5: 10; Opus 5.5: 15, 6 of its verdicts borderline at confidence 0.5-0.6), plus three further rows that both reviews had passed and root rulings made by 2026-10-31T03:30Z reclassified under the same standard (S12, S31, S36). 18 of the 20 sampled misses are corrected at frac/eta c825ec02 (S31 and S36 are not), but the sample estimates the rate over ALL instance tags: a comparable share of the unsampled instances is expected to be wrong and is NOT corrected.
   P4 at frac/eta c825ec02: 313 lemmas with a base twin are accounted for: 229 demonstrated (at least one NONDEGEN instance; this count includes 6 targets whose only NONDEGEN instance is judged false (as of 2026-10-31T03:30Z) and uncorrected at frac/eta c825ec02: PCUICClassificationEta.wf_fixpoint_spineE, wf_cofixpoint_spineE, whnf_classificationE, whnf_classification'E, ind_whnf_classificationE and ind_whnf_classification'E), 70 undemonstrable by their own statements (IMPOSSIBLE-only), and 14 with no working instance (NOT-BUILT-only): BDToPCUICEta.wf_rel_weakE; PCUICAlphaEta.eq_context_conversionE, isType_eq_context_conversionE, typing_alpha_propE, wf_local_alphaE; PCUICClassificationEta.typing_spine_nth_errorE, typing_spine_nth_error_NoneE, typing_spine_nth_error_None_prodE (non-degenerate instances for these 3 were built, unlanded and unreviewed as of 2026-10-31T03:30Z); PCUICInversionEta.into_ws_cumulE; PCUICPrincipalityEta.typing_leq_termE; PCUICSREta.prim_app_typing_invE, sr_prim_opE, typing_spine_prim_arg_typesE, typing_spine_prim_argsE. The demonstrated count rests on NONDEGEN tags with the measured miss rate above. As of 2026-10-31T03:30Z, 15 NONDEGEN tags are judged false, and at frac/eta c825ec02 they are uncorrected. 11 are conv → red cases whose input conversion was built from a reduction (for wf_fixpoint_spineE_inst the conv → red step sits inside its target's proof): 7 in BDFromPCUICEtaInstances (red_fix_witnessE_inst, mfix_body_on_conv_redE_fix_inst, red_cofix_witnessE_inst, mfix_body_on_conv_redE_cofix_inst, mfix_on_ind_conv_redE_cofix_inst, wf_fixpointE_wf_fixpoint_red_typed_inst, and sampled row S36 = wf_cofixpointE_wf_cofixpoint_red_inst) and PCUICPrincipalityEtaInstances.T8_Prod_l_plug_inst and T8_Prod_l_of_r_inst, whose targets are outside P4's input set, and PCUICClassificationEtaInstances.wf_fixpoint_spineE_inst and wf_cofixpoint_spineE_inst, whose targets are 2 of the 6 above. 4 are undemonstrable by their own statements (the conclusion is read off the head of the instance's own weak-head-normal witness): PCUICClassificationEtaInstances.whnf_classificationE_inst (sampled row S31), whnf_classification'E_inst, ind_whnf_classificationE_inst and ind_whnf_classification'E_inst, whose targets are the other 4 of the 6. Context of the demonstrations (context = a judgment argument of type list (context_decl term), empty or not by computing its length, not the lemma's Γ parameter): 79 use a non-empty context; 23 have the context as their subject; 20 have a non-empty context that no term or type mentions; 4 undecided; 70 work only at the empty context (10 forced by the statement, 60 by the instance's choice; up to 89 under stricter readings); 33 have no context argument, which is not the same as the empty context. A mechanical sweep flagged at least 31 of the 338 NONDEGEN instances at 0bf9899a, before the retags of LAND8a (eede40b7, 86d983ce), LAND9 (016ec167, 727d49e9) and LAND11-A (6568a017), whose conclusion is convertible to an input sub-derivation (3 of the 31 match the instance itself or its helper rather than an input); of its 9 non-equation flags, 9 were judged bad by 2026-10-31T03:30Z, with the kind-label correct in 6 of 9; it cannot see a cancellation inside the target lemma's own proof or a conclusion that is one part of a pair, and it does not discriminate the 22 closed equations (of the 3 sampled ones judged, S29 is weak only, S44 is not degenerate, and S31 is undemonstrable by its statement). Prose overclaims were not mechanically enumerated, because that detector failed its controls. Root rulings made by 2026-10-31T03:30Z reclassified three sampled rows that both reviews had passed, S36 (the red → conv → red class), S12 (its conclusion is the input's own cumulativity) and S31 (undemonstrable by its statement), raising the sampled rate from at least 17 to at least 20 of 60; the 45-row marker census had 2 reopened as of 2026-10-31T03:30Z. *)

(** * Satisfying instances of the hypotheses of [PCUICSREtaConv]

  Each lemma of [PCUICSREtaConv] that has a premise is applied here to a concrete instance with
  every premise proved. The environment is [si_Σ] of [PCUICCumulativitySpecEtaClosureInstances]
  ([Inductive I (A : Prop) : Prop := c : I A]; [si_cb], [si_wfE]). The terms are those of
  [PCUICEtaFracInstances] and [PCUICWsCumulEtaCtxInstances]: [fi_P := Prop], the β-redex
  [fi_beta := (λx:Prop. x) Prop], the η-redex [fi_eta := λx:Prop. Prop x], the identity [ci_id]
  of [Prop], [ci_False := ∀P:Prop. P], two λ-terms [ci_lam], [ci_lam'] that differ only in a
  binder name.

  Where a lemma relates two things, the instance relates two different things, and its NONDEGEN
  lemma states the difference: [(λx:Prop. x) Prop] against [Prop], [λx:Prop. Prop x] against
  [Prop], two contexts that differ in a let-body, in an assumption type or in a binder name, two
  types [(λy:Prop. y) x] and [x]. Each instance carries its tag (the instance-gate grammar); the
  lemmas that are degenerate by their statement are tagged IMPOSSIBLE at their instance.
  Among them are [conv_context_rel_relnE] and [conv_context_rel_to_extended_listE]: the premise
  forces the assumption/let shape that [reln] reads, so every instance only recomputes [reln] on
  that shape; their instances run on two contexts with a let above an assumption
  ([sc_Γm_reln_nondeg]). The fixpoint-witness rows ([mfix_body_on_red_typeE],
  [mfix_on_ind_red1_typeE]) run on [check_one_fix] and a declared type on which it finds no block,
  reduced to [sc_ty] ([sc_red_A]); the witness [sc_tw] of the premise ([sc_body_on]) is a
  one-step reduct of that type ([sc_closed_red1_tw]), and neither of [sc_ty], [sc_tw] reduces to
  the other ([sc_fix_peak_nondeg]).
  [declared_inductive_closed_params_instE] has no relation in it; its instance has a non-empty
  parameter context. [ws_cumul_ctx_pbE_cons_inv] inverts one constructor of [All2_fold], so its
  instance is tagged IMPOSSIBLE; it runs on the mixed pair of [sc_ctx_m], whose tails and heads
  differ. The reduction lemmas are applied to the β step [(λx:Prop. x → x) (∀P:Prop. P)] ⇝
  [(∀P:Prop. P) → ∀P:Prop. P], whose body uses its variable ([sc_xx_redex], [sc_xx_reduct]):
  as one step ([closed_red1_ws_cumul_pbE]), as a reduction moved into a context
  ([closed_red_from_empty_cb]) and as a step of an assumption type (the four one-declaration
  context rows); [red_it_mkProd_or_LetIn_smash_cb] is applied to a reduction of
  [Π w:Prop. let z := (λX:Prop. X → X) w : Prop in Π x:z → z. Prop] that changes only the let body
  ([sc_red_let_prod]), which [smash_context] substitutes into the type of [x]
  ([red_it_mkProd_or_LetIn_smash_cb_inst_nondeg]);
  [red_has_rec_arg_cb] is applied to the reduction of [Π x:(λy:Prop. y) Prop. Prop] to
  [Π x:Prop. Prop]; [red_expand_let_cb] and [red_expand_letE] to the unfolding of the
  let-bound [z] in [z → z], where [z] is not the whole term ([sc_let_unfolds]).

  WITNESSES: sc_* sc_Γm_reln_nondeg
  (the concrete contexts, definitions and derivations [sc_*] that the instances use; the NONDEGEN
  lemmas among them are classified by their tags) *)

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICLiftSubst PCUICEquality
     PCUICReduction PCUICOnOne PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICWellScopedCumulativity PCUICSubstitution PCUICContextSubst PCUICConfluence PCUICConversion
     PCUICContextConversion
     PCUICEtaI5 PCUICWellScopedCumulativityEta PCUICConversionEtaCongr
     PCUICContextConversionEta PCUICTypingEta PCUICTypingEtaInd PCUICClosedTypEta
     PCUICCumulativitySpecEtaClosureInstances PCUICEtaFracInstances
     PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp PCUICWsCumulEtaCtxInstances PCUICClosedBodies
     PCUICSREtaConv.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

Local Notation WS pb Γ := (ws_cumul_pbE pb si_Σ Γ).

(** ** Concrete data *)

(** One-assumption contexts with the types [(λy:Prop. y) Prop] and [Prop]. *)
Definition sc_Γb : context := [vass si_na fi_beta].

Lemma sc_ctx_beta : ws_cumul_ctx_pbE Conv si_Σ ([] ,,, sc_Γb) ([] ,,, fi_Γ1).
Proof. constructor; [constructor|]. constructor; [reflexivity|exact (fi_WS_beta Conv)]. Qed.

(** One-let contexts whose bodies are [λx:Prop. Prop x] and [Prop], at [Conv]. *)
Definition sc_Γd1 : context := [vdef si_na fi_eta fi_P].
Definition sc_Γd2 : context := [vdef si_na fi_P fi_P].

Lemma sc_rel_d : ws_cumul_ctx_pbE_rel Conv si_Σ [] sc_Γd1 sc_Γd2.
Proof.
  split; [reflexivity|]. constructor; [constructor|].
  constructor; [reflexivity|exact (ci_WS_eta Conv)|]. apply ws_cumul_pbE_refl; reflexivity.
Qed.

(** Mixed contexts: the let [z := λx:Prop. Prop x : Prop] / [z := Prop : Prop] above the
    assumption [x : (λy:Prop. y) Prop] / [x : Prop]. *)
Definition sc_Γm1 : context := [vdef si_na fi_eta fi_P; vass si_na fi_beta].
Definition sc_Γm2 : context := [vdef si_na fi_P fi_P; vass si_na fi_P].

Lemma sc_rel_m : ws_cumul_ctx_pbE_rel Conv si_Σ [] sc_Γm1 sc_Γm2.
Proof.
  split; [reflexivity|]. constructor.
  - constructor; [constructor|]. constructor; [reflexivity|exact (fi_WS_beta Conv)].
  - constructor; [reflexivity| |].
    + apply eta1_ws_cumul_pbE; [reflexivity|reflexivity|exact fi_eta1].
    + apply ws_cumul_pbE_refl; reflexivity.
Qed.

(** The same mixed pair, related as contexts: the tails [x : (λy:Prop. y) Prop] and [x : Prop] by
    [fi_WS_beta], the heads' bodies [λx:Prop. Prop x] and [Prop] by [fi_eta1]. *)
Lemma sc_ctx_m : ws_cumul_ctx_pbE Conv si_Σ sc_Γm1 sc_Γm2.
Proof.
  constructor.
  - constructor; [constructor|]. constructor; [reflexivity|exact (fi_WS_beta Conv)].
  - constructor; [reflexivity| |].
    + apply eta1_ws_cumul_pbE; [reflexivity|reflexivity|exact fi_eta1].
    + apply ws_cumul_pbE_refl; reflexivity.
Qed.

(** What [reln] reads of [sc_Γm1]: it keeps the assumption and skips the let, whose index shift
    the output shows ([tRel (n + 1)]), so the output is not empty; and the two related contexts
    differ. *)
Lemma sc_Γm_reln_nondeg :
  [/\ (forall acc n, reln acc n sc_Γm1 = tRel (n + 1) :: acc),
      to_extended_list sc_Γm1 = [tRel 1] &
      sc_Γm1 <> sc_Γm2].
Proof. split; [intros acc n; reflexivity|reflexivity|discriminate]. Qed.

(** ** Items 1-2 *)

(** The inversion of [sc_ctx_m]: the conclusion relates the tails [x : (λy:Prop. y) Prop] and
    [x : Prop], and the heads [z := λx:Prop. Prop x : Prop] and [z := Prop : Prop] in the first tail.
    INSTANCE IMPOSSIBLE: [ws_cumul_ctx_pbE_cons_inv] inverts the one [All2_fold] constructor that relates two non-empty contexts (its proof is [depelim] then [assumption]), so in every instance and environment its conclusion is the two premises of that constructor, a piece of its own premise. *)
Lemma ws_cumul_ctx_pbE_cons_inv_inst :
  ws_cumul_ctx_pbE Conv si_Σ [vass si_na fi_beta] [vass si_na fi_P] ×
  ws_cumul_declsE Conv si_Σ [vass si_na fi_beta] (vdef si_na fi_eta fi_P) (vdef si_na fi_P fi_P).
Proof.
  exact (ws_cumul_ctx_pbE_cons_inv (d := vdef si_na fi_eta fi_P) (d' := vdef si_na fi_P fi_P) sc_ctx_m).
Qed.

(** The contexts [x : (λy:Prop. y) Prop] and [x : Prop] differ, and the bodies [λz:Prop. Prop z]
    and [Prop] differ. *)
Lemma ws_cumul_pbE_it_mkLambda_or_LetIn_inst_nondeg : sc_Γb <> fi_Γ1 /\ fi_eta <> fi_P.
Proof. split; discriminate. Qed.

(** [λx:(λy:Prop. y) Prop. λz:Prop. Prop z] and [λx:Prop. Prop].
    INSTANCE NONDEGEN PCUICSREtaConvInstances.ws_cumul_pbE_it_mkLambda_or_LetIn_inst_nondeg *)
Lemma ws_cumul_pbE_it_mkLambda_or_LetIn_inst :
  WS Cumul [] (it_mkLambda_or_LetIn sc_Γb fi_eta) (it_mkLambda_or_LetIn fi_Γ1 fi_P).
Proof.
  apply (ws_cumul_pbE_it_mkLambda_or_LetIn (Γ := []) (Δ1 := sc_Γb) (Δ2 := fi_Γ1) sc_ctx_beta).
  apply eta1_ws_cumul_pbE; [reflexivity|reflexivity|exact fi_eta1].
Qed.

(** [x → x] over [x : Prop]: the variable [x] occurs in the domain and under the binder. *)
Definition sc_x_to_x : term := tProd si_na (tRel 0) (tRel 1).

(** The type [x → x] is not a bare variable; substituting [(λy:Prop. y) Prop] for [x] gives
    [(λy:Prop. y) Prop → (λy:Prop. y) Prop], and substituting [Prop] gives [Prop → Prop]; each
    result is not the term substituted, and the two results differ. *)
Lemma substitution_ws_cumul_ctx_pbE_red_subst_inst_nondeg :
  [/\ (forall k, sc_x_to_x <> tRel k),
      subst_context [fi_beta] 0 [vass si_na sc_x_to_x] = [vass si_na (tProd si_na fi_beta fi_beta)],
      subst_context [fi_P] 0 [vass si_na sc_x_to_x] = [vass si_na (tProd si_na fi_P fi_P)],
      tProd si_na fi_beta fi_beta <> fi_beta /\ tProd si_na fi_P fi_P <> fi_P &
      tProd si_na fi_beta fi_beta <> tProd si_na fi_P fi_P].
Proof. split; [intros k; discriminate|reflexivity|reflexivity|split; discriminate|discriminate]. Qed.

(** Substituting [(λy:Prop. y) Prop] and [Prop], related by [fi_closed_red_beta], for [x] in
    [x' : x → x] ([sc_x_to_x]); the results are given by
    [substitution_ws_cumul_ctx_pbE_red_subst_inst_nondeg].
    INSTANCE NONDEGEN PCUICSREtaConvInstances.substitution_ws_cumul_ctx_pbE_red_subst_inst_nondeg *)
Lemma substitution_ws_cumul_ctx_pbE_red_subst_inst :
  ws_cumul_ctx_pbE Conv si_Σ ([] ,,, subst_context [fi_beta] 0 [vass si_na sc_x_to_x])
    ([] ,,, subst_context [fi_P] 0 [vass si_na sc_x_to_x]).
Proof.
  apply (substitution_ws_cumul_ctx_pbE_red_subst (Γ := []) (Δ := [vass si_na fi_P])
           (s := [fi_beta]) (s' := [fi_P])).
  - reflexivity.
  - constructor; [exact fi_closed_red_beta|constructor].
  - exact ci_untyped_subslet.
Qed.

(** The two types differ (in a binder name). *)
Lemma eq_context_upto_ws_cumul_ctx_pbE_inst_nondeg : ci_lam <> ci_lam'.
Proof. discriminate. Qed.

(** Two contexts whose types [compare_term] relates without being equal.
    INSTANCE NONDEGEN PCUICSREtaConvInstances.eq_context_upto_ws_cumul_ctx_pbE_inst_nondeg *)
Lemma eq_context_upto_ws_cumul_ctx_pbE_inst :
  ws_cumul_ctx_pbE Cumul si_Σ [vass si_na ci_lam] [vass si_na ci_lam'].
Proof.
  apply (eq_context_upto_ws_cumul_ctx_pbE (Γ := [vass si_na ci_lam]) (Γ' := [vass si_na ci_lam']));
    [reflexivity|reflexivity|].
  constructor; [constructor|]. constructor; [reflexivity|exact (ci_eq_lam Cumul)].
Qed.

(** The β-redex [(λx:Prop. x → x) (∀P:Prop. P)] (the body [sc_x_to_x] under [λx:Prop]) and its
    contractum [(∀P:Prop. P) → ∀P:Prop. P]. *)
Definition sc_xx_redex : term := tApp (tLambda si_na fi_P sc_x_to_x) ci_False.
Definition sc_xx_reduct : term := tProd si_na ci_False ci_False.

Lemma sc_xx_red1 (Γ : context) : red1 si_Σ Γ sc_xx_redex sc_xx_reduct.
Proof. exact (red_beta si_Σ Γ si_na fi_P sc_x_to_x ci_False). Qed.

(** ** Item 3 *)

(** The fixpoint witness, on the check [check_one_fix] that [wf_fixpointE] uses. The declared type
    [sc_A := Π y:(λX:Prop. I X) (∀P.P). (λx:Prop. x → x) (∀P.P)] hides the inductive [I] behind a
    β-redex in its domain ([sc_IX]); its codomain is the β-redex [sc_xx_redex]. Two different
    one-step reducts of [sc_A]: [sc_ty] contracts the codomain (the reduction given to the lemmas,
    [sc_red_A]); [sc_tw] contracts the domain to [I (∀P.P)] ([sc_I]), the conversion witness
    ([sc_closed_red1_tw]). *)
Definition sc_IX : term := tApp (tLambda si_na fi_P (tApp (tInd si_ind []) (tRel 0))) ci_False.
Definition sc_I : term := tApp (tInd si_ind []) ci_False.
Definition sc_A : term := tProd si_na sc_IX sc_xx_redex.
Definition sc_ty : term := tProd si_na sc_IX sc_xx_reduct.
Definition sc_tw : term := tProd si_na sc_I sc_xx_redex.
Definition sc_d : def term := {| dname := si_na; dtype := sc_A; dbody := fi_P; rarg := 0 |}.

(** The β step of the codomain of [sc_A]. *)
Lemma sc_red_A : si_Σ ;;; [] ⊢ sc_A ⇝ sc_ty.
Proof. split; [reflexivity|reflexivity|]. apply rt_step. apply prod_red_r. exact (sc_xx_red1 _). Qed.

(** The β step of the domain of [sc_A]. *)
Lemma sc_closed_red1_tw : closed_red1 si_Σ [] sc_A sc_tw.
Proof.
  split; [reflexivity|reflexivity|]. apply prod_red_l.
  exact (red_beta si_Σ [] si_na fi_P (tApp (tInd si_ind []) (tRel 0)) ci_False).
Qed.

(** The witness [sc_tw] of [sc_d], converted to [sc_A] by the domain step [sc_closed_red1_tw]. *)
Lemma sc_body_on : mfix_body_on check_one_fix (conv_witnessE si_Σ []) si_kn sc_d.
Proof.
  exists sc_tw. split; [reflexivity|]. split; [reflexivity|].
  exact (ws_cumul_pbE_forget_spec (closed_red1_ws_cumul_pbE sc_closed_red1_tw)).
Qed.

(** [check_one_fix] finds no block on the declared type [sc_A] nor on its reduct [sc_ty], so a
    witness for [def_with_type sc_d sc_ty] cannot be [sc_ty] itself; it finds [I] on the witness
    [sc_tw]. Neither of [sc_ty], [sc_tw] reduces to the other, so a conversion between them is
    neither a reduction nor the inverse of one, and no reduction from [sc_A] to [sc_tw] passes
    through [sc_ty]; both differ from [sc_A]. *)
Lemma sc_fix_peak_nondeg :
  [/\ check_one_fix sc_d = None /\ check_one_fix (def_with_type sc_d sc_ty) = None,
      check_one_fix (def_with_type sc_d sc_tw) = Some si_kn,
      (si_Σ ;;; [] ⊢ sc_ty ⇝ sc_tw) -> False,
      (si_Σ ;;; [] ⊢ sc_tw ⇝ sc_ty) -> False &
      sc_ty <> dtype sc_d /\ sc_tw <> dtype sc_d].
Proof.
  split; [split; reflexivity|reflexivity| | |split; discriminate].
  - intros r. destruct (invert_red_prod_cb r) as [dom' [codom' [e _ rc]]].
    unfold sc_tw in e. injection e. intros; subst.
    destruct (invert_red_prod_cb rc) as [d2 [c2 [e2 _ _]]]. discriminate e2.
  - intros r. destruct (invert_red_prod_cb r) as [dom' [codom' [e rd _]]].
    unfold sc_ty in e. injection e. intros; subst.
    destruct (invert_red_mkApps_tInd_cb (ind := si_ind) (u := []) [ci_False] _ rd) as [args' [e2 _ _]].
    apply (f_equal decompose_app) in e2.
    rewrite (decompose_app_mkApps (tInd si_ind []) args' eq_refl) in e2.
    discriminate e2.
Qed.

(** The reduct [sc_ty] ([sc_red_A]) of the declared type [sc_A] gets a witness that
    [check_one_fix] accepts. [check_one_fix] finds no block on [sc_ty]; the witness [sc_tw] of the
    premise ([sc_body_on]) is a one-step reduct of [sc_A] ([sc_closed_red1_tw]); neither of
    [sc_ty], [sc_tw] reduces to the other ([sc_fix_peak_nondeg]).
    INSTANCE NONDEGEN PCUICSREtaConvInstances.sc_fix_peak_nondeg *)
Lemma mfix_body_on_red_typeE_inst :
  mfix_body_on check_one_fix (conv_witnessE si_Σ []) si_kn (def_with_type sc_d sc_ty).
Proof. exact (mfix_body_on_red_typeE (d := sc_d) sc_red_A sc_body_on). Qed.

(** A block of two bodies, with the recursivity check of [wf_fixpointE]: the type of the second
    body takes the reduction [sc_red_A], the first is unchanged; [sc_ty] and the witness [sc_tw] of
    the premise ([sc_body_on]) are as in [mfix_body_on_red_typeE_inst] ([sc_fix_peak_nondeg]).
    INSTANCE NONDEGEN PCUICSREtaConvInstances.sc_fix_peak_nondeg *)
Lemma mfix_on_ind_red1_typeE_inst :
  mfix_on_ind check_one_fix (conv_witnessE si_Σ [])
    (fun mind => check_recursivity_kind (lookup_env si_Σ) mind Finite) [sc_d; def_with_type sc_d sc_ty].
Proof.
  apply (mfix_on_ind_red1_typeE [] [sc_d; sc_d]).
  - apply OnOne2_tl. constructor. split; [exact sc_red_A|reflexivity].
  - exists si_kn. split; [discriminate|]. split; [|reflexivity].
    constructor; [exact sc_body_on|constructor; [exact sc_body_on|constructor]].
Qed.

(** [reln] on the mixed contexts related by [sc_rel_m] ([sc_Γm_reln_nondeg]).
    INSTANCE IMPOSSIBLE: the proof of [conv_context_rel_relnE] takes the [All2_fold] component of its premise and runs an induction on it with [auto]: [reln] reads only whether each declaration is an assumption or a let, and [All2_fold] of the declaration relation forces each pair of declarations to have the same shape; so in every instance and environment the equation follows from the shape the premise forces, and the relation of the types is never used. *)
Lemma conv_context_rel_relnE_inst : forall acc n, reln acc n sc_Γm1 = reln acc n sc_Γm2.
Proof. exact (conv_context_rel_relnE [] sc_Γm1 sc_Γm2 sc_rel_m). Qed.

(** [to_extended_list] on the same contexts ([sc_Γm_reln_nondeg]).
    INSTANCE IMPOSSIBLE: the proof of [conv_context_rel_to_extended_listE] unfolds [to_extended_list] to [reln [] 0] and applies [conv_context_rel_relnE], an induction on the [All2_fold] component of its premise with [auto] (the premise forces each pair of declarations to have the same assumption/let shape, which is all [reln] reads); so in every instance and environment the equation follows from the shape the premise forces, and the relation of the types is never used. *)
Lemma conv_context_rel_to_extended_listE_inst : to_extended_list sc_Γm1 = to_extended_list sc_Γm2.
Proof. exact (conv_context_rel_to_extended_listE (Δ := sc_Γm1) (Δ' := sc_Γm2) sc_rel_m). Qed.

(** Two contexts that differ only in a binder name.
    INSTANCE IMPOSSIBLE: the premise [eq_context_upto_names Δ Δ'] forces each pair of declarations to have identical types (and bodies), only the binder names may differ ([eq_decl_upto_names]), and the proof of [eq_context_alpha_convE] relates each type (and body) to itself by [ws_cumul_pbE_refl]; so in every instance and environment every declaration comparison of the conclusion is reflexive. *)
Lemma eq_context_alpha_convE_inst :
  ws_cumul_ctx_pbE_rel Conv si_Σ [] [vass si_na fi_P] [vass (mkBindAnn (nNamed "x") Relevant) fi_P].
Proof.
  apply (eq_context_alpha_convE [] [vass si_na fi_P] [vass (mkBindAnn (nNamed "x") Relevant) fi_P]);
    [repeat constructor|reflexivity|reflexivity].
Qed.

Definition sc_nas : list aname := [mkBindAnn (nNamed "x") Relevant].

(** The renaming changes the context, and the two related contexts differ in the let-body. *)
Lemma conv_ctx_set_binder_nameE_inst_nondeg :
  map2 set_binder_name sc_nas sc_Γd1 <> sc_Γd1 /\ sc_Γd1 <> sc_Γd2.
Proof. split; discriminate. Qed.

(* INSTANCE NONDEGEN PCUICSREtaConvInstances.conv_ctx_set_binder_nameE_inst_nondeg *)
Lemma conv_ctx_set_binder_nameE_inst :
  ws_cumul_ctx_pbE_rel Conv si_Σ [] (map2 set_binder_name sc_nas sc_Γd1) (map2 set_binder_name sc_nas sc_Γd2).
Proof.
  apply (conv_ctx_set_binder_nameE [] sc_Γd1 sc_Γd2 sc_nas);
    [repeat constructor|repeat constructor|exact sc_rel_d].
Qed.

(** One-assumption contexts with the types [(λx:Prop. x → x) (∀P.P)] and [(∀P.P) → ∀P.P]. *)
Definition sc_Γxx : context := [vass si_na sc_xx_redex].
Definition sc_Γxx' : context := [vass si_na sc_xx_reduct].

(** One step of context reduction: the type [sc_xx_redex] reduces to [sc_xx_reduct]. *)
Lemma sc_one_xx :
  OnOne2_local_env (fun Δ : context => on_one_decl (red1 si_Σ ([] ,,, Δ))) sc_Γxx sc_Γxx'.
Proof.
  apply onone2_localenv_cons_abs. cbn. split; [reflexivity|].
  exact (sc_xx_red1 []).
Qed.

(** The β step of the assumption type runs through a body that uses its variable ([x → x] is
    not a bare variable); its contractum is neither the argument [∀P.P] nor the body, and the two
    contexts differ. *)
Lemma sc_Γxx_nondeg :
  [/\ (forall k, sc_x_to_x <> tRel k), sc_xx_reduct <> ci_False, sc_xx_reduct <> sc_x_to_x &
      sc_Γxx <> sc_Γxx'].
Proof. split; [intros k; discriminate|discriminate|discriminate|discriminate]. Qed.

(* INSTANCE NONDEGEN PCUICSREtaConvInstances.sc_Γxx_nondeg *)
Lemma red_one_decl_red_ctx_cb_inst : red_ctx si_Σ ([] ,,, sc_Γxx) ([] ,,, sc_Γxx').
Proof. exact (red_one_decl_red_ctx_cb (Γ := []) (Δ := sc_Γxx) (Δ' := sc_Γxx') eq_refl sc_one_xx). Qed.

(* INSTANCE NONDEGEN PCUICSREtaConvInstances.sc_Γxx_nondeg *)
Lemma into_closed_red_ctx_cb_inst : closed_red_ctx si_Σ ([] ,,, sc_Γxx) ([] ,,, sc_Γxx').
Proof. exact (into_closed_red_ctx_cb (Γ := [] ,,, sc_Γxx) (Δ := [] ,,, sc_Γxx') eq_refl red_one_decl_red_ctx_cb_inst). Qed.

(* INSTANCE NONDEGEN PCUICSREtaConvInstances.sc_Γxx_nondeg *)
Lemma red_one_decl_red_context_cb_inst : closed_red_ctx si_Σ ([] ,,, sc_Γxx) ([] ,,, sc_Γxx').
Proof. exact (red_one_decl_red_context_cb (Γ := []) (Δ := sc_Γxx) (Δ' := sc_Γxx') eq_refl sc_one_xx). Qed.

(* INSTANCE NONDEGEN PCUICSREtaConvInstances.sc_Γxx_nondeg *)
Lemma red_one_decl_ws_cumul_ctx_pbE_inst : ws_cumul_ctx_pbE Conv si_Σ ([] ,,, sc_Γxx) ([] ,,, sc_Γxx').
Proof. exact (red_one_decl_ws_cumul_ctx_pbE (Γ := []) (Δ := sc_Γxx) (Δ' := sc_Γxx') eq_refl sc_one_xx). Qed.

(* INSTANCE IMPOSSIBLE: the premise T = U makes both sides of the conclusion the same term, in every instance and environment *)
Lemma ws_cumul_pbE_meta_refl_inst : WS Conv [] fi_P fi_P.
Proof. exact (ws_cumul_pbE_meta_refl (Σ := si_Σ) (Γ := []) (T := fi_P) (U := fi_P) eq_refl eq_refl eq_refl). Qed.

(* This instance relates the β-pair [fi_beta], [fi_P].
   INSTANCE IMPOSSIBLE: the premise U = V makes the conclusion the first premise (T related to U), in every instance and environment *)
Lemma ws_cumul_pbE_eq_trans_inst : WS Conv [] fi_beta fi_P.
Proof. exact (ws_cumul_pbE_eq_trans (fi_WS_beta Conv) eq_refl). Qed.

(* This instance relates the β-pair [fi_beta], [fi_P].
   INSTANCE IMPOSSIBLE: the premise T = U makes the conclusion the second premise (U related to V), in every instance and environment *)
Lemma eq_ws_cumul_pbE_trans_inst : WS Conv [] fi_beta fi_P.
Proof. exact (eq_ws_cumul_pbE_trans eq_refl (fi_WS_beta Conv)). Qed.

(* This instance relates [[fi_beta]] with [[fi_P]].
   INSTANCE IMPOSSIBLE: the premise U = V makes the conclusion the first premise (T related to U), in every instance and environment *)
Lemma ws_cumul_pbE_terms_eq_trans_inst : ws_cumul_pbE_terms si_Σ [] [fi_beta] [fi_P].
Proof. exact (ws_cumul_pbE_terms_eq_trans ci_WT eq_refl). Qed.

(* This instance relates [[fi_beta]] with [[fi_P]].
   INSTANCE IMPOSSIBLE: the premise T = U makes the conclusion the second premise (U related to V), in every instance and environment *)
Lemma eq_ws_cumul_pbE_terms_trans_inst : ws_cumul_pbE_terms si_Σ [] [fi_beta] [fi_P].
Proof. exact (eq_ws_cumul_pbE_terms_trans eq_refl ci_WT). Qed.

(** Over [x : Prop], the let-contexts [z := (λy:Prop. y) x : Prop] and [z := x : Prop]: their
    bodies are a β-pair that refers to [x]. *)
Definition sc_Δo1 : context := [vdef si_na (tApp ci_id (tRel 0)) fi_P].
Definition sc_Δo2 : context := [vdef si_na (tRel 0) fi_P].

Lemma sc_closed_red1_open : closed_red1 si_Σ fi_Γ1 (tApp ci_id (tRel 0)) (tRel 0).
Proof. split; [reflexivity|reflexivity|exact (red_beta si_Σ fi_Γ1 si_na fi_P (tRel 0) (tRel 0))]. Qed.

Lemma sc_ctx_open : ws_cumul_ctx_pbE Conv si_Σ (fi_Γ1 ,,, sc_Δo1) (fi_Γ1 ,,, sc_Δo2).
Proof.
  constructor; [exact (ws_cumul_ctx_pbE_refl_pb (Γ := fi_Γ1) eq_refl)|].
  constructor; [reflexivity|exact (closed_red1_ws_cumul_pbE sc_closed_red1_open)|].
  apply ws_cumul_pbE_refl; reflexivity.
Qed.

(** The lift by [#|fi_Γ1|] changes [sc_Δo1] (its body refers to [x]); the two contexts
    [z := (λy:Prop. y) x : Prop] and [z := x : Prop] differ, and so do their two lifts, which end
    the two contexts the instance relates. *)
Lemma weakening_ws_cumul_ctx_pbE_inst_nondeg :
  lift_context #|fi_Γ1| 0 sc_Δo1 <> sc_Δo1 /\ sc_Δo1 <> sc_Δo2 /\
  lift_context #|fi_Γ1| 0 sc_Δo1 <> lift_context #|fi_Γ1| 0 sc_Δo2.
Proof. split; [discriminate|split; discriminate]. Qed.

(** Weakening the let-contexts [z := (λy:Prop. y) x : Prop] and [z := x : Prop] by [w : Prop],
    inserted between [x : Prop] and [z].
    INSTANCE NONDEGEN PCUICSREtaConvInstances.weakening_ws_cumul_ctx_pbE_inst_nondeg *)
Lemma weakening_ws_cumul_ctx_pbE_inst :
  ws_cumul_ctx_pbE Conv si_Σ (fi_Γ1 ,,, fi_Γ1 ,,, lift_context #|fi_Γ1| 0 sc_Δo1)
    (fi_Γ1 ,,, fi_Γ1 ,,, lift_context #|fi_Γ1| 0 sc_Δo2).
Proof.
  apply (weakening_ws_cumul_ctx_pbE (Γ := fi_Γ1) (Δ := fi_Γ1) sc_ctx_open).
  exact (ws_cumul_ctx_pbE_refl_pb (Γ := fi_Γ1 ,,, fi_Γ1) eq_refl).
Qed.

Lemma sc_closed_red1_xx : closed_red1 si_Σ [] sc_xx_redex sc_xx_reduct.
Proof. split; [reflexivity|reflexivity|exact (sc_xx_red1 [])]. Qed.

(** The two related terms are the β-redex [(λx:Prop. x → x) (∀P.P)] and its contractum
    [(∀P.P) → ∀P.P]: they differ, the body [x → x] is not a bare variable, and the contractum is
    neither the argument [∀P.P] nor the body. *)
Lemma closed_red1_ws_cumul_pbE_inst_nondeg :
  [/\ sc_xx_redex <> sc_xx_reduct, (forall k, sc_x_to_x <> tRel k), sc_xx_reduct <> ci_False &
      sc_xx_reduct <> sc_x_to_x].
Proof. split; [discriminate|intros k; discriminate|discriminate|discriminate]. Qed.

(* INSTANCE NONDEGEN PCUICSREtaConvInstances.closed_red1_ws_cumul_pbE_inst_nondeg *)
Lemma closed_red1_ws_cumul_pbE_inst : WS Conv [] sc_xx_redex sc_xx_reduct.
Proof. exact (closed_red1_ws_cumul_pbE (t := sc_xx_redex) (u := sc_xx_reduct) sc_closed_red1_xx). Qed.

(** *** The typed lemmas *)

(* INSTANCE IMPOSSIBLE: the conclusion relates the term t with itself, in every instance and environment *)
Lemma wt_cumul_pb_reflE_inst : WS Conv fi_Γ1 (tRel 0) (tRel 0).
Proof. exact (wt_cumul_pb_reflE (Σ := si_Σ) (wfΣ := si_wfE) ci_x_typed). Qed.

(* INSTANCE IMPOSSIBLE: the conclusion relates the list ts with itself, in every instance and environment *)
Lemma wt_terms_ws_cumul_pbE_inst : ws_cumul_pbE_terms si_Σ fi_Γ1 [tRel 0] [tRel 0].
Proof.
  apply (wt_terms_ws_cumul_pbE (Σ := si_Σ) (wfΣ := si_wfE)).
  constructor; [exists fi_P; exact ci_x_typed|constructor].
Qed.

(** The context [x : Prop, h : (λy:Prop. y) x]: [h] has a type that β-reduces to [x]. *)
Definition sc_Γh : context := fi_Γ1 ,, vass si_na (tApp ci_id (tRel 0)).

Lemma sc_wf_Γh : wf_localE si_Σ sc_Γh.
Proof.
  apply localenv_cons_abs; [exact ci_wf_Γ1|]. apply ci_vass_Prop.
  exact (ci_app_typed fi_Γ1 (tRel 0) ci_wf_Γ1 ci_x_typed).
Qed.

Lemma sc_h_typed : si_Σ ;;; sc_Γh |-E tRel 0 : tApp ci_id (tRel 1).
Proof. exact (typeE_Rel _ _ 0 (vass si_na (tApp ci_id (tRel 0))) sc_wf_Γh eq_refl). Qed.

Lemma sc_x_typed : si_Σ ;;; sc_Γh |-E tRel 1 : fi_P.
Proof. exact (typeE_Rel _ _ 1 (vass si_na fi_P) sc_wf_Γh eq_refl). Qed.

Lemma sc_red_h : red si_Σ sc_Γh (tApp ci_id (tRel 1)) (tRel 1).
Proof. apply rt_step. unfold ci_id. apply red_beta. Qed.

(** The type [(λy:Prop. y) x] of [h] and the type [x] it is moved to differ. *)
Lemma type_Cumul_altE_inst_nondeg : tApp ci_id (tRel 1) <> tRel 1.
Proof. discriminate. Qed.

(* INSTANCE NONDEGEN PCUICSREtaConvInstances.type_Cumul_altE_inst_nondeg *)
Lemma type_Cumul_altE_inst : si_Σ ;;; sc_Γh |-E tRel 0 : tRel 1.
Proof.
  exact (type_Cumul_altE (Σ := si_Σ) (wfΣ := si_wfE) sc_Γh (tRel 0) (tApp ci_id (tRel 1)) (tRel 1)
           sc_h_typed (ci_on_typeE_Prop _ _ sc_x_typed) (JoinE_red_l si_Σ sc_Γh Cumul _ _ sc_red_h)).
Qed.

(** ** Environment and reduction facts *)

(** The parameter context [A : Prop] of [I] is not empty: the closedness is checked on a
    declaration. *)
Lemma declared_inductive_closed_params_instE_inst_nondeg : ind_params si_mdecl <> [].
Proof. discriminate. Qed.

(** [closed_ctx] is a boolean, so it computes on every concrete parameter context; [I] is
    monomorphic, so [subst_instance [Set]] leaves its parameters unchanged.
    INSTANCE NONDEGEN PCUICSREtaConvInstances.declared_inductive_closed_params_instE_inst_nondeg *)
Lemma declared_inductive_closed_params_instE_inst : closed_ctx (subst_instance [Level.lzero] (ind_params si_mdecl)).
Proof.
  exact (declared_inductive_closed_params_instE (Σ := si_Σ) (wfΣ := si_wfE) (mdecl := si_mdecl)
           (u := [Level.lzero]) si_declared_inductive).
Qed.

(** The let [z := ∀P:Prop. P : Prop]. *)
Lemma sc_wf_let : wf_localE si_Σ ([] ,,, [vdef si_na ci_False fi_P]).
Proof.
  apply localenv_cons_def; [constructor|].
  split; [exact (ci_False_typed [] localenv_nil)|].
  exists (Sort.super sProp). split; [exact (ci_typeE_P [] localenv_nil)|]. split; [exact I|reflexivity].
Qed.

(** [z → z] ([sc_x_to_x]) is not a bare variable: [z] occurs in the domain and under the binder.
    Unfolding [z] gives [(∀P:Prop. P) → ∀P:Prop. P], which is neither [z → z] nor the body
    [∀P:Prop. P]. *)
Lemma sc_let_unfolds :
  [/\ (forall k, sc_x_to_x <> tRel k),
      lift0 1 (subst1 ci_False 0 sc_x_to_x) = tProd si_na ci_False ci_False,
      tProd si_na ci_False ci_False <> sc_x_to_x &
      tProd si_na ci_False ci_False <> ci_False].
Proof. split; [intros k; discriminate|reflexivity|discriminate|discriminate]. Qed.

(** The unfolding of the let-bound [z] in [z → z], under [z := ∀P:Prop. P : Prop]
    ([sc_let_unfolds]).
    INSTANCE NONDEGEN PCUICSREtaConvInstances.sc_let_unfolds *)
Lemma red_expand_let_cb_inst :
  si_Σ ;;; [] ,, vdef si_na ci_False fi_P ⊢ sc_x_to_x ⇝ lift0 1 (subst1 ci_False 0 sc_x_to_x).
Proof.
  exact (red_expand_let_cb (Σ := si_Σ) (Γ := []) (na := si_na) (b := ci_False) (ty := fi_P) (t := sc_x_to_x)
           eq_refl eq_refl).
Qed.

(** The same unfolding, from the [wf_localE] of the let ([sc_wf_let]; [sc_let_unfolds]).
    INSTANCE NONDEGEN PCUICSREtaConvInstances.sc_let_unfolds *)
Lemma red_expand_letE_inst :
  si_Σ ;;; [] ,, vdef si_na ci_False fi_P ⊢ sc_x_to_x ⇝ lift0 1 (subst1 ci_False 0 sc_x_to_x).
Proof.
  exact (red_expand_letE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := []) (na := si_na) (b := ci_False) (ty := fi_P)
           (t := sc_x_to_x) sc_wf_let eq_refl).
Qed.

(** The target context [x : Prop] is not the empty context the reduction starts in; the
    reduction is the β step of [(λx:Prop. x → x) (∀P.P)], whose body is not a bare variable, and
    its contractum [(∀P.P) → ∀P.P] is neither the redex, the argument nor the body. *)
Lemma closed_red_from_empty_cb_inst_nondeg :
  fi_Γ1 <> [] /\
  [/\ (forall k, sc_x_to_x <> tRel k), sc_xx_redex <> sc_xx_reduct, sc_xx_reduct <> ci_False &
      sc_xx_reduct <> sc_x_to_x].
Proof. split; [discriminate|split; [intros k; discriminate|discriminate|discriminate|discriminate]]. Qed.

Lemma sc_red_xx : red si_Σ [] sc_xx_redex sc_xx_reduct.
Proof. apply rt_step. exact (sc_xx_red1 []). Qed.

(** The reduction [sc_xx_redex ⇝ sc_xx_reduct] in the empty context, moved into [x : Prop].
    INSTANCE NONDEGEN PCUICSREtaConvInstances.closed_red_from_empty_cb_inst_nondeg *)
Lemma closed_red_from_empty_cb_inst : si_Σ ;;; fi_Γ1 ⊢ sc_xx_redex ⇝ sc_xx_reduct.
Proof.
  exact (closed_red_from_empty_cb (Σ := si_Σ) (Γ := fi_Γ1) (M := sc_xx_redex) (N := sc_xx_reduct)
           eq_refl eq_refl sc_red_xx).
Qed.

(** [Π x:(λy:Prop. y) Prop. Prop] reduces to [Π x:Prop. Prop] in its domain. *)
Lemma sc_red_prod : si_Σ ;;; [] ⊢ it_mkProd_or_LetIn sc_Γb fi_P ⇝ tProd si_na fi_P fi_P.
Proof.
  split; [reflexivity|reflexivity|]. apply rt_step. cbn. apply prod_red_l.
  exact (red_beta si_Σ [] si_na fi_P (tRel 0) fi_P).
Qed.

(** The telescope [Π w:Prop. let z := (λX:Prop. X → X) w : Prop in Π x:z → z. Prop]: a let between
    two assumptions, whose body [sc_wb] uses [w], and the assumption type [z → z] ([sc_x_to_x]
    under [w], [z]), which uses [z] twice. [sc_Γzw'] is the same telescope with the let body
    contracted to [w → w] ([sc_x_to_x] under [w]). *)
Definition sc_wb : term := tApp (tLambda si_na fi_P sc_x_to_x) (tRel 0).
Definition sc_Γzw : context := [vass si_na sc_x_to_x; vdef si_na sc_wb fi_P; vass si_na fi_P].
Definition sc_Γzw' : context := [vass si_na sc_x_to_x; vdef si_na sc_x_to_x fi_P; vass si_na fi_P].
Definition sc_u : term := it_mkProd_or_LetIn sc_Γzw' fi_P.

(** The β step of the let body, under [w : Prop]. *)
Lemma sc_red_let_prod : si_Σ ;;; [] ⊢ it_mkProd_or_LetIn sc_Γzw fi_P ⇝ sc_u.
Proof.
  split; [reflexivity|reflexivity|]. apply rt_step. cbn. apply prod_red_r. apply letin_red_def.
  exact (red_beta si_Σ _ si_na fi_P sc_x_to_x (tRel 0)).
Qed.

(** [smash_context] substitutes the let body into the type [z → z] of [x]: in the input telescope
    the smashed type of [x] (index 1, after [w]) is [z → z] with [sc_wb] substituted, in the
    reduct's telescope it is [z → z] with the contracted body substituted, and the two differ. The
    type [z → z] is not a bare variable, so neither smashed type is the let body it substitutes.
    The prefix of the conclusion's context is [w : Prop], not empty. *)
Lemma red_it_mkProd_or_LetIn_smash_cb_inst_nondeg :
  [/\ smash_context [] sc_Γzw = [vass si_na (subst [sc_wb] 0 sc_x_to_x); vass si_na fi_P],
      decompose_prod_assum [] sc_u = (sc_Γzw', fi_P) /\
        smash_context [] sc_Γzw' = [vass si_na (subst [sc_x_to_x] 0 sc_x_to_x); vass si_na fi_P],
      subst [sc_wb] 0 sc_x_to_x <> subst [sc_x_to_x] 0 sc_x_to_x,
      (forall k, sc_x_to_x <> tRel k) /\ subst [sc_wb] 0 sc_x_to_x <> sc_wb /\
        subst [sc_x_to_x] 0 sc_x_to_x <> sc_x_to_x &
      skipn (#|smash_context [] sc_Γzw| - 1) (smash_context [] sc_Γzw) = [vass si_na fi_P]].
Proof.
  split; [reflexivity|split; reflexivity|discriminate|
          split; [intros k; discriminate|split; discriminate]|reflexivity].
Qed.

(** The argument at index 1 of the smashed telescope is [x], whose smashed type is [z → z] with the
    let body substituted; the input reduction goes from [sc_Γzw] to [sc_Γzw'], which differ only in
    the let body ([sc_red_let_prod]; [red_it_mkProd_or_LetIn_smash_cb_inst_nondeg]).
    INSTANCE NONDEGEN PCUICSREtaConvInstances.red_it_mkProd_or_LetIn_smash_cb_inst_nondeg *)
Lemma red_it_mkProd_or_LetIn_smash_cb_inst :
  ∑ ctx' t' d,
    [× decompose_prod_assum [] sc_u = (ctx', t'),
       nth_error (List.rev (smash_context [] ctx')) 1 = Some d &
       si_Σ ;;; [] ,,, skipn (#|smash_context [] sc_Γzw| - 1) (smash_context [] sc_Γzw)
         ⊢ decl_type (vass si_na (subst [sc_wb] 0 sc_x_to_x)) ⇝ decl_type d].
Proof.
  exact (red_it_mkProd_or_LetIn_smash_cb [] sc_Γzw fi_P sc_u 1
           (vass si_na (subst [sc_wb] 0 sc_x_to_x)) sc_red_let_prod eq_refl).
Qed.

Definition sc_dp : def term :=
  {| dname := si_na; dtype := it_mkProd_or_LetIn sc_Γb fi_P; dbody := fi_P; rarg := 0 |}.

(** Retyping [sc_dp] at [Π x:Prop. Prop] changes the definition. *)
Lemma red_has_rec_arg_cb_inst_nondeg : def_with_type sc_dp (tProd si_na fi_P fi_P) <> sc_dp.
Proof. discriminate. Qed.

(** [has_rec_arg] is a boolean on the type of the definition, so it computes on every concrete
    definition; the type here, [Π x:(λy:Prop. y) Prop. Prop], is replaced by [Π x:Prop. Prop],
    which changes the definition.
    INSTANCE NONDEGEN PCUICSREtaConvInstances.red_has_rec_arg_cb_inst_nondeg *)
Lemma red_has_rec_arg_cb_inst : has_rec_arg (def_with_type sc_dp (tProd si_na fi_P fi_P)).
Proof. exact (red_has_rec_arg_cb (d := sc_dp) sc_red_prod eq_refl). Qed.
