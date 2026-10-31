(* Distributed under the terms of the MIT license. *)

(* NONDEGEN tags: an INSTANCE NONDEGEN tag is a reader judgment backed by a compiled nontriviality
   lemma, not a mechanical guarantee.
   Measured reader miss rate: at least 19 of 60 instances sampled (seed 202610301905) from the 323 that an earlier focused review had not covered (31.7%, 95% upper bound 42.9%, one-sided Clopper-Pearson): 17 from the union of the verdicts held by two independent reviews (Opus 5: 10; Opus 5.5: 15, 6 of its verdicts borderline at confidence 0.5-0.6), plus two further rows that both reviews had passed and later root rulings reclassified under the same standard (S12, S36). 18 of the 19 sampled misses are corrected at this head (S36 is not yet), but the sample estimates the rate over ALL instance tags: a comparable share of the unsampled instances is expected to be wrong and is NOT corrected.
   P4 at this head: 313 lemmas with a base twin are accounted for: 229 demonstrated (at least one NONDEGEN instance; this count still includes 2 targets whose only NONDEGEN instance is already judged false and not yet corrected: PCUICClassificationEta.wf_fixpoint_spineE and wf_cofixpoint_spineE), 70 undemonstrable by their own statements (IMPOSSIBLE-only), and 14 with no working instance (NOT-BUILT-only): BDToPCUICEta.wf_rel_weakE; PCUICAlphaEta.eq_context_conversionE, isType_eq_context_conversionE, typing_alpha_propE, wf_local_alphaE; PCUICClassificationEta.typing_spine_nth_errorE, typing_spine_nth_error_NoneE, typing_spine_nth_error_None_prodE (non-degenerate instances of these 3 are built and under review, not yet landed); PCUICInversionEta.into_ws_cumulE; PCUICPrincipalityEta.typing_leq_termE; PCUICSREta.prim_app_typing_invE, sr_prim_opE, typing_spine_prim_arg_typesE, typing_spine_prim_argsE. The demonstrated count rests on NONDEGEN tags with the measured miss rate above. As of 2026-10-31T02:35Z, 11 NONDEGEN tags are judged false and not yet corrected, all conv → red cases whose input conversion was built from a reduction (for wf_fixpoint_spineE_inst the conv → red step sits inside its target's proof): 7 in BDFromPCUICEtaInstances (red_fix_witnessE_inst, mfix_body_on_conv_redE_fix_inst, red_cofix_witnessE_inst, mfix_body_on_conv_redE_cofix_inst, mfix_on_ind_conv_redE_cofix_inst, wf_fixpointE_wf_fixpoint_red_typed_inst, and sampled row S36 = wf_cofixpointE_wf_cofixpoint_red_inst) and PCUICPrincipalityEtaInstances.T8_Prod_l_plug_inst and T8_Prod_l_of_r_inst, whose targets are outside P4's input set, and PCUICClassificationEtaInstances.wf_fixpoint_spineE_inst and wf_cofixpoint_spineE_inst, whose targets are the 2 above. Context of the demonstrations (context = a judgment argument of type list (context_decl term), empty or not by computing its length, not the lemma's Γ parameter): 79 use a non-empty context; 23 have the context as their subject; 20 have a non-empty context that no term or type mentions; 4 undecided; 70 work only at the empty context (10 forced by the statement, 60 by the instance's choice; up to 89 under stricter readings); 33 have no context argument, which is not the same as the empty context. A mechanical sweep flagged at least 31 of the 338 NONDEGEN instances at 0bf9899a, before the later retags, whose conclusion is convertible to an input sub-derivation (3 of the 31 match the instance itself or its helper rather than an input); of its 9 non-equation flags, 9 were judged bad, with the kind-label correct in 6 of 9; it cannot see a cancellation inside the target lemma's own proof or a conclusion that is one part of a pair, and it does not discriminate the 22 closed equations. Prose overclaims were not mechanically enumerated, because that detector failed its controls. Later root rulings reclassified two sampled rows that both reviews had passed, S36 (the red → conv → red class) and S12 (its conclusion is the input's own cumulativity), raising the sampled rate from at least 17 to at least 19 of 60; the 45-row marker census stayed at 2 reopened. *)

(** * Satisfying instances for [Bidirectional/BDTypingEta]

  Each of the five judgments of [BDTypingEta] is inhabited by a concrete derivation whose own
  reduction or conversion premise is a real step, each context judgment by a context that is
  not empty, and each lemma of that file with a premise is applied to a concrete case with
  every premise proved, so the premises are shown to be jointly satisfiable. The environment is
  [si_Σ] ([PCUICCumulativitySpecEtaClosureInstances]: one
  inductive [I (A : Prop) : Prop] with one constructor [c : I A]). Each instance carries its
  tag of the instance degeneracy gate in the comment above it (for a NONDEGEN tag, the lemma
  that states why it is not degenerate; for an IMPOSSIBLE tag, why no instance of the target
  can be non-degenerate; and its target where the name does not give it); the declarations
  that are not instances are registered on the witness line after the imports.

  - the judgments ([The judgments, by a real step]): in [infering_sortE_inst] the type
    [inferE_Rel] gives [y] is not a sort ([bd_Γδ_not_sort]); in [infering_prodE_inst],
    [infering_induE_inst] and [checkingE_inst] the type [inferE_Rel] gives [x] is not the
    product, the application of [I] or the checked type that they reach ([bd_Γβπ_not_prod],
    [bd_Γβ_not_ind]); [inferingE_inst] infers an application whose argument check is
    [checkingE_eta_inst], on the pair of [bd_eta_pair_differ];
  - the size lemmas, tagged IMPOSSIBLE ([The size lemmas on the five judgments]):
    [inferingE_size_pos_inst], [infering_sortE_size_pos_inst], [infering_prodE_size_pos_inst],
    [infering_induE_size_pos_inst] and [checkingE_size_pos_inst] apply their lemmas to the
    five derivations above, but the conclusion [size d > 0] holds of every derivation, so no
    witness can make these rows non-degenerate; they stay as the rows of these lemmas;
  - the context judgments [wf_local_bdE_inst], [wf_local_bdE_eta_inst] and
    [wf_local_bd_relE_inst], on contexts that are not empty ([bd_ctxs_nonempty]);
  - [checkingE_eta_inst]: a check whose conversion premise is [JoinE_eta1_l] of the η step
    [bd_eta_step]: in the context
    [G : (Prop → Prop) → Prop, F : Prop → Prop, x : G (λ y : Prop. F y)], which is
    well formed for [wf_local_bdE] ([wf_local_bdE_eta_inst]), [x ◃ G F];
  - [inferingE_Case_inst]: a [match] derived by [inferE_Case], one of the two
    constructors whose comparison the E copy changed. The inductive [I] has one parameter;
    the scrutinee [c (G (λ y : Prop. F y))] has the parameter list [[bd_X]]
    ([bd_case_disc_ind]), the match's [pparams] is [[bd_GF]], and the parameter premise
    [bd_case_pars_join] compares the two, which differ ([bd_case_pars_differ]) and which one
    η step relates ([bd_case_eta_step]);
  - [bidir_ind_envE_closedn_inst]: the induction principle with predicates that are not
    [unit]: in any [Σ] with [wfE Σ], the subject of every E judgment is scoped by its
    context ([closedn]), every [lift_sorting1] judgment has its term and type scoped, every
    checked context is closed, and every checked extension is scoped by its base. Each of
    the eight predicates is false on some input ([bdc_nondegenerate]). Every case of the
    principle is proved in general. [inferingE_Case_inst_closedn] applies it to
    [inferingE_Case_inst];
  - the bridges to the checker's forecast form, [checkE_Cumul_ws_inst],
    [All2_ws_cumul_pbE_JoinE_inst] and [JoinE_ws_cumul_pbE_inst], tagged IMPOSSIBLE: each
    target only packs or unpacks its own premises ([checkE_Cumul] and the projection
    [ws_cumul_pbE_forget]; [All2_impl] of that projection; the record constructor
    [into_ws_cumul_pbE]), so every instance's conclusion is assembled from its premises. They
    run on the η pair of [checkingE_eta_inst] and stay as the rows of these lemmas;
  - the (co)fixpoint witness bridges, [wf_fixpoint_red_wf_fixpointE_inst],
    [wf_cofixpoint_red_wf_cofixpointE_inst], and [bd_mfix_on_ind_red_convE_inst] (copy 17's
    [PCUICFixWitnessEta.mfix_on_ind_red_convE], the typed form [BDTypingEta] stated until
    cross-lane commitment C4), at a declared type on which the check fails
    ([bd_mfix_check_fails], [bd_check_cofix_dtype]) and which reduces to a witness type
    ([bd_wf_fixpoint_red], [bd_wf_cofixpoint_red]). The cofixpoint uses [bd_coenv],
    [si_env] with the block declared [CoFinite]; [bd_cocb] gives its [ClosedBodies]. The
    typed form gets its [wfE si_env] from [si_wfE] and types the declared type over
    [typingE] ([bd_fix_dtype_isTypeE]). *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICEquality PCUICCases
     PCUICClosed PCUICClosedConv PCUICOnFreeVars PCUICTyping
     PCUICReduction PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICClosedBodies PCUICClosedTypEta
     PCUICTypingEta PCUICCumulativitySpecEtaClosureInstances PCUICEtaDefs PCUICEtaI5
     PCUICWellScopedCumulativity PCUICWellScopedCumulativityEta BDTyping BDTypingEta PCUICFixWitnessEta.
From Equations.Type Require Import Relation.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

(** The declarations that are not instances: the helpers, terms, contexts, derivations and
    non-degeneracy facts the instances are built from or name.
    WITNESSES: bd_* bdc_* wf_local_bdE_ΓFG inferingE_Case_inst_closedn bd_case_ctx_inst *)

(** ** Helpers in [si_Σ] *)

Lemma bd_vass (Γ : context) (na : aname) A s :
  si_Σ ;;; Γ |-E A ▹□ s -> isSortRel s na.(binder_relevance) ->
  lift_sorting (checkingE si_Σ Γ) (infering_sortE si_Σ Γ) (j_vass na A).
Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [exact I|exact r]. Qed.

Lemma bd_vass_s (Γ : context) (na : aname) A s :
  si_Σ ;;; Γ |-E A ▹□ s -> isSortRel s na.(binder_relevance) ->
  lift_sorting (checkingE si_Σ Γ) (infering_sortE si_Σ Γ) (j_vass_s na A s).
Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [reflexivity|exact r]. Qed.

Lemma bd_P_infer (Γ : context) : si_Σ ;;; Γ |-E si_P ▹ tSort (Sort.super sProp).
Proof. apply inferE_Sort. cbn; trivial. Qed.

Lemma bd_P_sort (Γ : context) : si_Σ ;;; Γ |-E si_P ▹□ Sort.super sProp.
Proof. eapply inferE_sort_Sort; [exact (bd_P_infer Γ)|apply rt_refl]. Qed.

(** [x ◃ P] for the last variable [x : P]. *)
Lemma bd_rel0_check (Γ : context) : si_Σ ;;; Γ ,, vass si_na si_P |-E tRel 0 ◃ si_P.
Proof. econstructor; [exact (inferE_Rel _ (Γ ,, vass si_na si_P) 0 (vass si_na si_P) eq_refl)|apply JoinE_refl]. Qed.

Definition bd_Γ1 : context := [vass si_na si_P].

(** [c ▹ Π A : Prop. I A], in any context. *)
Lemma bd_cstr_infer (Γ : context) :
  si_Σ ;;; Γ |-E tConstruct si_ind 0 [] ▹ tProd si_na si_P (tApp (tInd si_ind []) (tRel 0)).
Proof.
  refine (inferE_Construct _ _ si_ind 0 [] si_mdecl si_idecl si_cdecl si_declared_constructor _).
  reflexivity.
Qed.

Lemma bd_cstr_prod (Γ : context) :
  si_Σ ;;; Γ |-E tConstruct si_ind 0 [] ▹Π (si_na, si_P, tApp (tInd si_ind []) (tRel 0)).
Proof. econstructor; [exact (bd_cstr_infer Γ)|apply rt_refl]. Qed.

(** ** The context judgment on [[A : Prop]]

  [wf_local_bdE] is a notation for [All_local_env] over [lift_sorting1 checkingE
  infering_sortE]; its own premise, for an assumption, is the [▹□] judgment on the declared
  type, here [Prop ▹□ Type] ([bd_P_sort]). The context is not empty, so the [cons] rule runs. *)

(** INSTANCE NONDEGEN BDTypingEtaInstances.bd_ctxs_nonempty
    TARGET BDTypingEta.infering_sortE
    HELPER BDTypingEtaInstances.bd_P_sort *)
Lemma wf_local_bdE_inst : wf_local_bdE si_Σ bd_Γ1.
Proof.
  unfold bd_Γ1.
  apply localenv_cons_abs; [constructor|exact (bd_vass [] si_na si_P _ (bd_P_sort []) eq_refl)].
Qed.

(** ** A check by an η step

  [G : (Prop → Prop) → Prop, F : Prop → Prop, x : G (λ y : Prop. F y)] ⊢ [x ◃ G F]:
  [λ y : Prop. F y] is [eta_redex si_na si_P F] ([bd_lam_eta_redex]); it η-contracts to [F]. *)

Definition bd_s1 : sort := Sort.sort_of_product (Sort.super sProp) (Sort.super sProp).
Definition bd_FP : term := tProd si_na si_P si_P.
Definition bd_GP : term := tProd si_na bd_FP si_P.
(** In [[F; G]]: [λ y : Prop. F y] and [G (λ y : Prop. F y)]. *)
Definition bd_lam : term := tLambda si_na si_P (tApp (tRel 1) (tRel 0)).
Definition bd_X : term := tApp (tRel 1) bd_lam.
Definition bd_ΓFG : context := [vass si_na bd_FP; vass si_na bd_GP].
Definition bd_Γη : context := vass si_na bd_X :: bd_ΓFG.

Lemma bd_lam_eta_redex : bd_lam = eta_redex si_na si_P (tRel 0).
Proof. reflexivity. Qed.

(** [x]'s declared type in [bd_Γη] is [G (λ y : Prop. F y)], and lifted over [x] it is not
    [G F]: the pair is not syntactic equality. *)
Lemma bd_eta_pair_differ :
  nth_error bd_Γη 0 = Some (vass si_na bd_X) /\ lift0 1 bd_X <> tApp (tRel 2) (tRel 1).
Proof. split; [reflexivity|]. unfold bd_X, bd_lam. discriminate. Qed.

(** The contexts of the context instances are not empty: [bd_Γ1] and [bd_Γη] (of
    [wf_local_bdE_inst], [wf_local_bdE_eta_inst], [wf_local_bd_typingE_inst]) and the extension
    [[x : G (λ y : Prop. F y); F : Prop → Prop]] (of [wf_local_bd_relE_inst],
    [wf_local_bd_rel_typingE_inst]). The base [bd_ΓFG] (of [wf_rel_weakE_inst], tagged NOT-BUILT)
    and the one-declaration extension [[x : G (λ y : Prop. F y)]] are no longer used by an
    instance tagged with this lemma. *)
Lemma bd_ctxs_nonempty :
  bd_Γ1 <> [] /\ bd_Γη <> [] /\ bd_ΓFG <> [] /\ [vass si_na bd_X] <> [] /\
  [vass si_na bd_X; vass si_na bd_FP] <> [].
Proof. unfold bd_Γ1, bd_Γη, bd_ΓFG. repeat split; discriminate. Qed.

Lemma bd_FP_sort (Γ : context) : si_Σ ;;; Γ |-E bd_FP ▹□ bd_s1.
Proof.
  econstructor; [|apply rt_refl].
  unfold bd_FP, bd_s1. apply inferE_Prod.
  - exact (bd_vass_s Γ si_na si_P _ (bd_P_sort Γ) eq_refl).
  - exact (bd_P_sort _).
Qed.

Lemma bd_GP_sort (Γ : context) : si_Σ ;;; Γ |-E bd_GP ▹□ Sort.sort_of_product bd_s1 (Sort.super sProp).
Proof.
  econstructor; [|apply rt_refl].
  unfold bd_GP. apply inferE_Prod.
  - exact (bd_vass_s Γ si_na bd_FP _ (bd_FP_sort Γ) eq_refl).
  - exact (bd_P_sort _).
Qed.

Lemma bd_F_prod : si_Σ ;;; bd_ΓFG ,, vass si_na si_P |-E tRel 1 ▹Π (si_na, si_P, si_P).
Proof. econstructor; [exact (inferE_Rel _ (bd_ΓFG ,, vass si_na si_P) 1 (vass si_na bd_FP) eq_refl)|apply rt_refl]. Qed.

Lemma bd_lam_check : si_Σ ;;; bd_ΓFG |-E bd_lam ◃ bd_FP.
Proof.
  econstructor; [|apply JoinE_refl].
  unfold bd_lam. apply inferE_Lambda.
  - exact (bd_vass bd_ΓFG si_na si_P _ (bd_P_sort bd_ΓFG) eq_refl).
  - exact (inferE_App _ _ _ _ _ _ _ bd_F_prod (bd_rel0_check bd_ΓFG)).
Qed.

Lemma bd_G_prod : si_Σ ;;; bd_ΓFG |-E tRel 1 ▹Π (si_na, bd_FP, si_P).
Proof. econstructor; [exact (inferE_Rel _ bd_ΓFG 1 (vass si_na bd_GP) eq_refl)|apply rt_refl]. Qed.

Lemma bd_X_sort : si_Σ ;;; bd_ΓFG |-E bd_X ▹□ sProp.
Proof. eapply inferE_sort_Sort; [exact (inferE_App _ _ _ _ _ _ _ bd_G_prod bd_lam_check)|apply rt_refl]. Qed.

(** [bd_Γη] is well formed: [G (λ y : Prop. F y) ▹□ Prop] ([bd_X_sort]) over
    [F : Prop → Prop] and [G : (Prop → Prop) → Prop]; the judgment's target is the [▹□]
    judgment on each declared type (see [wf_local_bdE_inst]).
    INSTANCE NONDEGEN BDTypingEtaInstances.bd_ctxs_nonempty
    TARGET BDTypingEta.infering_sortE
    HELPER BDTypingEtaInstances.bd_X_sort *)
Lemma wf_local_bdE_eta_inst : wf_local_bdE si_Σ bd_Γη.
Proof.
  unfold bd_Γη, bd_ΓFG.
  apply localenv_cons_abs; [|exact (bd_vass _ si_na bd_X _ bd_X_sort eq_refl)].
  apply localenv_cons_abs; [|exact (bd_vass _ si_na bd_FP _ (bd_FP_sort _) eq_refl)].
  apply localenv_cons_abs; [constructor|exact (bd_vass _ si_na bd_GP _ (bd_GP_sort _) eq_refl)].
Qed.

(** [[x : G (λ y : Prop. F y); F : Prop → Prop]] over [[G : (Prop → Prop) → Prop]].
    INSTANCE NONDEGEN BDTypingEtaInstances.bd_ctxs_nonempty
    TARGET BDTypingEta.infering_sortE
    HELPER BDTypingEtaInstances.bd_X_sort *)
Lemma wf_local_bd_relE_inst : wf_local_bd_relE si_Σ [vass si_na bd_GP] [vass si_na bd_X; vass si_na bd_FP].
Proof.
  unfold All_local_rel.
  apply localenv_cons_abs; [|exact (bd_vass _ si_na bd_X _ bd_X_sort eq_refl)].
  apply localenv_cons_abs; [constructor|exact (bd_vass _ si_na bd_FP _ (bd_FP_sort _) eq_refl)].
Qed.

(** The η step: [G (λ y : Prop. F y)] contracts to [G F], in [bd_Γη]. *)
Definition bd_eta_step : eta1 (tApp (tRel 2) (eta_redex si_na si_P (tRel 1))) (tApp (tRel 2) (tRel 1)) :=
  app_eta_r _ _ (tRel 2) (eta_red si_na (tRel 1) si_P).

(** [x ◃ G F]: the conversion premise is the η step [bd_eta_step], between two types that
    are not syntactically equal ([bd_eta_pair_differ]).
    INSTANCE NONDEGEN BDTypingEtaInstances.bd_eta_pair_differ
    TARGET BDTypingEta.checkingE *)
Lemma checkingE_eta_inst : si_Σ ;;; bd_Γη |-E tRel 0 ◃ tApp (tRel 2) (tRel 1).
Proof.
  eapply checkE_Cumul; [exact (inferE_Rel _ bd_Γη 0 (vass si_na bd_X) eq_refl)|].
  apply JoinE_eta1_l. exact bd_eta_step.
Qed.

(** ** The bridges to the forecast form, on the η pair *)

(** [checkE_Cumul_ws] on the inference of [x] in [bd_Γη] and the η cumulativity to [G F].
    INSTANCE IMPOSSIBLE: the target's proof is the checkE_Cumul constructor on its inference premise and on ws_cumul_pbE_forget (a projection of the ws_cumul_pbE record) of its cumulativity premise, so every instance's conclusion only repacks its own premises and no witness can make it non-degenerate *)
Lemma checkE_Cumul_ws_inst : si_Σ ;;; bd_Γη |-E tRel 0 ◃ tApp (tRel 2) (tRel 1).
Proof.
  eapply checkE_Cumul_ws; [exact (inferE_Rel _ bd_Γη 0 (vass si_na bd_X) eq_refl)|].
  apply (eta1_ws_cumul_pbE (Σ := si_Σ)); [reflexivity|reflexivity|exact bd_eta_step].
Qed.

(** [All2_ws_cumul_pbE_JoinE] on the one-entry list of the η pair in [bd_Γη].
    INSTANCE IMPOSSIBLE: the target's proof is All2_impl of ws_cumul_pbE_forget (a projection of the ws_cumul_pbE record) on its premise, so every instance's conclusion is its premise with each entry projected and no witness can make it non-degenerate *)
Lemma All2_ws_cumul_pbE_JoinE_inst :
  All2 (JoinE si_Σ bd_Γη Conv) [lift0 1 bd_X] [tApp (tRel 2) (tRel 1)].
Proof.
  apply (All2_ws_cumul_pbE_JoinE (Γ := bd_Γη)). constructor; [|constructor].
  apply (eta1_ws_cumul_pbE (Σ := si_Σ)); [reflexivity|reflexivity|exact bd_eta_step].
Qed.

(** [JoinE_ws_cumul_pbE] on the η pair in [bd_Γη].
    INSTANCE IMPOSSIBLE: the target's proof is into_ws_cumul_pbE, the ws_cumul_pbE record constructor applied to its four premises (the closed context, the two scoping facts and the JoinE), so every instance's conclusion only packs its own premises and no witness can make it non-degenerate *)
Lemma JoinE_ws_cumul_pbE_inst :
  ws_cumul_pbE Cumul si_Σ bd_Γη (lift0 1 bd_X) (tApp (tRel 2) (tRel 1)).
Proof.
  apply (JoinE_ws_cumul_pbE (Γ := bd_Γη)); [reflexivity|reflexivity|reflexivity|].
  apply JoinE_eta1_l. exact bd_eta_step.
Qed.

(** ** The (co)fixpoint witness bridges

  The declared type has the domain (fixpoint) or is (cofixpoint) the β-redex
  [(λ B : Prop. I B) A], in [bd_Γ1 = [A : Prop]]; the witness is its reduct [I A].
  The check does not pass on the declared type itself ([bd_check_fix_dtype],
  [bd_check_cofix_dtype]). *)

Definition bd_fix_dom : term := tApp (tLambda si_na si_P (tApp (tInd si_ind []) (tRel 0))) (tRel 0).
Definition bd_fix_dtype : term := tProd si_na bd_fix_dom si_P.
Definition bd_fix_ty : term := tProd si_na (tApp (tInd si_ind []) (tRel 0)) si_P.
Definition bd_fix_d : def term :=
  {| dname := si_na; dtype := bd_fix_dtype; dbody := tLambda si_na bd_fix_dom (tRel 0); rarg := 0 |}.
Definition bd_mfix : mfixpoint term := [bd_fix_d].

Lemma bd_check_fix_dtype : check_one_fix bd_fix_d = None.
Proof. reflexivity. Qed.

(** The check fails on the one declared type of [bd_mfix] ([bd_check_fix_dtype]). *)
Lemma bd_mfix_check_fails : map check_one_fix bd_mfix = [None].
Proof. reflexivity. Qed.

Lemma bd_fix_dtype_red : red si_Σ bd_Γ1 bd_fix_dtype bd_fix_ty.
Proof.
  change (red si_Σ bd_Γ1
            (tProd si_na (tApp (tLambda si_na si_P (tApp (tInd si_ind []) (tRel 0))) (tRel 0)) si_P)
            (tProd si_na ((tApp (tInd si_ind []) (tRel 0)) {0 := tRel 0}) si_P)).
  apply rt_step. apply prod_red_l. apply red_beta.
Qed.

Lemma bd_wf_fixpoint_red : wf_fixpoint_red si_Σ bd_Γ1 bd_mfix.
Proof.
  split; [reflexivity|split; [reflexivity|]].
  exists si_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [|constructor].
  exists bd_fix_ty. split; [reflexivity|exact bd_fix_dtype_red].
Qed.

(** [check_one_fix] fails on the declared type of the one definition of [bd_mfix]
    ([bd_mfix_check_fails]); that declared type reduces to [bd_fix_ty] ([bd_fix_dtype_red]).
    INSTANCE NONDEGEN BDTypingEtaInstances.bd_mfix_check_fails *)
Lemma wf_fixpoint_red_wf_fixpointE_inst : wf_fixpointE si_Σ bd_Γ1 bd_mfix.
Proof.
  refine (@wf_fixpoint_red_wf_fixpointE _ si_Σ si_cb bd_Γ1 bd_mfix _ _ bd_wf_fixpoint_red).
  - reflexivity.
  - constructor; [reflexivity|constructor].
Qed.

(** [si_env] with the block declared coinductive. *)
Definition bd_comdecl : mutual_inductive_body :=
  {| ind_finite := CoFinite; ind_npars := 1; ind_params := si_params; ind_bodies := [si_idecl];
     ind_universes := Monomorphic_ctx; ind_variance := None |}.

Definition bd_coenv : global_env :=
  {| universes := ContextSet.empty; declarations := [(si_kn, InductiveDecl bd_comdecl)];
     retroknowledge := Retroknowledge.empty |}.

Definition bd_coΣ : global_env_ext := (bd_coenv, Monomorphic_ctx).

(** [bd_coenv] declares no constant, and one name. *)
Lemma bd_cocb : ClosedBodies bd_coenv.
Proof.
  apply Build_ClosedBodies.
  - intros cst decl body [h|[]] _. discriminate h.
  - cbn. constructor; [intros []|constructor].
Qed.

Definition bd_cofix_d : def term :=
  {| dname := si_na; dtype := bd_fix_dom; dbody := tRel 0; rarg := 0 |}.

Lemma bd_check_cofix_dtype : check_one_cofix bd_cofix_d = None.
Proof. reflexivity. Qed.

Lemma bd_wf_cofixpoint_red : wf_cofixpoint_red bd_coΣ bd_Γ1 [bd_cofix_d].
Proof.
  exists si_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [|constructor].
  exists (tApp (tInd si_ind []) (tRel 0)). split; [reflexivity|].
  change (red bd_coΣ bd_Γ1 (tApp (tLambda si_na si_P (tApp (tInd si_ind []) (tRel 0))) (tRel 0))
            ((tApp (tInd si_ind []) (tRel 0)) {0 := tRel 0})).
  apply rt_step. apply red_beta.
Qed.

(** [check_one_cofix] fails on the declared type [(λ B : Prop. I B) A] of [bd_cofix_d]
    ([bd_check_cofix_dtype]).
    INSTANCE NONDEGEN BDTypingEtaInstances.bd_check_cofix_dtype *)
Lemma wf_cofixpoint_red_wf_cofixpointE_inst : wf_cofixpointE bd_coΣ bd_Γ1 [bd_cofix_d].
Proof.
  refine (@wf_cofixpoint_red_wf_cofixpointE _ bd_coΣ bd_cocb bd_Γ1 [bd_cofix_d] _ _ bd_wf_cofixpoint_red).
  - reflexivity.
  - constructor; [reflexivity|constructor].
Qed.

(** *** The typed form: [wfE si_env], [wf_localE si_Σ bd_Γ1], and the declared type
    typed as a type over [typingE] *)

Lemma bd_P_typedE (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E si_P : tSort (Sort.super sProp).
Proof. intros h. apply typeE_Sort; [exact h|cbn; trivial]. Qed.

Lemma bd_wfE_P (Γ : context) : wf_localE si_Σ Γ -> wf_localE si_Σ (Γ ,, vass si_na si_P).
Proof.
  intros h. apply localenv_cons_abs; [exact h|].
  split; [exact tt|]. exists (Sort.super sProp). split; [exact (bd_P_typedE Γ h)|]. split; [exact I|reflexivity].
Qed.

Lemma bd_wfE_Γ1 : wf_localE si_Σ bd_Γ1.
Proof. apply (bd_wfE_P []). constructor. Qed.

Lemma bd_arity_typedE (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ |-E si_arity : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)).
Proof.
  intros h. apply typeE_Prod.
  - split; [exact tt|]. exists (Sort.super sProp). split; [exact (bd_P_typedE Γ h)|]. split; reflexivity.
  - apply typeE_Sort; [exact (bd_wfE_P Γ h)|cbn; trivial].
Qed.

Lemma bd_ind_typedE (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E tInd si_ind [] : si_arity.
Proof.
  intros h. refine (typeE_Ind _ _ si_ind [] si_mdecl si_idecl h si_declared_inductive _).
  reflexivity.
Qed.

(** [I B : Prop] for the last variable [B : Prop]. *)
Lemma bd_Ix0_typedE (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ ,, vass si_na si_P |-E tApp (tInd si_ind []) (tRel 0) : tSort sProp.
Proof.
  intros h. have w := bd_wfE_P Γ h.
  exact (typeE_App _ _ (tInd si_ind []) si_na si_P (tSort sProp) _ (tRel 0)
           (bd_arity_typedE _ w) (bd_ind_typedE _ w) (typeE_Rel _ _ 0 (vass si_na si_P) w eq_refl)).
Qed.

(** [(λ B : Prop. I B) A : Prop] in [bd_Γ1]. *)
Lemma bd_fix_dom_typedE : si_Σ ;;; bd_Γ1 |-E bd_fix_dom : tSort sProp.
Proof.
  have w := bd_wfE_Γ1.
  refine (typeE_App _ _ (tLambda si_na si_P (tApp (tInd si_ind []) (tRel 0))) si_na si_P (tSort sProp) _
            (tRel 0) (bd_arity_typedE _ w) _ (typeE_Rel _ _ 0 (vass si_na si_P) w eq_refl)).
  apply typeE_Lambda.
  - split; [exact tt|]. exists (Sort.super sProp). split; [exact (bd_P_typedE _ w)|]. split; [exact I|reflexivity].
  - exact (bd_Ix0_typedE _ w).
Qed.

Lemma bd_fix_dtype_isTypeE : on_type (lift_typing typingE) si_Σ bd_Γ1 bd_fix_dtype.
Proof.
  have hdom : lift_typing typingE si_Σ bd_Γ1 (j_vass si_na bd_fix_dom).
  { split; [exact tt|]. exists sProp. split; [exact bd_fix_dom_typedE|]. split; [exact I|reflexivity]. }
  split; [exact tt|]. exists (Sort.sort_of_product sProp (Sort.super sProp)). split; [|split; exact I].
  apply typeE_Prod.
  - split; [exact tt|]. exists sProp. split; [exact bd_fix_dom_typedE|]. split; reflexivity.
  - apply typeE_Sort; [|cbn; trivial].
    exact (localenv_cons_abs bd_wfE_Γ1 hdom).
Qed.

(** [bd_] keeps this name apart from copy 17's own [mfix_on_ind_red_convE_inst]
    ([PCUICTypingEtaCopy17Instances], at [c17_d]). [check_one_fix] fails on the declared type
    of the one definition of [bd_mfix] ([bd_mfix_check_fails]); that declared type reduces to
    [bd_fix_ty] ([bd_fix_dtype_red]).
    INSTANCE NONDEGEN BDTypingEtaInstances.bd_mfix_check_fails
    TARGET PCUICFixWitnessEta.mfix_on_ind_red_convE *)
Lemma bd_mfix_on_ind_red_convE_inst :
  mfix_on_ind check_one_fix (conv_witnessE si_Σ bd_Γ1)
    (fun mind => check_recursivity_kind (lookup_env si_Σ) mind Finite) bd_mfix.
Proof.
  refine (@mfix_on_ind_red_convE _ si_Σ si_wfE check_one_fix _ bd_Γ1 bd_mfix bd_wfE_Γ1 _ _).
  - constructor; [exact bd_fix_dtype_isTypeE|constructor].
  - exact (snd (snd bd_wf_fixpoint_red)).
Qed.

(** ** The judgments, by a real step

  Each judgment is derived where its own premise is a real step, not the identity: [▹□] by
  the δ-step of a let, [▹Π] and [▹{}] by a β step on the declared type of a variable, [◃] by
  that β step, and [▹] for an application whose argument is checked by the η step of
  [checkingE_eta_inst]. The β-redex is [bd_fix_dom = (λ B : Prop. I B) A] of the fixpoint
  section, over [bd_Γ1 = [A : Prop]]. *)

(** [y : d, d := Prop : Type]. *)
Definition bd_Γδ : context := [vass si_na (tRel 0); vdef si_na si_P (tSort (Sort.super sProp))].

(** The type [inferE_Rel] gives [y] in [bd_Γδ] (the declared type of [y], lifted over [y]) is
    not a sort. *)
Lemma bd_Γδ_not_sort : forall d u, nth_error bd_Γδ 0 = Some d -> lift0 1 (decl_type d) <> tSort u.
Proof. intros d u h. injection h as <-. discriminate. Qed.

(** [y ▹□ Prop] in [bd_Γδ]. The type [inferE_Rel] gives [y] is not a sort ([bd_Γδ_not_sort]).
    INSTANCE NONDEGEN BDTypingEtaInstances.bd_Γδ_not_sort *)
Lemma infering_sortE_inst : si_Σ ;;; bd_Γδ |-E tRel 0 ▹□ sProp.
Proof.
  refine (inferE_sort_Sort _ bd_Γδ (tRel 0) (tRel 1) sProp
            (inferE_Rel _ bd_Γδ 0 (vass si_na (tRel 0)) eq_refl) _).
  apply rt_step. exact (red_rel si_Σ bd_Γδ 1 si_P eq_refl).
Qed.

(** [x : Π _ : (λ B : Prop. I B) A. Prop] over [A : Prop]. *)
Definition bd_Γβπ : context := bd_Γ1 ,, vass si_na bd_fix_dtype.

(** The type [inferE_Rel] gives [x] in [bd_Γβπ] (the declared type of [x], lifted over [x],
    whose domain is the β-redex [(λ B : Prop. I B) A]) is not the product [Π _ : I A. Prop]. *)
Lemma bd_Γβπ_not_prod : forall d, nth_error bd_Γβπ 0 = Some d ->
  lift0 1 (decl_type d) <> tProd si_na (tApp (tInd si_ind []) (tRel 1)) si_P.
Proof. intros d h. injection h as <-. discriminate. Qed.

(** [x ▹Π (_ : I A, Prop)] in [bd_Γβπ]. The type [inferE_Rel] gives [x] is not
    [Π _ : I A. Prop] ([bd_Γβπ_not_prod]).
    INSTANCE NONDEGEN BDTypingEtaInstances.bd_Γβπ_not_prod *)
Lemma infering_prodE_inst :
  si_Σ ;;; bd_Γβπ |-E tRel 0 ▹Π (si_na, tApp (tInd si_ind []) (tRel 1), si_P).
Proof.
  refine (inferE_prod_Prod _ bd_Γβπ (tRel 0) (lift0 1 bd_fix_dtype) si_na
            (tApp (tInd si_ind []) (tRel 1)) si_P
            (inferE_Rel _ bd_Γβπ 0 (vass si_na bd_fix_dtype) eq_refl) _).
  change (red si_Σ bd_Γβπ
            (tProd si_na (tApp (tLambda si_na si_P (tApp (tInd si_ind []) (tRel 0))) (tRel 1)) si_P)
            (tProd si_na ((tApp (tInd si_ind []) (tRel 0)) {0 := tRel 1}) si_P)).
  apply rt_step. apply prod_red_l. apply red_beta.
Qed.

(** [x : (λ B : Prop. I B) A] over [A : Prop]. *)
Definition bd_Γβ : context := bd_Γ1 ,, vass si_na bd_fix_dom.

(** The type [inferE_Rel] gives [x] in [bd_Γβ] (the declared type of [x], lifted over [x]: the
    β-redex [(λ B : Prop. I B) A]) is not [I A]. *)
Lemma bd_Γβ_not_ind : forall d, nth_error bd_Γβ 0 = Some d ->
  lift0 1 (decl_type d) <> tApp (tInd si_ind []) (tRel 1).
Proof. intros d h. injection h as <-. discriminate. Qed.

Lemma bd_Γβ_red : red si_Σ bd_Γβ (lift0 1 bd_fix_dom) (tApp (tInd si_ind []) (tRel 1)).
Proof.
  change (red si_Σ bd_Γβ (tApp (tLambda si_na si_P (tApp (tInd si_ind []) (tRel 0))) (tRel 1))
            ((tApp (tInd si_ind []) (tRel 0)) {0 := tRel 1})).
  apply rt_step. apply red_beta.
Qed.

(** [x ▹{I} ([], [A])] in [bd_Γβ]. The type [inferE_Rel] gives [x] is not [I A]
    ([bd_Γβ_not_ind]).
    INSTANCE NONDEGEN BDTypingEtaInstances.bd_Γβ_not_ind *)
Lemma infering_induE_inst : si_Σ ;;; bd_Γβ |-E tRel 0 ▹{si_ind} ([], [tRel 1]).
Proof.
  exact (inferE_ind_Ind _ bd_Γβ si_ind (tRel 0) (lift0 1 bd_fix_dom) [] [tRel 1]
           (inferE_Rel _ bd_Γβ 0 (vass si_na bd_fix_dom) eq_refl) bd_Γβ_red).
Qed.

(** [x ◃ I A] in [bd_Γβ]. The type [inferE_Rel] gives [x] is not the checked type [I A]
    ([bd_Γβ_not_ind]).
    INSTANCE NONDEGEN BDTypingEtaInstances.bd_Γβ_not_ind *)
Lemma checkingE_inst : si_Σ ;;; bd_Γβ |-E tRel 0 ◃ tApp (tInd si_ind []) (tRel 1).
Proof.
  exact (checkE_Cumul _ bd_Γβ (tRel 0) (lift0 1 bd_fix_dom) (tApp (tInd si_ind []) (tRel 1))
           (inferE_Rel _ bd_Γβ 0 (vass si_na bd_fix_dom) eq_refl)
           (JoinE_red_l si_Σ bd_Γβ Cumul _ _ bd_Γβ_red)).
Qed.

(** In [bd_Γη]: [G ▹Π (_ : Prop → Prop, Prop)], [F ◃ Prop → Prop], [G F ▹□ Prop], and
    [λ z : G F. z ▹Π (_ : G F, G F)]. *)
Lemma bd_Gη_prod : si_Σ ;;; bd_Γη |-E tRel 2 ▹Π (si_na, bd_FP, si_P).
Proof. econstructor; [exact (inferE_Rel _ bd_Γη 2 (vass si_na bd_GP) eq_refl)|apply rt_refl]. Qed.

Lemma bd_Fη_check : si_Σ ;;; bd_Γη |-E tRel 1 ◃ bd_FP.
Proof. econstructor; [exact (inferE_Rel _ bd_Γη 1 (vass si_na bd_FP) eq_refl)|apply JoinE_refl]. Qed.

Lemma bd_GFη_sort : si_Σ ;;; bd_Γη |-E tApp (tRel 2) (tRel 1) ▹□ sProp.
Proof. econstructor; [exact (inferE_App _ _ _ _ _ _ _ bd_Gη_prod bd_Fη_check)|apply rt_refl]. Qed.

Lemma bd_idGFη_prod :
  si_Σ ;;; bd_Γη |-E tLambda si_na (tApp (tRel 2) (tRel 1)) (tRel 0)
    ▹Π (si_na, tApp (tRel 2) (tRel 1), lift0 1 (tApp (tRel 2) (tRel 1))).
Proof.
  econstructor; [|apply rt_refl].
  apply inferE_Lambda.
  - exact (bd_vass bd_Γη si_na _ _ bd_GFη_sort eq_refl).
  - exact (inferE_Rel _ (bd_Γη ,, vass si_na (tApp (tRel 2) (tRel 1))) 0
             (vass si_na (tApp (tRel 2) (tRel 1))) eq_refl).
Qed.

(** [(λ z : G F. z) x ▹ G F] in [bd_Γη]: the argument [x] is checked against [G F] by the η
    step of [checkingE_eta_inst], between types that are not syntactically equal
    ([bd_eta_pair_differ]).
    INSTANCE NONDEGEN BDTypingEtaInstances.bd_eta_pair_differ *)
Definition inferingE_inst :
  si_Σ ;;; bd_Γη |-E tApp (tLambda si_na (tApp (tRel 2) (tRel 1)) (tRel 0)) (tRel 0)
    ▹ tApp (tRel 2) (tRel 1) :=
  inferE_App si_Σ bd_Γη _ _ _ _ _ bd_idGFη_prod checkingE_eta_inst.

(** ** The size lemmas on the five judgments

  [inferingE_size_pos], [infering_sortE_size_pos], [infering_prodE_size_pos],
  [infering_induE_size_pos] and [checkingE_size_pos] ([BDTypingEta]) conclude [size d > 0],
  which holds of every derivation [d] ([destruct d; cbn; lia]: every rule adds one to the
  size). So no instance of them can be non-degenerate. Each instance below applies its lemma
  to one derivation above ([inferingE_inst], [infering_sortE_inst], [infering_prodE_inst],
  [infering_induE_inst], [checkingE_inst]) and is tagged IMPOSSIBLE. *)

(** The size lemma on [inferingE_inst].
    INSTANCE IMPOSSIBLE: the target's conclusion inferingE_size d > 0 holds of every derivation d (BDTypingEta proves it by destruct d; cbn; lia, every rule adds one to the size), so every instance concludes a fact true of all derivations and no witness can make it non-degenerate *)
Lemma inferingE_size_pos_inst : inferingE_size inferingE_inst > 0.
Proof. exact (inferingE_size_pos inferingE_inst). Qed.

(** The size lemma on [infering_sortE_inst] ([y ▹□ Prop] in [bd_Γδ]).
    INSTANCE IMPOSSIBLE: the target's conclusion infering_sortE_size d > 0 holds of every derivation d (BDTypingEta proves it by destruct d; cbn; lia, every rule adds one to the size), so every instance concludes a fact true of all derivations and no witness can make it non-degenerate *)
Lemma infering_sortE_size_pos_inst : infering_sortE_size infering_sortE_inst > 0.
Proof. exact (infering_sortE_size_pos (Σ := si_Σ) (Γ := bd_Γδ) infering_sortE_inst). Qed.

(** The size lemma on [infering_prodE_inst] ([x ▹Π (_ : I A, Prop)] in [bd_Γβπ]).
    INSTANCE IMPOSSIBLE: the target's conclusion infering_prodE_size d > 0 holds of every derivation d (BDTypingEta proves it by destruct d; cbn; lia, every rule adds one to the size), so every instance concludes a fact true of all derivations and no witness can make it non-degenerate *)
Lemma infering_prodE_size_pos_inst : infering_prodE_size infering_prodE_inst > 0.
Proof. exact (infering_prodE_size_pos (Σ := si_Σ) (Γ := bd_Γβπ) infering_prodE_inst). Qed.

(** The size lemma on [infering_induE_inst] ([x ▹{I} ([], [A])] in [bd_Γβ]).
    INSTANCE IMPOSSIBLE: the target's conclusion infering_induE_size d > 0 holds of every derivation d (BDTypingEta proves it by destruct d; cbn; lia, every rule adds one to the size), so every instance concludes a fact true of all derivations and no witness can make it non-degenerate *)
Lemma infering_induE_size_pos_inst : infering_induE_size infering_induE_inst > 0.
Proof. exact (infering_induE_size_pos (Σ := si_Σ) (Γ := bd_Γβ) infering_induE_inst). Qed.

(** The size lemma on [checkingE_inst] ([x ◃ I A] in [bd_Γβ]).
    INSTANCE IMPOSSIBLE: the target's conclusion checkingE_size d > 0 holds of every derivation d (BDTypingEta proves it by destruct d; cbn; lia, every rule adds one to the size), so every instance concludes a fact true of all derivations and no witness can make it non-degenerate *)
Lemma checkingE_size_pos_inst : checkingE_size checkingE_inst > 0.
Proof. exact (checkingE_size_pos (Σ := si_Σ) (Γ := bd_Γβ) checkingE_inst). Qed.

(** ** A [match] whose parameter comparison is an η step ([inferE_Case])

  [inferE_Case] is one of the two constructors whose comparison the E copy changed: it
  compares the scrutinee's parameters with the match's [pparams] by
  [All2 (JoinE Σ Γ Conv)]. In [bd_ΓFG = [F : Prop → Prop; G : (Prop → Prop) → Prop]],
  the term is
  [match c (G (λ y : Prop. F y)) as z in I (G F) return Prop with c => G F end].
  The inductive [I (A : Prop) : Prop] of [si_Σ] has one parameter. The scrutinee
  [c (G (λ y : Prop. F y))] has the type [I (G (λ y : Prop. F y))], so its parameter
  list is [[bd_X]]; the match's [pparams] is [[bd_GF]] = [[G F]]. The two parameters
  differ ([bd_case_pars_differ]); the premise holds by the η step
  [λ y : Prop. F y ⇝η F] under [G] ([bd_case_eta_step], [bd_case_pars_join]). The
  single branch returns [G F : Prop] at the branch type [(λ z : I (G F). Prop) (c (G F))],
  which a β step relates to [Prop] ([bd_case_br_check]). The global environment is
  [si_env], well formed ([si_wf]) and well formed for the η typing ([si_wfE]); the local
  context [bd_ΓFG] is well formed for the E judgments ([wf_local_bdE_ΓFG]). *)

Definition bd_GF : term := tApp (tRel 1) (tRel 0).
Definition bd_IGF : term := tApp (tInd si_ind []) bd_GF.
Definition bd_zna : aname := {| binder_name := nNamed (ind_name si_idecl); binder_relevance := Relevant |}.
Definition bd_case_ci : case_info := {| ci_ind := si_ind; ci_npar := 1; ci_relevance := Relevant |}.
Definition bd_case_p : predicate term :=
  {| pparams := [bd_GF]; puinst := []; pcontext := ind_predicate_context si_ind si_mdecl si_idecl;
     preturn := si_P |}.
Definition bd_case_disc : term := tApp (tConstruct si_ind 0 []) bd_X.
Definition bd_case_br : branch term := {| bcontext := []; bbody := bd_GF |}.
Definition bd_case : term := tCase bd_case_ci bd_case_p bd_case_disc [bd_case_br].
(** The return-type abstraction [λ z : I (G F). Prop] and the constructor [c (G F)]. *)
Definition bd_case_ptm : term := tLambda bd_zna bd_IGF si_P.
Definition bd_case_cstr : term := tApp (tConstruct si_ind 0 []) bd_GF.

Lemma wf_local_bdE_ΓFG : wf_local_bdE si_Σ bd_ΓFG.
Proof.
  unfold bd_ΓFG.
  apply localenv_cons_abs; [|exact (bd_vass _ si_na bd_FP _ (bd_FP_sort _) eq_refl)].
  apply localenv_cons_abs; [constructor|exact (bd_vass _ si_na bd_GP _ (bd_GP_sort _) eq_refl)].
Qed.

(** The predicate context the match computes is [[z : I (G F)]]. *)
Lemma bd_case_predctx :
  case_predicate_context si_ind si_mdecl si_idecl bd_case_p = [vass bd_zna bd_IGF].
Proof. reflexivity. Qed.

(** [F ◃ Prop → Prop], [G F ▹ Prop], [G F ◃ Prop], [G (λ y : Prop. F y) ◃ Prop]. *)
Lemma bd_F_check : si_Σ ;;; bd_ΓFG |-E tRel 0 ◃ bd_FP.
Proof. econstructor; [exact (inferE_Rel _ bd_ΓFG 0 (vass si_na bd_FP) eq_refl)|apply JoinE_refl]. Qed.

Lemma bd_GF_infer : si_Σ ;;; bd_ΓFG |-E bd_GF ▹ si_P.
Proof. exact (inferE_App _ _ _ _ _ _ _ bd_G_prod bd_F_check). Qed.

Lemma bd_GF_check : si_Σ ;;; bd_ΓFG |-E bd_GF ◃ si_P.
Proof. econstructor; [exact bd_GF_infer|apply JoinE_refl]. Qed.

Lemma bd_X_check : si_Σ ;;; bd_ΓFG |-E bd_X ◃ si_P.
Proof. econstructor; [exact (inferE_App _ _ _ _ _ _ _ bd_G_prod bd_lam_check)|apply JoinE_refl]. Qed.

(** [I ▹ Π A : Prop. Prop], [I (G F) ▹□ Prop]. *)
Lemma bd_ind_infer (Γ : context) : si_Σ ;;; Γ |-E tInd si_ind [] ▹ si_arity.
Proof. refine (inferE_Ind _ _ si_ind [] si_mdecl si_idecl si_declared_inductive _). reflexivity. Qed.

Lemma bd_ind_prod (Γ : context) : si_Σ ;;; Γ |-E tInd si_ind [] ▹Π (si_na, si_P, tSort sProp).
Proof. econstructor; [exact (bd_ind_infer Γ)|apply rt_refl]. Qed.

Lemma bd_IGF_sort : si_Σ ;;; bd_ΓFG |-E bd_IGF ▹□ sProp.
Proof. econstructor; [exact (inferE_App _ _ _ _ _ _ _ (bd_ind_prod bd_ΓFG) bd_GF_check)|apply rt_refl]. Qed.

(** The scrutinee [c (G (λ y : Prop. F y))] is in [I] with the parameter list [[bd_X]]. *)
Lemma bd_case_disc_infer : si_Σ ;;; bd_ΓFG |-E bd_case_disc ▹ tApp (tInd si_ind []) bd_X.
Proof. exact (inferE_App _ _ _ _ _ _ _ (bd_cstr_prod bd_ΓFG) bd_X_check). Qed.

Lemma bd_case_disc_ind : si_Σ ;;; bd_ΓFG |-E bd_case_disc ▹{si_ind} ([], [bd_X]).
Proof. econstructor; [exact bd_case_disc_infer|apply rt_refl]. Qed.

(** The parameter comparison. The two parameters are not syntactically equal; the η step
    [bd_case_eta_step] below relates [bd_X] to [bd_GF]. *)
Lemma bd_case_pars_differ : bd_X <> bd_GF.
Proof. unfold bd_X, bd_GF, bd_lam. discriminate. Qed.

Definition bd_case_eta_step : eta1 bd_X bd_GF :=
  app_eta_r _ _ (tRel 1) (eta_red si_na (tRel 0) si_P).

Lemma bd_case_pars_join : All2 (JoinE si_Σ bd_ΓFG Conv) [bd_X] [bd_GF].
Proof. constructor; [|constructor]. apply JoinE_eta1_l. exact bd_case_eta_step. Qed.

(** The side conditions. *)
Lemma bd_case_wf_pred : wf_predicate si_mdecl si_idecl bd_case_p.
Proof. split; [reflexivity|]. constructor; [reflexivity|constructor]. Qed.

Lemma bd_case_cons : consistent_instance_ext si_Σ (ind_universes si_mdecl) [].
Proof. reflexivity. Qed.

Lemma bd_case_predctx_wf : wf_local_bd_relE si_Σ bd_ΓFG [vass bd_zna bd_IGF].
Proof.
  unfold All_local_rel.
  apply localenv_cons_abs; [constructor|exact (bd_vass _ bd_zna bd_IGF _ bd_IGF_sort eq_refl)].
Qed.

Lemma bd_case_elim : is_allowed_elimination si_Σ (ind_kelim si_idecl) (Sort.super sProp).
Proof. exact eq_refl. Qed.

Lemma bd_case_rel : isSortRel (Sort.super sProp) (ci_relevance bd_case_ci).
Proof. exact eq_refl. Qed.

Lemma bd_case_ctx_inst : ctx_inst (checkingE si_Σ) bd_ΓFG [bd_GF] [vass si_na si_P].
Proof. econstructor; [exact bd_GF_check|constructor]. Qed.

Lemma bd_case_cmp : cmp_ind_universes si_Σ bd_case_ci #|[bd_X]| [] [].
Proof. unfold cmp_ind_universes. apply cmp_global_instance_refl; tc. Qed.

Lemma bd_case_wf_brs : wf_branches si_idecl [bd_case_br].
Proof. constructor; [constructor|constructor]. Qed.

(** The branch: [G F ◃ (λ z : I (G F). Prop) (c (G F))], by a β step on the right. *)
Lemma bd_case_br_check : si_Σ ;;; bd_ΓFG |-E bd_GF ◃ tApp bd_case_ptm bd_case_cstr.
Proof.
  econstructor; [exact bd_GF_infer|].
  apply JoinE_red_r. apply rt_step.
  change (red1 si_Σ bd_ΓFG (tApp (tLambda bd_zna bd_IGF si_P) bd_case_cstr) (si_P {0 := bd_case_cstr})).
  apply red_beta.
Qed.

(** The [match], by the constructor [inferE_Case]: its parameter premise [bd_case_pars_join]
    compares [G (λ y : Prop. F y)] and [G F], which differ ([bd_case_pars_differ]) and which
    the η step [bd_case_eta_step] relates.
    INSTANCE NONDEGEN BDTypingEtaInstances.bd_case_pars_differ
    TARGET BDTypingEta.inferE_Case *)
Lemma inferingE_Case_inst : si_Σ ;;; bd_ΓFG |-E bd_case ▹ tApp bd_case_ptm bd_case_disc.
Proof.
  refine (inferE_Case _ _ bd_case_ci bd_case_p bd_case_disc [bd_case_br] [bd_X] [] (Sort.super sProp)
            si_mdecl si_idecl bd_case_disc_ind si_declared_inductive (bd_P_sort _) eq_refl
            (alpha_eq_reflexive _) bd_case_wf_pred bd_case_cons bd_case_predctx_wf bd_case_elim
            bd_case_rel bd_case_ctx_inst eq_refl bd_case_cmp bd_case_pars_join bd_case_wf_brs _).
  constructor; [|constructor].
  split; [constructor|]. cbv zeta.
  split; [constructor|exact bd_case_br_check].
Qed.

(** ** [bidir_ind_envE] with predicates that are not [unit]: the subject is scoped

  [bidir_ind_envE_closedn_inst] instantiates the principle, in any [Σ] with [wfE Σ], with
  - [Pcheck], [Pinfer], [Psort], [Pprod], [Pind]: the subject is scoped by its context,
    [closedn #|Γ| t];
  - [Pj]: the judgment's term (if any) and type are scoped, [lift_wfb_term (closedn #|Γ|) j];
  - [PΓ]: the context is closed, [closed_ctx Γ]; [PΓ_rel]: the extension is scoped by the
    base, [closedn_ctx #|Γ| Γ'].
  Every case of the principle is proved in general. It is the bidirectional twin of the
  subject half of [typecheck_closedE] ([Typing/PCUICClosedTypEta]): it gives the scoping of
  a term from its E derivation, without going through soundness.
  The predicates are not degenerate: each of the eight is false on some input
  ([bdc_nondegenerate]): [tRel 0] is not scoped in [[]], which falsifies the five subject
  predicates; the judgment [_ : tRel 0] is not scoped in [[]]; the context [[_ : tRel 0]] is
  not closed; and the extension [[_ : tRel 0]] of [[]] is not scoped. Some cases still hold
  for every input: the [tSort], [tConst], [tInd] and [tConstruct] subjects are closed terms.
  The binder cases ([tProd], [tLambda],
  [tLetIn], the (co)fixpoints, the [tCase] predicate and branches) move the scope by the
  bound context; the [tCase] case uses [wfE Σ] for the closedness of the inductive's
  predicate and branch contexts ([declared_minductive_closedE]); the [tPrim] case reads
  the array hypotheses. *)

Lemma bdc_nondegenerate :
  closedn #|([] : context)| (tRel 0) = false /\
  lift_wfb_term (closedn #|([] : context)|) (j_vass si_na (tRel 0)) = false /\
  closed_ctx [vass si_na (tRel 0)] = false /\
  closedn_ctx #|([] : context)| [vass si_na (tRel 0)] = false.
Proof. repeat split; reflexivity. Qed.

Lemma bdc_ctx_inst_closedn {P : context -> term -> term -> Type} {Γ inst Δ} :
  ctx_inst P Γ inst Δ -> (forall t T, P Γ t T -> is_true (closedn #|Γ| t)) ->
  is_true (forallb (closedn #|Γ|) inst).
Proof.
  intros h hP. induction h as [|na t i inst' Δ' hi _ IH|na b t inst' Δ' _ IH].
  - reflexivity.
  - change (is_true (closedn #|Γ| i && forallb (closedn #|Γ|) inst')).
    apply/andP; split; [exact (hP _ _ hi)|exact IH].
  - exact IH.
Qed.

(** The principle, with the scoping predicates, each false on some input ([bdc_nondegenerate]).
    INSTANCE NONDEGEN BDTypingEtaInstances.bdc_nondegenerate
    TARGET BDTypingEta.bidir_ind_envE *)
Lemma bidir_ind_envE_closedn_inst {cf : checker_flags} (Σ : global_env_ext) (wfΣ : @wfE cf Σ) :
  @env_prop_bdE cf Σ
    (fun Γ t _ => closedn #|Γ| t)
    (fun Γ t _ => closedn #|Γ| t)
    (fun Γ t _ => closedn #|Γ| t)
    (fun Γ t _ _ _ => closedn #|Γ| t)
    (fun Γ _ t _ _ => closedn #|Γ| t)
    (fun Γ j => lift_wfb_term (closedn #|Γ|) j)
    (fun Γ => closed_ctx Γ)
    (fun Γ Γ' => closedn_ctx #|Γ| Γ').
Proof.
  eapply bidir_ind_envE.
  - (* judgments *)
    intros Γ j (Htm & s & (_ & Hty) & _).
    change (is_true (option_default (closedn #|Γ|) (j_term j) true && closedn #|Γ| (j_typ j))).
    apply/andP; split; [|exact Hty].
    revert Htm. case: (j_term j) => [tm|] /= Htm; [exact (snd Htm)|reflexivity].
  - (* contexts *)
    intros Γ wfΓ hover hall. clear hover wfΓ.
    change (is_true (closed_ctx Γ)).
    induction hall as [|Δ na t _ IH h|Δ na b t _ IH h].
    + reflexivity.
    + destruct h as (_ & s & hs & _).
      change (is_true (closed_ctx Δ && closedn (#|Δ| + 0) t)). rewrite Nat.add_0_r.
      apply/andP; split; [exact IH|exact hs].
    + destruct h as (hb & s & hs & _).
      change (is_true (closed_ctx Δ && (closedn (#|Δ| + 0) b && closedn (#|Δ| + 0) t))).
      rewrite Nat.add_0_r.
      apply/andP; split; [exact IH|apply/andP; split; [exact hb|exact hs]].
  - (* context extensions *)
    intros Γ Γ' wfΓ' hover hall. clear hover wfΓ'.
    change (is_true (closedn_ctx #|Γ| Γ')).
    unfold All_local_rel in hall.
    induction hall as [|Δ na t _ IH h|Δ na b t _ IH h].
    + reflexivity.
    + destruct h as (_ & s & hs & _).
      have hs' : is_true (closedn #|Γ ,,, Δ| t) := hs.
      rewrite app_context_length in hs'.
      change (is_true (closedn_ctx #|Γ| Δ && closedn (#|Δ| + #|Γ|) t)).
      apply/andP; split; [exact IH|exact hs'].
    + destruct h as (hb & s & hs & _).
      have hb' : is_true (closedn #|Γ ,,, Δ| b) := hb.
      have hs' : is_true (closedn #|Γ ,,, Δ| t) := hs.
      rewrite app_context_length in hb' hs'.
      change (is_true (closedn_ctx #|Γ| Δ && (closedn (#|Δ| + #|Γ|) b && closedn (#|Δ| + #|Γ|) t))).
      apply/andP; split; [exact IH|apply/andP; split; [exact hb'|exact hs']].
  - (* tRel *)
    intros Γ n decl h. change (is_true (n <? #|Γ|)).
    apply Nat.ltb_lt. exact (nth_error_Some_length h).
  - (* tSort *)
    intros; exact eq_refl.
  - (* tProd *)
    intros Γ na t b s1 s2 _ hj _ hb.
    have hj' : is_true (closedn #|Γ| t) := hj.
    change (is_true (closedn #|Γ| t && closedn (S #|Γ|) b)).
    apply/andP; split; [exact hj'|exact hb].
  - (* tLambda *)
    intros Γ na t b bty _ hj _ hb.
    have hj' : is_true (closedn #|Γ| t) := hj.
    change (is_true (closedn #|Γ| t && closedn (S #|Γ|) b)).
    apply/andP; split; [exact hj'|exact hb].
  - (* tLetIn *)
    intros Γ na b B t A _ hj _ ht.
    have hj' : is_true (closedn #|Γ| b && closedn #|Γ| B) := hj.
    change (is_true (closedn #|Γ| b && closedn #|Γ| B && closedn (S #|Γ|) t)).
    apply/andP; split; [exact hj'|exact ht].
  - (* tApp *)
    intros Γ t na A B u _ ht _ hu.
    change (is_true (closedn #|Γ| t && closedn #|Γ| u)).
    apply/andP; split; [exact ht|exact hu].
  - (* tConst *)
    intros; exact eq_refl.
  - (* tInd *)
    intros; exact eq_refl.
  - (* tConstruct *)
    intros; exact eq_refl.
  - (* tCase *)
    intros Γ ci p c brs args u ps mdecl idecl predctx ptm
      _ hc isdecl _ hret _ heqctx hwfp _ _ _ _ _ _ hpars _ _ _ hwfbrs hbrs.
    pose proof (declared_minductive_closedE (wfΣ := wfΣ) (proj1 isdecl)) as hcl.
    pose proof (declared_minductive_ind_nparsE (wfΣ := wfΣ) (proj1 isdecl)) as hnp.
    pose proof (declared_inductive_closed_constructorsE (wfΣ := wfΣ) isdecl) as hctors.
    pose proof (wf_predicate_length_pars hwfp) as hlenp.
    rewrite hnp in hlenp.
    change (is_true (test_predicate_k (fun _ => true) closedn #|Γ| p && closedn #|Γ| c &&
                     test_branches_k p closedn #|Γ| brs)).
    apply/andP; split; [apply/andP; split|].
    + change (is_true (forallb (closedn #|Γ|) (pparams p) &&
                       test_context_k closedn #|pparams p| (pcontext p) &&
                       closedn (#|pcontext p| + #|Γ|) (preturn p))).
      apply/andP; split; [apply/andP; split|].
      * exact (bdc_ctx_inst_closedn hpars (fun _ _ h => h)).
      * rewrite (closedn_ctx_alpha heqctx) hlenp.
        exact (PCUICClosed.closed_ind_predicate_context isdecl hcl).
      * have e : #|Γ ,,, predctx| = #|pcontext p| + #|Γ|.
        { rewrite app_context_length. f_equal. exact (case_predicate_context_length (ci := ci) hwfp). }
        have hret' : is_true (closedn #|Γ ,,, predctx| (preturn p)) := hret.
        rewrite e in hret'. exact hret'.
    + exact hc.
    + pose proof (All2i_All_mix_left hctors
        (All2i_All2_mix_left (Forall2_All2 (P := wf_branch) _ _ hwfbrs) hbrs)) as hb.
      clear -hb hcl hlenp.
      induction hb as [|i cdecl br cdecls brs' [hcc [hwb hR]] _ IH]; [reflexivity|].
      change (is_true (test_branch_k p closedn #|Γ| br && forallb (test_branch_k p closedn #|Γ|) brs')).
      apply/andP; split; [|exact IH].
      destruct hR as (heqb & hR). cbv zeta in hR. destruct hR as (_ & _ & _ & hbody).
      change (is_true (test_context_k closedn #|pparams p| (bcontext br) &&
                       closedn (#|bcontext br| + #|Γ|) (bbody br))).
      apply/andP; split.
      * rewrite (closedn_ctx_alpha heqb) hlenp.
        exact (closed_cstr_branch_context_genE hcl hcc).
      * have hbody' : is_true (closedn #|Γ ,,, (case_branch_type (ci_ind ci) mdecl idecl p br ptm i cdecl).1|
                                 (bbody br)) := hbody.
        rewrite app_context_length case_branch_type_fst (case_branch_context_length hwb) in hbody'.
        exact hbody'.
  - (* tProj *)
    intros Γ p c u mdecl idecl cdecl pdecl args _ _ hc _.
    change (is_true (closedn #|Γ| c)). exact hc.
  - (* tFix *)
    intros Γ mfix n decl _ _ _ htys _ hbodies _.
    change (is_true (forallb (test_def (closedn #|Γ|) (closedn (#|mfix| + #|Γ|))) mfix)).
    apply All_forallb. eapply All_impl; [exact (All_mix htys hbodies)|]. intros d [hty hbody].
    have hty' : is_true (closedn #|Γ| (dtype d)) := hty.
    have hbody' : is_true (closedn #|Γ ,,, fix_context mfix| (dbody d) &&
                           closedn #|Γ ,,, fix_context mfix| (lift0 #|fix_context mfix| (dtype d))) := hbody.
    move/andP: hbody' => [hb _]. rewrite app_context_length fix_context_length in hb.
    change (is_true (closedn #|Γ| (dtype d) && closedn (#|mfix| + #|Γ|) (dbody d))).
    apply/andP; split; [exact hty'|exact hb].
  - (* tCoFix *)
    intros Γ mfix n decl _ _ _ htys _ hbodies _.
    change (is_true (forallb (test_def (closedn #|Γ|) (closedn (#|mfix| + #|Γ|))) mfix)).
    apply All_forallb. eapply All_impl; [exact (All_mix htys hbodies)|]. intros d [hty hbody].
    have hty' : is_true (closedn #|Γ| (dtype d)) := hty.
    have hbody' : is_true (closedn #|Γ ,,, fix_context mfix| (dbody d) &&
                           closedn #|Γ ,,, fix_context mfix| (lift0 #|fix_context mfix| (dtype d))) := hbody.
    move/andP: hbody' => [hb _]. rewrite app_context_length fix_context_length in hb.
    change (is_true (closedn #|Γ| (dtype d) && closedn (#|mfix| + #|Γ|) (dbody d))).
    apply/andP; split; [exact hty'|exact hb].
  - (* tPrim *)
    intros Γ p prim_ty cdecl _ _ _ _ hp.
    destruct hp as [i|f|s|a _ hty hdef hvalue]; try exact eq_refl.
    change (is_true (forallb (closedn #|Γ|) (array_value a) && closedn #|Γ| (array_default a) &&
                     closedn #|Γ| (array_type a))).
    apply/andP; split; [apply/andP; split|].
    + exact (All_forallb (closedn #|Γ|) _ hvalue).
    + exact hdef.
    + exact hty.
  - (* ▹□ *)
    intros Γ t T u _ ht _. exact ht.
  - (* ▹Π *)
    intros Γ t T na A B _ ht _. exact ht.
  - (* ▹{ind} *)
    intros Γ ind t T ui args _ ht _. exact ht.
  - (* ◃ *)
    intros Γ t T T' _ ht _. exact ht.
Qed.

(** The instance applied to the η-parameter [match] of [inferingE_Case_inst]. *)
Lemma inferingE_Case_inst_closedn : closedn #|bd_ΓFG| bd_case.
Proof.
  exact (fst (snd (snd (snd (snd (bidir_ind_envE_closedn_inst si_Σ si_wfE))))) _ _ _ inferingE_Case_inst).
Qed.
