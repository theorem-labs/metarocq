(* Distributed under the terms of the MIT license. *)

(** * The conversion layer of subject reduction over [typingE] (row T1)

  Base [PCUICSR.v] uses conversion facts that had no E twin at [d8120081] (T1 audit, defect 2).
  This file states their E twins and proves them from the landed E layer. Each lemma restates its
  base twin with the relation changed and nothing else: [ws_cumul_pb] → [ws_cumul_pbE],
  [ws_cumul_ctx_pb] → [ws_cumul_ctx_pbE], [ws_cumul_ctx_pb_rel] → [ws_cumul_ctx_pbE_rel],
  [typing] → [typingE], [isType] → [on_type (lift_typing typingE)], the algorithmic
  [cumulAlgo_gen] ([Σ ;;; Γ |- T <= U] / [= U]) → [JoinE Σ Γ pb T U] (stream lead's ruling,
  2026-10-29 09:26Z: the canonical I5 join of [PCUICEtaI5], the one [ws_cumul_pbE] is defined over;
  it is the only [JoinE] in scope here), [conv_witness] →
  [conv_witnessE]. The environment premise is [wfE Σ] for typed facts and [ClosedBodies Σ] for
  conversion and reduction facts ([wfE_ClosedBodies] gives it from [wfE]); where base's [wf Σ]
  premise is not used, the twin has no premise.

  This file stays LOW in the import order: the E copies of [PCUICSpine] and [PCUICInductives]
  (copies 15/16) import it, so it imports neither base [PCUICSR] nor any of those copies. Where base
  [conv_ctx_set_binder_name] uses the SR-local syntactic lemma [is_closed_context_set_binder_name],
  the twin here transports closedness with [eq_context_upto_names_on_free_vars] ([PCUICConfluence])
  instead. [subst_instance_ws_cumul_ctx_pbE_rel] (two different lemmas carry this name: P3's in
  [PCUICWsCumulEtaCtx] and copy 8's) is not used here.

  ** Triage (items 1-3 of the T1 conversion list)

  (a) syntactic: not copied. (b) E twin written here. (c) needs an unlanded T0 copy: not written,
  the copy is named. (d) needs SR-local syntactic lemmas, so it belongs to the T1 copy (which can
  import base [PCUICSR]); not written here. "landed" names the existing E twin. Lines are base lines
  at [d8120081] (unchanged at [07e404be]).

  | base lemma (file:line)                                   | decision | E name / where / waits on |
  |----------------------------------------------------------|----------|---------------------------|
  | ws_cumul_pb_it_mkLambda_or_LetIn (PCUICConversion:2923)  | (b)      | ws_cumul_pbE_it_mkLambda_or_LetIn |
  | substitution_ws_cumul_ctx_pb_red_subst (Conversion:3194) | (b)      | substitution_ws_cumul_ctx_pbE_red_subst |
  | eq_context_upto_ws_cumul_ctx_pb (PCUICConversion:3229)   | (b)      | eq_context_upto_ws_cumul_ctx_pbE |
  | red_conv (PCUICWellScopedCumulativity:358)               | landed   | red_ws_cumul_pbE @ PCUICWellScopedCumulativityEta.v:164 |
  | mfix_body_on_red_type (PCUICSR:55)                       | (b)      | mfix_body_on_red_typeE |
  | mfix_on_ind_red1_type (PCUICSR:67)                       | (b)      | mfix_on_ind_red1_typeE |
  | conv_context_smash_end (PCUICSR:140)                     | (c)      | copy 15 (PCUICSpine): the E twin of ws_cumul_ctx_pb_rel_smash (PCUICSpine:2854), whose premises are wf_local |
  | conv_context_rel_reln (PCUICSR:172)                      | (b)      | conv_context_rel_relnE |
  | conv_context_rel_to_extended_list (PCUICSR:181)          | (b)      | conv_context_rel_to_extended_listE |
  | eq_context_alpha_conv (PCUICSR:191)                      | (b)      | eq_context_alpha_convE |
  | conv_refl' (PCUICSR:384), conv_context_refl (PCUICSR:450)| item 4   | algorithmic; see the second table |
  | conv_ctx_set_binder_name (PCUICSR:492)                   | (b)      | conv_ctx_set_binder_nameE |
  | red_one_decl_red_ctx (PCUICSR:628)                       | (b)      | red_one_decl_red_ctx_cb (reduction; ClosedBodies) |
  | into_closed_red_ctx (PCUICSR:642)                        | (b)      | into_closed_red_ctx_cb (reduction; base's wf is unused, so no premise) |
  | red_one_decl_red_context (PCUICSR:660)                   | (b)      | red_one_decl_red_context_cb (reduction; ClosedBodies) |
  | red_one_decl_ws_cumul_ctx_pb (PCUICSR:670)               | (b)      | red_one_decl_ws_cumul_ctx_pbE |
  | wt_cumul_pb_refl (PCUICSR:1056)                          | (b)      | wt_cumul_pb_reflE |
  | ws_cumul_pb_meta_refl (PCUICSR:1063)                     | (b)      | ws_cumul_pbE_meta_refl |
  | ws_cumul_pb_eq_trans (PCUICSR:1069)                      | (b)      | ws_cumul_pbE_eq_trans |
  | eq_ws_cumul_pb_trans (PCUICSR:1075)                      | (b)      | eq_ws_cumul_pbE_trans |
  | ws_cumul_pb_terms_eq_trans (PCUICSR:1081)                | (b)      | ws_cumul_pbE_terms_eq_trans |
  | eq_ws_cumul_pb_terms_trans (PCUICSR:1087)                | (b)      | eq_ws_cumul_pbE_terms_trans |
  | wt_terms_ws_cumul_pb (PCUICSR:1113)                      | (b)      | wt_terms_ws_cumul_pbE |
  | weakening_ws_cumul_ctx_pb (PCUICSR:1119)                 | (b)      | weakening_ws_cumul_ctx_pbE |
  | ws_cumul_pb_terms_refl (PCUICSR:1210)                    | landed   | WT_refl @ PCUICConversionEtaCongr.v:88 |
  | closed_red1_ws_cumul_pb (PCUICSR:1239)                   | (b)      | closed_red1_ws_cumul_pbE |
  | substitution_ws_cumul_pb_subst_conv (PCUICSR:1360, the   | (c)      | copy 10 (PCUICSubstitution: subsletE, subslet_untyped_subsletE) and copy 16 (PCUICInductives: wf_subsletE). Its core is landed: substitution_ws_cumul_pbE_subst_conv @ PCUICWsCumulEtaCtx.v:523 (untyped_subslet form); the SR-local lemma only turns subslet into untyped_subslet |
  |   SR-local version)                                      |          |                           |
  | type_Cumul_alt (PCUICSR:1456)                            | (b)      | type_Cumul_altE: the JoinE form, which is both the base twin (by the ruling) and the checker's T1_facts field |
  | case_nondep_predicate_conv (PCUICSR:1550)                | (d)      | belongs to the T1 copy itself: it needs four SR-local syntactic lemmas (case_predicate_context_vass, mk_ctx_subst_snoc_ass, subst0_cons_nondep, on_free_vars_it_mkLambda_or_LetIn), which this file cannot import; its conversion steps are landed (red_betas_typedE @ PCUICWsCumulEtaCtxTyp.v:187, red_ws_cumul_pbE) |
  | typing_spine_prim_arg_types (PCUICSR:1591),              | (c)      | copy 14 (PCUICArities: typing_spineE) |
  |   typing_spine_prim_args (PCUICSR:1870)                  |          |                           |
  | red_has_rec_arg (PCUICSR:36)                             | (b)      | red_has_rec_arg_cb (reduction; ClosedBodies), from red_it_mkProd_or_LetIn_smash_cb below |
  | upto_names_conv_context (PCUICAlpha:383)                 | item 4   | algorithmic ([conv_context cumulAlgo_gen] from [≡Γ]); see the second table |

  ** Environment and reduction facts with a base [wf Σ] premise (T1 case audit §2, §12 N2/N3)

  | base lemma (file:line)                                         | decision | E name / where |
  |----------------------------------------------------------------|----------|----------------|
  | declared_inductive_closed_params_inst (Typing/PCUICClosedTyp:594)| (b)    | declared_inductive_closed_params_instE (wfE), from the landed declared_inductive_closed_paramsE @ Typing/PCUICClosedTypEta.v:641 |
  | declared_minductive_closed_inds (Conversion/PCUICClosedConv:108)| landed  | closed_inds @ Syntax/PCUICClosed.v:824: the same conclusion with no premise at all (inds are closed syntactically) |
  | declared_inductive_wf_global_ext (Conversion/PCUICUnivSubstitutionConv:1997) | copy 8 | declared_inductive_wf_global_extE @ Typing/PCUICUnivSubstitutionTypEta.v:372 on fork/wip/eta-e3-copies2-2026-10-29 (unlanded). Base's conclusion wf_global_ext contains base [wf Σ], which [wfE Σ] does not give; copy 8's twin concludes wf_global_extE |
  | consistent_instance_valid_constraints (Conversion/PCUICUnivSubstitutionConv:737) | copy 8 | consistent_instance_valid_constraintsE @ Typing/PCUICUnivSubstitutionTypEta.v:222 on the same branch (premise wf_ext_wkE) |
  | red_it_mkProd_or_LetIn_smash (PCUICInductives:2034)            | (b)      | red_it_mkProd_or_LetIn_smash_cb (ClosedBodies; base's proof with the _cb lemmas) |
  | closed_red_from_empty (PCUICInductives:269)                    | (b)      | closed_red_from_empty_cb (ClosedBodies) |
  | red_expand_let (PCUICSpine:1686)                               | (b)      | red_expand_let_cb: no environment premise, and base's [wf_local Σ (Γ ,,, [vdef na b ty])] premise replaced by the closedness it is used for; red_expand_letE: the twin with [wfE Σ] and [wf_localE], which is also the form of the checker's U_facts field |

  The other declarations of [PCUICSR.v] before [sr_red1] (line 1942) are syntactic (a) or belong to
  the typing layer of the T1 copy itself (prim-op typing, [lift_judgment_SR], [isType_*],
  [wt_closed_red1], case-context well-formedness); their conversion steps map as in the second table.

  ** Item 4: the algorithmic ([cumulAlgo_gen]) uses in [PCUICSR.v], and the landed E fact for each

  There is no E algorithmic relation. Each use maps to a landed fact; no lemma is added for them.

  | base fact (PCUICSR lines)                                    | landed E fact |
  |--------------------------------------------------------------|---------------|
  | cumulAlgo_cumulSpec (64, 2881)                               | ws_cumul_pbE_forget_spec (PCUICWellScopedCumulativityEta.v:99) |
  | cumulSpec_cumulAlgo (1739), cumulSpec_cumulAlgo_curry,       | into_ws_cumul_pbE_spec (PCUICWellScopedCumulativityEta.v:113) |
  |   convSpec_convAlgo_curry                                    |               |
  | convSpec_cumulSpec                                           | convSpecE_cumulSpecE (PCUICEtaJoinSpec.v:108) |
  | cumul_Trans (63)                                             | constructor cumulE_Trans (PCUICCumulativitySpecEta.v:31) |
  | convSpec_subst_instance (1733)                               | cumulSpecE_subst_instance (PCUICCumulativitySpecEtaClosure.v:1039) |
  | red_conv, scoped (hint 118; 1242, 2026, 2035, 2058, 2072,    | red_ws_cumul_pbE (PCUICWellScopedCumulativityEta.v:164) |
  |   3255)                                                      |               |
  | PCUICCumulativity.red_conv (2942, 3418, 3552, 3696, 3768,    | JoinE_red_l at Conv (PCUICWellScopedCumulativityEta.v:67) |
  |   3773, 3774)                                                |               |
  | red_cumul (hint 118; 3395, 3539)                             | JoinE_red_l at Cumul; red1 steps also red1_cumulSpecE (PCUICEtaJoinSpec.v) |
  | red_cumul_inv (2108)                                         | JoinE_red_r (PCUICWellScopedCumulativityEta.v:72) |
  | conv_sym (2942, 3417, 3474, 3551, 3598)                      | JoinE_sym (PCUICEtaI5A2.v:480); scoped: ws_cumul_pbE_sym |
  | conv_cumul (2940, 3417, 3474, 3551, 3598, 3696)              | JoinE_sym twice, as in ws_cumul_pbE_eq_le (PCUICWsCumulEtaCtx.v:111); scoped: ws_cumul_pbE_eq_le / ws_cumul_eq_pbE |
  | cumul_refl' (2038, 2049, 2062, 2076), conv_refl' (384, no use)| JoinE_refl (PCUICWellScopedCumulativityEta.v:55) |
  | cumul_red_r / [econstructor 3] on cumul_refl' and a red1 step| JoinE_red_r of red1_red |
  |   (2038, 2048, 2061, 2075)                                   |               |
  | conv_context cumulAlgo_gen (3338, 3483, 3764), conv_ctx_refl | conv_context (@JoinE cf) Σ, refl by eq_context_upto_names_conv_contextE (PCUICWsCumulEtaCtx.v:203) or cumul_decls_reflE (PCUICWsCumulEtaCtxTyp.v:224); scoped: ws_cumul_ctx_pbE_refl_pb; its consumer context_conversion is copy 9 |
  |   (3341, 3767, 3770), instance conv_context_refl (450)       |               |
  | ws_cumul_pb_forget_conv (3357)                               | ws_cumul_pbE_forget (PCUICWellScopedCumulativityEta.v:96) |
  | notation [Σ ;;; Γ |- x = y] (386) / [<=] (1458)              | JoinE Σ Γ Conv x y / JoinE Σ Γ Cumul x y |
  | upto_names_conv_context (PCUICAlpha:383; SR use 2677)        | the SR use converts [Γ ,,, pctx] and [Γ ,,, case_predicate_context ..], related by [eq_context_upto_names] (built at 2678-2679 by eq_context_upto_cat and eq_context_upto_names_eq_context_alpha): eq_context_upto_names_conv_contextE (PCUICWsCumulEtaCtx.v:203), then into_ws_cumul_ctx_pbE. The general premise [≡Γ] (α-equivalence inside the types) has no landed twin and SR does not need it |

  **The hypotheses are satisfiable:** [ClosedBodies Σ] by any well-formed environment
  ([wf_ClosedBodies]; [wfE_ClosedBodies] for [wfE]); [wfE Σ] by [wf_incl_E]; every [ws_cumul_pbE],
  [ws_cumul_ctx_pbE] and [JoinE] premise by reflexivity; the scoping premises by any scoped context
  and terms. Each lemma with a premise is applied to a concrete instance, with every premise proved,
  in [PCUICSREtaConvInstances]. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICInduction PCUICCases PCUICLiftSubst PCUICEquality
     PCUICSigmaCalculus PCUICClosed PCUICReduction PCUICOnOne PCUICOnFreeVars PCUICTyping
     PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICWellScopedCumulativity PCUICSubstitution PCUICContextSubst PCUICConfluence PCUICContextReduction
     PCUICParallelReduction PCUICConversion PCUICContextConversion PCUICCasesContexts PCUICContexts
     PCUICTypingEta PCUICTypingEtaInd PCUICClosedTypEta PCUICEtaI5
     PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICWsCumulEtaSubst
     PCUICContextConversionEta PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp PCUICClosedBodies.
From MetaRocq.PCUIC Require PCUICClosedTyp PCUICWeakeningConv.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(** ** Item 1-2: the base conversion lemmas *)

Section ConvE.

  Context {cf : checker_flags} {Σ : global_env_ext} {cbΣ : ClosedBodies Σ}.

  Lemma ws_cumul_ctx_pbE_cons_inv {pb Γ Γ' d d'} :
    ws_cumul_ctx_pbE pb Σ (d :: Γ) (d' :: Γ') ->
    ws_cumul_ctx_pbE pb Σ Γ Γ' × ws_cumul_declsE pb Σ Γ d d'.
  Proof. intros h. unfold ws_cumul_ctx_pbE in h. depelim h. split; assumption. Qed.

  (** Base [ws_cumul_pb_it_mkLambda_or_LetIn] ([PCUICConversion.v:2923]), under
      [ClosedBodies Σ] in place of [wf Σ]. *)
  Lemma ws_cumul_pbE_it_mkLambda_or_LetIn {pb Γ Δ1 Δ2 t1 t2} :
    ws_cumul_ctx_pbE Conv Σ (Γ ,,, Δ1) (Γ ,,, Δ2) ->
    ws_cumul_pbE Conv Σ (Γ ,,, Δ1) t1 t2 ->
    ws_cumul_pbE pb Σ Γ (it_mkLambda_or_LetIn Δ1 t1) (it_mkLambda_or_LetIn Δ2 t2).
  Proof.
    induction Δ1 as [|d Δ1 IH] in Δ2, t1, t2 |- *; intros X Y.
    - destruct Δ2 as [|c Δ2].
      + exact (ws_cumul_eq_pbE Y).
      + have hl := All2_fold_length X. rewrite !app_context_length /= in hl. lia.
    - destruct Δ2 as [|c Δ2].
      { have hl := All2_fold_length X. rewrite !app_context_length /= in hl. lia. }
      have X' : ws_cumul_ctx_pbE Conv Σ (d :: (Γ ,,, Δ1)) (c :: (Γ ,,, Δ2)) := X.
      destruct (ws_cumul_ctx_pbE_cons_inv X') as [Xr w].
      refine (IH Δ2 (mkLambda_or_LetIn d t1) (mkLambda_or_LetIn c t2) Xr _).
      revert Y. unfold ws_cumul_declsE in w.
      destruct w as [na na' A A' hna hA|na na' b A b' A' hna hb hA]; cbn; intros Y.
      + exact (ws_cumul_pbE_Lambda (wsE_right hA) Y).
      + exact (ws_cumul_pbE_LetIn hna hb hA Y).
  Qed.

  (** Base [substitution_ws_cumul_ctx_pb_red_subst] ([PCUICConversion.v:3194]), under
      [ClosedBodies Σ]. *)
  Lemma substitution_ws_cumul_ctx_pbE_red_subst {Γ Δ Γ' s s'} :
    is_closed_context (Γ ,,, Δ ,,, Γ') ->
    All2 (closed_red Σ Γ) s s' ->
    untyped_subslet Γ s Δ ->
    ws_cumul_ctx_pbE Conv Σ (Γ ,,, subst_context s 0 Γ') (Γ ,,, subst_context s' 0 Γ').
  Proof.
    move=> cl hs hsub.
    induction Γ' as [|d Γ' IH].
    - rewrite !subst_context_nil /=. apply ws_cumul_ctx_pbE_refl_pb.
      destruct (closed_app3_inv Γ Δ [] cl) as [hΓ _ _]. exact hΓ.
    - have cl0 : is_closed_context (Γ ,,, Δ ,,, Γ').
      { move: cl. by rewrite /= on_free_vars_ctx_snoc => /andP []. }
      have hd : on_free_vars_decl (shiftnP #|Γ ,,, Δ ,,, Γ'| xpred0) d.
      { move: cl. by rewrite /= on_free_vars_ctx_snoc => /andP []. }
      rewrite !subst_context_snoc0. constructor; [exact (IH cl0)|].
      unfold ws_cumul_declsE.
      destruct d as [na [bd|] A]; move: hd; rewrite /on_free_vars_decl /test_decl /=.
      + move=> /andP [h1 h2]. rewrite /subst_decl /map_decl /=. constructor; [reflexivity| |].
        * exact (red_ws_cumul_pbE (closed_red_red_subst_cb cl0 hs hsub h1)).
        * exact (red_ws_cumul_pbE (closed_red_red_subst_cb cl0 hs hsub h2)).
      + intros h1. rewrite /subst_decl /map_decl /=. constructor; [reflexivity|].
        exact (red_ws_cumul_pbE (closed_red_red_subst_cb cl0 hs hsub h1)).
  Qed.

  (** Base [eq_context_upto_ws_cumul_ctx_pb] ([PCUICConversion.v:3229]), under
      [ClosedBodies Σ]. Each [compare_term] step enters through the spec
      ([eq_term_upto_univ_cumulSpecE], [into_ws_cumul_pbE_spec]). *)
  Lemma eq_context_upto_ws_cumul_ctx_pbE {pb Γ Γ'} :
    is_closed_context Γ ->
    is_closed_context Γ' ->
    PCUICContextConversion.compare_context Σ pb Γ Γ' ->
    ws_cumul_ctx_pbE pb Σ Γ Γ'.
  Proof.
    intros cl cl' heq.
    induction heq as [|d d' Γ0 Γ0' h IH hd] in cl, cl' |- *; [constructor|].
    move: cl cl'. rewrite !on_free_vars_ctx_snoc => /andP [cl hdcl] /andP [cl' hdcl'].
    constructor; [exact (IH cl cl')|].
    have hlen : #|Γ0| = #|Γ0'| := All2_fold_length h.
    rewrite -hlen in hdcl'.
    move: hdcl hdcl'. unfold ws_cumul_declsE.
    destruct hd as [na na' A A' hna hA|na na' b A b' A' hna hb hA];
      rewrite /on_free_vars_decl /test_decl /=.
    - intros h1 h2. constructor; [exact hna|].
      exact (into_ws_cumul_pbE_spec (eq_term_upto_univ_cumulSpecE Σ Γ0 A A' hA) cl h1 h2).
    - move=> /andP [h1 h1'] /andP [h2 h2']. constructor; [exact hna| |].
      + exact (into_ws_cumul_pbE_spec (eq_term_upto_univ_cumulSpecE Σ Γ0 b b' hb) cl h1 h2).
      + exact (into_ws_cumul_pbE_spec (eq_term_upto_univ_cumulSpecE Σ Γ0 A A' hA) cl h1' h2').
  Qed.

End ConvE.

(** ** Item 3: the helpers of [PCUICSR.v] before [sr_red1] *)

(** *** The fixpoint witness along a reduction of the declared type *)

Section Witness.

  Context {cf : checker_flags} {Σ : global_env_ext} {cbΣ : ClosedBodies Σ}.

  (** Base [mfix_body_on_red_type] ([PCUICSR.v:55]), over [conv_witnessE], under
      [ClosedBodies Σ]. *)
  Lemma mfix_body_on_red_typeE {check Γ mind} {d : def term} {ty} :
    Σ ;;; Γ ⊢ dtype d ⇝ ty ->
    mfix_body_on check (conv_witnessE Σ Γ) mind d ->
    mfix_body_on check (conv_witnessE Σ Γ) mind (def_with_type d ty).
  Proof.
    intros r [tw [hcheck [hop hconv]]].
    exists tw. split; [exact hcheck|]. split; [exact hop|]. cbn.
    eapply cumulE_Trans with (u := dtype d); [exact (clrel_ctx r)|exact (clrel_src r)| |exact hconv].
    exact (ws_cumul_pbE_forget_spec (red_ws_cumul_pbE_inv r)).
  Qed.

  (** Base [mfix_on_ind_red1_type] ([PCUICSR.v:67]), over [conv_witnessE]. *)
  Lemma mfix_on_ind_red1_typeE {check ok} Γ mfix mfix1 :
    OnOne2
    (fun x y : def term =>
     Σ ;;; Γ ⊢ dtype x ⇝ dtype y
     × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) mfix mfix1 ->
    mfix_on_ind check (conv_witnessE Σ Γ) ok mfix ->
    mfix_on_ind check (conv_witnessE Σ Γ) ok mfix1.
  Proof.
    intros o. eapply mfix_on_ind_OnOne2; tea.
    intros [na ty bo ra] [na' ty' bo' ra'] m [r eqs] h; cbn in r, eqs.
    case: eqs => <- <- <-.
    exact (mfix_body_on_red_typeE (d := {| dname := na; dtype := ty; dbody := bo; rarg := ra |}) r h).
  Qed.

End Witness.

(** *** Relative contexts *)

(** Base [conv_context_rel_reln] ([PCUICSR.v:172]); no premise, as in base. *)
Lemma conv_context_rel_relnE {cf} {Σ} {le} Γ Δ Δ' :
  ws_cumul_ctx_pbE_rel le Σ Γ Δ Δ' ->
  forall acc n, reln acc n Δ = reln acc n Δ'.
Proof.
  intros [cl a]. induction a.
  - constructor.
  - intros acc n; destruct p; simpl; auto.
Qed.

(** Base [conv_context_rel_to_extended_list] ([PCUICSR.v:181]). *)
Lemma conv_context_rel_to_extended_listE {cf} {Σ} {le} {Γ Δ Δ'} :
  ws_cumul_ctx_pbE_rel le Σ Γ Δ Δ' ->
  to_extended_list Δ = to_extended_list Δ'.
Proof.
  unfold to_extended_list, to_extended_list_k.
  intros; now eapply conv_context_rel_relnE.
Qed.

(** Base [eq_context_alpha_conv] ([PCUICSR.v:191]); base's [wf Σ] premise is not used, so
    this has none. *)
Lemma eq_context_alpha_convE {cf} {Σ} Γ Δ Δ' :
  eq_context_upto_names Δ Δ' ->
  is_closed_context (Γ ,,, Δ) ->
  is_closed_context (Γ ,,, Δ') ->
  ws_cumul_ctx_pbE_rel Conv Σ Γ Δ Δ'.
Proof.
  intros h cl cl'. split.
  { move: cl. rewrite on_free_vars_ctx_app => /andP [] //. }
  induction h as [|d d' Δ0 Δ0' hd h IH] in cl, cl' |- *; [constructor|].
  move: cl cl'. rewrite /= !on_free_vars_ctx_snoc => /andP [cl hdcl] /andP [cl' _].
  constructor; [exact (IH cl cl')|].
  move: hdcl. destruct hd as [na na' T hna|na na' b T hna]; rewrite /on_free_vars_decl /test_decl /=.
  - intros h1. constructor; [exact hna|]. exact (ws_cumul_pbE_refl cl h1).
  - move=> /andP [h1 h2]. constructor; [exact hna| |].
    + exact (ws_cumul_pbE_refl cl h1).
    + exact (ws_cumul_pbE_refl cl h2).
Qed.

(** Base [conv_ctx_set_binder_name] ([PCUICSR.v:492]), under [ClosedBodies Σ]. *)
Lemma conv_ctx_set_binder_nameE {cf} {Σ : global_env_ext} {cbΣ : ClosedBodies Σ} (Γ Δ Δ' : context) (nas : list aname) :
  All2 (fun x y => eq_binder_annot x y.(decl_name)) nas Δ ->
  All2 (fun x y => eq_binder_annot x y.(decl_name)) nas Δ' ->
  ws_cumul_ctx_pbE_rel Conv Σ Γ Δ Δ' ->
  ws_cumul_ctx_pbE_rel Conv Σ Γ (map2 set_binder_name nas Δ) (map2 set_binder_name nas Δ').
Proof.
  induction 1 in Δ' |- *; intros H; depelim H; intros [cl H']; split; auto;
  depelim H'. cbn. constructor; auto. eapply IHX; auto. split; auto.
  have clΓl' : is_closed_context (Γ ,,, l').
  { depelim a; cbn in *; now apply ws_cumul_pbE_is_closed_context in eqt. }
  have eqctx : ws_cumul_ctx_pbE Conv Σ (Γ,,, map2 set_binder_name l l') (Γ,,, l').
  { eapply eq_context_upto_ws_cumul_ctx_pbE => //.
    eapply (eq_context_upto_names_on_free_vars _ (Γ ,,, l')); [exact clΓl'|].
    eapply All2_app; [|reflexivity]. eapply All2_symP; [tc|]. now apply eq_binder_annots_eq.
    apply eq_context_upto_cat. reflexivity.
    apply eq_context_upto_names_eq_context_upto; tc.
    apply eq_binder_annots_eq => //. }
  depelim a; cbn in *; constructor; auto;
  eapply (ws_cumul_pbE_ws_cumul_ctx_pb (pb':=Conv)); tea.
Qed.

(** *** One-step context reduction *)

Section RedCtx.

  Context {cf : checker_flags} {Σ : global_env_ext} {cbΣ : ClosedBodies Σ}.

  (** Base [red_one_decl_red_ctx] ([PCUICSR.v:628]), under [ClosedBodies Σ]. *)
  Lemma red_one_decl_red_ctx_cb {Γ Δ Δ'} :
    is_closed_context (Γ ,,, Δ) ->
    OnOne2_local_env (fun Δ : context => on_one_decl (red1 Σ (Γ ,,, Δ))) Δ Δ' ->
    red_ctx Σ (Γ ,,, Δ) (Γ ,,, Δ').
  Proof.
    intros iscl o.
    eapply red_ctx_red_context.
    apply red_context_app; [apply red_context_refl|].
    have cl : on_ctx_free_vars (closedP #|Γ ,,, Δ| xpredT) (Γ ,,, Δ)
      := on_free_vars_ctx_on_ctx_free_vars_closedP_impl _ iscl.
    apply (fst (red_ctx_rel_red_context_rel_cb cbΣ Γ Δ Δ' cl)).
    constructor. exact o.
  Qed.

  (** Base [into_closed_red_ctx] ([PCUICSR.v:642]). Base's [wf Σ] premise is not used, so this
      has none ([cbΣ] is not a premise of it). *)
  Lemma into_closed_red_ctx_cb {Γ Δ} :
    is_closed_context Γ ->
    red_ctx Σ Γ Δ ->
    closed_red_ctx Σ Γ Δ.
  Proof.
    intros iscl red.
    apply on_free_vars_ctx_All_fold in iscl.
    eapply All2_fold_All_fold_mix_left in red; tea. cbn in red. clear iscl.
    eapply All2_fold_impl_ind ; tea.
    intros ???? IH IH' [wf ad].
    eapply All_decls_on_free_vars_impl; tea.
    intros t t' clt redt.
    eapply into_closed_red; tea.
    eapply All2_fold_prod_inv in IH as [IH _].
    eapply All2_fold_All_left in IH.
    now eapply on_free_vars_ctx_All_fold in IH.
  Qed.

  (** Base [red_one_decl_red_context] ([PCUICSR.v:660]), under [ClosedBodies Σ]. *)
  Lemma red_one_decl_red_context_cb {Γ Δ Δ'} :
    is_closed_context (Γ ,,, Δ) ->
    OnOne2_local_env (fun Δ : context => on_one_decl (red1 Σ (Γ ,,, Δ))) Δ Δ' ->
    closed_red_ctx Σ (Γ ,,, Δ) (Γ ,,, Δ').
  Proof.
    intros iscl o.
    eapply into_closed_red_ctx_cb => //.
    now apply red_one_decl_red_ctx_cb.
  Qed.

  (** Base [red_one_decl_ws_cumul_ctx_pb] ([PCUICSR.v:670]), under [ClosedBodies Σ]. *)
  Lemma red_one_decl_ws_cumul_ctx_pbE {Γ Δ Δ'} :
    is_closed_context (Γ ,,, Δ) ->
    OnOne2_local_env (fun Δ : context => on_one_decl (red1 Σ (Γ ,,, Δ))) Δ Δ' ->
    ws_cumul_ctx_pbE Conv Σ (Γ ,,, Δ) (Γ ,,, Δ').
  Proof.
    intros; now eapply closed_red_ctx_ctx, red_one_decl_red_context_cb.
  Qed.

End RedCtx.

(** *** Reflexivity, equations, weakening *)

(** Base [ws_cumul_pb_meta_refl] ([PCUICSR.v:1063]); base's [wf Σ] is not used. *)
Lemma ws_cumul_pbE_meta_refl {cf} {Σ} {Γ T U} :
  is_closed_context Γ -> closedn #|Γ| T -> T = U -> ws_cumul_pbE Conv Σ Γ T U.
Proof.
  intros clΓ cl ->. apply ws_cumul_pbE_refl => //. now apply closedn_on_free_vars.
Qed.

(** Base [ws_cumul_pb_eq_trans] ([PCUICSR.v:1069]). *)
Lemma ws_cumul_pbE_eq_trans {cf} {Σ} {Γ T U V} :
  ws_cumul_pbE Conv Σ Γ T U -> U = V -> ws_cumul_pbE Conv Σ Γ T V.
Proof. now intros tr ->. Qed.

(** Base [eq_ws_cumul_pb_trans] ([PCUICSR.v:1075]). *)
Lemma eq_ws_cumul_pbE_trans {cf} {Σ} {Γ T U V} :
  T = U -> ws_cumul_pbE Conv Σ Γ U V -> ws_cumul_pbE Conv Σ Γ T V.
Proof. now intros -> tr. Qed.

(** Base [ws_cumul_pb_terms_eq_trans] ([PCUICSR.v:1081]). *)
Lemma ws_cumul_pbE_terms_eq_trans {cf} {Σ} {Γ T U V} :
  ws_cumul_pbE_terms Σ Γ T U -> U = V -> ws_cumul_pbE_terms Σ Γ T V.
Proof. now intros tr ->. Qed.

(** Base [eq_ws_cumul_pb_terms_trans] ([PCUICSR.v:1087]). *)
Lemma eq_ws_cumul_pbE_terms_trans {cf} {Σ} {Γ T U V} :
  T = U -> ws_cumul_pbE_terms Σ Γ U V -> ws_cumul_pbE_terms Σ Γ T V.
Proof. now intros -> tr. Qed.

(** Base [weakening_ws_cumul_ctx_pb] ([PCUICSR.v:1119]), under [ClosedBodies Σ]. *)
Lemma weakening_ws_cumul_ctx_pbE {cf} {Σ : global_env_ext} {cbΣ : ClosedBodies Σ} {Γ Δ Δ0 Δ1} :
  ws_cumul_ctx_pbE Conv Σ (Γ ,,, Δ0) (Γ ,,, Δ1) ->
  ws_cumul_ctx_pbE Conv Σ (Γ ,,, Δ) (Γ ,,, Δ) ->
  ws_cumul_ctx_pbE Conv Σ (Γ ,,, Δ ,,, lift_context #|Δ| 0 Δ0) (Γ ,,, Δ ,,, lift_context #|Δ| 0 Δ1).
Proof.
  intros h h'.
  pose proof (ws_cumul_ctx_pbE_closed_left h') as clΓΔ.
  apply (fst ws_cumul_ctx_pbE_rel_app). split; [exact clΓΔ|].
  destruct (snd ws_cumul_ctx_pbE_rel_app h) as [_ hr]. clear h h'.
  induction hr as [|d0 d1 Γ0 Γ1 hr IH hd]; [constructor|].
  rewrite !lift_context_snoc0 !Nat.add_0_r -(All2_fold_length hr).
  constructor; [exact IH|].
  destruct hd as [na na' A A' hna hA|na na' b A b' A' hna hb hA]; cbn; constructor; try exact hna.
  - exact (weakening_ws_cumul_pbE hA clΓΔ).
  - exact (weakening_ws_cumul_pbE hb clΓΔ).
  - exact (weakening_ws_cumul_pbE hA clΓΔ).
Qed.

(** Base [closed_red1_ws_cumul_pb] ([PCUICSR.v:1239]), under [ClosedBodies Σ]. *)
Lemma closed_red1_ws_cumul_pbE {cf} {Σ : global_env_ext} {cbΣ : ClosedBodies Σ} {Γ} {t u} :
  closed_red1 Σ Γ t u -> ws_cumul_pbE Conv Σ Γ t u.
Proof. intros cl. exact (red_ws_cumul_pbE (closed_red1_red cl)). Qed.

(** *** Typed facts, under [wfE Σ] *)

Section Typed.

  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}.

  (** Base [wt_cumul_pb_refl] ([PCUICSR.v:1056]). *)
  Lemma wt_cumul_pb_reflE {Γ t T} : Σ ;;; Γ |-E t : T -> ws_cumul_pbE Conv Σ Γ t t.
  Proof.
    intros h. apply ws_cumul_pbE_refl.
    - exact (wf_local_closed_contextE (typingE_wf_local h)).
    - exact (subject_is_open_termE h).
  Qed.

  (** Base [wt_terms_ws_cumul_pb] ([PCUICSR.v:1113]). *)
  Lemma wt_terms_ws_cumul_pbE {Γ ts} :
    All (fun t => ∑ T, Σ ;;; Γ |-E t : T) ts -> ws_cumul_pbE_terms Σ Γ ts ts.
  Proof.
    intros h. unfold ws_cumul_pbE_terms. eapply All_All2; tea.
    cbn; intros x [T HT]. exact (wt_cumul_pb_reflE HT).
  Qed.

  (** Base [type_Cumul_alt] ([PCUICSR.v:1456]). Base's premise is the algorithmic
      [Σ ;;; Γ |- T <= T'] ([cumulAlgo]); by the stream lead's ruling (2026-10-29 09:26Z) its E
      counterpart is the canonical I5 join [JoinE Σ Γ Cumul T T'] ([PCUICEtaI5]), the relation
      [ws_cumul_pbE] is defined over. This is also the form of the field [type_Cumul_alt] of
      [T1_facts] in the checker's [PCUICTypingEtaHyps.v] ([isTypeE] unfolds to
      [on_type (lift_typing typingE)]). The scoping comes from the typings: [T] from
      [type_is_open_termE], [T'] from its sort. *)
  Lemma type_Cumul_altE (Γ : context) (t T T' : term) :
    Σ ;;; Γ |-E t : T -> on_type (lift_typing typingE) Σ Γ T' ->
    JoinE Σ Γ Cumul T T' -> Σ ;;; Γ |-E t : T'.
  Proof.
    intros Ht (_ & s & Hs & _) cum.
    pose proof (wfE_ClosedBodies Σ.1) as cbΣ.
    apply (typeE_Cumul _ _ _ _ _ _ Ht Hs).
    apply (ws_cumul_pbE_forget_spec (pb := Cumul)).
    apply into_ws_cumul_pbE; [exact cum| |exact (type_is_open_termE Ht)|exact (subject_is_open_termE Hs)].
    exact (wf_local_closed_contextE (typingE_wf_local Ht)).
  Qed.

End Typed.

(** ** Environment and reduction facts with a base [wf Σ] premise (T1 case audit §2, §12) *)

(** Base [declared_inductive_closed_params_inst] ([Typing/PCUICClosedTyp.v:594]), under [wfE Σ],
    from the landed [declared_inductive_closed_paramsE]. *)
Lemma declared_inductive_closed_params_instE {cf:checker_flags} {Σ mdecl ind idecl} {wfΣ : wfE Σ} {u} :
  declared_inductive Σ ind mdecl idecl ->
  closed_ctx (subst_instance u mdecl.(ind_params)).
Proof.
  intros h.
  rewrite closedn_subst_instance_context.
  now apply (declared_inductive_closed_paramsE h).
Qed.

(** Base [red_expand_let] ([PCUICSpine.v:1686]). Base's [wf Σ] and its premise
    [wf_local Σ (Γ ,,, [vdef na b ty])] serve only the closedness of that context: the reduction
    unfolds variable 0 ([red_rel_all]). So this has no environment premise, and the closedness of
    the context in place of [wf_local]. *)
Lemma red_expand_let_cb {cf} {Σ : global_env_ext} {Γ na b ty t} :
  is_closed_context (Γ ,,, [vdef na b ty]) ->
  is_open_term (Γ ,,, [vdef na b ty]) t ->
  Σ ;;; Γ ,, vdef na b ty ⊢ t ⇝ lift0 1 (subst1 b 0 t).
Proof.
  intros cl ont.
  apply into_closed_red; [|exact cl|exact ont].
  exact (red_rel_all (Σ := Σ) (Γ := Γ ,, vdef na b ty) (i := 0) (body := b) (t := t) eq_refl).
Qed.

(** Base [red_expand_let] with [wfE]/[wf_localE] in place of [wf]/[wf_local]: the twin, and the
    form of the field [red_expand_let] of [U_facts] in the checker's [PCUICTypingEtaHyps.v]. *)
Lemma red_expand_letE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ na b ty t} :
  wf_localE Σ (Γ ,,, [vdef na b ty]) ->
  is_open_term (Γ ,,, [vdef na b ty]) t ->
  Σ ;;; Γ ,, vdef na b ty ⊢ t ⇝ lift0 1 (subst1 b 0 t).
Proof. intros wfΓ ont. exact (red_expand_let_cb (wf_local_closed_contextE wfΓ) ont). Qed.

(** The two lemmas below are base's proofs ([PCUICInductives.v]), run with base's settings of that
    file, with each [wf Σ] lemma replaced by its landed [_cb] version. *)
Local Set SimplIsCbn.
#[local] Arguments subst_context !s _ !Γ.

(** Base [closed_red_from_empty] ([PCUICInductives.v:269]), under [ClosedBodies Σ]. *)
Lemma closed_red_from_empty_cb {cf} {Σ : global_env_ext} {cbΣ : ClosedBodies Σ} {Γ M N} :
  is_closed_context Γ -> closed M -> red Σ [] M N -> Σ ;;; Γ ⊢ M ⇝ N.
Proof.
  intros clΓ clM r.
  have clN : closed N.
  { rewrite closed_on_free_vars_none.
    eapply (PCUICClosedTyp.red_on_free_vars_cb (P := ssrbool.xpred0)); tea.
    all: rewrite -?closed_on_free_vars_none //. }
  eapply (PCUICWeakeningConv.weakening_red_0_cb (Γ := []) (Γ' := Γ) (P := ssrbool.xpred0) eq_refl) in r => //.
  2:now rewrite -closed_on_free_vars_none.
  rewrite app_context_nil_l !lift_closed // in r.
  eapply into_closed_red => //.
  rewrite -PCUICClosedTyp.is_open_term_closed. eapply closed_upwards; tea. lia.
Qed.

(** Base [red_it_mkProd_or_LetIn_smash] ([PCUICInductives.v:2034]), under [ClosedBodies Σ]. *)
Lemma red_it_mkProd_or_LetIn_smash_cb {cf} {Σ} {cbΣ : ClosedBodies Σ} Γ ctx t u n c :
  Σ ;;; Γ ⊢ it_mkProd_or_LetIn ctx t ⇝ u ->
  nth_error (List.rev (smash_context [] ctx)) n = Some c ->
  ∑ ctx' t' d,
    [× (decompose_prod_assum [] u = (ctx', t')),
       (nth_error (List.rev (smash_context [] ctx')) n = Some d) &
        Σ ;;; Γ ,,, skipn (#|smash_context [] ctx| - n) (smash_context [] ctx) ⊢ decl_type c ⇝ decl_type d ].
Proof.
  rename Γ into Δ.
  revert Δ t u n c.
  induction ctx using ctx_length_rev_ind; simpl; intros Δ t u n c r.
  rewrite nth_error_nil => //.
  destruct d as [na [b|] ty].
  rewrite it_mkProd_or_LetIn_app in r.
  simpl in *.
  eapply invert_red_letin_cb in r as [[d' [ty' [b' [-> redb redty redbody]]]]|]; auto.
  - intros Hnth.
    rewrite !smash_context_app smash_context_acc in Hnth |- *; simpl in *.
    pose proof (nth_error_Some_length Hnth).
    autorewrite with len in H. simpl in H.
    rewrite nth_error_rev_inv in Hnth.
    now autorewrite with len.
    autorewrite with len in Hnth. simpl in Hnth.
    rewrite subst_empty lift0_id lift0_context in Hnth.
    rewrite app_nil_r in Hnth.
    rewrite nth_error_subst_context in Hnth.
    unfold snoc; simpl.
    rewrite decompose_prod_assum_ctx.
    specialize (X Γ ltac:(lia)).
    destruct nth_error eqn:hnth.
    specialize (X _ _ _ n c0 redbody).
    rewrite nth_error_rev_inv in X; autorewrite with len. auto.
    autorewrite with len in X |- *. simpl in *.
    specialize (X hnth).
    destruct X as [ctx' [t' [d [decompb hnth' hred]]]].
    rewrite decompb. eexists _, _, _. split; eauto.
    have hlen := nth_error_Some_length hnth'.
    autorewrite with len in hlen.
    rewrite nth_error_rev_inv in hnth'; autorewrite with len. auto.
    rewrite nth_error_rev_inv; autorewrite with len. cbn.
    rewrite context_assumptions_app /=. simpl in hlen. lia.
    rewrite smash_context_app smash_context_acc /= app_nil_r.
    rewrite subst_empty lift0_id lift0_context.
    rewrite nth_error_subst_context /=.
    autorewrite with len. simpl in *.
    rewrite context_assumptions_app /=. simpl.
    rewrite Nat.add_0_r. autorewrite with len in hnth'. rewrite hnth'.
    simpl. reflexivity. simpl.
    autorewrite with len in Hnth. simpl in Hnth. move: Hnth.
    intros [= <-]. cbn.
    assert (context_assumptions Γ -
    S (context_assumptions Γ - S n) = n) as -> by lia.
    pose proof (nth_error_Some_length hnth'). len in H0.
    assert (context_assumptions ctx' -
    S (context_assumptions ctx'  - S n) = n) as -> by lia.
    simpl.
    rewrite app_nil_r.
    transitivity (subst [b] n (decl_type d)).
    rewrite subst_empty lift0_id lift0_context.
    epose proof (@closed_red_untyped_substitution_cb _ _ _ Δ [vdef na b ty] (skipn (context_assumptions Γ - n) (smash_context [] Γ)) [b]
      (decl_type c0) (decl_type d)).
    forward X. rewrite -{1}(subst_empty 0 b). repeat constructor.
    forward X. cbn. rewrite andb_true_r. eapply redb.
    forward X. eapply hred.
    rewrite skipn_subst_context.
    rewrite !length_skipn in X.
    len in X. simpl in X.
    assert(context_assumptions Γ - (context_assumptions Γ - n) = n) by lia.
    rewrite H1 in X. apply X.
    epose proof (@closed_red_red_subst_cb _ _ _ Δ [vdef na b ty]
       (skipn (context_assumptions Γ - n) (smash_context [] Γ)) _ _ _).
    rewrite subst_empty lift0_id lift0_context.
    rewrite !length_skipn in X; autorewrite with len.
    autorewrite with len in X. simpl in X.
    assert(context_assumptions Γ - (context_assumptions Γ - n) = n) by lia.
    rewrite H1 in X. rewrite skipn_subst_context.
    eapply X; auto. 2:rewrite -{1}(subst_empty 0 b); repeat constructor.
    3:simpl in Hnth; discriminate.
    clear X.
    apply hred. clear X.
    apply closed_red_open_right_cb in hred.
    len in hred.

  - rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in c0.
    intros hnth.
    rewrite smash_context_app smash_context_acc /= app_nil_r in hnth.
    rewrite subst_empty lift0_id lift0_context in hnth.
    specialize (X (subst_context [b] 0 Γ) ltac:(autorewrite with len; lia)).
    specialize (X _ _ _ n c c0).
    rewrite (smash_context_subst []) in X.
    specialize (X hnth). len.
    len in X. simpl in X.
    rewrite smash_context_app smash_context_acc /=.
    rewrite subst_empty lift0_id lift0_context app_nil_r.
    apply X.

  - rewrite smash_context_app /= List.rev_app_distr /=.
    move=> hnth.
    rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= in r.
    eapply invert_red_prod_cb in r as [A' [B' [-> redty redB']]]; auto.
    simpl. rewrite decompose_prod_assum_ctx.
    destruct n.
    * simpl in hnth. noconf hnth; simpl in *.
      destruct (decompose_prod_assum [] B') eqn:decomp.
      eexists _, _, _; split; eauto.
      unfold snoc; simpl. rewrite smash_context_app /= List.rev_app_distr /= //.
      len. simpl.
      rewrite skipn_all2. len. simpl => //.
    * simpl in hnth.
      specialize (X Γ ltac:(lia) (vass na ty :: Δ) t B' n c redB' hnth).
      destruct X as [ctx' [t' [decomp [d hnth' red]]]].
      rewrite d. simpl. eexists _, _, _; split; eauto.
      unfold snoc; simpl. rewrite smash_context_app /= List.rev_app_distr /= hnth' //.
      rewrite length_app. simpl. len.
      assert (context_assumptions Γ + 1 - S n = context_assumptions Γ - n) by lia.
      rewrite H. rewrite skipn_app. len.
      rewrite [skipn _ [_]]skipn_0_eq. lia.
      rewrite app_context_assoc. unfold app_context in red |- *.
      simpl. len in red.
Qed.

(** Base [red_has_rec_arg] ([PCUICSR.v:36]), under [ClosedBodies Σ]. *)
Lemma red_has_rec_arg_cb {cf} {Σ : global_env_ext} {cbΣ : ClosedBodies Σ} {Γ} {d : def term} {ty} :
  Σ ;;; Γ ⊢ dtype d ⇝ ty ->
  has_rec_arg d -> has_rec_arg (def_with_type d ty).
Proof.
  intros r. rewrite /has_rec_arg /def_with_type /=.
  destruct (decompose_prod_assum [] (dtype d)) as [ctx concl] eqn:decomp.
  cbn. move/Nat.ltb_lt => hlt.
  have eqty := decompose_prod_assum_it_mkProd_or_LetIn _ _ _ _ decomp. cbn in eqty.
  have hlt' : rarg d < #|List.rev (smash_context [] ctx)| by len.
  destruct (nth_error (List.rev (smash_context [] ctx)) (rarg d)) as [c|] eqn:hnth.
  2:{ eapply nth_error_None in hnth. lia. }
  rewrite eqty in r.
  destruct (red_it_mkProd_or_LetIn_smash_cb Γ ctx concl ty (rarg d) c r hnth)
    as [ctx' [t' [d' [decomp' hnth' _]]]].
  rewrite decomp' /=. apply/Nat.ltb_lt.
  have hle := nth_error_Some_length hnth'. len in hle.
Qed.
