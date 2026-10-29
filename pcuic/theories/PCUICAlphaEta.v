(* Distributed under the terms of the MIT license. *)

(** * Typing under α-equivalence over [typingE] (plan row T6): the E copy of [PCUICAlpha]

  The E twin of every lemma of base [PCUICAlpha] whose statement mentions typing or
  conversion: [typing] → [typingE], [wf] → [wfE], [wf_local] → [wf_localE], [isType] →
  [isTypeE], [isWfArity] → [isWfArityE], [lift_typing typing] → [lift_typing typingE],
  [cumulSpec0] → [cumulSpecE0], [conv_witness] → [conv_witnessE], [env_prop] → [env_propE]
  ([PCUICTypingEtaInd]), [ws_cumul_ctx_pb_rel] → [ws_cumul_ctx_pbE_rel], and the unscoped
  algorithmic context relation [conv_context cumulAlgo_gen] → [conv_context (@JoinE cf)] (the
  canonical I5 join, stream lead's ruling 2026-10-29 09:26Z). Nothing else changes in a
  statement; each name takes the suffix [E] (plan [t0-plan.md] §2, D1).

  Map, base → E: [upto_names_mfix_on_ind] → [upto_names_mfix_on_indE];
  [eq_context_upto_conv_context_rel] → [eq_context_upto_conv_context_relE];
  [inst_case_predicate_context_eq] → [inst_case_predicate_context_eqE];
  [wf_local_eq_context_upto_names] → [wf_local_eq_context_upto_namesE];
  [eq_context_conversion] → [eq_context_conversionE]; [upto_names_conv_context] →
  [upto_names_conv_contextE]; [isType_eq_context_conversion] →
  [isType_eq_context_conversionE]; [lift_judgment_alpha] → [lift_judgment_alphaE];
  [typing_alpha_prop] → [typing_alpha_propE]; [typing_alpha] → [typing_alphaE];
  [wf_local_alpha] → [wf_local_alphaE]; [isType_alpha] → [isType_alphaE]; [isType_alpha_ctx] →
  [isType_alpha_ctxE]; [isWfArity_alpha] → [isWfArity_alphaE].

  Base lemmas NOT copied, because they mention neither typing nor conversion (they are
  imported from base [PCUICAlpha] and used as they are): [upto_names_terms_refl] (instance),
  [eq_context_upto_empty_impl], [fix_context_nth_error], [destInd_spec],
  [upto_names_has_rec_arg], [rarg_check_one_fix], [is_closed_context_app_left/right],
  [on_free_vars_ctx_All_fold_over], [All2_fold_All_fold_mix_right], [All2_fold_All_right],
  [All_decls_alpha_pb_ws_decl], [eq_context_upto_subst_instance],
  [eq_context_upto_names_eq_context_alpha], [case_predicate_context_equiv],
  [case_branch_context_equiv], [case_branch_type_equiv], [ctx_inst_eq_context] (generic in its
  predicates; written [PCUICAlpha.ctx_inst_eq_context] here, as base [PCUICSpine] has a lemma of
  that name), [case_branch_type_eq_context_gen_1/2], [eq_term_upto_univ_napp_0],
  [upto_names_eq_term_upto_univ], [upto_names_leq_term], [upto_names_eq_term],
  [destArity_alpha].

  ** Same names

  Base has two [wf_local_alpha]: [PCUICSpine.wf_local_alpha] (over [eq_context_upto_names]) and
  [PCUICAlpha.wf_local_alpha] (over [≡Γ]). Their twins are [PCUICSpineEta.wf_local_alphaE]
  (copy 15) and [PCUICAlphaEta.wf_local_alphaE] (here); wherever both are in scope, write them
  qualified (cross-lane-commitments.md C6). [isType_is_open_termE] and [weaken_wf_localE] each
  have two declaration sites on the tree; they are written qualified here.

  ** Proof routes that differ from base (statements do not)

  - α-equal terms are related by [JoinE] with no scoping: [canon] erases every difference that
    α-equality allows ([eq_term_upto_names_upto_domain_r], then [upto_domain_r_canon]), and
    [JoinE_canon_eq] relates terms with equal [canon]. This gives [upto_names_conv_contextE];
    base builds [conv_context cumulAlgo_gen] by [compare_context_cumul_pb_context]. The fixpoint
    case of [typing_alpha_propE] uses it on [Γ ,,, fix_context mfix ≡Γ Γ ,,, fix_context mfix']
    where base goes through [eq_context Σ Σ] and [eq_context_upto_univ_conv_context].
  - [eq_context_upto_conv_context_relE]: base turns each α-equal pair into [ws_cumul_pb] by
    [ws_cumul_pb_compare]; here [upto_names_JoinE] and [into_ws_cumul_pbE] (the bridge
    [ws_cumul_pb_incl_E] would add [functional_extensionality_dep], which base's twin does not use).
  - Base's [type_Cumul'] ([PCUICTyping]) has no E twin on the tree; the local
    [type_Cumul'E] restates it over [typingE] (from [typeE_Cumul], as base's from
    [type_Cumul]).
  - The cumulativity case: base turns the [cumulSpec] premise into [ws_cumul_pb] with
    [PCUICInversion.into_ws_cumul] and moves it by [ws_cumul_pb_ws_cumul_ctx]; here
    [into_ws_cumul_pbE_spec] with the scoping of the typings, and [ws_cumul_pbE_ws_cumul_ctx]
    (whose context relation is oriented [Γ] to [Δ], so no [symmetry]).

  ** The forecast block

  The lemmas take T1's forecast class [SRForecastCopy18] ([PCUICSREta]; its field
  [wf_case_branches_types'E]) as a section [Context]; it is imported, never redefined. The
  copy-16 facts ([validityE]'s, [on_minductive_wf_params_indices_instE], [isType_mkApps_IndE])
  come from the landed [PCUICInductivesEta] (frac/eta 0fb43f10). This file adds no class.
  [Print Assumptions] in [PCUICAlphaEtaInstances] shows the class as an argument.

  **The hypotheses are satisfiable:** [wfE Σ] by any well-formed environment ([wf_incl_E]),
  each typing premise by a concrete derivation; [PCUICAlphaEtaInstances] gives an instance of
  every lemma family. *)

From Stdlib Require Import ssreflect ssrbool CRelationClasses CMorphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICInduction
     PCUICLiftSubst PCUICTyping PCUICWeakeningConv PCUICWeakeningTyp
     PCUICCumulativity PCUICEquality PCUICClosedTyp
     PCUICConversion PCUICContextConversion PCUICContextConversionTyp
     PCUICValidity PCUICArities PCUICSpine
     PCUICInductives PCUICInductiveInversion PCUICOnFreeVars
     PCUICWellScopedCumulativity PCUICGuardCondition PCUICAlpha.
From MetaRocq.PCUIC Require Import PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
     PCUICTypingEtaNotions PCUICClosedBodies PCUICClosedTypEta PCUICWeakeningTypEta
     PCUICEtaCanon PCUICEtaI5 PCUICEtaI5A2 PCUICWellScopedCumulativityEta PCUICConversionEtaCongr
     PCUICContextConversionEta PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp
     PCUICContextConversionTypEta PCUICInversionEta PCUICSubstitutionEta PCUICContextsEta
     PCUICAritiesEta PCUICSpineEta PCUICInductivesEta PCUICValidityEta PCUICSREta.

From Equations Require Import Equations.

Implicit Types cf : checker_flags.

(** ** α-equality is erased by [canon] (syntactic) *)

(** The instances of [upto_names] are equal: with the empty environment, every global
    reference is compared by [cmp_universe_instance eq]. *)
Lemma cmp_global_instance_empty_eq pb gr napp u u' :
  cmp_global_instance empty_global_env (fun _ => eq) pb gr napp u u' -> u = u'.
Proof.
  destruct gr; cbn; apply cmp_universe_instance_eq.
Qed.

(** [upto_domain_r] ignores binder names and λ domains, so it contains α-equality. *)
Lemma eq_term_upto_names_upto_domain_r pb napp t u :
  eq_term_upto_univ_napp empty_global_env (fun _ => eq) (fun _ => eq) pb napp t u ->
  upto_domain_r t u.
Proof.
  intros e. induction t in pb, napp, u, e |- * using term_forall_list_ind; depelim e.
  all: try solve [constructor; eauto].
  - (* Evar *) constructor. eapply All_All2_impl; [exact X|exact a|]. cbn. intros x y IH h. now eapply IH.
  - (* Sort *) cbn in *. subst. constructor.
  - (* Const *) match goal with h : cmp_universe_instance _ _ _ |- _ => apply cmp_universe_instance_eq in h end.
    subst. constructor.
  - (* Ind *) match goal with h : cmp_global_instance_gen _ _ _ _ _ _ _ |- _ => apply cmp_global_instance_empty_eq in h end.
    subst. constructor.
  - (* Construct *) match goal with h : cmp_global_instance_gen _ _ _ _ _ _ _ |- _ => apply cmp_global_instance_empty_eq in h end.
    subst. constructor.
  - (* Case *) destruct X as (Hpar & _ & Hret).
    match goal with h : eq_predicate _ _ _ _ |- _ => destruct h as (epars & einst & ectx & eret) end.
    match goal with h : eq_branches _ _ _ |- _ => rename h into ebrs end.
    apply cmp_universe_instance_eq in einst.
    constructor; eauto.
    + eapply All_All2_impl; [exact Hpar|exact epars|]. cbn. intros x y IH h. now eapply IH.
    + clear -X0 ebrs. unfold eq_branches, eq_branch in ebrs.
      induction ebrs in X0 |- *; depelim X0; constructor.
      * destruct r as [Hc Hb], p as [_ HP]. split; [exact Hc|now eapply HP].
      * now apply IHebrs.
  - (* Fix *) constructor.
    match goal with h : eq_mfixpoint _ _ _ |- _ => rename h into em end.
    unfold eq_mfixpoint in em. clear -X em.
    induction em in X |- *; depelim X; constructor.
    * destruct r as (Ht & Hb & Hr & Hn), p as [HPt HPb].
      repeat split; [exact Hn|now eapply HPt|now eapply HPb|exact Hr].
    * now apply IHem.
  - (* CoFix *) constructor.
    match goal with h : eq_mfixpoint _ _ _ |- _ => rename h into em end.
    unfold eq_mfixpoint in em. clear -X em.
    induction em in X |- *; depelim X; constructor.
    * destruct r as (Ht & Hb & Hr & Hn), p as [HPt HPb].
      repeat split; [exact Hn|now eapply HPt|now eapply HPb|exact Hr].
    * now apply IHem.
  - (* Prim *) constructor.
    match goal with h : onPrims _ _ _ _ |- _ => rename h into o end.
    depelim o; try solve [constructor].
    destruct X as (HPt & HPd & HPv). constructor.
    + assumption.
    + now eapply HPd.
    + now eapply HPt.
    + eapply All_All2_impl; [exact HPv|eassumption|]. cbn. intros x y IH h. now eapply IH.
Qed.

Lemma upto_names_canon_eq t u : t ≡α u -> canon t = canon u.
Proof.
  intros e. apply upto_domain_r_canon. exact (eq_term_upto_names_upto_domain_r _ _ _ _ e).
Qed.

(** α-equal terms are joined, with no scoping and at any [pb]. *)
Lemma upto_names_JoinE {cf} (Σ : global_env_ext) Γ pb t u : t ≡α u -> JoinE Σ Γ pb t u.
Proof.
  intros e. apply JoinE_canon_eq. exact (upto_names_canon_eq t u e).
Qed.

(** Base [type_Cumul'] ([PCUICTyping.v:679]) over [typingE]; a proof device of this file. *)
Local Lemma type_Cumul'E {cf} {Σ Γ t} T {T'} :
  Σ ;;; Γ |-E t : T ->
  isTypeE Σ Γ T' ->
  cumulSpecE Σ Γ T T' ->
  Σ ;;; Γ |-E t : T'.
Proof.
  intros Ht (_ & s & Hs & _) cum.
  eapply typeE_Cumul; eauto.
Qed.

Section AlphaEta.

(* FORECAST-ONLY: T1's class ([PCUICSREta], copy 18b); delete it when its copy lands. *)
Context {F18 : SRForecastCopy18}.

(** The E counterparts of base's [typing]-specific [pcuic] hints ([PCUICTyping.has_sort_isType],
    [typing_wf_local]), as in [PCUICSREta]. *)
#[local] Hint Resolve has_sort_isTypeE typingE_wf_local : pcuic.

Section Alpha.
  Context {cf:checker_flags}.

  (** Base [upto_names_mfix_on_ind] ([PCUICAlpha.v:94]). *)
  Lemma upto_names_mfix_on_indE {Σ : global_env_ext} {wfΣ : wfE Σ} Γ check ok mfix mfix' :
    (forall d d' ty, rarg d = rarg d' -> check (def_with_type d ty) = check (def_with_type d' ty)) ->
    is_closed_context Γ -> All (fun d => is_open_term Γ (dtype d)) mfix ->
    eq_mfixpoint upto_names' mfix mfix' ->
    mfix_on_ind check (conv_witnessE Σ Γ) ok mfix -> mfix_on_ind check (conv_witnessE Σ Γ) ok mfix'.
  Proof.
    intros hc clΓ hop eqm h.
    refine (mfix_on_ind_All2 _ (fun _ hk => hk) h).
    eapply (All2_All_mix_left hop) in eqm.
    eapply (All2_impl eqm).
    intros d d' [opd (eqty & _ & eqr & _)] m [ty [hcheck [hopty hconv]]].
    exists ty. split; [now rewrite -(hc d d' ty eqr)|].
    split; [exact hopty|].
    eapply (cumulE_Trans _ _ _ _ (dtype d)); tea.
    eapply eq_term_upto_univ_cumulSpecE, upto_names_impl_eq_term.
    now symmetry.
  Qed.

  Import PCUICClosed PCUICOnFreeVars PCUICParallelReduction PCUICConfluence.

  (** Base [PCUICAlpha]'s section-local hints ([PCUICAlpha.v:120, 128, 129]), which the copied
      proofs use; registered here locally in the same way. *)
  #[local] Hint Resolve is_closed_context_app_left : fvs.
  #[local] Hint Resolve is_closed_context_app_right : fvs.
  #[local] Hint Constructors All_Forall.All_fold : core.

  (** Base [eq_context_upto_conv_context_rel] ([PCUICAlpha.v:174]). *)
  Lemma eq_context_upto_conv_context_relE {Σ : global_env_ext} {wfΣ : wfE Σ} {le} (Γ Δ Δ' : context) :
    is_closed_context (Γ ,,, Δ) ->
    is_closed_context (Γ ,,, Δ') ->
    Δ ≡Γ Δ' ->
    ws_cumul_ctx_pbE_rel le Σ Γ Δ Δ'.
  Proof.
    intros cl cl' eq.
    split; eauto with fvs.
    eapply on_free_vars_ctx_All_fold in cl.
    eapply on_free_vars_ctx_All_fold in cl'.
    eapply All_fold_app_inv in cl as [onΓ onΔ].
    eapply All_fold_app_inv in cl' as [_ onΔ'].
    eapply All2_fold_All_fold_mix_left in eq; tea.
    eapply All2_fold_All_fold_mix_right in eq; tea.
    cbn in eq.
    eapply All2_fold_impl_ind. tea. cbn.
    intros ???? IH IH' [? [? ?]].
    apply All2_fold_prod_inv in IH as [a a'].
    apply All2_fold_prod_inv in a' as [a' a''].
    eapply All2_fold_All_left in a'.
    eapply All2_fold_All_right in a.
    eapply on_free_vars_ctx_All_fold_over in a.
    eapply on_free_vars_ctx_All_fold_over in a'.
    eapply on_free_vars_ctx_All_fold in onΓ.
    move: (on_free_vars_ctx_app xpred0 Γ Γ0).
    rewrite onΓ a' /= => iscl.
    move: (on_free_vars_ctx_app xpred0 Γ Δ0).
    rewrite onΓ a /= => iscl'.
    eapply All_decls_alpha_pb_ws_decl; tea.
    intros ? ? ? ? ? e. apply into_ws_cumul_pbE; [now apply upto_names_JoinE|..]; assumption.
    rewrite length_app (All2_fold_length IH') -length_app //.
  Qed.

  Import PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp.

  (** Base [inst_case_predicate_context_eq] ([PCUICAlpha.v:302]); its [wfE] binder is unused,
      as base's [wf] binder is. *)
  Lemma inst_case_predicate_context_eqE {Σ : global_env_ext} {wfΣ : wfE Σ} {ind mdecl idecl p} :
    wf_predicate mdecl idecl p ->
    eq_context_upto_names (ind_predicate_context ind mdecl idecl) (pcontext p) ->
    eq_context_upto_names (case_predicate_context ind mdecl idecl p) (inst_case_predicate_context p).
  Proof.
    intros wfp eq.
    rewrite /case_predicate_context /case_predicate_context_gen.
    epose proof (wf_pre_case_predicate_context_gen wfp).
    etransitivity.
    now apply eq_binder_annots_eq_ctx.
    rewrite /pre_case_predicate_context_gen /inst_case_predicate_context.
    rewrite /inst_case_context.
    eapply eq_context_upto_names_subst_context.
    now eapply eq_context_upto_names_univ_subst_preserved.
  Qed.

  (** Base [wf_local_eq_context_upto_names] ([PCUICAlpha.v:327]). *)
  Lemma wf_local_eq_context_upto_namesE {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Δ Δ'} :
    wf_localE Σ (Γ,,, Δ) ->
    eq_context_upto_names Δ' Δ ->
    wf_localE Σ (Γ ,,, Δ').
  Proof.
    intros a eq.
    induction eq; depelim a; cbn; try solve [constructor; auto];
    depelim r; subst; constructor; auto.
    all: rewrite e.
    all: apply lift_typing_impl with (1 := l) => ?? Hs.
    all: eapply (closed_context_cumulativityE _ (pb:=Conv)); tea; [apply IHeq; pcuic|].
    all: eapply ws_cumul_ctx_pbE_rel_app.
    all: eapply eq_context_upto_conv_context_relE; fvs.
    all: now eapply eq_context_upto_names_eq_context_alpha.
  Qed.

  (** Base [eq_context_conversion] ([PCUICAlpha.v:368]). *)
  Lemma eq_context_conversionE {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Δ} {t T} :
    Σ ;;; Γ |-E t : T ->
    Γ ≡Γ Δ ->
    wf_localE Σ Δ ->
    Σ ;;; Δ |-E t : T.
  Proof.
    intros.
    eapply closed_context_conversionE; tea.
    eapply typingE_wf_local in X.
    eapply (eq_context_upto_conv_context_relE []) in X0.
    eapply ws_cumul_ctx_pbE_rel_app in X0; tea.
    rewrite !app_context_nil_l in X0. exact X0.
    all:rewrite !app_context_nil_l; fvs.
  Qed.

  (** Base [upto_names_conv_context] ([PCUICAlpha.v:383]). *)
  Lemma upto_names_conv_contextE (Σ : global_env_ext) Γ Δ :
    Γ ≡Γ Δ -> conv_context (@JoinE cf) Σ Γ Δ.
  Proof.
    intro H. induction H; constructor; auto.
    match goal with h : compare_decls _ _ _ _ |- _ => destruct h end.
    all: constructor; try assumption; now apply upto_names_JoinE.
  Qed.

  (** Base [isType_eq_context_conversion] ([PCUICAlpha.v:391]). *)
  Lemma isType_eq_context_conversionE {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Δ} {T} :
    isTypeE Σ Γ T ->
    Γ ≡Γ Δ ->
    wf_localE Σ Δ ->
    isTypeE Σ Δ T.
  Proof.
    intros Hty eq wfΔ; apply lift_typing_impl with (1 := Hty); intros ?? Hs.
    now eapply eq_context_conversionE.
  Qed.

  (** Base [lift_judgment_alpha] ([PCUICAlpha.v:401]). *)
  Lemma lift_judgment_alphaE {Σ : global_env_ext} {Γ tm tm' t t' u r} :
    lift_typing0 (fun t T : term =>
      forall u : term, upto_names' t u -> Σ;;; Γ |-E u : T)
      (Judge tm t u r) ->
    match tm', tm with None, _ => unit | Some tm', Some tm => upto_names' tm tm' | _, _ => False end ->
    upto_names' t t' ->
    lift_typing typingE Σ Γ (Judge tm' t' u r).
  Proof.
    intros tu Htm Hty.
    apply lift_sorting_it_impl_gen with tu => //.
    2: intro HT; now apply HT.
    destruct tm' as [tm'|], tm as [tm|] => // HT.
    specialize (HT _ Htm).
    eapply type_Cumul'E; tea.
    { eapply lift_sorting_forget_rel, lift_sorting_forget_univ, lift_sorting_it_impl_gen with tu => // Ht. now apply Ht. }
    eapply eq_term_upto_univ_cumulSpecE.
    eapply eq_term_leq_term.
    now eapply upto_names_impl_eq_term.
  Qed.

  (** Base [typing_alpha_prop] ([PCUICAlpha.v:421]). *)
  Lemma typing_alpha_propE :
    env_propE (fun Σ Γ u A =>
      forall Δ v,
        u ≡α v ->
        Γ ≡Γ Δ ->
        Σ ;;; Δ |-E v : A)
    (fun Σ Γ j =>
      forall Δ,
      Γ ≡Γ Δ ->
      lift_typing0 (fun t T =>
        forall u, t ≡α u ->
        Σ ;;; Δ |-E u : T) j)
    (fun Σ Γ => forall Δ, Γ ≡Γ Δ -> wf_localE Σ Δ).
  Proof.
    eapply typingE_ind_env.
    1:{
      intros Σ wfΣ Γ j Hj Δ HΔ.
      apply lift_typing_impl with (1 := Hj); intros ?? [_ IH].
      intros; now apply IH.
    }
    all: intros Σ wfΣ Γ wfΓ.
    - intros _; clear wfΓ. induction 1 using All_local_env_ind1.
      * intros Δ eq; destruct Δ; depelim eq; constructor.
      * intros Δ eq; depelim eq. depelim c.
        all: constructor; auto.
        all: rewrite -eqna.
        all: eapply lift_judgment_alphaE with (1 := X _ eq) => //.

    - intros n decl hnth ih Δ v e eqctx; invs e.
      assert (isTypeE Σ Γ (lift0 (S n) (decl_type decl))).
      { eapply validityE. econstructor; eauto. }
      specialize (ih _ eqctx).
      epose proof (eq_context_upto_nth_error _ _ _ _ _ _ _ eqctx).
      erewrite hnth in X0. depelim X0.
      eapply typeE_Cumul.
      eapply typeE_Rel ; tea.
      eapply eq_context_conversionE; tea. eapply X.2.π2.1.
      depelim e. destruct p.
      eapply eq_term_upto_univ_cumulSpecE, eq_term_leq_term, eq_term_upto_univ_lift.
      eapply upto_names_impl_eq_term. now symmetry.
    - intros l ih hl Δ v e eqctx; invs e.
      specialize (ih _ eqctx).
      eapply eq_context_conversionE; tea.
      eapply typeE_Sort; assumption.
    - intros na A B s1 s2 ih hA ihA hB ihB Δ v e eqctx; invs e.
      assert (lift_typing typingE Σ Δ (j_vass_s na' a' s1)).
      + rewrite -H3.
        eapply lift_judgment_alphaE with (1 := ihA _ eqctx) => //.
      + econstructor; tas.
        eapply context_conversionE.
        * eapply ihB. assumption. reflexivity.
        * constructor; eauto.
          now eapply lift_sorting_forget_univ.
        * constructor.
          -- now eapply upto_names_conv_contextE.
          -- constructor. assumption.
             now apply upto_names_JoinE.
    - intros na A t B ih hA ihA hB ihB Δ v e eqctx; invs e.
      eapply type_Cumul'E.
      + assert (lift_typing typingE Σ Δ (j_vass na' ty')).
        * rewrite -H3.
          eapply lift_judgment_alphaE with (1 := ihA _ eqctx) => //.
        * econstructor; eauto.
          eapply eq_context_conversionE.
          -- eapply ihB. assumption. reflexivity.
          -- constructor. 1: assumption.
             simpl. constructor; auto.
          -- constructor; eauto.
      + eapply validityE in hB;tea.
        eapply isType_tProdE; eauto. split; eauto with pcuic.
        eapply lift_judgment_alphaE with (1 := ihA _ eqctx) => //. reflexivity.
        eapply validityE. eapply ihB; eauto.
        constructor; auto. constructor ; auto. reflexivity.
      + apply eq_term_upto_univ_cumulSpecE, eq_term_leq_term.
        symmetry. constructor; auto.
        all: try (eapply upto_names_impl_eq_term ; assumption).
        all: reflexivity.
    - intros na b B t A ih hbB ihbB hA ihA Δ v e eqctx; invs e.
      assert (isTypeE Σ Γ (tLetIn na b B A)).
      { eapply validityE. econstructor; eauto. }
      eapply type_Cumul'E.
      + assert (lift_typing typingE Σ Δ (j_vdef na' t' ty')).
        * rewrite -H4.
          eapply lift_judgment_alphaE with (1 := ihbB _ eqctx) => //.
        * econstructor; auto.
          eapply eq_context_conversionE.
          -- eapply ihA; trea.
          -- constructor.
            ++ assumption.
            ++ constructor; auto.
          -- constructor; auto.
      + apply lift_typing_impl with (1 := X2) => ?? Hs.
        eapply eq_context_conversionE; tea. eauto.
      + eapply eq_term_upto_univ_cumulSpecE, eq_term_leq_term.
        symmetry; constructor. assumption.
        all: try (eapply upto_names_impl_eq_term ; assumption).
        all: reflexivity.
    - intros t na A B s u ih hty ihty ht iht hu ihu Δ v e e'; invs e.
      assert (isTypeE Σ Γ (B {0 := s})).
      { eapply validityE; econstructor; eauto. }
      eapply type_Cumul'E.
      + econstructor; cycle 1.
        * eapply iht; trea.
          eapply eq_term_upto_univ_empty_impl in X; eauto.
          all:typeclasses eauto.
        * eapply ihu; trea.
        * eapply ihty. reflexivity. auto.
      + apply lift_typing_impl with (1 := X1) => ?? Hs. eapply eq_context_conversionE; tea. eauto.
      + eapply eq_term_upto_univ_cumulSpecE, eq_term_leq_term.
        symmetry.
        eapply upto_names_impl_eq_term.
        eapply eq_term_upto_univ_subst ; now auto.
    - intros cst u decl ? ? hdecl hcons Δ v e e'; invs e.
      eapply cmp_universe_instance_eq in H2. subst.
      constructor; eauto.
    - intros ind u mdecl idecl isdecl ? ? hcons Δ v e e'; invs e.
      eapply cmp_universe_instance_eq in H2. subst.
      econstructor ; eauto.
    - intros ind i u mdecl idecl cdecl isdecl ? ? ? Δ v e e'; invs e.
      eapply cmp_universe_instance_eq in H4. subst.
      econstructor ; eauto.
    - intros ind p c brs args ps mdecl idecl isdecl X X0 H Hpctx cpc wfp
        cup wfpctx Hret IHret
            wfcpc kelim Her HIHctxi Hc IHc iscof ptm wfbrs Hbrs Δ v e e'; invs e.
      have eqp := X1.
      eassert (ctx_instE _ _ _ _) as Hctxi by now eapply ctx_inst_impl with (1 := HIHctxi).
      eassert (PCUICEnvTyping.ctx_inst _ _ _ _) as IHctxi.
      { eapply ctx_inst_impl with (1 := HIHctxi). intros ? ? [? r]. pattern Γ, t, T in r. exact r. }
      destruct X1 as [eqpars [eqinst [eqctx eqret]]].
      assert (iscof' : (isCoFinite (ind_finite mdecl) ==>
        on_free_vars (strengthenP 0 1 xpredT) (preturn p')) = true).
      { apply/implyP => hcof. move/implyP: iscof => /(_ hcof) h.
        eapply PCUICConfluence.eq_term_upto_univ_napp_on_free_vars; tea. }
      assert (wf_predicate mdecl idecl p').
      { destruct wfp. split; auto.
        { now rewrite <-(All2_length eqpars). }
        eapply Forall2_All2 in H1. eapply All2_Forall2.
        eapply All2_sym in eqctx.
        eapply (All2_trans' (@eq_binder_annot name name)); tea.
        2:{ eapply All2_map; tea. eapply All2_impl; tea.
            simpl; intros. destruct X1; simpl; now symmetry. }
        simpl. intros x y [] []; etransitivity; tea. }
      have wfcpc' := wfcpc (Δ ,,, case_predicate_context ind mdecl idecl p').
      forward wfcpc'. { eapply eq_context_upto_cat; auto.
      apply (case_predicate_context_equiv eqp). }
      eapply cmp_universe_instance_eq in eqinst.
      assert (isTypeE Σ Δ (mkApps ptm (args ++ [c]))).
      { eapply isType_eq_context_conversionE. eapply validityE. econstructor; eauto.
        constructor; eauto. constructor; eauto.
        solve_all. eapply a0; eauto; reflexivity. all:auto. }
      eapply type_Cumul'E; tea.
      + have cu' : consistent_instance_ext Σ (ind_universes mdecl) (puinst p').
        { now rewrite -eqinst. }
        have convctx' : eq_context_upto_names (pcontext p') (ind_predicate_context ind mdecl idecl).
        { etransitivity; tea. now symmetry. }
        assert (eqp' : eq_context_upto_names (inst_case_predicate_context p')
          (case_predicate_context ind mdecl idecl p')).
        { rewrite /inst_case_predicate_context.
          rewrite /case_predicate_context /case_predicate_context_gen in wfcpc.
          symmetry. apply inst_case_predicate_context_eqE; tea. now symmetry. }
        assert (wf_localE Σ (Δ,,, inst_case_predicate_context p')).
        { eapply wf_local_eq_context_upto_namesE.
          exact wfcpc'. assumption. }
        have ty' : Σ;;; Δ,,, case_predicate_context ind mdecl idecl p' |-E preturn p' : tSort ps.
        { eapply eq_context_conversionE. eapply IHret. eauto. reflexivity. all:eauto.
          eapply eq_context_upto_cat; eauto. now eapply case_predicate_context_equiv. }
        have ctxinst' : ctx_instE Σ Δ (pparams p' ++ args)
          (List.rev
             (subst_instance (puinst p') (ind_params mdecl,,, ind_indices idecl))).
        { rewrite -eqinst.
          move: IHctxi => ctxi.
          destruct eqp.
          eapply ctx_inst_eq_contextE; tea.
          rewrite List.rev_involutive.
          * eapply PCUICWeakeningTypEta.weaken_wf_localE; tea. now eapply All_local_env_app_inv in X4 as [].
            eapply (on_minductive_wf_params_indices_instE isdecl _ cup).
          * eapply PCUICAlpha.ctx_inst_eq_context; tea. cbn; eauto.
          * eapply PCUICAlpha.ctx_inst_eq_context; tea. cbn; intros; eauto.
            now exact (X6 _ u ltac:(reflexivity) X5).
          * eapply All2_app => //. apply All2_refl => //. reflexivity. }
        have wfbrs' : wf_branches idecl brs'.
        { move/Forall2_All2: wfbrs => wf.
          apply All2_Forall2. eapply All2_trans'; tea.
          intros cdecl br br'.
          intros [wfbr [eqbrctx eqbodies]].
          rewrite /wf_branch.
          red. do 2 red in wfbr.
          eapply Forall2_All2 in wfbr. eapply All2_Forall2.
          eapply All2_map_left.
          eapply All2_map_left_inv in wfbr.
          eapply All2_trans'; tea.
          2:{ eapply All2_symP; tea. tc. }
          intros ??? [[] ?]; try constructor; simpl; auto; now transitivity na'. }
        destruct (All_local_env_app_inv X4) as [wfΔ _].
        assert (clΔ := (wf_local_closed_contextE wfΔ)).
        econstructor; tea; eauto. 2,3: constructor; tea ; eauto.
        * eapply (type_ws_cumul_pbE (pb:=Cumul)).
          eapply IHc; eauto.
          eapply has_sort_isTypeE; eapply isType_mkApps_IndE; tea.
          unshelve eapply (ctx_inst_spine_substE _ ctxinst').
          eapply PCUICWeakeningTypEta.weaken_wf_localE; tea.
          now eapply (on_minductive_wf_params_indices_instE isdecl).
          eapply ws_cumul_pbE_eq_le. rewrite -eqinst.
          eapply ws_cumul_pbE_mkApps; trea.
          eapply ws_cumul_pbE_refl => //. eauto with fvs.
          eapply wf_local_closed_contextE in wfΓ.
          eapply PCUICClosedTypEta.isType_is_open_termE in X1.
          rewrite on_free_vars_mkApps in X1. move/andP: X1 => [] _.
          rewrite forallb_app => /andP[] hargs hc.
          unfold ws_cumul_pbE_terms.
          eapply All2_app.
          2:{ eapply eq_terms_ws_cumul_pbE_terms => //.
              now eapply wf_local_closed_contextE in wfΔ. }
          eapply ctx_inst_closedE, All_app in Hctxi as []; eauto.
          eapply ctx_inst_closedE, All_app in ctxinst' as []; eauto.
          eapply eq_terms_ws_cumul_pbE_terms => //.
          rewrite (All2_fold_length e') in a, a0.
          solve_all. now eapply closedn_on_free_vars.
          solve_all. now eapply closedn_on_free_vars.
          eapply (All2_impl eqpars).
          intros. now eapply upto_names_impl_eq_term.
        * eapply All2i_All2_mix_left in Hbrs; tea.
          2:now eapply Forall2_All2 in wfbrs.
          epose proof (wf_case_branches_types'E (p:=p') ps args brs' isdecl) as a.
          forward a.
          { eapply has_sort_isTypeE; eapply isType_mkApps_IndE; tea.
            unshelve eapply (ctx_inst_spine_substE _ ctxinst').
            eapply PCUICWeakeningTypEta.weaken_wf_localE; tea.
            eapply (on_minductive_wf_params_indices_instE isdecl _ cu'). }
          specialize (a H0). cbn in a.
          forward a.
          { eapply eq_context_conversionE; tea.
            eapply eq_context_upto_cat; auto. reflexivity.
            eapply eq_context_upto_names_eq_context_alpha. now symmetry. }
          do 2 forward a by auto.
          eapply (All2i_All2_All2i_All2i Hbrs X3 a).
          intros n cdecl br br' [wfbr [wfbrctx wfbrty]].
          destruct wfbrty as (IHbrctx & (Hbbody & IHbbody) & (Hbty & IHbty)).
          intros [eqbctx eqbodies] [wfbr' wfcpars wfcparsn wfcbctx Hbr'ty].
          split; intuition auto.
          etransitivity. symmetry. exact eqbctx. assumption.
          eapply eq_context_upto_names_eq_context_alpha in eqbctx.
          assert (cbreq := case_branch_context_equiv (ind:=ind) (mdecl:=mdecl) (cdecl:=cdecl) eqp eqbctx).
          rewrite case_branch_type_fst.
          intuition auto.
          { eapply typeE_Cumul. eapply IHbbody; auto.
            eapply eq_context_upto_cat; auto. eapply Hbr'ty.
            eapply eq_term_upto_univ_cumulSpecE, eq_term_leq_term.
            rewrite /ptm /cpc. eapply case_branch_type_equiv; auto.
            now eapply case_predicate_context_equiv. }


      + apply eq_term_upto_univ_cumulSpecE, eq_term_leq_term.
        apply eq_term_mkApps; tea.
        rewrite /ptm.
        eapply eq_term_upto_univ_it_mkLambda_or_LetIn; tea; tc.
        2:eapply upto_names_impl_eq_term => //. 2:now symmetry.
        apply eq_context_upto_empty_impl.
        eapply case_predicate_context_equiv. now symmetry.
        eapply All2_app. apply All2_refl; reflexivity.
        repeat constructor. now apply upto_names_impl_eq_term.

    - intros p c u mdecl idecl cdecl pdecl isdecl args X X0 hc ihc H Δ v e e'; invs e.
      eapply type_Cumul'E.
      + econstructor. all: try eassumption.
        eapply ihc; tea.
      + eapply validityE ; eauto.
        econstructor ; eauto.
        eapply eq_context_conversionE; tea; pcuic.
      + apply eq_term_upto_univ_cumulSpecE, eq_term_leq_term.
        symmetry.
        eapply upto_names_impl_eq_term.
        eapply eq_term_upto_univ_substs ; auto; try reflexivity.
        * constructor ; auto.
          eapply All2_same.
          intro. eapply eq_term_upto_univ_refl ; auto.

    - intros mfix n decl types hguard hnth hwf hmfix ihmfix hmfixb ihmfixb wffix Δ v e e'; invs e.
      eapply All2_nth_error_Some in hnth as hnth' ; eauto.
      destruct hnth' as [decl' [hnth' hh]].
      destruct hh as (ety & eqann & ebo & era).
      assert (hwf' : wf_localE Σ (Γ ,,, fix_context mfix')).
      { apply All_mfix_wfE; auto.
        eapply (All2_All_mix_left ihmfix) in X.
        clear -X.
        induction X; constructor; simpl; auto.
        destruct r as (Hty & eqty & eqbod & eqrarg & eqann). rewrite -eqann.
        eapply lift_judgment_alphaE with (1 := Hty _ ltac:(reflexivity)) => //. }
      assert (convctx : conv_context (@JoinE cf) Σ (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix')).
      { eapply upto_names_conv_contextE.
        eapply eq_context_upto_cat. 1: reflexivity.
        change (fix_context mfix) with (fix_context_gen 0 mfix).
        change (fix_context mfix') with (fix_context_gen 0 mfix').
        generalize 0 at 2 3.
        unfold fix_context_gen.
        eapply (All2_All_mix_left ihmfix) in X.
        clear -X.
        induction X; try constructor; simpl; intros n; auto.
        destruct r as [Hty (eqty & eqbod & eqrarg & eqann)].
        eapply eq_context_upto_cat.
        + constructor; constructor; auto.
          now eapply eq_term_upto_univ_lift.
        + apply IHX. }
      assert(#|fix_context mfix| = #|fix_context mfix'|).
      { now rewrite !fix_context_length (All2_length X). }
      specialize (hwf (Δ ,,, types)) as hwfΔ.
      forward hwfΔ.
      { apply eq_context_upto_cat; auto. reflexivity. }
      specialize (hwf (Γ ,,, types)).
      forward hwf. { apply eq_context_upto_cat; auto; reflexivity. }
      eapply All_local_env_app_inv in hwfΔ as [].
      eapply eq_context_conversionE; tea.
      eapply type_Cumul'E.
      + econstructor.
        * assumption.
        * eapply (fix_guard_eq_term _ _ _ _ n); eauto.
          constructor. assumption.
        * eassumption.
        * eapply (All2_All_mix_left ihmfix) in X.
          clear -X.
          induction X; constructor; simpl; auto.
          destruct r as (Hty & eqty & eqbod & eqrarg & eqann). rewrite /on_def_type -eqann.
          eapply lift_judgment_alphaE with (1 := Hty _ ltac:(reflexivity)) => //.
        * unfold eq_mfixpoint in *. solve_all.
          rewrite /on_def_body -b.
          specialize (b1 (Γ ,,, types)) as IHb.
          forward IHb by eapply eq_context_upto_cat; reflexivity.
          eapply @lift_judgment_alphaE with (tm' := Some _) in IHb; tea.
          1: apply lift_typing_impl with (1 := IHb) => t T HT.
          2: { rewrite -H. apply eq_term_upto_univ_lift; assumption. }
          eapply context_conversionE; eauto.
        * unfold eq_mfixpoint in X.
          destruct wffix as (isl & hra & hon).
          split; [|split].
          { move: isl. clear -X. induction X; cbn; auto.
            move/andP => [] h hs. apply/andP; split; [|now apply IHX].
            destruct r as (eqty & eqbod & eqrarg & eqann).
            move: h eqbod. rewrite /Basics.compose /=.
            generalize (dbody x) (dbody y). clear => t t' isL eq.
            destruct t => //. now depelim eq. }
          { move: hra. clear -X. induction X; cbn; auto.
            move/andP => [] h hs. apply/andP; split; [|now apply IHX].
            destruct r as (eqty & eqbod & eqrarg & eqann).
            now eapply (upto_names_has_rec_arg x y). }
          refine (upto_names_mfix_on_indE (wfΣ := wfΣ) Γ check_one_fix _ mfix mfix'
            rarg_check_one_fix (wf_local_closed_contextE (wfΣ := wfΣ) wfΓ) _ X hon).
          eapply (All_impl hmfix) => d hd.
          now eapply PCUICClosedTypEta.isType_is_open_termE, isTypeRelE_isTypeE, hd.
        + eapply isTypeRelE_isTypeE. eapply All_nth_error in hmfix; tea.
        + apply eq_term_upto_univ_cumulSpecE, eq_term_leq_term, upto_names_impl_eq_term.
          now symmetry.

  - intros mfix n decl types hguard hnth hwf hmfix ihmfix hmfixb ihmfixb wffix Δ v e e'; invs e.
    eapply All2_nth_error_Some in hnth as hnth' ; eauto.
    destruct hnth' as [decl' [hnth' hh]].
    destruct hh as (ety & eqann & ebo & era).
    assert (hwf' : wf_localE Σ (Γ ,,, fix_context mfix')).
    { apply All_mfix_wfE; auto.
      eapply (All2_All_mix_left ihmfix) in X.
      clear -X.
      induction X; constructor; simpl; auto.
      destruct r as (Hty & eqty & eqbod & eqrarg & eqann). rewrite -eqann.
      eapply lift_judgment_alphaE with (1 := Hty _ ltac:(reflexivity)) => //. }
    assert (convctx : conv_context (@JoinE cf) Σ (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix')).
    { eapply upto_names_conv_contextE.
        eapply eq_context_upto_cat. 1: reflexivity.
        change (fix_context mfix) with (fix_context_gen 0 mfix).
        change (fix_context mfix') with (fix_context_gen 0 mfix').
        generalize 0 at 2 3.
        unfold fix_context_gen.
        eapply (All2_All_mix_left ihmfix) in X.
        clear -X.
        induction X; try constructor; simpl; intros n; auto.
        destruct r as [Hty (eqty & eqbod & eqrarg & eqann)].
        eapply eq_context_upto_cat.
        + constructor; constructor; auto.
          now eapply eq_term_upto_univ_lift.
        + apply IHX. }
    assert(#|fix_context mfix| = #|fix_context mfix'|).
    { now rewrite !fix_context_length (All2_length X). }
    specialize (hwf (Δ ,,, types)) as hwfΔ.
    forward hwfΔ.
    { apply eq_context_upto_cat; auto. reflexivity. }
    specialize (hwf (Γ ,,, types)).
    forward hwf. { apply eq_context_upto_cat; auto; reflexivity. }
    eapply All_local_env_app_inv in hwfΔ as [].
    eapply eq_context_conversionE; tea.
    eapply type_Cumul'E.
    + econstructor.
      * assumption.
      * eapply (cofix_guard_eq_term _ _ _ _ n); eauto.
        constructor. assumption.
      * eassumption.
      * eapply (All2_All_mix_left ihmfix) in X.
        clear -X.
        induction X; constructor; simpl; auto.
        destruct r as (Hty & eqty & eqbod & eqrarg & eqann). rewrite /on_def_type -eqann.
        eapply lift_judgment_alphaE with (1 := Hty _ ltac:(reflexivity)) => //.
      * unfold eq_mfixpoint in *. solve_all.
        rewrite /on_def_body -b.
        specialize (b1 (Γ ,,, types)) as IHb.
        forward IHb by eapply eq_context_upto_cat; reflexivity.
        eapply @lift_judgment_alphaE with (tm' := Some _) in IHb; tea.
        1: apply lift_typing_impl with (1 := IHb) => t T HT.
        2: { rewrite -H. apply eq_term_upto_univ_lift; assumption. }
        eapply context_conversionE; eauto.
      * refine (upto_names_mfix_on_indE (wfΣ := wfΣ) Γ check_one_cofix _ mfix mfix'
          (fun _ _ _ _ => eq_refl) (wf_local_closed_contextE (wfΣ := wfΣ) wfΓ) _ X wffix).
        eapply (All_impl hmfix) => d hd.
        now eapply PCUICClosedTypEta.isType_is_open_termE, isTypeRelE_isTypeE, hd.
      + eapply isTypeRelE_isTypeE. eapply All_nth_error in hmfix; tea.
      + apply eq_term_upto_univ_cumulSpecE, eq_term_leq_term, upto_names_impl_eq_term.
        now symmetry.
    - intros p prim_ty cdecl IH prim decl pinv pty ptyIH Δ v e e'.
      depelim e. depelim o. 1-3:econstructor; eauto; constructor.
      pose proof (validityE (typeE_Prim Σ Γ _ _ _ wfΓ prim decl pinv pty)) as (_ & s & Hs & _).
      eapply typeE_Cumul. econstructor; eauto.
      * depelim ptyIH. constructor; eauto. now rewrite -e. rewrite -e; eauto.
        specialize (hty _ _ e1 e'); eauto. eapply typeE_Cumul; tea. eapply hdef; eauto.
        eapply upto_names_impl_eq_term in e1.
        eapply eq_term_upto_univ_cumulSpecE.
        eapply eq_term_leq_term. eapply e1.
        solve_all.
        specialize (hty _ _ e1 e'); eauto. eapply typeE_Cumul; tea. eapply a0; eauto.
        eapply upto_names_impl_eq_term in e1.
        eapply eq_term_upto_univ_cumulSpecE.
        eapply eq_term_leq_term. eapply e1.
      * eapply eq_context_conversionE in Hs; eauto.
      * simp prim_type. eapply Universe.make'_inj in e. rewrite e.
        eapply eq_term_upto_univ_cumulSpecE.
        eapply upto_names_impl_leq_term.
        constructor. constructor. reflexivity. now symmetry.

    - intros t A B X wf ht iht har ihar hcu Δ v e e'.
      eapply (type_ws_cumul_pbE (pb:=Cumul)).
      + eapply iht; tea.
      + eapply has_sort_isTypeE.
        specialize (wf _ e'). now eapply eq_context_conversionE.
      + eapply (ws_cumul_pbE_ws_cumul_ctx (Γ := Γ)).
        * specialize (wf _ e').
          apply wf_conv_context_closedE => //.
          now apply upto_names_conv_contextE.
        * eapply into_ws_cumul_pbE_spec; [exact hcu| | |].
          -- now eapply typingE_wf_local, wf_local_closed_contextE in ht.
          -- now eapply type_is_open_termE in ht.
          -- now eapply subject_is_open_termE in har.
  Qed.

  (** Base [typing_alpha] ([PCUICAlpha.v:867]). *)
  Lemma typing_alphaE {Σ : global_env_ext} {Γ u v A} {wfΣ : wfE Σ.1} :
    Σ ;;; Γ |-E u : A ->
    u ≡' v ->
    Σ ;;; Γ |-E v : A.
  Proof.
    intros. eapply (env_propE_typing typing_alpha_propE); eauto. reflexivity.
  Qed.

  (** Base [wf_local_alpha] ([PCUICAlpha.v:940]); base [PCUICSpine] has another lemma of this
      name, whose twin is [PCUICSpineEta.wf_local_alphaE]. *)
  Lemma wf_local_alphaE {Σ} {wfΣ : wfE Σ.1} {Γ Γ'} :
    wf_localE Σ Γ -> Γ ≡Γ Γ' -> wf_localE Σ Γ'.
  Proof.
    intros; eapply (env_propE_wf_local typing_alpha_propE); tea.
  Qed.

  (** Base [isType_alpha] ([PCUICAlpha.v:946]). *)
  Lemma isType_alphaE {Σ} {wfΣ : wfE Σ.1} Γ u v :
    isTypeE Σ Γ u ->
    u ≡α v ->
    isTypeE Σ Γ v.
  Proof.
    intros Hty eq.
    apply lift_sorting_it_impl_gen with Hty => // Hs.
    eapply typing_alphaE; eauto.
  Qed.

  (** Base [isType_alpha_ctx] ([PCUICAlpha.v:956]). *)
  Lemma isType_alpha_ctxE {Σ} {wfΣ : wfE Σ.1} {Γ Δ u v} :
    isTypeE Σ Γ u ->
    Γ ≡Γ Δ ->
    u ≡α v ->
    isTypeE Σ Δ v.
  Proof.
    intros Hty eqctx eqtm.
    apply lift_sorting_it_impl_gen with Hty => // Hs.
    eapply typing_alpha_propE; eauto.
  Qed.

  (** Base [isWfArity_alpha] ([PCUICAlpha.v:967]). *)
  Lemma isWfArity_alphaE {Σ} {wfΣ : wfE Σ.1} {Γ u v} :
    isWfArityE Σ Γ u ->
    u ≡α v ->
    isWfArityE Σ Γ v.
  Proof.
    intros [isTy [ctx [s X1]]] e.
    eapply destArity_alpha in X1; tea.
    split; [eapply isType_alphaE; eauto|].
    destruct X1 as [ctx' [X1 X1']].
    exists ctx', s; auto.
  Qed.

End Alpha.

End AlphaEta.
