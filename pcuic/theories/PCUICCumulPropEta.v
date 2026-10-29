(* Distributed under the terms of the MIT license. *)

(** * The E copy of [PCUICCumulProp] (row T6): [cumul_prop] over the η relation

  HEADER (the full register is at the end of this comment).

  Base [PCUICCumulProp] defines [cumul_prop] ([Σ ;;; Γ |- t ~~ u]), the closure of [red1]
  and [eq_term_prop] (conversion up to universe levels within a sort family), and proves
  that two well-typed terms related by [compare_term] have [cumul_prop]-related types
  ([typing_leq_term_prop]). This file states the same facts over [typingE], [wfE],
  [wf_extE], [wf_localE], [ws_cumul_pbE] and the E twin [cumul_propE]
  ([Σ ;;; Γ |-E t ~~ u]) of [cumul_prop]. Each E lemma takes the suffix [E].

  ** Why an E twin of [cumul_prop] is needed

  With base [cumul_prop] kept as the target relation, two E forms are FALSE, with typable
  witnesses ([PCUICCumulPropEtaRefutations]): [cumul_pb_cumul_prop_baseE_false]
  ([λx:Prop. f x] and [f] are related by [ws_cumul_pbE] but not by [cumul_prop]) and
  [typing_leq_term_prop_baseE_false] (a variable typed at [G F] and at [G (λy:Prop. F y)]).
  They are the counterexamples to the absence of the η rule in [cumul_propE].

  ** The definition chosen

  [cumul_propE Σ Γ t u] is a record like [ws_cumul_pbE]: [Γ] closed, [t] and [u] open in
  [Γ], and the join [JoinPropE Σ Γ t u], which is [JoinE]'s shape (two [(R_c ∪ eta1)*]
  chains from the canonical forms, [PCUICEtaI5]) ending in [eq_term_prop_finst], i.e.
  [eq_term_upto_univ_eta_napp Σ.1 (fun _ _ _ => True) (fun _ => eq_univ_prop) Conv 0]
  ([PCUICEtaFInst]) in place of [compare_term_eta]. Why this one: the canonical-join
  machinery of I5/A6/A7 is generic in the final comparison, so transitivity is
  [I5_join_trans]'s proof ([JoinPropE_trans], from the generic C1c lemmas), the
  inversions are A6's chain lemmas ([chain_Sort], [chain_Prod], [chain_mkApps_Ind]), and
  every closure property (substitution, context conversion, the congruences) comes from
  the SANDWICH form [cumul_propE_sandwich]: [t =E v ≈ v' =E u] with [≈] the final
  comparison, so each one is the [ws_cumul_pbE] lemma of A7/A8/the congruences plus a
  syntactic fact about [≈]. A closure-style definition (base's inductive plus η rules)
  would make transitivity and the inversions need exactly this join anyway.

  ** Register, against base [PCUICCumulProp.v] (line numbers of base)

  - Twins (base statement with the relation changed, nothing else): [cumul_sort_confluenceE]
    (:28; untyped proof, no added premise: [ws_cumul_pbE_Sort_r_inv] twice and
    [canon_beta_eta_confluence]), [is_propositional_bottomE] (:86), [is_prop_bottomE]
    (:99), [is_sprop_bottomE] (:112), [prop_sort_eqE] (:124), [sprop_sort_eqE] (:134),
    [cumul_propE] (:189, definition), [cumul_pb_cumul_propE] (:238), [cumul_prop_sortE]
    (:278), [cumul_prop_propsE] (:289), [cumul_sprop_propsE] (:298), [cumul_prop_symE]
    (:431), [cumul_prop_transE] (:443), [cumul_prop_transitiveE] (:464, instance),
    [cumul_prop_cumul_pb_lE] (:467), [cumul_prop_cum_pb_rE] (:478),
    [cumul_prop_prod_invE] (:578), [substitution_untyped_cumul_propE] (:593),
    [substitution_cumul_propE] (:610), [substitution_untyped_cumul_prop_equivE] (:621),
    [red_conv_propE] (:663), [substitution_red_terms_conv_propE] (:671),
    [context_conversion_cumul_propE] (:683), [substitution_untyped_cumul_prop_cumulE]
    (:713), [substitution1_untyped_cumul_propE] (:742), [cmp_True_subst_instanceE]
    (:753), [cumul_prop_subst_instanceE] (:764), [cmp_True_instanceE] (:806),
    [cumul_prop_tProdE] (:840), [cumul_prop_tLetInE] (:863), [cumul_prop_mkAppsE] (:892),
    [red_cumul_propE] (:915), [eq_term_prop_mkApps_invE] (:922),
    [cumul_prop_mkApps_Ind_invE] (:940), [cumul_prop_sym'E] (:959, instance),
    [cumul_prop_is_openE] (:970), [typing_leq_term_prop_genE] (:987),
    [typing_leq_term_propE] (:1243).
  - Imported, E counterpart already landed elsewhere (not redefined):
    [conv_sort_invE] (:144; [PCUICEtaA6More.v:96]) and [ws_cumul_pbE_LetIn_l_inv_alt]
    (:71; [PCUICEtaA6More.v:175]). Both are STRONGER than the base-substituted form:
    [conv_sort_invE] has no environment premise (base: [wf Σ]); the LetIn lemma takes
    [ClosedBodies Σ] for [wf Σ] and drops base's [wf_local] premise. Compiled-form
    comparison: [PCUICCumulPropEtaInstances] ([cpE_import_conv_sort_inv],
    [cpE_import_LetIn_l_inv_alt]): each landed lemma inhabits the base-substituted
    type; the converse ascription does not hold (the landed type has fewer premises).
  - Imported from base, syntactic (no typing, no conversion, no E relation): [is_prop_superE]
    (:155, a BASE name), [is_sprop_superE], [is_prop_prod], [is_sprop_prod], [eq_univ_prop],
    [eq_term_prop], [eq_term_prop_impl], [subrelation_compare_sort_eq_prop] (global
    instance), [eq_term_eq_term_prop_impl], the [eq_univ_prop]/[True] instances (:307-350),
    the [LevelExprSet] lemmas (:352-413), [conv_decls_prop], [conv_ctx_prop] and its lemmas,
    [red1_upto_conv_ctx_prop], [closed_red1_upto_conv_ctx_prop], [red_upto_conv_ctx_prop],
    [closed_red_upto_conv_ctx_prop], [is_closed_context_snoc_inv], [untyped_subslet_inds],
    [is_closed_context_weaken], the notations [eq_term_napp]/[leq_term_napp].
  - Replaced: [cumul_prop_alt] (:248) is definitional for [cumul_propE] (the record's
    fields); its right-to-left half is [into_cumul_propE_red]; its left-to-right half is
    FALSE over η ([cumul_prop_altE_false]).
  - FALSE over η, not copied, refuted ([PCUICCumulPropEtaRefutations]): [cumul_prop_args]
    (:639, reducts compared by [eq_term_prop]: [cumul_prop_argsE_false]); its two consumers
    go through [cumul_propE_terms_sandwich] instead.
  - DROPPED (no caller anywhere, no named future consumer; DROP rule of
    [lanes/eta/meta/t8-consumers.md] §7): [cumul_ind_confluence] (:45). Its untyped E form,
    and the form with [A] merely well-typed, are FALSE ([cumul_ind_confluenceE_false],
    [cumul_ind_confluenceE_typed_false], witness [λx:Set. I@{a} x] of
    [PCUICEtaIndInvRefutations]); the form with [isTypeE Σ Γ A] is not refuted.
    Remove-and-build: this file builds without it (it never contained it).
  - DROPPED: [typing_cumul_term_prop] (:1255). No E consumer: its only base consumer is
    [PCUICElimination.v:747], and [PCUICElimination] stays base, off the checker path
    ([lanes/eta/t0-plan.md] §3 row 19). The E statement (premise [t' ≤sE[pb] t]) is believed
    TRUE and is NOT refuted. Base's route (common reducts compared by [compare_term], typed
    by subject reduction, then [typing_leq_term_prop]) does not exist over η: the E premise
    gives only a canonical join, [canon] changes λ domains, and η-reducts need not be typed
    ([PCUICEtaT8Probe.v:64-67]). A proof needs a NEW η-aware metatheorem: "for typed
    [t1 : T] and [t1' : T'] whose canonical forms are related by η steps and the final
    comparison, [T ~~E T']" (an induction with η cases and typed strengthening), after η
    postponement. Remove-and-build: this file builds without it.

  ** Statement changes: none. Every twin restates base with the relation changed; an
  environment binder of base stays a binder ([wf] → [wfE], [wf_ext] → [wf_extE]), also where
  the E proof does not use it. [typing_leq_term_prop_genE] and [typing_leq_term_propE] take
  the forecast class [ValForecastCopy16] ([PCUICValidityEta], imported, not redefined) as a
  section premise: the Proj case reads the consistency of the two instances from
  [isType_mkApps_Ind_invE] and [validityE] as base does from [isType_mkApps_Ind_inv] and
  [validity] (copy 16 not landed).

  ** Routes that differ from base (availability; statements unchanged)
  - Construct case: the closedness of the arities context comes from the landed
    [wf_arities_contextE] (copy 10) instead of copy 16's [wf_arities_context_inst]; the
    closedness of the constructor type is base [declared_constructor_closed_gen_type]'s
    proof over [declared_inductive_closed_constructorsE] (that lemma has no landed E copy).
  - Proj case: as in [BDFromPCUICEta], the projection context's closedness and the untyped
    substitution [c :: rev args] come from [BDFromPCUICEta.is_closed_projection_contextE] and
    [BDFromPCUICEta.untyped_subslet_projection_contextE] instead of copy 16's
    [wf_projection_context] and [projection_subslet]; the typed [substitution_cumul_prop]
    becomes [substitution_untyped_cumul_propE] with the scoping read off the typing.

  **The hypotheses are satisfiable:** [wfE Σ]/[wf_extE Σ] by any well-formed environment
  ([wf_incl_E], [wf_ext_incl_E]); every [cumul_propE] and [ws_cumul_pbE] premise by
  reflexivity or by the η pair [λx:Prop. f x], [f]; [ValForecastCopy16] is a forecast class
  (copy 16), a premise, never an axiom. Instances, each non-degenerate:
  [PCUICCumulPropEtaInstances]. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Universes.
From MetaRocq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils PCUICTactics PCUICLiftSubst PCUICInduction
     PCUICInductives PCUICGlobalEnv PCUICEquality PCUICReduction PCUICOnFreeVars
     PCUICWellScopedCumulativity PCUICConversion PCUICContextConversion PCUICSubstitution
     PCUICUnivSubst PCUICUnivSubstitutionConv PCUICCumulativity PCUICConfluence PCUICCumulProp.
From MetaRocq.PCUIC Require Import PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICTypingEta
     PCUICTypingEtaInd PCUICTypingEtaNotions PCUICClosedBodies PCUICEtaDefs PCUICEtaScope
     PCUICEtaCanon PCUICEtaCanonRed PCUICEtaCanonC4 PCUICEtaC1b PCUICEtaFInst PCUICEtaFInstEquiv
     PCUICEtaFInstC1c PCUICEtaFInstFlip PCUICEtaFInstEtaC1c PCUICEtaFInstGlue PCUICEtaFInstTransport
     PCUICEtaI5 PCUICEtaI5Trans PCUICEtaI5A2 PCUICWellScopedCumulativityEta PCUICConversionEtaCongr
     PCUICWsCumulEtaSubst PCUICEtaA6 PCUICEtaA6Ind PCUICEtaA6More PCUICContextConversionEta
     PCUICInversionEta PCUICSubstitutionEta PCUICSpineEta PCUICWsCumulEtaCtx PCUICValidityEta.
From MetaRocq.PCUIC.Typing Require Import PCUICClosedTypEta PCUICContextConversionTypEta.
From MetaRocq.PCUIC Require PCUICGenerationEta.
From MetaRocq.PCUIC.Bidirectional Require BDFromPCUICEta.

From Equations.Type Require Import Relation Relation_Properties.
Require Equations.Prop.DepElim.
From Equations Require Import Equations.
From Stdlib Require Import ssreflect.

Implicit Types (Σ : global_env_ext).

(** ** The final comparison of a [cumul_propE] join

  Base [eq_term_prop] with F-inst's instance comparison ([eq_term_upto_univ_eta_napp]). *)

Notation eq_term_prop_finst Σ napp :=
  (eq_term_upto_univ_eta_napp Σ (fun _ _ _ => True) (fun _ => eq_univ_prop) Conv napp).

(** ** Generic facts about [eq_term_upto_univ_eta_napp] (new statements, no base twin) *)

(** Changing the comparisons, by two flips ([finst_flip]). *)
Lemma finst_impl (Σ : global_env) cu cu' cs cs' pb pb' napp t u :
  RelationClasses.subrelation (cu Conv) (cu' Conv) ->
  RelationClasses.subrelation (cu pb) (cu' pb') ->
  RelationClasses.subrelation (cs Conv) (cs' Conv) ->
  RelationClasses.subrelation (cs pb) (cs' pb') ->
  eq_term_upto_univ_eta_napp Σ cu cs pb napp t u ->
  eq_term_upto_univ_eta_napp Σ cu' cs' pb' napp t u.
Proof.
  intros h1 h2 h3 h4 e.
  apply (finst_flip Σ (fun pb => CRelationClasses.flip (cu' pb)) cu'
           (fun pb => CRelationClasses.flip (cs' pb)) cs' pb' pb' napp u t);
    try (intros x y h; exact h).
  exact (finst_flip Σ cu (fun pb => CRelationClasses.flip (cu' pb)) cs
           (fun pb => CRelationClasses.flip (cs' pb)) pb pb' napp t u h1 h2 h3 h4 e).
Qed.

(** Base's comparison is included in F-inst's, for every pair of comparisons
    ([cumul_ind_finst], [cumul_construct_finst] at the two heads that read [napp]). *)
Lemma finst_of_eq_term_upto_univ (Σ : global_env) cu cs pb napp t u :
  eq_term_upto_univ_napp Σ cu cs pb napp t u -> eq_term_upto_univ_eta_napp Σ cu cs pb napp t u.
Proof.
  induction t in pb, napp, u |- * using term_forall_list_ind;
    try (inversion 1; subst; constructor; eauto; fail).
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea. eapply All_impl; eauto.
  - inversion 1; subst; constructor. now apply cumul_ind_finst.
  - inversion 1; subst; constructor. now apply cumul_construct_finst.
  - inversion 1; subst; constructor; unfold eq_predicate, eq_branches, eq_branch in *; eauto; solve_all.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea. eapply All_impl; eauto.
    cbn. intros x [? ?] y (?&?&?&?). repeat split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea. eapply All_impl; eauto.
    cbn. intros x [? ?] y (?&?&?&?). repeat split; eauto.
  - intros h; depelim h. depelim o; constructor; cbn in X; constructor; intuition eauto.
    solve_all.
Qed.

(** ** The comparison relations of [eq_term_prop_finst] *)

Section PropComparison.

  Context {cf : checker_flags}.

  Lemma cpP_pre_u : RelationClasses.PreOrder (fun _ _ : Universe.t => True).
  Proof. split; [intros ?; exact I|intros ??? _ _; exact I]. Qed.

  Lemma cpP_pre_s : RelationClasses.PreOrder (fun u v : sort => is_true (@eq_univ_prop cf u v)).
  Proof. split; [exact refl_eq_univ_prop|exact trans_eq_univ_prop]. Qed.

  Lemma cpP_su_u : SubstUnivPreserving (fun _ _ : Universe.t => True) (fun _ _ : Universe.t => True).
  Proof. intros ????; exact I. Qed.

  Lemma cpP_su_s : SubstUnivPreserving (fun _ _ : Universe.t => True)
                     (fun u v : sort => is_true (@eq_univ_prop cf u v)).
  Proof. exact substu_True_eq_univ_prop. Qed.

  (** Reflexivity, symmetry and transitivity ([PCUICEtaFInstEquiv]). *)
  Lemma finstP_refl (Σ : global_env) napp t : eq_term_prop_finst Σ napp t t.
  Proof.
    apply eq_term_upto_univ_eta_refl; try (intros ?; exact I); exact refl_eq_univ_prop.
  Qed.

  Lemma finstP_sym (Σ : global_env) napp t u : eq_term_prop_finst Σ napp t u -> eq_term_prop_finst Σ napp u t.
  Proof.
    apply eq_term_upto_univ_eta_sym; try (intros ?? _; exact I); exact sym_eq_univ_prop.
  Qed.

  Lemma finstP_trans (Σ : global_env) napp t u v :
    eq_term_prop_finst Σ napp t u -> eq_term_prop_finst Σ napp u v -> eq_term_prop_finst Σ napp t v.
  Proof.
    apply eq_term_upto_univ_eta_trans;
      try (intros ?? h; exact h); try (intros ??? _ _; exact I); exact trans_eq_univ_prop.
  Qed.

  (** [canon] preserves it ([finst_canon]). *)
  Lemma finstP_canon (Σ : global_env) napp t u :
    eq_term_prop_finst Σ napp t u -> eq_term_prop_finst Σ napp (canon t) (canon u).
  Proof. exact (finst_canon Σ _ _ refl_eq_univ_prop Conv napp t u). Qed.

  (** Base [eq_term_prop] is included. *)
  Lemma finstP_of_eq_term_prop (Σ : global_env) napp t u : eq_term_prop Σ napp t u -> eq_term_prop_finst Σ napp t u.
  Proof. exact (finst_of_eq_term_upto_univ Σ _ _ Conv napp t u). Qed.

  (** The real comparison is included, at any [pb]. *)
  Lemma finstP_of_compare {Σ : global_env_ext} pb napp t u :
    eq_term_upto_univ_eta_napp Σ.1 (compare_universe Σ) (compare_sort Σ) pb napp t u ->
    eq_term_prop_finst Σ.1 napp t u.
  Proof.
    apply finst_impl; try (intros ?? _; exact I).
    all: apply subrelation_compare_sort_eq_prop.
  Qed.

  (** Monotone in [napp] ([finst_napp_mono]). *)
  Lemma finstP_napp_mono (Σ : global_env) n m t u :
    eq_term_prop_finst Σ n t u -> n <= m -> eq_term_prop_finst Σ m t u.
  Proof. intros e h. exact (finst_napp_mono Σ _ _ Conv n m t u (fun x y h => h) e h). Qed.

  (** Free variables ([finst_on_free_vars]). *)
  Lemma finstP_on_free_vars (Σ : global_env) P n t u :
    eq_term_prop_finst Σ n t u -> on_free_vars P t -> on_free_vars P u.
  Proof. exact (finst_on_free_vars Σ _ _ P n t u). Qed.

  (** Substitution, by the transport to base at [Conv] ([finst_Conv_base]) and base
      [eq_term_upto_univ_substs]. *)
  Lemma finstP_substs (Σ : global_env) napp t u n l l' :
    eq_term_prop_finst Σ napp t u -> All2 (eq_term_prop_finst Σ 0) l l' ->
    eq_term_prop_finst Σ napp (subst l n t) (subst l' n u).
  Proof.
    intros e hl. apply finst_Conv_of_base.
    apply eq_term_upto_univ_substs; try (intros ?? h; exact h).
    - exact (finst_Conv_to_base _ _ _ _ _ _ e).
    - eapply All2_impl; [exact hl|]. intros x y h. exact (finst_Conv_to_base _ _ _ _ _ _ h).
  Qed.

  (** Spines. *)
  Lemma finstP_mkApps (Σ : global_env) n f f' l l' :
    eq_term_prop_finst Σ (#|l| + n) f f' -> All2 (eq_term_prop_finst Σ 0) l l' ->
    eq_term_prop_finst Σ n (mkApps f l) (mkApps f' l').
  Proof.
    intros e hl. induction hl as [|a a' l l' ha _ IH] in f, f', n, e |- *; cbn in *; [exact e|].
    apply IH. constructor; [|exact ha].
    now replace (S (#|l| + n)) with (S #|l| + n) by lia.
  Qed.

  Lemma finstP_tApp_l (Σ : global_env) n f a v : eq_term_prop_finst Σ n (tApp f a) v ->
    ∑ f' a', [× v = tApp f' a', eq_term_prop_finst Σ (S n) f f' & eq_term_prop_finst Σ 0 a a'].
  Proof. intros e. depelim e. do 2 eexists; split; [reflexivity|eassumption|eassumption]. Qed.

  Lemma finstP_mkApps_Ind_l (Σ : global_env) n ind u l v : eq_term_prop_finst Σ n (mkApps (tInd ind u) l) v ->
    ∑ u' l', (v = mkApps (tInd ind u') l') × All2 (eq_term_prop_finst Σ 0) l l'.
  Proof.
    revert n v. induction l as [|a l IH] using rev_ind; intros n v e.
    - cbn in e. depelim e. eexists _, []. split; [reflexivity|constructor].
    - rewrite mkApps_app in e. cbn in e.
      destruct (finstP_tApp_l _ _ _ _ _ e) as (f' & a' & [-> ef ea]).
      destruct (IH _ _ ef) as (u' & l' & [-> hl]).
      exists u', (l' ++ [a']). split.
      + now rewrite mkApps_app.
      + apply All2_app; [exact hl|constructor; [exact ea|constructor]].
  Qed.

  Lemma finstP_Prod_inv (Σ : global_env) n na A B na' A' B' :
    eq_term_prop_finst Σ n (tProd na A B) (tProd na' A' B') -> eq_term_prop_finst Σ 0 B B'.
  Proof. intros e. depelim e. assumption. Qed.

  Lemma finstP_Sort_inv (Σ : global_env) n s s' :
    eq_term_prop_finst Σ n (tSort s) (tSort s') -> eq_univ_prop s s'.
  Proof. intros e. depelim e. assumption. Qed.

End PropComparison.

(** ** [cumul_propE] *)

Definition JoinPropE {cf : checker_flags} (Σ : global_env_ext) (Γ : context) (t u : term) : Type :=
  ∑ v v', clos_refl_trans (union (R_c Σ Γ) eta1) (canon t) v ×
          clos_refl_trans (union (R_c Σ Γ) eta1) (canon u) v' ×
          eq_term_prop_finst Σ.1 0 v v'.

(** The E twin of base [cumul_prop] ([PCUICCumulProp.v:189]). Base's inductive sits in its
    section and binds [checker_flags] twice; this one binds it once. *)
Record cumul_propE {cf : checker_flags} (Σ : global_env_ext) (Γ : context) (t u : term) : Type :=
  { cpE_ctx : is_closed_context Γ;
    cpE_left : is_open_term Γ t;
    cpE_right : is_open_term Γ u;
    cpE_join : JoinPropE Σ Γ t u }.

Arguments cpE_ctx {cf Σ Γ t u}.
Arguments cpE_left {cf Σ Γ t u}.
Arguments cpE_right {cf Σ Γ t u}.
Arguments cpE_join {cf Σ Γ t u}.

Notation " Σ ;;; Γ |-E t ~~ u " := (cumul_propE Σ Γ t u) (at level 50, Γ, t, u at next level) : type_scope.

#[local] Hint Resolve cpE_ctx cpE_left cpE_right : fvs.

(** ** Joins that need no environment premise *)

Section JoinsNoEnv.

  Context {cf : checker_flags} (Σ : global_env_ext).

  Local Notation RE Γ := (union (R_c Σ Γ) eta1).
  Local Notation BE Γ := (clos_refl_trans (be_step Σ Γ)).
  Local Notation RFP n := (eq_term_prop_finst Σ.1 n).

  Lemma JoinPropE_sym Γ t u : JoinPropE Σ Γ t u -> JoinPropE Σ Γ u t.
  Proof.
    intros (v & v' & hv & hv' & e). exists v', v. repeat split; [exact hv'|exact hv|].
    exact (finstP_sym _ _ _ _ e).
  Qed.

  Lemma JoinPropE_of_JoinE Γ pb t u : JoinE Σ Γ pb t u -> JoinPropE Σ Γ t u.
  Proof.
    intros (v & v' & hv & hv' & e). exists v, v'. repeat split; [exact hv|exact hv'|].
    exact (finstP_of_compare pb 0 v v' e).
  Qed.

  Lemma BE_JoinPropE Γ t u v v' :
    BE Γ t v -> BE Γ u v' -> RFP 0 (canon v) (canon v') -> JoinPropE Σ Γ t u.
  Proof.
    intros hv hv' e. exists (canon v), (canon v').
    repeat split; [exact (BE_RE Σ Γ _ _ hv)|exact (BE_RE Σ Γ _ _ hv')|exact e].
  Qed.

  Lemma JoinPropE_of_finst Γ t u : RFP 0 t u -> JoinPropE Σ Γ t u.
  Proof.
    intros e. exists (canon t), (canon u). repeat split; [apply rt_refl|apply rt_refl|].
    exact (finstP_canon _ _ _ _ e).
  Qed.

End JoinsNoEnv.

(** ** Transitivity: [I5_join_trans]'s proof at the comparison [eq_term_prop_finst] *)

Section JoinsTrans.

  Context {cf : checker_flags} (Σ : global_env_ext) (wfΣ : ClosedBodies Σ).

  Local Notation RE Γ := (union (R_c Σ Γ) eta1).
  Local Notation RFP n := (eq_term_prop_finst Σ.1 n).

  Lemma cpP_step_l Γ a b a' :
    is_open_term Γ a -> RE Γ a b -> RFP 0 a a' -> ∑ b', RE Γ a' b' × RFP 0 b b'.
  Proof.
    intros ha [[b0 [hr ->]]|he] e.
    - destruct (red1_finst_l Σ.1 (fun _ _ _ => True) (fun _ => eq_univ_prop) cpP_pre_u cpP_pre_s
                  cpP_su_u cpP_su_s Σ Γ a b0 hr Conv 0 a' (fun x y h => h) (fun x y h => h) e)
        as (b0' & hr' & e').
      exists (canon b0'). split; [left; exists b0'; split; [exact hr'|reflexivity]|].
      exact (finstP_canon _ _ _ _ e').
    - destruct (eta1_finst_l Σ.1 (fun _ _ _ => True) (fun _ => eq_univ_prop) a b he _ Conv 0 a'
                  (fun x y h => h) (fun x y h => h) ha e) as (b' & he' & e').
      exists b'. split; [right; exact he'|exact e'].
  Qed.

  Lemma cpP_step_r Γ a a' b' :
    is_open_term Γ a' -> RFP 0 a a' -> RE Γ a' b' -> ∑ b, RE Γ a b × RFP 0 b b'.
  Proof.
    intros ha' e s.
    destruct (cpP_step_l Γ a' b' a ha' s (finstP_sym _ _ _ _ e)) as (b & hb & eb).
    exists b. split; [exact hb|exact (finstP_sym _ _ _ _ eb)].
  Qed.

  Lemma cpP_star_l Γ a b a' :
    is_closed_context Γ -> is_open_term Γ a ->
    clos_refl_trans (RE Γ) a b -> RFP 0 a a' ->
    ∑ b', clos_refl_trans (RE Γ) a' b' × RFP 0 b b'.
  Proof.
    intros hΓ ha h. apply clos_rt_rt1n_iff in h.
    revert a' ha. induction h as [a|a a1 b hs _ IH]; intros a' ha e.
    - exists a'. split; [apply rt_refl|exact e].
    - destruct (cpP_step_l Γ a a1 a' ha hs e) as (a1' & hs' & e1).
      destruct (IH a1' (step_open Σ wfΣ Γ a a1 hΓ ha hs) e1) as (b' & hb' & eb).
      exists b'. split; [eapply rt_trans; [apply rt_step; exact hs'|exact hb']|exact eb].
  Qed.

  Lemma cpP_star_r Γ a a' b' :
    is_closed_context Γ -> is_open_term Γ a' ->
    RFP 0 a a' -> clos_refl_trans (RE Γ) a' b' ->
    ∑ b, clos_refl_trans (RE Γ) a b × RFP 0 b b'.
  Proof.
    intros hΓ ha' e h. apply clos_rt_rt1n_iff in h.
    revert a e ha'. induction h as [a'|a' a1' b' hs _ IH]; intros a e ha'.
    - exists a. split; [apply rt_refl|exact e].
    - destruct (cpP_step_r Γ a a' a1' ha' e hs) as (a1 & hs1 & e1).
      destruct (IH a1 e1 (step_open Σ wfΣ Γ a' a1' hΓ ha' hs)) as (b & hb & eb).
      exists b. split; [eapply rt_trans; [apply rt_step; exact hs1|exact hb]|exact eb].
  Qed.

  Theorem JoinPropE_trans Γ t u w :
    is_closed_context Γ -> is_open_term Γ u ->
    JoinPropE Σ Γ t u -> JoinPropE Σ Γ u w -> JoinPropE Σ Γ t w.
  Proof.
    intros hΓ hu (v & v' & hv & hv' & e1) (x & x' & hx & hx' & e2).
    have hcu : is_open_term Γ (canon u) := canon_is_open_term Γ u hu.
    destruct (canon_beta_eta_confluence Σ wfΣ Γ (canon u) v' x hΓ hcu (canon_idem u) hv' hx)
      as (y & hy1 & hy2).
    destruct (cpP_star_r Γ v v' y hΓ (star_open Σ wfΣ Γ _ _ hΓ hcu hv') e1 hy1) as (z & hz & ez).
    destruct (cpP_star_l Γ x y x' hΓ (star_open Σ wfΣ Γ _ _ hΓ hcu hx) hy2 e2) as (z' & hz' & ez').
    exists z, z'. repeat split.
    - eapply rt_trans; [exact hv|exact hz].
    - eapply rt_trans; [exact hx'|exact hz'].
    - exact (finstP_trans _ _ _ _ _ ez ez').
  Qed.

End JoinsTrans.

(** ** The toolkit: building [cumul_propE] and the sandwich form *)

Section Toolkit.

  Context {cf : checker_flags} {Σ : global_env_ext}.

  Local Notation RFP n := (eq_term_prop_finst Σ.1 n).
  Local Notation WS pb Γ := (ws_cumul_pbE pb Σ Γ).

  Lemma cpE_of_finst {Γ t u} :
    is_closed_context Γ -> is_open_term Γ t -> is_open_term Γ u -> RFP 0 t u -> Σ ;;; Γ |-E t ~~ u.
  Proof. intros hΓ ht hu e. constructor; try assumption. exact (JoinPropE_of_finst Σ Γ t u e). Qed.

  Lemma cpE_of_eq_term_prop {Γ t u} :
    is_closed_context Γ -> is_open_term Γ t -> is_open_term Γ u -> eq_term_prop Σ.1 0 t u ->
    Σ ;;; Γ |-E t ~~ u.
  Proof. intros hΓ ht hu e. apply cpE_of_finst; try assumption. exact (finstP_of_eq_term_prop _ _ _ _ e). Qed.

  Lemma cpE_of_ws {pb Γ t u} : WS pb Γ t u -> Σ ;;; Γ |-E t ~~ u.
  Proof. intros [hΓ ht hu j]. constructor; try assumption. exact (JoinPropE_of_JoinE Σ Γ pb t u j). Qed.

  Context {wfΣ : ClosedBodies Σ}.

  Lemma cpE_sym {Γ t u} : Σ ;;; Γ |-E t ~~ u -> Σ ;;; Γ |-E u ~~ t.
  Proof. intros [hΓ ht hu j]. constructor; try assumption. exact (JoinPropE_sym Σ Γ t u j). Qed.

  Lemma cpE_trans {Γ t u w} : Σ ;;; Γ |-E t ~~ u -> Σ ;;; Γ |-E u ~~ w -> Σ ;;; Γ |-E t ~~ w.
  Proof.
    intros [hΓ ht hu j1] [_ _ hw j2]. constructor; try assumption.
    exact (JoinPropE_trans Σ wfΣ Γ t u w hΓ hu j1 j2).
  Qed.

  (** The sandwich form: [t =E v], [u =E v'], [v ≈ v']. *)
  Lemma cumul_propE_sandwich {Γ t u} : Σ ;;; Γ |-E t ~~ u ->
    ∑ v v', [× WS Conv Γ t v, WS Conv Γ u v' & RFP 0 v v'].
  Proof.
    intros [hΓ ht hu (v & v' & hv & hv' & e)].
    have hvo := star_open Σ wfΣ Γ _ _ hΓ (canon_is_open_term Γ t ht) hv.
    have hvo' := star_open Σ wfΣ Γ _ _ hΓ (canon_is_open_term Γ u hu) hv'.
    exists v, v'. split; [| |exact e].
    - constructor; [exact hΓ|exact ht|exact hvo|].
      apply (BE_JoinE Σ Γ Conv t v v v); [|apply rt_refl|apply compare_term_eta_refl].
      eapply rt_trans; [apply BE_to_canon|exact (RE_BE Σ Γ _ _ hv)].
    - constructor; [exact hΓ|exact hu|exact hvo'|].
      apply (BE_JoinE Σ Γ Conv u v' v' v'); [|apply rt_refl|apply compare_term_eta_refl].
      eapply rt_trans; [apply BE_to_canon|exact (RE_BE Σ Γ _ _ hv')].
  Qed.

  Lemma cumul_propE_of_sandwich {Γ t u v v'} :
    WS Conv Γ t v -> WS Conv Γ u v' -> RFP 0 v v' -> Σ ;;; Γ |-E t ~~ u.
  Proof.
    intros hv hv' e.
    have c1 := cpE_of_ws hv.
    have c2 : Σ ;;; Γ |-E v ~~ v' := cpE_of_finst (wsE_ctx hv) (wsE_right hv) (wsE_right hv') e.
    have c3 := cpE_sym (cpE_of_ws hv').
    exact (cpE_trans (cpE_trans c1 c2) c3).
  Qed.

  Lemma ws_terms_open_right {Γ l l'} : ws_cumul_pbE_terms Σ Γ l l' -> forallb (is_open_term Γ) l'.
  Proof.
    unfold ws_cumul_pbE_terms. induction 1 as [|x x' l l' hx _ IH]; [reflexivity|].
    cbn. rewrite (wsE_right hx). exact IH.
  Qed.

  Lemma cumul_propE_terms_sandwich {Γ l l'} : All2 (cumul_propE Σ Γ) l l' ->
    ∑ vs vs', [× ws_cumul_pbE_terms Σ Γ l vs, ws_cumul_pbE_terms Σ Γ l' vs' &
                 All2 (RFP 0) vs vs'].
  Proof.
    unfold ws_cumul_pbE_terms.
    induction 1 as [|x x' l l' hx _ IH]; [exists [], []; split; constructor|].
    destruct IH as (vs & vs' & [h1 h2 h3]).
    destruct (cumul_propE_sandwich hx) as (v & v' & [g1 g2 g3]).
    exists (v :: vs), (v' :: vs'). split; constructor; assumption.
  Qed.

  (** Two lists joined element by element, from [BE] chains. *)
  Lemma All2_cpE_zip Γ l l' l1 l1' :
    is_closed_context Γ -> forallb (is_open_term Γ) l -> forallb (is_open_term Γ) l' ->
    All2 (fun a a' => clos_refl_trans (be_step Σ Γ) a a') l l1 ->
    All2 (fun a a' => clos_refl_trans (be_step Σ Γ) a a') l' l1' ->
    All2 (RFP 0) l1 l1' -> All2 (cumul_propE Σ Γ) l l'.
  Proof.
    intros hΓ hl hl' h1 h2 e. induction e as [|a1 a1' l1 l1' ea _ IH] in l, l', hl, hl', h1, h2 |- *.
    - depelim h1; depelim h2; constructor.
    - depelim h1. depelim h2. move: hl hl' => /= /andP [ha hl] /andP [ha' hl'].
      constructor; [|eapply IH; eassumption].
      constructor; [exact hΓ|exact ha|exact ha'|].
      apply (BE_JoinPropE Σ Γ _ _ a1 a1'); [eassumption|eassumption|exact (finstP_canon _ _ _ _ ea)].
  Qed.

End Toolkit.

(** A [compare_term] pair at napp 0 is joined. *)
Lemma JoinE_of_compare_term {cf : checker_flags} (Σ : global_env_ext) Γ pb t u :
  compare_term_napp Σ Σ pb 0 t u -> JoinE Σ Γ pb t u.
Proof.
  intros e. exists (canon t), (canon u). repeat split; [apply rt_refl|apply rt_refl|].
  exact (RF_canon Σ pb 0 t u (finst_of_eq_term_upto_univ _ _ _ _ _ _ _ e)).
Qed.

(** [conv_context] over [JoinE] is reflexive (the proof of [conv_context_reflE],
    [PCUICSREta.v:576], which this file does not import). *)
Local Lemma cpE_conv_context_refl {cf : checker_flags} Σ Γ : All2_fold (conv_decls (@JoinE cf) Σ) Γ Γ.
Proof.
  induction Γ as [|[na [b|] ty] x IH]; constructor; auto; constructor; auto; apply JoinE_refl.
Qed.

(** [wf_extE] gives [wfE] (base gets [wf] from [wf_ext] by [wf_ext_wf]). *)
#[local] Instance cpE_wf_extE_wfE {cf : checker_flags} {Σ : global_env_ext} (h : wf_extE Σ) : wfE Σ.1 := h.1.

Section no_prop_leq_typeE.

Context `{cf : checker_flags}.
Variable Hcf : prop_sub_type = false.

Lemma cumul_sort_confluenceE {Σ} {wfΣ : wfE Σ} {Γ A u v} :
  Σ ;;; Γ ⊢E A ≤ tSort u ->
  Σ ;;; Γ ⊢E A ≤ tSort v ->
  ∑ v', (Σ ;;; Γ ⊢E A = tSort v') *
        (leq_sort (global_ext_constraints Σ) v' u /\
          leq_sort (global_ext_constraints Σ) v' v).
Proof using Type.
  move=> H H'.
  have hΓ := wsE_ctx H. have hA := wsE_left H.
  destruct (ws_cumul_pbE_Sort_r_inv Cumul H) as [u' [hu hcu]].
  destruct (ws_cumul_pbE_Sort_r_inv Cumul H') as [v' [hv hcv]].
  destruct (canon_beta_eta_confluence Σ (wfE_ClosedBodies Σ) Γ (canon A) _ _ hΓ
              (canon_is_open_term Γ A hA) (canon_idem A) hu hv) as [w [hw1 hw2]].
  apply chain_Sort in hw1. apply chain_Sort in hw2. subst w. noconf hw2.
  exists u'. split; [|split; [exact hcu|exact hcv]].
  constructor; [exact hΓ|exact hA|reflexivity|].
  exists (tSort u'), (tSort u'). repeat split; [exact hu|apply rt_refl|apply compare_term_eta_refl].
Qed.

Lemma is_propositional_bottomE {Σ Γ T s s'} :
  wf_extE Σ ->
  Σ ;;; Γ ⊢E T ≤ tSort s ->
  Σ ;;; Γ ⊢E T ≤ tSort s' ->
  Sort.is_propositional s -> Sort.is_propositional s'.
Proof using Hcf.
  intros wfΣ hs hs'.
  destruct (cumul_sort_confluenceE (wfΣ := wfΣ.1) hs hs') as [x' [conv [leq leq']]].
  move: leq leq'.
  destruct x', s, s' => //=.
  now rewrite Hcf.
Qed.

Lemma is_prop_bottomE {Σ Γ T s s'} :
  wf_extE Σ ->
  Σ ;;; Γ ⊢E T ≤ tSort s ->
  Σ ;;; Γ ⊢E T ≤ tSort s' ->
  Sort.is_prop s -> Sort.is_prop s'.
Proof using Hcf.
  intros wfΣ hs hs'.
  destruct (cumul_sort_confluenceE (wfΣ := wfΣ.1) hs hs') as [x' [conv [leq leq']]].
  move: leq leq'.
  destruct x', s, s' => //=.
  now rewrite Hcf.
Qed.

Lemma is_sprop_bottomE {Σ Γ T s s'} :
  wf_extE Σ ->
  Σ ;;; Γ ⊢E T ≤ tSort s ->
  Σ ;;; Γ ⊢E T ≤ tSort s' ->
  Sort.is_sprop s -> Sort.is_sprop s'.
Proof using Type.
  intros wfΣ hs hs'.
  destruct (cumul_sort_confluenceE (wfΣ := wfΣ.1) hs hs') as [x' [conv [leq leq']]].
  move: leq leq'.
  destruct x', s, s' => //=.
Qed.

Lemma prop_sort_eqE {Σ Γ u u'} : Sort.is_prop u -> Sort.is_prop u' ->
  is_closed_context Γ ->
  Σ ;;; Γ ⊢E tSort u = tSort u'.
Proof using Type.
  destruct u, u';
  move=> //_ //_ hΓ.
  constructor; [exact hΓ|reflexivity|reflexivity|].
  exists (tSort sProp), (tSort sProp). repeat split; [apply rt_refl|apply rt_refl|apply compare_term_eta_refl].
Qed.

Lemma sprop_sort_eqE {Σ Γ u u'} : Sort.is_sprop u -> Sort.is_sprop u' ->
  is_closed_context Γ ->
  Σ ;;; Γ ⊢E tSort u = tSort u'.
Proof using Type.
  destruct u, u';
  move=> //_ //_ hΓ.
  constructor; [exact hΓ|reflexivity|reflexivity|].
  exists (tSort sSProp), (tSort sSProp). repeat split; [apply rt_refl|apply rt_refl|apply compare_term_eta_refl].
Qed.

Lemma cumul_pb_cumul_propE Σ Γ pb A B :
  Σ ;;; Γ ⊢E A ≤[pb] B ->
  Σ ;;; Γ |-E A ~~ B.
Proof using Type.
  exact cpE_of_ws.
Qed.

(** The right-to-left half of base [cumul_prop_alt] ([PCUICCumulProp.v:248]); the other
    half is false with η ([cumul_prop_altE_false]). *)
Lemma into_cumul_propE_red {Σ : global_env_ext} {Γ T U} :
  (∑ nf nf', [× Σ ;;; Γ ⊢ T ⇝ nf, Σ ;;; Γ ⊢ U ⇝ nf' & eq_term_prop Σ 0 nf nf']) ->
  Σ ;;; Γ |-E T ~~ U.
Proof using Type.
  intros (nf & nf' & [r r' e]).
  constructor; [exact (clrel_ctx r)|exact (clrel_src r)|exact (clrel_src r')|].
  apply (BE_JoinPropE Σ Γ T U nf nf'); [exact (BE_red Σ Γ _ _ (clrel_rel r))|exact (BE_red Σ Γ _ _ (clrel_rel r'))|].
  apply finstP_canon. exact (finstP_of_eq_term_prop _ _ _ _ e).
Qed.

Lemma cumul_prop_sortE {Σ Γ s s'} {wfΣ : wfE Σ} :
  Σ ;;; Γ |-E tSort s ~~ tSort s' ->
  eq_univ_prop s s'.
Proof.
  intros [_ _ _ (v & v' & hv & hv' & e)]. cbn [canon] in hv, hv'.
  apply chain_Sort in hv. apply chain_Sort in hv'. subst v v'.
  exact (finstP_Sort_inv _ _ _ _ e).
Qed.

Lemma cumul_prop_propsE {Σ Γ u u'} {wfΣ : wfE Σ}:
  Sort.is_prop u ->
  Σ ;;; Γ |-E tSort u ~~ tSort u' ->
  Sort.is_prop u'.
Proof using Hcf.
  move => isp /cumul_prop_sortE. move: isp.
  destruct u, u' => //=. cbn. rewrite Hcf //.
Qed.

Lemma cumul_sprop_propsE {Σ Γ u u'} {wfΣ : wfE Σ} :
  Sort.is_sprop u ->
  Σ ;;; Γ |-E tSort u ~~ tSort u' ->
  Sort.is_sprop u'.
Proof using Type.
  move => isp /cumul_prop_sortE. move: isp.
  destruct u, u' => //.
Qed.

Lemma cumul_prop_symE Σ Γ T U :
  wfE Σ.1 ->
  Σ ;;; Γ |-E T ~~ U ->
  Σ ;;; Γ |-E U ~~ T.
Proof using Type.
  intros wfΣ Hl.
  exact (cpE_sym Hl).
Qed.

Lemma cumul_prop_transE Σ Γ T U V :
  wfE Σ ->
  Σ ;;; Γ |-E T ~~ U ->
  Σ ;;; Γ |-E U ~~ V ->
  Σ ;;; Γ |-E T ~~ V.
Proof using Type.
  intros wfΣ Hl Hr.
  exact (cpE_trans (wfΣ := wfE_ClosedBodies Σ.1) Hl Hr).
Qed.

Global Instance cumul_prop_transitiveE Σ Γ : wfE Σ -> CRelationClasses.Transitive (cumul_propE Σ Γ).
Proof using Type. intros. red. intros. now eapply cumul_prop_transE. Qed.

Lemma cumul_prop_cumul_pb_lE {Σ Γ pb A T B} {wfΣ : wf_extE Σ} :
  Σ ;;; Γ |-E A ~~ T ->
  Σ ;;; Γ ⊢E A ≤[pb] B ->
  Σ ;;; Γ |-E B ~~ T.
Proof using Type.
  intros HT cum.
  eapply cumul_pb_cumul_propE in cum; auto.
  eapply (cumul_prop_transE _ _ _ _ _ wfΣ.1); [|exact HT].
  eapply cumul_prop_symE; [exact wfΣ.1|exact cum].
Qed.

Lemma cumul_prop_cum_pb_rE {Σ Γ pb A T B} {wfΣ : wf_extE Σ} :
  Σ ;;; Γ |-E A ~~ T ->
  Σ ;;; Γ ⊢E B ≤[pb] A ->
  Σ ;;; Γ |-E B ~~ T.
Proof using Type.
  intros HT cum.
  eapply cumul_pb_cumul_propE in cum; auto.
  exact (cumul_prop_transE _ _ _ _ _ wfΣ.1 cum HT).
Qed.

Lemma cumul_prop_prod_invE {Σ Γ na A B na' A' B'} {wfΣ : wfE Σ} :
  Σ ;;; Γ |-E tProd na A B ~~ tProd na' A' B' ->
  Σ ;;; Γ ,, vass na A |-E B ~~ B'.
Proof using Type.
  intros [hΓ hl hr (v & v' & hv & hv' & e)]. cbn [canon] in hv, hv'.
  destruct (open_Prod_inv Γ na A B hl) as [hA hB].
  destruct (open_Prod_inv Γ na' A' B' hr) as [hA' hB'].
  destruct (chain_Prod _ _ _ _ _ hv) as (na1 & A1 & B1 & [-> _ _ hB1]).
  destruct (chain_Prod _ _ _ _ _ hv') as (na2 & A2 & B2 & [-> _ _ hB2]).
  have e3 := finstP_Prod_inv _ _ _ _ _ _ _ _ e.
  constructor; [exact (closed_snoc_vass Γ na A hΓ hA)|exact hB| |].
  - apply open_snoc. exact (open_snoc_inv Γ _ _ hB').
  - apply (BE_JoinPropE Σ (Γ ,, vass na A) B B' B1 B2).
    + eapply rt_trans; [apply BE_to_canon|]. exact (BE_ctx Σ _ _ _ _ (bodies_vass Γ _ na _ A) hB1).
    + eapply rt_trans; [apply BE_to_canon|]. exact (BE_ctx Σ _ _ _ _ (bodies_vass Γ _ na _ A) hB2).
    + exact (finstP_canon _ _ _ _ e3).
Qed.

Lemma substitution_untyped_cumul_propE {Σ Γ Δ Γ' s M N} {wfΣ : wfE Σ} :
  forallb (is_open_term Γ) s ->
  untyped_subslet Γ s Δ ->
  Σ ;;; (Γ ,,, Δ ,,, Γ') |-E M ~~ N ->
  Σ ;;; (Γ ,,, subst_context s 0 Γ') |-E (subst s #|Γ'| M) ~~ (subst s #|Γ'| N).
Proof using Type.
  intros cls subs Hcum.
  have cb := wfE_ClosedBodies Σ.1.
  destruct (cumul_propE_sandwich Hcum) as (v & v' & [hv hv' e]).
  apply (cumul_propE_of_sandwich (v := subst s #|Γ'| v) (v' := subst s #|Γ'| v')).
  - exact (untyped_substitution_ws_cumul_pbE subs cls hv).
  - exact (untyped_substitution_ws_cumul_pbE subs cls hv').
  - apply finstP_substs; [exact e|]. apply All2_refl. intros x. apply finstP_refl.
Qed.

Lemma substitution_cumul_propE {Σ Γ Δ Γ' s M N} {wfΣ : wfE Σ} :
  subsletE Σ Γ s Δ ->
  Σ ;;; (Γ ,,, Δ ,,, Γ') |-E M ~~ N ->
  Σ ;;; (Γ ,,, subst_context s 0 Γ') |-E (subst s #|Γ'| M) ~~ (subst s #|Γ'| N).
Proof using Type.
  intros subs Hcum.
  eapply substitution_untyped_cumul_propE; tea.
  - have h := subslet_open_termsE Γ s Δ subs. solve_all.
  - now eapply subslet_untyped_subsletE in subs.
Qed.

Lemma substitution_untyped_cumul_prop_equivE {Σ Γ Δ Γ' s s' M} {wfΣ : wfE Σ} :
  is_closed_context (Γ ,,, Δ ,,, Γ') ->
  forallb (is_open_term Γ) s ->
  forallb (is_open_term Γ) s' ->
  is_open_term (Γ ,,, Δ ,,, Γ') M ->
  #|s| = #|Δ| -> #|s'| = #|Δ| ->
  All2 (eq_term_prop Σ.1 0) s s' ->
  Σ ;;; (Γ ,,, subst_context s 0 Γ') |-E (subst s #|Γ'| M) ~~ (subst s' #|Γ'| M).
Proof using Type.
  intros clctx cls cls' clM lens_ lens' Heq.
  apply cpE_of_eq_term_prop.
  { eapply is_closed_subst_context; tea. }
  { eapply is_open_term_subst; tea. }
  { relativize #|Γ ,,, _|. eapply is_open_term_subst; tea. len. }
  eapply PCUICEquality.eq_term_upto_univ_substs => //.
  reflexivity.
Qed.

Lemma red_conv_propE {Σ Γ T U} {wfΣ : wf_extE Σ} :
  Σ ;;; Γ ⊢ T ⇝ U ->
  Σ ;;; Γ |-E T ~~ U.
Proof using Type.
  intros r. apply (cumul_pb_cumul_propE _ _ Conv).
  exact (red_ws_cumul_pbE (wfΣ := wfE_ClosedBodies Σ.1 (wfΣ := wfΣ.1)) r).
Qed.

Lemma substitution_red_terms_conv_propE {Σ Γ Δ Γ' s s' M} {wfΣ : wf_extE Σ} :
  is_closed_context (Γ ,,, Δ ,,, Γ') ->
  is_open_term (Γ ,,, Δ ,,, Γ') M ->
  untyped_subslet Γ s Δ ->
  red_terms Σ Γ s s' ->
  Σ ;;; (Γ ,,, subst_context s 0 Γ') |-E (subst s #|Γ'| M) ~~ (subst s' #|Γ'| M).
Proof using Type.
  intros.
  apply red_conv_propE.
  exact (closed_red_red_subst_cb (cbΣ := wfE_ClosedBodies Σ.1 (wfΣ := wfΣ.1)) H X0 X H0).
Qed.

Lemma context_conversion_cumul_propE {Σ Γ Δ M N} {wfΣ : wf_extE Σ} :
  Σ ;;; Γ |-E M ~~ N ->
  ws_cumul_ctx_pbE Conv Σ Γ Δ ->
  Σ ;;; Δ |-E M ~~ N.
Proof using Type.
  intros H X.
  have cb := wfE_ClosedBodies Σ.1 (wfΣ := wfΣ.1).
  destruct (cumul_propE_sandwich H) as (v & v' & [hv hv' e]).
  exact (cumul_propE_of_sandwich (ws_cumul_pbE_ws_cumul_ctx X hv) (ws_cumul_pbE_ws_cumul_ctx X hv') e).
Qed.

Lemma substitution_untyped_cumul_prop_cumulE {Σ Γ Δ Δ' s s' M} {wfΣ : wf_extE Σ} :
  is_closed_context (Γ ,,, Δ) ->
  is_closed_context (Γ ,,, Δ') ->
  is_open_term (Γ ,,, Δ) M ->
  untyped_subslet Γ s Δ ->
  untyped_subslet Γ s' Δ' ->
  All2 (cumul_propE Σ Γ) s s' ->
  Σ ;;; Γ |-E subst0 s M ~~ subst0 s' M.
Proof using Type.
  intros clctx clctx' clM subs subs' Heq.
  have cb := wfE_ClosedBodies Σ.1 (wfΣ := wfΣ.1).
  have hΓ : is_closed_context Γ by (rewrite on_free_vars_ctx_app in clctx; now move/andP: clctx => []).
  have lens' := All2_length Heq.
  have hlen := untyped_subslet_length subs.
  have hM : forall l : list term, #|l| = #|s| -> on_free_vars (shiftnP #|l| (shiftnP #|Γ| xpred0)) M.
  { intros l hl. rewrite shiftnP_add hl hlen.
    first [exact clM | rewrite app_context_length in clM; exact clM | len in clM; exact clM]. }
  destruct (cumul_propE_terms_sandwich Heq) as (vs & vs' & [h1 h2 h3]).
  have l1 := All2_length h1. have l2 := All2_length h2. have l3 := All2_length h3.
  apply (cumul_propE_of_sandwich (v := subst0 vs M) (v' := subst0 vs' M)).
  - exact (ws_cumul_pbE_subst0_conv hΓ h1 M (hM s eq_refl)).
  - exact (ws_cumul_pbE_subst0_conv hΓ h2 M (hM s' (eq_sym lens'))).
  - apply finstP_substs; [apply finstP_refl|exact h3].
Qed.

Lemma substitution1_untyped_cumul_propE {Σ Γ na t u M N} {wfΣ : wfE Σ.1} :
  is_open_term Γ u ->
  Σ ;;; (Γ ,, vass na t) |-E M ~~ N ->
  Σ ;;; Γ |-E M {0 := u} ~~ N {0 := u}.
Proof using Type.
  intros clu Hcum.
  eapply (substitution_untyped_cumul_propE (Δ := [_]) (Γ' := [])) in Hcum; cbn; eauto.
  cbn; rewrite clu //.
  repeat constructor.
Qed.

Lemma cmp_True_subst_instanceE Σ univs u u' (i : Instance.t) :
  wfE Σ.1 ->
  consistent_instance_ext Σ univs u ->
  consistent_instance_ext Σ univs u' ->
  cmp_universe_instance (fun _ _ => True) (subst_instance u i) (subst_instance u' i).
Proof using Type.
  intros wfΣ cu cu'. red.
  eapply All2_Forall2, All2_map, All2_refl => ui.
  unfold on_rel. auto.
Qed.

Lemma cumul_prop_subst_instanceE {Σ Γ univs u u' T} {wfΣ : wfE Σ} :
  is_closed_context Γ ->
  is_open_term Γ T ->
  consistent_instance_ext Σ univs u ->
  consistent_instance_ext Σ univs u' ->
  Σ ;;; Γ |-E subst_instance u T ~~ subst_instance u' T.
Proof using Type.
  intros clΓ clT cu cu'.
  enough (eq_term_prop Σ 0 T@[u] T@[u']) as e.
  { apply cpE_of_eq_term_prop; try assumption; now rewrite on_free_vars_subst_instance. }
  clear clΓ clT.
  induction T using PCUICInduction.term_forall_list_ind; cbn; intros;
    try solve [constructor; eauto; solve_all].
  - cbn. constructor.
    destruct s; split; reflexivity.
  - constructor. eapply PCUICEquality.eq_term_upto_univ_impl in IHT1; eauto.
    all:try typeclasses eauto.
    apply IHT2.
  - constructor. now eapply cmp_True_subst_instanceE.
  - constructor. now eapply cmp_instance_opt_variance, cmp_True_subst_instanceE.
  - constructor. now eapply cmp_instance_opt_variance, cmp_True_subst_instanceE.
  - cbn. constructor. splits; simpl; solve_all.
    eapply cmp_True_subst_instanceE; tea. reflexivity.
    apply IHT.
    eapply All2_map.
    eapply All_All2; tea. cbn. unfold eq_branch.
    intuition auto. rewrite /id. reflexivity.
  - constructor. unfold eq_mfixpoint.
    eapply All2_map. eapply All_All2; tea.
    cbn. intros d [].
    intuition eauto.
  - constructor. unfold eq_mfixpoint.
    eapply All2_map. eapply All_All2; tea.
    cbn. intros d [].
    intuition eauto.
  - cbn. constructor; splits; simpl.
    destruct p as [? []]; constructor; cbn in *; intuition eauto.
    solve_all.
Qed.

Lemma cmp_True_instanceE Σ univs u u' :
  wfE Σ.1 ->
  consistent_instance_ext Σ univs u ->
  consistent_instance_ext Σ univs u' ->
  cmp_universe_instance (fun _ _ => True) u u'.
Proof using Type.
  intros wfΣ cu cu'.
  destruct univs; simpl in *.
  - destruct u, u' => //=.
  - apply Forall2_triv.
    destruct cu as (_ & ? & _).
    destruct cu' as (_ & ? & _).
    congruence.
Qed.

Lemma cumul_prop_tProdE {Σ : global_env_ext} {Γ na t ty na' t' ty'} {wfΣ : wf_extE Σ} :
  eq_binder_annot na na' ->
  eq_term Σ.1 Σ t t' ->
  Σ ;;; Γ ,, vass na t |-E ty ~~ ty' ->
  Σ ;;; Γ |-E tProd na t ty ~~ tProd na' t' ty'.
Proof using Type.
  intros eqann eq cum.
  have cb := wfE_ClosedBodies Σ.1 (wfΣ := wfΣ.1).
  destruct (closed_snoc_vass_inv Γ na t (cpE_ctx cum)) as [hΓ ht].
  have hty' := open_snoc_inv Γ _ _ (cpE_right cum).
  have ht' : is_open_term Γ t' by eapply PCUICConfluence.eq_term_upto_univ_napp_on_free_vars in eq; tea.
  destruct (cumul_propE_sandwich cum) as (v & v' & [hv hv' e]).
  have hvo' := open_snoc_inv Γ _ _ (wsE_right hv').
  refine (cpE_trans (u := tProd na t v) _ _); [exact (cpE_of_ws (ws_cumul_pbE_Prod_r hv))|].
  refine (cpE_trans (u := tProd na t v') _ _).
  { apply cpE_of_finst; [exact hΓ| | |].
    - cbn [on_free_vars]. now rewrite ht (open_snoc_inv Γ _ _ (wsE_right hv)).
    - cbn [on_free_vars]. now rewrite ht hvo'.
    - constructor; [reflexivity|apply finstP_refl|exact e]. }
  refine (cpE_trans (u := tProd na t ty') _ _).
  { refine (cpE_sym _). exact (cpE_of_ws (ws_cumul_pbE_Prod_r hv')). }
  apply cpE_of_eq_term_prop; [exact hΓ| | |].
  - cbn [on_free_vars]. now rewrite ht hty'.
  - cbn [on_free_vars]. now rewrite ht' hty'.
  - constructor; [exact eqann|now eapply eq_term_eq_term_prop_impl|reflexivity].
Qed.

Lemma cumul_prop_tLetInE (Σ : global_env_ext) {Γ na t d ty na' t' d' ty'} {wfΣ : wf_extE Σ} :
  eq_binder_annot na na' ->
  eq_term Σ.1 Σ t t' ->
  eq_term Σ.1 Σ d d' ->
  Σ ;;; Γ ,, vdef na d t |-E ty ~~ ty' ->
  Σ ;;; Γ |-E tLetIn na d t ty ~~ tLetIn na' d' t' ty'.
Proof using Type.
  intros eqann eq eq' cum.
  have cb := wfE_ClosedBodies Σ.1 (wfΣ := wfΣ.1).
  destruct (closed_snoc_vdef_inv Γ na d t (cpE_ctx cum)) as [hΓ hd ht].
  have hty' := open_snoc_inv Γ _ _ (cpE_right cum).
  have ht' : is_open_term Γ t' by eapply PCUICConfluence.eq_term_upto_univ_napp_on_free_vars in eq; tea.
  have hd' : is_open_term Γ d' by eapply PCUICConfluence.eq_term_upto_univ_napp_on_free_vars in eq'; tea.
  destruct (cumul_propE_sandwich cum) as (v & v' & [hv hv' e]).
  have hvo := open_snoc_inv Γ _ _ (wsE_right hv).
  have hvo' := open_snoc_inv Γ _ _ (wsE_right hv').
  refine (cpE_trans (u := tLetIn na d t v) _ _); [exact (cpE_of_ws (ws_cumul_pbE_LetIn_bo_pb hv))|].
  refine (cpE_trans (u := tLetIn na d t v') _ _).
  { apply cpE_of_finst; [exact hΓ| | |].
    - cbn [on_free_vars]. now rewrite hd ht hvo.
    - cbn [on_free_vars]. now rewrite hd ht hvo'.
    - constructor; [reflexivity|apply finstP_refl|apply finstP_refl|exact e]. }
  refine (cpE_trans (u := tLetIn na d t ty') _ _).
  { refine (cpE_sym _). exact (cpE_of_ws (ws_cumul_pbE_LetIn_bo_pb hv')). }
  apply cpE_of_eq_term_prop; [exact hΓ| | |].
  - cbn [on_free_vars]. now rewrite hd ht hty'.
  - cbn [on_free_vars]. now rewrite hd' ht' hty'.
  - constructor; [exact eqann|now eapply eq_term_eq_term_prop_impl|now eapply eq_term_eq_term_prop_impl|reflexivity].
Qed.

Lemma cumul_prop_mkAppsE {Σ Γ f args f' args'} {wfΣ : wf_extE Σ} :
  is_closed_context Γ ->
  is_open_term Γ f ->
  is_open_term Γ f' ->
  eq_term Σ.1 Σ f f' ->
  All2 (cumul_propE Σ Γ) args args' ->
  Σ ;;; Γ |-E mkApps f args ~~ mkApps f' args'.
Proof using Type Hcf cf.
  intros clΓ clf clf' eq eq'.
  have cb := wfE_ClosedBodies Σ.1 (wfΣ := wfΣ.1).
  destruct (cumul_propE_terms_sandwich eq') as (vs & vs' & [h1 h2 h3]).
  have hvs : forallb (is_open_term Γ) vs.
  { exact (ws_terms_open_right h1). }
  have hvs' : forallb (is_open_term Γ) vs'.
  { exact (ws_terms_open_right h2). }
  refine (cpE_trans (u := mkApps f vs) _ _).
  { refine (cpE_of_ws (pb := Conv) _). apply (ws_cumul_pbE_mkApps (pb := Conv)); [exact (ws_cumul_pbE_refl clΓ clf)|exact h1]. }
  refine (cpE_trans (u := mkApps f' vs') _ _).
  { apply cpE_of_finst; [exact clΓ| | |].
    - rewrite on_free_vars_mkApps clf hvs //.
    - rewrite on_free_vars_mkApps clf' hvs' //.
    - apply finstP_mkApps; [|exact h3].
      apply (finstP_napp_mono _ 0); [|lia].
      apply finstP_of_eq_term_prop. now eapply eq_term_eq_term_prop_impl. }
  refine (cpE_sym (cpE_of_ws (pb := Conv) _)).
  apply (ws_cumul_pbE_mkApps (pb := Conv)); [exact (ws_cumul_pbE_refl clΓ clf')|exact h2].
Qed.

Lemma red_cumul_propE {Σ Γ} {wfΣ : wfE Σ} :
  CRelationClasses.subrelation (closed_red Σ Γ) (cumul_propE Σ Γ).
Proof using Type.
  intros x y r. apply (cumul_pb_cumul_propE _ _ Conv).
  exact (red_ws_cumul_pbE (wfΣ := wfE_ClosedBodies Σ.1) r).
Qed.

Lemma eq_term_prop_mkApps_invE {Σ ind u args ind' u' args'} {wfΣ : wf_extE Σ} :
  forall n, eq_term_prop Σ n (mkApps (tInd ind u) args) (mkApps (tInd ind' u') args') ->
  All2 (eq_term_prop Σ 0) args args'.
Proof using Type.
  revert args'.
  induction args using rev_ind; intros args' n; simpl.
  intros H; destruct args' using rev_case.
  constructor.
  depelim H. solve_discr. eapply app_eq_nil in H1 as [_ H]. congruence.
  intros H.
  destruct args' using rev_case. depelim H. solve_discr.
  apply app_eq_nil in H1 as [_ H]; discriminate.
  rewrite !mkApps_app /= in H. depelim H.
  eapply All2_app => //.
  eapply IHargs; eauto. repeat constructor.
  red. apply H0.
Qed.

Lemma cumul_prop_mkApps_Ind_invE {Σ Γ ind u args ind' u' args'} {wfΣ : wf_extE Σ} :
  Σ ;;; Γ |-E mkApps (tInd ind u) args ~~ mkApps (tInd ind' u') args' ->
  All2 (cumul_propE Σ Γ) args args'.
Proof using Type.
  intros [hΓ hl hr (v & v' & hv & hv' & e)].
  have cb := wfE_ClosedBodies Σ.1 (wfΣ := wfΣ.1).
  rewrite canon_mkApps in hv. rewrite canon_mkApps in hv'. cbn [canon] in hv, hv'.
  destruct (chain_mkApps_Ind (wfΣ := cb) Γ ind u (map canon args) v hΓ
              (open_mkApps_canon Γ _ args eq_refl hl) hv) as (l1 & -> & hl1).
  destruct (chain_mkApps_Ind (wfΣ := cb) Γ ind' u' (map canon args') v' hΓ
              (open_mkApps_canon Γ _ args' eq_refl hr) hv') as (l1' & -> & hl1').
  destruct (finstP_mkApps_Ind_l _ _ _ _ _ _ e) as (u2 & l2 & [E hl2]).
  destruct (mkApps_head_inj (tInd ind' u') (tInd ind u2) _ _ eq_refl eq_refl E) as [_ <-].
  exact (All2_cpE_zip Γ args args' l1 l1' hΓ (forallb_open_mkApps Γ _ _ hl)
           (forallb_open_mkApps Γ _ _ hr) (All2_BE_from_canon Γ args l1 hl1)
           (All2_BE_from_canon Γ args' l1' hl1') hl2).
Qed.

Global Instance cumul_prop_sym'E Σ Γ : wfE Σ.1 -> CRelationClasses.Symmetric (cumul_propE Σ Γ).
Proof using Type.
  now intros wf x y; eapply cumul_prop_symE.
Qed.

Lemma cumul_prop_is_openE {Σ Γ T U} :
  Σ ;;; Γ |-E T ~~ U ->
  [× is_closed_context Γ, is_open_term Γ T & is_open_term Γ U].
Proof using Type.
  intros [hΓ hT hU _]. split; auto.
Qed.

#[local] Hint Resolve wf_local_closed_contextE subject_is_open_termE type_is_open_termE
  typing_closed_contextE : fvs.

Section MainE.

(* FORECAST-ONLY: the class of copy 16 that [validityE] and [isType_mkApps_Ind_invE] belong to
   ([PCUICValidityEta.v:104], imported, not redefined); delete with that class. *)
Context {V16 : ValForecastCopy16}.

(** Well-typed terms in the leq_term relation live in the same sort hierarchy. *)
Lemma typing_leq_term_prop_genE :
  env_propE
    (fun Σ Γ t T =>
      forall t' T' : term,
      on_udecl Σ.1 Σ.2 ->
      Σ ;;; Γ |-E t' : T' ->
      forall pb n, compare_term_napp Σ Σ pb n t' t ->
      Σ ;;; Γ |-E T ~~ T')%type
    (fun Σ Γ j => on_udecl Σ.1 Σ.2 ->
      lift_typing0 (fun t T =>
      forall t' T' : term,
      Σ ;;; Γ |-E t' : T' ->
      forall pb n, compare_term_napp Σ Σ pb n t' t ->
      Σ ;;; Γ |-E T ~~ T') j)
    (fun Σ Γ => wf_localE Σ Γ).
Proof using V16 Hcf cf.
  eapply typingE_ind_env.
  { intros ???? H ?. apply lift_typing_impl with (1 := H) => ?? [] ?? ?? //. eauto. }
  1: now auto.

  all: intros Σ wfΣ Γ wfΓ; intros.

  1-13:match goal with
  [ H : compare_term_napp _ _ _ _ _ _ |- _ ] => depelim H
  end; assert (wf_extE Σ) by (split; assumption).

  15:{ assert (wf_extE Σ) by (split; assumption). specialize (X1 _ _ H X5 _ _ X6).
       eapply cumul_prop_cumul_pb_lE; tea.
       eapply into_ws_cumul_pbE_spec; [exact X4|..]; fvs. }

  6:{ eapply inversion_AppE in X6 as (na' & A' & B' & hf & ha & cum); auto.
      specialize (X3 _ _ H hf _ _ X7_1).
      specialize (X5 _ _ H ha _ _ X7_2).
      eapply cumul_pb_cumul_propE in cum; auto.
      transitivity (B' {0 := u0}) => //.
      eapply cumul_prop_prod_invE in X3 => //.
      transitivity (B' {0 := u}).
      eapply substitution1_untyped_cumul_propE in X3. eapply X3.
      now eapply subject_is_open_termE.
      destruct (cumul_prop_is_openE cum).
      apply cpE_of_eq_term_prop; auto. eapply PCUICOnFreeVars.on_free_vars_subst => /= //.
      eapply subject_is_open_termE in X4. now rewrite X4.
      rewrite shiftnP_add. now eapply cumul_prop_is_openE in X3 as [].
      eapply eq_term_eq_term_prop_impl => //.
      eapply PCUICEquality.eq_term_upto_univ_substs.
      all: try reflexivity.
      constructor. 2:constructor. now symmetry. }

  - eapply inversion_RelE in X0 as [decl' [wfΓ' [Hnth Hcum]]]; auto.
    rewrite Hnth in H; noconf H. now eapply cumul_pb_cumul_propE in Hcum.

  - eapply inversion_SortE in X0 as [wf [wfs Hs]]; auto.
    apply subrelation_compare_sort_eq_prop in c => //.
    apply cumul_pb_cumul_propE in Hs => //.
    eapply cumul_prop_transE; eauto.
    destruct (cumul_prop_is_openE Hs) as [].
    apply cpE_of_eq_term_prop => //. constructor. rewrite /eq_univ_prop !Sort.sType_super //.

  - eapply inversion_ProdE in X4 as [s1' [s2' [Ha [Hb Hs]]]]; auto.
    specialize (X1 H). apply unlift_TypUniv in X1, Ha.
    specialize (X1 _ _ Ha _ _ X5_1).
    eapply context_conversionE in Hb.
    3:{ constructor. apply cpE_conv_context_refl. constructor. eassumption.
      exact (JoinE_of_compare_term _ _ _ _ _ X5_1). }
    2:{ exact (typingE_wf_local X2). }
    specialize (X3 _ _ H Hb _ _ X5_2).
    eapply cumul_pb_cumul_propE in Hs => //.
    eapply cumul_prop_transE; eauto.
    apply cpE_of_eq_term_prop; fvs. constructor.
    apply cumul_prop_sortE in X1, X3. move: X1 X3. clear.
    unfold eq_univ_prop.
    destruct s2, s2' => //=.
    all: destruct s1, s1' => //=.

  - eapply inversion_LambdaE in X4 as (B & dom & bod & cum); tas.
    specialize (X3 t0 B H).
    assert (hctx : conv_context (@JoinE cf) Σ (Γ ,, vass na0 ty) (Γ ,, vass na t)).
    { constructor. apply cpE_conv_context_refl. constructor. eassumption.
      exact (JoinE_of_compare_term _ _ _ _ _ X5_1). }
    forward X3.
    { eapply (context_conversionE (Γ ,, vass na0 ty)); [exact bod|exact (typingE_wf_local X2)|exact hctx]. }
    specialize (X3 _ _ X5_2). eapply cumul_pb_cumul_propE in cum; eauto.
    eapply cumul_prop_transE; eauto.
    eapply cumul_prop_tProdE; eauto. now symmetry. now symmetry.

  - eapply inversion_LetInE in X4 as (A & dombod & codom & cum); auto.
    assert (hctx : conv_context (@JoinE cf) Σ (Γ ,, vdef na0 t ty) (Γ ,, vdef na b b_ty)).
    { constructor. apply cpE_conv_context_refl. constructor; try eassumption.
      all: now apply JoinE_of_compare_term. }
    specialize (X3 u A H).
    forward X3.
    { eapply (context_conversionE (Γ ,, vdef na0 t ty)); [exact codom|exact (typingE_wf_local X2)|exact hctx]. }
    specialize (X3 _ _ X5_3).
    eapply cumul_pb_cumul_propE in cum; eauto.
    eapply cumul_prop_transE; eauto.
    eapply cumul_prop_tLetInE; auto; now symmetry.

  - eapply inversion_ConstE in X1 as [decl' [wf [declc [cu cum]]]]; auto.
    eapply cumul_pb_cumul_propE in cum; eauto.
    eapply cumul_prop_transE; eauto.
    unshelve eapply declared_constant_to_gen in H, declc; eauto.
    pose proof (declared_constant_inj _ _ H declc); subst decl'.
    eapply cumul_prop_subst_instanceE; eauto. fvs.
    destruct (cumul_prop_is_openE cum) as [].
    now rewrite on_free_vars_subst_instance in i0.

  - eapply inversion_IndE in X1 as [decl' [idecl' [wf [declc [cu cum]]]]]; auto.
    unshelve eapply declared_inductive_to_gen in isdecl, declc; eauto.
    pose proof (declared_inductive_inj isdecl declc) as [-> ->].
    eapply cumul_pb_cumul_propE in cum; eauto.
    eapply cumul_prop_transE; eauto.
    eapply cumul_prop_subst_instanceE; tea. fvs.
    destruct (cumul_prop_is_openE cum) as [].
    now rewrite on_free_vars_subst_instance in i0.

  - eapply inversion_ConstructE in X1 as [decl' [idecl' [cdecl' [wf [declc [cu cum]]]]]]; auto.
    have isdeclE := isdecl.
    unshelve eapply declared_constructor_to_gen in declc; eauto.
    unshelve epose proof (isdecl' := declared_constructor_to_gen isdecl); eauto.
    pose proof (declared_constructor_inj isdecl' declc) as [-> [-> ->]].
    eapply cumul_pb_cumul_propE in cum; eauto.
    eapply cumul_prop_transE; eauto.
    unfold type_of_constructor.
    (* Route change (availability): the landed [wf_arities_contextE] (copy 10), not copy 16's
       [wf_arities_context_inst]; the instance is removed below by
       [on_free_vars_ctx_subst_instance], as in base. *)
    have clars : is_closed_context (arities_context (ind_bodies mdecl)).
    { exact (wf_local_closed_contextE (Σ := (Σ.1, ind_universes mdecl)) (wfΣ := wfΣ)
               (wf_arities_contextE (wfΣ := wfΣ) (proj1 (proj1 isdeclE)))). }
    (* Base [declared_constructor_closed_gen_type]'s proof ([Typing/PCUICClosedTyp.v:638]), over
       the landed [declared_inductive_closed_constructorsE]. *)
    have clty : is_open_term (Γ,,, arities_context (ind_bodies mdecl)) (cstr_type cdecl').
    { eapply closedn_on_free_vars, closed_upwards.
      { destruct isdeclE as [hidecl hcdecl].
        eapply declared_inductive_closed_constructorsE in hidecl as h.
        eapply All_nth_error in h. 2: eassumption.
        move/andP: h => [/andP [hargs hindices]] hty. exact hty. }
      len. }
    etransitivity.
    eapply (@substitution_untyped_cumul_prop_equivE _ Γ (subst_instance u (arities_context mdecl.(ind_bodies))) []); auto.
    * simpl.
      apply is_closed_context_weaken. fvs.
      now rewrite on_free_vars_ctx_subst_instance.
    * eapply on_free_vars_terms_inds.
    * eapply on_free_vars_terms_inds.
    * simpl.
      rewrite on_free_vars_subst_instance /=.
      len. len in clty.
    * len.
    * len.
    * induction (ind_bodies mdecl) in |- *; simpl; constructor; auto.
      constructor. simpl. eapply cmp_instance_opt_variance.
      eapply cmp_True_instanceE; eauto.
    * simpl.
      eapply (@substitution_untyped_cumul_propE _ Γ (subst_instance u0 (arities_context mdecl.(ind_bodies))) []) => //.
      eapply on_free_vars_terms_inds.
      eapply untyped_subslet_inds; tea. simpl.
      eapply cumul_prop_subst_instanceE => //; eauto.
      eapply is_closed_context_weaken; fvs.
      len in clty; len.

  - eapply inversion_CaseE in X9 as (mdecl' & idecl' & isdecl' & indices' & data & cum); auto.
    eapply cumul_pb_cumul_propE in cum; eauto.
    eapply cumul_prop_transE; eauto. simpl.
    clear X8.
    unshelve eapply declared_inductive_to_gen in isdecl, isdecl'; eauto.
    destruct (declared_inductive_inj isdecl isdecl'). subst.
    destruct data.
    specialize (X7 _ _ H6 scrut_ty _ _ X10).
    eapply cumul_prop_symE => //.
    destruct e as [eqpars [eqinst [eqpctx eqpret]]].
    rewrite /ptm.
    eapply cumul_prop_mkAppsE => //. fvs.
    { eapply cumul_prop_is_openE in cum as [].
      rewrite on_free_vars_mkApps in i0.
      move/andP: i0 => [] //. }
    { now eapply PCUICGenerationEta.type_it_mkLambda_or_LetInE, subject_is_open_termE in pret. }
    { eapply PCUICEquality.eq_term_upto_univ_it_mkLambda_or_LetIn => //. tc.
      rewrite /predctx.
      rewrite /case_predicate_context /case_predicate_context_gen.
      rewrite /pre_case_predicate_context_gen /inst_case_context.
      eapply eq_context_upto_names_map2_set_binder_name; tea.
      eapply eq_context_upto_subst_context; tea. 1,2: tc.
      eapply eq_context_upto_univ_subst_instance; try tc. tas.
      now eapply All2_rev. }
    eapply All2_app.
    2:{ constructor; [|constructor].
        apply cpE_of_eq_term_prop; [fvs|now eapply subject_is_open_termE in scrut_ty
          |now eapply subject_is_open_termE in X6|now eapply eq_term_eq_term_prop_impl]. }
    eapply cumul_prop_mkApps_Ind_invE in X7 => //.
    eapply All2_app_inv_l in X7 as (?&?&?&?&?).
    eapply All2_symP => //. exact (cumul_prop_sym'E _ _ wfΣ).
    eapply app_inj in e as [eql ->] => //.
    move: (All2_length eqpars).
    move: (All2_length a). lia.

  - eapply inversion_ProjE in X3 as (u' & mdecl' & idecl' & cdecl' & pdecl' & args' & inv); auto.
    have hlen' : #|args'| = ind_npars mdecl' by (destruct inv as [_ [_ [h _]]]; exact h).
    intuition auto.
    specialize (X2 _ _  H0 a0 _ _ X4).
    eapply cumul_pb_cumul_propE in b; eauto.
    eapply cumul_prop_transE; eauto.
    eapply cumul_prop_mkApps_Ind_invE in X2 => //.
    unshelve epose proof (a' := declared_projection_to_gen a); eauto.
    unshelve epose proof (isdecl' := declared_projection_to_gen isdecl); eauto.
    destruct (declared_projection_inj a' isdecl') as [<- [<- [<- <-]]].
    destruct (isType_mkApps_Ind_invE _ isdecl X0 (validityE X1)) as [ps [argss [_ cu]]]; eauto.
    destruct (isType_mkApps_Ind_invE _ isdecl X0 (validityE a0)) as [? [? [_ cu']]]; eauto.
    (* Route change (availability), as in [BDFromPCUICEta]: the closed projection context and the
       untyped substitution [c :: rev args], in place of copy 16's [wf_projection_context] and
       [projection_subslet]. *)
    have clp := BDFromPCUICEta.is_closed_projection_contextE (wfΣ := wfΣ) u isdecl.
    have clp' := BDFromPCUICEta.is_closed_projection_contextE (wfΣ := wfΣ) u' isdecl.
    have hc0 : is_open_term Γ c0 by now eapply subject_is_open_termE in a0.
    have hargs' : forallb (is_open_term Γ) (List.rev args').
    { rewrite forallb_rev. eapply type_is_open_termE in a0. exact (forallb_open_mkApps Γ _ _ a0). }
    have clΓ : is_closed_context Γ := wf_local_closed_contextE (wfΣ := wfΣ) wfΓ.
    have hprojty : forall v, is_open_term (Γ ,,, projection_context p.(proj_ind) mdecl' idecl' v)
                                (subst_instance v pdecl'.(proj_type)).
    { intros v. epose proof (declared_projection_closedE a).
      len. rewrite on_free_vars_subst_instance. simpl; len.
      rewrite (declared_minductive_ind_nparsE a) in H1.
      rewrite closedn_on_free_vars //. eapply closed_upwards; tea. lia. }
    transitivity (subst0 (c0 :: List.rev args') (subst_instance u pdecl'.(proj_type))).
    eapply (substitution_untyped_cumul_prop_cumulE (Γ := Γ) (Δ := projection_context p.(proj_ind) mdecl' idecl' u)
              (Δ' := projection_context p.(proj_ind) mdecl' idecl' u')).
    * exact (is_closed_context_weaken clΓ clp).
    * exact (is_closed_context_weaken clΓ clp').
    * exact (hprojty u).
    * exact (BDFromPCUICEta.untyped_subslet_projection_contextE (wfΣ := wfΣ) u isdecl H).
    * exact (BDFromPCUICEta.untyped_subslet_projection_contextE (wfΣ := wfΣ) u' isdecl hlen').
    * constructor.
      { symmetry. apply cpE_of_eq_term_prop; [exact clΓ|exact hc0|now eapply subject_is_open_termE in X1|].
        now eapply eq_term_eq_term_prop_impl. }
      now eapply All2_rev.
    * eapply (substitution_untyped_cumul_propE (wfΣ := wfΣ) (Γ := Γ)
                (Δ := projection_context p.(proj_ind) mdecl' idecl' u') (Γ' := [])).
      { exact (andb_true_intro (conj hc0 hargs')). }
      { exact (BDFromPCUICEta.untyped_subslet_projection_contextE (wfΣ := wfΣ) u' isdecl hlen'). }
      eapply cumul_prop_subst_instanceE.
      { exact (is_closed_context_weaken clΓ clp'). }
      { have h := hprojty u'. rewrite on_free_vars_subst_instance in h. exact h. }
      all: eassumption.

  - match goal with Hty : _ ;;; _ |-E tFix _ _ : _ |- _ =>
      eapply inversion_FixE in Hty as (decl' & fixguard' & Hnth & types' & bodies & wffix & cum)
    end; auto.
    eapply cumul_pb_cumul_propE in cum; eauto.
    eapply cumul_prop_transE; eauto.
    eapply All2_nth_error in e; eauto.
    destruct e as (a & _).
    apply cpE_of_eq_term_prop; [fvs|..].
    { eapply nth_error_all in X0; tea.
      now apply isTypeRel_is_open_termE in X0. }
    { now eapply cumul_prop_is_openE in cum as []. }
    eapply eq_term_eq_term_prop_impl; eauto.
    now symmetry in a.

  - match goal with Hty : _ ;;; _ |-E tCoFix _ _ : _ |- _ =>
      eapply inversion_CoFixE in Hty as (decl' & fixguard' & Hnth & types' & bodies & wfcofix & cum)
    end; auto.
    eapply cumul_pb_cumul_propE in cum; eauto.
    eapply cumul_prop_transE; eauto.
    eapply All2_nth_error in e; eauto.
    destruct e as (a & _).
    apply cpE_of_eq_term_prop; [fvs|..].
    { eapply nth_error_all in X0; tea.
      now apply isTypeRel_is_open_termE in X0. }
    { now eapply cumul_prop_is_openE in cum as []. }
    eapply eq_term_eq_term_prop_impl; eauto.
    now symmetry in a.

  - depelim X3.
    eapply inversion_PrimE in X2 as [prim_ty' [cdecl' []]]; tea. depelim o.
    1-3:rewrite H in e; noconf e; eapply cumul_pb_cumul_propE; eauto; pcuic.
    depelim X1.
    cbn in H, e2. rewrite H in e2. noconf e2. eapply cumul_pb_cumul_propE; eauto; pcuic.
    move: w; simp prim_type. intro. etransitivity; tea.
    constructor; fvs. cbn.
    all: depelim X0; fvs.
    apply JoinE_of_compare_term. eapply eq_term_leq_term. symmetry; repeat constructor; eauto.
Qed.

Lemma typing_leq_term_propE (Σ : global_env_ext) Γ t t' T T' :
  wfE Σ.1 ->
  Σ ;;; Γ |-E t : T ->
  on_udecl Σ.1 Σ.2 ->
  Σ ;;; Γ |-E t' : T' ->
  forall pb n, compare_term_napp Σ Σ pb n t' t ->
  Σ ;;; Γ |-E T ~~ T'.
Proof using V16 Hcf cf.
  intros.
  now eapply (env_propE_typing typing_leq_term_prop_genE).
Qed.

End MainE.

End no_prop_leq_typeE.
