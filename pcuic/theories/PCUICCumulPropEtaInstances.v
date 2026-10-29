(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the lemmas of [PCUICCumulPropEta] (row T6)

  Each lemma family of [PCUICCumulPropEta] with a premise is applied here to concrete premises,
  each proved. NON-DEGENERATE: every instance with a relational premise exercises a non-trivial
  step: an η step ([λx:Prop. f x] and [f] in the context [f : Prop → Prop], [cpi_eta]), a β step
  ([cpi_beta]), two universe levels of one family, or two universe instances. The exceptions,
  each with its reason:
  - [cumul_prop_propsE], [cumul_sprop_propsE], [prop_sort_eqE], [sprop_sort_eqE]: IMPOSSIBLE to
    instantiate otherwise than at [Prop]/[SProp] on both sides (a property of the statement: the
    premises [Sort.is_prop u]/[Sort.is_sprop u] force the sort, and a [cumul_propE] between two
    sorts is their comparison); the instances are at [Prop] and [SProp].
  - [typing_leq_term_prop_genE], [typing_leq_term_propE]: they take the forecast class
    [ValForecastCopy16] (copy 16, not landed), so, as in [PCUICValidityEtaInstances], the
    instance [typing_leq_term_propE_inst] states the premises AND the conclusion at concrete
    arguments, each proved without the lemma and without any class. The pair is the η one:
    the variable [x] typed at [G F] and at [G (λy:Prop. F y)]
    ([PCUICCumulPropEtaRefutations], [tw_witness_typed]).

  The flags: [cpr_flags] ([prop_sub_type = false]) where a lemma takes base's section variable
  [Hcf]; otherwise any flags.

  The two imported E lemmas are compared with the base-substituted statement in compiled form:
  [cpE_import_conv_sort_inv] and [cpE_import_LetIn_l_inv_alt] inhabit the base-substituted type
  ([conv_sort_inv], [ws_cumul_pb_LetIn_l_inv_alt] with [wf] → [wfE], [wf_local] → [wf_localE],
  [⊢] → [⊢E]) by the landed lemmas. The converse ascription does not hold: the landed types
  take fewer premises (no environment premise for [conv_sort_invE]; [ClosedBodies] and no
  [wf_localE] for the LetIn lemma). *)

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICEquality PCUICReduction
     PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICTypingEta
     PCUICWellScopedCumulativity PCUICConversion PCUICCumulProp PCUICClosedBodies
     PCUICEtaDefs PCUICEtaCanon PCUICEtaFInst PCUICEtaFInstEquiv PCUICEtaI5 PCUICEtaI5A2 PCUICEtaC1b
     PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICContextConversionEta
     PCUICSubstitutionEta PCUICEtaA6More PCUICWsCumulEtaCtx PCUICEtaIndInvRefutations
     PCUICCumulPropEta PCUICCumulPropEtaRefutations.
From MetaRocq.PCUIC.Typing Require Import PCUICClosedTypEta.

(** ** The two imported E lemmas against the base-substituted statements *)

Definition cpE_import_conv_sort_inv :
  forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wfE Σ) (Γ : context) (s s' : sort),
    Σ ;;; Γ ⊢E tSort s = tSort s' -> eq_sort (global_ext_constraints Σ) s s'
  := fun cf Σ wfΣ Γ s s' h => conv_sort_invE Γ s s' h.

Definition cpE_import_LetIn_l_inv_alt :
  forall (cf : checker_flags) (Σ : global_env_ext) (Γ : context) (C : term) (na : aname)
    (d ty b : term) (wfΣ : wfE Σ.1),
    wf_localE Σ (Γ ,, vdef na d ty) ->
    Σ ;;; Γ ⊢E tLetIn na d ty b = C ->
    Σ ;;; Γ ,, vdef na d ty ⊢E b = lift0 1 C
  := fun cf Σ Γ C na d ty b wfΣ _ h => ws_cumul_pbE_LetIn_l_inv_alt (wfΣ := wfE_ClosedBodies Σ.1) h.

(** ** The environments and the steps *)

Section Generic.

  Context {cf : checker_flags}.

  Definition cpi_wfE : wfE rf_Σ := wf_incl_E (@wf_empty_global_env cf).
  Definition cpi_wf_extE : wf_extE rf_Σ := wf_ext_incl_E cpr_wf_ext_empty.
  Definition cpi_cb : ClosedBodies rf_Σ := wfE_ClosedBodies rf_Σ.1 (wfΣ := cpi_wfE).

  (** η: [f : Prop → Prop ⊢ λx:Prop. f x ≡ f], at any flags (the proof of [rf_premise]). *)
  Lemma cpi_eta pb : ws_cumul_pbE pb rf_Σ rf_Γ rf_t (tRel 0).
  Proof.
    constructor; try reflexivity.
    exists (tRel 0), (tRel 0). split; [|split].
    - apply rt_step; right. cbn. exact (eta_red canon_la (tRel 0) canon_dom).
    - cbn. apply rt_refl.
    - apply compare_term_eta_refl.
  Qed.

  Definition cpi_eta_cp : rf_Σ ;;; rf_Γ |-E rf_t ~~ tRel 0 :=
    cumul_pb_cumul_propE rf_Σ rf_Γ Conv _ _ (cpi_eta Conv).

  (** β: [(λx:Type. x) Prop ⇝ Prop]. *)
  Definition cpi_na : aname := mkBindAnn nAnon Relevant.
  Definition cpi_beta : term := tApp (tLambda cpi_na (tSort (Sort.super sProp)) (tRel 0)) (tSort sProp).

  Lemma cpi_beta_red Γ : is_closed_context Γ -> rf_Σ ;;; Γ ⊢ cpi_beta ⇝ tSort sProp.
  Proof. intros hΓ. split; [exact hΓ|reflexivity|]. apply red1_red. constructor. Qed.

  (** ** Basic structure *)

  Definition cumul_pb_cumul_propE_inst := cpi_eta_cp.

  Definition cumul_prop_symE_inst : rf_Σ ;;; rf_Γ |-E tRel 0 ~~ rf_t :=
    cumul_prop_symE rf_Σ rf_Γ _ _ cpi_wfE cpi_eta_cp.

  Definition cumul_prop_transE_inst : rf_Σ ;;; rf_Γ |-E rf_t ~~ rf_t :=
    cumul_prop_transE rf_Σ rf_Γ _ _ _ cpi_wfE cpi_eta_cp cumul_prop_symE_inst.

  Definition cumul_prop_transitiveE_inst : rf_Σ ;;; rf_Γ |-E rf_t ~~ rf_t :=
    @cumul_prop_transitiveE cf rf_Σ rf_Γ cpi_wfE _ _ _ cpi_eta_cp cumul_prop_symE_inst.

  Definition cumul_prop_sym'E_inst : rf_Σ ;;; rf_Γ |-E tRel 0 ~~ rf_t :=
    @cumul_prop_sym'E cf rf_Σ rf_Γ cpi_wfE _ _ cpi_eta_cp.

  Definition cumul_prop_is_openE_inst := cumul_prop_is_openE cpi_eta_cp.

  Definition cumul_prop_cumul_pb_lE_inst : rf_Σ ;;; rf_Γ |-E tRel 0 ~~ tRel 0 :=
    cumul_prop_cumul_pb_lE (wfΣ := cpi_wf_extE) cpi_eta_cp (cpi_eta Cumul).

  Definition cumul_prop_cum_pb_rE_inst : rf_Σ ;;; rf_Γ |-E rf_t ~~ rf_t :=
    cumul_prop_cum_pb_rE (wfΣ := cpi_wf_extE) cumul_prop_symE_inst (cpi_eta Cumul).

  Definition into_cumul_propE_red_inst : rf_Σ ;;; [] |-E cpi_beta ~~ tSort sProp :=
    into_cumul_propE_red (tSort sProp; tSort sProp; (cpi_beta_red [] eq_refl,
      closed_red_refl (Γ := []) eq_refl eq_refl, ltac:(reflexivity))).

  Definition red_cumul_propE_inst : rf_Σ ;;; [] |-E cpi_beta ~~ tSort sProp :=
    red_cumul_propE (wfΣ := cpi_wfE) _ _ (cpi_beta_red [] eq_refl).

  Definition red_conv_propE_inst : rf_Σ ;;; [] |-E cpi_beta ~~ tSort sProp :=
    red_conv_propE (wfΣ := cpi_wf_extE) (cpi_beta_red [] eq_refl).

  (** ** Sorts *)

  (** [Type₀] and [Type₁]: one family, two levels. *)
  Lemma cpi_type01 : rf_Σ ;;; [] |-E tSort Sort.type0 ~~ tSort (Sort.super Sort.type0).
  Proof. apply cpE_of_eq_term_prop; try reflexivity. constructor. reflexivity. Qed.

  Definition cumul_prop_sortE_inst : eq_univ_prop Sort.type0 (Sort.super Sort.type0) :=
    cumul_prop_sortE (wfΣ := cpi_wfE) cpi_type01.

  Definition cumul_sprop_propsE_inst : Sort.is_sprop sSProp :=
    cumul_sprop_propsE (wfΣ := cpi_wfE) (u := sSProp) eq_refl
      (cpE_of_eq_term_prop eq_refl eq_refl eq_refl ltac:(reflexivity)).

  Lemma cpi_beta_cumul_Prop : ws_cumul_pbE Cumul rf_Σ [] cpi_beta (tSort sProp).
  Proof. exact (red_ws_cumul_pbE (wfΣ := cpi_cb) (cpi_beta_red [] eq_refl)). Qed.

  Definition cumul_sort_confluenceE_inst :=
    cumul_sort_confluenceE (wfΣ := cpi_wfE) cpi_beta_cumul_Prop cpi_beta_cumul_Prop.

  Definition cpi_betaS : term := tApp (tLambda cpi_na (tSort (Sort.super sSProp)) (tRel 0)) (tSort sSProp).

  Lemma cpi_betaS_cumul_SProp : ws_cumul_pbE Cumul rf_Σ [] cpi_betaS (tSort sSProp).
  Proof.
    apply (red_ws_cumul_pbE (wfΣ := cpi_cb)).
    split; [reflexivity|reflexivity|]. apply red1_red. constructor.
  Qed.

  Definition is_sprop_bottomE_inst : Sort.is_sprop sSProp :=
    is_sprop_bottomE cpi_wf_extE cpi_betaS_cumul_SProp cpi_betaS_cumul_SProp eq_refl.

  Definition prop_sort_eqE_inst : rf_Σ ;;; [] ⊢E tSort sProp = tSort sProp :=
    @prop_sort_eqE cf rf_Σ [] sProp sProp eq_refl eq_refl eq_refl.

  Definition sprop_sort_eqE_inst : rf_Σ ;;; [] ⊢E tSort sSProp = tSort sSProp :=
    @sprop_sort_eqE cf rf_Σ [] sSProp sSProp eq_refl eq_refl eq_refl.

  (** ** Binders: the η pair under a product and under a let *)

  (** In [f : Prop → Prop, x : Prop]: [λy:Prop. f y] (written in the extended context) and [f]. *)
  Definition cpi_lam : term := tLambda cpi_na (tSort sProp) (tApp (tRel 2) (tRel 0)).

  Lemma cpi_eta_ext d : is_closed_context (rf_Γ ,, d) ->
    ws_cumul_pbE Conv rf_Σ (rf_Γ ,, d) cpi_lam (tRel 1).
  Proof.
    intros hΓ. apply (eta1_ws_cumul_pbE (wfΣ := cpi_cb)); [exact hΓ|reflexivity|].
    exact (eta_red cpi_na (tRel 1) (tSort sProp)).
  Qed.

  Definition cpi_ctx_vass : context := rf_Γ ,, vass cpi_na (tSort sProp).
  Definition cpi_ctx_vdef : context := rf_Γ ,, vdef cpi_na (tSort sProp) (tSort (Sort.super sProp)).

  Definition cpi_codom_cp : rf_Σ ;;; cpi_ctx_vass |-E cpi_lam ~~ tRel 1 :=
    cumul_pb_cumul_propE _ _ Conv _ _ (cpi_eta_ext _ eq_refl).

  Definition cumul_prop_tProdE_inst :
    rf_Σ ;;; rf_Γ |-E tProd cpi_na (tSort sProp) cpi_lam ~~ tProd cpi_na (tSort sProp) (tRel 1) :=
    cumul_prop_tProdE (wfΣ := cpi_wf_extE) eq_refl ltac:(reflexivity) cpi_codom_cp.

  Definition cumul_prop_prod_invE_inst : rf_Σ ;;; cpi_ctx_vass |-E cpi_lam ~~ tRel 1 :=
    cumul_prop_prod_invE (wfΣ := cpi_wfE) cumul_prop_tProdE_inst.

  Definition cumul_prop_tLetInE_inst :
    rf_Σ ;;; rf_Γ |-E tLetIn cpi_na (tSort sProp) (tSort (Sort.super sProp)) cpi_lam
                    ~~ tLetIn cpi_na (tSort sProp) (tSort (Sort.super sProp)) (tRel 1) :=
    cumul_prop_tLetInE rf_Σ (wfΣ := cpi_wf_extE) eq_refl ltac:(reflexivity) ltac:(reflexivity)
      (cumul_pb_cumul_propE _ _ Conv _ _ (cpi_eta_ext _ eq_refl)).

  (** ** Substitution and contexts *)

  (** The identity on [Prop], of type [Prop → Prop] ([rf_F]). *)
  Definition cpi_id : term := tLambda c1b_na (tSort sProp) (tRel 0).

  Lemma cpi_id_typed : rf_Σ ;;; [] |-E cpi_id : rf_F.
  Proof.
    have w : wf_localE rf_Σ ([] ,, vass c1b_na (tSort sProp)) := localenv_cons_abs localenv_nil (rf_P_vass [] localenv_nil).
    unfold cpi_id, rf_F. apply typeE_Lambda; [exact (rf_P_vass [] localenv_nil)|].
    exact (typeE_Rel _ _ 0 (vass c1b_na (tSort sProp)) w eq_refl).
  Qed.

  (** [λx:Prop. id x ~~ id]. *)
  Definition substitution_untyped_cumul_propE_inst :=
    @substitution_untyped_cumul_propE cf rf_Σ [] rf_Γ [] [cpi_id] rf_t (tRel 0) cpi_wfE
      eq_refl ltac:(repeat constructor) cpi_eta_cp.

  Lemma cpi_subslet : subsletE rf_Σ [] [cpi_id] rf_Γ.
  Proof. constructor; [constructor|exact cpi_id_typed]. Qed.

  Definition substitution_cumul_propE_inst :=
    @substitution_cumul_propE cf rf_Σ [] rf_Γ [] [cpi_id] rf_t (tRel 0) cpi_wfE cpi_subslet cpi_eta_cp.

  (** [Type₀] and [Type₁] substituted for one variable. *)
  Definition substitution_untyped_cumul_prop_equivE_inst :=
    @substitution_untyped_cumul_prop_equivE cf rf_Σ [] [vass cpi_na (tSort (Sort.super (Sort.super Sort.type0)))] []
      [tSort Sort.type0] [tSort (Sort.super Sort.type0)] (tRel 0) cpi_wfE
      eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
      (All2_cons (ltac:(constructor; reflexivity)) All2_nil).

  Definition substitution_red_terms_conv_propE_inst :=
    @substitution_red_terms_conv_propE cf rf_Σ [] [vass cpi_na (tSort (Sort.super sProp))] []
      [cpi_beta] [tSort sProp] (tRel 0) cpi_wf_extE eq_refl eq_refl ltac:(repeat constructor)
      (All2_cons (cpi_beta_red [] eq_refl) All2_nil).

  (** A context changed by β, a relation by η. *)
  Definition cpi_Fbeta : term := tApp (tLambda cpi_na (tSort sProp) (tRel 0)) rf_F.
  Definition cpi_ctx_beta : context := [vass c1b_na cpi_Fbeta].

  Lemma cpi_ctx_conv : ws_cumul_ctx_pbE Conv rf_Σ cpi_ctx_beta rf_Γ.
  Proof.
    constructor; [constructor|]. constructor; [reflexivity|].
    apply (red_ws_cumul_pbE (wfΣ := cpi_cb)).
    split; [reflexivity|reflexivity|]. apply red1_red. constructor.
  Qed.

  Lemma cpi_eta_beta_ctx : rf_Σ ;;; cpi_ctx_beta |-E rf_t ~~ tRel 0.
  Proof.
    apply (cumul_pb_cumul_propE _ _ Conv).
    apply (eta1_ws_cumul_pbE (wfΣ := cpi_cb)); [reflexivity|reflexivity|].
    exact (eta_red c1b_na (tRel 0) (tSort sProp)).
  Qed.

  Definition context_conversion_cumul_propE_inst : rf_Σ ;;; rf_Γ |-E rf_t ~~ tRel 0 :=
    context_conversion_cumul_propE (wfΣ := cpi_wf_extE) cpi_eta_beta_ctx cpi_ctx_conv.

  Definition substitution_untyped_cumul_prop_cumulE_inst :=
    @substitution_untyped_cumul_prop_cumulE cf rf_Σ rf_Γ [vass c1b_na rf_F] [vass c1b_na rf_F]
      [rf_t] [tRel 0] (tRel 0) cpi_wf_extE eq_refl eq_refl eq_refl
      ltac:(repeat constructor) ltac:(repeat constructor) (All2_cons cpi_eta_cp All2_nil).

  Definition substitution1_untyped_cumul_propE_inst :=
    @substitution1_untyped_cumul_propE cf rf_Σ [] c1b_na rf_F cpi_id rf_t (tRel 0) cpi_wfE eq_refl cpi_eta_cp.

End Generic.

(** ** The lemmas that take base's [Hcf : prop_sub_type = false] *)

Section NoPropSub.

  #[local] Existing Instance cpr_flags.

  Definition cumul_prop_propsE_inst : Sort.is_prop sProp :=
    @cumul_prop_propsE cpr_flags eq_refl rf_Σ [] sProp sProp cpi_wfE eq_refl
      (cpE_of_eq_term_prop eq_refl eq_refl eq_refl ltac:(reflexivity)).

  Definition is_propositional_bottomE_inst : Sort.is_propositional sProp :=
    @is_propositional_bottomE cpr_flags eq_refl rf_Σ [] cpi_beta sProp sProp cpi_wf_extE
      cpi_beta_cumul_Prop cpi_beta_cumul_Prop eq_refl.

  Definition is_prop_bottomE_inst : Sort.is_prop sProp :=
    @is_prop_bottomE cpr_flags eq_refl rf_Σ [] cpi_beta sProp sProp cpi_wf_extE
      cpi_beta_cumul_Prop cpi_beta_cumul_Prop eq_refl.

  (** [f (λx:Prop. f x) ~~ f f]. *)
  Definition cumul_prop_mkAppsE_inst :
    rf_Σ ;;; rf_Γ |-E mkApps (tRel 0) [rf_t] ~~ mkApps (tRel 0) [tRel 0] :=
    @cumul_prop_mkAppsE cpr_flags eq_refl rf_Σ rf_Γ (tRel 0) [rf_t] (tRel 0) [tRel 0] cpi_wf_extE
      eq_refl eq_refl eq_refl ltac:(reflexivity) (All2_cons cpi_eta_cp All2_nil).

  (** The η-typed variable ([tw_witness_typed]): the premises of [typing_leq_term_propE] and its
      conclusion, the conclusion proved without the lemma (which takes [ValForecastCopy16]). *)
  Lemma typing_leq_term_propE_inst :
    [× wfE tw_Σ.1, tw_Σ ;;; tw_Γ |-E tRel 0 : tw_Geta, on_udecl tw_Σ.1 tw_Σ.2,
       tw_Σ ;;; tw_Γ |-E tRel 0 : tw_GF, compare_term_napp tw_Σ tw_Σ Conv 0 (tRel 0) (tRel 0) &
       tw_Σ ;;; tw_Γ |-E tw_Geta ~~ tw_GF].
  Proof.
    have wfE0 : wfE tw_Σ.1 := wf_incl_E (@wf_empty_global_env cpr_flags).
    have cb := wfE_ClosedBodies tw_Σ.1 (wfΣ := wfE0).
    split; [exact wfE0|exact tw_x_Geta|exact cpr_on_udecl_empty|exact tw_x_GF|reflexivity|].
    apply (cumul_prop_symE _ _ _ _ wfE0).
    apply (cumul_pb_cumul_propE _ _ Cumul).
    apply (into_ws_cumul_pbE_spec tw_spec).
    - exact (typing_closed_contextE (wfΣ := wfE0) tw_x_GF).
    - exact (type_is_open_termE (wfΣ := wfE0) tw_x_GF).
    - exact (subject_is_open_termE (wfΣ := wfE0) tw_Geta_typed).
  Qed.

End NoPropSub.

(** ** Inductive spines and universe instances ([iu_Σ]: [I@{i} (A : Set) : Set], levels [a], [b]) *)

Section Inductives.

  #[local] Existing Instance default_checker_flags.

  Definition cpi_iu_wfE : wfE iu_Σ := wf_incl_E iu_wf.

  (** [I@{a} Set] and [I@{b} Set]: the instances differ at an [Irrelevant] universe. *)
  Lemma cpi_iu_eq : eq_term_prop iu_Σ 0 (mkApps (tInd iu_ind [iu_a]) [iu_Set]) (mkApps (tInd iu_ind [iu_b]) [iu_Set]).
  Proof.
    cbn. constructor; [|reflexivity]. constructor.
    cbn. left. constructor; [exact I|constructor].
  Qed.

  Definition eq_term_prop_mkApps_invE_inst :=
    @eq_term_prop_mkApps_invE default_checker_flags iu_Σ iu_ind [iu_a] [iu_Set] iu_ind [iu_b] [iu_Set]
      iu_wf_extE 0 cpi_iu_eq.

  (** [(λx:Type. x) Set]: a β step in an argument. *)
  Definition cpi_iu_beta : term := tApp (tLambda iu_na (tSort (Sort.super Sort.type0)) (tRel 0)) iu_Set.

  Lemma cpi_iu_spine :
    iu_Σ ;;; [] |-E mkApps (tInd iu_ind [iu_a]) [cpi_iu_beta] ~~ mkApps (tInd iu_ind [iu_b]) [iu_Set].
  Proof.
    apply (cumul_prop_transE _ _ _ (mkApps (tInd iu_ind [iu_a]) [iu_Set]) _ cpi_iu_wfE).
    - apply (red_cumul_propE (wfΣ := cpi_iu_wfE)).
      split; [reflexivity|reflexivity|]. apply red1_red. cbn. apply app_red_r. constructor.
    - apply cpE_of_eq_term_prop; [reflexivity|reflexivity|reflexivity|exact cpi_iu_eq].
  Qed.

  Definition cumul_prop_mkApps_Ind_invE_inst : All2 (cumul_propE iu_Σ []) [cpi_iu_beta] [iu_Set] :=
    cumul_prop_mkApps_Ind_invE (wfΣ := iu_wf_extE) cpi_iu_spine.

  Definition cmp_True_subst_instanceE_inst :=
    cmp_True_subst_instanceE iu_Σ iu_udecl [iu_a] [iu_b] [Level.lvar 0] cpi_iu_wfE
      (iu_consistent iu_a (or_introl eq_refl)) (iu_consistent iu_b (or_intror eq_refl)).

  Definition cmp_True_instanceE_inst :=
    cmp_True_instanceE iu_Σ iu_udecl [iu_a] [iu_b] cpi_iu_wfE
      (iu_consistent iu_a (or_introl eq_refl)) (iu_consistent iu_b (or_intror eq_refl)).

  (** [I@{a} ~~ I@{b}], from one instance pattern. *)
  Definition cumul_prop_subst_instanceE_inst :=
    @cumul_prop_subst_instanceE default_checker_flags iu_Σ [] iu_udecl [iu_a] [iu_b]
      (tInd iu_ind [Level.lvar 0]) cpi_iu_wfE eq_refl eq_refl
      (iu_consistent iu_a (or_introl eq_refl)) (iu_consistent iu_b (or_intror eq_refl)).

End Inductives.
