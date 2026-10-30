(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the lemmas of [PCUICCumulPropEta] (row T6)

  Each lemma family of [PCUICCumulPropEta] with a premise is applied here to concrete premises,
  each proved. NON-DEGENERATE: every instance tagged NONDEGEN rests on a non-trivial premise: an
  η step ([λx:Prop. f x] and [f] in the context [f : Prop → Prop], [cpi_eta]; [G (λy:Prop. F y)]
  and [G F] for the two [typing_leq_term_prop] rows), a β step ([cpi_beta], [cpi_redex]), two
  universe levels of one family, two different upper sorts of one term ([Prop] and [Type₀] in
  [cumul_sort_confluenceE_inst]), or two universe instances. The substitution rows: the three
  [cpi_id] rows substitute [id] for [f] in [λx:Prop. f x] and in [f] itself, whose result is
  [id]; [cpi_id_subst_nondeg] states that the result on [λx:Prop. f x] differs from
  [λx:Prop. f x] and from the result on [f]. The other three substitute into [∀y:Prop. g y]
  ([cpi_subst_body]) on both sides; their NONDEGEN lemmas state that each result differs from the
  substituted terms, and the two results from each other. The chains (transitivity and the two
  [cumul_pb] lemmas) pass through three pairwise distinct terms: [λx:Prop. f x], [f] and the
  β-redex [(λg. g) f] ([cpi_redex]). The rows that are degenerate by their statement are tagged
  IMPOSSIBLE at each instance, with the property of the statement that forces them: forced to
  [Prop]/[SProp] on both sides (the [cumul_*props*], [*_sort_eqE] and three [*_bottomE] rows), or
  compared by the constant relation [fun _ _ => True] (the two [cmp_True_*] rows).

  **[typing_leq_term_propE] and [typing_leq_term_prop_genE] are applied**, with no class (the
  forecast class [ValForecastCopy16] they took was deleted when copy 16 landed, frac/eta
  0fb43f10): [typing_leq_term_propE_inst] applies the first and [typing_leq_term_prop_genE_inst]
  the second (through [env_propE_typing]) to the η pair: the variable [x] typed at
  [G (λy:Prop. F y)] ([tw_x_Geta]) and at [G F] ([tw_x_GF]) ([PCUICCumulPropEtaRefutations],
  [tw_witness_typed]); the conclusion relates the two types, which are one η step apart.
  Both lemmas are in the section of [PCUICCumulPropEta] that carries base's section variable
  [Hcf : prop_sub_type = false]. Its reach:
  - [Hcf] is a binder in exactly base's position: [typing_leq_term_propE] takes [{cf} Hcf Σ …],
    as [PCUICCumulProp.typing_leq_term_prop] does; the two instances pass it at [cpr_flags]
    ([prop_sub_type = false], by [eq_refl]);
  - no checker root reaches the section: [git grep PCUICCumulProp] finds 0 files in
    [safechecker/] and [safechecker-plugin/] on each of the 33 fork [etak*] branches and on the
    landing head 96191b19 (2026-10-30);
  - the roots of the land3 gate (land3e, commit 96191b19, [roots_land3e.txt]) read 36/36/36/34
    axioms, the same bytes after the header as frac/eta's record ([roots_e3c21m3.txt], frac/eta
    b5e4d018).

  The flags: [cpr_flags] ([prop_sub_type = false]) where a lemma takes base's section variable
  [Hcf]; the default flags for [cumul_sort_confluenceE_inst] ([Prop ≤ Type₀] needs
  [prop_sub_type = true]) and the typed substitution; otherwise any flags.

  The two imported E lemmas are compared with the base-substituted statement in compiled form
  ([conv_sort_inv], [ws_cumul_pb_LetIn_l_inv_alt] with [wf] → [wfE], [wf_local] → [wf_localE],
  [⊢] → [⊢E]): the types are NOT identical, since ascription fails in both directions (the
  [Fail Check]s below); the landed lemmas inhabit the base-substituted types
  ([cpE_import_conv_sort_inv], [cpE_import_LetIn_l_inv_alt]), as they take fewer premises
  (no environment premise for [conv_sort_invE]; [ClosedBodies] and no [wf_localE] for the
  LetIn lemma). *)

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
From MetaRocq.PCUIC Require PCUICTypingEtaInd.

(** The declarations of this file that are neither instances nor nondegeneracy lemmas: the
    ascription witnesses of the imported lemmas and the [cpi_] environments, terms and steps.
    WITNESSES: cpE_import_* cpi_* *)

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

(** Both-way ascription fails: the landed types are not the base-substituted ones. *)
Fail Check (@conv_sort_invE : ltac:(let T := type of @cpE_import_conv_sort_inv in exact T)).
Fail Check (cpE_import_conv_sort_inv : ltac:(let T := type of @conv_sort_invE in exact T)).
Fail Check (@ws_cumul_pbE_LetIn_l_inv_alt : ltac:(let T := type of @cpE_import_LetIn_l_inv_alt in exact T)).
Fail Check (cpE_import_LetIn_l_inv_alt : ltac:(let T := type of @ws_cumul_pbE_LetIn_l_inv_alt in exact T)).

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
    cumul_pb_cumul_propE rf_Σ rf_Γ Conv rf_t (tRel 0) (cpi_eta Conv).

  (** The η pair: [λx:Prop. f x] is not [f], and contracts to [f] in one η step ([eta1]). *)
  Lemma cpi_eta_nondeg : (rf_t <> tRel 0) × eta1 rf_t (tRel 0).
  Proof.
    split; [intros h; vm_compute in h; discriminate h|].
    exact (eta_red c1b_na (tRel 0) (tSort sProp)).
  Qed.

  (** β: [(λx:Type. x) Prop ⇝ Prop]. *)
  Definition cpi_na : aname := mkBindAnn nAnon Relevant.
  Definition cpi_beta : term := tApp (tLambda cpi_na (tSort (Sort.super sProp)) (tRel 0)) (tSort sProp).

  Lemma cpi_beta_red Γ : is_closed_context Γ -> rf_Σ ;;; Γ ⊢ cpi_beta ⇝ tSort sProp.
  Proof. intros hΓ. split; [exact hΓ|reflexivity|]. apply red1_red. constructor. Qed.

  (** The β-redex [(λx:Type. x) Prop] is not the sort [Prop], and reduces to it in one [red1]
      step. *)
  Lemma cpi_beta_nondeg : (cpi_beta <> tSort sProp) × red1 rf_Σ [] cpi_beta (tSort sProp).
  Proof. split; [intros h; vm_compute in h; discriminate h|constructor]. Qed.

  (** A third term, one β step from [f]: [(λg:Prop → Prop. g) f]. *)
  Definition cpi_redex : term := tApp (tLambda cpi_na rf_F (tRel 0)) (tRel 0).

  Lemma cpi_redex_red : rf_Σ ;;; rf_Γ ⊢ cpi_redex ⇝ tRel 0.
  Proof. split; [reflexivity|reflexivity|]. apply red1_red. constructor. Qed.

  Definition cpi_redex_cp : rf_Σ ;;; rf_Γ |-E tRel 0 ~~ cpi_redex :=
    cpE_of_ws (red_ws_cumul_pbE_inv (wfΣ := cpi_cb) (pb := Conv) cpi_redex_red).

  Definition cpi_eta_redex_cp : rf_Σ ;;; rf_Γ |-E rf_t ~~ cpi_redex :=
    cpE_trans (wfΣ := cpi_cb) cpi_eta_cp cpi_redex_cp.

  (** The chain [λx:Prop. f x], [f], [(λg. g) f]: three pairwise distinct terms; the first
      contracts to [f] in one η step ([eta1]), and the β-redex [(λg. g) f] reduces to [f] in one
      [red1] step. *)
  Lemma cpi_chain_nondeg :
    [× rf_t <> tRel 0, tRel 0 <> cpi_redex, rf_t <> cpi_redex, eta1 rf_t (tRel 0)
     & red1 rf_Σ rf_Γ cpi_redex (tRel 0)].
  Proof.
    split.
    - intros h; vm_compute in h; discriminate h.
    - intros h; vm_compute in h; discriminate h.
    - intros h; vm_compute in h; discriminate h.
    - exact (eta_red c1b_na (tRel 0) (tSort sProp)).
    - constructor.
  Qed.

  (** ** Basic structure *)

  (** η: [λx:Prop. f x ~~ f], built by [cpi_eta_cp] from [cpi_eta].
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_eta_nondeg
      HELPER PCUICCumulPropEtaInstances.cpi_eta_cp *)
  Definition cumul_pb_cumul_propE_inst := cpi_eta_cp.

  (** The η pair, reversed.
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_eta_nondeg *)
  Definition cumul_prop_symE_inst : rf_Σ ;;; rf_Γ |-E tRel 0 ~~ rf_t :=
    cumul_prop_symE rf_Σ rf_Γ rf_t (tRel 0) cpi_wfE cpi_eta_cp.

  (** [λx:Prop. f x ~~ f ~~ (λg. g) f]: an η step, then a β step.
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_chain_nondeg *)
  Definition cumul_prop_transE_inst : rf_Σ ;;; rf_Γ |-E rf_t ~~ cpi_redex :=
    cumul_prop_transE rf_Σ rf_Γ rf_t (tRel 0) cpi_redex cpi_wfE cpi_eta_cp cpi_redex_cp.

  (** The same chain, through the [Transitive] instance.
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_chain_nondeg *)
  Definition cumul_prop_transitiveE_inst : rf_Σ ;;; rf_Γ |-E rf_t ~~ cpi_redex :=
    @cumul_prop_transitiveE cf rf_Σ rf_Γ cpi_wfE rf_t (tRel 0) cpi_redex cpi_eta_cp cpi_redex_cp.

  (** The η pair, reversed through the [Symmetric] instance.
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_eta_nondeg *)
  Definition cumul_prop_sym'E_inst : rf_Σ ;;; rf_Γ |-E tRel 0 ~~ rf_t :=
    @cumul_prop_sym'E cf rf_Σ rf_Γ cpi_wfE rf_t (tRel 0) cpi_eta_cp.

  (** The scoping of the η pair.
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_eta_nondeg *)
  Definition cumul_prop_is_openE_inst := cumul_prop_is_openE (T := rf_t) (U := tRel 0) cpi_eta_cp.

  (** [λx:Prop. f x ~~ (λg. g) f] and [λx:Prop. f x ≤ f] give [f ~~ (λg. g) f].
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_chain_nondeg *)
  Definition cumul_prop_cumul_pb_lE_inst : rf_Σ ;;; rf_Γ |-E tRel 0 ~~ cpi_redex :=
    cumul_prop_cumul_pb_lE (wfΣ := cpi_wf_extE) (A := rf_t) (T := cpi_redex) (B := tRel 0)
      cpi_eta_redex_cp (cpi_eta Cumul).

  (** [f ~~ (λg. g) f] and [λx:Prop. f x ≤ f] give [λx:Prop. f x ~~ (λg. g) f].
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_chain_nondeg *)
  Definition cumul_prop_cum_pb_rE_inst : rf_Σ ;;; rf_Γ |-E rf_t ~~ cpi_redex :=
    cumul_prop_cum_pb_rE (wfΣ := cpi_wf_extE) (A := tRel 0) (T := cpi_redex) (B := rf_t)
      cpi_redex_cp (cpi_eta Cumul).

  Lemma cpi_Prop_red_refl : rf_Σ ;;; [] ⊢ tSort sProp ⇝ tSort sProp.
  Proof. split; [reflexivity|reflexivity|]. apply rt_refl. Qed.

  Lemma cpi_Prop_eq : eq_term_prop rf_Σ 0 (tSort sProp) (tSort sProp).
  Proof. constructor. reflexivity. Qed.

  Lemma cpi_beta_reducts : ∑ nf nf', [× rf_Σ ;;; [] ⊢ cpi_beta ⇝ nf, rf_Σ ;;; [] ⊢ tSort sProp ⇝ nf'
                                        & eq_term_prop rf_Σ 0 nf nf'].
  Proof.
    exists (tSort sProp), (tSort sProp).
    split; [exact (cpi_beta_red [] eq_refl)|exact cpi_Prop_red_refl|exact cpi_Prop_eq].
  Qed.

  (** β: [(λx:Type. x) Prop ~~ Prop], from reducts of the two sides related by [eq_term_prop]
      ([cpi_beta_reducts]).
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_beta_nondeg *)
  Definition into_cumul_propE_red_inst : rf_Σ ;;; [] |-E cpi_beta ~~ tSort sProp :=
    into_cumul_propE_red (T := cpi_beta) (U := tSort sProp) cpi_beta_reducts.

  (** β, from the reduction.
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_beta_nondeg *)
  Definition red_cumul_propE_inst : rf_Σ ;;; [] |-E cpi_beta ~~ tSort sProp :=
    red_cumul_propE (wfΣ := cpi_wfE) cpi_beta (tSort sProp) (cpi_beta_red [] eq_refl).

  (** β, from the reduction, under [wf_extE].
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_beta_nondeg *)
  Definition red_conv_propE_inst : rf_Σ ;;; [] |-E cpi_beta ~~ tSort sProp :=
    red_conv_propE (wfΣ := cpi_wf_extE) (T := cpi_beta) (U := tSort sProp) (cpi_beta_red [] eq_refl).

  (** ** Sorts *)

  (** [Type₀] and [Type₁]: one family, two levels. *)
  Lemma cpi_type01 : rf_Σ ;;; [] |-E tSort Sort.type0 ~~ tSort (Sort.super Sort.type0).
  Proof. apply cpE_of_eq_term_prop; try reflexivity. constructor. reflexivity. Qed.

  (** The two levels differ. *)
  Lemma cpi_type01_nondeg : Sort.type0 <> Sort.super Sort.type0.
  Proof. intros h; vm_compute in h; discriminate h. Qed.

  (** [Type₀ ~~ Type₁] gives their family comparison.
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_type01_nondeg *)
  Definition cumul_prop_sortE_inst : eq_univ_prop Sort.type0 (Sort.super Sort.type0) :=
    cumul_prop_sortE (wfΣ := cpi_wfE) (s := Sort.type0) (s' := Sort.super Sort.type0) cpi_type01.

  Lemma cpi_SProp_cp : rf_Σ ;;; [] |-E tSort sSProp ~~ tSort sSProp.
  Proof. apply cpE_of_eq_term_prop; [reflexivity|reflexivity|reflexivity|]. constructor. reflexivity. Qed.

  (** [SProp ~~ SProp]. The premise [Sort.is_sprop u] forces [u = SProp]; a [cumul_propE] between
      two sorts gives their family comparison ([cumul_prop_sortE]), so [u' = SProp] too.
      INSTANCE IMPOSSIBLE: every instance is at SProp on both sides (is_sprop u forces u, the sort comparison forces u') *)
  Definition cumul_sprop_propsE_inst : Sort.is_sprop sSProp :=
    cumul_sprop_propsE (wfΣ := cpi_wfE) (u := sSProp) eq_refl cpi_SProp_cp.

  Lemma cpi_beta_cumul_Prop : ws_cumul_pbE Cumul rf_Σ [] cpi_beta (tSort sProp).
  Proof. exact (red_ws_cumul_pbE (wfΣ := cpi_cb) (cpi_beta_red [] eq_refl)). Qed.

  Definition cpi_betaS : term := tApp (tLambda cpi_na (tSort (Sort.super sSProp)) (tRel 0)) (tSort sSProp).

  Lemma cpi_betaS_cumul_SProp : ws_cumul_pbE Cumul rf_Σ [] cpi_betaS (tSort sSProp).
  Proof.
    apply (red_ws_cumul_pbE (wfΣ := cpi_cb)).
    split; [reflexivity|reflexivity|]. apply red1_red. constructor.
  Qed.

  (** [(λx:Type. x) SProp] below [SProp], one bound derivation passed twice.
      INSTANCE IMPOSSIBLE: the statement forces s' = s = SProp (the two bounds share a sort below both, cumul_sort_confluenceE, and only SProp is below SProp, and SProp is below no other sort), so the conclusion is_sprop s' is the premise is_sprop s in every instance and environment *)
  Definition is_sprop_bottomE_inst : Sort.is_sprop sSProp :=
    is_sprop_bottomE (T := cpi_betaS) cpi_wf_extE cpi_betaS_cumul_SProp cpi_betaS_cumul_SProp eq_refl.

  (** [Prop = Prop].
      INSTANCE IMPOSSIBLE: the premises Sort.is_prop u and Sort.is_prop u' force u = u' = Prop, so the conclusion tSort u = tSort u' is reflexive in every instance *)
  Definition prop_sort_eqE_inst : rf_Σ ;;; [] ⊢E tSort sProp = tSort sProp :=
    @prop_sort_eqE cf rf_Σ [] sProp sProp eq_refl eq_refl eq_refl.

  (** [SProp = SProp].
      INSTANCE IMPOSSIBLE: the premises Sort.is_sprop u and Sort.is_sprop u' force u = u' = SProp, so the conclusion tSort u = tSort u' is reflexive in every instance *)
  Definition sprop_sort_eqE_inst : rf_Σ ;;; [] ⊢E tSort sSProp = tSort sSProp :=
    @sprop_sort_eqE cf rf_Σ [] sSProp sSProp eq_refl eq_refl eq_refl.

  (** ** Binders: the η pair under a product and under a let *)

  (** In [f : Prop → Prop, x : Prop]: [λy:Prop. f y] (written in the extended context) and [f]. *)
  Definition cpi_lam : term := tLambda cpi_na (tSort sProp) (tApp (tRel 2) (tRel 0)).

  Lemma cpi_eta_ext d : is_closed_context (rf_Γ ,, d) ->
    ws_cumul_pbE Conv rf_Σ (rf_Γ ,, d) cpi_lam (tRel 1).
  Proof.
    intros hΓ. apply (eta1_ws_cumul_pbE (Σ := rf_Σ)); [exact hΓ|reflexivity|].
    exact (eta_red cpi_na (tRel 1) (tSort sProp)).
  Qed.

  (** The η pair of the extended context: [λy:Prop. f y] is not [f], and contracts to [f] in one
      η step ([eta1]). *)
  Lemma cpi_lam_nondeg : (cpi_lam <> tRel 1) × eta1 cpi_lam (tRel 1).
  Proof.
    split; [intros h; vm_compute in h; discriminate h|].
    exact (eta_red cpi_na (tRel 1) (tSort sProp)).
  Qed.

  Definition cpi_ctx_vass : context := rf_Γ ,, vass cpi_na (tSort sProp).
  Definition cpi_ctx_vdef : context := rf_Γ ,, vdef cpi_na (tSort sProp) (tSort (Sort.super sProp)).

  Definition cpi_codom_cp : rf_Σ ;;; cpi_ctx_vass |-E cpi_lam ~~ tRel 1 :=
    cumul_pb_cumul_propE _ _ Conv _ _ (cpi_eta_ext (vass cpi_na (tSort sProp)) eq_refl).

  (** The η pair in the codomain of a product.
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_lam_nondeg *)
  Definition cumul_prop_tProdE_inst :
    rf_Σ ;;; rf_Γ |-E tProd cpi_na (tSort sProp) cpi_lam ~~ tProd cpi_na (tSort sProp) (tRel 1) :=
    cumul_prop_tProdE (wfΣ := cpi_wf_extE) (ty := cpi_lam) (ty' := tRel 1) eq_refl ltac:(reflexivity)
      cpi_codom_cp.

  (** The η pair, recovered from the products.
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_lam_nondeg *)
  Definition cumul_prop_prod_invE_inst : rf_Σ ;;; cpi_ctx_vass |-E cpi_lam ~~ tRel 1 :=
    cumul_prop_prod_invE (wfΣ := cpi_wfE) (B := cpi_lam) (B' := tRel 1) cumul_prop_tProdE_inst.

  (** The η pair in the body of a let.
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_lam_nondeg *)
  Definition cumul_prop_tLetInE_inst :
    rf_Σ ;;; rf_Γ |-E tLetIn cpi_na (tSort sProp) (tSort (Sort.super sProp)) cpi_lam
                    ~~ tLetIn cpi_na (tSort sProp) (tSort (Sort.super sProp)) (tRel 1) :=
    cumul_prop_tLetInE rf_Σ (wfΣ := cpi_wf_extE) eq_refl ltac:(reflexivity) ltac:(reflexivity)
      (cumul_pb_cumul_propE _ _ Conv cpi_lam (tRel 1)
         (cpi_eta_ext (vdef cpi_na (tSort sProp) (tSort (Sort.super sProp))) eq_refl)).

  (** ** Substitution and contexts *)

  (** The identity on [Prop], of type [Prop → Prop] ([rf_F]). *)
  Definition cpi_id : term := tLambda c1b_na (tSort sProp) (tRel 0).

  (** Substituting [id] for [f] changes [λx:Prop. f x], and the two sides stay distinct; the pair
      is one η step apart ([eta1]) before the substitution and after it. *)
  Lemma cpi_id_subst_nondeg :
    [× subst [cpi_id] 0 rf_t <> rf_t, subst [cpi_id] 0 rf_t <> subst [cpi_id] 0 (tRel 0),
       eta1 rf_t (tRel 0) & eta1 (subst [cpi_id] 0 rf_t) (subst [cpi_id] 0 (tRel 0))].
  Proof.
    split.
    - intros h; vm_compute in h; discriminate h.
    - intros h; vm_compute in h; discriminate h.
    - exact (eta_red c1b_na (tRel 0) (tSort sProp)).
    - exact (eta_red c1b_na cpi_id (tSort sProp)).
  Qed.

  (** [λx:Prop. id x ~~ id].
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_id_subst_nondeg *)
  Definition substitution_untyped_cumul_propE_inst :=
    @substitution_untyped_cumul_propE cf rf_Σ [] rf_Γ [] [cpi_id] rf_t (tRel 0) cpi_wfE
      eq_refl ltac:(repeat constructor) cpi_eta_cp.

  (** The body the substitution rows act on: [∀y:Prop. g y], where [g] is the substituted
      variable ([tRel 0] outside the binder). [g] sits under a binder, at the head of an
      application. *)
  Definition cpi_subst_body : term := tProd cpi_na (tSort sProp) (tApp (tRel 1) (tRel 0)).

  Lemma cpi_type01_eq : eq_term_prop rf_Σ.1 0 (tSort Sort.type0) (tSort (Sort.super Sort.type0)).
  Proof. constructor. reflexivity. Qed.

  (** [Type₀] and [Type₁] differ. Substituted for [g] in [∀y:Prop. g y], they give
      [∀y:Prop. Type₀ y] and [∀y:Prop. Type₁ y], which differ from both sorts and from each
      other. *)
  Lemma cpi_type01_subst_nondeg :
    [× Sort.type0 <> Sort.super Sort.type0,
       subst0 [tSort Sort.type0] cpi_subst_body <> tSort Sort.type0,
       subst0 [tSort Sort.type0] cpi_subst_body <> tSort (Sort.super Sort.type0),
       subst0 [tSort (Sort.super Sort.type0)] cpi_subst_body <> tSort Sort.type0,
       subst0 [tSort (Sort.super Sort.type0)] cpi_subst_body <> tSort (Sort.super Sort.type0)
     & subst0 [tSort Sort.type0] cpi_subst_body <> subst0 [tSort (Sort.super Sort.type0)] cpi_subst_body].
  Proof. split; intros h; vm_compute in h; discriminate h. Qed.

  (** [Type₀] and [Type₁], related by [eq_term_prop] ([cpi_type01_eq]), substituted for [g] in
      [∀y:Prop. g y] ([cpi_subst_body]; the lemma asks for scoping, not typing). The results
      [∀y:Prop. Type₀ y] and [∀y:Prop. Type₁ y] differ from both sorts and from each other
      ([cpi_type01_subst_nondeg]).
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_type01_subst_nondeg *)
  Definition substitution_untyped_cumul_prop_equivE_inst :
    rf_Σ ;;; [] |-E subst0 [tSort Sort.type0] cpi_subst_body
                  ~~ subst0 [tSort (Sort.super Sort.type0)] cpi_subst_body :=
    @substitution_untyped_cumul_prop_equivE cf rf_Σ [] [vass cpi_na (tSort (Sort.super (Sort.super Sort.type0)))] []
      [tSort Sort.type0] [tSort (Sort.super Sort.type0)] cpi_subst_body cpi_wfE
      eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
      (All2_cons cpi_type01_eq All2_nil).

  (** The β-redex [(λx:Type. x) Prop] and its reduct [Prop]: they differ, and the first reduces to
      the second in one [red1] step. Substituted for [g] in [∀y:Prop. g y], they give
      [∀y:Prop. (λx:Type. x) Prop y] and [∀y:Prop. Prop y], which differ from both substituted terms
      and from each other; the first reduces to the second in one [red1] step (the β step at the
      head of the application, under the binder). *)
  Lemma cpi_beta_subst_nondeg :
    [× cpi_beta <> tSort sProp, red1 rf_Σ [] cpi_beta (tSort sProp),
       subst0 [cpi_beta] cpi_subst_body <> cpi_beta,
       subst0 [cpi_beta] cpi_subst_body <> tSort sProp,
       subst0 [tSort sProp] cpi_subst_body <> cpi_beta,
       subst0 [tSort sProp] cpi_subst_body <> tSort sProp,
       subst0 [cpi_beta] cpi_subst_body <> subst0 [tSort sProp] cpi_subst_body
     & red1 rf_Σ [] (subst0 [cpi_beta] cpi_subst_body) (subst0 [tSort sProp] cpi_subst_body)].
  Proof.
    split.
    - exact (fst cpi_beta_nondeg).
    - exact (snd cpi_beta_nondeg).
    - intros h; vm_compute in h; discriminate h.
    - intros h; vm_compute in h; discriminate h.
    - intros h; vm_compute in h; discriminate h.
    - intros h; vm_compute in h; discriminate h.
    - intros h; vm_compute in h; discriminate h.
    - vm_compute. apply PCUICReduction.prod_red_r. apply PCUICReduction.app_red_l. constructor.
  Qed.

  (** [(λx:Type. x) Prop] and its reduct [Prop] ([cpi_beta_red]), substituted for [g] in
      [∀y:Prop. g y] ([cpi_subst_body]; the lemma asks for scoping and the reduction, not typing).
      The results differ from both substituted terms and from each other, and are one [red1] step
      apart ([cpi_beta_subst_nondeg]).
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_beta_subst_nondeg *)
  Definition substitution_red_terms_conv_propE_inst :
    rf_Σ ;;; [] |-E subst0 [cpi_beta] cpi_subst_body ~~ subst0 [tSort sProp] cpi_subst_body :=
    @substitution_red_terms_conv_propE cf rf_Σ [] [vass cpi_na (tSort (Sort.super sProp))] []
      [cpi_beta] [tSort sProp] cpi_subst_body cpi_wf_extE eq_refl eq_refl ltac:(repeat constructor)
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
    apply (eta1_ws_cumul_pbE (Σ := rf_Σ)); [reflexivity|reflexivity|].
    exact (eta_red c1b_na (tRel 0) (tSort sProp)).
  Qed.

  (** The two contexts differ: the type [(λX:Prop. X) (Prop → Prop)] of the first's declaration
      reduces to the type [Prop → Prop] of the second's in one [red1] step. The two terms differ
      and are one η step apart ([eta1]). *)
  Lemma cpi_ctx_nondeg :
    [× cpi_ctx_beta <> rf_Γ, red1 rf_Σ [] cpi_Fbeta rf_F, rf_t <> tRel 0 & eta1 rf_t (tRel 0)].
  Proof.
    split.
    - intros h; vm_compute in h; discriminate h.
    - constructor.
    - intros h; vm_compute in h; discriminate h.
    - exact (eta_red c1b_na (tRel 0) (tSort sProp)).
  Qed.

  (** The η pair, moved from the β-context [f : (λX:Prop. X) (Prop → Prop)] to [f : Prop → Prop].
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_ctx_nondeg *)
  Definition context_conversion_cumul_propE_inst : rf_Σ ;;; rf_Γ |-E rf_t ~~ tRel 0 :=
    context_conversion_cumul_propE (wfΣ := cpi_wf_extE) (Γ := cpi_ctx_beta) (Δ := rf_Γ) (M := rf_t)
      (N := tRel 0) cpi_eta_beta_ctx cpi_ctx_conv.

  (** The terms substituted for [g], [λx:Prop. f x] and [f], differ and are one η step apart
      ([eta1]). The two declarations of [g] differ: the type [(λX:Prop. X) (Prop → Prop)] of the
      second reduces to the type [Prop → Prop] of the first in one [red1] step. The results of the
      substitutions into [∀y:Prop. g y], [∀y:Prop. (λx:Prop. f x) y] and [∀y:Prop. f y], differ
      from both substituted terms and from each other, and are one η step apart ([eta1]). *)
  Lemma cpi_subst_cumul_nondeg :
    [× rf_t <> tRel 0, eta1 rf_t (tRel 0), [vass c1b_na rf_F] <> [vass c1b_na cpi_Fbeta],
       red1 rf_Σ rf_Γ cpi_Fbeta rf_F,
       subst0 [rf_t] cpi_subst_body <> rf_t, subst0 [rf_t] cpi_subst_body <> tRel 0,
       subst0 [tRel 0] cpi_subst_body <> rf_t, subst0 [tRel 0] cpi_subst_body <> tRel 0,
       subst0 [rf_t] cpi_subst_body <> subst0 [tRel 0] cpi_subst_body
     & eta1 (subst0 [rf_t] cpi_subst_body) (subst0 [tRel 0] cpi_subst_body)].
  Proof.
    split.
    - intros h; vm_compute in h; discriminate h.
    - exact (eta_red c1b_na (tRel 0) (tSort sProp)).
    - intros h; vm_compute in h; discriminate h.
    - constructor.
    - intros h; vm_compute in h; discriminate h.
    - intros h; vm_compute in h; discriminate h.
    - intros h; vm_compute in h; discriminate h.
    - intros h; vm_compute in h; discriminate h.
    - intros h; vm_compute in h; discriminate h.
    - vm_compute. apply prod_eta_r. apply app_eta_l.
      exact (eta_red c1b_na (tRel 1) (tSort sProp)).
  Qed.

  (** [λx:Prop. f x] and [f] substituted for [g] in [∀y:Prop. g y] ([cpi_subst_body]), checked
      against two declarations of [g] whose types differ by β (the substitutions are
      [untyped_subslet]). The two results, [∀y:Prop. (λx:Prop. f x) y] and [∀y:Prop. f y], differ
      from both substituted terms and from each other ([cpi_subst_cumul_nondeg]).
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_subst_cumul_nondeg *)
  Definition substitution_untyped_cumul_prop_cumulE_inst :
    rf_Σ ;;; rf_Γ |-E subst0 [rf_t] cpi_subst_body ~~ subst0 [tRel 0] cpi_subst_body :=
    @substitution_untyped_cumul_prop_cumulE cf rf_Σ rf_Γ [vass c1b_na rf_F] [vass c1b_na cpi_Fbeta]
      [rf_t] [tRel 0] cpi_subst_body cpi_wf_extE eq_refl eq_refl eq_refl
      ltac:(repeat constructor) ltac:(repeat constructor) (All2_cons cpi_eta_cp All2_nil).

  (** [id] substituted for [f] in the η pair.
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_id_subst_nondeg *)
  Definition substitution1_untyped_cumul_propE_inst :=
    @substitution1_untyped_cumul_propE cf rf_Σ [] c1b_na rf_F cpi_id rf_t (tRel 0) cpi_wfE eq_refl cpi_eta_cp.

End Generic.

(** ** At the default flags of the [rf_] witnesses ([PCUICWsCumulEtaCtx]): the typed substitution,
    and the confluence of two sorts that [Prop ≤ Type₀] ([prop_sub_type = true]) makes distinct *)

Section DefaultFlags.

  #[local] Existing Instance default_checker_flags.

  Lemma cpi_id_typed : rf_Σ ;;; [] |-E cpi_id : rf_F.
  Proof.
    have w : wf_localE rf_Σ ([] ,, vass c1b_na (tSort sProp)) := localenv_cons_abs localenv_nil (rf_P_vass [] localenv_nil).
    unfold cpi_id, rf_F. apply typeE_Lambda; [exact (rf_P_vass [] localenv_nil)|].
    exact (typeE_Rel _ _ 0 (vass c1b_na (tSort sProp)) w eq_refl).
  Qed.

  Lemma cpi_subslet : subsletE rf_Σ [] [cpi_id] rf_Γ.
  Proof. apply cons_let_assE; [constructor|exact cpi_id_typed]. Qed.

  (** [id], typed at [Prop → Prop], substituted for [f] in the η pair.
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_id_subst_nondeg *)
  Definition substitution_cumul_propE_inst :=
    @substitution_cumul_propE default_checker_flags rf_Σ [] rf_Γ [] [cpi_id] rf_t (tRel 0) cpi_wfE cpi_subslet cpi_eta_cp.

  (** [(λx:Type. x) Prop] below [Type₀]: below [Prop], and [Prop ≤ Type₀]. *)
  Lemma cpi_beta_cumul_Type0 : ws_cumul_pbE Cumul rf_Σ [] cpi_beta (tSort Sort.type0).
  Proof.
    refine (ws_cumul_pbE_trans (wfΣ := cpi_cb) cpi_beta (tSort sProp) (tSort Sort.type0)
              cpi_beta_cumul_Prop _).
    apply ws_cumul_pbE_Sort; [reflexivity|exact eq_refl].
  Qed.

  (** [(λx:Type. x) Prop] below [Prop] and below [Type₀]: the common sort is [Prop].
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_confluence_nondeg *)
  Definition cumul_sort_confluenceE_inst :=
    cumul_sort_confluenceE (wfΣ := cpi_wfE) (A := cpi_beta) (u := sProp) (v := Sort.type0)
      cpi_beta_cumul_Prop cpi_beta_cumul_Type0.

  (** The term is the β-redex [(λx:Type. x) Prop]: it is not [Prop], and reduces to it in one
      [red1] step. Its two upper sorts [Prop] and [Type₀] differ. The sort the instance returns,
      below both, is [Prop]. *)
  Lemma cpi_confluence_nondeg :
    [× cpi_beta <> tSort sProp, red1 rf_Σ [] cpi_beta (tSort sProp), sProp <> Sort.type0
     & projT1 cumul_sort_confluenceE_inst = sProp].
  Proof.
    split.
    - exact (fst cpi_beta_nondeg).
    - exact (snd cpi_beta_nondeg).
    - discriminate.
    - destruct cumul_sort_confluenceE_inst as [v' hv']. cbn.
      destruct hv' as [_ [hle _]].
      destruct v' as [| |l]; [reflexivity|exfalso; exact hle|exfalso; exact hle].
  Qed.

End DefaultFlags.

(** ** The lemmas that take base's [Hcf : prop_sub_type = false] *)

Section NoPropSub.

  #[local] Existing Instance cpr_flags.

  Lemma cpi_Prop_cp : rf_Σ ;;; [] |-E tSort sProp ~~ tSort sProp.
  Proof. apply cpE_of_eq_term_prop; [reflexivity|reflexivity|reflexivity|]. constructor. reflexivity. Qed.

  (** [Prop ~~ Prop]. The premise [Sort.is_prop u] forces [u = Prop]; a [cumul_propE] between two
      sorts gives their family comparison ([cumul_prop_sortE]), which relates [Prop] only to [Prop]
      when [prop_sub_type = false] ([eq_univ_prop]), so [u' = Prop] too.
      INSTANCE IMPOSSIBLE: under the section premise Hcf : prop_sub_type = false, every instance is at Prop on both sides (is_prop u forces u = Prop; with Hcf the family comparison eq_univ_prop relates Prop only to Prop, so u' = Prop) *)
  Definition cumul_prop_propsE_inst : Sort.is_prop sProp :=
    @cumul_prop_propsE cpr_flags eq_refl rf_Σ [] sProp sProp cpi_wfE eq_refl cpi_Prop_cp.

  (** [(λx:Type. x) Prop] below [Prop], one bound derivation passed twice.
      INSTANCE IMPOSSIBLE: under the section premise Hcf : prop_sub_type = false, the statement forces s' = s (the two bounds share a sort below both, cumul_sort_confluenceE, and with Hcf a propositional sort is below and above only itself), so the conclusion is_propositional s' is the premise is_propositional s in every instance and environment *)
  Definition is_propositional_bottomE_inst : Sort.is_propositional sProp :=
    @is_propositional_bottomE cpr_flags eq_refl rf_Σ [] cpi_beta sProp sProp cpi_wf_extE
      cpi_beta_cumul_Prop cpi_beta_cumul_Prop eq_refl.

  (** The same, for [Sort.is_prop].
      INSTANCE IMPOSSIBLE: under the section premise Hcf : prop_sub_type = false, the statement forces s' = s (the two bounds share a sort below both, cumul_sort_confluenceE, and with Hcf Prop is below and above only itself), so the conclusion is_prop s' is the premise is_prop s in every instance and environment *)
  Definition is_prop_bottomE_inst : Sort.is_prop sProp :=
    @is_prop_bottomE cpr_flags eq_refl rf_Σ [] cpi_beta sProp sProp cpi_wf_extE
      cpi_beta_cumul_Prop cpi_beta_cumul_Prop eq_refl.

  (** [f (λx:Prop. f x) ~~ f f].
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_eta_nondeg *)
  Definition cumul_prop_mkAppsE_inst :
    rf_Σ ;;; rf_Γ |-E mkApps (tRel 0) [rf_t] ~~ mkApps (tRel 0) [tRel 0] :=
    @cumul_prop_mkAppsE cpr_flags eq_refl rf_Σ rf_Γ (tRel 0) [rf_t] (tRel 0) [tRel 0] cpi_wf_extE
      eq_refl eq_refl eq_refl ltac:(reflexivity) (All2_cons cpi_eta_cp All2_nil).

  (** The two types of [x]: [G (λy:Prop. F y)] is not [G F], and contracts to it in one η step
      inside the argument of [G] ([eta1]). *)
  Lemma cpi_tw_nondeg : (tw_Geta <> tw_GF) × eta1 tw_Geta tw_GF.
  Proof.
    split; [intros h; vm_compute in h; discriminate h|].
    unfold tw_Geta, tw_GF. apply app_eta_r. exact (eta_red tw_na (tRel 1) tw_P).
  Qed.

  (** [typing_leq_term_propE], applied to the η-typed variable ([tw_witness_typed]): [x] at
      [G (λy:Prop. F y)] and at [G F], compared with itself; the conclusion relates the two types.
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_tw_nondeg *)
  Lemma typing_leq_term_propE_inst : tw_Σ ;;; tw_Γ |-E tw_Geta ~~ tw_GF.
  Proof.
    have wfE0 : wfE tw_Σ.1 := wf_incl_E (@wf_empty_global_env cpr_flags).
    apply (@typing_leq_term_propE cpr_flags eq_refl tw_Σ tw_Γ (tRel 0) (tRel 0) tw_Geta tw_GF wfE0
             tw_x_Geta cpr_on_udecl_empty tw_x_GF Conv 0).
    reflexivity.
  Qed.

  (** [typing_leq_term_prop_genE], applied through [env_propE_typing] to the same pair.
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_tw_nondeg *)
  Lemma typing_leq_term_prop_genE_inst : tw_Σ ;;; tw_Γ |-E tw_Geta ~~ tw_GF.
  Proof.
    have wfE0 : wfE tw_Σ.1 := wf_incl_E (@wf_empty_global_env cpr_flags).
    apply (@PCUICTypingEtaInd.env_propE_typing cpr_flags _ _ _ (@typing_leq_term_prop_genE cpr_flags eq_refl)
             tw_Σ wfE0 tw_Γ (tRel 0) tw_Geta tw_x_Geta (tRel 0) tw_GF cpr_on_udecl_empty tw_x_GF Conv 0).
    reflexivity.
  Qed.

End NoPropSub.

(** ** Inductive spines and universe instances ([iu_Σ]: [I@{i} (A : Set) : Set], levels [a], [b]) *)

Section Inductives.

  #[local] Existing Instance default_checker_flags.

  Definition cpi_iu_wfE : wfE iu_Σ := wf_incl_E iu_wf.

  (** The two universe levels differ, and so do the instances of [I@{i}] at [a] and at [b]. *)
  Lemma cpi_iu_levels_nondeg :
    iu_a <> iu_b /\
    subst_instance [iu_a] (tInd iu_ind [Level.lvar 0]) <> subst_instance [iu_b] (tInd iu_ind [Level.lvar 0]).
  Proof. split; intros h; vm_compute in h; discriminate h. Qed.

  (** [I@{a} Set] and [I@{b} Set]: the instances differ at an [Irrelevant] universe. *)
  Lemma cpi_iu_eq : eq_term_prop iu_Σ 0 (mkApps (tInd iu_ind [iu_a]) [iu_Set]) (mkApps (tInd iu_ind [iu_b]) [iu_Set]).
  Proof.
    cbn. constructor; [|reflexivity]. constructor.
    cbn. left. constructor; [exact I|constructor].
  Qed.

  (** [I@{a} Set] and [I@{b} Type₁]: the instances differ, and so do the arguments
      ([eq_term_prop] compares two sorts by their family). *)
  Lemma cpi_iu_eq01 : eq_term_prop iu_Σ 0 (mkApps (tInd iu_ind [iu_a]) [iu_Set])
                        (mkApps (tInd iu_ind [iu_b]) [tSort (Sort.super Sort.type0)]).
  Proof.
    cbn. constructor.
    - constructor. cbn. left. constructor; [exact I|constructor].
    - unfold iu_Set. constructor. reflexivity.
  Qed.

  (** The universe instances differ, and so do the arguments. *)
  Lemma cpi_iu_args_nondeg : iu_a <> iu_b /\ iu_Set <> tSort (Sort.super Sort.type0).
  Proof. split; intros h; vm_compute in h; discriminate h. Qed.

  (** The arguments [Set] and [Type₁] of [I@{a} Set ≈ I@{b} Type₁].
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_iu_args_nondeg *)
  Definition eq_term_prop_mkApps_invE_inst :=
    @eq_term_prop_mkApps_invE default_checker_flags iu_Σ iu_ind [iu_a] [iu_Set] iu_ind [iu_b]
      [tSort (Sort.super Sort.type0)] iu_wf_extE 0 cpi_iu_eq01.

  (** [cpE_of_eq_term_prop] on [I@{a} Set] and [I@{b} Type₁], related by [eq_term_prop]
      ([cpi_iu_eq01]): the two terms are not the same, since their universe instances differ and
      their arguments differ ([cpi_iu_args_nondeg]).
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_iu_args_nondeg *)
  Definition cpE_of_eq_term_prop_inst :
    iu_Σ ;;; [] |-E mkApps (tInd iu_ind [iu_a]) [iu_Set]
                   ~~ mkApps (tInd iu_ind [iu_b]) [tSort (Sort.super Sort.type0)] :=
    cpE_of_eq_term_prop (Σ := iu_Σ) (Γ := []) (t := mkApps (tInd iu_ind [iu_a]) [iu_Set])
      (u := mkApps (tInd iu_ind [iu_b]) [tSort (Sort.super Sort.type0)]) eq_refl eq_refl eq_refl
      cpi_iu_eq01.

  (** [(λx:Type. x) Set]: a β step in an argument. *)
  Definition cpi_iu_beta : term := tApp (tLambda iu_na (tSort (Sort.super Sort.type0)) (tRel 0)) iu_Set.

  Lemma cpi_iu_spine :
    iu_Σ ;;; [] |-E mkApps (tInd iu_ind [iu_a]) [cpi_iu_beta] ~~ mkApps (tInd iu_ind [iu_b]) [iu_Set].
  Proof.
    apply (cumul_prop_transE _ _ _ (mkApps (tInd iu_ind [iu_a]) [iu_Set]) _ cpi_iu_wfE).
    - apply (red_cumul_propE (wfΣ := cpi_iu_wfE)).
      split; [reflexivity|reflexivity|]. apply red1_red. cbn. apply PCUICReduction.app_red_r. constructor.
    - apply cpE_of_eq_term_prop; [reflexivity|reflexivity|reflexivity|exact cpi_iu_eq].
  Qed.

  (** The argument is the β-redex [(λx:Type. x) Set]: it is not [Set], and reduces to it in one
      [red1] step. The universe instances differ. *)
  Lemma cpi_iu_spine_nondeg :
    [× cpi_iu_beta <> iu_Set, red1 iu_Σ [] cpi_iu_beta iu_Set & iu_a <> iu_b].
  Proof.
    split.
    - intros h; vm_compute in h; discriminate h.
    - constructor.
    - intros h; vm_compute in h; discriminate h.
  Qed.

  (** The arguments of [I@{a} ((λx:Type. x) Set) ~~ I@{b} Set].
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_iu_spine_nondeg *)
  Definition cumul_prop_mkApps_Ind_invE_inst : All2 (cumul_propE iu_Σ []) [cpi_iu_beta] [iu_Set] :=
    cumul_prop_mkApps_Ind_invE (wfΣ := iu_wf_extE) (u := [iu_a]) (u' := [iu_b])
      (args := [cpi_iu_beta]) (args' := [iu_Set]) cpi_iu_spine.

  (** The instances [a] and [b], substituted into [i].
      INSTANCE IMPOSSIBLE: the compared relation is fun _ _ => True, so the conclusion holds of every pair of instances the premises admit (both sides are subst_instance of the same i, of length #|i|), in every environment *)
  Definition cmp_True_subst_instanceE_inst :=
    cmp_True_subst_instanceE iu_Σ iu_udecl [iu_a] [iu_b] [Level.lvar 0] cpi_iu_wfE
      (iu_consistent iu_a (or_introl eq_refl)) (iu_consistent iu_b (or_intror eq_refl)).

  (** The instances [a] and [b].
      INSTANCE IMPOSSIBLE: the compared relation is fun _ _ => True, so the conclusion holds of every pair of instances the premises admit (the consistent_instance_ext premises force equal length), in every environment *)
  Definition cmp_True_instanceE_inst :=
    cmp_True_instanceE iu_Σ iu_udecl [iu_a] [iu_b] cpi_iu_wfE
      (iu_consistent iu_a (or_introl eq_refl)) (iu_consistent iu_b (or_intror eq_refl)).

  (** [I@{a} ~~ I@{b}], from one instance pattern.
      INSTANCE NONDEGEN PCUICCumulPropEtaInstances.cpi_iu_levels_nondeg *)
  Definition cumul_prop_subst_instanceE_inst :=
    @cumul_prop_subst_instanceE default_checker_flags iu_Σ [] iu_udecl [iu_a] [iu_b]
      (tInd iu_ind [Level.lvar 0]) cpi_iu_wfE eq_refl eq_refl
      (iu_consistent iu_a (or_introl eq_refl)) (iu_consistent iu_b (or_intror eq_refl)).

End Inductives.
