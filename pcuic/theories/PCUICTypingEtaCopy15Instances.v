(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the hypotheses of [PCUICSpineEta]

  Each lemma of [PCUICSpineEta] that has a premise is applied here to a concrete instance
  with every premise proved. The environments:
  - [rf_Σ] of [PCUICWsCumulEtaCtx] (the empty environment) with the context
    [k_Γ := [a : G F; G : (Prop → Prop) → Prop; F : Prop → Prop]] (below). In it
    [k_T := G (λy:Prop. F y)] and [k_U := G F] are related by one η step and by no
    reduction or syntactic comparison ([wc_T_normal], [wc_U_normal], [wc_not_compare] of
    [PCUICSubstitutionEta], lifted over [a]); [a : G F] is retyped at [k_T] through that step
    ([k_a_T]). The spines, substitutions, context relations and conversions of the
    instances below go through this step.
  - [si_Σ] of [PCUICCumulativitySpecEtaClosureInstances] ([Inductive I (A : Prop) : Prop :=
    c : I A]) with the kits of [PCUICTypingEtaCopies2Instances], for the substitution and
    let-in instances.
  - [up_env] of [PCUICTypingEtaCopies2Instances] (a universe-polymorphic axiom
    [T@{l0} : Type@{l0}]) for the two universe-instantiation lemmas, at the instance [Set],
    which changes [Type@{l0}] into [Type@{Set}].
  - the context [rf_Γ := [f : Prop → Prop]] of [PCUICWsCumulEtaCtx], in which [λx:Prop. f x]
    and [f] are related by one η step ([rf_premise]), for the instance-rewriting lemmas
    [OnOne2_ctx_instE], [All2_ctx_instE] and [ctx_inst_eq_contextE].
  No instance is marked WEAK: the two lemmas whose conclusion is an equality of substitutions
  ([spine_subst_inj_substE], [ctx_inst_sub_eqE]) are applied to derivations whose
  substitutions are not convertible, as checked by [Fail] next to each. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping uGraph.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICEquality PCUICCases PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICWeakeningEnv
     PCUICUnivSubst PCUICUnivSubstitutionConv PCUICWfUniverses PCUICClosedBodies PCUICContextSubst
     PCUICWellScopedCumulativity PCUICReduction PCUICSigmaCalculus PCUICContexts
     PCUICTypingEta PCUICTypingEtaInd PCUICClosedTypEta PCUICWeakeningEnvTypEta PCUICWeakeningTypEta
     PCUICTypingEtaNotions PCUICUnivSubstitutionTypEta PCUICSubstitutionEta PCUICContextsEta
     PCUICAritiesEta PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICContextConversionEta
     PCUICWsCumulEtaSubst PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp PCUICEtaC1b
     PCUICCumulativitySpecEtaClosureInstances PCUICTypingEtaCopies1Instances PCUICEtaFracInstances
     PCUICWsCumulEtaCtxInstances PCUICTypingEtaCopies2Instances PCUICSpineEta.
From Equations.Prop Require Import DepElim.

#[local] Existing Instance default_checker_flags.

(** ** The η kit in [rf_Σ] *)

Definition k_Γ : context := wc_Γ ,, vass c1b_na wc_U.
Definition k_T : term := lift0 1 wc_T.
Definition k_U : term := lift0 1 wc_U.
Definition k_cb : ClosedBodies rf_Σ := @wfE_ClosedBodies _ rf_Σ wc_wfE.
#[local] Existing Instance k_cb.

Lemma k_vass (Γ : context) T : rf_Σ ;;; Γ |-E T : tSort sProp -> lift_typing typingE rf_Σ Γ (j_vass c1b_na T).
Proof. intros h. split; [exact tt|]. exists sProp. split; [exact h|]. split; [exact I|reflexivity]. Qed.

Lemma k_vass_s (Γ : context) T : rf_Σ ;;; Γ |-E T : tSort sProp ->
  lift_typing typingE rf_Σ Γ (j_vass_s c1b_na T sProp).
Proof. intros h. split; [exact tt|]. exists sProp. split; [exact h|]. split; reflexivity. Qed.

Lemma k_wf_Γ : wf_localE rf_Σ k_Γ.
Proof. apply localenv_cons_abs; [exact wc_wf_Γ|exact (k_vass wc_Γ wc_U wc_U_typed)]. Qed.

Lemma k_lift_typed {t} : rf_Σ ;;; wc_Γ |-E t : tSort sProp -> rf_Σ ;;; k_Γ |-E lift0 1 t : tSort sProp.
Proof. intros h. exact (weakeningE rf_Σ wc_Γ [vass c1b_na wc_U] t (tSort sProp) wc_wfE k_wf_Γ h). Qed.

Definition k_T_typed : rf_Σ ;;; k_Γ |-E k_T : tSort sProp := k_lift_typed wc_T_typed.
Definition k_U_typed : rf_Σ ;;; k_Γ |-E k_U : tSort sProp := k_lift_typed wc_U_typed.
Lemma k_isT_T : isTypeE rf_Σ k_Γ k_T. Proof. exact (has_sort_isTypeE _ k_T_typed). Qed.
Lemma k_isT_U : isTypeE rf_Σ k_Γ k_U. Proof. exact (has_sort_isTypeE _ k_U_typed). Qed.
Lemma k_isT_Prop : isTypeE rf_Σ k_Γ (tSort sProp). Proof. exact (isType_SortE rf_wf_sort k_wf_Γ). Qed.

Lemma k_closed : is_closed_context k_Γ.
Proof. exact (wf_local_closed_contextE (Σ := rf_Σ) (wfΣ := wc_wfE) k_wf_Γ). Qed.

(** The η step [G (λy:Prop. F y) ≡ G F], under [a]. *)
Lemma k_η pb : ws_cumul_pbE pb rf_Σ k_Γ k_T k_U.
Proof. exact (weakening_ws_cumul_pbE (Γ := wc_Γ) (Γ' := []) (Γ'' := [vass c1b_na wc_U]) (c2_wc_ws pb) k_closed). Qed.

Lemma k_η_sym pb : ws_cumul_pbE pb rf_Σ k_Γ k_U k_T.
Proof. exact (ws_cumul_pbE_sym_pb (k_η Conv)). Qed.

Lemma k_a_U : rf_Σ ;;; k_Γ |-E tRel 0 : k_U.
Proof. exact (typeE_Rel _ _ 0 (vass c1b_na wc_U) k_wf_Γ eq_refl). Qed.

(** [a : G F] retyped at [G (λy:Prop. F y)], through the η step only. *)
Lemma k_a_T : rf_Σ ;;; k_Γ |-E tRel 0 : k_T.
Proof. exact (type_ws_cumul_pbE k_U k_a_U k_isT_T (k_η_sym Cumul)). Qed.

(** The one-variable telescopes [x : G (λy:Prop. F y)] and [x : G F]. *)
Definition k_Δ : context := [vass c1b_na k_T].
Definition k_Δ' : context := [vass c1b_na k_U].

Lemma k_wf_ΓΔ : wf_localE rf_Σ (k_Γ ,,, k_Δ).
Proof. apply localenv_cons_abs; [exact k_wf_Γ|exact (k_vass k_Γ k_T k_T_typed)]. Qed.
Lemma k_wf_ΓΔ' : wf_localE rf_Σ (k_Γ ,,, k_Δ').
Proof. apply localenv_cons_abs; [exact k_wf_Γ|exact (k_vass k_Γ k_U k_U_typed)]. Qed.

Lemma k_rel pb : ws_cumul_ctx_pbE_rel pb rf_Σ k_Γ k_Δ k_Δ'.
Proof. split; [exact k_closed|]. constructor; [constructor|]. constructor; [reflexivity|exact (k_η pb)]. Qed.
Lemma k_rel_sym pb : ws_cumul_ctx_pbE_rel pb rf_Σ k_Γ k_Δ' k_Δ.
Proof. split; [exact k_closed|]. constructor; [constructor|]. constructor; [reflexivity|exact (k_η_sym pb)]. Qed.

Lemma k_sub_T : subsletE rf_Σ k_Γ [tRel 0] k_Δ. Proof. exact (subslet_ass_tipE k_a_T). Qed.
Lemma k_sub_U : subsletE rf_Σ k_Γ [tRel 0] k_Δ'. Proof. exact (subslet_ass_tipE k_a_U). Qed.

Lemma k_cs T : context_subst [vass c1b_na T] [tRel 0] [tRel 0].
Proof. exact (context_subst_ass [] [] [] c1b_na T (tRel 0) context_subst_nil). Qed.

(** [x := a] for [x : G (λy:Prop. F y)]: the substitution types [a : G F] through η. *)
Definition k_sp_T : spine_substE rf_Σ k_Γ [tRel 0] [tRel 0] k_Δ :=
  {| spine_dom_wfE := k_wf_Γ; spine_codom_wfE := k_wf_ΓΔ; inst_ctx_substE := k_cs k_T;
     inst_subsletE := k_sub_T |}.
Definition k_sp_U : spine_substE rf_Σ k_Γ [tRel 0] [tRel 0] k_Δ' :=
  {| spine_dom_wfE := k_wf_Γ; spine_codom_wfE := k_wf_ΓΔ'; inst_ctx_substE := k_cs k_U;
     inst_subsletE := k_sub_U |}.

Lemma k_ci : ctx_instE rf_Σ k_Γ [tRel 0] k_Δ.
(* Transparent: [ctx_inst_subE k_ci] computes to [[tRel 0]] below. *)
Proof. constructor; [exact k_a_T|constructor]. Defined.

(** The products [Π x : G (λy:Prop. F y). Prop] and [Π x : G F. Prop]. *)
Definition k_PT : term := tProd c1b_na k_T (tSort sProp).
Definition k_PU : term := tProd c1b_na k_U (tSort sProp).

Lemma k_PT_typed : rf_Σ ;;; k_Γ |-E k_PT : tSort (Sort.sort_of_product sProp (Sort.super sProp)).
Proof. apply typeE_Prod; [exact (k_vass_s k_Γ k_T k_T_typed)|exact (rf_P_typed _ k_wf_ΓΔ)]. Qed.
Lemma k_PU_typed : rf_Σ ;;; k_Γ |-E k_PU : tSort (Sort.sort_of_product sProp (Sort.super sProp)).
Proof. apply typeE_Prod; [exact (k_vass_s k_Γ k_U k_U_typed)|exact (rf_P_typed _ k_wf_ΓΔ')]. Qed.
Lemma k_isT_PT : isTypeE rf_Σ k_Γ k_PT. Proof. exact (has_sort_isTypeE _ k_PT_typed). Qed.
Lemma k_isT_PU : isTypeE rf_Σ k_Γ k_PU. Proof. exact (has_sort_isTypeE _ k_PU_typed). Qed.

Lemma k_PT_η pb : ws_cumul_pbE pb rf_Σ k_Γ k_PT k_PU.
Proof.
  apply ws_cumul_pbE_Prod; [reflexivity|exact (k_η Conv)|].
  apply ws_cumul_pbE_refl; [exact (wf_local_closed_contextE (Σ := rf_Σ) (wfΣ := wc_wfE) k_wf_ΓΔ)|reflexivity].
Qed.

Lemma k_sp_Prop : typing_spineE rf_Σ k_Γ (tSort sProp) [] (tSort sProp).
Proof.
  apply type_spine_nilE; [exact k_isT_Prop|exact k_isT_Prop|].
  exact (isType_ws_cumul_pbE_refl (wfΣ := wc_wfE) _ _ k_isT_Prop).
Qed.

(** The spine [Π x : G (λy:Prop. F y). Prop] applied to [a : G F]: its head comparison and
    its argument go through the η step. *)
Lemma k_spη : typing_spineE rf_Σ k_Γ k_PT [tRel 0] (tSort sProp).
Proof. eapply type_spine_consE; [exact k_isT_PT|exact k_isT_PU|exact (k_PT_η Cumul)|exact k_a_U|exact k_sp_Prop]. Qed.

(** [λx : G (λy:Prop. F y). G (λy:Prop. F y)], of type [k_PT]. *)
Definition k_t : term := tLambda c1b_na k_T (lift0 1 k_T).
Lemma k_t_typed : rf_Σ ;;; k_Γ |-E k_t : k_PT.
Proof.
  apply typeE_Lambda; [exact (k_vass k_Γ k_T k_T_typed)|].
  exact (weakeningE rf_Σ k_Γ k_Δ k_T (tSort sProp) wc_wfE k_wf_ΓΔ k_T_typed).
Qed.

(** The η step weakened by one more variable [w], and its typing. *)
Lemma k_η_up pb (d : context_decl) : is_closed_context (k_Γ ,, d) ->
  ws_cumul_pbE pb rf_Σ (k_Γ ,, d) (lift0 1 k_T) (lift0 1 k_U).
Proof. intros h. exact (weakening_ws_cumul_pbE (Γ := k_Γ) (Γ' := []) (Γ'' := [d]) (k_η pb) h). Qed.

Lemma k_T_typed_up (d : context_decl) : wf_localE rf_Σ (k_Γ ,, d) ->
  rf_Σ ;;; k_Γ ,, d |-E lift0 1 k_T : tSort sProp.
Proof. intros h. exact (weakeningE rf_Σ k_Γ [d] k_T (tSort sProp) wc_wfE h k_T_typed). Qed.
Lemma k_U_typed_up (d : context_decl) : wf_localE rf_Σ (k_Γ ,, d) ->
  rf_Σ ;;; k_Γ ,, d |-E lift0 1 k_U : tSort sProp.
Proof. intros h. exact (weakeningE rf_Σ k_Γ [d] k_U (tSort sProp) wc_wfE h k_U_typed). Qed.

(** [z : Prop] and [z := a : G F] on top of [k_Γ]. *)
Lemma k_wf_Γz : wf_localE rf_Σ (k_Γ ,, vass c1b_na (tSort sProp)).
Proof. apply localenv_cons_abs; [exact k_wf_Γ|exact (rf_P_vass k_Γ k_wf_Γ)]. Qed.
Lemma k_wf_Γlet : wf_localE rf_Σ (k_Γ ,, vdef c1b_na (tRel 0) k_U).
Proof.
  apply localenv_cons_def; [exact k_wf_Γ|].
  split; [exact k_a_U|]. exists sProp. split; [exact k_U_typed|]. split; reflexivity.
Qed.
Lemma k_closed_up {d} : wf_localE rf_Σ (k_Γ ,, d) -> is_closed_context (k_Γ ,, d).
Proof. exact (wf_local_closed_contextE (Σ := rf_Σ) (wfΣ := wc_wfE)). Qed.

(** ** Instances, in the order of [PCUICSpineEta] *)

Definition typing_spine_eqE_inst :=
  typing_spine_eqE rf_Σ k_Γ k_PT [tRel 0] [tRel 0] (tSort sProp) eq_refl k_spη.

(** [(λy:Prop. y) x ⇝ x] in [x : Prop], weakened by [z : Prop]. *)
Lemma k_cred : closed_red si_Σ fi_Γ1 (tApp ci_id (tRel 0)) (tRel 0).
Proof. split; [reflexivity|reflexivity|exact c2_red_id_x']. Qed.
Definition weakening_closed_redE_inst :=
  @weakening_closed_redE _ si_Σ si_wfE [] fi_Γ1 [vass si_na fi_P] _ _ k_cred eq_refl.

(** The telescope and the context with the binder [a] renamed. *)
Definition k_nx : aname := mkBindAnn (nNamed "x") Relevant.
Definition k_Δn : context := [vass k_nx k_T].
Definition k_Γn : context := wc_Γ ,, vass k_nx wc_U.
Lemma k_eq_Δn : eq_context_upto_names k_Δ k_Δn.
Proof. repeat constructor. Qed.
Lemma k_eq_Γn : eq_context_upto_names k_Γ k_Γn.
Proof. repeat constructor. Qed.
Lemma k_eq_ΓΔn : eq_context_upto_names (k_Γ ,,, k_Δ) (k_Γ ,,, k_Δn).
Proof. repeat constructor. Qed.

Definition subslet_eq_context_alphaE_inst := subslet_eq_context_alphaE k_eq_Δn k_sub_T.
Definition wf_local_alphaE_inst :=
  @wf_local_alphaE _ rf_Σ wc_wfE (k_Γ ,,, k_Δ) (k_Γ ,,, k_Δn) k_eq_ΓΔn k_wf_ΓΔ.
Definition subslet_eq_context_alpha_domE_inst :=
  @subslet_eq_context_alpha_domE _ rf_Σ wc_wfE k_Γ k_Γn _ _ k_eq_Γn k_sub_T.

(** [x := a, y := a] for [x : G (λy:Prop. F y), y : G F]. *)
Definition k_Δy : context := [vass c1b_na (lift0 1 k_U)].
Lemma k_sub_y : subsletE rf_Σ k_Γ [tRel 0] (subst_context [tRel 0] 0 k_Δy).
Proof. exact (subslet_ass_tipE k_a_U). Qed.
Definition subslet_appE_inst := subslet_appE rf_Σ k_Γ [tRel 0] [tRel 0] k_Δy k_Δ k_sub_y k_sub_T.
Definition subslet_skipnE_inst := subslet_skipnE rf_Σ k_Γ _ _ 1 subslet_appE_inst.

(** [x : Type@{l0} ⊢ x] instantiated at [Set]. *)
Definition k_up_Δ : context := [vass si_na (tSort up_s0)].
Lemma k_up_ci : ctx_instE up_Σp up_Γ [tRel 0] k_up_Δ.
Proof. constructor; [exact up_x_typed|constructor]. Qed.
Definition ctx_inst_instE_inst :=
  ctx_inst_instE up_Σm up_univs [Level.lzero] up_Γ [tRel 0] k_up_Δ up_global_ext k_up_ci up_cu.

Definition spine_subst_eqE_inst := spine_subst_eqE k_sp_T eq_refl.
(** [spine_subst_inj_substE]: its conclusion is Leibniz equality, so any two closed spines of
    one instance have equal substitutions; the witness equates two terms that are not
    convertible. One spine comes from an OPAQUE [ctx_inst] derivation through
    [ctx_inst_spine_substE] (substitution [ctx_inst_subE r_ci]), the other is [k_sp_T]
    (substitution [[tRel 0]]); [r_ci_not_refl] checks that [eq_refl] does not prove it. *)
Lemma r_ci : ctx_instE rf_Σ k_Γ [tRel 0] (List.rev k_Δ).
Proof. exact k_ci. Qed.
Definition spine_subst_inj_substE_inst : ctx_inst_subE r_ci = [tRel 0] :=
  spine_subst_inj_substE (ctx_inst_spine_substE (wfΣ := wc_wfE) k_wf_ΓΔ r_ci) k_sp_T.
Fail Definition r_ci_not_refl : ctx_inst_subE r_ci = [tRel 0] := eq_refl.

(** The η step under [x : G F], substituted by [x := a]. *)
Lemma k_η_Δ' pb : ws_cumul_pbE pb rf_Σ (k_Γ ,,, k_Δ' ,,, []) (lift0 1 k_T) (lift0 1 k_U).
Proof. exact (k_η_up pb (vass c1b_na k_U) (k_closed_up k_wf_ΓΔ')). Qed.
Definition substitution_ws_cumul_pbE_typed_inst :=
  @substitution_ws_cumul_pbE_typed _ rf_Σ wc_wfE Cumul k_Γ k_Δ' [] [tRel 0] _ _ k_sub_U (k_η_Δ' Cumul).

(** The empty spine at [G F], strengthened to [G (λy:Prop. F y)] by the η step. *)
Lemma k_sp_U_refl : typing_spineE rf_Σ k_Γ k_U [] k_U.
Proof. exact (@typing_spine_reflE _ rf_Σ wc_wfE k_Γ k_U k_isT_U). Qed.
Definition typing_spine_strengthenE_inst :=
  @typing_spine_strengthenE _ rf_Σ wc_wfE k_Γ k_U [] k_U k_sp_U_refl k_T k_isT_T (k_η Cumul).
Definition typing_spine_reflE_inst := @typing_spine_reflE _ rf_Σ wc_wfE k_Γ k_T k_isT_T.

(** [(λx : G (λy:Prop. F y). G (λy:Prop. F y)) a : Prop], typed through [k_spη]. *)
Definition type_mkAppsE_inst := @type_mkAppsE _ rf_Σ k_cb k_Γ k_t [tRel 0] (tSort sProp) k_PT k_t_typed k_spη.
Definition inversion_mkApps_directE_inst :=
  @inversion_mkApps_directE _ rf_Σ wc_wfE k_Γ k_t [tRel 0] (tSort sProp) k_isT_Prop type_mkAppsE_inst.

(** [y : x] under [x := ∀P:Prop. P]. *)
Definition subst_type_local_ctxE_inst :=
  @PCUICSpineEta.subst_type_local_ctxE _ si_Σ si_wfE [] [] c2_x [vass si_na (tRel 0)] [ci_False] sProp
    ci_wf_Γ1 c2_tlc c2_sub.
Definition subst_sorts_local_ctxE_inst :=
  @PCUICSpineEta.subst_sorts_local_ctxE _ si_Σ si_wfE [] [] c2_x [vass si_na (tRel 0)] [ci_False] [sProp]
    ci_wf_Γ1 c2_slc c2_sub.

(** The arity spine [Π x : G (λy:Prop. F y). G (λy:Prop. F y)] applied to [a] (retyped by η),
    ending in a conversion step [G (λy:Prop. F y) ≤ G F] (η). *)
Definition k_PTT : term := tProd c1b_na k_T (lift0 1 k_T).
Lemma k_PTT_typed : rf_Σ ;;; k_Γ |-E k_PTT : tSort (Sort.sort_of_product sProp sProp).
Proof. apply typeE_Prod; [exact (k_vass_s k_Γ k_T k_T_typed)|exact (k_T_typed_up _ k_wf_ΓΔ)]. Qed.
Lemma k_asp : arity_spineE rf_Σ k_Γ k_PTT [tRel 0] k_U.
Proof. eapply arity_spine_assE; [exact k_a_T|]. eapply arity_spine_convE; [exact k_isT_U|exact (k_η Cumul)]. Qed.
Definition k_wasp : wf_arity_spineE rf_Σ k_Γ k_PTT [tRel 0] k_U :=
  {| wf_arity_spine_wfE := has_sort_isTypeE _ k_PTT_typed; wf_arity_spine_spineE := k_asp |}.
Definition wf_arity_spine_typing_spineE_inst := @wf_arity_spine_typing_spineE _ rf_Σ wc_wfE _ _ _ _ k_wasp.

Definition arity_typing_spineE_inst :=
  @arity_typing_spineE _ rf_Σ wc_wfE k_Γ k_Δ sProp [tRel 0] sProp k_spη.

Definition typing_spine_it_mkProd_or_LetIn_genE_inst :=
  @typing_spine_it_mkProd_or_LetIn_genE _ rf_Σ wc_wfE k_Γ k_Δ [] (tSort sProp) [tRel 0] [tRel 0] [] []
    (tSort sProp) eq_refl k_sp_Prop eq_refl k_sub_T k_isT_PT.
Definition typing_spine_it_mkProd_or_LetInE_inst :=
  @typing_spine_it_mkProd_or_LetInE _ rf_Σ wc_wfE k_Γ k_Δ (tSort sProp) [tRel 0] [tRel 0] [] (tSort sProp)
    eq_refl k_sp_Prop eq_refl k_sub_T k_isT_PT.
Definition typing_spine_it_mkProd_or_LetIn'E_inst :=
  @typing_spine_it_mkProd_or_LetIn'E _ rf_Σ wc_wfE k_Γ k_Δ (tSort sProp) [tRel 0] [tRel 0] [] (tSort sProp)
    k_sp_T k_sp_Prop k_isT_PT.
Definition typing_spine_it_mkProd_or_LetIn_close_make_substE_inst :=
  @typing_spine_it_mkProd_or_LetIn_close_make_substE _ rf_Σ wc_wfE k_Γ k_Δ (tSort sProp) [tRel 0] [tRel 0]
    eq_refl eq_refl k_sub_T k_isT_PT.
Definition typing_spine_it_mkProd_or_LetIn_closeE_inst :=
  @typing_spine_it_mkProd_or_LetIn_closeE _ rf_Σ wc_wfE k_Γ k_Δ (tSort sProp) [tRel 0] [tRel 0] _ k_sp_T k_isT_PT
    eq_refl.

(** The substitutions for [x : G (λy:Prop. F y)] and for [x : G F] are convertible, the
    telescopes related by η. *)
Lemma k_terms_refl : ws_cumul_pbE_terms rf_Σ k_Γ [tRel 0] [tRel 0].
Proof. constructor; [|constructor]. apply ws_cumul_pbE_refl; [exact k_closed|reflexivity]. Qed.
Definition spine_subst_convE_inst :=
  @spine_subst_convE _ rf_Σ wc_wfE k_Γ _ _ _ _ _ _ k_sp_T k_sp_U (k_rel Conv) k_terms_refl.

(** [x : Prop ⊢ x] for [y : Prop], under [x := ∀P:Prop. P]. *)
Lemma k_si_sp : spine_substE si_Σ fi_Γ1 [tRel 0] [tRel 0] [vass si_na fi_P].
Proof.
  split; [exact ci_wf_Γ1|exact (ci_wf_P _ ci_wf_Γ1)|exact (context_subst_ass [] [] [] si_na fi_P (tRel 0) context_subst_nil)|].
  exact (subslet_ass_tipE ci_x_typed).
Qed.
Definition spine_subst_substE_inst :=
  @spine_subst_substE _ si_Σ si_wfE [] c2_x [] _ _ _ _ k_si_sp c2_sub.
Definition spine_subst_subst_firstE_inst :=
  @spine_subst_subst_firstE _ si_Σ si_wfE c2_x [] _ _ _ _ k_si_sp c2_sub.

Definition weaken_subsletE_inst :=
  @PCUICSpineEta.weaken_subsletE _ si_Σ si_wfE [tRel 0] c2_x fi_Γ1 c2_x ci_wf_Γ1 ci_wf_Γ1 c2_sub_x.

(** Weakening by [z : Prop] below [k_Γ]. *)
Lemma k_wf_z : wf_localE rf_Σ [vass c1b_na (tSort sProp)].
Proof. apply localenv_cons_abs; [constructor|exact (rf_P_vass [] localenv_nil)]. Qed.
Definition spine_subst_weakenE_inst :=
  @spine_subst_weakenE _ rf_Σ wc_wfE k_Γ _ _ _ [vass c1b_na (tSort sProp)] k_wf_z k_sp_T.

(** [x := a, y := a] for [x : G (λy:Prop. F y), y : G F], built from its two halves. *)
Lemma k_wf_ΓΔy : wf_localE rf_Σ (k_Γ ,,, k_Δ ,,, k_Δy).
Proof. apply localenv_cons_abs; [exact k_wf_ΓΔ|exact (k_vass _ _ (k_U_typed_up _ k_wf_ΓΔ))]. Qed.
Definition spine_subst_appE_inst :
  spine_substE rf_Σ k_Γ ([tRel 0] ++ [tRel 0]) [tRel 0; tRel 0] (k_Δ ,,, k_Δy) :=
  @spine_subst_appE _ rf_Σ k_Γ k_Δ k_Δy [tRel 0] [tRel 0] [tRel 0; tRel 0] eq_refl k_wf_ΓΔy k_sp_T k_sp_U.
Definition spine_subst_app_invE_inst :=
  @spine_subst_app_invE _ rf_Σ wc_wfE k_Γ k_Δ k_Δy [tRel 0] [tRel 0] _ eq_refl spine_subst_appE_inst.
Definition spine_subst_smash_app_invE_inst :=
  @spine_subst_smash_app_invE _ rf_Σ wc_wfE k_Γ k_Δ k_Δy [tRel 0] [tRel 0] eq_refl spine_subst_appE_inst.

(** [x : Type@{l0} ⊢ x] instantiated at [Set]. *)
Lemma k_up_wf_Δ : wf_localE up_Σp (up_Γ ,,, k_up_Δ).
Proof.
  apply localenv_cons_abs; [exact up_wf_Γ|]. split; [exact tt|]. exists (Sort.super up_s0).
  split; [apply typeE_Sort; [exact up_wf_Γ|exact up_wf_sort_p]|]. split; [exact I|reflexivity].
Qed.
Lemma k_up_sp : spine_substE up_Σp up_Γ [tRel 0] [tRel 0] k_up_Δ.
Proof.
  split; [exact up_wf_Γ|exact k_up_wf_Δ|exact (context_subst_ass [] [] [] si_na _ (tRel 0) context_subst_nil)|].
  exact (subslet_ass_tipE up_x_typed).
Qed.
Definition spine_subst_instE_inst :=
  @spine_subst_instE _ up_Σm up_wfE up_univs [Level.lzero] up_Γ _ _ _ up_global_ext k_up_sp up_cu.

Lemma k_wf_ΓΓz : wf_localE rf_Σ (k_Γ ,,, [vass c1b_na (tSort sProp)]).
Proof. exact k_wf_Γz. Qed.
Definition spine_subst_weakeningE_inst :=
  @spine_subst_weakeningE _ rf_Σ wc_wfE k_Γ _ _ _ [vass c1b_na (tSort sProp)] k_wf_ΓΓz k_sp_T.

(** [x ⊢ x : Prop] under [x := ∀P:Prop. P]. *)
Lemma k_si_ci : ctx_instE si_Σ fi_Γ1 [tRel 0] [vass si_na fi_P].
Proof. constructor; [exact ci_x_typed|constructor]. Qed.
Definition ctx_inst_substE_inst := @ctx_inst_substE _ si_Σ si_wfE [] c2_x [] _ _ _ k_si_ci c2_sub.
Definition ctx_inst_weakenE_inst :=
  @ctx_inst_weakenE _ rf_Σ wc_wfE k_Γ _ _ [vass c1b_na (tSort sProp)] k_wf_z k_ci.

Definition ctx_inst_sub_specE_inst := ctx_inst_sub_specE k_ci.

(** The arity spine of [Π x : G (λy:Prop. F y). G (λy:Prop. F y)] at [x := a], ending in the
    conversion [G (λy:Prop. F y) ≤ G F]. *)
Lemma k_asp_conv : arity_spineE rf_Σ k_Γ (subst0 [tRel 0] (lift0 1 k_T)) [] k_U.
Proof. eapply arity_spine_convE; [exact k_isT_U|exact (k_η Cumul)]. Qed.
Definition arity_spine_it_mkProd_or_LetInE_inst :=
  @arity_spine_it_mkProd_or_LetInE _ rf_Σ k_Γ k_Δ (lift0 1 k_T) [tRel 0] [tRel 0] [] k_U k_sp_T k_asp_conv.

Definition spine_subst_is_closed_contextE_inst :=
  @spine_subst_is_closed_contextE _ rf_Σ wc_wfE k_Γ _ _ _ k_sp_T.
Definition spine_subst_is_closed_context_codomE_inst :=
  @spine_subst_is_closed_context_codomE _ rf_Σ wc_wfE k_Γ _ _ _ k_sp_T.
Lemma k_leq_Prop : leq_sort (global_ext_constraints rf_Σ) sProp sProp.
Proof. apply leq_sort_refl. Qed.
Definition arity_spine_it_mkProd_or_LetIn_SortE_inst :=
  @arity_spine_it_mkProd_or_LetIn_SortE _ rf_Σ wc_wfE k_Γ k_Δ sProp sProp _ _ rf_wf_sort k_leq_Prop k_sp_T.

Definition ctx_inst_subst_lengthE_inst := ctx_inst_subst_lengthE k_ci.

(** [x := a, y := a] as a [ctx_inst] of [x : G (λy:Prop. F y), y : G F]. *)
Lemma k_ci_y : ctx_instE rf_Σ k_Γ [tRel 0] (subst_telescope (ctx_inst_subE k_ci) 0 k_Δy).
Proof. cbn. constructor; [exact k_a_U|constructor]. Qed.
Definition ctx_inst_appE_inst := ctx_inst_appE k_ci k_ci_y.
Definition ctx_inst_app_invE_inst := ctx_inst_app_invE (Δ := k_Δ) ctx_inst_appE_inst.
(** [ctx_inst_sub_eqE]: [ctx_inst_subE] depends only on the arguments, and the premises force
    equal arguments; the witness equates the substitutions of two DIFFERENT opaque derivations
    ([r_ci] types [a] at [k_T] by one η retyping; [r_ci2] adds a second cumulativity node),
    over argument lists and telescopes that are equal but not syntactically the same.
    [r_ci2_not_refl] checks that [eq_refl] does not prove it. *)
Lemma r_ci2 : ctx_instE rf_Σ k_Γ (List.rev [tRel 0]) k_Δ.
Proof.
  constructor; [|constructor].
  exact (type_ws_cumul_pbE (pb := Cumul) k_T k_a_T k_isT_T
           (ws_cumul_pbE_refl k_closed (subject_is_open_termE (Σ := rf_Σ) (wfΣ := wc_wfE) k_T_typed))).
Qed.
Definition ctx_inst_sub_eqE_inst : ctx_inst_subE r_ci = ctx_inst_subE r_ci2 :=
  ctx_inst_sub_eqE r_ci r_ci2 eq_refl eq_refl.
Fail Definition r_ci2_not_refl : ctx_inst_subE r_ci = ctx_inst_subE r_ci2 := eq_refl.
Definition ctx_inst_app_subE_inst := ctx_inst_app_subE (Δ := k_Δ) ctx_inst_appE_inst.

(** A [ctx_inst] of the let [z := a : G F]: it takes no argument. *)
Lemma k_ci_def : ctx_instE rf_Σ k_Γ [] [vdef c1b_na (tRel 0) k_U].
Proof. constructor. constructor. Qed.
Definition ctx_inst_defE_inst := ctx_inst_defE k_ci_def.
Definition ctx_inst_assE_inst := ctx_inst_assE k_ci.

Definition ctx_inst_spine_substE_inst := @ctx_inst_spine_substE _ rf_Σ wc_wfE k_Γ k_Δ _ k_wf_ΓΔ k_ci.
Definition spine_subst_ctx_instE_inst := spine_subst_ctx_instE k_sp_T.

(** The let [z := ∀P:Prop. P] under [y : z]: unfolding it is a reduction. *)
Definition all_rels_substE_inst := all_rels_substE si_Σ c2_Γlet [] (tRel 1) si_wfE c2_wf_Γlet.

Lemma k_closed_Γlet : is_closed_context ([] ,,, c2_Γlet ,,, []).
Proof. reflexivity. Qed.
Definition all_rels_subst_liftE_inst :=
  @all_rels_subst_liftE _ si_Σ si_wfE c2_Γlet [] [] (tRel 1) c2_wf_Γlet k_closed_Γlet eq_refl.

Definition spine_subst_to_extended_list_kE_inst := @spine_subst_to_extended_list_kE _ rf_Σ wc_wfE k_Δ k_Γ k_wf_ΓΔ.

(** [let z := ∀P:Prop. P : Prop in z : Prop]: the let branch, whose comparison goes through
    the let-in inversion [ws_cumul_pbE_LetIn_l_inv]. *)
Definition type_it_mkProd_or_LetIn_invE_inst :=
  @type_it_mkProd_or_LetIn_invE _ si_Σ si_wfE [] [vdef si_na ci_False fi_P] (tRel 0) sProp c2_letT_typed.
Definition inversion_it_mkProd_or_LetInE_inst :=
  @inversion_it_mkProd_or_LetInE _ si_Σ si_wfE [] [vdef si_na ci_False fi_P] (tRel 0) sProp c2_letT_typed.

(** [∀x:Prop. x : Prop], expanded at [x := ∀P:Prop. P]. *)
Lemma k_sub_smash : subsletE si_Σ [] [ci_False] (smash_context [] c2_x).
Proof. exact c2_sub. Qed.
Definition isType_it_mkProd_or_LetIn_appE_inst :=
  @isType_it_mkProd_or_LetIn_appE _ si_Σ si_wfE [] c2_x [] [ci_False] (tRel 0) sProp c2_False0 k_sub_smash.

Definition ctx_inst_sub_to_extended_list_kE_inst := ctx_inst_sub_to_extended_list_kE k_Γ [tRel 0] k_Δ k_ci.
Definition spine_subst_subst_to_extended_list_kE_inst := spine_subst_subst_to_extended_list_kE k_sp_T.
Definition spine_subst_subst_to_extended_list_k_genE_inst :=
  spine_subst_subst_to_extended_list_k_genE (Δ' := k_Δ') k_sp_T eq_refl.
Definition arity_spine_eqE_inst := @arity_spine_eqE _ rf_Σ k_Γ k_U k_U k_isT_U eq_refl.
Definition typing_spine_wf_localE_inst := typing_spine_wf_localE k_spη.

(** The η step under [w : G F] and under [z := a : G F], substituted by [a]. *)
Definition substitution_ws_cumul_pb_vassE_inst :=
  @substitution_ws_cumul_pb_vassE _ rf_Σ wc_wfE Cumul k_Γ (tRel 0) c1b_na k_U _ _ k_a_U
    (k_η_up Cumul (vass c1b_na k_U) (k_closed_up k_wf_ΓΔ')).
Definition substitution_ws_cumul_pb_vdefE_inst :=
  @substitution_ws_cumul_pb_vdefE _ rf_Σ wc_wfE Cumul k_Γ (tRel 0) c1b_na k_U _ _ k_wf_Γlet
    (k_η_up Cumul (vdef c1b_na (tRel 0) k_U) (k_closed_up k_wf_Γlet)).

Definition typing_spine_invE_inst :=
  @typing_spine_invE _ rf_Σ wc_wfE k_Γ k_Δ (tSort sProp) [tRel 0] [] (tSort sProp) eq_refl k_spη.
Definition spine_subst_ctx_inst_subE_inst := spine_subst_ctx_inst_subE k_sp_T.
Definition typing_spine_ctx_instE_inst :=
  @typing_spine_ctx_instE _ rf_Σ wc_wfE k_Γ k_Δ (tSort sProp) [tRel 0] [] (tSort sProp) eq_refl k_spη.

(** The empty spine from [Π x : G (λy:Prop. F y). Prop] to [Π x : G F. Prop] (η), extended
    by [a : G F]. *)
Lemma k_sp_PT_PU : typing_spineE rf_Σ k_Γ k_PT [] k_PU.
Proof. apply type_spine_nilE; [exact k_isT_PT|exact k_isT_PU|exact (k_PT_η Cumul)]. Qed.
Definition typing_spine_appE_inst :=
  @typing_spine_appE _ rf_Σ wc_wfE k_Γ k_PT [] c1b_na k_U (tSort sProp) (tRel 0) k_sp_PT_PU k_a_U.
Definition typing_spine_nth_errorE_inst :=
  @typing_spine_nth_errorE _ rf_Σ wc_wfE k_Γ k_Δ (tSort sProp) [tRel 0] 0 (tRel 0) (tSort sProp) k_spη eq_refl
    (le_n 1).
Definition spine_subst_smashE_inst := @spine_subst_smashE _ rf_Σ wc_wfE k_Γ _ _ _ k_sp_T.
Definition ctx_inst_sub_substE_inst := ctx_inst_sub_substE (Δ := k_Δ) k_ci.
Definition typing_spine_ctx_inst_smashE_inst :=
  @typing_spine_ctx_inst_smashE _ rf_Σ wc_wfE k_Γ k_Δ (tSort sProp) [tRel 0] [] (tSort sProp) eq_refl k_spη.

Lemma k_sub_T_smash : subsletE rf_Σ k_Γ (List.rev [tRel 0]) (smash_context [] k_Δ).
Proof. exact k_sub_T. Qed.
Lemma k_asp_conv' : arity_spineE rf_Σ k_Γ (subst_let_expand (List.rev [tRel 0]) k_Δ (lift0 1 k_T)) [] k_U.
Proof. eapply arity_spine_convE; [exact k_isT_U|exact (k_η Cumul)]. Qed.
Definition arity_spine_it_mkProd_or_LetIn_smashE_inst :=
  @arity_spine_it_mkProd_or_LetIn_smashE _ rf_Σ k_Γ k_Δ (lift0 1 k_T) [tRel 0] [] k_U k_sub_T_smash k_asp_conv'.

(** [x := a] moved from [x : G (λy:Prop. F y)] to [x : G F] along the η-related telescopes. *)
Lemma k_ass : assumption_context k_Δ. Proof. repeat constructor. Qed.
Lemma k_ass' : assumption_context k_Δ'. Proof. repeat constructor. Qed.
Definition subslet_cumulE_inst :=
  @subslet_cumulE _ rf_Σ wc_wfE Cumul k_Γ [tRel 0] k_Δ k_Δ' k_ass k_ass' k_wf_ΓΔ k_wf_ΓΔ' (k_rel Cumul) k_sub_T.
Definition spine_subst_cumulE_inst :=
  @spine_subst_cumulE _ rf_Σ wc_wfE k_Γ [tRel 0] k_Δ k_Δ' k_ass k_ass' k_wf_ΓΔ k_wf_ΓΔ' (k_rel Cumul) k_sp_T.

(** [(λx : G (λy:Prop. F y). G (λy:Prop. F y)) a] through the arity spine, [a] retyped by η. *)
Lemma k_asp_PT : arity_spineE rf_Σ k_Γ k_PT [tRel 0] (tSort sProp).
Proof. eapply arity_spine_assE; [exact k_a_T|]. apply arity_spine_nilE. Qed.
Definition pre_type_mkApps_arityE_inst :=
  @pre_type_mkApps_arityE _ rf_Σ wc_wfE k_Γ k_t [tRel 0] k_PT (tSort sProp) k_t_typed k_isT_PT k_asp_PT.

Definition spine_subst_extended_substE_inst := spine_subst_extended_substE k_sp_T.
Definition ws_cumul_ctx_pb_rel'_context_assumptionsE_inst := ws_cumul_ctx_pb_rel'_context_assumptionsE (snd (k_rel Cumul)).
Definition ws_cumul_ctx_pb_rel_context_assumptionsE_inst := ws_cumul_ctx_pb_rel_context_assumptionsE (k_rel Cumul).

(** The η step under the let [z := a : G F], with the let expanded. *)
Lemma k_η_let pb : ws_cumul_pbE pb rf_Σ (k_Γ ,,, [vdef c1b_na (tRel 0) k_U] ,,, []) (lift0 1 k_T) (lift0 1 k_U).
Proof. exact (k_η_up pb (vdef c1b_na (tRel 0) k_U) (k_closed_up k_wf_Γlet)). Qed.
Definition ws_cumul_pb_expand_lets_kE_inst :=
  @ws_cumul_pb_expand_lets_kE _ rf_Σ wc_wfE Cumul k_Γ [vdef c1b_na (tRel 0) k_U] [] _ _ k_wf_Γlet (k_η_let Cumul).
Definition ws_cumul_pb_expand_letsE_inst :=
  @ws_cumul_pb_expand_letsE _ rf_Σ wc_wfE Cumul k_Γ [vdef c1b_na (tRel 0) k_U] _ _ k_wf_Γlet (k_η_let Cumul).

Lemma k_terms_η : ws_cumul_pbE_terms rf_Σ k_Γ [k_T] [k_U].
Proof. constructor; [exact (k_η Conv)|constructor]. Qed.
Definition ws_cumul_pb_terms_liftE_inst :=
  @ws_cumul_pb_terms_liftE _ rf_Σ wc_wfE k_Γ [vass c1b_na (tSort sProp)] _ _ (k_closed_up k_wf_Γz) k_terms_η.
Definition ws_cumul_pb_le_leE_inst := ws_cumul_pb_le_leE (k_η Conv).

Definition k_ctx pb : ws_cumul_ctx_pbE pb rf_Σ (k_Γ ,,, k_Δ) (k_Γ ,,, k_Δ') := fst ws_cumul_ctx_pbE_rel_app (k_rel pb).
Definition ws_cumul_ctx_pb_le_leE_inst := ws_cumul_ctx_pb_le_leE (k_ctx Conv).
Definition ws_cumul_ctx_pb_eq_leE_inst := ws_cumul_ctx_pb_eq_leE (pb := Cumul) (k_ctx Conv).

(** [x : G (λy:Prop. F y) ⊢ x : G (λy:Prop. F y)], moved to [x : G F] (η). *)
Definition k_Γw : context := [vass c1b_na (lift0 1 k_T)].
Lemma k_sub_x : subsletE rf_Σ (k_Γ ,,, k_Δ) [tRel 0] k_Γw.
Proof. exact (subslet_ass_tipE (typeE_Rel _ _ 0 (vass c1b_na k_T) k_wf_ΓΔ eq_refl)). Qed.
Definition subslet_ws_cumul_ctx_pbE_inst :=
  @subslet_ws_cumul_ctx_pbE _ rf_Σ wc_wfE Cumul k_Γ k_Γw k_Δ k_Δ' [tRel 0] k_wf_ΓΔ k_wf_ΓΔ' (k_rel_sym Cumul) k_sub_x.

Definition ws_cumul_ctx_pb_rel_conv_extended_substE_inst :=
  @ws_cumul_ctx_pb_rel_conv_extended_substE _ rf_Σ wc_wfE Cumul k_Γ k_Δ k_Δ' k_wf_ΓΔ k_wf_ΓΔ' (k_rel Cumul).
Definition ws_cumul_ctx_pb_rel_smashE_inst :=
  @ws_cumul_ctx_pb_rel_smashE _ rf_Σ wc_wfE Cumul k_Γ k_Δ k_Δ' k_wf_ΓΔ k_wf_ΓΔ' (k_rel Cumul).

(** The η step under [x : G F], moved to [x : G (λy:Prop. F y)] (η). *)
Lemma k_terms_η_Δ' : ws_cumul_pbE_terms rf_Σ (k_Γ ,,, k_Δ') [lift0 1 k_T] [lift0 1 k_U].
Proof. constructor; [exact (k_η_Δ' Conv)|constructor]. Qed.
Definition ws_cumul_pb_terms_ws_cumul_ctxE_inst :=
  @ws_cumul_pb_terms_ws_cumul_ctxE _ rf_Σ wc_wfE Cumul k_Γ k_Δ k_Δ' _ _ k_wf_ΓΔ k_wf_ΓΔ' (k_rel Cumul) k_terms_η_Δ'.
Definition ws_cumul_ctx_pb_rel_lengthE_inst := ws_cumul_ctx_pb_rel_lengthE (k_rel Cumul).

Lemma k_η_Δ pb : ws_cumul_pbE pb rf_Σ (k_Γ ,,, k_Δ) (lift0 1 k_T) (lift0 1 k_U).
Proof. exact (k_η_up pb (vass c1b_na k_T) (k_closed_up k_wf_ΓΔ)). Qed.
Definition ws_cumul_pb_expand_lets_ws_cumul_ctxE_inst :=
  @ws_cumul_pb_expand_lets_ws_cumul_ctxE _ rf_Σ wc_wfE Cumul Cumul k_Γ k_Δ k_Δ' _ _ k_wf_ΓΔ k_wf_ΓΔ'
    (k_η_Δ Cumul) (k_rel Cumul).

(** [x := a] as a [ctx_inst] of [x : G (λy:Prop. F y)], moved to [x : G F] (η). *)
Lemma k_rel_wf : wf_local_relE rf_Σ k_Γ k_Δ.
Proof. apply localenv_cons_abs; [constructor|exact (k_vass k_Γ k_T k_T_typed)]. Qed.
Lemma k_rel_wf' : wf_local_relE rf_Σ k_Γ k_Δ'.
Proof. apply localenv_cons_abs; [constructor|exact (k_vass k_Γ k_U k_U_typed)]. Qed.
Definition ctx_inst_cumulE_inst :=
  @ctx_inst_cumulE _ rf_Σ wc_wfE Cumul k_Γ [tRel 0] k_Δ k_Δ' (k_rel Cumul) k_ci k_rel_wf k_rel_wf'.

Definition ctx_inst_smash_accE_inst := fst (@ctx_inst_smash_accE _ rf_Σ k_Γ [tRel 0] k_Δ) k_ci.
Definition ctx_inst_smashE_inst := fst (@ctx_inst_smashE _ rf_Σ k_Γ [tRel 0] k_Δ) k_ci.

(** [x : G (λy:Prop. F y)] to [x : G F] and back: the middle telescope differs from the ends. *)
Definition ws_cumul_ctx_pb_rel_transE_inst :=
  @ws_cumul_ctx_pb_rel_transE _ rf_Σ wc_wfE Cumul k_Γ k_Δ k_Δ' k_Δ (k_rel Cumul) (k_rel_sym Cumul).

(** [OnOne2_ctx_instE] and [All2_ctx_instE]: the relation [r_P] relates exactly the η pair
    [λx:Prop. f x] ↦ [f] in [f : Prop → Prop] ([rf_Γ], [rf_t], [rf_premise] of
    [PCUICWsCumulEtaCtx]); the instance is rewritten from [[λx. f x]] to [[f]]. The premise
    quantified over every context and substitution is proved in general, by
    [substitution_ws_cumul_ctx_pbE]. *)
Definition r_P : global_env_ext -> context -> term -> term -> Type :=
  fun _ Γ t u => ((Γ = rf_Γ) * (t = rf_t) * (u = tRel 0))%type.
Definition r_Δ : context := [vass c1b_na rf_F].

Lemma r_wf : wf_localE rf_Σ (rf_Γ ,,, List.rev r_Δ).
Proof.
  apply localenv_cons_abs; [exact rf_wf_Γ|].
  split; [exact tt|]. exists (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)).
  split; [exact (rf_F_typed rf_Γ rf_wf_Γ)|]. split; [exact I|reflexivity].
Qed.

Lemma r_ci_t : ctx_instE rf_Σ rf_Γ [rf_t] r_Δ.
Proof. constructor; [exact rf_t_typed|constructor]. Qed.

Lemma r_ci_P : PCUICTyping.ctx_inst
  (fun (Γ : context) (t T : term) => forall u : term, r_P rf_Σ Γ t u -> rf_Σ ;;; Γ |-E u : T)
  rf_Γ [rf_t] r_Δ.
Proof.
  constructor; [|constructor].
  intros u h. cbv [r_P] in h. destruct h as [[_ _] ->]. exact rf_f_typed.
Qed.

Lemma r_refl_tl {Γ} (tl : list term) : is_closed_context Γ -> forallb (is_open_term Γ) tl ->
  All2 (ws_cumul_pbE Conv rf_Σ Γ) tl tl.
Proof.
  intros cl. induction tl as [|t tl IH]; [constructor|].
  move=> /= /andP [ht htl]. constructor; [exact (ws_cumul_pbE_refl cl ht)|exact (IH htl)].
Qed.

Lemma r_conv_of_P {Γ t u} : r_P rf_Σ Γ t u -> ws_cumul_pbE Conv rf_Σ Γ t u.
Proof. cbv [r_P]. intros [[-> ->] ->]. exact rf_premise. Qed.

Lemma r_All2_of_OnOne2 {Γ s s'} : is_closed_context Γ -> forallb (is_open_term Γ) s ->
  OnOne2 (r_P rf_Σ Γ) s s' -> All2 (ws_cumul_pbE Conv rf_Σ Γ) s s'.
Proof.
  intros cl op o. induction o.
  - constructor; [exact (r_conv_of_P p)|]. move: op => /= /andP [_ op]. exact (r_refl_tl tl cl op).
  - move: op => /= /andP [hh op]. constructor; [exact (ws_cumul_pbE_refl cl hh)|exact (IHo op)].
Qed.

Lemma r_All2_of_All2 {Γ s s'} : All2 (r_P rf_Σ Γ) s s' -> All2 (ws_cumul_pbE Conv rf_Σ Γ) s s'.
Proof. intros a. induction a; constructor; [exact (r_conv_of_P r)|exact IHa]. Qed.

Lemma r_H1_gen (Γ Δ' Δ : context) (s s' : list term) :
  wf_localE rf_Σ (Γ ,,, Δ' ,,, Δ) ->
  subsletE rf_Σ Γ (List.rev s) Δ' -> subsletE rf_Σ Γ (List.rev s') Δ' ->
  All2 (ws_cumul_pbE Conv rf_Σ Γ) s s' ->
  ws_cumul_ctx_pbE Conv rf_Σ (Γ ,,, subst_context (List.rev s) 0 Δ) (Γ ,,, subst_context (List.rev s') 0 Δ).
Proof.
  intros wf sub sub' a.
  have cl : is_closed_context (Γ ,,, Δ' ,,, Δ) := wf_local_closed_contextE (Σ := rf_Σ) (wfΣ := wc_wfE) wf.
  apply (substitution_ws_cumul_ctx_pbE (Δ := Δ') (Δ' := Δ'));
    [exact (subslet_untyped_subsletE _ _ _ _ sub)|exact (subslet_untyped_subsletE _ _ _ _ sub')
    |exact (All2_rev _ _ _ _ _ a)|exact cl|exact cl].
Qed.

Lemma r_open {Γ Δ' s} : wf_localE rf_Σ Γ -> subsletE rf_Σ Γ (List.rev s) Δ' -> forallb (is_open_term Γ) s.
Proof. intros _ sub. have h := subsletE_open_terms (wfΣ := wc_wfE) sub. by rewrite forallb_rev in h. Qed.

Definition OnOne2_ctx_instE_inst : ctx_instE rf_Σ rf_Γ [tRel 0] r_Δ :=
  @OnOne2_ctx_instE _ rf_Σ wc_wfE Conv r_P rf_Γ [rf_t] [tRel 0] r_Δ
    (fun Γ Δ' Δ s s' wf sub sub' o =>
       let wfΓ := wf_localE_app_l _ _ _ (wf_localE_app_l _ _ _ wf) in
       r_H1_gen Γ Δ' Δ s s' wf sub sub'
         (r_All2_of_OnOne2 (wf_local_closed_contextE (Σ := rf_Σ) (wfΣ := wc_wfE) wfΓ)
                           (r_open wfΓ sub) o))
    r_wf r_ci_P r_ci_t (OnOne2_hd _ _ _ _ ((eq_refl, eq_refl), eq_refl)).

Definition All2_ctx_instE_inst : ctx_instE rf_Σ rf_Γ [tRel 0] r_Δ :=
  @All2_ctx_instE _ rf_Σ wc_wfE Conv r_P rf_Γ [rf_t] [tRel 0] r_Δ
    (fun Γ Δ' Δ s s' wf sub sub' a => r_H1_gen Γ Δ' Δ s s' wf sub sub' (r_All2_of_All2 a))
    r_wf r_ci_P r_ci_t (All2_cons ((eq_refl, eq_refl), eq_refl) All2_nil).

Definition ctx_inst_open_termsE_inst := @ctx_inst_open_termsE _ rf_Σ wc_wfE k_Γ _ _ k_ci.
Definition subslet_open_termsE_inst := @subslet_open_termsE _ rf_Σ wc_wfE k_Γ _ _ k_sub_T.

(** [ctx_inst_eq_contextE]: the instance [λx:Prop. f x] (anonymous binder) is replaced by its
    α-variant [λy:Prop. f y] (binder named [y]); the premise over EVERY α-variant is proved by
    inverting [upto_names']. *)
Definition r_ny : aname := mkBindAnn (nNamed "y") Relevant.
Definition rf_t' : term := tLambda r_ny (tSort sProp) (tApp (tRel 1) (tRel 0)).

Lemma r_lam_typed0 (n : name) :
  rf_Σ ;;; rf_Γ |-E tLambda (mkBindAnn n Relevant) (tSort sProp) (tApp (tRel 1) (tRel 0))
    : tProd (mkBindAnn n Relevant) (tSort sProp) (tSort sProp).
Proof.
  have hv : lift_typing typingE rf_Σ rf_Γ (j_vass (mkBindAnn n Relevant) (tSort sProp)).
  { split; [exact tt|]. exists (Sort.super sProp).
    split; [exact (rf_P_typed rf_Γ rf_wf_Γ)|]. split; [exact I|reflexivity]. }
  have hΓ1 : wf_localE rf_Σ (rf_Γ ,, vass (mkBindAnn n Relevant) (tSort sProp)).
  { apply localenv_cons_abs; [exact rf_wf_Γ|exact hv]. }
  apply typeE_Lambda; [exact hv|].
  apply (typeE_App _ _ (tRel 1) c1b_na (tSort sProp) (tSort sProp)
           (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) (tRel 0)).
  - exact (rf_F_typed _ hΓ1).
  - exact (typeE_Rel _ _ 1 (vass c1b_na rf_F) hΓ1 eq_refl).
  - exact (typeE_Rel _ _ 0 (vass (mkBindAnn n Relevant) (tSort sProp)) hΓ1 eq_refl).
Qed.

(** The α-variant's principal type [Π y:Prop. Prop] differs from [rf_F] by the binder name only;
    it is retyped at [rf_F] through [ws_cumul_pbE_Prod]. *)
Lemma r_lam_typed (n : name) :
  rf_Σ ;;; rf_Γ |-E tLambda (mkBindAnn n Relevant) (tSort sProp) (tApp (tRel 1) (tRel 0)) : rf_F.
Proof.
  have cl : is_closed_context rf_Γ := wf_local_closed_contextE (Σ := rf_Σ) (wfΣ := wc_wfE) rf_wf_Γ.
  have hv : wf_localE rf_Σ (rf_Γ ,, vass (mkBindAnn n Relevant) (tSort sProp)).
  { apply localenv_cons_abs; [exact rf_wf_Γ|]. split; [exact tt|]. exists (Sort.super sProp).
    split; [exact (rf_P_typed rf_Γ rf_wf_Γ)|]. split; [exact I|reflexivity]. }
  refine (type_ws_cumul_pbE (pb := Cumul) _ (r_lam_typed0 n) (has_sort_isTypeE _ (rf_F_typed rf_Γ rf_wf_Γ)) _).
  unfold rf_F. apply ws_cumul_pbE_Prod; [reflexivity| |].
  - apply ws_cumul_pbE_refl; [exact cl|reflexivity].
  - apply ws_cumul_pbE_refl; [exact (wf_local_closed_contextE (Σ := rf_Σ) (wfΣ := wc_wfE) hv)|reflexivity].
Qed.

Lemma r_alpha_inv v : upto_names' rf_t v -> rf_Σ ;;; rf_Γ |-E v : rf_F.
Proof.
  unfold rf_t. intros h. depelim h.
  repeat match goal with H : eq_term_upto_univ_napp _ _ _ _ _ _ _ |- _ => depelim H end.
  repeat match goal with H : _ = _ |- _ => progress cbn in H end.
  subst.
  match goal with |- _ ;;; _ |-E tLambda ?na _ _ : _ => destruct na as [n r] end.
  match goal with H : eq_binder_annot _ _ |- _ => unfold eq_binder_annot in H; cbn in H; subst r end.
  apply r_lam_typed.
Qed.

Lemma r_ci_alpha : PCUICTyping.ctx_inst
  (fun (Γ : context) (u A : term) => forall v : term, upto_names' u v -> rf_Σ ;;; Γ |-E v : A)
  rf_Γ [rf_t] r_Δ.
Proof. constructor; [exact r_alpha_inv|constructor]. Qed.

Lemma r_upto : All2 upto_names' [rf_t] [rf_t'].
Proof. repeat constructor. Qed.

Definition ctx_inst_eq_contextE_inst : ctx_instE rf_Σ rf_Γ [rf_t'] r_Δ :=
  @ctx_inst_eq_contextE _ rf_Σ wc_wfE rf_Γ r_Δ [rf_t] [rf_t'] r_wf r_ci_alpha r_ci_t r_upto.

(** [x := a, y := a] for [x : G (λy:Prop. F y), y : G F], one variable at a time. *)
Lemma k_jy : lift_typing typingE rf_Σ (k_Γ ,,, k_Δ) (j_vass c1b_na (lift0 1 k_U)).
Proof. exact (k_vass _ _ (k_U_typed_up _ k_wf_ΓΔ)). Qed.
Lemma k_a_Uy : rf_Σ ;;; k_Γ |-E tRel 0 : subst0 [tRel 0] (lift0 1 k_U).
Proof. exact k_a_U. Qed.
Definition spine_subst_vassE_inst :=
  spine_subst_vassE rf_Σ k_Γ [tRel 0] (tRel 0) [tRel 0] k_Δ c1b_na (lift0 1 k_U) wc_wfE k_sp_T k_jy k_a_Uy.
Definition wf_local_nth_isTypeRelE_inst := @wf_local_nth_isTypeRelE _ rf_Σ k_Γ 0 _ k_wf_Γ eq_refl.
Lemma k_wf_ΓΔy' : wf_localE rf_Σ (k_Γ ,,, (k_Δ ,, vass c1b_na (lift0 1 k_U))).
Proof. exact k_wf_ΓΔy. Qed.
Definition spine_subst_vass'E_inst :=
  spine_subst_vass'E rf_Σ k_Γ [tRel 0] (tRel 0) [tRel 0] k_Δ c1b_na (lift0 1 k_U) wc_wfE k_sp_T k_wf_ΓΔy'
    (fun _ _ => k_a_Uy).
Definition mk_ctx_subst_spec'E_inst := mk_ctx_subst_spec'E (Δ := k_Δ) k_ci.

Definition closed_subsletE_inst := @closed_subsletE _ rf_Σ wc_wfE k_Γ _ _ k_sub_T.
Definition closed_spine_substE_inst := @closed_spine_substE _ rf_Σ wc_wfE k_Γ _ _ _ k_sp_T.
Definition closed_spine_subst_instE_inst := @closed_spine_subst_instE _ rf_Σ wc_wfE k_Γ _ _ _ k_sp_T.
