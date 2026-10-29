(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the hypotheses of [PCUICInductiveInversionEta]

  Each lemma of [PCUICInductiveInversionEta] that has a premise is applied here to a concrete
  instance with every premise proved. The environments:
  - [rf_Σ] of [PCUICWsCumulEtaCtx] (the empty environment) with the context
    [wc_Γ := [G : (Prop → Prop) → Prop; F : Prop → Prop]] of [PCUICSubstitutionEta], in which
    [wc_T := G (λy:Prop. F y)] and [wc_U := G F] are related by one η step and by no reduction
    or syntactic comparison ([wc_T_normal], [wc_U_normal], [wc_not_compare]). The conversion
    lemmas ([ws_cumul_pb_mkApps_eqE], [ws_cumul_pb_LetIn_substE], [ws_cumul_pb_red_stepE],
    [cumul_ctx_relSpec_AlgoE]) are applied through that step; the reduction lemmas
    ([invert_red_mkApps_tRelE], [closed_red_mkAppsE]) to a β step in an argument of [G].
  - [iv_Σ] of [PCUICInversionEtaInstances] ([CoInductive R (A : Prop) : Prop := mkR { f : A }],
    a record with one projection, well formed for the η typing by [iv_wfE]), with the context
    [iv_Γk := [y : k g; k : (Prop → Prop) → Prop; g : Prop → Prop]], in which [k g] and
    [k (λx:Prop. g x)] are related by one η step ([c18_η]). [ctx_inst_app_weakE] and
    [inductive_cumulative_indicesE] take their parameters through that step: [R (k (λx. g x))]
    is related to [R (k g)].
  - [if_Σ] of [PCUICConversionEtaCongrFinst] ([Inductive I@{u} (A : Prop) : Prop :=.], variance
    [Irrelevant], with two bound levels [l0], [l1]) for the universe lemmas; [ws_cumul_pb_inst_varianceE]
    transports the η step of [wc_Γ] from the variance environment of [I] to [if_Σ], at the
    instances [l0] and [l1].
  The instances marked WEAK show satisfiability only; the reason is next to each. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping uGraph.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICEquality PCUICCases PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICReduction
     PCUICUnivSubst PCUICUnivSubstitutionConv PCUICContextSubst PCUICSigmaCalculus PCUICClosedBodies
     PCUICWellScopedCumulativity PCUICConversion PCUICWeakeningEnv PCUICArityRed
     PCUICTypingEta PCUICTypingEtaInd PCUICClosedTypEta PCUICWeakeningEnvTypEta PCUICWeakeningTypEta
     PCUICTypingEtaNotions PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta
     PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICConversionEtaCongrFinst
     PCUICWsCumulEtaCtx PCUICEtaMkAppsTRel PCUICEtaJoinSpec PCUICEtaC1b
     PCUICCumulativitySpecEtaClosureInstances PCUICInversionEtaInstances
     PCUICSpineEta PCUICInductivesEta PCUICInductiveInversionEta.
From Equations.Prop Require Import DepElim.

#[local] Existing Instance default_checker_flags.

(** ** The η pair [G (λy:Prop. F y)] / [G F], in any environment *)

Definition c18_rf_cb : ClosedBodies rf_Σ := @wfE_ClosedBodies _ rf_Σ wc_wfE.
Definition c18_iv_cb : ClosedBodies iv_env := @wfE_ClosedBodies _ iv_env iv_wfE.
#[local] Existing Instance c18_rf_cb.
#[local] Existing Instance c18_iv_cb.
#[local] Existing Instance if_cb.

Lemma c18_wc_spec (Σ : global_env_ext) pb (Γ : context) : Σ ;;; Γ ⊢ wc_T ≤sE[pb] wc_U.
Proof.
  apply convSpecE_cumulSpecE.
  unfold wc_T, wc_U. apply cumulE_App; [apply cumulE_Refl|].
  unfold wc_eta_F. apply cumul_eta_l. apply cumulE_Refl.
Qed.

Lemma c18_wc_closed : is_closed_context wc_Γ. Proof. reflexivity. Qed.
Lemma c18_wc_T_open : is_open_term wc_Γ wc_T. Proof. reflexivity. Qed.
Lemma c18_wc_U_open : is_open_term wc_Γ wc_U. Proof. reflexivity. Qed.

(** [G (λy:Prop. F y) ≡ G F] in [wc_Γ], over any environment with closed bodies. *)
Lemma c18_wc_ws (Σ : global_env_ext) {cb : ClosedBodies Σ} pb : ws_cumul_pbE pb Σ wc_Γ wc_T wc_U.
Proof. exact (into_ws_cumul_pbE_spec (c18_wc_spec Σ pb wc_Γ) c18_wc_closed c18_wc_T_open c18_wc_U_open). Qed.

(** The arguments [λy:Prop. F y] and [F] of the η pair. *)
Lemma c18_wc_args : ws_cumul_pbE_terms rf_Σ wc_Γ [wc_eta_F] [tRel 1].
Proof.
  exact (ws_cumul_pbE_mkApps_tRel (Γ := wc_Γ) (n := 0) (d := vass c1b_na wc_G_ty) (u := [wc_eta_F])
           (u' := [tRel 1]) eq_refl eq_refl (c18_wc_ws rf_Σ Cumul)).
Qed.

(** A β step in an argument of [G]: [(λx:Prop → Prop. x) F ⇝ F]. *)
Definition c18_idF : term := tLambda c1b_na rf_F (tRel 0).
Definition c18_Fβ : term := tApp c18_idF (tRel 1).

Lemma c18_red_Fβ : rf_Σ ;;; wc_Γ ⊢ c18_Fβ ⇝ tRel 1.
Proof. apply into_closed_red; [apply red1_red; apply red_beta|exact c18_wc_closed|reflexivity]. Qed.

Lemma c18_red_GFβ : rf_Σ ;;; wc_Γ ⊢ mkApps (tRel 0) [c18_Fβ] ⇝ wc_U.
Proof.
  apply into_closed_red; [|exact c18_wc_closed|reflexivity].
  apply red1_red. apply app_red_r. apply red_beta.
Qed.

(** ** Instances in [rf_Σ]: reductions and the η step *)

Definition invert_red_mkApps_tRelE_inst :=
  invert_red_mkApps_tRelE (Σ := rf_Σ) (wfΣ := wc_wfE) (Γ := wc_Γ) (n := 0) (d := vass c1b_na wc_G_ty)
    (args := [c18_Fβ]) eq_refl eq_refl c18_red_GFβ.

Definition closed_red_mkAppsE_inst :=
  closed_red_mkAppsE (Σ := rf_Σ) (wfΣ := wc_wfE) wc_Γ (tRel 0) [c18_Fβ] [tRel 1] c18_wc_closed eq_refl
    (All2_cons c18_red_Fβ All2_nil).

(** [G (λy:Prop. F y) ≤ G F]: the heads are equal, the arguments are η related. *)
Definition ws_cumul_pb_mkApps_eqE_inst :=
  ws_cumul_pb_mkApps_eqE (Σ := rf_Σ) (wfΣ := wc_wfE) wc_Γ (tRel 0) (tRel 0) [wc_eta_F] [tRel 1]
    c18_wc_closed eq_refl eq_refl ltac:(constructor) c18_wc_args.

(** [let x := λy:Prop. F y in G x ≤ let x := F in G x]: the bodies are η related. *)
Definition c18_Gx : term := tApp (tRel 1) (tRel 0).

Definition ws_cumul_pb_LetIn_substE_inst :=
  ws_cumul_pb_LetIn_substE (Σ := rf_Σ) (wfΣ := wc_wfE) (le := Cumul) (Γ := wc_Γ) (na := c1b_na)
    (na' := c1b_na) (b := wc_eta_F) (b' := tRel 1) (ty := rf_F) (ty' := rf_F) (t := c18_Gx) (t' := c18_Gx)
    eq_refl eq_refl (c18_wc_ws rf_Σ Cumul).

(** [(λx:Prop → Prop. G x) (λy:Prop. F y) ≤ G F]: a β step to [G (λy:Prop. F y)], then the η step. *)
Definition c18_Tβ : term := tApp (tLambda c1b_na rf_F (tApp (tRel 1) (tRel 0))) wc_eta_F.

Lemma c18_red_Tβ : red rf_Σ wc_Γ c18_Tβ wc_T.
Proof. apply red1_red. apply red_beta. Qed.

Lemma c18_red_U : red rf_Σ wc_Γ wc_U wc_U.
Proof. reflexivity. Qed.

Definition ws_cumul_pb_red_stepE_inst :=
  ws_cumul_pb_red_stepE (Σ := rf_Σ) (wfΣ := wc_wfE) (pb := Cumul) (Δ := wc_Γ) (a := c18_Tβ) (a' := wc_T)
    (b := wc_U) (b' := wc_U) c18_wc_closed eq_refl eq_refl c18_red_Tβ c18_red_U
    (fun _ _ => c18_wc_ws rf_Σ Cumul).

(** The specification relates [x : G (λy:Prop. F y)] to [x : G F] by the η step. *)
Lemma c18_cumul_ctx : cumul_ctx_rel cumulSpecE0 rf_Σ wc_Γ [vass c1b_na wc_T] [vass c1b_na wc_U].
Proof. constructor; [constructor|]. constructor; [reflexivity|]. exact (c18_wc_spec rf_Σ Cumul _). Qed.

Definition cumul_ctx_relSpec_AlgoE_inst :=
  cumul_ctx_relSpec_AlgoE (Σ := rf_Σ) (wfΣ := wc_wfE) c18_cumul_ctx eq_refl eq_refl.

(** ** The η kit in [iv_Σ] *)

Lemma c18_K_typed (Γ : context) : wf_localE iv_Σ Γ ->
  iv_Σ ;;; Γ |-E iv_K : tSort (Sort.sort_of_product iv_sPP (Sort.super sProp)).
Proof.
  intros h. unfold iv_K. apply typeE_Prod.
  - exact (iv_vass_s iv_Σ Γ si_na iv_PP _ (iv_PP_typed iv_Σ Γ h) eq_refl).
  - exact (iv_P_typed iv_Σ _ (iv_wf_vass iv_Σ Γ si_na iv_PP _ h (iv_PP_typed iv_Σ Γ h) eq_refl)).
Qed.

Lemma c18_wf_Γg : wf_localE iv_Σ iv_Γg.
Proof. exact (iv_wf_vass iv_Σ [] si_na iv_PP _ localenv_nil (iv_PP_typed iv_Σ [] localenv_nil) eq_refl). Qed.

Lemma c18_wf_Γkg : wf_localE iv_Σ iv_Γkg.
Proof. exact (iv_wf_vass iv_Σ iv_Γg si_na iv_K _ c18_wf_Γg (c18_K_typed iv_Γg c18_wf_Γg) eq_refl). Qed.

Lemma c18_kg0_typed : iv_Σ ;;; iv_Γkg |-E tApp (tRel 0) (tRel 1) : si_P.
Proof.
  exact (typeE_App _ _ (tRel 0) si_na iv_PP si_P _ (tRel 1) (c18_K_typed iv_Γkg c18_wf_Γkg)
           (typeE_Rel _ _ 0 (vass si_na iv_K) c18_wf_Γkg eq_refl)
           (typeE_Rel _ _ 1 (vass si_na iv_PP) c18_wf_Γkg eq_refl)).
Qed.

Lemma c18_wf_Γk : wf_localE iv_Σ iv_Γk.
Proof. exact (iv_wf_vass iv_Σ iv_Γkg si_na (tApp (tRel 0) (tRel 1)) sProp c18_wf_Γkg c18_kg0_typed eq_refl). Qed.

Lemma c18_closed_Γk : is_closed_context iv_Γk.
Proof. exact (wf_local_closed_contextE (Σ := iv_Σ) (wfΣ := iv_wfE) c18_wf_Γk). Qed.

(** [k g : Prop]. *)
Lemma c18_kg_typed : iv_Σ ;;; iv_Γk |-E iv_kg : si_P.
Proof.
  exact (typeE_App _ _ (tRel 1) si_na iv_PP si_P _ (tRel 2) (c18_K_typed iv_Γk c18_wf_Γk)
           (typeE_Rel _ _ 1 (vass si_na iv_K) c18_wf_Γk eq_refl)
           (typeE_Rel _ _ 2 (vass si_na iv_PP) c18_wf_Γk eq_refl)).
Qed.

Lemma c18_eta_g_typed : iv_Σ ;;; iv_Γk |-E iv_eta_g : iv_PP.
Proof.
  have w : wf_localE iv_Σ (iv_Γk ,, vass si_na si_P) := iv_wf_P iv_Σ iv_Γk c18_wf_Γk.
  unfold iv_eta_g, iv_PP. apply typeE_Lambda.
  - exact (iv_vass iv_Σ iv_Γk si_na si_P _ (iv_P_typed iv_Σ iv_Γk c18_wf_Γk) eq_refl).
  - exact (typeE_App _ _ (tRel 3) si_na si_P si_P _ (tRel 0) (iv_PP_typed iv_Σ _ w)
             (typeE_Rel _ _ 3 (vass si_na iv_PP) w eq_refl)
             (typeE_Rel _ _ 0 (vass si_na si_P) w eq_refl)).
Qed.

(** [k (λx:Prop. g x) : Prop]. *)
Lemma c18_keta_typed : iv_Σ ;;; iv_Γk |-E iv_keta : si_P.
Proof.
  exact (typeE_App _ _ (tRel 1) si_na iv_PP si_P _ iv_eta_g (c18_K_typed iv_Γk c18_wf_Γk)
           (typeE_Rel _ _ 1 (vass si_na iv_K) c18_wf_Γk eq_refl) c18_eta_g_typed).
Qed.

Lemma c18_kg_open : is_open_term iv_Γk iv_kg. Proof. reflexivity. Qed.
Lemma c18_keta_open : is_open_term iv_Γk iv_keta. Proof. reflexivity. Qed.

(** [k (λx:Prop. g x) ≡ k g]: one [cumul_eta_l] step under [k]. *)
Lemma c18_η pb : ws_cumul_pbE pb iv_Σ iv_Γk iv_keta iv_kg.
Proof.
  apply (into_ws_cumul_pbE_spec (Σ := iv_Σ)); [|exact c18_closed_Γk|exact c18_keta_open|exact c18_kg_open].
  apply convSpecE_cumulSpecE. unfold iv_keta, iv_kg, iv_eta_g.
  apply cumulE_App; [apply cumulE_Refl|]. apply cumul_eta_l. apply cumulE_Refl.
Qed.

Lemma c18_cu : consistent_instance_ext iv_Σ (ind_universes iv_mdecl) [].
Proof. reflexivity. Qed.

Lemma c18_ru : cmp_opt_variance (compare_universe iv_Σ) Cumul
  (match ind_variance iv_mdecl with Some var => Variance var | None => AllEqual end) [] [].
Proof. cbn. constructor. Qed.

Lemma c18_cmp_ind n : cmp_ind_universes iv_Σ iv_ind n [] [].
Proof. eapply cmp_global_instance_refl; typeclasses eauto. Qed.

Lemma c18_onudecl : on_udecl_prop iv_Σ (ind_universes iv_mdecl).
Proof. intros x hx. exfalso. eapply ConstraintSet.empty_spec. exact hx. Qed.

(** The projections fact of [R], from its declaration. *)
Lemma c18_onps : on_projections iv_mdecl (inductive_mind iv_ind) (inductive_ind iv_ind) iv_idecl
  (ind_indices iv_idecl) iv_cdecl.
Proof.
  destruct (on_declared_projectionE (wfΣ := iv_wfE) iv_declared_projection) as [[_ _] [[[_ onps] _] _]].
  exact onps.
Qed.

(** [R (k (λx:Prop. g x))] and [R (k g)]. *)
Lemma c18_Rketa_typed : iv_Σ ;;; iv_Γk |-E mkApps (tInd iv_ind []) [iv_keta] : si_P.
Proof. exact (iv_RX_typed iv_Γk iv_keta c18_wf_Γk c18_keta_typed). Qed.

Lemma c18_isT_Rketa : isTypeE iv_Σ iv_Γk (mkApps (tInd iv_ind []) [iv_keta]).
Proof. exact (has_sort_isTypeE _ c18_Rketa_typed). Qed.

Lemma c18_terms : ws_cumul_pbE_terms iv_Σ iv_Γk [iv_keta] [iv_kg].
Proof. constructor; [exact (c18_η Conv)|constructor]. Qed.

(** [R (k (λx:Prop. g x)) ≤ R (k g)]: equal instances, the parameter through the η step. *)
Lemma c18_R_η : ws_cumul_pbE Cumul iv_Σ iv_Γk (mkApps (tInd iv_ind []) [iv_keta]) (mkApps (tInd iv_ind []) [iv_kg]).
Proof. apply ws_cumul_pbE_Ind; [exact (c18_cmp_ind 1)|exact c18_closed_Γk|exact c18_terms]. Qed.

(** [A := X] for the parameter [A : Prop] of [R]. *)
Definition c18_sp (X : term) (hX : iv_Σ ;;; iv_Γk |-E X : si_P) :
  spine_substE iv_Σ iv_Γk [X] [X] (subst_instance [] (ind_params iv_mdecl)).
Proof.
  constructor.
  - exact c18_wf_Γk.
  - exact (iv_wf_P iv_Σ iv_Γk c18_wf_Γk).
  - exact (context_subst_ass [] [] [] si_na si_P X context_subst_nil).
  - exact (subslet_ass_tipE hX).
Defined.

(** ** Instances in [iv_Σ] *)

Definition on_constructor_wf_argsE_inst :=
  on_constructor_wf_argsE (Σ := iv_env) (wfΣ := iv_wfE) iv_declared_constructor.

Definition on_constructor_substE_inst :=
  on_constructor_substE (Σ := iv_env) (wfΣ := iv_wfE) iv_declared_constructor.

Definition on_constructor_instE_inst :=
  on_constructor_instE (Σ := iv_Σ) (wfΣ := iv_wfE) iv_declared_constructor [] c18_cu.

Definition wt_ind_app_varianceE_inst :=
  wt_ind_app_varianceE (Σ := iv_Σ) (wfΣ := iv_wfE) (Γ := iv_Γk) c18_isT_Rketa.

(** The parameters [k g] of [R] after a cumulativity through the η step:
    [R (k (λx:Prop. g x)) ≤ R (k g)]. *)
Lemma c18_ci_kg : ctx_instE iv_Σ iv_Γk [iv_kg] (List.rev (subst_instance [] (ind_params iv_mdecl))).
Proof. constructor; [exact c18_kg_typed|constructor]. Qed.

Definition ctx_inst_app_weakE_inst :=
  ctx_inst_app_weakE iv_Σ iv_wfE iv_ind iv_mdecl iv_idecl iv_declared_inductive iv_Γk c18_wf_Γk
    [iv_kg] [iv_keta] [] [] c18_isT_Rketa c18_cu c18_ci_kg c18_R_η.

(** The parameters [k (λx:Prop. g x)] and [k g], related by the η step. [R] has no index, so the
    conclusion relates two empty contexts. *)
Definition inductive_cumulative_indicesE_inst :=
  inductive_cumulative_indicesE (Σ := iv_Σ) (wfΣ := iv_wfE) (napp := 1) iv_declared_inductive c18_cu c18_cu
    (c18_cmp_ind 1) iv_Γk [iv_keta] [iv_kg] [iv_keta] [iv_kg] (c18_sp iv_keta c18_keta_typed)
    (c18_sp iv_kg c18_kg_typed) c18_terms.

(* WEAK: [R] is monomorphic, so the two instances are [] and the conclusion compares the type of
   the projection with itself; the lemma compares one declared type at two instances, where no
   η step can occur. *)
Definition projection_cumulative_indicesE_inst :=
  projection_cumulative_indicesE (Σ := iv_Σ) (wfΣ := iv_wfE) iv_declared_projection c18_onudecl c18_cu c18_cu
    (c18_cmp_ind (ind_npars iv_mdecl)).

Definition subslet_projs_smashE_inst :=
  subslet_projs_smashE iv_Σ iv_ind iv_mdecl iv_idecl iv_wfE iv_declared_inductive c18_onps iv_Γk (tRel 0) [].

(** The positivity lemmas relate one term (or context) at two universe instances, after the
    substitution of the inductives; at the monomorphic block [R] both instances are [], so
    their comparisons are reflexive: WEAK, each at a closed argument or the constructor of [R]. *)

Definition c18_Pβ : term := tApp (tLambda si_na si_P (tRel 0)) si_P.

Lemma c18_red_Pβ (Ξ : context) : red iv_Σ Ξ c18_Pβ si_P.
Proof. apply red1_red. apply red_beta. Qed.

Lemma c18_cl_ar : closed_ctx (ind_arities iv_mdecl ,,, [])@[[]].
Proof. reflexivity. Qed.

Lemma c18_refl0 (t : term) : closedn 0 t -> ws_cumul_pbE Conv iv_Σ [] t t.
Proof. intros h. apply ws_cumul_pbE_refl; [reflexivity|]. by rewrite -is_open_term_closedE. Qed.

(* WEAK: a β step at a closed term, [Γ = Δ = []]. *)
Definition red_subst_indsE_inst :=
  red_subst_indsE (Σ := iv_Σ) (wfΣ := iv_wfE) (ind := iv_ind) (mdecl := iv_mdecl) (Γ := []) (Δ := [])
    (a := c18_Pβ) (b := si_P) (u := []) (v := []) ltac:(constructor) c18_cl_ar eq_refl eq_refl c18_red_Pβ.

(* WEAK: see above; [t] is a β redex at a closed term. *)
Definition positive_inds_conv_red_stepE_inst :=
  positive_inds_conv_red_stepE (Σ := iv_Σ) (wfΣ := iv_wfE) (ind := iv_ind) (mdecl := iv_mdecl) (Γ := [])
    (Δ := []) (t := c18_Pβ) (t' := si_P) (u := []) (u' := []) ltac:(constructor) c18_cl_ar eq_refl eq_refl
    c18_red_Pβ eq_refl eq_refl (fun _ _ => c18_refl0 si_P eq_refl).

Lemma c18_whd_P : whd_rel true iv_Σ.1 (arities_context (ind_bodies iv_mdecl) ,,, []) si_P [] si_P [].
Proof. apply whd_stop. reflexivity. Qed.

(* WEAK: see above; [ty = ty' = Prop]. *)
Lemma positive_inds_conv_ass_redE_inst :
  ws_cumul_pbE Conv iv_Σ [] (subst (ind_subst iv_mdecl iv_ind []) 0 (tProd si_na si_P si_P)@[[]])
    (subst (ind_subst iv_mdecl iv_ind []) 0 (tProd si_na si_P si_P)@[[]]).
Proof.
  refine (positive_inds_conv_ass_redE (Σ := iv_Σ) (wfΣ := iv_wfE) (ind := iv_ind) (mdecl := iv_mdecl)
            (Γ := []) (Δ := []) (na := si_na) (ty := si_P) (ty' := si_P) (h := si_P) (l := []) (u := []) (u' := [])
            ltac:(constructor) c18_cl_ar eq_refl eq_refl c18_whd_P eq_refl eq_refl eq_refl _).
  intros _ Δ' _ clΔ' onl _ _. apply ws_cumul_pbE_refl; [by rewrite -is_closed_ctx_closedE|exact onl].
Qed.

(* WEAK: see above; [p = Prop], closed. *)
Definition positive_inds_convE_inst :=
  positive_inds_convE (Σ := iv_Σ) (wfΣ := iv_wfE) (ind := iv_ind) (mdecl := iv_mdecl) (idecl := iv_idecl)
    (NI := []) (Γ := []) (p := si_P) (u := []) (u' := []) (Δ := []) iv_declared_inductive c18_cu c18_ru I
    c18_cl_ar (pos_arg_closed _ _ _ _ si_P eq_refl) eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(constructor).

(* WEAK: see above; [t = Prop], closed. *)
Definition positive_cstr_arg_subst_closedE_inst :=
  positive_cstr_arg_subst_closedE (Σ := iv_Σ) (wfΣ := iv_wfE) (ind := iv_ind) (mdecl := iv_mdecl)
    (idecl := iv_idecl) (Γ := []) (t := si_P) (pb := Cumul) (u := []) (u' := []) iv_declared_inductive c18_cu
    eq_refl ltac:(apply ws_cumul_pbE_refl; reflexivity).

(* WEAK: see above; [t] is a β redex at a closed term. *)
Definition positive_cstr_arg_subst_red_stepE_inst :=
  positive_cstr_arg_subst_red_stepE (Σ := iv_Σ) (wfΣ := iv_wfE) (ind := iv_ind) (mdecl := iv_mdecl) (Γ := [])
    (t := c18_Pβ) (t' := si_P) (pb := Cumul) (u := []) (u' := []) ltac:(constructor) c18_cl_ar
    (fun _ Ξ => c18_red_Pβ Ξ) ltac:(apply ws_cumul_pbE_refl; reflexivity) (fun _ => ltac:(apply ws_cumul_pbE_refl; reflexivity)).

(* WEAK: see above; the nested inductive is [R] itself, at the closed argument [∀P:Prop. P]. *)
Definition positive_cstr_arg_subst_nestedE_inst :=
  positive_cstr_arg_subst_nestedE (Σ := iv_Σ) (wfΣ := iv_wfE) (ind := iv_ind) (mdecl := iv_mdecl)
    (idecl := iv_idecl) (NI := []) (Γ := []) (ind' := iv_ind) (ui := []) (args := [iv_False]) (k := 0) (u := [])
    (u' := []) iv_declared_inductive c18_cu c18_ru I c18_cl_ar eq_refl ltac:(repeat constructor) ltac:(constructor)
    ltac:(apply ws_cumul_pbE_refl; reflexivity) ltac:(constructor).

(* WEAK: see above; [t = Prop], closed. *)
Definition positive_cstr_arg_substE_inst :=
  positive_cstr_arg_substE (Σ := iv_Σ) (wfΣ := iv_wfE) (ind := iv_ind) (mdecl := iv_mdecl) (idecl := iv_idecl)
    (Γ := []) (t := si_P) (u := []) (u' := []) iv_declared_inductive c18_cu c18_ru c18_cl_ar
    ltac:(apply ws_cumul_pbE_refl; reflexivity) (pos_arg_closed _ _ _ _ si_P eq_refl) ltac:(constructor).

(** A context related to itself. *)
Lemma c18_rel_refl (Σ : global_env_ext) (Γ Δ : context) :
  is_closed_context (Γ ,,, Δ) -> ws_cumul_ctx_pbE_rel Cumul Σ Γ Δ Δ.
Proof. intros h. apply ws_cumul_ctx_pbE_rel_app. now apply ws_cumul_ctx_pbE_refl_pb. Qed.

(* WEAK: see above; the arguments [f : A] of [mkR] at the instances [] and []. *)
Definition positive_cstr_closed_argsE_inst :=
  positive_cstr_closed_argsE (Σ := iv_Σ) (wfΣ := iv_wfE) (u := []) (u' := []) iv_declared_constructor c18_cu c18_ru
    ltac:(apply c18_rel_refl; reflexivity).

Lemma c18_wf_ar_pars : wf_localE iv_Σ (subst_instance [] (ind_arities iv_mdecl ,,, smash_context [] (ind_params iv_mdecl) ,,, [])).
Proof.
  have h := on_constructor_wf_argsE_inst.
  apply All_local_env_app_inv in h as [h _]. exact h.
Qed.

(* WEAK: see above; [Γ = []]. *)
Lemma positive_cstr_closed_args_subst_aritiesE_inst :
  ws_cumul_ctx_pbE_rel Cumul iv_Σ (subst_instance [] (smash_context [] (ind_params iv_mdecl))) [] [].
Proof.
  destruct (on_declared_constructorE (wfΣ := iv_wfE) iv_declared_constructor) as [_ [cs [_ onc]]].
  exact (positive_cstr_closed_args_subst_aritiesE (Σ := iv_Σ) (wfΣ := iv_wfE) (u := []) (u' := []) (Γ := [])
           iv_declared_inductive c18_cu onc c18_ru eq_refl c18_wf_ar_pars localenv_nil ltac:(constructor)
           ltac:(apply c18_rel_refl; reflexivity)).
Qed.

(** ** Instances in [if_Σ]: universes *)

Lemma c18_if_declared : declared_inductive if_Σ if_ind if_mdecl if_idecl.
Proof. split; [left; reflexivity|reflexivity]. Qed.

Lemma c18_if_cu0 : consistent_instance_ext if_Σ if_univs [Level.lvar 0].
Proof. split; [reflexivity|split; [reflexivity|]]. unfold valid_constraints; cbn. intros v _ c Hc. exfalso. vm_compute in Hc. inversion Hc. Qed.

Lemma c18_if_cu1 : consistent_instance_ext if_Σ if_univs [Level.lvar 1].
Proof. split; [reflexivity|split; [reflexivity|]]. unfold valid_constraints; cbn. intros v _ c Hc. exfalso. vm_compute in Hc. inversion Hc. Qed.

Lemma c18_if_onudecl : on_udecl_prop if_Σ (ind_universes if_mdecl).
Proof. intros x hx. exfalso. vm_compute in hx. inversion hx. Qed.

Lemma c18_if_onvar : on_variance if_Σ (ind_universes if_mdecl) (Some [Variance.Irrelevant]).
Proof.
  cbn. eexists; eexists; eexists. split.
  - reflexivity.
  - split; [reflexivity|split; [reflexivity|]].
    unfold valid_constraints; cbn. intros v _ c Hc. exfalso. vm_compute in Hc. inversion Hc.
  - split; [reflexivity|split; [reflexivity|]].
    unfold valid_constraints; cbn. intros v _ c Hc. exfalso. vm_compute in Hc. inversion Hc.
  - reflexivity.
Qed.

Lemma c18_if_var : cmp_universe_instance_variance (compare_universe if_Σ) Cumul [Variance.Irrelevant]
  [Level.lvar 0] [Level.lvar 1].
Proof. repeat constructor. Qed.

(** At the full arity [1], [I]'s variance [Irrelevant] relates any two instances. *)
Lemma c18_if_cmp : cmp_global_instance if_Σ (compare_universe if_Σ) Cumul (IndRef if_ind) 1
  [Level.lvar 0] [Level.lvar 1].
Proof. cbn. right. repeat constructor. Qed.

Definition cmp_global_instance_ind_invE_inst :=
  cmp_global_instance_ind_invE (Σ := if_Σ) (wfΣ := if_wfE) (compare_universe if_Σ) Cumul if_ind if_mdecl if_idecl 1
    [Level.lvar 0] [Level.lvar 1] ltac:(typeclasses eauto) c18_if_declared c18_if_cmp.

(** The η step of [wc_Γ], transported from the variance environment of [I] to [if_Σ] at the
    instances [l0], [l1]. *)
Lemma ws_cumul_pb_inst_varianceE_inst :
  ws_cumul_pbE Cumul if_Σ (subst_instance [Level.lvar 0] wc_Γ) (subst_instance [Level.lvar 0] wc_T)
    (subst_instance [Level.lvar 1] wc_U).
Proof.
  refine (ws_cumul_pb_inst_varianceE (Σ := if_Σ) (wfΣ := if_wfE) (le := Cumul) (mdecl := if_mdecl)
            (l := [Variance.Irrelevant]) (Γ := wc_Γ) (u := [Level.lvar 0]) (u' := [Level.lvar 1])
            c18_if_onudecl c18_if_onvar eq_refl c18_if_cu0 c18_if_cu1 c18_if_var wc_T wc_U _).
  exact (c18_wc_ws (if_Σ.1, _) Cumul).
Qed.

(* WEAK: the lemma relates one context at two instances; [x : G (λy:Prop. F y)] mentions no
   universe, so the relation is reflexive. *)
Lemma All2_fold_instE_inst :
  ws_cumul_ctx_pbE_rel Cumul if_Σ (subst_instance [Level.lvar 0] wc_Γ)
    (subst_instance [Level.lvar 0] [vass c1b_na wc_T]) (subst_instance [Level.lvar 1] [vass c1b_na wc_T]).
Proof.
  refine (All2_fold_instE (Σ := if_Σ) (wfΣ := if_wfE) (le := Cumul) if_mdecl [Variance.Irrelevant] _ _ _
            [Level.lvar 0] [Level.lvar 1] wc_Γ [vass c1b_na wc_T]
            c18_if_onudecl c18_if_onvar c18_if_cu0 c18_if_cu1 eq_refl c18_if_var _).
  exact (c18_rel_refl _ wc_Γ [vass c1b_na wc_T] eq_refl).
Qed.

Definition consistent_instance_poly_lengthE_inst :=
  consistent_instance_poly_lengthE (Σ := if_Σ) (wfΣ := if_wfE) c18_if_cu0.

Definition consistent_instance_validE_inst :=
  consistent_instance_validE (Σ := if_Σ) (wfΣ := if_wfE) c18_if_cu0 eq_refl.

Lemma c18_lzero_in : LevelSet.In Level.lzero (global_levels if_env).
Proof. apply LevelSet.mem_spec. reflexivity. Qed.

Definition LSet_in_global_boundedE_inst :=
  LSet_in_global_boundedE (Σ := if_env) (l := Level.lzero) 0 if_wfE c18_lzero_in.

(** Two bound levels with the constraint [l0 = l1]. *)
Definition c18_cstr : UnivConstraint.t := (Level.lvar 0, ConstraintType.Eq, Level.lvar 1).

Lemma c18_onudecl2 : on_udecl_prop if_env (Polymorphic_ctx ([nAnon; nAnon], ConstraintSet.singleton c18_cstr)).
Proof.
  intros x hx. apply ConstraintSet.singleton_spec in hx. subst x.
  split; apply LevelSet.mem_spec; reflexivity.
Qed.

Definition on_udecl_prop_poly_boundedE_inst :=
  on_udecl_prop_poly_boundedE if_Σ [nAnon; nAnon] (ConstraintSet.singleton c18_cstr) if_wfE c18_onudecl2.
