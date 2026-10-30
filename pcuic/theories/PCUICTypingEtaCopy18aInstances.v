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
  Every instance that does not reach the whole of a lemma carries a mark. IMPOSSIBLE names a
  part that cannot hold an η step by the head and the rule set (the [red] and [whd_rel]
  premises: η relates terms only through [cumul_eta_l] of [cumulSpecE0] or through [JoinE],
  and [red1] has no η rule). NOT BUILT names a part that this file's environments do not
  reach, with the missing witness and its cost. Three costs recurred: a universe-polymorphic
  record WITH A PROJECTION (a new inductive, a new environment and its [wfE] proof), a
  universe-polymorphic inductive WITH A CONSTRUCTOR whose argument holds an under-applied
  occurrence (the same cost), and an under-applied occurrence of the block's own arity
  variable, which [positive_cstr_arg] admits only at full arity ([pos_arg_concl] asks
  [#|l| = ind_realargs]). The last section supplies the CONSTRUCTOR half at [J]. *)

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
From MetaRocq.PCUIC Require PCUICEtaIdxEnv. From Equations.Prop Require Import DepElim.

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
           (u' := [tRel 1]) Logic.eq_refl Logic.eq_refl (c18_wc_ws rf_Σ Cumul)).
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
    (args := [c18_Fβ]) Logic.eq_refl Logic.eq_refl c18_red_GFβ.

Definition closed_red_mkAppsE_inst :=
  closed_red_mkAppsE (Σ := rf_Σ) (wfΣ := wc_wfE) wc_Γ (tRel 0) [c18_Fβ] [tRel 1] c18_wc_closed Logic.eq_refl
    (All2_cons c18_red_Fβ All2_nil).

(** [G (λy:Prop. F y) ≤ G F]: the heads are equal, the arguments are η related. *)
Definition ws_cumul_pb_mkApps_eqE_inst :=
  ws_cumul_pb_mkApps_eqE (Σ := rf_Σ) (wfΣ := wc_wfE) wc_Γ (tRel 0) (tRel 0) [wc_eta_F] [tRel 1]
    c18_wc_closed Logic.eq_refl Logic.eq_refl ltac:(constructor) c18_wc_args.

(** [let x := λy:Prop. F y in G x ≤ let x := F in G x]: the bodies are η related. *)
Definition c18_Gx : term := tApp (tRel 1) (tRel 0).

Definition ws_cumul_pb_LetIn_substE_inst :=
  ws_cumul_pb_LetIn_substE (Σ := rf_Σ) (wfΣ := wc_wfE) (le := Cumul) (Γ := wc_Γ) (na := c1b_na)
    (na' := c1b_na) (b := wc_eta_F) (b' := tRel 1) (ty := rf_F) (ty' := rf_F) (t := c18_Gx) (t' := c18_Gx)
    Logic.eq_refl Logic.eq_refl (c18_wc_ws rf_Σ Cumul).

(** [(λx:Prop → Prop. G x) (λy:Prop. F y) ≤ G F]: a β step to [G (λy:Prop. F y)], then the η step. *)
Definition c18_Tβ : term := tApp (tLambda c1b_na rf_F (tApp (tRel 1) (tRel 0))) wc_eta_F.

Lemma c18_red_Tβ : red rf_Σ wc_Γ c18_Tβ wc_T.
Proof. apply red1_red. apply red_beta. Qed.

Lemma c18_red_U : red rf_Σ wc_Γ wc_U wc_U.
Proof. reflexivity. Qed.

Definition ws_cumul_pb_red_stepE_inst :=
  ws_cumul_pb_red_stepE (Σ := rf_Σ) (wfΣ := wc_wfE) (pb := Cumul) (Δ := wc_Γ) (a := c18_Tβ) (a' := wc_T)
    (b := wc_U) (b' := wc_U) c18_wc_closed Logic.eq_refl Logic.eq_refl c18_red_Tβ c18_red_U
    (fun _ _ => c18_wc_ws rf_Σ Cumul).

(** The specification relates [x : G (λy:Prop. F y)] to [x : G F] by the η step. *)
Lemma c18_cumul_ctx : cumul_ctx_rel cumulSpecE0 rf_Σ wc_Γ [vass c1b_na wc_T] [vass c1b_na wc_U].
Proof. constructor; [constructor|]. constructor; [reflexivity|]. exact (c18_wc_spec rf_Σ Cumul _). Qed.

Definition cumul_ctx_relSpec_AlgoE_inst :=
  cumul_ctx_relSpec_AlgoE (Σ := rf_Σ) (wfΣ := wc_wfE) c18_cumul_ctx Logic.eq_refl Logic.eq_refl.

(** ** The η kit in [iv_Σ] *)

Lemma c18_K_typed (Γ : context) : wf_localE iv_Σ Γ ->
  iv_Σ ;;; Γ |-E iv_K : tSort (Sort.sort_of_product iv_sPP (Sort.super sProp)).
Proof.
  intros h. unfold iv_K. apply typeE_Prod.
  - exact (iv_vass_s iv_Σ Γ si_na iv_PP _ (iv_PP_typed iv_Σ Γ h) Logic.eq_refl).
  - exact (iv_P_typed iv_Σ _ (iv_wf_vass iv_Σ Γ si_na iv_PP _ h (iv_PP_typed iv_Σ Γ h) Logic.eq_refl)).
Qed.

Lemma c18_wf_Γg : wf_localE iv_Σ iv_Γg.
Proof. exact (iv_wf_vass iv_Σ [] si_na iv_PP _ localenv_nil (iv_PP_typed iv_Σ [] localenv_nil) Logic.eq_refl). Qed.

Lemma c18_wf_Γkg : wf_localE iv_Σ iv_Γkg.
Proof. exact (iv_wf_vass iv_Σ iv_Γg si_na iv_K _ c18_wf_Γg (c18_K_typed iv_Γg c18_wf_Γg) Logic.eq_refl). Qed.

Lemma c18_kg0_typed : iv_Σ ;;; iv_Γkg |-E tApp (tRel 0) (tRel 1) : si_P.
Proof.
  exact (typeE_App _ _ (tRel 0) si_na iv_PP si_P _ (tRel 1) (c18_K_typed iv_Γkg c18_wf_Γkg)
           (typeE_Rel _ _ 0 (vass si_na iv_K) c18_wf_Γkg Logic.eq_refl)
           (typeE_Rel _ _ 1 (vass si_na iv_PP) c18_wf_Γkg Logic.eq_refl)).
Qed.

Lemma c18_wf_Γk : wf_localE iv_Σ iv_Γk.
Proof. exact (iv_wf_vass iv_Σ iv_Γkg si_na (tApp (tRel 0) (tRel 1)) sProp c18_wf_Γkg c18_kg0_typed Logic.eq_refl). Qed.

Lemma c18_closed_Γk : is_closed_context iv_Γk.
Proof. exact (wf_local_closed_contextE (Σ := iv_Σ) (wfΣ := iv_wfE) c18_wf_Γk). Qed.

(** [k g : Prop]. *)
Lemma c18_kg_typed : iv_Σ ;;; iv_Γk |-E iv_kg : si_P.
Proof.
  exact (typeE_App _ _ (tRel 1) si_na iv_PP si_P _ (tRel 2) (c18_K_typed iv_Γk c18_wf_Γk)
           (typeE_Rel _ _ 1 (vass si_na iv_K) c18_wf_Γk Logic.eq_refl)
           (typeE_Rel _ _ 2 (vass si_na iv_PP) c18_wf_Γk Logic.eq_refl)).
Qed.

Lemma c18_eta_g_typed : iv_Σ ;;; iv_Γk |-E iv_eta_g : iv_PP.
Proof.
  have w : wf_localE iv_Σ (iv_Γk ,, vass si_na si_P) := iv_wf_P iv_Σ iv_Γk c18_wf_Γk.
  unfold iv_eta_g, iv_PP. apply typeE_Lambda.
  - exact (iv_vass iv_Σ iv_Γk si_na si_P _ (iv_P_typed iv_Σ iv_Γk c18_wf_Γk) Logic.eq_refl).
  - exact (typeE_App _ _ (tRel 3) si_na si_P si_P _ (tRel 0) (iv_PP_typed iv_Σ _ w)
             (typeE_Rel _ _ 3 (vass si_na iv_PP) w Logic.eq_refl)
             (typeE_Rel _ _ 0 (vass si_na si_P) w Logic.eq_refl)).
Qed.

(** [k (λx:Prop. g x) : Prop]. *)
Lemma c18_keta_typed : iv_Σ ;;; iv_Γk |-E iv_keta : si_P.
Proof.
  exact (typeE_App _ _ (tRel 1) si_na iv_PP si_P _ iv_eta_g (c18_K_typed iv_Γk c18_wf_Γk)
           (typeE_Rel _ _ 1 (vass si_na iv_K) c18_wf_Γk Logic.eq_refl) c18_eta_g_typed).
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

(** ** A telescope whose typing holds an η step, over any well-formed context

  [Γ0 ,, g : Prop → Prop ,, k : (Prop → Prop) → Prop ,, y : k g ,, h : (Π x : k (λx:Prop. g x). Prop)
  ,, w : h y]. The last entry is typed only through the η step: [h] asks for its argument at
  [k (λx:Prop. g x)] while [y] is declared at [k g]. *)

Definition c18_tel_hty : term := tProd si_na iv_keta (tSort sProp).
Definition c18_tel_hy : term := tApp (tRel 0) (tRel 1).
Definition c18_tel : context := iv_Γk ,,, [vass si_na c18_tel_hy; vass si_na c18_tel_hty].

(** [k g ≤sE k (λx:Prop. g x)]: congruence, and the symmetric of one [cumul_eta_l] step. *)
Lemma c18_spec_eta (Γ : context) : cumulSpecE iv_Σ Γ iv_kg iv_keta.
Proof.
  unfold cumulSpecE, iv_kg, iv_keta, iv_eta_g.
  apply cumulE_App; [apply cumulE_Refl|].
  apply cumulE_Sym. apply cumul_eta_l. apply cumulE_Refl.
Qed.

Section C18Tel.
  Context (Γ0 : context) (wf0 : wf_localE iv_Σ Γ0).

  Lemma c18_tel_wf_Γg : wf_localE iv_Σ (Γ0 ,,, iv_Γg).
  Proof. exact (iv_wf_vass iv_Σ Γ0 si_na iv_PP _ wf0 (iv_PP_typed iv_Σ Γ0 wf0) Logic.eq_refl). Qed.

  Lemma c18_tel_wf_Γkg : wf_localE iv_Σ (Γ0 ,,, iv_Γkg).
  Proof.
    exact (iv_wf_vass iv_Σ (Γ0 ,,, iv_Γg) si_na iv_K _ c18_tel_wf_Γg
             (c18_K_typed (Γ0 ,,, iv_Γg) c18_tel_wf_Γg) Logic.eq_refl).
  Qed.

  Lemma c18_tel_kg0_typed : iv_Σ ;;; (Γ0 ,,, iv_Γkg) |-E tApp (tRel 0) (tRel 1) : si_P.
  Proof.
    exact (typeE_App _ _ (tRel 0) si_na iv_PP si_P _ (tRel 1) (c18_K_typed _ c18_tel_wf_Γkg)
             (typeE_Rel _ _ 0 (vass si_na iv_K) c18_tel_wf_Γkg Logic.eq_refl)
             (typeE_Rel _ _ 1 (vass si_na iv_PP) c18_tel_wf_Γkg Logic.eq_refl)).
  Qed.

  Lemma c18_tel_wf_Γk : wf_localE iv_Σ (Γ0 ,,, iv_Γk).
  Proof.
    exact (iv_wf_vass iv_Σ (Γ0 ,,, iv_Γkg) si_na (tApp (tRel 0) (tRel 1)) sProp c18_tel_wf_Γkg
             c18_tel_kg0_typed Logic.eq_refl).
  Qed.

  Lemma c18_tel_eta_g_typed : iv_Σ ;;; (Γ0 ,,, iv_Γk) |-E iv_eta_g : iv_PP.
  Proof.
    have w : wf_localE iv_Σ ((Γ0 ,,, iv_Γk) ,, vass si_na si_P) := iv_wf_P iv_Σ (Γ0 ,,, iv_Γk) c18_tel_wf_Γk.
    unfold iv_eta_g, iv_PP. apply typeE_Lambda.
    - exact (iv_vass iv_Σ (Γ0 ,,, iv_Γk) si_na si_P _ (iv_P_typed iv_Σ (Γ0 ,,, iv_Γk) c18_tel_wf_Γk) Logic.eq_refl).
    - exact (typeE_App _ _ (tRel 3) si_na si_P si_P _ (tRel 0) (iv_PP_typed iv_Σ _ w)
               (typeE_Rel _ _ 3 (vass si_na iv_PP) w Logic.eq_refl)
               (typeE_Rel _ _ 0 (vass si_na si_P) w Logic.eq_refl)).
  Qed.

  Lemma c18_tel_keta_typed : iv_Σ ;;; (Γ0 ,,, iv_Γk) |-E iv_keta : si_P.
  Proof.
    exact (typeE_App _ _ (tRel 1) si_na iv_PP si_P _ iv_eta_g (c18_K_typed _ c18_tel_wf_Γk)
             (typeE_Rel _ _ 1 (vass si_na iv_K) c18_tel_wf_Γk Logic.eq_refl) c18_tel_eta_g_typed).
  Qed.

  Lemma c18_tel_y_typed : iv_Σ ;;; (Γ0 ,,, iv_Γk) |-E tRel 0 : iv_kg.
  Proof. exact (typeE_Rel _ _ 0 (vass si_na (tApp (tRel 0) (tRel 1))) c18_tel_wf_Γk Logic.eq_refl). Qed.

  (** [y : k g] retyped at [k (λx:Prop. g x)] through the η step only. *)
  Lemma c18_tel_y_eta : iv_Σ ;;; (Γ0 ,,, iv_Γk) |-E tRel 0 : iv_keta.
  Proof.
    exact (typeE_Cumul _ _ (tRel 0) iv_kg iv_keta sProp c18_tel_y_typed c18_tel_keta_typed
             (c18_spec_eta (Γ0 ,,, iv_Γk))).
  Qed.

  Lemma c18_tel_hty_typed :
    iv_Σ ;;; (Γ0 ,,, iv_Γk) |-E c18_tel_hty : tSort (Sort.sort_of_product sProp (Sort.super sProp)).
  Proof.
    unfold c18_tel_hty. apply typeE_Prod.
    - exact (iv_vass_s iv_Σ (Γ0 ,,, iv_Γk) si_na iv_keta sProp c18_tel_keta_typed Logic.eq_refl).
    - exact (iv_P_typed iv_Σ _ (iv_wf_vass iv_Σ (Γ0 ,,, iv_Γk) si_na iv_keta sProp c18_tel_wf_Γk
                                  c18_tel_keta_typed Logic.eq_refl)).
  Qed.

  Lemma c18_tel_wf_Γh : wf_localE iv_Σ ((Γ0 ,,, iv_Γk) ,, vass si_na c18_tel_hty).
  Proof.
    exact (iv_wf_vass iv_Σ (Γ0 ,,, iv_Γk) si_na c18_tel_hty _ c18_tel_wf_Γk c18_tel_hty_typed Logic.eq_refl).
  Qed.

  (** [h y : Prop]: the η step of [c18_tel_y_eta] is inside this derivation. *)
  Lemma c18_tel_hy_typed : iv_Σ ;;; ((Γ0 ,,, iv_Γk) ,, vass si_na c18_tel_hty) |-E c18_tel_hy : si_P.
  Proof.
    have w := c18_tel_wf_Γh.
    exact (typeE_App _ _ (tRel 0) si_na (lift0 1 iv_keta) si_P _ (tRel 1)
             (weakeningE iv_Σ (Γ0 ,,, iv_Γk) [vass si_na c18_tel_hty] c18_tel_hty _ iv_wfE w c18_tel_hty_typed)
             (typeE_Rel _ _ 0 (vass si_na c18_tel_hty) w Logic.eq_refl)
             (weakeningE iv_Σ (Γ0 ,,, iv_Γk) [vass si_na c18_tel_hty] (tRel 0) iv_keta iv_wfE w c18_tel_y_eta)).
  Qed.

  Lemma c18_tel_wf : wf_localE iv_Σ (Γ0 ,,, c18_tel).
  Proof.
    exact (iv_wf_vass iv_Σ ((Γ0 ,,, iv_Γk) ,, vass si_na c18_tel_hty) si_na c18_tel_hy sProp
             c18_tel_wf_Γh c18_tel_hy_typed Logic.eq_refl).
  Qed.
End C18Tel.

(** [Γh := [g; k; y; h]] and [R (h y)], whose argument is typed through the η step. *)
Definition c18_Γh : context := iv_Γk ,, vass si_na c18_tel_hty.

Lemma c18_wf_Γh : wf_localE iv_Σ c18_Γh.
Proof. exact (c18_tel_wf_Γh [] localenv_nil). Qed.

Lemma c18_isT_Rhy : isTypeE iv_Σ c18_Γh (mkApps (tInd iv_ind []) [c18_tel_hy]).
Proof.
  exact (has_sort_isTypeE _ (iv_RX_typed c18_Γh c18_tel_hy c18_wf_Γh (c18_tel_hy_typed [] localenv_nil))).
Qed.

(** ** Instances in [iv_Σ] *)

Definition on_constructor_wf_argsE_inst :=
  on_constructor_wf_argsE (Σ := iv_env) (wfΣ := iv_wfE) iv_declared_constructor.

Definition on_constructor_substE_inst :=
  on_constructor_substE (Σ := iv_env) (wfΣ := iv_wfE) iv_declared_constructor.

(* The universe part is built at [J] ([on_constructor_instE_jinst]): the premises are a
   declaration and [consistent_instance_ext], and here [R] is monomorphic, so the only
   instance is [[]] and [subst_instance []] is the identity, while [J] has a constructor
   whose argument context moves with the instance. *)
Definition on_constructor_instE_inst :=
  on_constructor_instE (Σ := iv_Σ) (wfΣ := iv_wfE) iv_declared_constructor [] c18_cu.

(** The only premise is the typing of [R (h y)], whose argument [h y] is typed through the
    η step ([c18_tel_y_eta]). [R] has no variance, so the conclusion is at [AllEqual]. *)
Definition wt_ind_app_varianceE_inst :=
  wt_ind_app_varianceE (Σ := iv_Σ) (wfΣ := iv_wfE) (Γ := c18_Γh) c18_isT_Rhy.

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

(* NOT BUILT (the η step and the universe part). What is true: a comparison of one type at two
   universe instances CAN hold by an η step and fail in base — [I@{l0}] against [I@{l1}] below
   [I]'s arity is related by [ws_cumul_pbE_Ind_finst] ([ws_cumul_pbE_Ind_finst_inst]) and
   refuted by base's clause ([if_cumul_Ind_univ_fails]). It is not reached here because [R] is
   monomorphic (both instances are [], so the conclusion compares the projection's type with
   itself) and because neither [I] nor [J] has a projection ([ind_projs] of [J] is []): the
   witness needs a universe-polymorphic record WITH A PROJECTION whose type holds an
   under-applied occurrence of a variance-irrelevant inductive. *)
Definition projection_cumulative_indicesE_inst :=
  projection_cumulative_indicesE (Σ := iv_Σ) (wfΣ := iv_wfE) iv_declared_projection c18_onudecl c18_cu c18_cu
    (c18_cmp_ind (ind_npars iv_mdecl)).

Definition subslet_projs_smashE_inst :=
  subslet_projs_smashE iv_Σ iv_ind iv_mdecl iv_idecl iv_wfE iv_declared_inductive c18_onps iv_Γk (tRel 0) [].

(** A context related to itself. *)
Lemma c18_rel_refl (Σ : global_env_ext) (Γ Δ : context) :
  is_closed_context (Γ ,,, Δ) -> ws_cumul_ctx_pbE_rel Cumul Σ Γ Δ Δ.
Proof. intros h. apply ws_cumul_ctx_pbE_rel_app. now apply ws_cumul_ctx_pbE_refl_pb. Qed.

(* NOT BUILT (the η step). The universe part is built at [J]
   ([positive_cstr_closed_argsE_jinst]): the premise compares the constructor's argument
   context at the two instances, and here [R] is monomorphic, so both are [], while [J]'s
   [jc] has the argument [X : Type@{i}]: [Type@{Set}] at one instance, [Type@{a}] at the
   other. The η half needs an under-applied variance-irrelevant occurrence in it. *)
Definition positive_cstr_closed_argsE_inst :=
  positive_cstr_closed_argsE (Σ := iv_Σ) (wfΣ := iv_wfE) (u := []) (u' := []) iv_declared_constructor c18_cu c18_ru
    ltac:(apply c18_rel_refl; reflexivity).

Lemma c18_wf_ar_pars : wf_localE iv_Σ (subst_instance [] (ind_arities iv_mdecl ,,, smash_context [] (ind_params iv_mdecl) ,,, [])).
Proof.
  have h := on_constructor_wf_argsE_inst.
  apply All_local_env_app_inv in h as [h _]. exact h.
Qed.

(** The telescope [c18_tel] over the arities and the smashed parameters: its last entry
    [w : h y] is typed through the η step, so the [wf_localE] premise holds an η step.
    The universe part is built at [J] ([positive_cstr_closed_args_subst_aritiesE_jinst]):
    here [R] is monomorphic, so [u = u' = []] and the context comparison is reflexive,
    while at [J] the telescope is [X : Type@{Set}] against [X : Type@{a}]. *)
Lemma c18_wf_ar_pars_tel :
  wf_localE iv_Σ (subst_instance [] (ind_arities iv_mdecl ,,, smash_context [] (ind_params iv_mdecl) ,,, c18_tel)).
Proof. exact (c18_tel_wf _ c18_wf_ar_pars). Qed.

Lemma c18_pos_tel :
  All_local_env (fun Γ j => positive_cstr_arg iv_Σ.1 iv_mdecl []
    ([] ,,, (smash_context [] (ind_params iv_mdecl) ,,, Γ)) (j_typ j)) c18_tel.
Proof.
  repeat (apply localenv_cons_abs; [|cbn; apply pos_arg_closed; reflexivity]). exact localenv_nil.
Qed.

Lemma positive_cstr_closed_args_subst_aritiesE_inst :
  ws_cumul_ctx_pbE_rel Cumul iv_Σ (subst_instance [] (smash_context [] (ind_params iv_mdecl)))
    (subst_context (ind_subst iv_mdecl iv_ind []) (context_assumptions (ind_params iv_mdecl))
       (subst_instance [] c18_tel))
    (subst_context (ind_subst iv_mdecl iv_ind []) (context_assumptions (ind_params iv_mdecl))
       (subst_instance [] c18_tel)).
Proof.
  destruct (on_declared_constructorE (wfΣ := iv_wfE) iv_declared_constructor) as [_ [cs [_ onc]]].
  exact (positive_cstr_closed_args_subst_aritiesE (Σ := iv_Σ) (wfΣ := iv_wfE) (u := []) (u' := [])
           (Γ := c18_tel) iv_declared_inductive c18_cu onc c18_ru Logic.eq_refl c18_wf_ar_pars_tel
           c18_pos_tel ltac:(repeat constructor) ltac:(apply c18_rel_refl; reflexivity)).
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
            c18_if_onudecl c18_if_onvar Logic.eq_refl c18_if_cu0 c18_if_cu1 c18_if_var wc_T wc_U _).
  exact (c18_wc_ws (if_Σ.1, _) Cumul).
Qed.

(** The context [[x : I@{l0}]] at the two instances: the comparison of its one declaration is
    the under-applied F-inst pair, inside the variance environment of [I]. *)
Lemma All2_fold_instE_inst :
  ws_cumul_ctx_pbE_rel Cumul if_Σ (subst_instance [Level.lvar 0] ([] : context))
    (subst_instance [Level.lvar 0] [vass if_na (tInd if_ind [Level.lvar 0])])
    (subst_instance [Level.lvar 1] [vass if_na (tInd if_ind [Level.lvar 0])]).
Proof.
  refine (All2_fold_instE (Σ := if_Σ) (wfΣ := if_wfE) (le := Cumul) if_mdecl [Variance.Irrelevant] _ _ _
            [Level.lvar 0] [Level.lvar 1] [] [vass if_na (tInd if_ind [Level.lvar 0])]
            c18_if_onudecl c18_if_onvar c18_if_cu0 c18_if_cu1 Logic.eq_refl c18_if_var _).
  apply ws_cumul_ctx_pbE_rel_app. constructor; [constructor|].
  constructor; [reflexivity|].
  apply (ws_cumul_pbE_Ind_finst (l := []) (l' := []));
    [cbn; right; repeat constructor|reflexivity|constructor].
Qed.

Definition consistent_instance_poly_lengthE_inst :=
  consistent_instance_poly_lengthE (Σ := if_Σ) (wfΣ := if_wfE) c18_if_cu0.

Definition consistent_instance_validE_inst :=
  consistent_instance_validE (Σ := if_Σ) (wfΣ := if_wfE) c18_if_cu0 Logic.eq_refl.

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

(** ** Positivity in [if_Σ]: the under-applied F-inst pair

  [I] is universe-polymorphic with variance [Irrelevant] and arity one. Below that arity
  base's clause refutes [I@{l0}] against [I@{l1}] ([if_cumul_Ind_univ_fails]) while the η
  relation relates them through the full-arity variance ([ws_cumul_pbE_Ind_finst]). Each
  instance below takes its comparison premise through that pair, at the instances [l0] and
  [l1], either on the term itself or on the block's arity variable, which [ind_subst]
  replaces by [I] at the two instances. *)

Lemma c18_if_optvar : cmp_opt_variance (compare_universe if_Σ) Cumul
  (match ind_variance if_mdecl with Some var => Variance var | None => AllEqual end)
  [Level.lvar 0] [Level.lvar 1].
Proof. cbn. right. repeat constructor. Qed.

Lemma c18_if_nvok : nested_variance_ok if_mdecl.
Proof. cbn. constructor; [discriminate|constructor]. Qed.

Lemma c18_if_cl_ar : closed_ctx (ind_arities if_mdecl ,,, ([] : context))@[[Level.lvar 0]].
Proof. reflexivity. Qed.

Lemma c18_if_closed_ctx (Δ : context) : closed_ctx Δ -> is_closed_context Δ.
Proof. intros h. by rewrite -is_closed_ctx_closedE. Qed.

(** [I@{l0} ≤ I@{l1}] with no argument, in the arities context: the premise of
    [positive_cstr_arg_subst_closedE] at [t := I@{l0}]. *)
Lemma up_premise :
  ws_cumul_pbE Cumul if_Σ ((ind_arities if_mdecl)@[[Level.lvar 0]] ,,, ([] : context)@[[Level.lvar 0]])
    (tInd if_ind [Level.lvar 0])@[[Level.lvar 0]] (tInd if_ind [Level.lvar 0])@[[Level.lvar 1]].
Proof.
  apply (ws_cumul_pbE_Ind_finst (Σ := if_Σ) (l := []) (l' := []) (if_finst Cumul)); [reflexivity|constructor].
Qed.

(** The same pair, in any closed context, at [Conv]. *)
Lemma c18_if_conv_arity (Δ : context) : is_closed_context Δ ->
  ws_cumul_pbE Conv if_Σ Δ (tInd if_ind [Level.lvar 0]) (tInd if_ind [Level.lvar 1]).
Proof.
  intros h. apply (ws_cumul_pbE_Ind_finst (Σ := if_Σ) (l := []) (l' := []) (if_finst Conv));
    [exact h|constructor].
Qed.

(** Base's clause refutes the premise of [up_W6] in the same environment. *)
Definition up_base_fails := if_cumul_Ind_univ_fails Cumul.

Definition up_W6 :=
  positive_cstr_arg_subst_closedE (Σ := if_Σ) (wfΣ := if_wfE) (ind := if_ind) (mdecl := if_mdecl)
    (idecl := if_idecl) (Γ := []) (t := tInd if_ind [Level.lvar 0]) (pb := Cumul)
    (u := [Level.lvar 0]) (u' := [Level.lvar 1]) c18_if_declared c18_if_cu0 Logic.eq_refl up_premise.

(** The conversion premise is the F-inst pair, at two different instances. *)
Definition positive_cstr_arg_subst_closedE_inst := up_W6.

(** A β redex of [I@{l0}], and the arity variable under a β redex. *)
Definition c18_if_redex : term := tApp (tLambda if_na (tSort sProp) (tRel 0)) (tInd if_ind [Level.lvar 0]).
Definition c18_if_rel_redex : term := tApp (tLambda if_na (tSort sProp) (tRel 1)) (tSort sProp).

Lemma c18_if_red w (Ξ : context) : red if_Σ Ξ c18_if_redex@[w] (tInd if_ind [Level.lvar 0])@[w].
Proof. apply red1_red. apply red_beta. Qed.

Lemma c18_if_rel_red (Ξ : context) : red if_Σ Ξ c18_if_rel_redex (tRel 0).
Proof. apply red1_red. apply red_beta. Qed.

(* IMPOSSIBLE (the η step): the relation premise and the conclusion are [red], and [red1] has no
   η rule. The universe part is built: [u] and [v] are the two instances of [I], and the reduct
   is the arity variable, which [ind_subst] replaces by [I@{l1}]. *)
Definition red_subst_indsE_inst :=
  red_subst_indsE (Σ := if_Σ) (wfΣ := if_wfE) (ind := if_ind) (mdecl := if_mdecl) (Γ := []) (Δ := [])
    (a := c18_if_rel_redex) (b := tRel 0) (u := [Level.lvar 0]) (v := [Level.lvar 1])
    ltac:(constructor) c18_if_cl_ar Logic.eq_refl Logic.eq_refl c18_if_rel_red.

(* IMPOSSIBLE (the reduction premise): as [red_subst_indsE_inst]. The conversion premise and the
   conclusion are the F-inst pair: the arity variable at the two instances, which [ind_subst]
   replaces by [I@{l0}] and [I@{l1}] below the arity. *)
Definition positive_inds_conv_red_stepE_inst :=
  positive_inds_conv_red_stepE (Σ := if_Σ) (wfΣ := if_wfE) (ind := if_ind) (mdecl := if_mdecl)
    (Γ := []) (Δ := []) (t := c18_if_rel_redex) (t' := tRel 0)
    (u := [Level.lvar 0]) (u' := [Level.lvar 1]) ltac:(constructor) c18_if_cl_ar Logic.eq_refl
    Logic.eq_refl c18_if_rel_red Logic.eq_refl Logic.eq_refl
    (fun _ _ => c18_if_conv_arity [] Logic.eq_refl).

Lemma c18_if_whd : whd_rel true if_Σ.1 (arities_context (ind_bodies if_mdecl) ,,, ([] : context))
  (tSort sProp) [] (tSort sProp) [].
Proof. apply whd_stop. reflexivity. Qed.

(* IMPOSSIBLE (the [whd_rel] premise): it is a reduction, and [red1] has no η rule. The
   conversion premise and the conclusion are the F-inst pair, under one product. *)
Lemma positive_inds_conv_ass_redE_inst :
  ws_cumul_pbE Conv if_Σ []
    (subst (ind_subst if_mdecl if_ind [Level.lvar 0]) 0 (tProd if_na (tSort sProp) (tRel 1))@[[Level.lvar 1]])
    (subst (ind_subst if_mdecl if_ind [Level.lvar 1]) 0 (tProd if_na (tSort sProp) (tRel 1))@[[Level.lvar 1]]).
Proof.
  refine (positive_inds_conv_ass_redE (Σ := if_Σ) (wfΣ := if_wfE) (ind := if_ind) (mdecl := if_mdecl)
            (Γ := []) (Δ := []) (na := if_na) (ty := tSort sProp) (ty' := tRel 1) (h := tSort sProp)
            (l := []) (u := [Level.lvar 0]) (u' := [Level.lvar 1])
            ltac:(constructor) c18_if_cl_ar Logic.eq_refl Logic.eq_refl c18_if_whd Logic.eq_refl
            Logic.eq_refl Logic.eq_refl _).
  intros _ Δ' _ clΔ' _ _ _. exact (c18_if_conv_arity Δ' (c18_if_closed_ctx Δ' clΔ')).
Qed.

Lemma c18_if_at_i : mdecl_at_i if_mdecl if_idecl ([] : context) 0.
Proof. cbn. split; [constructor|split; [constructor|reflexivity]]. Qed.

Lemma c18_if_pos_concl : positive_cstr_arg if_Σ.1 if_mdecl [] [] (mkApps (tRel 0) [tSort sProp]).
Proof.
  apply (pos_arg_concl _ _ _ _ [tSort sProp] 0 if_idecl);
    [reflexivity|repeat constructor|exact c18_if_at_i].
Qed.

(* NOT BUILT (the η step): the conclusion compares the arity variable at the two instances, and
   [positive_cstr_arg] admits that variable only at FULL arity ([pos_arg_concl] asks
   [#|l| = ind_realargs]), where base's clause already relates [I@{l0}] and [I@{l1}] through the
   variance [Irrelevant]. An η-specific comparison needs the variable under-applied, which the
   predicate rejects, so the witness needs another inductive whose positivity derivation puts an
   under-applied occurrence in the compared term (a new inductive, a new environment and its
   [wfE] proof). The universe part is built: [u ≠ u']. *)
Definition positive_inds_convE_inst :=
  positive_inds_convE (Σ := if_Σ) (wfΣ := if_wfE) (ind := if_ind) (mdecl := if_mdecl) (idecl := if_idecl)
    (NI := []) (Γ := []) (p := mkApps (tRel 0) [tSort sProp]) (u := [Level.lvar 0])
    (u' := [Level.lvar 1]) (Δ := []) c18_if_declared c18_if_cu0 c18_if_optvar c18_if_nvok c18_if_cl_ar
    c18_if_pos_concl Logic.eq_refl Logic.eq_refl Logic.eq_refl Logic.eq_refl Logic.eq_refl
    ltac:(constructor).

(** The two β redexes of [I] at the two instances, related through their reducts. *)
Lemma up_premise7 : ws_cumul_pbE Cumul if_Σ
  ((ind_arities if_mdecl)@[[Level.lvar 0]] ,,, ([] : context)@[[Level.lvar 0]])
  c18_if_redex@[[Level.lvar 0]] c18_if_redex@[[Level.lvar 1]].
Proof.
  apply (ws_cumul_pb_red_stepE (Σ := if_Σ) (wfΣ := if_wfE) (pb := Cumul)
           (a' := (tInd if_ind [Level.lvar 0])@[[Level.lvar 0]])
           (b' := (tInd if_ind [Level.lvar 0])@[[Level.lvar 1]]));
    [reflexivity|reflexivity|reflexivity|apply c18_if_red|apply c18_if_red|intros _ _; exact up_premise].
Qed.

(* IMPOSSIBLE (the reduction premise): as [red_subst_indsE_inst]. Both conversion premises are
   the F-inst pair, on the redex and on its reduct. *)
Definition positive_cstr_arg_subst_red_stepE_inst :=
  positive_cstr_arg_subst_red_stepE (Σ := if_Σ) (wfΣ := if_wfE) (ind := if_ind) (mdecl := if_mdecl)
    (Γ := []) (t := c18_if_redex) (t' := tInd if_ind [Level.lvar 0]) (pb := Cumul)
    (u := [Level.lvar 0]) (u' := [Level.lvar 1]) ltac:(constructor) c18_if_cl_ar c18_if_red
    up_premise7 (fun _ => up_W6).

(** The nested inductive is [I] itself, under-applied: no argument of its one parameter. *)
Definition positive_cstr_arg_subst_nestedE_inst :=
  positive_cstr_arg_subst_nestedE (Σ := if_Σ) (wfΣ := if_wfE) (ind := if_ind) (mdecl := if_mdecl)
    (idecl := if_idecl) (NI := []) (Γ := []) (ind' := if_ind) (ui := [Level.lvar 0]) (args := [])
    (k := 0) (u := [Level.lvar 0]) (u' := [Level.lvar 1])
    c18_if_declared c18_if_cu0 c18_if_optvar c18_if_nvok c18_if_cl_ar Logic.eq_refl
    ltac:(constructor) ltac:(constructor) up_premise ltac:(constructor).

(** The conversion premise is the F-inst pair at the closed term [I@{l0}]. *)
Definition positive_cstr_arg_substE_inst :=
  positive_cstr_arg_substE (Σ := if_Σ) (wfΣ := if_wfE) (ind := if_ind) (mdecl := if_mdecl)
    (idecl := if_idecl) (Γ := []) (t := tInd if_ind [Level.lvar 0])
    (u := [Level.lvar 0]) (u' := [Level.lvar 1]) c18_if_declared c18_if_cu0 c18_if_optvar
    c18_if_cl_ar up_premise (pos_arg_closed _ _ _ _ (tInd if_ind [Level.lvar 0]) Logic.eq_refl)
    ltac:(constructor).

(** ** Universe witnesses at the polymorphic inductive [J]

  [PCUICEtaIdxEnv] declares
  [Polymorphic Cumulative Inductive J@{i} (A : Prop) : forall (X : Type@{i}), (fun Z => Z) Prop]
  with the covariant variance and the constructor [jc], whose only argument is the index
  [X : Type@{i}]. That argument is what [I] of [if_Σ] lacks: at the two instances [[Set]]
  and [[a]] the constructor's argument context is [X : Type@{Set}] against [X : Type@{a}],
  two DIFFERENT contexts related by [Set ≤ a], so the context comparison of the two rows
  below is not reflexivity. The file is required and not imported, and every name of it is
  written qualified.

  [J] does not serve [projection_cumulative_indicesE_inst]: [ind_projs J = []], and that row
  compares a projection's type at two instances. *)

Definition j18_Ta : term := tSort (sType (Universe.make' PCUICEtaIdxEnv.ji_a)).
Definition j18_Γ0 : context :=
  subst_instance PCUICEtaIdxEnv.ji_u0 (ind_arities PCUICEtaIdxEnv.ji_mdecl) ,,,
  subst_instance PCUICEtaIdxEnv.ji_u0 (smash_context [] (ind_params PCUICEtaIdxEnv.ji_mdecl)).

Lemma j18_cb : ClosedBodies PCUICEtaIdxEnv.ji_Σ.
Proof. exact (@wfE_ClosedBodies _ PCUICEtaIdxEnv.ji_Σ PCUICEtaIdxEnv.ji_wfE). Qed.

(** The two instances differ: [Type@{Set}] is not [Type@{a}]. *)
Lemma j18_args_move :
  eqb (subst_instance PCUICEtaIdxEnv.ji_u0 (cstr_args PCUICEtaIdxEnv.ji_cdecl))
      (subst_instance PCUICEtaIdxEnv.ji_u1 (cstr_args PCUICEtaIdxEnv.ji_cdecl)) = false.
Proof. reflexivity. Qed.

Lemma j18_leq_Set_a (Γ : context) :
  cumulSpecE0 PCUICEtaIdxEnv.ji_Σ Γ Cumul PCUICEtaIdxEnv.ji_TSet j18_Ta.
Proof.
  apply cumulE_Sort.
  change (leq0_universe_n 0 (global_ext_constraints PCUICEtaIdxEnv.ji_Σ)
            (Universe.make' Level.lzero) (Universe.make' PCUICEtaIdxEnv.ji_a)).
  intros v _. rewrite !Universe.val_make'. cbn. lia.
Qed.

Lemma j18_cmp_var :
  cmp_opt_variance (compare_universe PCUICEtaIdxEnv.ji_Σ) Cumul
    (match ind_variance PCUICEtaIdxEnv.ji_mdecl with
     | Some var => Variance var | None => AllEqual end)
    PCUICEtaIdxEnv.ji_u0 PCUICEtaIdxEnv.ji_u1.
Proof.
  cbn. right. constructor; [|constructor].
  change (leq0_universe_n 0 (global_ext_constraints PCUICEtaIdxEnv.ji_Σ)
            (Universe.make' Level.lzero) (Universe.make' PCUICEtaIdxEnv.ji_a)).
  intros v _. rewrite !Universe.val_make'. cbn. lia.
Qed.

Lemma j18_ws_sort :
  ws_cumul_pbE Cumul PCUICEtaIdxEnv.ji_Σ j18_Γ0 PCUICEtaIdxEnv.ji_TSet j18_Ta.
Proof.
  apply (into_ws_cumul_pbE_spec (Σ := PCUICEtaIdxEnv.ji_Σ) (wfΣ := j18_cb) (j18_leq_Set_a j18_Γ0));
    [reflexivity|reflexivity|reflexivity].
Qed.

(** The constructor's argument context at the two instances: [X : Type@{Set}] below
    [X : Type@{a}], not a reflexive comparison. *)
Lemma j18_tel_cumul :
  ws_cumul_ctx_pbE_rel Cumul PCUICEtaIdxEnv.ji_Σ j18_Γ0
    [vass PCUICEtaIdxEnv.ji_naX PCUICEtaIdxEnv.ji_TSet] [vass PCUICEtaIdxEnv.ji_naX j18_Ta].
Proof.
  apply ws_cumul_ctx_pbE_rel_app. constructor.
  - apply ws_cumul_ctx_pbE_refl_pb. reflexivity.
  - constructor; [reflexivity|exact j18_ws_sort].
Qed.

Definition on_constructor_instE_jinst :=
  on_constructor_instE (Σ := PCUICEtaIdxEnv.ji_Σ) (wfΣ := PCUICEtaIdxEnv.ji_wfE)
    PCUICEtaIdxEnv.ji_declared_constructor PCUICEtaIdxEnv.ji_u0 PCUICEtaIdxEnv.ji_cons0.

Lemma j18_wf_ar_pars_tel :
  wf_localE PCUICEtaIdxEnv.ji_Σ
    (subst_instance PCUICEtaIdxEnv.ji_u0
       (ind_arities PCUICEtaIdxEnv.ji_mdecl ,,,
        smash_context [] (ind_params PCUICEtaIdxEnv.ji_mdecl) ,,,
        cstr_args PCUICEtaIdxEnv.ji_cdecl)).
Proof. exact (fst on_constructor_instE_jinst). Qed.

Lemma j18_pos_tel :
  All_local_env (fun Γ j => positive_cstr_arg PCUICEtaIdxEnv.ji_Σ.1 PCUICEtaIdxEnv.ji_mdecl []
    ([] ,,, (smash_context [] (ind_params PCUICEtaIdxEnv.ji_mdecl) ,,, Γ)) (j_typ j))
    (cstr_args PCUICEtaIdxEnv.ji_cdecl).
Proof.
  repeat (apply localenv_cons_abs; [|cbn; apply pos_arg_closed; reflexivity]). exact localenv_nil.
Qed.

Definition positive_cstr_closed_argsE_jinst :=
  @positive_cstr_closed_argsE _ PCUICEtaIdxEnv.ji_Σ PCUICEtaIdxEnv.ji_wfE PCUICEtaIdxEnv.ji_u0
    PCUICEtaIdxEnv.ji_u1 (PCUICEtaIdxEnv.ji_ind, 0) PCUICEtaIdxEnv.ji_mdecl
    PCUICEtaIdxEnv.ji_idecl PCUICEtaIdxEnv.ji_cdecl PCUICEtaIdxEnv.ji_declared_constructor
    PCUICEtaIdxEnv.ji_cons0 j18_cmp_var j18_tel_cumul.

Lemma positive_cstr_closed_args_subst_aritiesE_jinst :
  ws_cumul_ctx_pbE_rel Cumul PCUICEtaIdxEnv.ji_Σ
    (subst_instance PCUICEtaIdxEnv.ji_u0 (smash_context [] (ind_params PCUICEtaIdxEnv.ji_mdecl)))
    (subst_context (ind_subst PCUICEtaIdxEnv.ji_mdecl PCUICEtaIdxEnv.ji_ind PCUICEtaIdxEnv.ji_u0)
       (context_assumptions (ind_params PCUICEtaIdxEnv.ji_mdecl))
       (subst_instance PCUICEtaIdxEnv.ji_u0 (cstr_args PCUICEtaIdxEnv.ji_cdecl)))
    (subst_context (ind_subst PCUICEtaIdxEnv.ji_mdecl PCUICEtaIdxEnv.ji_ind PCUICEtaIdxEnv.ji_u1)
       (context_assumptions (ind_params PCUICEtaIdxEnv.ji_mdecl))
       (subst_instance PCUICEtaIdxEnv.ji_u1 (cstr_args PCUICEtaIdxEnv.ji_cdecl))).
Proof.
  destruct (on_declared_constructorE (wfΣ := PCUICEtaIdxEnv.ji_wfE)
              PCUICEtaIdxEnv.ji_declared_constructor) as [_ [cs [_ onc]]].
  exact (positive_cstr_closed_args_subst_aritiesE (Σ := PCUICEtaIdxEnv.ji_Σ)
           (wfΣ := PCUICEtaIdxEnv.ji_wfE) (u := PCUICEtaIdxEnv.ji_u0) (u' := PCUICEtaIdxEnv.ji_u1)
           (Γ := cstr_args PCUICEtaIdxEnv.ji_cdecl) PCUICEtaIdxEnv.ji_declared_inductive
           PCUICEtaIdxEnv.ji_cons0 onc j18_cmp_var Logic.eq_refl j18_wf_ar_pars_tel
           j18_pos_tel ltac:(repeat constructor) j18_tel_cumul).
Qed.
