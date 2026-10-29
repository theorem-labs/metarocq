(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the lemmas of [PCUICPrincipalityEta] (row T2b)

  The forecast classes are section variables (no instance exists before their rows land).
  Non-degeneracy: [common_typingE_eta_inst] (two types of one variable related by η);
  T8 sites at types that are NOT head forms: [Sort_r] (a let-in, ζ), [Prod_r] and [Prod_l] (the
  let-bound variable [z], δ; [Prod_l] on [λP. x P], the η-expansion of [x]), [Ind_r] (the
  β-redex [(λB. R B) (∀P. P)], Proj case and [principal_type_indE_inst], whose two argument lists
  differ); [closed_red_confluence_cb_inst] (two different reducts); [chain_ws_cumul_pbE_Conv_inst]
  ([T ≠ H]); [typing_leq_termE_inst] ([Prop ≤ Set] in a codomain); [typing_eq_termE_inst] (two
  binder names). Degenerate by necessity: [invert_red_sort_cb_inst] (a sort has no reduct);
  [principal_typeE_case_inst]'s T8 site (reflexive reduct). *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICReduction PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICClosedBodies PCUICTypingEta
     PCUICTypingEtaInd PCUICTypingEtaNotions PCUICCumulativitySpecEtaClosureInstances PCUICEtaDefs
     PCUICEtaCanon PCUICEtaCanonRed PCUICEtaI5 PCUICWellScopedCumulativity PCUICWellScopedCumulativityEta
     PCUICEtaA6 PCUICEquality PCUICConversionEtaCongr PCUICClosedTypEta
     PCUICEtaPrimOpInstance PCUICInversionEtaInstances
     PCUICValidityEta PCUICSREta BDTyping BDTypingEta BDTypingEtaInstances BDToPCUICEta
     BDToPCUICEtaInstances BDFromPCUICEta BDFromPCUICEtaInstances PCUICPrincipalityEta.
From MetaRocq.PCUIC Require PCUICPrincipality PCUICContextConversion PCUICConversion PCUICEtaT8Probe.
From Equations.Type Require Import Relation Relation_Properties.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

(** ** The environments: [wf_extE] *)

Definition pr_si_wfext : wf_extE si_Σ := (si_wfE, si_on_udecl).
Definition pr_iv_wfext : wf_extE iv_Σ := (iv_wfE, si_on_udecl).
Definition pr_po_wfext : wf_extE Σ_po := wf_ext_incl_E iv_po_wf_ext.

#[local] Instance pr_iv_cb : ClosedBodies iv_env := @wfE_ClosedBodies _ iv_env iv_wfE.

(** ** Untyped helpers *)

(** [let z : Prop := ∀P:Prop. P in (λx:Prop. x) z] has two different one-step reducts: [ζ]
    gives [(λx:Prop. x) (∀P:Prop. P)], [β] under the let gives [let z := ∀P:Prop. P in z]. *)
Definition pr_let_beta : term := tLetIn si_na iv_False si_P (tApp iv_id (tRel 0)).

Lemma pr_let_beta_zeta : si_Σ ;;; [] ⊢ pr_let_beta ⇝ tApp iv_id iv_False.
Proof.
  exact (closed_red_of (Σ := si_Σ) (Γ := []) (t := pr_let_beta) Logic.eq_refl Logic.eq_refl
           (red1_red _ _ _ _ (PCUICReduction.red_zeta _ _ si_na iv_False si_P (tApp iv_id (tRel 0))))).
Qed.

Lemma pr_let_beta_body : si_Σ ;;; [] ⊢ pr_let_beta ⇝ tLetIn si_na iv_False si_P (tRel 0).
Proof.
  exact (closed_red_of (Σ := si_Σ) (Γ := []) (t := pr_let_beta) Logic.eq_refl Logic.eq_refl
           (red1_red _ _ _ _ (PCUICReduction.letin_red_body _ _ si_na iv_False si_P _ _
              (PCUICReduction.red_beta _ _ si_na si_P (tRel 0) (tRel 0))))).
Qed.

Lemma closed_red_confluence_cb_inst :
  ∑ v', si_Σ ;;; [] ⊢ tApp iv_id iv_False ⇝ v' × si_Σ ;;; [] ⊢ tLetIn si_na iv_False si_P (tRel 0) ⇝ v'.
Proof. exact (closed_red_confluence_cb pr_let_beta_zeta pr_let_beta_body). Qed.

(** A sort has no one-step reduct, so the only instance relates [Prop] to itself. *)
Lemma invert_red_sort_cb_inst : tSort sProp = tSort sProp.
Proof.
  exact (invert_red_sort_cb (Σ := si_Σ) [] sProp (tSort sProp)
           (closed_red_of (Σ := si_Σ) (Γ := []) (t := tSort sProp) Logic.eq_refl Logic.eq_refl (Equations.Type.Relation.rt_refl _ _))).
Qed.

(** A chain of one [R_c] step (β) from [canon ((λx:Prop. x) A)], in [A : Prop], to [A]. *)
Lemma pr_chain : Equations.Type.Relation.clos_refl_trans (Equations.Type.Relation.union (R_c si_Σ bd_Γ1) eta1) (canon (tApp iv_id (tRel 0))) (tRel 0).
Proof.
  have e : canon (tApp iv_id (tRel 0)) = tApp iv_id (tRel 0) by reflexivity.
  rewrite e. apply Equations.Type.Relation.rt_step. left. exists (tRel 0). split; [|reflexivity].
  exact (PCUICReduction.red_beta _ _ si_na si_P (tRel 0) (tRel 0)).
Qed.

Lemma chain_ws_cumul_pbE_Conv_inst : ws_cumul_pbE Conv si_Σ bd_Γ1 (tApp iv_id (tRel 0)) (tRel 0).
Proof. exact (chain_ws_cumul_pbE_Conv (Σ := si_Σ) bd_Γ1 (tApp iv_id (tRel 0)) (tRel 0) Logic.eq_refl Logic.eq_refl pr_chain). Qed.

(** ** Typing derivations, without any class *)

(** In [bdf_Γz = [x : z; z := ∀P:Prop. P]], [z : Prop]. *)
Lemma pr_z_typed : si_Σ ;;; bdf_Γz |-E tRel 1 : tSort sProp.
Proof. exact (typeE_Rel _ _ 1 (vdef si_na iv_False si_P) bdi_wf_subst1_prem Logic.eq_refl). Qed.

(** [z ⇝ ∀P:Prop. P], so [∀P:Prop. P ≤ z]. *)
Lemma pr_z_red : si_Σ ;;; bdf_Γz ⊢ tRel 1 ⇝ iv_False.
Proof.
  exact (closed_red_of (Σ := si_Σ) (Γ := bdf_Γz) (t := tRel 1) Logic.eq_refl Logic.eq_refl
           (red1_red _ _ _ _ (PCUICReduction.red_rel _ bdf_Γz 1 iv_False Logic.eq_refl))).
Qed.

Lemma pr_False_le_z : ws_cumul_pbE Cumul si_Σ bdf_Γz iv_False (tRel 1).
Proof. exact (red_ws_cumul_pbE_inv (Σ := si_Σ) pr_z_red). Qed.

(** [∀ (y : let z := ∀P. P in z). Prop]: the principal type of the domain is a let-in. *)
Definition pr_prod_let : term := tProd si_na bdf_let si_P.

Lemma pr_wf_let : wf_localE si_Σ ([] ,, vass si_na bdf_let).
Proof. exact (iv_wf_vass si_Σ [] si_na bdf_let sProp localenv_nil bdf_let_sort_typed Logic.eq_refl). Qed.

Lemma pr_prod_let_typed :
  si_Σ ;;; [] |-E pr_prod_let : tSort (Sort.sort_of_product sProp (Sort.super sProp)).
Proof.
  apply typeE_Prod.
  - exact (iv_vass_s si_Σ [] si_na bdf_let sProp bdf_let_sort_typed Logic.eq_refl).
  - exact (iv_P_typed si_Σ _ pr_wf_let).
Qed.

(** [x (∀P:Prop. P)] in [bdf_Γz]: the principal type of [x] is the variable [z]. *)
Lemma pr_app_z_typed : si_Σ ;;; bdf_Γz |-E tApp (tRel 0) iv_False : (tRel 0) {0 := iv_False}.
Proof.
  exact (typeE_App _ _ (tRel 0) si_na si_P (tRel 0) sProp iv_False
           (iv_False_typed si_Σ bdf_Γz bdi_wf_subst1_prem) bdf_x_prod_typed
           (iv_False_typed si_Σ bdf_Γz bdi_wf_subst1_prem)).
Qed.

(** [λP:Prop. x P], the η-expansion of [x], typed at [z] in [bdf_Γz]. *)
Definition pr_eta_x : term := tLambda si_na si_P (tApp (tRel 1) (tRel 0)).
Definition pr_Γzp : context := bdf_Γz ,, vass si_na si_P.

Lemma pr_wf_Γzp : wf_localE si_Σ pr_Γzp.
Proof. exact (iv_wf_P si_Σ bdf_Γz bdi_wf_subst1_prem). Qed.

Lemma pr_x_False_typed : si_Σ ;;; pr_Γzp |-E tRel 1 : iv_False.
Proof.
  eapply (typeE_Cumul _ _ (tRel 1) (tRel 2) iv_False sProp).
  - exact (typeE_Rel _ _ 1 (vass si_na (tRel 0)) pr_wf_Γzp Logic.eq_refl).
  - exact (iv_False_typed si_Σ pr_Γzp pr_wf_Γzp).
  - apply (ws_cumul_pbE_forget_spec (pb := Cumul)).
    apply (red_ws_cumul_pbE (Σ := si_Σ)).
    exact (closed_red_of (Σ := si_Σ) (Γ := pr_Γzp) (t := tRel 2) Logic.eq_refl Logic.eq_refl
             (red1_red _ _ _ _ (PCUICReduction.red_rel _ pr_Γzp 2 iv_False Logic.eq_refl))).
Qed.

Lemma pr_eta_x_False_typed : si_Σ ;;; bdf_Γz |-E pr_eta_x : iv_False.
Proof.
  apply typeE_Lambda.
  - exact (iv_vass si_Σ bdf_Γz si_na si_P _ (iv_P_typed si_Σ bdf_Γz bdi_wf_subst1_prem) Logic.eq_refl).
  - exact (typeE_App _ _ (tRel 1) si_na si_P (tRel 0) sProp (tRel 0)
             (iv_False_typed si_Σ pr_Γzp pr_wf_Γzp) pr_x_False_typed
             (typeE_Rel _ _ 0 (vass si_na si_P) pr_wf_Γzp Logic.eq_refl)).
Qed.

Lemma pr_eta_x_typed : si_Σ ;;; bdf_Γz |-E pr_eta_x : tRel 1.
Proof.
  exact (typeE_Cumul _ _ pr_eta_x iv_False (tRel 1) sProp pr_eta_x_False_typed pr_z_typed
           (ws_cumul_pbE_forget_spec pr_False_le_z)).
Qed.

(** In iv_Σ, [r : (λB:Prop. R B) (∀P:Prop. P)]: [r] has the inductive types [R (∀P:Prop. P)] and
    [R ((λx:Prop. x) (∀P:Prop. P))], and its principal type is the β-redex. *)
Definition pr_Γr : context := [vass si_na bdf_RFβ].

Lemma pr_wf_Γr : wf_localE iv_Σ pr_Γr.
Proof. exact (iv_wf_vass iv_Σ [] si_na bdf_RFβ sProp localenv_nil (bdf_RFβ_typed [] localenv_nil) Logic.eq_refl). Qed.

Lemma pr_r_typed : iv_Σ ;;; pr_Γr |-E tRel 0 : bdf_RFβ.
Proof. exact (typeE_Rel _ _ 0 (vass si_na bdf_RFβ) pr_wf_Γr Logic.eq_refl). Qed.

Lemma pr_RFβ_red : iv_Σ ;;; pr_Γr ⊢ bdf_RFβ ⇝ iv_RF.
Proof. exact (closed_red_of (Σ := iv_Σ) (Γ := pr_Γr) (t := bdf_RFβ) Logic.eq_refl Logic.eq_refl (bdf_RFβ_red pr_Γr)). Qed.

Lemma pr_r_RF_typed : iv_Σ ;;; pr_Γr |-E tRel 0 : mkApps (tInd iv_ind []) [iv_False].
Proof.
  exact (typeE_Cumul _ _ (tRel 0) bdf_RFβ iv_RF sProp pr_r_typed (iv_RF_typed pr_Γr pr_wf_Γr)
           (ws_cumul_pbE_forget_spec (red_ws_cumul_pbE (Σ := iv_Σ) (pb := Cumul) pr_RFβ_red))).
Qed.

Definition pr_idF : term := tApp iv_id iv_False.

Lemma pr_RidF_red : iv_Σ ;;; pr_Γr ⊢ iv_R pr_idF ⇝ iv_RF.
Proof.
  exact (closed_red_of (Σ := iv_Σ) (Γ := pr_Γr) (t := iv_R pr_idF) Logic.eq_refl Logic.eq_refl
           (red1_red _ _ _ _ (PCUICReduction.app_red_r _ _ _ _ _ (PCUICReduction.red_beta _ _ si_na si_P (tRel 0) iv_False)))).
Qed.

Lemma pr_r_RidF_typed : iv_Σ ;;; pr_Γr |-E tRel 0 : mkApps (tInd iv_ind []) [pr_idF].
Proof.
  refine (typeE_Cumul _ _ (tRel 0) bdf_RFβ (iv_R pr_idF) sProp pr_r_typed
           (iv_RX_typed pr_Γr pr_idF pr_wf_Γr (iv_app_typed iv_Σ pr_Γr pr_wf_Γr)) _).
  apply (ws_cumul_pbE_forget_spec (pb := Cumul)).
  exact (ws_cumul_pbE_trans (Σ := iv_Σ) _ _ _ (red_ws_cumul_pbE (Σ := iv_Σ) pr_RFβ_red)
           (red_ws_cumul_pbE_inv (Σ := iv_Σ) pr_RidF_red)).
Qed.

(** [f r : ∀P:Prop. P], the projection of [r]. *)
Lemma pr_proj_typed : iv_Σ ;;; pr_Γr |-E tProj iv_proj (tRel 0) : iv_False.
Proof.
  exact (typeE_Proj _ _ iv_proj (tRel 0) [] iv_mdecl iv_idecl iv_cdecl iv_pdecl [iv_False]
           iv_declared_projection pr_r_RF_typed Logic.eq_refl).
Qed.

(** [∀_:Prop. Set], a type of the sort [pr_sPS]; [∀_:Prop. Prop] is below it up to universes. *)
Definition pr_PS : term := tProd si_na si_P (tSort Sort.type0).
Definition pr_sPS : Universes.sort := Sort.sort_of_product (Sort.super sProp) (Sort.super Sort.type0).

Lemma pr_PS_typed : si_Σ ;;; [] |-E pr_PS : tSort pr_sPS.
Proof.
  apply typeE_Prod.
  - exact (iv_vass_s si_Σ [] si_na si_P _ (iv_P_typed si_Σ [] localenv_nil) Logic.eq_refl).
  - apply typeE_Sort; [exact (iv_wf_P si_Σ [] localenv_nil)|apply/(PCUICWfUniverses.wf_sort_reflect si_Σ); reflexivity].
Qed.

Lemma pr_PP_leq_PS : leq_term empty_global_env si_Σ iv_PP pr_PS.
Proof. constructor; [reflexivity|constructor; reflexivity|constructor; cbn; trivial]. Qed.

(** [λx:Prop. x] with the binder name [x] instead of the anonymous one. *)
Definition pr_nx : aname := mkBindAnn (nNamed "x") Relevant.
Definition pr_lam' : term := tLambda pr_nx si_P (tRel 0).

Lemma pr_lam'_typed : si_Σ ;;; [] |-E pr_lam' : tProd pr_nx si_P si_P.
Proof.
  have w := iv_wf_vass si_Σ [] pr_nx si_P _ localenv_nil (iv_P_typed si_Σ [] localenv_nil) Logic.eq_refl.
  apply typeE_Lambda.
  - exact (iv_vass si_Σ [] pr_nx si_P _ (iv_P_typed si_Σ [] localenv_nil) Logic.eq_refl).
  - exact (typeE_Rel _ _ 0 (vass pr_nx si_P) w Logic.eq_refl).
Qed.

Lemma pr_id_eq_lam' : eq_term empty_global_env si_Σ iv_id pr_lam'.
Proof. constructor; [reflexivity|constructor; reflexivity|constructor]. Qed.

(** ** The lemmas of [PCUICPrincipalityEta], at concrete arguments *)

Lemma isWfArity_sortE_inst : isWfArityE si_Σ iv_Γ1 (tSort sProp).
Proof. exact (isWfArity_sortE si_Σ iv_Γ1 sProp iv_wf_Γ1 I). Qed.

Section PrincipalityEtaInstances.

(* FORECAST-ONLY: the four classes of [PCUICPrincipalityEta]; delete each when its row lands. *)
Context {V16 : ValForecastCopy16} {F16 : SRForecastCopy16} {F18 : SRForecastCopy18}
  {BF18 : BDFromForecastCopy18}.

(** [Prod_l] at the variable [z], which reduces to [∀P:Prop. P] by unfolding the let. *)
Lemma T8_Prod_l_plug_inst :
  ∑ na' dom' codom',
    [× si_Σ ;;; bdf_Γz ⊢ tRel 1 ⇝ tProd na' dom' codom', eq_binder_annot si_na na',
       ws_cumul_pbE Conv si_Σ bdf_Γz si_P dom' &
       ws_cumul_pbE Cumul si_Σ (bdf_Γz ,, vass si_na si_P) (tRel 0) codom'].
Proof. exact (T8_Prod_l_plug _ si_Σ bdf_Γz Cumul (tRel 1) si_na si_P (tRel 0) sProp si_wfE pr_z_typed pr_False_le_z). Qed.

Lemma T8_Prod_l_of_r_inst :
  ∑ na' dom' codom',
    [× si_Σ ;;; bdf_Γz ⊢ tRel 1 ⇝ tProd na' dom' codom', eq_binder_annot si_na na',
       ws_cumul_pbE Conv si_Σ bdf_Γz si_P dom' &
       ws_cumul_pbE Cumul si_Σ (bdf_Γz ,, vass si_na si_P) (tRel 0) codom'].
Proof.
  exact (T8_Prod_l_of_r si_Σ (T8_Prod_r_plug _ si_Σ) bdf_Γz Cumul (tRel 1) si_na si_P (tRel 0) sProp
           si_wfE pr_z_typed pr_False_le_z).
Qed.

(** The two types of [x : G (λy:Prop. F y)] in [bd_Γη]: its declared type and [G F] (η). *)
Lemma common_typingE_eta_inst :
  ∑ C, si_Σ ;;; bd_Γη ⊢E C ≤ lift0 1 bd_X × si_Σ ;;; bd_Γη ⊢E C ≤ tApp (tRel 2) (tRel 1) ×
       si_Σ ;;; bd_Γη |-E tRel 0 : C.
Proof.
  exact (common_typingE si_Σ pr_si_wfext (typeE_Rel _ _ 0 (vass si_na bd_X) bdi_wfη Logic.eq_refl) bdf_eta_typed).
Qed.

Lemma principal_typeE_eta_inst :
  ∑ C, si_Σ ;;; bd_Γη ⊢E C ≤ tApp (tRel 2) (tRel 1) × si_Σ ;;; bd_Γη |-E tRel 0 : C.
Proof.
  destruct (principal_typeE si_Σ pr_si_wfext bdf_eta_typed) as [C HC].
  exists C. exact (HC _ bdf_eta_typed).
Qed.

(** T8 [Sort_r]: the principal type of the domain [let z := ∀P. P in z] is the let-in
    [let z := ∀P. P in Prop], reduced to [Prop] by ζ. *)
Lemma principal_typeE_sort_r_inst :
  ∑ C, si_Σ ;;; [] ⊢E C ≤ tSort (Sort.sort_of_product sProp (Sort.super sProp)) ×
       si_Σ ;;; [] |-E pr_prod_let : C.
Proof.
  destruct (principal_typeE si_Σ pr_si_wfext pr_prod_let_typed) as [C HC].
  exists C. exact (HC _ pr_prod_let_typed).
Qed.

(** T8 [Prod_r]: the principal type of [x] is [z], reduced to [∀P:Prop. P] by unfolding. *)
Lemma principal_typeE_prod_r_inst :
  ∑ C, si_Σ ;;; bdf_Γz ⊢E C ≤ (tRel 0) {0 := iv_False} × si_Σ ;;; bdf_Γz |-E tApp (tRel 0) iv_False : C.
Proof.
  destruct (principal_typeE si_Σ pr_si_wfext pr_app_z_typed) as [C HC].
  exists C. exact (HC _ pr_app_z_typed).
Qed.

(** T8 [Prod_l]: [λP:Prop. x P] at the type [z], which reduces to a product by unfolding. *)
Lemma principal_typeE_prod_l_inst :
  ∑ C, si_Σ ;;; bdf_Γz ⊢E C ≤ tRel 1 × si_Σ ;;; bdf_Γz |-E pr_eta_x : C.
Proof.
  destruct (principal_typeE si_Σ pr_si_wfext pr_eta_x_False_typed) as [C HC].
  exists C. exact (HC _ pr_eta_x_typed).
Qed.

(** T8 [Ind_r], Proj case: the principal type of [r] is the β-redex [(λB:Prop. R B) (∀P. P)]. *)
Lemma principal_typeE_proj_inst :
  ∑ C, iv_Σ ;;; pr_Γr ⊢E C ≤ iv_False × iv_Σ ;;; pr_Γr |-E tProj iv_proj (tRel 0) : C.
Proof.
  destruct (principal_typeE iv_Σ pr_iv_wfext pr_proj_typed) as [C HC].
  exists C. exact (HC _ pr_proj_typed).
Qed.

(** T8 [Ind_r], Case case, on [iv_match]: the principal type of the scrutinee is an applied
    inductive already, so the reduction at this site is reflexive. *)
Lemma principal_typeE_case_inst :
  ∑ C, si_Σ ;;; iv_Γ1 ⊢E C ≤ iv_match_ty × si_Σ ;;; iv_Γ1 |-E iv_match : C.
Proof.
  destruct (principal_typeE si_Σ pr_si_wfext iv_match_typed) as [C HC].
  exists C. exact (HC _ iv_match_typed).
Qed.

(** The other typing rules, on the derivations of [PCUICInversionEtaInstances]. *)
Definition principal_typeE_Rel_inst := principal_typeE si_Σ pr_si_wfext iv_x_typed.
Definition principal_typeE_Sort_inst := principal_typeE si_Σ pr_si_wfext (iv_P_typed si_Σ [] localenv_nil).
Definition principal_typeE_Prod_inst := principal_typeE si_Σ pr_si_wfext (iv_PP_typed si_Σ [] localenv_nil).
Definition principal_typeE_Lambda_inst := principal_typeE si_Σ pr_si_wfext (iv_id_typed si_Σ [] localenv_nil).
Definition principal_typeE_LetIn_inst := principal_typeE si_Σ pr_si_wfext (iv_let_typed si_Σ [] localenv_nil).
Definition principal_typeE_App_inst := principal_typeE si_Σ pr_si_wfext (iv_app_typed si_Σ [] localenv_nil).
Definition principal_typeE_Ind_inst := principal_typeE si_Σ pr_si_wfext (iv_ind_typed [] localenv_nil).
Definition principal_typeE_Construct_inst := principal_typeE si_Σ pr_si_wfext (iv_cstr_typed [] localenv_nil).
Definition principal_typeE_Fix_inst := principal_typeE si_Σ pr_si_wfext iv_fix_typed.
Definition principal_typeE_CoFix_inst := principal_typeE iv_Σ pr_iv_wfext iv_cofix_typed.
Definition principal_typeE_Const_inst := principal_typeE Σ_po pr_po_wfext iv_land_typed.
Definition principal_typeE_Prim_inst := principal_typeE Σ_po pr_po_wfext iv_prim_typed.

(** [r : R (∀P. P)] and [r : R ((λx:Prop. x) (∀P. P))]: the argument lists differ, and the
    principal type of [r] (T8 [Ind_r], twice) is the β-redex. *)
Lemma principal_type_indE_inst :
  (∑ ui',
    cmp_ind_universes iv_Σ iv_ind #|[iv_False]| ui' [] *
    cmp_ind_universes iv_Σ iv_ind #|[pr_idF]| ui' []) *
  ws_cumul_pbE_terms iv_Σ pr_Γr [iv_False] [pr_idF] *
  (iv_ind = iv_ind).
Proof. exact (principal_type_indE (wfΣ := pr_iv_wfext) pr_r_RF_typed pr_r_RidF_typed). Qed.

(** [typing_leq_termE]: [∀_:Prop. Prop ≤ ∀_:Prop. Set] up to universes (the codomain at
    [Cumul], [Prop ≤ Set]): the term [∀_:Prop. Prop] gets the type of [∀_:Prop. Set]. *)
Lemma typing_leq_termE_inst : si_Σ ;;; [] |-E iv_PP : tSort pr_sPS.
Proof.
  exact (typing_leq_termE si_Σ [] pr_PS iv_PP (tSort pr_sPS) (tSort iv_sPP) si_wfE si_on_udecl
           pr_PS_typed (iv_PP_typed si_Σ [] localenv_nil) pr_PP_leq_PS).
Qed.

(** [typing_eq_termE]: [λx:Prop. x] with two binder names; the second term gets the type of
    the first. *)
Lemma typing_eq_termE_inst : si_Σ ;;; [] |-E pr_lam' : iv_PP.
Proof.
  exact (typing_eq_termE si_Σ [] iv_id pr_lam' iv_PP (tProd pr_nx si_P si_P) pr_si_wfext
           (iv_id_typed si_Σ [] localenv_nil) pr_lam'_typed pr_id_eq_lam').
Qed.

End PrincipalityEtaInstances.

(** ** Assumptions: base's lemmas, then their E copies *)

Print Assumptions PCUICPrincipality.principal_type.
Print Assumptions principal_typeE.
Print Assumptions PCUICPrincipality.common_typing.
Print Assumptions common_typingE.
Print Assumptions PCUICPrincipality.principal_type_ind.
Print Assumptions principal_type_indE.
Print Assumptions PCUICPrincipality.isWfArity_sort.
Print Assumptions isWfArity_sortE.
Print Assumptions PCUICContextConversion.closed_red_confluence.
Print Assumptions closed_red_confluence_cb.
Print Assumptions PCUICConversion.invert_red_sort.
Print Assumptions invert_red_sort_cb.
Print Assumptions chain_ws_cumul_pbE_Conv.
Print Assumptions T8_Prod_l_of_r.
Print Assumptions T8_Prod_l_plug_fit.
Print Assumptions principal_typeE_prod_l_inst.
Print Assumptions principal_typeE_proj_inst.
Print Assumptions principal_type_indE_inst.
Print Assumptions PCUICPrincipality.typing_leq_term.
Print Assumptions typing_leq_termE.
Print Assumptions PCUICPrincipality.typing_eq_term.
Print Assumptions typing_eq_termE.
Print Assumptions typing_leq_termE_inst.
Print Assumptions typing_eq_termE_inst.
About principal_typeE.
