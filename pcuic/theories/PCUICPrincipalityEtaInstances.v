(* Distributed under the terms of the MIT license. *)

(* NONDEGEN tags: an INSTANCE NONDEGEN tag is a reader judgment backed by a compiled nontriviality
   lemma; the measured reader miss rate is recorded in lanes/eta/meta/reader-catch-rate.tsv. *)

(** * Satisfying instances of the lemmas of [PCUICPrincipalityEta] (row T2b)

  No forecast class: T1's [SRForecastCopy18], a section variable here until copy 18b landed
  (frac/eta 3e6b422d), is deleted.
  Non-degeneracy: each instance is tagged for the instance gate in the comment directly above it
  (its non-degeneracy lemma, or the reason its row is degenerate by the statement;
  [isWfArity_sortE_inst] and [invert_red_sort_cb_inst] are tagged IMPOSSIBLE).
  [common_typingE_eta_inst] and [principal_typeE_eta_inst]: two types of one variable, its
  declared type and the type it η-contracts to ([pr_eta_types_nondeg]). Inputs chosen for T8
  sites, at types that are NOT head forms; each lemma states the type and its one step to a head
  form, and no lemma here states which site a run of the proof reaches: [Sort_r] (a let-in type,
  ζ), [Prod_r] and [Prod_l] (the let-bound variable [z], δ; [Prod_l] on [λP. x P], the
  η-expansion of [x]), [Ind_r] (the β-redex [(λB. R B) (∀P. P)], Proj case and
  [principal_type_indE_inst], whose two argument lists differ; the let-in type
  [let y := x in I y] of the scrutinee of [PCUICProgressEtaInstances.pgi_match_let_open], Case
  case, ζ); [closed_red_confluence_cb_inst] (two different one-step reducts);
  [chain_ws_cumul_pbE_Conv_inst] ([T ≠ H], one β step); [typing_leq_termE_inst] ([Prop ≤ Set]
  in a codomain); [typing_eq_termE_inst] (two binder names). The rule-coverage instances apply
  [principal_typeE] to terms of twelve different head formers and compare the returned principal
  type with a β-wrapped type that differs from the type of the derivation it was built from
  ([principal_typeE_rules_nondeg]). *)

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
From MetaRocq.PCUIC Require PCUICPrincipality PCUICContextConversion PCUICConversion PCUICEtaT8Probe
     PCUICProgressEtaInstances.
From Equations.Type Require Import Relation Relation_Properties.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

(** Declarations of this file that are neither instances nor non-degeneracy lemmas (instance gate):
    WITNESSES: pr_* *)

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

(** [pr_let_beta] reduces in one step to each of two different terms: [(λx:Prop. x) (∀P:Prop. P)]
    (ζ) and [let z := ∀P:Prop. P in z] (β under the let). *)
Lemma closed_red_confluence_cb_inst_nondeg :
  tApp iv_id iv_False <> tLetIn si_na iv_False si_P (tRel 0) /\
  ∥ red1 si_Σ [] pr_let_beta (tApp iv_id iv_False) ∥ /\
  ∥ red1 si_Σ [] pr_let_beta (tLetIn si_na iv_False si_P (tRel 0)) ∥.
Proof.
  split; [discriminate|]. split; constructor.
  - exact (PCUICReduction.red_zeta _ _ si_na iv_False si_P (tApp iv_id (tRel 0))).
  - exact (PCUICReduction.letin_red_body _ _ si_na iv_False si_P _ _
             (PCUICReduction.red_beta _ _ si_na si_P (tRel 0) (tRel 0))).
Qed.

(** INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.closed_red_confluence_cb_inst_nondeg *)
Lemma closed_red_confluence_cb_inst :
  ∑ v', si_Σ ;;; [] ⊢ tApp iv_id iv_False ⇝ v' × si_Σ ;;; [] ⊢ tLetIn si_na iv_False si_P (tRel 0) ⇝ v'.
Proof.
  exact (closed_red_confluence_cb (u := tApp iv_id iv_False) (v := tLetIn si_na iv_False si_P (tRel 0))
           pr_let_beta_zeta pr_let_beta_body).
Qed.

(** A sort has no one-step reduct, so the only instance relates [Prop] to itself.
    INSTANCE IMPOSSIBLE: the conclusion is [v = tSort u] and a sort has no one-step reduct, so in every [Σ] and [Γ] the premise [Σ ;;; Γ ⊢ tSort u ⇝ v] forces [v = tSort u]: every instance concludes [tSort u = tSort u]. *)
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

(** [T ≠ H]; [canon T] is [T] itself, the β-redex [(λx:Prop. x) A], which reduces to [H = A] in
    one β step: the chain from [canon T] to [H] is not empty. *)
Lemma chain_ws_cumul_pbE_Conv_inst_nondeg :
  tApp iv_id (tRel 0) <> tRel 0 /\ canon (tApp iv_id (tRel 0)) = tApp iv_id (tRel 0) /\
  ∥ red1 si_Σ bd_Γ1 (tApp iv_id (tRel 0)) (tRel 0) ∥.
Proof.
  split; [discriminate|]. split; [reflexivity|]. constructor.
  exact (PCUICReduction.red_beta _ _ si_na si_P (tRel 0) (tRel 0)).
Qed.

(** INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.chain_ws_cumul_pbE_Conv_inst_nondeg *)
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

(** [∀ (y : let z := ∀P. P in z). Prop]: its domain is a let-in. *)
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

(** [x (∀P:Prop. P)] in [bdf_Γz]: [x] is declared at the variable [z]. *)
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

(** In iv_Σ, [r : (λB:Prop. R B) (∀P:Prop. P)]: [r] is declared at the β-redex, and has the
    inductive types [R (∀P:Prop. P)] and [R ((λx:Prop. x) (∀P:Prop. P))]. *)
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

(** [isWfArity_sortE] at [Set], in the non-empty context [iv_Γ1 = [A : Prop]].
    INSTANCE IMPOSSIBLE: the target's proof only packs its own premises: it applies the sort constructor typeE_Sort to the premises wf_sort Σ u and wf_localE Σ Γ (through isType_SortE, PCUICAritiesEta.v:86-94) and gives the arity witness ([], u), whose equation destArity [] (tSort u) = Some ([], u) holds by computation (PCUICPrincipalityEta.v:186-193), so in every environment, context and sort the conclusion isWfArityE Σ Γ (tSort u) is assembled from the instance's own premises, and no instance exercises more. *)
Lemma isWfArity_sortE_inst : isWfArityE si_Σ iv_Γ1 (tSort Sort.type0).
Proof.
  apply (isWfArity_sortE si_Σ iv_Γ1 Sort.type0 iv_wf_Γ1).
  apply/(PCUICWfUniverses.wf_sort_reflect si_Σ). reflexivity.
Qed.

Section PrincipalityEtaInstances.

(** The variable [z] ([tRel 1] in [bdf_Γz = [x : z; z := ∀P:Prop. P]]) is not a product; it is
    let-bound to [∀P:Prop. P] and unfolds (δ) to it in one step; [x] ([tRel 0]) is declared at
    [z] ([tRel 1] after the lift), and every type inferred for [x] is [z]. *)
Lemma pr_z_delta_nondeg :
  (forall na A B, tRel 1 <> tProd na A B) /\ nth_error bdf_Γz 1 = Some (vdef si_na iv_False si_P) /\
  ∥ red1 si_Σ bdf_Γz (tRel 1) iv_False ∥ /\
  option_map (fun d => lift0 1 (decl_type d)) (nth_error bdf_Γz 0) = Some (tRel 1) /\
  (forall T', si_Σ ;;; bdf_Γz |-E tRel 0 ▹ T' -> T' = tRel 1).
Proof.
  split; [intros na A B; discriminate|]. split; [reflexivity|].
  split; [constructor; exact (PCUICReduction.red_rel _ bdf_Γz 1 iv_False Logic.eq_refl)|].
  split; [reflexivity|].
  intros T' h. inversion h; subst.
  match goal with hn : nth_error _ _ = Some _ |- _ => vm_compute in hn; injection hn as hd; subst end.
  reflexivity.
Qed.

(** [Prod_l] at the variable [z], which is not a product and unfolds (δ) to [∀P:Prop. P] in one
    step ([pr_z_delta_nondeg]).
    INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.pr_z_delta_nondeg *)
Lemma T8_Prod_l_plug_inst :
  ∑ na' dom' codom',
    [× si_Σ ;;; bdf_Γz ⊢ tRel 1 ⇝ tProd na' dom' codom', eq_binder_annot si_na na',
       ws_cumul_pbE Conv si_Σ bdf_Γz si_P dom' &
       ws_cumul_pbE Cumul si_Σ (bdf_Γz ,, vass si_na si_P) (tRel 0) codom'].
Proof. exact (T8_Prod_l_plug _ si_Σ bdf_Γz Cumul (tRel 1) si_na si_P (tRel 0) sProp si_wfE pr_z_typed pr_False_le_z). Qed.

(** INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.pr_z_delta_nondeg *)
Lemma T8_Prod_l_of_r_inst :
  ∑ na' dom' codom',
    [× si_Σ ;;; bdf_Γz ⊢ tRel 1 ⇝ tProd na' dom' codom', eq_binder_annot si_na na',
       ws_cumul_pbE Conv si_Σ bdf_Γz si_P dom' &
       ws_cumul_pbE Cumul si_Σ (bdf_Γz ,, vass si_na si_P) (tRel 0) codom'].
Proof.
  exact (T8_Prod_l_of_r si_Σ (T8_Prod_r_plug _ si_Σ) bdf_Γz Cumul (tRel 1) si_na si_P (tRel 0) sProp
           si_wfE pr_z_typed pr_False_le_z).
Qed.

(** In [bd_Γη], [x] is declared at [G (λy:Prop. F y)]; lifted, that type is not [G F] and
    η-contracts to [G F] in one step. *)
Lemma pr_eta_types_nondeg :
  nth_error bd_Γη 0 = Some (vass si_na bd_X) /\ lift0 1 bd_X <> tApp (tRel 2) (tRel 1) /\
  ∥ eta1 (lift0 1 bd_X) (tApp (tRel 2) (tRel 1)) ∥.
Proof. split; [reflexivity|]. split; [discriminate|]. constructor. exact bd_eta_step. Qed.

(** The two types of [x] in [bd_Γη]: its declared type [G (λy:Prop. F y)] (lifted) and [G F],
    which differ, the first η-contracting to the second in one step ([pr_eta_types_nondeg]).
    INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.pr_eta_types_nondeg
    TARGET PCUICPrincipalityEta.common_typingE *)
Lemma common_typingE_eta_inst :
  ∑ C, si_Σ ;;; bd_Γη ⊢E C ≤ lift0 1 bd_X × si_Σ ;;; bd_Γη ⊢E C ≤ tApp (tRel 2) (tRel 1) ×
       si_Σ ;;; bd_Γη |-E tRel 0 : C.
Proof.
  exact (common_typingE si_Σ pr_si_wfext (typeE_Rel _ _ 0 (vass si_na bd_X) bdi_wfη Logic.eq_refl) bdf_eta_typed).
Qed.

(** The principal type of [x], from its declared typing [x : G (λy:Prop. F y)], is below [G F],
    to which the declared type η-contracts in one step ([pr_eta_types_nondeg]).
    INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.pr_eta_types_nondeg
    TARGET PCUICPrincipalityEta.principal_typeE *)
Lemma principal_typeE_eta_inst :
  ∑ C, si_Σ ;;; bd_Γη ⊢E C ≤ tApp (tRel 2) (tRel 1) × si_Σ ;;; bd_Γη |-E tRel 0 : C.
Proof.
  destruct (principal_typeE si_Σ pr_si_wfext (typeE_Rel _ _ 0 (vass si_na bd_X) bdi_wfη Logic.eq_refl))
    as [C HC].
  exists C. exact (HC _ bdf_eta_typed).
Qed.

(** The domain of [pr_prod_let] is the let-in [bdf_let]; every type inferred for [bdf_let] is
    [let z := ∀P:Prop. P in Prop] (and [bdf_let] has that type), which is not a sort and
    ζ-reduces to [Prop] in one step. *)
Lemma principal_typeE_sort_r_inst_nondeg :
  pr_prod_let = tProd si_na bdf_let si_P /\ (forall s, tLetIn si_na iv_False si_P si_P <> tSort s) /\
  ∥ si_Σ ;;; [] |-E bdf_let : tLetIn si_na iv_False si_P si_P ∥ /\
  ∥ red1 si_Σ [] (tLetIn si_na iv_False si_P si_P) si_P ∥ /\
  (forall T', si_Σ ;;; [] |-E bdf_let ▹ T' -> T' = tLetIn si_na iv_False si_P si_P).
Proof.
  split; [reflexivity|]. split; [intros s; discriminate|].
  split; [constructor; exact (iv_let_typed si_Σ [] localenv_nil)|].
  split; [constructor; exact (PCUICReduction.red_zeta _ _ si_na iv_False si_P si_P)|].
  intros T' h. unfold bdf_let in h. inversion h; subst.
  match goal with hb : _ ;;; _ |-E tRel 0 ▹ _ |- _ => inversion hb; subst end.
  match goal with hn : nth_error _ _ = Some _ |- _ => vm_compute in hn; injection hn as hd; subst end.
  reflexivity.
Qed.

(** Chosen for T8 [Sort_r]: the product [pr_prod_let], whose domain [let z := ∀P. P in z] has the
    inferred type [let z := ∀P. P in Prop] (every type inferred for it is that let-in), which is
    not a sort and ζ-reduces to [Prop] in one step ([principal_typeE_sort_r_inst_nondeg]).
    INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.principal_typeE_sort_r_inst_nondeg
    TARGET PCUICPrincipalityEta.principal_typeE *)
Lemma principal_typeE_sort_r_inst :
  ∑ C, si_Σ ;;; [] ⊢E C ≤ tSort (Sort.sort_of_product sProp (Sort.super sProp)) ×
       si_Σ ;;; [] |-E pr_prod_let : C.
Proof.
  destruct (principal_typeE si_Σ pr_si_wfext (u := pr_prod_let) pr_prod_let_typed) as [C HC].
  exists C. exact (HC _ pr_prod_let_typed).
Qed.

(** Chosen for T8 [Prod_r]: the application [x (∀P. P)], whose function [x] has the inferred type
    [z] (every type inferred for [x] is [z]), which is not a product and unfolds (δ) in one step to
    the product [∀P:Prop. P] ([pr_z_delta_nondeg]).
    INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.pr_z_delta_nondeg
    TARGET PCUICPrincipalityEta.principal_typeE *)
Lemma principal_typeE_prod_r_inst :
  ∑ C, si_Σ ;;; bdf_Γz ⊢E C ≤ (tRel 0) {0 := iv_False} × si_Σ ;;; bdf_Γz |-E tApp (tRel 0) iv_False : C.
Proof.
  destruct (principal_typeE si_Σ pr_si_wfext (Γ := bdf_Γz) pr_app_z_typed) as [C HC].
  exists C. exact (HC _ pr_app_z_typed).
Qed.

(** Chosen for T8 [Prod_l]: [λP:Prop. x P] at the type [z], which is not a product and unfolds (δ)
    in one step to the product [∀P:Prop. P] ([pr_z_delta_nondeg]).
    INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.pr_z_delta_nondeg
    TARGET PCUICPrincipalityEta.principal_typeE *)
Lemma principal_typeE_prod_l_inst :
  ∑ C, si_Σ ;;; bdf_Γz ⊢E C ≤ tRel 1 × si_Σ ;;; bdf_Γz |-E pr_eta_x : C.
Proof.
  destruct (principal_typeE si_Σ pr_si_wfext (Γ := bdf_Γz) pr_eta_x_False_typed) as [C HC].
  exists C. exact (HC _ pr_eta_x_typed).
Qed.

(** The declared type of [r] in [pr_Γr] is [bdf_RFβ], whose head is an abstraction: a β-redex,
    not an applied inductive; it β-reduces to [R (∀P. P)] in one step. *)
Lemma principal_typeE_proj_inst_nondeg :
  pr_Γr = [vass si_na bdf_RFβ] /\ isLambda (PCUICAstUtils.head bdf_RFβ) /\
  ∥ red1 iv_Σ pr_Γr bdf_RFβ iv_RF ∥.
Proof.
  split; [reflexivity|]. split; [reflexivity|]. constructor.
  exact (PCUICReduction.red_beta _ _ si_na si_P (iv_R (tRel 0)) iv_False).
Qed.

(** Chosen for T8 [Ind_r], Proj case: the projection [f r], where [r] is declared at the β-redex
    [(λB:Prop. R B) (∀P. P)] ([bdf_RFβ]), whose head is an abstraction, not an inductive, and
    which β-reduces to [R (∀P. P)] in one step ([principal_typeE_proj_inst_nondeg]).
    INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.principal_typeE_proj_inst_nondeg
    TARGET PCUICPrincipalityEta.principal_typeE *)
Lemma principal_typeE_proj_inst :
  ∑ C, iv_Σ ;;; pr_Γr ⊢E C ≤ iv_False × iv_Σ ;;; pr_Γr |-E tProj iv_proj (tRel 0) : C.
Proof.
  destruct (principal_typeE iv_Σ pr_iv_wfext (Γ := pr_Γr) pr_proj_typed) as [C HC].
  exists C. exact (HC _ pr_proj_typed).
Qed.

(** The scrutinee of [pgi_match_let_open] is [let y := x in c y] ([pgi_disc_let]); it has the type
    [let y := x in I y] ([pgi_disc_let_ty]), which is not an applied inductive and ζ-reduces to
    [I x] in one step; every type inferred for the scrutinee is a let-in [let y := x in _]. *)
Lemma principal_typeE_case_inst_nondeg :
  PCUICProgressEtaInstances.pgi_match_let_open =
    tCase iv_ci iv_mp PCUICProgressEtaInstances.pgi_disc_let [iv_br] /\
  (forall ind u args, PCUICProgressEtaInstances.pgi_disc_let_ty <> mkApps (tInd ind u) args) /\
  ∥ si_Σ ;;; iv_Γ1 |-E PCUICProgressEtaInstances.pgi_disc_let : PCUICProgressEtaInstances.pgi_disc_let_ty ∥ /\
  ∥ red1 si_Σ iv_Γ1 PCUICProgressEtaInstances.pgi_disc_let_ty (iv_Ix 0) ∥ /\
  (forall T', si_Σ ;;; iv_Γ1 |-E PCUICProgressEtaInstances.pgi_disc_let ▹ T' ->
     exists A, T' = tLetIn si_na (tRel 0) si_P A).
Proof.
  split; [reflexivity|]. split.
  - intros ind u args. induction args as [|a args _] using rev_ind; [discriminate|].
    rewrite mkApps_app. cbn. discriminate.
  - split; [constructor; exact PCUICProgressEtaInstances.pgi_disc_let_letin_typed|].
    split; [constructor; exact (PCUICReduction.red_zeta _ _ si_na (tRel 0) si_P (iv_Ix 0))|].
    intros T' h. unfold PCUICProgressEtaInstances.pgi_disc_let in h. inversion h; subst.
    eexists; reflexivity.
Qed.

(** Chosen for T8 [Ind_r], Case case: [PCUICProgressEtaInstances.pgi_match_let_open] ([iv_match]
    with the scrutinee [let y := x in c y]); the scrutinee has the type [let y := x in I y], which
    is not an applied inductive and ζ-reduces to [I x] in one step, and every type inferred for the
    scrutinee is a let-in ([principal_typeE_case_inst_nondeg]).
    INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.principal_typeE_case_inst_nondeg
    TARGET PCUICPrincipalityEta.principal_typeE *)
Lemma principal_typeE_case_inst :
  ∑ C, si_Σ ;;; iv_Γ1 ⊢E C ≤ PCUICProgressEtaInstances.pgi_match_let_open_ty ×
       si_Σ ;;; iv_Γ1 |-E PCUICProgressEtaInstances.pgi_match_let_open : C.
Proof.
  destruct (principal_typeE si_Σ pr_si_wfext (u := PCUICProgressEtaInstances.pgi_match_let_open)
              PCUICProgressEtaInstances.pgi_match_let_open_typed) as [C HC].
  exists C. exact (HC _ PCUICProgressEtaInstances.pgi_match_let_open_typed).
Qed.

(** The other typing rules, on the derivations of [PCUICInversionEtaInstances]. [pr_head_rule]
    numbers the head former of a term, in the order of the term constructors ([tVar] and [tEvar]
    left out); apart from the conversion rule, each typing rule types terms of one head former. *)
Definition pr_head_rule (t : term) : nat :=
  match t with
  | tRel _ => 0 | tSort _ => 1 | tProd _ _ _ => 2 | tLambda _ _ _ => 3 | tLetIn _ _ _ _ => 4
  | tApp _ _ => 5 | tConst _ _ => 6 | tInd _ _ => 7 | tConstruct _ _ _ => 8
  | tCase _ _ _ _ => 9 | tProj _ _ => 10 | tFix _ _ => 11 | tCoFix _ _ => 12 | tPrim _ => 13
  | _ => 14
  end.

(** [x : Prop] in [iv_Γ1], [Prop → Prop] and [(λx:Prop. x) (∀P:Prop. P)], each retyped at a
    β-wrapped type ([iv_retype]), for the rule-coverage instances below. *)
Lemma pr_x_typed_conv : si_Σ ;;; iv_Γ1 |-E tRel 0 : tApp (iv_idS (Sort.super sProp)) si_P.
Proof.
  exact (iv_retype si_Σ si_wfE iv_Γ1 (tRel 0) si_P (Sort.super sProp) (iv_P_typed si_Σ iv_Γ1 iv_wf_Γ1)
           iv_x_typed).
Qed.

Lemma pr_PP_typed_conv : si_Σ ;;; [] |-E iv_PP : tApp (iv_idS (Sort.super iv_sPP)) (tSort iv_sPP).
Proof.
  apply (iv_retype si_Σ si_wfE); [|exact (iv_PP_typed si_Σ [] localenv_nil)].
  apply typeE_Sort; [constructor|].
  exact (PCUICWfUniversesEta.typing_wf_sortE (Σ := si_Σ) si_wfE (iv_PP_typed si_Σ [] localenv_nil)).
Qed.

Lemma pr_app_typed_conv : si_Σ ;;; [] |-E tApp iv_id iv_False : tApp (iv_idS (Sort.super sProp)) si_P.
Proof.
  exact (iv_retype si_Σ si_wfE [] (tApp iv_id iv_False) si_P (Sort.super sProp)
           (iv_P_typed si_Σ [] localenv_nil) (iv_app_typed si_Σ [] localenv_nil)).
Qed.

(** The twelve rule-coverage instances below apply [principal_typeE] to terms of twelve different
    head formers ([pr_head_rule]): the variable [x], declared in [iv_Γ1], a sort, a product, an
    abstraction, a let-in, an application, an inductive, a constructor, a fixpoint, a cofixpoint,
    a constant, a primitive. Each builds the principal type [C] from a derivation at a type [T]
    and compares [C] with a second type of the same term, the β-wrapped [(λX : s. X) T]; in each
    pair below (in the order of the instances) the compared type is not [T]. *)
Lemma principal_typeE_rules_nondeg :
  nth_error iv_Γ1 0 = Some (vass si_na si_P) /\
  map pr_head_rule
    [tRel 0; si_P; iv_PP; iv_id; tLetIn si_na iv_False si_P (tRel 0); tApp iv_id iv_False;
     tInd si_ind []; tConstruct si_ind 0 []; tFix iv_mfix 0; tCoFix iv_cmfix 0;
     tConst po_land_kn []; tPrim iv_one] =
  [0; 1; 2; 3; 4; 5; 7; 8; 11; 12; 6; 13] /\
  Forall (fun p : term × term => fst p <> snd p)
    [(tApp (iv_idS (Sort.super sProp)) si_P, si_P);
     (tApp (iv_idS (Sort.super (Sort.super sProp))) (tSort (Sort.super sProp)), tSort (Sort.super sProp));
     (tApp (iv_idS (Sort.super iv_sPP)) (tSort iv_sPP), tSort iv_sPP);
     (tApp (iv_idS iv_sPP) iv_PP, iv_PP);
     (tApp (iv_idS (Sort.super sProp)) (tLetIn si_na iv_False si_P si_P), tLetIn si_na iv_False si_P si_P);
     (tApp (iv_idS (Sort.super sProp)) si_P, si_P);
     (tApp (iv_idS iv_sPP) si_arity, si_arity);
     (tApp (iv_idS (Sort.sort_of_product (Sort.super sProp) sProp))
        (tProd si_na si_P (tApp (tInd si_ind []) (tRel 0))),
      tProd si_na si_P (tApp (tInd si_ind []) (tRel 0)));
     (tApp (iv_idS (Sort.sort_of_product sProp sProp)) iv_fix_ty, iv_fix_ty);
     (tApp (iv_idS sProp) iv_RF, iv_RF);
     (tApp (iv_idS (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0))) po_land_ty,
      po_land_ty);
     (tApp (iv_idS Sort.type0) (prim_type iv_one po_int_kn), prim_type iv_one po_int_kn)].
Proof.
  split; [reflexivity|]. split; [reflexivity|].
  repeat constructor; intros h; cbn [fst snd] in h; discriminate h.
Qed.

(** INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.principal_typeE_rules_nondeg
    TARGET PCUICPrincipalityEta.principal_typeE *)
Lemma principal_typeE_Rel_inst :
  ∑ C, si_Σ ;;; iv_Γ1 ⊢E C ≤ tApp (iv_idS (Sort.super sProp)) si_P × si_Σ ;;; iv_Γ1 |-E tRel 0 : C.
Proof.
  destruct (principal_typeE si_Σ pr_si_wfext (Γ := iv_Γ1) iv_x_typed) as [C HC].
  exists C. exact (HC _ pr_x_typed_conv).
Qed.
(** INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.principal_typeE_rules_nondeg
    TARGET PCUICPrincipalityEta.principal_typeE *)
Lemma principal_typeE_Sort_inst :
  ∑ C, si_Σ ;;; [] ⊢E C ≤ tApp (iv_idS (Sort.super (Sort.super sProp))) (tSort (Sort.super sProp)) ×
       si_Σ ;;; [] |-E si_P : C.
Proof.
  destruct (principal_typeE si_Σ pr_si_wfext (u := si_P) (iv_P_typed si_Σ [] localenv_nil)) as [C HC].
  exists C. exact (HC _ iv_P_typed_conv).
Qed.
(** INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.principal_typeE_rules_nondeg
    TARGET PCUICPrincipalityEta.principal_typeE *)
Lemma principal_typeE_Prod_inst :
  ∑ C, si_Σ ;;; [] ⊢E C ≤ tApp (iv_idS (Sort.super iv_sPP)) (tSort iv_sPP) × si_Σ ;;; [] |-E iv_PP : C.
Proof.
  destruct (principal_typeE si_Σ pr_si_wfext (u := iv_PP) (iv_PP_typed si_Σ [] localenv_nil)) as [C HC].
  exists C. exact (HC _ pr_PP_typed_conv).
Qed.
(** INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.principal_typeE_rules_nondeg
    TARGET PCUICPrincipalityEta.principal_typeE *)
Lemma principal_typeE_Lambda_inst :
  ∑ C, si_Σ ;;; [] ⊢E C ≤ tApp (iv_idS iv_sPP) iv_PP × si_Σ ;;; [] |-E iv_id : C.
Proof.
  destruct (principal_typeE si_Σ pr_si_wfext (u := iv_id) (iv_id_typed si_Σ [] localenv_nil)) as [C HC].
  exists C. exact (HC _ iv_id_typed_conv).
Qed.
(** INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.principal_typeE_rules_nondeg
    TARGET PCUICPrincipalityEta.principal_typeE *)
Lemma principal_typeE_LetIn_inst :
  ∑ C, si_Σ ;;; [] ⊢E C ≤ tApp (iv_idS (Sort.super sProp)) (tLetIn si_na iv_False si_P si_P) ×
       si_Σ ;;; [] |-E tLetIn si_na iv_False si_P (tRel 0) : C.
Proof.
  destruct (principal_typeE si_Σ pr_si_wfext (u := tLetIn si_na iv_False si_P (tRel 0))
              (iv_let_typed si_Σ [] localenv_nil)) as [C HC].
  exists C. exact (HC _ iv_let_typed_conv).
Qed.
(** INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.principal_typeE_rules_nondeg
    TARGET PCUICPrincipalityEta.principal_typeE *)
Lemma principal_typeE_App_inst :
  ∑ C, si_Σ ;;; [] ⊢E C ≤ tApp (iv_idS (Sort.super sProp)) si_P × si_Σ ;;; [] |-E tApp iv_id iv_False : C.
Proof.
  destruct (principal_typeE si_Σ pr_si_wfext (u := tApp iv_id iv_False) (iv_app_typed si_Σ [] localenv_nil))
    as [C HC].
  exists C. exact (HC _ pr_app_typed_conv).
Qed.
(** INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.principal_typeE_rules_nondeg
    TARGET PCUICPrincipalityEta.principal_typeE *)
Lemma principal_typeE_Ind_inst :
  ∑ C, si_Σ ;;; [] ⊢E C ≤ tApp (iv_idS iv_sPP) si_arity × si_Σ ;;; [] |-E tInd si_ind [] : C.
Proof.
  destruct (principal_typeE si_Σ pr_si_wfext (u := tInd si_ind []) (iv_ind_typed [] localenv_nil)) as [C HC].
  exists C. exact (HC _ iv_ind_typed_conv).
Qed.
(** INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.principal_typeE_rules_nondeg
    TARGET PCUICPrincipalityEta.principal_typeE *)
Lemma principal_typeE_Construct_inst :
  ∑ C, si_Σ ;;; [] ⊢E C ≤ tApp (iv_idS (Sort.sort_of_product (Sort.super sProp) sProp))
                             (tProd si_na si_P (tApp (tInd si_ind []) (tRel 0))) ×
       si_Σ ;;; [] |-E tConstruct si_ind 0 [] : C.
Proof.
  destruct (principal_typeE si_Σ pr_si_wfext (u := tConstruct si_ind 0 []) (iv_cstr_typed [] localenv_nil))
    as [C HC].
  exists C. exact (HC _ iv_cstr_typed_conv).
Qed.
(** INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.principal_typeE_rules_nondeg
    TARGET PCUICPrincipalityEta.principal_typeE *)
Lemma principal_typeE_Fix_inst :
  ∑ C, si_Σ ;;; [] ⊢E C ≤ tApp (iv_idS (Sort.sort_of_product sProp sProp)) iv_fix_ty ×
       si_Σ ;;; [] |-E tFix iv_mfix 0 : C.
Proof.
  destruct (principal_typeE si_Σ pr_si_wfext (u := tFix iv_mfix 0) iv_fix_typed) as [C HC].
  exists C. exact (HC _ iv_fix_typed_conv).
Qed.
(** INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.principal_typeE_rules_nondeg
    TARGET PCUICPrincipalityEta.principal_typeE *)
Lemma principal_typeE_CoFix_inst :
  ∑ C, iv_Σ ;;; iv_Γc ⊢E C ≤ tApp (iv_idS sProp) iv_RF × iv_Σ ;;; iv_Γc |-E tCoFix iv_cmfix 0 : C.
Proof.
  destruct (principal_typeE iv_Σ pr_iv_wfext (u := tCoFix iv_cmfix 0) iv_cofix_typed) as [C HC].
  exists C. exact (HC _ iv_cofix_typed_conv).
Qed.
(** INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.principal_typeE_rules_nondeg
    TARGET PCUICPrincipalityEta.principal_typeE *)
Lemma principal_typeE_Const_inst :
  ∑ C, Σ_po ;;; [] ⊢E C ≤ tApp (iv_idS (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0)))
                            po_land_ty ×
       Σ_po ;;; [] |-E tConst po_land_kn [] : C.
Proof.
  destruct (principal_typeE Σ_po pr_po_wfext (u := tConst po_land_kn []) iv_land_typed) as [C HC].
  exists C. exact (HC _ iv_land_typed_conv).
Qed.
(** INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.principal_typeE_rules_nondeg
    TARGET PCUICPrincipalityEta.principal_typeE *)
Lemma principal_typeE_Prim_inst :
  ∑ C, Σ_po ;;; [] ⊢E C ≤ tApp (iv_idS Sort.type0) (prim_type iv_one po_int_kn) ×
       Σ_po ;;; [] |-E tPrim iv_one : C.
Proof.
  destruct (principal_typeE Σ_po pr_po_wfext (u := tPrim iv_one) iv_prim_typed) as [C HC].
  exists C. exact (HC _ iv_prim_typed_conv).
Qed.

(** The two argument lists of [r]'s inductive types differ; [r] is declared at [bdf_RFβ], whose
    head is an abstraction (a β-redex) and which β-reduces to [R (∀P. P)] in one step. *)
Lemma principal_type_indE_inst_nondeg :
  [iv_False] <> [pr_idF] /\ pr_Γr = [vass si_na bdf_RFβ] /\
  isLambda (PCUICAstUtils.head bdf_RFβ) /\ ∥ red1 iv_Σ pr_Γr bdf_RFβ iv_RF ∥.
Proof.
  split; [discriminate|]. split; [reflexivity|]. split; [reflexivity|]. constructor.
  exact (PCUICReduction.red_beta _ _ si_na si_P (iv_R (tRel 0)) iv_False).
Qed.

(** [r : R (∀P. P)] and [r : R ((λx:Prop. x) (∀P. P))]: the argument lists differ; [r] is
    declared at the β-redex [(λB:Prop. R B) (∀P. P)], which β-reduces to [R (∀P. P)] in one step
    (chosen for T8 [Ind_r], twice).
    INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.principal_type_indE_inst_nondeg *)
Lemma principal_type_indE_inst :
  (∑ ui',
    cmp_ind_universes iv_Σ iv_ind #|[iv_False]| ui' [] *
    cmp_ind_universes iv_Σ iv_ind #|[pr_idF]| ui' []) *
  ws_cumul_pbE_terms iv_Σ pr_Γr [iv_False] [pr_idF] *
  (iv_ind = iv_ind).
Proof.
  exact (principal_type_indE (wfΣ := pr_iv_wfext) (args := [iv_False]) (args' := [pr_idF])
           pr_r_RF_typed pr_r_RidF_typed).
Qed.

(** [∀_:Prop. Prop] and [∀_:Prop. Set] differ (their codomains, [Prop] and [Set]). *)
Lemma typing_leq_termE_inst_nondeg : iv_PP <> pr_PS.
Proof. discriminate. Qed.

(** [typing_leq_termE]: [∀_:Prop. Prop ≤ ∀_:Prop. Set] up to universes ([pr_PP_leq_PS]; the
    codomain at [Cumul], [Prop ≤ Set]): the term [∀_:Prop. Prop] gets the type of [∀_:Prop. Set];
    the two terms differ ([typing_leq_termE_inst_nondeg]).
    INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.typing_leq_termE_inst_nondeg *)
Lemma typing_leq_termE_inst : si_Σ ;;; [] |-E iv_PP : tSort pr_sPS.
Proof.
  exact (typing_leq_termE si_Σ [] pr_PS iv_PP (tSort pr_sPS) (tSort iv_sPP) si_wfE si_on_udecl
           pr_PS_typed (iv_PP_typed si_Σ [] localenv_nil) pr_PP_leq_PS).
Qed.

(** [λx:Prop. x] with the anonymous binder and with the binder [x] differ. *)
Lemma typing_eq_termE_inst_nondeg : iv_id <> pr_lam'.
Proof. discriminate. Qed.

(** [typing_eq_termE]: [λx:Prop. x] with two binder names; the second term gets the type of
    the first.
    INSTANCE NONDEGEN PCUICPrincipalityEtaInstances.typing_eq_termE_inst_nondeg *)
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
