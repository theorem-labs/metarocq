(* Distributed under the terms of the MIT license. *)

(* NONDEGEN tags: an INSTANCE NONDEGEN tag is a reader judgment backed by a compiled nontriviality
   lemma, not a mechanical guarantee. *)

(** * Satisfying instances of the lemmas of [Bidirectional/BDFromPCUICEta] (row T6)

  **No forecast class.** The lemmas of [BDFromPCUICEta] took T1's [SRForecastCopy18] (copy 18b)
  as a premise until copy 18b landed (frac/eta 3e6b422d); the class is deleted, and copies 10,
  12, 14, 15, 16 and 18a landed earlier. T8 enters through the proved two-hypothesis forms
  [PCUICEtaT8Probe.T8_*_r_two], whose one hypothesis is [PCUICSREta.subject_reductionE] (row B1's
  [fix_rarg_inductive] is proved there). The instances below, in section
  [BDFromPCUICEtaInstances] (which held the class), apply the lemmas. Everything each instance
  needs (the environment, its [wfE], every typing derivation) is built here or in the landed
  instance files ([PCUICInversionEtaInstances], [BDTypingEtaInstances],
  [BDToPCUICEtaInstances]).

  **The environment** is [si_Σ] ([PCUICCumulativitySpecEtaClosureInstances]):
  [Inductive I (A : Prop) : Prop := c : I A], with [si_wfE]; [Σ_po]
  ([PCUICEtaPrimOpInstance]) for the constant and primitive rows.

  **Non-degeneracy.** Each instance applies a lemma of [BDFromPCUICEta] to concrete premises:
  typing derivations, inference pairs, judgments or a conversion. Each carries a tag of the
  instance degeneracy gate. [INSTANCE NONDEGEN <lemma>] names the compiled lemma whose
  statement gives its non-degeneracy; the tag's prose claims what that statement gives, and
  names the derivation that states any other fact it uses. [INSTANCE IMPOSSIBLE: <reason>]
  marks a row whose target's proof only packs or unpacks its own premises, so that every
  instance of that target is degenerate. The rows:
  - the η pair: [typing_inferingE_eta_inst], [typing_checkingE_eta_inst],
    [bidirectional_from_pcuicE_inst] and the fits [T6BDc_typing_infering_fit_inst],
    [T6BDc_typing_checking_fit_inst] run on [bdf_eta_typed] ([x : G F] in [bd_Γη]); every
    type inferred for [x] in [bd_Γη] is not [G F], and one η step relates it to [G F]
    ([bdf_eta_nondeg]);
  - the T8 sites, at subjects none of whose inferred types is the head form:
    [typing_infering_sortE_let_inst], [conv_infer_sortE_let_inst] and
    [T6BDc_typing_infering_sort_fit_inst] on [bdf_let_sort_typed] ([bdf_let : Prop]), where
    every type inferred for [bdf_let] is not a sort ([bdf_let_nondeg]);
    [typing_infer_prodE_let_inst] and [conv_infer_prodE_inst] on [bdf_x_prod_typed]
    ([x : ∀P:Prop. P] in [bdf_Γz]), where every type inferred for [x] is not a product
    ([bdf_z_nondeg]); [typing_infer_indE_beta_inst] and [conv_infer_indE_inst] on
    [bdf_x_ind_typed] ([x : I A] in [bdf_Γβ]), where every type inferred for [x] is not an
    application of an inductive type ([bdf_beta_nondeg]); [isTypeE_mkApps_Ind_head_arity_inst]
    on the same [x], where the head arity of [I] is the length of the argument list [[A]]
    ([bdf_head_arity_nondeg]);
  - the (co)fixpoint witness, at a declared type on which the check fails and which reduces to
    a type on which it passes: [wf_fixpointE_wf_fixpoint_red_inst],
    [mfix_on_ind_conv_redE_fix_inst], [mfix_body_on_conv_redE_fix_inst],
    [red_fix_witnessE_inst] ([bdf_fix_d_nondeg]); [mfix_body_on_conv_redE_cofix_inst],
    [mfix_on_ind_conv_redE_cofix_inst], [red_cofix_witnessE_inst] ([bdf_cofix_d_nondeg]);
    [typing_inferingE_Fix_beta_inst] and [wf_fixpointE_wf_fixpoint_red_typed_inst] on the
    typed fixpoint [bdf_fix_typed] ([bdf_fix_dβ_nondeg]); [typing_inferingE_CoFix_inst] and
    [wf_cofixpointE_wf_cofixpoint_red_inst] on the typed cofixpoint [bdf_cofix_typed] of
    [iv_Σ], a [CoFinite] record [R] ([bdf_cofix_dβ_nondeg]);
  - completeness per typing rule, [typing_inferingE_<rule>_inst]: Rel, Lambda, LetIn and App
    on [bdf_x_prod_typed], [bdf_lam_z_typed], [bdf_letlam_z_typed] and [bdf_app_z_typed], each
    with the variable [x] of [bdf_Γz] in its subject ([bdf_z_nondeg]); Prod on
    [bdf_prod_let_typed], whose domain is [bdf_let] ([bdf_let_nondeg]); Case on
    [iv_match_typed], whose scrutinee and branch body are [c x]: every type inferred for
    [c x] is [I x], which is not the β-redex [(λ z : I x. I x) (c x)], and one reduction step
    takes that β-redex to [I x] ([bdf_case_br_nondeg]); Proj on [bdf_proj_typed]
    ([bdf_rβ_nondeg]); Fix_beta and CoFix above. The Sort, Ind, Construct, Fix, Const and
    Prim rows run on a derivation retyped at the β-wrap [bdf_wrap s T = (λ X : s. X) T] of a
    type [T] ([bdf_sort_wrapped], [bdf_ind_wrapped], [bdf_cstr_wrapped], [bdf_fix_wrapped],
    [bdf_const_wrapped], [bdf_prim_wrapped]); for each, every type inferred for the subject
    is [T], which is not [bdf_wrap s T], and one reduction step takes [bdf_wrap s T] to [T]
    ([bdf_sort_wrap_nondeg], [bdf_ind_wrap_nondeg], [bdf_cstr_wrap_nondeg],
    [bdf_fix_wrap_nondeg], [bdf_const_wrap_nondeg], [bdf_prim_wrap_nondeg]);
  - the judgment and context lemmas: the let-judgment [z := bdf_let : Prop], [bdf_let] as a
    type and the context [[x : bdf_let]] ([bdf_let_nondeg]); [[x : bdf_let]] over [bd_ΓFG]
    ([bdf_let_FG_nondeg], the same fact in [bd_ΓFG]); the parameter instance [[x]] of
    [bdf_ctx_inst_z] in [bdf_Γz] ([bdf_z_nondeg]);
  - tagged IMPOSSIBLE, because the target's proof only packs or unpacks its premises:
    [conv_checkE_eta_inst] (one destruct, the [checkE_Cumul] constructor and the projection
    [ws_cumul_pbE_forget]), [conv_lift_judgmentE_inst] and [conv_lift_judgment_univE_inst]
    (record repacking and [geq_relevance]), [ws_cumul_ctx_pbE_vass_inst] (the context
    constructor, prefix reflexivity and the declaration constructor). They run on the
    inference pair of [typing_inferingE_eta_inst], the let-judgment [z := bdf_let : Prop],
    the assumption [x : bdf_let] at [Prop], and the contexts [bd_ΓFG ,, x : G (λ y. F y)] and
    [bd_ΓFG ,, x : G F].

  **Rows not inhabited.** None: every lemma of [BDFromPCUICEta] has an instance here, or is a
  helper of one of them ([T8_Sort_r_plug], [T8_Prod_r_plug], [T8_Ind_r_plug],
  [is_closed_projection_contextE], [untyped_subslet_projection_contextE], the syntactic
  helpers). [conv_checkE], [conv_infer_prodE], [conv_infer_indE], [conv_lift_judgmentE],
  [conv_lift_judgment_univE] and [ws_cumul_ctx_pbE_vass] have direct instances (above).

  **Assumptions.** The end of this file prints the assumptions of base's main theorems and of
  their E copies: the same set, and no forecast class is an argument ([About]). *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICReduction PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICClosedBodies PCUICTypingEta
     PCUICTypingEtaInd PCUICTypingEtaNotions PCUICCumulativitySpecEtaClosureInstances PCUICEtaDefs
     PCUICEtaI5 PCUICWellScopedCumulativity PCUICWellScopedCumulativityEta PCUICEtaA6 PCUICEquality
     PCUICConversionEtaCongr PCUICEtaFInst PCUICGuardClosure PCUICClosedTypEta
     PCUICEtaPrimOpInstance PCUICInversionEtaInstances
     PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICSpineEta PCUICValidityEta PCUICSREta
     BDTyping BDTypingEta BDTypingEtaInstances BDToPCUICEta BDToPCUICEtaInstances BDFromPCUICEta.
From MetaRocq.PCUIC Require BDFromPCUIC PCUICFixWitness PCUICWfUniversesEta PCUICGlobalEnv PCUICConversion
     PCUICConfluence.
From Equations.Type Require Import Relation.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

(* WITNESSES: bdf_* *)

(** ** Typing derivations, without any class *)

(** The η-typed variable: [G : (Prop → Prop) → Prop, F : Prop → Prop,
    x : G (λ y : Prop. F y) ⊢ x : G F]. *)
Lemma bdf_eta_typed : si_Σ ;;; bd_Γη |-E tRel 0 : tApp (tRel 2) (tRel 1).
Proof.
  eapply (typeE_Cumul _ _ (tRel 0) (lift0 1 bd_X) _ sProp).
  - exact (typeE_Rel _ _ 0 (vass si_na bd_X) bdi_wfη eq_refl).
  - exact bdi_GF_eta_typed.
  - exact (ws_cumul_pbE_forget_spec JoinE_ws_cumul_pbE_inst).
Qed.

(** [let z : Prop := ∀P:Prop. P in z : Prop]: its inferred type is a let-in. *)
Definition bdf_let : term := tLetIn si_na iv_False si_P (tRel 0).

Lemma bdf_let_sort_typed : si_Σ ;;; [] |-E bdf_let : tSort sProp.
Proof.
  eapply (typeE_Cumul _ _ bdf_let (tLetIn si_na iv_False si_P si_P) si_P (Sort.super sProp)).
  - exact (iv_let_typed si_Σ [] localenv_nil).
  - exact (iv_P_typed si_Σ [] localenv_nil).
  - apply (ws_cumul_pbE_forget_spec (pb := Cumul)).
    apply (red_ws_cumul_pbE (Σ := si_Σ)).
    exact (closed_red_of (Σ := si_Σ) (Γ := []) (t := tLetIn si_na iv_False si_P si_P) eq_refl eq_refl
             (red1_red _ _ _ _ (red_zeta _ _ si_na iv_False si_P si_P))).
Qed.

(** [x : z, z := ∀P:Prop. P ⊢ x : ∀P:Prop. P]: the inferred type of [x] is the variable [z]. *)
Definition bdf_Γz : context := [vass si_na (tRel 0); vdef si_na iv_False si_P].

Lemma bdf_x_prod_typed : si_Σ ;;; bdf_Γz |-E tRel 0 : iv_False.
Proof.
  eapply (typeE_Cumul _ _ (tRel 0) (tRel 1) iv_False sProp).
  - exact (typeE_Rel _ _ 0 (vass si_na (tRel 0)) bdi_wf_subst1_prem eq_refl).
  - exact (iv_False_typed si_Σ bdf_Γz bdi_wf_subst1_prem).
  - apply (ws_cumul_pbE_forget_spec (pb := Cumul)).
    apply (red_ws_cumul_pbE (Σ := si_Σ)).
    exact (closed_red_of (Σ := si_Σ) (Γ := bdf_Γz) (t := tRel 1) eq_refl eq_refl
             (red1_red _ _ _ _ (red_rel _ bdf_Γz 1 iv_False eq_refl))).
Qed.

(** [x : (λ B : Prop. I B) A, A : Prop ⊢ x : I A]: the inferred type of [x] is a β-redex. *)
Definition bdf_Γβ : context := [vass si_na bd_fix_dom; vass si_na si_P].

Lemma bdf_wfβ : wf_localE si_Σ bdf_Γβ.
Proof. exact (iv_wf_vass si_Σ bd_Γ1 si_na bd_fix_dom sProp bd_wfE_Γ1 bd_fix_dom_typedE eq_refl). Qed.

Lemma bdf_x_ind_typed : si_Σ ;;; bdf_Γβ |-E tRel 0 : mkApps (tInd si_ind []) [tRel 1].
Proof.
  eapply (typeE_Cumul _ _ (tRel 0) (lift0 1 bd_fix_dom) _ sProp).
  - exact (typeE_Rel _ _ 0 (vass si_na bd_fix_dom) bdf_wfβ eq_refl).
  - exact (iv_IX_typed bdf_Γβ (tRel 1) bdf_wfβ (typeE_Rel _ _ 1 (vass si_na si_P) bdf_wfβ eq_refl)).
  - apply (ws_cumul_pbE_forget_spec (pb := Cumul)).
    apply (red_ws_cumul_pbE (Σ := si_Σ)).
    exact (closed_red_of (Σ := si_Σ) (Γ := bdf_Γβ) (t := lift0 1 bd_fix_dom) eq_refl eq_refl
             (red1_red _ _ _ _ (red_beta _ bdf_Γβ si_na si_P (tApp (tInd si_ind []) (tRel 0)) (tRel 1)))).
Qed.

(** The witness of the domain [(λ B. I B) A] of [bd_fix_dtype] is its β-reduct [I A]. *)
Lemma bdf_fix_dtype_ws : ws_cumul_pbE Conv si_Σ bd_Γ1 bd_fix_dtype
  (it_mkProd_or_LetIn [vass si_na (mkApps (tInd si_ind []) [tRel 0])] si_P).
Proof.
  apply (red_ws_cumul_pbE (Σ := si_Σ)).
  exact (closed_red_of (Σ := si_Σ) (Γ := bd_Γ1) (t := bd_fix_dtype) eq_refl eq_refl bd_fix_dtype_red).
Qed.

(** A cofixpoint-shaped declaration in [si_Σ]: its type is the β-redex [(λ B. I B) A], on which
    [check_one_cofix] fails; its witness is [I A]. *)
Definition bdf_cofix_d : def term :=
  {| dname := si_na; dtype := bd_fix_dom; dbody := tRel 0; rarg := 0 |}.

Lemma bdf_check_cofix_dtype : check_one_cofix bdf_cofix_d = None.
Proof. reflexivity. Qed.

Lemma bdf_cofix_dom_red : red si_Σ bd_Γ1 bd_fix_dom (mkApps (tInd si_ind []) [tRel 0]).
Proof. apply rt_step. exact (red_beta _ _ si_na si_P (tApp (tInd si_ind []) (tRel 0)) (tRel 0)). Qed.

Lemma bdf_cofix_dom_ws : ws_cumul_pbE Conv si_Σ bd_Γ1 bd_fix_dom
  (it_mkProd_or_LetIn [] (mkApps (tInd si_ind []) [tRel 0])).
Proof.
  apply (red_ws_cumul_pbE (Σ := si_Σ)).
  exact (closed_red_of (Σ := si_Σ) (Γ := bd_Γ1) (t := bd_fix_dom) eq_refl eq_refl bdf_cofix_dom_red).
Qed.

Lemma bdf_cofix_witness :
  mfix_body_on check_one_cofix (conv_witnessE si_Σ bd_Γ1) si_kn bdf_cofix_d.
Proof.
  exists (mkApps (tInd si_ind []) [tRel 0]). split; [reflexivity|]. split; [reflexivity|].
  exact (ws_cumul_pbE_forget_spec bdf_cofix_dom_ws).
Qed.

Lemma bdf_fix_witness : mfix_body_on check_one_fix (conv_witnessE si_Σ bd_Γ1) si_kn bd_fix_d.
Proof.
  exists bd_fix_ty. split; [reflexivity|]. split; [reflexivity|].
  exact (ws_cumul_pbE_forget_spec bdf_fix_dtype_ws).
Qed.

#[local] Instance bdf_iv_cb : ClosedBodies iv_env := @wfE_ClosedBodies _ iv_env iv_wfE.

(** A typed cofixpoint in [iv_Σ] ([PCUICInversionEtaInstances]: the [CoFinite] record
    [R (A : Prop) := mkR { f : A }]), in the context [p : ∀P:Prop. P]:
    [cofix g : (λ B : Prop. R B) (∀P. P) := mkR (∀P. P) p]. The declared type is a β-redex,
    on which [check_one_cofix] fails ([bdf_check_cofix_dtypeβ]); the witness is its reduct
    [R (∀P. P)] ([bdf_wf_cofix]). *)
Definition bdf_RFβ : term := tApp (tLambda si_na si_P (iv_R (tRel 0))) iv_False.

Lemma bdf_RFβ_typed (Γ : context) : wf_localE iv_Σ Γ -> iv_Σ ;;; Γ |-E bdf_RFβ : si_P.
Proof.
  intros h.
  refine (typeE_App _ _ (tLambda si_na si_P (iv_R (tRel 0))) si_na si_P si_P _ iv_False
            (iv_PP_typed iv_Σ Γ h) _ (iv_False_typed iv_Σ Γ h)).
  apply typeE_Lambda.
  - exact (iv_vass iv_Σ Γ si_na si_P _ (iv_P_typed iv_Σ Γ h) eq_refl).
  - exact (iv_RX_typed _ (tRel 0) (iv_wf_P iv_Σ Γ h)
             (typeE_Rel _ _ 0 (vass si_na si_P) (iv_wf_P iv_Σ Γ h) eq_refl)).
Qed.

Definition bdf_cofix_dβ : def term :=
  {| dname := si_na; dtype := bdf_RFβ; dbody := iv_cofix_body; rarg := 0 |}.
Definition bdf_cmfix : mfixpoint term := [bdf_cofix_dβ].
Definition bdf_Γcf : context := [vass si_na bdf_RFβ; vass si_na iv_False].

Lemma bdf_check_cofix_dtypeβ : check_one_cofix bdf_cofix_dβ = None.
Proof. reflexivity. Qed.

Lemma bdf_wf_Γcf : wf_localE iv_Σ bdf_Γcf.
Proof. exact (iv_wf_vass iv_Σ iv_Γc si_na bdf_RFβ sProp iv_wf_Γc (bdf_RFβ_typed iv_Γc iv_wf_Γc) eq_refl). Qed.

Lemma bdf_RFβ_red (Γ : context) : red iv_Σ Γ bdf_RFβ iv_RF.
Proof. apply rt_step. exact (red_beta _ _ si_na si_P (iv_R (tRel 0)) iv_False). Qed.

Lemma bdf_cofix_body_typed : iv_Σ ;;; bdf_Γcf |-E iv_cofix_body : lift0 1 bdf_RFβ.
Proof.
  pose proof (iv_False_typed iv_Σ bdf_Γcf bdf_wf_Γcf) as hF.
  pose proof (iv_wf_vass iv_Σ bdf_Γcf iv_fna iv_False sProp bdf_wf_Γcf hF eq_refl) as wF.
  eapply (typeE_Cumul _ _ _ iv_RF _ sProp).
  - refine (typeE_App _ _ (tApp (tConstruct iv_ind 0 []) iv_False) iv_fna iv_False iv_RF
              (Sort.sort_of_product sProp sProp) (tRel 1) _ (iv_mkRF_typed bdf_Γcf bdf_wf_Γcf) _).
    + apply typeE_Prod; [exact (iv_vass_s iv_Σ bdf_Γcf iv_fna iv_False sProp hF eq_refl)|].
      exact (iv_RF_typed _ wF).
    + exact (typeE_Rel _ _ 1 (vass si_na iv_False) bdf_wf_Γcf eq_refl).
  - exact (bdf_RFβ_typed bdf_Γcf bdf_wf_Γcf).
  - apply (ws_cumul_pbE_forget_spec (pb := Cumul)).
    apply (red_ws_cumul_pbE_inv (Σ := iv_Σ)).
    exact (closed_red_of (Σ := iv_Σ) (Γ := bdf_Γcf) (t := bdf_RFβ) eq_refl eq_refl (bdf_RFβ_red bdf_Γcf)).
Qed.

Lemma bdf_cofix_guard : cofix_guard iv_Σ iv_Γc bdf_cmfix.
Proof.
  change (guard_cl CoFix iv_Σ iv_Γc bdf_cmfix). apply gc_check.
  split; [vm_compute; reflexivity|]. exists 30. vm_compute. reflexivity.
Qed.

Lemma bdf_wf_cofix : wf_cofixpointE iv_Σ iv_Γc bdf_cmfix.
Proof.
  exists iv_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [|constructor].
  exists iv_RF. split; [reflexivity|]. split; [reflexivity|].
  apply (ws_cumul_pbE_forget_spec (pb := Conv)).
  apply (red_ws_cumul_pbE (Σ := iv_Σ)).
  exact (closed_red_of (Σ := iv_Σ) (Γ := iv_Γc) (t := bdf_RFβ) eq_refl eq_refl (bdf_RFβ_red iv_Γc)).
Qed.

Lemma bdf_cofix_typed : iv_Σ ;;; iv_Γc |-E tCoFix bdf_cmfix 0 : bdf_RFβ.
Proof.
  refine (typeE_CoFix _ _ bdf_cmfix 0 bdf_cofix_dβ iv_wf_Γc bdf_cofix_guard eq_refl _ _ bdf_wf_cofix).
  - constructor; [|constructor].
    exact (iv_vass iv_Σ iv_Γc si_na bdf_RFβ sProp (bdf_RFβ_typed iv_Γc iv_wf_Γc) eq_refl).
  - constructor; [|constructor].
    exact (iv_vdef iv_Σ bdf_Γcf si_na iv_cofix_body (lift0 1 bdf_RFβ) sProp bdf_cofix_body_typed
             (bdf_RFβ_typed bdf_Γcf bdf_wf_Γcf) eq_refl).
Qed.

(** A typed fixpoint in [si_Σ] whose recursive argument's domain is a β-redex, in
    [bd_Γ1 = [A : Prop]]: [fix f (x : (λ B : Prop. I B) A) : I A := x]. [check_one_fix]
    fails on the declared type ([bdf_check_fix_dtypeβ]); the witness is the reduct
    [Π (x : I A). I A] ([bdf_wf_fix]). [bdf_Dk k] is [(λ B. I B) (tRel k)]. *)
Definition bdf_Dk (k : nat) : term := tApp (tLambda si_na si_P (tApp (tInd si_ind []) (tRel 0))) (tRel k).
Definition bdf_fxty (k : nat) : term := tProd si_na (bdf_Dk k) (tApp (tInd si_ind []) (tRel (S k))).
Definition bdf_fix_dβ : def term :=
  {| dname := si_na; dtype := bdf_fxty 0; dbody := tLambda si_na (bdf_Dk 1) (tRel 0); rarg := 0 |}.
Definition bdf_fmfix : mfixpoint term := [bdf_fix_dβ].
Definition bdf_Γff : context := [vass si_na (bdf_fxty 0); vass si_na si_P].

Lemma bdf_check_fix_dtypeβ : check_one_fix bdf_fix_dβ = None.
Proof. reflexivity. Qed.

Lemma bdf_dom_typed (Γ : context) k : wf_localE si_Σ Γ -> nth_error Γ k = Some (vass si_na si_P) ->
  si_Σ ;;; Γ |-E bdf_Dk k : tSort sProp.
Proof.
  intros h hk.
  refine (typeE_App _ _ (tLambda si_na si_P (tApp (tInd si_ind []) (tRel 0))) si_na si_P (tSort sProp) _
            (tRel k) (bd_arity_typedE _ h) _ (typeE_Rel _ _ k (vass si_na si_P) h hk)).
  apply typeE_Lambda.
  - exact (iv_vass si_Σ Γ si_na si_P _ (iv_P_typed si_Σ Γ h) eq_refl).
  - exact (bd_Ix0_typedE _ h).
Qed.

Lemma bdf_fxty_typed (Γ : context) k : wf_localE si_Σ Γ -> nth_error Γ k = Some (vass si_na si_P) ->
  si_Σ ;;; Γ |-E bdf_fxty k : tSort (Sort.sort_of_product sProp sProp).
Proof.
  intros h hk.
  pose proof (bdf_dom_typed Γ k h hk) as hD.
  pose proof (iv_wf_vass si_Σ Γ si_na (bdf_Dk k) sProp h hD eq_refl) as hx.
  unfold bdf_fxty. apply typeE_Prod.
  - exact (iv_vass_s si_Σ Γ si_na (bdf_Dk k) sProp hD eq_refl).
  - exact (iv_IX_typed _ (tRel (S k)) hx (typeE_Rel _ _ (S k) (vass si_na si_P) hx hk)).
Qed.

Lemma bdf_wf_Γff : wf_localE si_Σ bdf_Γff.
Proof.
  exact (iv_wf_vass si_Σ bd_Γ1 si_na (bdf_fxty 0) _ bd_wfE_Γ1
           (bdf_fxty_typed bd_Γ1 0 bd_wfE_Γ1 eq_refl) eq_refl).
Qed.

Lemma bdf_fix_body_typed : si_Σ ;;; bdf_Γff |-E tLambda si_na (bdf_Dk 1) (tRel 0) : lift0 1 (bdf_fxty 0).
Proof.
  pose proof (bdf_dom_typed bdf_Γff 1 bdf_wf_Γff eq_refl) as hD.
  pose proof (iv_wf_vass si_Σ bdf_Γff si_na (bdf_Dk 1) sProp bdf_wf_Γff hD eq_refl) as hx.
  eapply (typeE_Cumul _ _ _ (tProd si_na (bdf_Dk 1) (bdf_Dk 2)) _ (Sort.sort_of_product sProp sProp)).
  - apply typeE_Lambda.
    + exact (iv_vass si_Σ bdf_Γff si_na (bdf_Dk 1) sProp hD eq_refl).
    + exact (typeE_Rel _ _ 0 (vass si_na (bdf_Dk 1)) hx eq_refl).
  - exact (bdf_fxty_typed bdf_Γff 1 bdf_wf_Γff eq_refl).
  - apply (ws_cumul_pbE_forget_spec (pb := Cumul)).
    apply (red_ws_cumul_pbE (Σ := si_Σ)).
    apply (closed_red_of (Σ := si_Σ) (Γ := bdf_Γff) (t := tProd si_na (bdf_Dk 1) (bdf_Dk 2)) eq_refl eq_refl).
    apply rt_step. change (lift0 1 (bdf_fxty 0)) with (tProd si_na (bdf_Dk 1) (tApp (tInd si_ind []) (tRel 2))).
    apply prod_red_r. exact (red_beta _ _ si_na si_P (tApp (tInd si_ind []) (tRel 0)) (tRel 2)).
Qed.

Lemma bdf_fix_guard : fix_guard si_Σ bd_Γ1 bdf_fmfix.
Proof.
  change (guard_cl Fix si_Σ bd_Γ1 bdf_fmfix). apply gc_check.
  split; [vm_compute; reflexivity|]. exists 30. vm_compute. reflexivity.
Qed.

Lemma bdf_wf_fix : wf_fixpointE si_Σ bd_Γ1 bdf_fmfix.
Proof.
  split; [reflexivity|]. split; [reflexivity|].
  exists si_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [|constructor].
  exists (tProd si_na (tApp (tInd si_ind []) (tRel 0)) (tApp (tInd si_ind []) (tRel 1))).
  split; [reflexivity|]. split; [reflexivity|].
  apply (ws_cumul_pbE_forget_spec (pb := Conv)).
  apply (red_ws_cumul_pbE (Σ := si_Σ)).
  apply (closed_red_of (Σ := si_Σ) (Γ := bd_Γ1) (t := bdf_fxty 0) eq_refl eq_refl).
  apply rt_step. apply prod_red_l. exact (red_beta _ _ si_na si_P (tApp (tInd si_ind []) (tRel 0)) (tRel 0)).
Qed.

Lemma bdf_fix_typed : si_Σ ;;; bd_Γ1 |-E tFix bdf_fmfix 0 : bdf_fxty 0.
Proof.
  refine (typeE_Fix _ _ bdf_fmfix 0 bdf_fix_dβ bd_wfE_Γ1 bdf_fix_guard eq_refl _ _ bdf_wf_fix).
  - constructor; [|constructor].
    exact (iv_vass si_Σ bd_Γ1 si_na (bdf_fxty 0) _ (bdf_fxty_typed bd_Γ1 0 bd_wfE_Γ1 eq_refl) eq_refl).
  - constructor; [|constructor].
    exact (iv_vdef si_Σ bdf_Γff si_na _ (lift0 1 (bdf_fxty 0)) _ bdf_fix_body_typed
             (bdf_fxty_typed bdf_Γff 1 bdf_wf_Γff eq_refl) eq_refl).
Qed.

(** ** Derivations whose comparisons relate two different types

  Each one below is a [typeE_Cumul], or contains one, whose two types differ: the per-rule rows
  and the judgment rows of completeness run on them. *)

(** [z := ∀P:Prop. P ⊢ λ x : z. x : Π x : z. ∀P:Prop. P]: the body [x] is typed at [∀P. P]
    through the δ-step of [z] ([bdf_x_prod_typed]). *)
Definition bdf_Γz1 : context := [vdef si_na iv_False si_P].

Lemma bdf_lam_z_typed : si_Σ ;;; bdf_Γz1 |-E tLambda si_na (tRel 0) (tRel 0) : tProd si_na (tRel 0) iv_False.
Proof.
  apply typeE_Lambda.
  - exact (iv_vass si_Σ bdf_Γz1 si_na (tRel 0) sProp
             (typeE_Rel _ _ 0 (vdef si_na iv_False si_P) (iv_wf_vdef si_Σ [] localenv_nil) eq_refl) eq_refl).
  - exact bdf_x_prod_typed.
Qed.

(** [let z : Prop := ∀P:Prop. P in λ x : z. x]: the body of the let is [bdf_lam_z_typed]. *)
Lemma bdf_letlam_z_typed :
  si_Σ ;;; [] |-E tLetIn si_na iv_False si_P (tLambda si_na (tRel 0) (tRel 0))
    : tLetIn si_na iv_False si_P (tProd si_na (tRel 0) iv_False).
Proof. apply typeE_LetIn; [exact (iv_vdef_False si_Σ [] localenv_nil)|exact bdf_lam_z_typed]. Qed.

(** [x (∀P:Prop. P) : ∀P:Prop. P] in [bdf_Γz]: the function [x] is typed at the product
    [∀P:Prop. P] through the δ-step of [z] ([bdf_x_prod_typed]). *)
Lemma bdf_app_z_typed : si_Σ ;;; bdf_Γz |-E tApp (tRel 0) iv_False : iv_False.
Proof.
  exact (typeE_App _ _ (tRel 0) si_na si_P (tRel 0) sProp iv_False
           (iv_False_typed si_Σ bdf_Γz bdi_wf_subst1_prem) bdf_x_prod_typed
           (iv_False_typed si_Σ bdf_Γz bdi_wf_subst1_prem)).
Qed.

(** [Π x : bdf_let. Prop]: the domain [bdf_let] is a type through the ζ-step of the let-in it
    infers ([bdf_let_sort_typed]). *)
Lemma bdf_prod_let_typed :
  si_Σ ;;; [] |-E tProd si_na bdf_let si_P : tSort (Sort.sort_of_product sProp (Sort.super sProp)).
Proof.
  apply typeE_Prod.
  - exact (iv_vass_s si_Σ [] si_na bdf_let sProp bdf_let_sort_typed eq_refl).
  - exact (iv_P_typed si_Σ _ (iv_wf_vass si_Σ [] si_na bdf_let sProp localenv_nil bdf_let_sort_typed eq_refl)).
Qed.

(** [r : (λ B : Prop. R B) (∀P. P) ⊢ r.(f) : ∀P:Prop. P] in [iv_Σ]: [r] is typed at
    [R (∀P. P)] through the β-step of its declared type ([bdf_r_typed]). *)
Definition bdf_Γrβ : context := [vass si_na bdf_RFβ].

Lemma bdf_wf_Γrβ : wf_localE iv_Σ bdf_Γrβ.
Proof. exact (iv_wf_vass iv_Σ [] si_na bdf_RFβ sProp localenv_nil (bdf_RFβ_typed [] localenv_nil) eq_refl). Qed.

Lemma bdf_r_typed : iv_Σ ;;; bdf_Γrβ |-E tRel 0 : mkApps (tInd iv_ind []) [iv_False].
Proof.
  refine (typeE_Cumul _ _ (tRel 0) (lift0 1 bdf_RFβ) _ sProp
            (typeE_Rel _ _ 0 (vass si_na bdf_RFβ) bdf_wf_Γrβ eq_refl) (iv_RF_typed _ bdf_wf_Γrβ) _).
  exact (cumulE_beta _ _ Cumul si_na si_P (iv_R (tRel 0)) iv_False).
Qed.

Lemma bdf_proj_typed : iv_Σ ;;; bdf_Γrβ |-E tProj iv_proj (tRel 0) : iv_False.
Proof.
  exact (typeE_Proj _ _ iv_proj (tRel 0) [] iv_mdecl iv_idecl iv_cdecl iv_pdecl [iv_False]
           iv_declared_projection bdf_r_typed eq_refl).
Qed.

(** The β-wrap [bdf_wrap s T = (λ X : s. X) T] of a type [T : s]: a type of sort [s], which one
    β-step relates to [T]. *)
Definition bdf_wrap (s : sort) (T : term) : term := tApp (tLambda si_na (tSort s) (tRel 0)) T.

Lemma bdf_wrap_typed (Σ : global_env_ext) (Γ : context) (s : sort) (T : term) :
  wf_localE Σ Γ -> wf_sort Σ s -> Σ ;;; Γ |-E T : tSort s -> Σ ;;; Γ |-E bdf_wrap s T : tSort s.
Proof.
  intros h hs hT.
  have rel : isSortRel (Sort.super s) si_na.(binder_relevance) by destruct s; exact eq_refl.
  have hS : Σ ;;; Γ |-E tSort s : tSort (Sort.super s) := typeE_Sort Σ Γ s h hs.
  have w : wf_localE Σ (Γ ,, vass si_na (tSort s)) := iv_wf_vass Σ Γ si_na (tSort s) (Sort.super s) h hS rel.
  refine (typeE_App _ _ (tLambda si_na (tSort s) (tRel 0)) si_na (tSort s) (tSort s)
            (Sort.sort_of_product (Sort.super s) (Sort.super s)) T _ _ hT).
  - apply typeE_Prod; [exact (iv_vass_s Σ Γ si_na (tSort s) _ hS rel)|exact (typeE_Sort _ _ s w hs)].
  - apply typeE_Lambda; [exact (iv_vass Σ Γ si_na (tSort s) _ hS rel)|].
    exact (typeE_Rel _ _ 0 (vass si_na (tSort s)) w eq_refl).
Qed.

Lemma bdf_wrap_cumul (Σ : global_env_ext) (Γ : context) (s : sort) (T : term) :
  cumulSpecE Σ Γ T (bdf_wrap s T).
Proof.
  apply cumulE_Sym.
  have h := cumulE_beta Σ Γ Conv si_na (tSort s) (tRel 0) T.
  have e : (tRel 0) {0 := T} = T by exact (lift0_p T).
  rewrite e in h. exact (h _).
Qed.

(** One reduction step, the β step [red_beta], takes [bdf_wrap s T] to [T]. *)
Lemma bdf_wrap_red1 (Σ : global_env) (Γ : context) (s : sort) (T : term) :
  red1 Σ Γ (bdf_wrap s T) T.
Proof.
  have h := red_beta Σ Γ si_na (tSort s) (tRel 0) T.
  have e : (tRel 0) {0 := T} = T by exact (lift0_p T).
  rewrite e in h. exact h.
Qed.

(** [Prop : (λ X. X) Type@{1}]. *)
Lemma bdf_sort_wrapped :
  si_Σ ;;; [] |-E si_P : bdf_wrap (Sort.super (Sort.super sProp)) (tSort (Sort.super sProp)).
Proof.
  have hP : si_Σ ;;; [] |-E si_P : tSort (Sort.super sProp) := iv_P_typed si_Σ [] localenv_nil.
  have hT : si_Σ ;;; [] |-E tSort (Sort.super sProp) : tSort (Sort.super (Sort.super sProp)) :=
    @typeE_Sort default_checker_flags si_Σ [] (Sort.super sProp) localenv_nil
      (PCUICWfUniversesEta.typing_wf_sortE (Σ := si_Σ) si_wfE hP).
  exact (typeE_Cumul _ _ si_P _ _ _ hP
           (bdf_wrap_typed si_Σ [] _ _ localenv_nil (PCUICWfUniversesEta.typing_wf_sortE (Σ := si_Σ) si_wfE hT) hT)
           (bdf_wrap_cumul si_Σ [] _ _)).
Qed.

(** [I : (λ X. X) (Π A : Prop. Prop)]. *)
Lemma bdf_ind_wrapped :
  si_Σ ;;; [] |-E tInd si_ind [] : bdf_wrap (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) si_arity.
Proof.
  have hT : si_Σ ;;; [] |-E si_arity : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) :=
    bd_arity_typedE [] localenv_nil.
  exact (typeE_Cumul _ _ (tInd si_ind []) _ _ _ (bd_ind_typedE [] localenv_nil)
           (bdf_wrap_typed si_Σ [] _ _ localenv_nil (PCUICWfUniversesEta.typing_wf_sortE (Σ := si_Σ) si_wfE hT) hT)
           (bdf_wrap_cumul si_Σ [] _ _)).
Qed.

(** [c : (λ X. X) (Π A : Prop. I A)]. *)
Lemma bdf_cstr_wrapped :
  si_Σ ;;; [] |-E tConstruct si_ind 0 [] :
    bdf_wrap (Sort.sort_of_product (Sort.super sProp) sProp) (tProd si_na si_P (tApp (tInd si_ind []) (tRel 0))).
Proof.
  have hT : si_Σ ;;; [] |-E tProd si_na si_P (tApp (tInd si_ind []) (tRel 0))
      : tSort (Sort.sort_of_product (Sort.super sProp) sProp) := iv_cstr_prod_typed [] localenv_nil.
  exact (typeE_Cumul _ _ (tConstruct si_ind 0 []) _ _ _ (iv_cstr_typed [] localenv_nil)
           (bdf_wrap_typed si_Σ [] _ _ localenv_nil (PCUICWfUniversesEta.typing_wf_sortE (Σ := si_Σ) si_wfE hT) hT)
           (bdf_wrap_cumul si_Σ [] _ _)).
Qed.

(** The fixpoint [iv_fix] of [PCUICInversionEtaInstances] at [(λ X. X) iv_fix_ty]. *)
Lemma bdf_fix_wrapped :
  si_Σ ;;; [] |-E tFix iv_mfix 0 : bdf_wrap (Sort.sort_of_product sProp sProp) iv_fix_ty.
Proof.
  have hT : si_Σ ;;; [] |-E iv_fix_ty : tSort (Sort.sort_of_product sProp sProp) := iv_fix_ty_typed [] localenv_nil.
  exact (typeE_Cumul _ _ (tFix iv_mfix 0) _ _ _ iv_fix_typed
           (bdf_wrap_typed si_Σ [] _ _ localenv_nil (PCUICWfUniversesEta.typing_wf_sortE (Σ := si_Σ) si_wfE hT) hT)
           (bdf_wrap_cumul si_Σ [] _ _)).
Qed.

(** [int : Set] in [Σ_po] over [typingE] ([PCUICEtaPrimOpInstance.po_int_typed] over [typing]). *)
Lemma bdf_int_typed (Γ : context) : wf_localE Σ_po Γ -> Σ_po ;;; Γ |-E tConst po_int_kn [] : tSort Sort.type0.
Proof.
  intros h. change (tSort Sort.type0) with (subst_instance [] (cst_type po_int_body)).
  exact (typeE_Const _ _ po_int_kn [] po_int_body h iv_po_declared_int eq_refl).
Qed.

(** [int → int → int : Set] in [Σ_po] over [typingE]. *)
Lemma bdf_land_ty_typed :
  Σ_po ;;; [] |-E po_land_ty : tSort (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0)).
Proof.
  have w1 : wf_localE Σ_po [vass (mkBindAnn nAnon rel_of_Type) (tConst po_int_kn [])] :=
    iv_wf_vass Σ_po [] (mkBindAnn nAnon rel_of_Type) (tConst po_int_kn []) Sort.type0
      localenv_nil (bdf_int_typed [] localenv_nil) eq_refl.
  have w2 : wf_localE Σ_po [vass (mkBindAnn nAnon rel_of_Type) (tConst po_int_kn []);
                            vass (mkBindAnn nAnon rel_of_Type) (tConst po_int_kn [])] :=
    iv_wf_vass Σ_po _ (mkBindAnn nAnon rel_of_Type) (tConst po_int_kn []) Sort.type0
      w1 (bdf_int_typed _ w1) eq_refl.
  unfold po_land_ty, tImpl.
  apply typeE_Prod.
  { exact (iv_vass_s Σ_po [] (mkBindAnn nAnon rel_of_Type) (tConst po_int_kn []) Sort.type0
             (bdf_int_typed [] localenv_nil) eq_refl). }
  apply typeE_Prod.
  { exact (iv_vass_s Σ_po _ (mkBindAnn nAnon rel_of_Type) (tConst po_int_kn []) Sort.type0
             (bdf_int_typed _ w1) eq_refl). }
  exact (bdf_int_typed _ w2).
Qed.

(** [land : (λ X. X) (int → int → int)]. *)
Lemma bdf_const_wrapped :
  Σ_po ;;; [] |-E tConst po_land_kn [] :
    bdf_wrap (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0)) po_land_ty.
Proof.
  exact (typeE_Cumul _ _ (tConst po_land_kn []) _ _ _ iv_land_typed
           (bdf_wrap_typed Σ_po [] _ _ localenv_nil
              (PCUICWfUniversesEta.typing_wf_sortE (Σ := Σ_po) iv_po_wfE bdf_land_ty_typed) bdf_land_ty_typed)
           (bdf_wrap_cumul Σ_po [] _ _)).
Qed.

(** The literal [1 : (λ X. X) int]. *)
Lemma bdf_prim_wrapped :
  Σ_po ;;; [] |-E tPrim iv_one : bdf_wrap Sort.type0 (prim_type iv_one po_int_kn).
Proof.
  have hT : Σ_po ;;; [] |-E prim_type iv_one po_int_kn : tSort Sort.type0 by exact (bdf_int_typed [] localenv_nil).
  exact (typeE_Cumul _ _ (tPrim iv_one) _ _ _ iv_prim_typed
           (bdf_wrap_typed Σ_po [] _ _ localenv_nil (PCUICWfUniversesEta.typing_wf_sortE (Σ := Σ_po) iv_po_wfE hT) hT)
           (bdf_wrap_cumul Σ_po [] _ _)).
Qed.

(** The let-judgment [z := bdf_let : Prop]: its body [bdf_let] is typed at [Prop] through the
    ζ-step of the let-in it infers ([bdf_let_sort_typed]). *)
Lemma bdf_vdef_let_typed : lift_typing typingE si_Σ [] (j_vdef si_na bdf_let si_P).
Proof.
  exact (iv_vdef si_Σ [] si_na bdf_let si_P (Sort.super sProp) bdf_let_sort_typed
           (iv_P_typed si_Σ [] localenv_nil) eq_refl).
Qed.

(** The context [[x : bdf_let]], alone and over [bd_ΓFG]. *)
Definition bdf_Γlet : context := [vass si_na bdf_let].

Lemma bdf_wf_Γlet : wf_localE si_Σ bdf_Γlet.
Proof. exact (iv_wf_vass si_Σ [] si_na bdf_let sProp localenv_nil bdf_let_sort_typed eq_refl). Qed.

Lemma bdf_let_sort_typed_FG : si_Σ ;;; bd_ΓFG |-E bdf_let : tSort sProp.
Proof.
  eapply (typeE_Cumul _ _ bdf_let (tLetIn si_na iv_False si_P si_P) si_P (Sort.super sProp)).
  - exact (iv_let_typed si_Σ bd_ΓFG bdi_wfFG).
  - exact (iv_P_typed si_Σ bd_ΓFG bdi_wfFG).
  - apply (ws_cumul_pbE_forget_spec (pb := Cumul)).
    apply (red_ws_cumul_pbE (Σ := si_Σ)).
    exact (closed_red_of (Σ := si_Σ) (Γ := bd_ΓFG) (t := tLetIn si_na iv_False si_P si_P) eq_refl eq_refl
             (red1_red _ _ _ _ (red_zeta _ _ si_na iv_False si_P si_P))).
Qed.

Lemma bdf_wf_ΓFGlet : wf_localE si_Σ (bd_ΓFG ,,, [vass si_na bdf_let]).
Proof. exact (iv_wf_vass si_Σ bd_ΓFG si_na bdf_let sProp bdi_wfFG bdf_let_sort_typed_FG eq_refl). Qed.

(** The parameter instance [[x]] against [[_ : ∀P:Prop. P]] in [bdf_Γz]: [x] is typed at
    [∀P. P] through the δ-step of [z] ([bdf_x_prod_typed]). *)
Lemma bdf_ctx_inst_z : PCUICTyping.ctx_inst (typingE si_Σ) bdf_Γz [tRel 0] [vass si_na iv_False].
Proof. econstructor; [|constructor]. exact bdf_x_prod_typed. Qed.

Section BDFromPCUICEtaInstances.

(** ** Through an η conversion *)

(** Every type inferred for [x] in [bd_Γη] is not [G F], the type of [x] in [bdf_eta_typed],
    and one η step relates it to [G F]. *)
Lemma bdf_eta_nondeg :
  forall T', si_Σ ;;; bd_Γη |-E tRel 0 ▹ T' ->
    (T' <> tApp (tRel 2) (tRel 1)) × eta1 T' (tApp (tRel 2) (tRel 1)).
Proof.
  intros T' h. inversion h; subst.
  match goal with hn : nth_error _ _ = Some _ |- _ => vm_compute in hn; injection hn as hd; subst end.
  split; [discriminate|exact bd_eta_step].
Qed.

(** Completeness on [bdf_eta_typed] ([x : G F] in [bd_Γη]). Every type inferred for [x] is not
    [G F] and one η step relates it to [G F] ([bdf_eta_nondeg]), so the cumulativity this
    instance returns relates two different types.
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_eta_nondeg
    TARGET BDFromPCUICEta.typing_inferingE *)
Lemma typing_inferingE_eta_inst :
  ∑ T', si_Σ ;;; bd_Γη |-E tRel 0 ▹ T' × si_Σ ;;; bd_Γη ⊢E T' ≤ tApp (tRel 2) (tRel 1).
Proof. exact (typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) bdf_eta_typed). Qed.

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_eta_nondeg
    TARGET BDFromPCUICEta.typing_checkingE *)
Lemma typing_checkingE_eta_inst : si_Σ ;;; bd_Γη |-E tRel 0 ◃ tApp (tRel 2) (tRel 1).
Proof. exact (typing_checkingE (Σ := si_Σ) (wfΣ := si_wfE) bdf_eta_typed). Qed.

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_eta_nondeg *)
Lemma bidirectional_from_pcuicE_inst :
  {T' & si_Σ ;;; bd_Γη |-E tRel 0 ▹ T' × si_Σ ;;; bd_Γη ⊢E T' ≤ tApp (tRel 2) (tRel 1)}.
Proof. exact (env_propE_typing bidirectional_from_pcuicE si_Σ si_wfE _ _ _ bdf_eta_typed). Qed.

(** [conv_checkE] on the inference pair of [typing_inferingE_eta_inst] in [bd_Γη].
    INSTANCE IMPOSSIBLE: the target's proof destructs its premise pair and applies the checkE_Cumul constructor to the inference and to ws_cumul_pbE_forget (a projection of the ws_cumul_pbE record) of the cumulativity, so every instance's conclusion only repacks its own premise and no witness can make it non-degenerate
    TARGET BDFromPCUICEta.conv_checkE *)
Lemma conv_checkE_eta_inst : si_Σ ;;; bd_Γη |-E tRel 0 ◃ tApp (tRel 2) (tRel 1).
Proof. exact (conv_checkE si_Σ si_wfE _ _ _ typing_inferingE_eta_inst). Qed.

(** ** Through the T8 sites, at inferred types that are not head forms *)

(** Every type inferred for [bdf_let] in the empty context is not a sort. *)
Lemma bdf_let_nondeg : forall T', si_Σ ;;; [] |-E bdf_let ▹ T' -> forall s, T' <> tSort s.
Proof. intros T' h s. unfold bdf_let in h. inversion h; subst. discriminate. Qed.

(** The twin of [bdf_let_nondeg] in [bd_ΓFG]: every type inferred for [bdf_let] in [bd_ΓFG]
    is not a sort. *)
Lemma bdf_let_FG_nondeg : forall T', si_Σ ;;; bd_ΓFG |-E bdf_let ▹ T' -> forall s, T' <> tSort s.
Proof. intros T' h s. unfold bdf_let in h. inversion h; subst. discriminate. Qed.

(** [typing_infering_sortE] on [bdf_let_sort_typed] ([bdf_let : Prop]). Every type inferred
    for [bdf_let] is not a sort ([bdf_let_nondeg]), so the [▹□] judgment this instance returns
    reaches its sort by a reduction between two different terms.
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_let_nondeg
    TARGET BDFromPCUICEta.typing_infering_sortE *)
Lemma typing_infering_sortE_let_inst :
  ∑ u', si_Σ ;;; [] |-E bdf_let ▹□ u' × leq_sort si_Σ u' sProp.
Proof. exact (typing_infering_sortE (Σ := si_Σ) (wfΣ := si_wfE) bdf_let_sort_typed). Qed.

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_let_nondeg
    TARGET BDFromPCUICEta.conv_infer_sortE *)
Lemma conv_infer_sortE_let_inst :
  {s' & si_Σ ;;; [] |-E bdf_let ▹□ s' × leq_sort si_Σ s' sProp}.
Proof.
  exact (conv_infer_sortE si_Σ si_wfE [] bdf_let sProp bdf_let_sort_typed
           (typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) bdf_let_sort_typed)).
Qed.

(** Every type inferred for [x] in [bdf_Γz] is not a product, so in particular not
    [∀P:Prop. P], the type of [x] in [bdf_x_prod_typed]. *)
Lemma bdf_z_nondeg :
  forall T', si_Σ ;;; bdf_Γz |-E tRel 0 ▹ T' -> forall na A B, T' <> tProd na A B.
Proof.
  intros T' h na A B. inversion h; subst.
  match goal with hn : nth_error _ _ = Some _ |- _ => vm_compute in hn; injection hn as hd; subst end.
  discriminate.
Qed.

(** [typing_infer_prodE] on [bdf_x_prod_typed] ([x : ∀P:Prop. P] in [bdf_Γz]). Every type
    inferred for [x] is not a product ([bdf_z_nondeg]), so the [▹Π] judgment this instance
    returns reaches its product by a reduction between two different terms.
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_z_nondeg
    TARGET BDFromPCUICEta.typing_infer_prodE *)
Lemma typing_infer_prodE_let_inst :
  ∑ na' A' B', [× si_Σ ;;; bdf_Γz |-E tRel 0 ▹Π (na',A',B'),
    eq_binder_annot si_na na', si_Σ ;;; bdf_Γz ⊢E A' = si_P &
    si_Σ ;;; bdf_Γz ,, vass si_na si_P ⊢E B' ≤ tRel 0].
Proof. exact (typing_infer_prodE (Σ := si_Σ) (wfΣ := si_wfE) bdf_x_prod_typed). Qed.

(** [conv_infer_prodE] on [bdf_x_prod_typed] and the inference pair that [typing_inferingE]
    gives for it. The pair's type is a type inferred for [x] in [bdf_Γz], so it is not a
    product ([bdf_z_nondeg]): the cumulativity passed in relates a type that is not a product
    to [∀P:Prop. P].
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_z_nondeg *)
Lemma conv_infer_prodE_inst :
  ∑ na' A' B', [× si_Σ ;;; bdf_Γz |-E tRel 0 ▹Π (na',A',B'),
    eq_binder_annot si_na na', si_Σ ;;; bdf_Γz ⊢E A' = si_P &
    si_Σ ;;; bdf_Γz ,, vass si_na si_P ⊢E B' ≤ tRel 0].
Proof.
  exact (conv_infer_prodE si_Σ si_wfE bdf_Γz (tRel 0) si_na si_P (tRel 0) bdf_x_prod_typed
           (typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) bdf_x_prod_typed)).
Qed.

(** Every type inferred for [x] in [bdf_Γβ] is not an application of an inductive type. *)
Lemma bdf_beta_nondeg :
  forall T', si_Σ ;;; bdf_Γβ |-E tRel 0 ▹ T' -> forall ind u args, T' <> mkApps (tInd ind u) args.
Proof.
  intros T' h ind u args. inversion h; subst.
  match goal with hn : nth_error _ _ = Some _ |- _ => vm_compute in hn; injection hn as hd; subst end.
  intros e.
  have hdec : decompose_app (mkApps (tInd ind u) args) = (tInd ind u, args) by apply decompose_app_mkApps.
  rewrite -e in hdec. vm_compute in hdec. discriminate hdec.
Qed.

(** [typing_infer_indE] on [bdf_x_ind_typed] ([x : I A] in [bdf_Γβ]). Every type inferred for
    [x] is not an application of an inductive type ([bdf_beta_nondeg]), so the [▹{I}] judgment
    this instance returns reaches an application of [I] by a reduction between two different
    terms.
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_beta_nondeg
    TARGET BDFromPCUICEta.typing_infer_indE *)
Lemma typing_infer_indE_beta_inst :
  ∑ ui' args', [× si_Σ ;;; bdf_Γβ |-E tRel 0 ▹{si_ind} (ui',args'),
      cmp_ind_universes si_Σ si_ind #|[tRel 1]| ui' []
      & ws_cumul_pbE_terms si_Σ bdf_Γβ args' [tRel 1]].
Proof. exact (typing_infer_indE si_Σ si_wfE _ _ _ _ _ bdf_x_ind_typed). Qed.

(** [conv_infer_indE] on [bdf_x_ind_typed] and the inference pair that [typing_inferingE]
    gives for it. The pair's type is a type inferred for [x] in [bdf_Γβ], so it is not an
    application of an inductive type ([bdf_beta_nondeg]): the cumulativity passed in relates
    such a type to [I A].
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_beta_nondeg *)
Lemma conv_infer_indE_inst :
  ∑ ui' args', [× si_Σ ;;; bdf_Γβ |-E tRel 0 ▹{si_ind} (ui',args'),
      cmp_ind_universes si_Σ si_ind #|[tRel 1]| ui' []
      & ws_cumul_pbE_terms si_Σ bdf_Γβ args' [tRel 1]].
Proof.
  exact (conv_infer_indE si_Σ si_wfE bdf_Γβ (tRel 0) si_ind [] [tRel 1] bdf_x_ind_typed
           (typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) bdf_x_ind_typed)).
Qed.

(** The bound is attained: the head arity of [I] (its parameter [A]) is the length of
    [[tRel 1]], so the instance is not the vacuous case of an inductive with no parameter. *)
Lemma bdf_head_arity_nondeg : head_arity si_Σ.1 (IndRef si_ind) = #|[tRel 1]|.
Proof. reflexivity. Qed.

(** The premise is [validityE] of [bdf_x_ind_typed] ([x : I A] in [bdf_Γβ]). The head arity of
    [I] is the length of [[tRel 1]] ([bdf_head_arity_nondeg]), so the bound is attained.
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_head_arity_nondeg *)
Lemma isTypeE_mkApps_Ind_head_arity_inst : head_arity si_Σ.1 (IndRef si_ind) <= #|[tRel 1]|.
Proof.
  exact (isTypeE_mkApps_Ind_head_arity (Σ := si_Σ) (wfΣ := si_wfE) bdf_wfβ
           (validityE (Σ := si_Σ) (wfΣ := si_wfE) bdf_x_ind_typed)).
Qed.

(** ** The (co)fixpoint witness, at declared types on which the check fails *)

(** [bd_fix_d]: [check_one_fix] fails at the declared type [bd_fix_dtype = Π x : (λ B. I B) A.
    Prop], passes at [bd_fix_ty = Π x : I A. Prop], and [bd_fix_dtype] reduces to
    [bd_fix_ty]. *)
Lemma bdf_fix_d_nondeg :
  [× map check_one_fix bd_mfix = [None],
     check_one_fix (def_with_type bd_fix_d bd_fix_ty) = Some si_kn &
     red si_Σ bd_Γ1 bd_fix_dtype bd_fix_ty].
Proof. split; [reflexivity|reflexivity|exact bd_fix_dtype_red]. Qed.

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_fix_d_nondeg *)
Lemma red_fix_witnessE_inst :
  ∑ Δ na u' l' B,
    [× red si_Σ bd_Γ1 bd_fix_dtype (it_mkProd_or_LetIn (vass na (mkApps (tInd si_ind u') l') :: Δ) B),
       assumption_context Δ & #|Δ| = 0].
Proof.
  exact (red_fix_witnessE (Σ := si_Σ) (wfΣ := si_wfE) [vass si_na (mkApps (tInd si_ind []) [tRel 0])]
           0 (vass si_na (mkApps (tInd si_ind []) [tRel 0])) bd_Γ1 bd_fix_dtype si_P si_ind [] [tRel 0]
           bd_fix_dtype_isTypeE bdf_fix_dtype_ws eq_refl eq_refl).
Qed.

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_fix_d_nondeg *)
Lemma mfix_body_on_conv_redE_fix_inst : mfix_body_on check_one_fix (red si_Σ bd_Γ1) si_kn bd_fix_d.
Proof.
  exact (mfix_body_on_conv_redE_fix (Σ := si_Σ) (wfΣ := si_wfE) (d := bd_fix_d) bd_wfE_Γ1 bd_fix_dtype_isTypeE
           bdf_fix_witness).
Qed.

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_fix_d_nondeg *)
Lemma mfix_on_ind_conv_redE_fix_inst :
  mfix_on_ind check_one_fix (red si_Σ bd_Γ1)
    (fun mind => check_recursivity_kind (lookup_env si_Σ) mind Finite) bd_mfix.
Proof.
  exact (mfix_on_ind_conv_redE_fix (Σ := si_Σ) (wfΣ := si_wfE) (mfix := bd_mfix) bd_wfE_Γ1
           (@All_cons _ _ bd_fix_d _ bd_fix_dtype_isTypeE All_nil) bd_mfix_on_ind_red_convE_inst).
Qed.

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_fix_d_nondeg *)
Lemma wf_fixpointE_wf_fixpoint_red_inst : wf_fixpoint_red si_Σ bd_Γ1 bd_mfix.
Proof.
  exact (wf_fixpointE_wf_fixpoint_red (Σ := si_Σ) (wfΣ := si_wfE) (mfix := bd_mfix) bd_wfE_Γ1
           (@All_cons _ _ bd_fix_d _ bd_fix_dtype_isTypeE All_nil) wf_fixpoint_red_wf_fixpointE_inst).
Qed.

(** [bdf_cofix_d]: [check_one_cofix] fails at the declared type [(λ B. I B) A], passes at
    [I A], and [(λ B. I B) A] reduces to [I A]. *)
Lemma bdf_cofix_d_nondeg :
  [× check_one_cofix bdf_cofix_d = None,
     check_one_cofix (def_with_type bdf_cofix_d (mkApps (tInd si_ind []) [tRel 0])) = Some si_kn &
     red si_Σ bd_Γ1 bd_fix_dom (mkApps (tInd si_ind []) [tRel 0])].
Proof. split; [reflexivity|reflexivity|exact bdf_cofix_dom_red]. Qed.

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_cofix_d_nondeg *)
Lemma red_cofix_witnessE_inst :
  ∑ Δ u' l', red si_Σ bd_Γ1 bd_fix_dom (it_mkProd_or_LetIn Δ (mkApps (tInd si_ind u') l')).
Proof.
  exact (red_cofix_witnessE (Σ := si_Σ) (wfΣ := si_wfE) [] bd_Γ1 bd_fix_dom si_ind [] [tRel 0]
           (has_sort_isTypeE _ bd_fix_dom_typedE) bdf_cofix_dom_ws).
Qed.

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_cofix_d_nondeg *)
Lemma mfix_body_on_conv_redE_cofix_inst :
  mfix_body_on check_one_cofix (red si_Σ bd_Γ1) si_kn bdf_cofix_d.
Proof.
  exact (mfix_body_on_conv_redE_cofix (Σ := si_Σ) (wfΣ := si_wfE) (d := bdf_cofix_d) bd_wfE_Γ1
           (has_sort_isTypeE _ bd_fix_dom_typedE) bdf_cofix_witness).
Qed.

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_cofix_d_nondeg *)
Lemma mfix_on_ind_conv_redE_cofix_inst :
  mfix_on_ind check_one_cofix (red si_Σ bd_Γ1) (fun _ => true) [bdf_cofix_d].
Proof.
  refine (mfix_on_ind_conv_redE_cofix (Σ := si_Σ) (wfΣ := si_wfE) (mfix := [bdf_cofix_d]) bd_wfE_Γ1
            (@All_cons _ _ bdf_cofix_d _ (has_sort_isTypeE _ bd_fix_dom_typedE) All_nil) _).
  exists si_kn. split; [discriminate|]. split; [|reflexivity].
  exact (All_cons bdf_cofix_witness All_nil).
Qed.

(** ** Completeness per typing rule *)

(** A β-wrap is never the type it wraps ([T] is a proper subterm of [bdf_wrap s T]). *)
Lemma bdf_wrap_nondeg : forall s T, bdf_wrap s T <> T.
Proof.
  intros s T. induction T; try discriminate.
  unfold bdf_wrap in *. intros e. injection e as e1 e2. subst.
  match goal with IH : tApp ?L ?v <> ?v, e : tApp ?L ?v = ?v |- _ => exact (IH e) end.
Qed.

(** Rel: completeness on [bdf_x_prod_typed] ([x : ∀P:Prop. P] in [bdf_Γz]). Every type
    inferred for [x] is not a product ([bdf_z_nondeg]), so not [∀P:Prop. P]: the cumulativity
    this instance returns relates two different types.
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_z_nondeg
    TARGET BDFromPCUICEta.typing_inferingE *)
Definition typing_inferingE_Rel_inst := typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) bdf_x_prod_typed.

(** Every type inferred for [Prop] is [tSort (Sort.super sProp)], which is not
    [bdf_wrap (Sort.super (Sort.super sProp)) (tSort (Sort.super sProp))]; one reduction step
    takes that β-wrap to it. *)
Lemma bdf_sort_wrap_nondeg :
  forall T', si_Σ ;;; [] |-E si_P ▹ T' ->
    [× T' = tSort (Sort.super sProp),
       T' <> bdf_wrap (Sort.super (Sort.super sProp)) (tSort (Sort.super sProp)) &
       red1 si_Σ [] (bdf_wrap (Sort.super (Sort.super sProp)) (tSort (Sort.super sProp))) T'].
Proof.
  intros T' h.
  assert (e : T' = tSort (Sort.super sProp)).
  { unfold si_P in h. inversion h; subst. reflexivity. }
  subst T'. split; [reflexivity|exact (fun e => bdf_wrap_nondeg _ _ (eq_sym e))|apply bdf_wrap_red1].
Qed.

(** Sort: completeness on [bdf_sort_wrapped], [Prop] at [bdf_wrap _ T] with
    [T = tSort (Sort.super sProp)]. Every type inferred for [Prop] is [T], which is not
    [bdf_wrap _ T], and one reduction step takes [bdf_wrap _ T] to [T]
    ([bdf_sort_wrap_nondeg]): the cumulativity this instance returns relates two different
    types.
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_sort_wrap_nondeg
    TARGET BDFromPCUICEta.typing_inferingE *)
Definition typing_inferingE_Sort_inst :=
  typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE)
    (T := bdf_wrap (Sort.super (Sort.super sProp)) (tSort (Sort.super sProp))) bdf_sort_wrapped.

(** Prod: completeness on [bdf_prod_let_typed] ([Π x : bdf_let. Prop]). Every type inferred
    for its domain [bdf_let] is not a sort ([bdf_let_nondeg]).
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_let_nondeg
    TARGET BDFromPCUICEta.typing_inferingE *)
Definition typing_inferingE_Prod_inst := typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) bdf_prod_let_typed.

(** Lambda: completeness on [bdf_lam_z_typed] ([λ x : z. x : Π x : z. ∀P:Prop. P] in
    [z := ∀P:Prop. P]). Its body [x] lives in [bdf_Γz], where every type inferred for [x] is
    not a product ([bdf_z_nondeg]), so not [∀P:Prop. P].
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_z_nondeg
    TARGET BDFromPCUICEta.typing_inferingE *)
Definition typing_inferingE_Lambda_inst := typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) bdf_lam_z_typed.

(** LetIn: completeness on [bdf_letlam_z_typed] ([let z := ∀P:Prop. P in λ x : z. x]). The
    inner variable [x] lives in [bdf_Γz], where every type inferred for [x] is not a product
    ([bdf_z_nondeg]).
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_z_nondeg
    TARGET BDFromPCUICEta.typing_inferingE *)
Definition typing_inferingE_LetIn_inst := typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) bdf_letlam_z_typed.

(** App: completeness on [bdf_app_z_typed] ([x (∀P:Prop. P) : ∀P:Prop. P] in [bdf_Γz]). Every
    type inferred for the function [x] is not a product ([bdf_z_nondeg]), so a [▹Π] judgment
    on [x] in [bdf_Γz] reaches its product by a reduction between two different terms.
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_z_nondeg
    TARGET BDFromPCUICEta.typing_inferingE *)
Definition typing_inferingE_App_inst := typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) bdf_app_z_typed.

(** Every type inferred for [I] is [si_arity], which is not [bdf_wrap _ si_arity]; one
    reduction step takes [bdf_wrap _ si_arity] to it. *)
Lemma bdf_ind_wrap_nondeg :
  forall T', si_Σ ;;; [] |-E tInd si_ind [] ▹ T' ->
    [× T' = si_arity,
       T' <> bdf_wrap (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) si_arity &
       red1 si_Σ [] (bdf_wrap (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) si_arity) T'].
Proof.
  intros T' h.
  assert (e : T' = si_arity).
  { inversion h; subst.
    match goal with hd : declared_inductive _ _ _ _ |- _ =>
      destruct (PCUICGlobalEnv.declared_inductive_inj (declared_inductive_to_gen (wfΣ := si_wf) hd)
                  (declared_inductive_to_gen (wfΣ := si_wf) si_declared_inductive)) as [e1 e2];
      subst end.
    reflexivity. }
  subst T'. split; [reflexivity|exact (fun e => bdf_wrap_nondeg _ _ (eq_sym e))|apply bdf_wrap_red1].
Qed.

(** Ind: completeness on [bdf_ind_wrapped], [I] at [bdf_wrap _ si_arity]. Every type inferred
    for [I] is [si_arity], which is not [bdf_wrap _ si_arity], and one reduction step takes
    [bdf_wrap _ si_arity] to [si_arity] ([bdf_ind_wrap_nondeg]): the cumulativity this
    instance returns relates two different types.
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_ind_wrap_nondeg
    TARGET BDFromPCUICEta.typing_inferingE *)
Definition typing_inferingE_Ind_inst :=
  typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE)
    (T := bdf_wrap (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) si_arity) bdf_ind_wrapped.

(** Every type inferred for [c] is [Π A : Prop. I A], which is not its β-wrap
    [bdf_wrap _ (Π A : Prop. I A)]; one reduction step takes that β-wrap to it. *)
Lemma bdf_cstr_wrap_nondeg :
  forall T', si_Σ ;;; [] |-E tConstruct si_ind 0 [] ▹ T' ->
    [× T' = tProd si_na si_P (tApp (tInd si_ind []) (tRel 0)),
       T' <> bdf_wrap (Sort.sort_of_product (Sort.super sProp) sProp)
               (tProd si_na si_P (tApp (tInd si_ind []) (tRel 0))) &
       red1 si_Σ [] (bdf_wrap (Sort.sort_of_product (Sort.super sProp) sProp)
                       (tProd si_na si_P (tApp (tInd si_ind []) (tRel 0)))) T'].
Proof.
  intros T' h.
  assert (e : T' = tProd si_na si_P (tApp (tInd si_ind []) (tRel 0))).
  { inversion h; subst.
    match goal with hd : declared_constructor _ _ _ _ _ |- _ =>
      destruct (PCUICGlobalEnv.declared_constructor_inj (declared_constructor_to_gen (wfΣ := si_wf) hd)
                  (declared_constructor_to_gen (wfΣ := si_wf) si_declared_constructor)) as (e1 & e2 & e3);
      subst end.
    reflexivity. }
  subst T'. split; [reflexivity|exact (fun e => bdf_wrap_nondeg _ _ (eq_sym e))|apply bdf_wrap_red1].
Qed.

(** Construct: completeness on [bdf_cstr_wrapped], [c] at [bdf_wrap _ T] with
    [T = Π A : Prop. I A]. Every type inferred for [c] is [T], which is not [bdf_wrap _ T], and
    one reduction step takes [bdf_wrap _ T] to [T] ([bdf_cstr_wrap_nondeg]): the cumulativity
    this instance returns relates two different types.
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_cstr_wrap_nondeg
    TARGET BDFromPCUICEta.typing_inferingE *)
Definition typing_inferingE_Construct_inst :=
  typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE)
    (T := bdf_wrap (Sort.sort_of_product (Sort.super sProp) sProp) (tProd si_na si_P (tApp (tInd si_ind []) (tRel 0))))
    bdf_cstr_wrapped.

(** Every type inferred for [c x] ([iv_disc]) in [iv_Γ1] is [I x] ([iv_Ix 0]); the β-redex
    [(λ z : I x. I x) (c x)] is not [I x], and one reduction step takes it to [I x]. *)
Lemma bdf_case_br_nondeg :
  [× tApp (tLambda iv_zna (iv_Ix 0) (iv_Ix 1)) iv_disc <> iv_Ix 0,
     red1 si_Σ iv_Γ1 (tApp (tLambda iv_zna (iv_Ix 0) (iv_Ix 1)) iv_disc) (iv_Ix 0) &
     forall T', si_Σ ;;; iv_Γ1 |-E iv_disc ▹ T' -> T' = iv_Ix 0].
Proof.
  split; [discriminate|exact (red_beta _ _ iv_zna (iv_Ix 0) (iv_Ix 1) iv_disc)|].
  intros T' h. unfold iv_disc in h. inversion h; subst.
  match goal with hp : @infering_prodE _ _ _ (tConstruct _ _ _) _ _ _ |- _ => inversion hp; subst end.
  match goal with hc : @inferingE _ _ _ (tConstruct _ _ _) _ |- _ => inversion hc; subst end.
  match goal with hd : declared_constructor _ _ _ _ _ |- _ =>
    destruct (PCUICGlobalEnv.declared_constructor_inj (declared_constructor_to_gen (wfΣ := si_wf) hd)
                (declared_constructor_to_gen (wfΣ := si_wf) si_declared_constructor)) as (e1 & e2 & e3);
    subst end.
  match goal with hr : red _ _ _ (tProd _ _ _) |- _ =>
    destruct (PCUICConversion.invert_red_prod_cb (Σ := si_Σ) (cbΣ := si_cb)
                (closed_red_of (Σ := si_Σ) (Γ := iv_Γ1)
                   (t := tProd si_na si_P (tApp (tInd si_ind []) (tRel 0))) eq_refl eq_refl hr))
      as (dom' & codom' & [ep _ hcod])
  end.
  injection ep as e1 e2 e3. subst.
  destruct (PCUICConversion.invert_red_mkApps_tInd_cb (Σ := si_Σ) (cbΣ := si_cb) (ind := si_ind) (u := [])
              [tRel 0] _ hcod) as (args' & [ec _ ha]).
  subst.
  destruct args' as [|a [|a' rest]].
  - inversion ha.
  - assert (hra : closed_red si_Σ (iv_Γ1 ,, vass si_na si_P) (tRel 0) a) by (inversion ha; assumption).
    destruct hra as [clΓ _ rr].
    destruct (PCUICConfluence.red_mkApps_tRel_cb (Σ := si_Σ) (wfΣ := si_cb)
                (Γ := exist (iv_Γ1 ,, vass si_na si_P) clΓ) (k := 0) (b := vass si_na si_P) (args := [])
                eq_refl eq_refl eq_refl rr) as (args'' & ea & ha'').
    destruct args''; [|inversion ha''].
    subst. reflexivity.
  - inversion ha. match goal with hn : All2 _ [] (_ :: _) |- _ => inversion hn end.
Qed.

(** Case: completeness on [iv_match_typed] ([iv_match], whose scrutinee and branch body are both
    [c x]). Every type inferred for [c x] is [I x], which is not [(λ z : I x. I x) (c x)], the
    type at which [iv_br_typed] types [c x]; one reduction step takes the latter to [I x]
    ([bdf_case_br_nondeg]).
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_case_br_nondeg
    TARGET BDFromPCUICEta.typing_inferingE *)
Definition typing_inferingE_Case_inst := typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) iv_match_typed.

(** Every type inferred for [tFix iv_mfix 0] is [iv_fix_ty], which is not
    [bdf_wrap _ iv_fix_ty]; one reduction step takes [bdf_wrap _ iv_fix_ty] to it. *)
Lemma bdf_fix_wrap_nondeg :
  forall T', si_Σ ;;; [] |-E tFix iv_mfix 0 ▹ T' ->
    [× T' = iv_fix_ty,
       T' <> bdf_wrap (Sort.sort_of_product sProp sProp) iv_fix_ty &
       red1 si_Σ [] (bdf_wrap (Sort.sort_of_product sProp sProp) iv_fix_ty) T'].
Proof.
  intros T' h.
  assert (e : T' = iv_fix_ty).
  { inversion h; subst.
    match goal with hn : nth_error _ _ = Some _ |- _ => vm_compute in hn; injection hn as hd; subst end.
    reflexivity. }
  subst T'. split; [reflexivity|exact (fun e => bdf_wrap_nondeg _ _ (eq_sym e))|apply bdf_wrap_red1].
Qed.

(** Fix: completeness on [bdf_fix_wrapped], [tFix iv_mfix 0] ([PCUICInversionEtaInstances]) at
    [bdf_wrap _ iv_fix_ty]. Every type inferred for [tFix iv_mfix 0] is [iv_fix_ty], which is
    not [bdf_wrap _ iv_fix_ty], and one reduction step takes [bdf_wrap _ iv_fix_ty] to it
    ([bdf_fix_wrap_nondeg]): the cumulativity this instance returns relates two different
    types. A fixpoint whose declared type fails [check_one_fix] is the row
    [typing_inferingE_Fix_beta_inst] ([bdf_fix_dβ_nondeg]).
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_fix_wrap_nondeg
    TARGET BDFromPCUICEta.typing_inferingE *)
Definition typing_inferingE_Fix_inst :=
  typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE)
    (T := bdf_wrap (Sort.sort_of_product sProp sProp) iv_fix_ty) bdf_fix_wrapped.

(** [bdf_fix_dβ] ([bdf_fmfix]): [check_one_fix] fails at the declared type
    [bdf_fxty 0 = Π x : (λ B. I B) A. I A], passes at [Π x : I A. I A], and [bdf_fxty 0]
    reduces to [Π x : I A. I A]. *)
Lemma bdf_fix_dβ_nondeg :
  [× map check_one_fix bdf_fmfix = [None],
     check_one_fix (def_with_type bdf_fix_dβ
       (tProd si_na (tApp (tInd si_ind []) (tRel 0)) (tApp (tInd si_ind []) (tRel 1)))) = Some si_kn &
     red si_Σ bd_Γ1 (bdf_fxty 0) (tProd si_na (tApp (tInd si_ind []) (tRel 0)) (tApp (tInd si_ind []) (tRel 1)))].
Proof.
  split; [reflexivity|reflexivity|].
  apply rt_step. apply prod_red_l. exact (red_beta _ _ si_na si_P (tApp (tInd si_ind []) (tRel 0)) (tRel 0)).
Qed.

(** Fix_beta: completeness on [bdf_fix_typed] ([tFix bdf_fmfix 0] at its declared type
    [bdf_fxty 0]). [check_one_fix] fails at that declared type, passes at [Π x : I A. I A],
    and [bdf_fxty 0] reduces to [Π x : I A. I A] ([bdf_fix_dβ_nondeg]).
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_fix_dβ_nondeg
    TARGET BDFromPCUICEta.typing_inferingE *)
Definition typing_inferingE_Fix_beta_inst := typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) bdf_fix_typed.

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_fix_dβ_nondeg
    TARGET BDFromPCUICEta.wf_fixpointE_wf_fixpoint_red *)
Lemma wf_fixpointE_wf_fixpoint_red_typed_inst : wf_fixpoint_red si_Σ bd_Γ1 bdf_fmfix.
Proof.
  exact (wf_fixpointE_wf_fixpoint_red (Σ := si_Σ) (wfΣ := si_wfE) (mfix := bdf_fmfix) bd_wfE_Γ1
           (@All_cons _ _ bdf_fix_dβ _ (has_sort_isTypeE _ (bdf_fxty_typed bd_Γ1 0 bd_wfE_Γ1 eq_refl)) All_nil)
           bdf_wf_fix).
Qed.

(** Every type inferred for [land] ([tConst po_land_kn []]) in [Σ_po] is [po_land_ty], which is
    not [bdf_wrap _ po_land_ty]; one reduction step takes [bdf_wrap _ po_land_ty] to it. *)
Lemma bdf_const_wrap_nondeg :
  forall T', Σ_po ;;; [] |-E tConst po_land_kn [] ▹ T' ->
    [× T' = po_land_ty,
       T' <> bdf_wrap (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0))
               po_land_ty &
       red1 Σ_po [] (bdf_wrap (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0))
                       po_land_ty) T'].
Proof.
  intros T' h.
  assert (e : T' = po_land_ty).
  { inversion h; subst.
    match goal with hd : declared_constant _ _ _ |- _ =>
      pose proof (PCUICGlobalEnv.declared_constant_inj _ _
                    (declared_constant_to_gen (wfΣ := fst iv_po_wf_ext) hd)
                    (declared_constant_to_gen (wfΣ := fst iv_po_wf_ext) Σ_po_declared_land)) as e1;
      subst end.
    reflexivity. }
  subst T'. split; [reflexivity|exact (fun e => bdf_wrap_nondeg _ _ (eq_sym e))|apply bdf_wrap_red1].
Qed.

(** Const: completeness on [bdf_const_wrapped], [land] at [bdf_wrap _ po_land_ty]
    ([po_land_ty = int → int → int]). Every type inferred for [land] is [po_land_ty], which is
    not [bdf_wrap _ po_land_ty], and one reduction step takes [bdf_wrap _ po_land_ty] to it
    ([bdf_const_wrap_nondeg]): the cumulativity this instance returns relates two different
    types.
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_const_wrap_nondeg
    TARGET BDFromPCUICEta.typing_inferingE *)
Definition typing_inferingE_Const_inst :=
  typing_inferingE (Σ := Σ_po) (wfΣ := iv_po_wfE)
    (T := bdf_wrap (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0)) po_land_ty)
    bdf_const_wrapped.

(** Every type inferred for the literal [1] ([tPrim iv_one]) in [Σ_po] is
    [prim_type iv_one po_int_kn], which is not [bdf_wrap _ (prim_type iv_one po_int_kn)]; one
    reduction step takes that β-wrap to it. *)
Lemma bdf_prim_wrap_nondeg :
  forall T', Σ_po ;;; [] |-E tPrim iv_one ▹ T' ->
    [× T' = prim_type iv_one po_int_kn,
       T' <> bdf_wrap Sort.type0 (prim_type iv_one po_int_kn) &
       red1 Σ_po [] (bdf_wrap Sort.type0 (prim_type iv_one po_int_kn)) T'].
Proof.
  intros T' h.
  assert (e : T' = prim_type iv_one po_int_kn).
  { inversion h; subst.
    match goal with hp : primitive_constant _ _ = Some ?k |- _ =>
      assert (hk : Some po_int_kn = Some k) by (rewrite -hp; reflexivity);
      injection hk as hk; subst k end.
    reflexivity. }
  subst T'. split; [reflexivity|exact (fun e => bdf_wrap_nondeg _ _ (eq_sym e))|apply bdf_wrap_red1].
Qed.

(** Prim: completeness on [bdf_prim_wrapped], the literal [1] at [bdf_wrap _ T] with
    [T = prim_type iv_one po_int_kn] ([int]). Every type inferred for [1] is [T], which is not
    [bdf_wrap _ T], and one reduction step takes [bdf_wrap _ T] to [T]
    ([bdf_prim_wrap_nondeg]): the cumulativity this instance returns relates two different
    types.
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_prim_wrap_nondeg
    TARGET BDFromPCUICEta.typing_inferingE *)
Definition typing_inferingE_Prim_inst :=
  typing_inferingE (Σ := Σ_po) (wfΣ := iv_po_wfE)
    (T := bdf_wrap Sort.type0 (prim_type iv_one po_int_kn)) bdf_prim_wrapped.

(** Every type inferred for [r] in [bdf_Γrβ] is not an application of an inductive type. *)
Lemma bdf_rβ_nondeg :
  forall T', iv_Σ ;;; bdf_Γrβ |-E tRel 0 ▹ T' -> forall ind u args, T' <> mkApps (tInd ind u) args.
Proof.
  intros T' h ind u args. inversion h; subst.
  match goal with hn : nth_error _ _ = Some _ |- _ => vm_compute in hn; injection hn as hd; subst end.
  intros e.
  have hdec : decompose_app (mkApps (tInd ind u) args) = (tInd ind u, args) by apply decompose_app_mkApps.
  rewrite -e in hdec. vm_compute in hdec. discriminate hdec.
Qed.

(** Proj: completeness on [bdf_proj_typed] ([r.(f)] in [bdf_Γrβ], whose one declaration types
    [r] at [(λ B. R B) (∀P. P)]). Every type inferred for [r] is not an application of an
    inductive type ([bdf_rβ_nondeg]), so a [▹{R}] judgment on [r] in [bdf_Γrβ] reaches an
    application of [R] by a reduction between two different terms.
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_rβ_nondeg
    TARGET BDFromPCUICEta.typing_inferingE *)
Definition typing_inferingE_Proj_inst := typing_inferingE (Σ := iv_Σ) (wfΣ := iv_wfE) bdf_proj_typed.

(** [bdf_cofix_dβ] ([bdf_cmfix]): [check_one_cofix] fails at the declared type
    [bdf_RFβ = (λ B. R B) (∀P. P)], passes at [iv_RF = R (∀P. P)], and [bdf_RFβ] reduces to
    [iv_RF]. *)
Lemma bdf_cofix_dβ_nondeg :
  [× map check_one_cofix bdf_cmfix = [None],
     check_one_cofix (def_with_type bdf_cofix_dβ iv_RF) = Some iv_kn &
     red iv_Σ iv_Γc bdf_RFβ iv_RF].
Proof. split; [reflexivity|reflexivity|exact (bdf_RFβ_red iv_Γc)]. Qed.

(** CoFix: completeness on [bdf_cofix_typed] ([tCoFix bdf_cmfix 0] at its declared type
    [bdf_RFβ]). [check_one_cofix] fails at that declared type, passes at [iv_RF], and
    [bdf_RFβ] reduces to [iv_RF] ([bdf_cofix_dβ_nondeg]).
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_cofix_dβ_nondeg
    TARGET BDFromPCUICEta.typing_inferingE *)
Definition typing_inferingE_CoFix_inst := typing_inferingE (Σ := iv_Σ) (wfΣ := iv_wfE) bdf_cofix_typed.

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_cofix_dβ_nondeg *)
Lemma wf_cofixpointE_wf_cofixpoint_red_inst : wf_cofixpoint_red iv_Σ iv_Γc bdf_cmfix.
Proof.
  exact (wf_cofixpointE_wf_cofixpoint_red (Σ := iv_Σ) (wfΣ := iv_wfE) (mfix := bdf_cmfix) iv_wf_Γc
           (@All_cons _ _ bdf_cofix_dβ _ (has_sort_isTypeE _ (bdf_RFβ_typed iv_Γc iv_wf_Γc)) All_nil)
           bdf_wf_cofix).
Qed.

(** ** The judgment and context lemmas *)

(** The let-judgment [z := bdf_let : Prop] ([bdf_vdef_let_typed]). Every type inferred for its
    body [bdf_let] is not a sort ([bdf_let_nondeg]), so not [Prop]: the check of the body
    against [Prop] in this instance's conclusion compares two different types.
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_let_nondeg *)
Lemma lift_typing_lift_sortingE_inst :
  lift_sorting (checkingE si_Σ []) (infering_sortE si_Σ []) (j_vdef si_na bdf_let si_P).
Proof. exact (lift_typing_lift_sortingE (Σ := si_Σ) si_wfE bdf_vdef_let_typed). Qed.

(** [bdf_let] as a type ([bdf_let_sort_typed]). Every type inferred for [bdf_let] is not a sort
    ([bdf_let_nondeg]), so the [▹□] judgment this instance returns reaches its sort by a
    reduction between two different terms.
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_let_nondeg *)
Lemma isType_infering_sortE_inst : ∑ u', si_Σ ;;; [] |-E bdf_let ▹□ u'.
Proof.
  exact (isType_infering_sortE (Σ := si_Σ) (wfΣ := si_wfE) (has_sort_isTypeE _ bdf_let_sort_typed)).
Qed.

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_let_nondeg *)
Lemma isTypeRel_infering_sortE_inst :
  ∑ u, si_Σ ;;; [] |-E bdf_let ▹□ u × relevance_of_sort u = Relevant.
Proof.
  exact (isTypeRel_infering_sortE si_Σ [] bdf_let Relevant si_wfE
           (iv_vass si_Σ [] si_na bdf_let sProp bdf_let_sort_typed eq_refl)).
Qed.

(** The context [[x : bdf_let]] ([bdf_wf_Γlet]). Every type inferred for its declared type
    [bdf_let] in the empty context is not a sort ([bdf_let_nondeg]), so the [▹□] judgment on
    that declaration reaches its sort by a reduction between two different terms.
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_let_nondeg *)
Lemma wf_local_wf_local_bdE_inst : wf_local_bdE si_Σ bdf_Γlet.
Proof. exact (wf_local_wf_local_bdE (Σ := si_Σ) si_wfE bdf_wf_Γlet). Qed.

(** [[x : bdf_let]] over [bd_ΓFG] ([bdf_wf_ΓFGlet]). Every type inferred for [bdf_let] in
    [bd_ΓFG] is not a sort ([bdf_let_FG_nondeg]), so the [▹□] judgment on that declaration
    reaches its sort by a reduction between two different terms.
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_let_FG_nondeg *)
Lemma wf_local_rel_wf_local_bdE_inst : wf_local_bd_relE si_Σ bd_ΓFG [vass si_na bdf_let].
Proof.
  exact (wf_local_rel_wf_local_bdE (Σ := si_Σ) si_wfE
           (wf_local_local_relE si_Σ bd_ΓFG [vass si_na bdf_let] bdf_wf_ΓFGlet)).
Qed.

(** The parameter instance [[x]] against [[_ : ∀P:Prop. P]] in [bdf_Γz] ([bdf_ctx_inst_z]).
    Every type inferred for [x] is not a product ([bdf_z_nondeg]), so not [∀P:Prop. P]: the
    check of [x] against [∀P:Prop. P] in this instance's conclusion compares two different
    types.
    INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_z_nondeg *)
Lemma ctx_inst_typing_bdE_inst :
  PCUICTyping.ctx_inst (checkingE si_Σ) bdf_Γz [tRel 0] [vass si_na iv_False].
Proof. exact (ctx_inst_typing_bdE si_Σ bdf_Γz [tRel 0] [vass si_na iv_False] si_wfE bdf_ctx_inst_z). Qed.

(** [conv_lift_judgmentE] on the let-judgment [z := bdf_let : Prop]: the check of the body is
    [typing_checkingE] of [bdf_let_sort_typed]; the sort of [Prop] is [typing_infering_sortE] of
    [Prop : Type@{1}].
    INSTANCE IMPOSSIBLE: the target's proof repacks its lift_sorting premise (lift_sorting_ex_it_impl_gen keeps the term check and the infering_sortE judgment of the sort witness) and gets the relevance by geq_relevance from the premise's leq_sort, so every instance's conclusion is assembled from its own premise and no witness can make it non-degenerate *)
Lemma conv_lift_judgmentE_inst :
  lift_sorting (checkingE si_Σ []) (infering_sortE si_Σ []) (j_decl (mkdecl si_na (Some bdf_let) si_P)).
Proof.
  apply (conv_lift_judgmentE si_Σ [] si_na (Some bdf_let) si_P).
  split; [exact (typing_checkingE (Σ := si_Σ) (wfΣ := si_wfE) bdf_let_sort_typed)|].
  exists (Sort.super sProp).
  split; [exact (typing_infering_sortE (Σ := si_Σ) (wfΣ := si_wfE) (iv_P_typed si_Σ [] localenv_nil))|].
  split; [exact I|exact eq_refl].
Qed.

(** [conv_lift_judgment_univE] on the assumption [x : bdf_let] at the sort [Prop]: the sort
    judgment passed in is [typing_infering_sortE] of [bdf_let_sort_typed].
    INSTANCE IMPOSSIBLE: the target's proof destructs its lift_sorting premise and repacks its term check, its infering_sortE judgment and its leq_sort, with the relevance by geq_relevance, so every instance's conclusion is assembled from its own premise and no witness can make it non-degenerate *)
Lemma conv_lift_judgment_univE_inst :
  ∑ u', lift_sorting (checkingE si_Σ []) (infering_sortE si_Σ [])
          (j_decl_s (mkdecl si_na None bdf_let) (Some u')) × leq_sort si_Σ u' sProp.
Proof.
  apply (conv_lift_judgment_univE si_Σ [] si_na None bdf_let sProp).
  split; [exact tt|].
  exists sProp.
  split; [exact (typing_infering_sortE (Σ := si_Σ) (wfΣ := si_wfE) bdf_let_sort_typed)|].
  split; [reflexivity|exact eq_refl].
Qed.

(** [ws_cumul_ctx_pbE_vass] on [bd_ΓFG ,, x : G (λ y. F y)] and [bd_ΓFG ,, x : G F], whose
    declared types are converted by the η step [bd_case_eta_step] ([eta1_ws_cumul_pbE]).
    [ws_cumul_ctx_pbE] is qualified: its module [PCUICContextConversionEta] is loaded through
    [BDFromPCUICEta], not imported here.
    INSTANCE IMPOSSIBLE: the target's proof is the context constructor on prefix reflexivity (ws_cumul_ctx_pbE_refl of the closed prefix) and the declaration constructor on its own premises (the binder annotation and the conversion of the two declared types), so every instance's conclusion only packs its premises and no witness can make it non-degenerate *)
Lemma ws_cumul_ctx_pbE_vass_inst :
  PCUICContextConversionEta.ws_cumul_ctx_pbE Conv si_Σ (bd_ΓFG ,, vass si_na bd_X) (bd_ΓFG ,, vass si_na bd_GF).
Proof.
  exact (ws_cumul_ctx_pbE_vass (Σ := si_Σ) (Γ := bd_ΓFG) (na := si_na) (na' := si_na)
           (A := bd_X) (A' := bd_GF) eq_refl eq_refl
           (eta1_ws_cumul_pbE (Σ := si_Σ) (pb := Conv) (Γ := bd_ΓFG) (t := bd_X) (u := bd_GF)
              eq_refl eq_refl bd_case_eta_step)).
Qed.

(** ** The checker's [T6BDc_facts], at concrete arguments *)

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_eta_nondeg *)
Lemma T6BDc_typing_infering_fit_inst :
  ∑ T', si_Σ ;;; bd_Γη |-E tRel 0 ▹ T' × si_Σ ;;; bd_Γη ⊢E T' ≤ tApp (tRel 2) (tRel 1).
Proof. exact (T6BDc_typing_infering_fit (Σ := si_Σ) (wfΣ := si_wfE) bdf_eta_typed). Qed.

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_eta_nondeg *)
Lemma T6BDc_typing_checking_fit_inst : si_Σ ;;; bd_Γη |-E tRel 0 ◃ tApp (tRel 2) (tRel 1).
Proof. exact (T6BDc_typing_checking_fit (Σ := si_Σ) (wfΣ := si_wfE) bdf_eta_typed). Qed.

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_let_nondeg *)
Lemma T6BDc_typing_infering_sort_fit_inst :
  ∑ u', si_Σ ;;; [] |-E bdf_let ▹□ u' × leq_sort si_Σ u' sProp.
Proof. exact (T6BDc_typing_infering_sort_fit (Σ := si_Σ) (wfΣ := si_wfE) bdf_let_sort_typed). Qed.

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_let_nondeg *)
Lemma T6BDc_lift_typing_lift_sorting_fit_inst :
  lift_sorting (checkingE si_Σ []) (infering_sortE si_Σ []) (j_vdef si_na bdf_let si_P).
Proof. exact (T6BDc_lift_typing_lift_sorting_fit (Σ := si_Σ) si_wfE bdf_vdef_let_typed). Qed.

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_z_nondeg *)
Lemma T6BDc_ctx_inst_typing_bd_fit_inst :
  PCUICTyping.ctx_inst (checkingE si_Σ) bdf_Γz [tRel 0] [vass si_na iv_False].
Proof.
  exact (T6BDc_ctx_inst_typing_bd_fit si_Σ bdf_Γz [tRel 0] [vass si_na iv_False] si_wfE bdf_ctx_inst_z).
Qed.

(** INSTANCE NONDEGEN BDFromPCUICEtaInstances.bdf_let_FG_nondeg *)
Lemma T6BDc_wf_local_rel_wf_local_bd_fit_inst : wf_local_bd_relE si_Σ bd_ΓFG [vass si_na bdf_let].
Proof.
  exact (T6BDc_wf_local_rel_wf_local_bd_fit (Σ := si_Σ) si_wfE
           (wf_local_local_relE si_Σ bd_ΓFG [vass si_na bdf_let] bdf_wf_ΓFGlet)).
Qed.

End BDFromPCUICEtaInstances.

(** ** Assumptions: base's main theorems, then their E copies *)

Print Assumptions BDFromPCUIC.bidirectional_from_pcuic.
Print Assumptions bidirectional_from_pcuicE.
Print Assumptions BDFromPCUIC.typing_infering.
Print Assumptions typing_inferingE.
Print Assumptions BDFromPCUIC.typing_checking.
Print Assumptions typing_checkingE.
Print Assumptions BDFromPCUIC.typing_infering_sort.
Print Assumptions typing_infering_sortE.
Print Assumptions BDFromPCUIC.lift_typing_lift_sorting.
Print Assumptions lift_typing_lift_sortingE.
Print Assumptions BDFromPCUIC.ctx_inst_typing_bd.
Print Assumptions ctx_inst_typing_bdE.
Print Assumptions BDFromPCUIC.wf_local_rel_wf_local_bd.
Print Assumptions wf_local_rel_wf_local_bdE.
Print Assumptions PCUICFixWitness.mfix_on_ind_conv_red.
Print Assumptions mfix_on_ind_conv_redE_fix.
Print Assumptions mfix_on_ind_conv_redE_cofix.
Print Assumptions wf_fixpointE_wf_fixpoint_red.
Print Assumptions wf_cofixpointE_wf_cofixpoint_red.
Print Assumptions T6BDc_typing_infering_fit.
Print Assumptions T8_Ind_r_plug_fit.
Print Assumptions typing_inferingE_eta_inst.
Print Assumptions typing_infer_indE_beta_inst.
Print Assumptions wf_fixpointE_wf_fixpoint_red_inst.
Print Assumptions typing_inferingE_CoFix_inst.
Print Assumptions typing_inferingE_Proj_inst.
Print Assumptions wf_cofixpointE_wf_cofixpoint_red_inst.
Print Assumptions typing_inferingE_Fix_beta_inst.
About typing_inferingE.
