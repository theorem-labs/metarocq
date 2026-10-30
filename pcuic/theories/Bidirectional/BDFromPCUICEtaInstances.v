(* Distributed under the terms of the MIT license. *)

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

  **Non-degeneracy.** Each instance applies a lemma to a typing derivation that is not empty,
  and where the lemma's content is a comparison, the compared objects differ:
  - through an η conversion: [bdf_eta_typed] is [x : G (λ y : Prop. F y) ⊢ x : G F], typed by
    [typeE_Cumul] whose [cumulSpecE] premise is the η step [λ y. F y ⇝η F] under [G]
    ([JoinE_ws_cumul_pbE_inst]). [typing_inferingE_eta_inst], [typing_checkingE_eta_inst],
    [bidirectional_from_pcuicE_inst] and the fits [T6BDc_typing_infering_fit_inst],
    [T6BDc_typing_checking_fit_inst] run completeness's Cumul case on it: the inferred type
    [lift0 1 (G (λ y. F y))] is related to [G F] by that η step;
  - through a T8 site, each with an inferred type that is NOT the head form, so each runs the
    proved T8 theorem ([T8_Sort_r_plug], [T8_Prod_r_plug], [T8_Ind_r_plug]: row B1's
    [PCUICEtaT8Probe.T8_*_r]) on a real reduction:
    [Sort_r]: [typing_infering_sortE_let_inst] (and [T6BDc_typing_infering_sort_fit_inst]) on
    [let z : Prop := ∀P. P in z : Prop], whose inferred type is the let-in
    [let z := ∀P. P in Prop], reduced to [Prop] by zeta; [Prod_r]:
    [typing_infer_prodE_let_inst] on [x : z, z := ∀P. P ⊢ x : ∀P:Prop. P], whose inferred type
    is the variable [z], reduced to the product by unfolding the let; [Ind_r]:
    [typing_infer_indE_beta_inst] on [x : (λ B : Prop. I B) A, A : Prop ⊢ x : I A], whose
    inferred type is the β-redex;
  - the (co)fixpoint witness, at a declared type on which the check FAILS
    ([bd_check_fix_dtype]; [bdf_check_cofix_dtype], [bdf_check_cofix_dtypeβ]) and a β-reduct
    on which it passes: [wf_fixpointE_wf_fixpoint_red_inst], [mfix_on_ind_conv_redE_fix_inst],
    [mfix_body_on_conv_redE_fix_inst], [red_fix_witnessE_inst] (the domain [(λ B. I B) A]);
    [mfix_body_on_conv_redE_cofix_inst], [mfix_on_ind_conv_redE_cofix_inst],
    [red_cofix_witnessE_inst] (the type [(λ B. I B) A] itself);
    [wf_cofixpointE_wf_cofixpoint_red_inst] and [typing_inferingE_CoFix_inst] (the typed
    cofixpoint [bdf_cofix_typed] of [iv_Σ], a [CoFinite] record [R], whose declared type is
    the β-redex [(λ B : Prop. R B) (∀P. P)]: completeness's CoFix case runs the witness lemma
    on it);
  - completeness per typing rule: [typing_inferingE_<rule>_inst] for Rel, Sort, Prod, Lambda,
    LetIn, App, Const, Ind, Construct, Case (a [match] whose branch type is a β-redex), Proj
    (through copy 18a's [projection_cumulative_indicesE]), Fix, CoFix and Prim, plus the
    context lemmas on contexts with a let ([bdf_Γz]) or three declarations.

  **Rows not inhabited.** None: every lemma of [BDFromPCUICEta] has an instance here, or is a
  helper that one of these instances runs ([T8_Sort_r_plug], [T8_Prod_r_plug],
  [T8_Ind_r_plug], [conv_lift_judgmentE], [conv_lift_judgment_univE],
  [ws_cumul_ctx_pbE_vass], [is_closed_projection_contextE],
  [untyped_subslet_projection_contextE], the syntactic helpers). Degenerate points: the Fix
  row [typing_inferingE_Fix_inst] ([iv_fix_typed]) has a witness equal to its declared type;
  the non-degenerate Fix row is [typing_inferingE_Fix_beta_inst] (the typed fixpoint
  [bdf_fix_typed], whose recursive argument's domain is the β-redex [(λ B. I B) A], so
  [check_one_fix] fails on the declared type, [bdf_check_fix_dtypeβ], and completeness's Fix
  case reduces it to [I A] through the witness lemma); the Ind and Construct rows compare a
  type with itself.

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
From MetaRocq.PCUIC Require BDFromPCUIC PCUICFixWitness.
From Equations.Type Require Import Relation.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

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

Section BDFromPCUICEtaInstances.

(** ** Through an η conversion *)

Lemma typing_inferingE_eta_inst :
  ∑ T', si_Σ ;;; bd_Γη |-E tRel 0 ▹ T' × si_Σ ;;; bd_Γη ⊢E T' ≤ tApp (tRel 2) (tRel 1).
Proof. exact (typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) bdf_eta_typed). Qed.

Lemma typing_checkingE_eta_inst : si_Σ ;;; bd_Γη |-E tRel 0 ◃ tApp (tRel 2) (tRel 1).
Proof. exact (typing_checkingE (Σ := si_Σ) (wfΣ := si_wfE) bdf_eta_typed). Qed.

Lemma bidirectional_from_pcuicE_inst :
  {T' & si_Σ ;;; bd_Γη |-E tRel 0 ▹ T' × si_Σ ;;; bd_Γη ⊢E T' ≤ tApp (tRel 2) (tRel 1)}.
Proof. exact (env_propE_typing bidirectional_from_pcuicE si_Σ si_wfE _ _ _ bdf_eta_typed). Qed.

Lemma conv_checkE_eta_inst : si_Σ ;;; bd_Γη |-E tRel 0 ◃ tApp (tRel 2) (tRel 1).
Proof. exact (conv_checkE si_Σ si_wfE _ _ _ typing_inferingE_eta_inst). Qed.

(** ** Through the T8 sites, at inferred types that are not head forms *)

(** [Sort_r]: the inferred type [let z := ∀P. P in Prop] reduces to [Prop]. *)
Lemma typing_infering_sortE_let_inst :
  ∑ u', si_Σ ;;; [] |-E bdf_let ▹□ u' × leq_sort si_Σ u' sProp.
Proof. exact (typing_infering_sortE (Σ := si_Σ) (wfΣ := si_wfE) bdf_let_sort_typed). Qed.

Lemma conv_infer_sortE_let_inst :
  {s' & si_Σ ;;; [] |-E bdf_let ▹□ s' × leq_sort si_Σ s' sProp}.
Proof.
  exact (conv_infer_sortE si_Σ si_wfE [] bdf_let sProp bdf_let_sort_typed
           (typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) bdf_let_sort_typed)).
Qed.

(** [Prod_r]: the inferred type [z] reduces to [∀P:Prop. P] by unfolding the let. *)
Lemma typing_infer_prodE_let_inst :
  ∑ na' A' B', [× si_Σ ;;; bdf_Γz |-E tRel 0 ▹Π (na',A',B'),
    eq_binder_annot si_na na', si_Σ ;;; bdf_Γz ⊢E A' = si_P &
    si_Σ ;;; bdf_Γz ,, vass si_na si_P ⊢E B' ≤ tRel 0].
Proof. exact (typing_infer_prodE (Σ := si_Σ) (wfΣ := si_wfE) bdf_x_prod_typed). Qed.

(** [Ind_r]: the inferred type [(λ B. I B) A] reduces to [I A] by β; the universe clause is
    at the full arity of [I] ([isTypeE_mkApps_Ind_head_arity]). *)
Lemma typing_infer_indE_beta_inst :
  ∑ ui' args', [× si_Σ ;;; bdf_Γβ |-E tRel 0 ▹{si_ind} (ui',args'),
      cmp_ind_universes si_Σ si_ind #|[tRel 1]| ui' []
      & ws_cumul_pbE_terms si_Σ bdf_Γβ args' [tRel 1]].
Proof. exact (typing_infer_indE si_Σ si_wfE _ _ _ _ _ bdf_x_ind_typed). Qed.

Lemma isTypeE_mkApps_Ind_head_arity_inst : head_arity si_Σ.1 (IndRef si_ind) <= #|[tRel 1]|.
Proof.
  exact (isTypeE_mkApps_Ind_head_arity (Σ := si_Σ) (wfΣ := si_wfE) bdf_wfβ
           (validityE (Σ := si_Σ) (wfΣ := si_wfE) bdf_x_ind_typed)).
Qed.

(** ** The (co)fixpoint witness, at declared types on which the check fails *)

Lemma red_fix_witnessE_inst :
  ∑ Δ na u' l' B,
    [× red si_Σ bd_Γ1 bd_fix_dtype (it_mkProd_or_LetIn (vass na (mkApps (tInd si_ind u') l') :: Δ) B),
       assumption_context Δ & #|Δ| = 0].
Proof.
  exact (red_fix_witnessE (Σ := si_Σ) (wfΣ := si_wfE) [vass si_na (mkApps (tInd si_ind []) [tRel 0])]
           0 (vass si_na (mkApps (tInd si_ind []) [tRel 0])) bd_Γ1 bd_fix_dtype si_P si_ind [] [tRel 0]
           bd_fix_dtype_isTypeE bdf_fix_dtype_ws eq_refl eq_refl).
Qed.

Lemma mfix_body_on_conv_redE_fix_inst : mfix_body_on check_one_fix (red si_Σ bd_Γ1) si_kn bd_fix_d.
Proof.
  exact (mfix_body_on_conv_redE_fix (Σ := si_Σ) (wfΣ := si_wfE) (d := bd_fix_d) bd_wfE_Γ1 bd_fix_dtype_isTypeE
           bdf_fix_witness).
Qed.

Lemma mfix_on_ind_conv_redE_fix_inst :
  mfix_on_ind check_one_fix (red si_Σ bd_Γ1)
    (fun mind => check_recursivity_kind (lookup_env si_Σ) mind Finite) bd_mfix.
Proof.
  exact (mfix_on_ind_conv_redE_fix (Σ := si_Σ) (wfΣ := si_wfE) (mfix := bd_mfix) bd_wfE_Γ1
           (@All_cons _ _ bd_fix_d _ bd_fix_dtype_isTypeE All_nil) bd_mfix_on_ind_red_convE_inst).
Qed.

Lemma wf_fixpointE_wf_fixpoint_red_inst : wf_fixpoint_red si_Σ bd_Γ1 bd_mfix.
Proof.
  exact (wf_fixpointE_wf_fixpoint_red (Σ := si_Σ) (wfΣ := si_wfE) (mfix := bd_mfix) bd_wfE_Γ1
           (@All_cons _ _ bd_fix_d _ bd_fix_dtype_isTypeE All_nil) wf_fixpoint_red_wf_fixpointE_inst).
Qed.

Lemma red_cofix_witnessE_inst :
  ∑ Δ u' l', red si_Σ bd_Γ1 bd_fix_dom (it_mkProd_or_LetIn Δ (mkApps (tInd si_ind u') l')).
Proof.
  exact (red_cofix_witnessE (Σ := si_Σ) (wfΣ := si_wfE) [] bd_Γ1 bd_fix_dom si_ind [] [tRel 0]
           (has_sort_isTypeE _ bd_fix_dom_typedE) bdf_cofix_dom_ws).
Qed.

Lemma mfix_body_on_conv_redE_cofix_inst :
  mfix_body_on check_one_cofix (red si_Σ bd_Γ1) si_kn bdf_cofix_d.
Proof.
  exact (mfix_body_on_conv_redE_cofix (Σ := si_Σ) (wfΣ := si_wfE) (d := bdf_cofix_d) bd_wfE_Γ1
           (has_sort_isTypeE _ bd_fix_dom_typedE) bdf_cofix_witness).
Qed.

Lemma mfix_on_ind_conv_redE_cofix_inst :
  mfix_on_ind check_one_cofix (red si_Σ bd_Γ1) (fun _ => true) [bdf_cofix_d].
Proof.
  refine (mfix_on_ind_conv_redE_cofix (Σ := si_Σ) (wfΣ := si_wfE) (mfix := [bdf_cofix_d]) bd_wfE_Γ1
            (@All_cons _ _ bdf_cofix_d _ (has_sort_isTypeE _ bd_fix_dom_typedE) All_nil) _).
  exists si_kn. split; [discriminate|]. split; [|reflexivity].
  exact (All_cons bdf_cofix_witness All_nil).
Qed.

(** ** Completeness per typing rule *)

Definition typing_inferingE_Rel_inst := typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) iv_x_typed.
Definition typing_inferingE_Sort_inst := typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) (iv_P_typed si_Σ [] localenv_nil).
Definition typing_inferingE_Prod_inst := typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) (iv_PP_typed si_Σ [] localenv_nil).
Definition typing_inferingE_Lambda_inst := typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) (iv_id_typed si_Σ [] localenv_nil).
Definition typing_inferingE_LetIn_inst := typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) (iv_let_typed si_Σ [] localenv_nil).
Definition typing_inferingE_App_inst := typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) (iv_app_typed si_Σ [] localenv_nil).
Definition typing_inferingE_Ind_inst := typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) (iv_ind_typed [] localenv_nil).
Definition typing_inferingE_Construct_inst := typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) (iv_cstr_typed [] localenv_nil).
Definition typing_inferingE_Case_inst := typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) iv_match_typed.
Definition typing_inferingE_Fix_inst := typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) iv_fix_typed.
(** Fix, non-degenerate: the declared type fails [check_one_fix]; completeness's Fix case runs
    [wf_fixpointE_wf_fixpoint_red] on it. *)
Definition typing_inferingE_Fix_beta_inst := typing_inferingE (Σ := si_Σ) (wfΣ := si_wfE) bdf_fix_typed.

Lemma wf_fixpointE_wf_fixpoint_red_typed_inst : wf_fixpoint_red si_Σ bd_Γ1 bdf_fmfix.
Proof.
  exact (wf_fixpointE_wf_fixpoint_red (Σ := si_Σ) (wfΣ := si_wfE) (mfix := bdf_fmfix) bd_wfE_Γ1
           (@All_cons _ _ bdf_fix_dβ _ (has_sort_isTypeE _ (bdf_fxty_typed bd_Γ1 0 bd_wfE_Γ1 eq_refl)) All_nil)
           bdf_wf_fix).
Qed.
Definition typing_inferingE_Const_inst := typing_inferingE (Σ := Σ_po) (wfΣ := iv_po_wfE) iv_land_typed.
Definition typing_inferingE_Prim_inst := typing_inferingE (Σ := Σ_po) (wfΣ := iv_po_wfE) iv_prim_typed.
Definition typing_inferingE_Proj_inst := typing_inferingE (Σ := iv_Σ) (wfΣ := iv_wfE) iv_proj_typed.
(** CoFix: the declared type is a β-redex; completeness's CoFix case runs
    [wf_cofixpointE_wf_cofixpoint_red] on it. *)
Definition typing_inferingE_CoFix_inst := typing_inferingE (Σ := iv_Σ) (wfΣ := iv_wfE) bdf_cofix_typed.

Lemma wf_cofixpointE_wf_cofixpoint_red_inst : wf_cofixpoint_red iv_Σ iv_Γc bdf_cmfix.
Proof.
  exact (wf_cofixpointE_wf_cofixpoint_red (Σ := iv_Σ) (wfΣ := iv_wfE) (mfix := bdf_cmfix) iv_wf_Γc
           (@All_cons _ _ bdf_cofix_dβ _ (has_sort_isTypeE _ (bdf_RFβ_typed iv_Γc iv_wf_Γc)) All_nil)
           bdf_wf_cofix).
Qed.

(** ** The judgment and context lemmas *)

(** The let-judgment [z := ∀P:Prop. P : Prop]. *)
Lemma lift_typing_lift_sortingE_inst :
  lift_sorting (checkingE si_Σ []) (infering_sortE si_Σ []) (j_vdef si_na iv_False si_P).
Proof. exact (lift_typing_lift_sortingE (Σ := si_Σ) si_wfE (iv_vdef_False si_Σ [] localenv_nil)). Qed.

Lemma isType_infering_sortE_inst : ∑ u', si_Σ ;;; bd_Γ1 |-E bd_fix_dtype ▹□ u'.
Proof. exact (isType_infering_sortE (Σ := si_Σ) (wfΣ := si_wfE) bd_fix_dtype_isTypeE). Qed.

Lemma isTypeRel_infering_sortE_inst :
  ∑ u, si_Σ ;;; bd_Γ1 |-E bd_fix_dom ▹□ u × relevance_of_sort u = Relevant.
Proof.
  exact (isTypeRel_infering_sortE si_Σ bd_Γ1 bd_fix_dom Relevant si_wfE
           (iv_vass si_Σ bd_Γ1 si_na bd_fix_dom sProp bd_fix_dom_typedE eq_refl)).
Qed.

Lemma wf_local_wf_local_bdE_inst : wf_local_bdE si_Σ bdf_Γz.
Proof. exact (wf_local_wf_local_bdE (Σ := si_Σ) si_wfE bdi_wf_subst1_prem). Qed.

Lemma wf_local_rel_wf_local_bdE_inst : wf_local_bd_relE si_Σ bd_ΓFG [vass si_na bd_X].
Proof.
  exact (wf_local_rel_wf_local_bdE (Σ := si_Σ) si_wfE
           (wf_local_local_relE si_Σ bd_ΓFG [vass si_na bd_X] bdi_wfη)).
Qed.

Lemma ctx_inst_typing_bdE_inst : PCUICTyping.ctx_inst (checkingE si_Σ) iv_Γ1 [tRel 0] [vass si_na si_P].
Proof. exact (ctx_inst_typing_bdE si_Σ iv_Γ1 [tRel 0] [vass si_na si_P] si_wfE iv_ctx_inst). Qed.

(** ** The checker's [T6BDc_facts], at concrete arguments *)

Lemma T6BDc_typing_infering_fit_inst :
  ∑ T', si_Σ ;;; bd_Γη |-E tRel 0 ▹ T' × si_Σ ;;; bd_Γη ⊢E T' ≤ tApp (tRel 2) (tRel 1).
Proof. exact (T6BDc_typing_infering_fit (Σ := si_Σ) (wfΣ := si_wfE) bdf_eta_typed). Qed.

Lemma T6BDc_typing_checking_fit_inst : si_Σ ;;; bd_Γη |-E tRel 0 ◃ tApp (tRel 2) (tRel 1).
Proof. exact (T6BDc_typing_checking_fit (Σ := si_Σ) (wfΣ := si_wfE) bdf_eta_typed). Qed.

Lemma T6BDc_typing_infering_sort_fit_inst :
  ∑ u', si_Σ ;;; [] |-E bdf_let ▹□ u' × leq_sort si_Σ u' sProp.
Proof. exact (T6BDc_typing_infering_sort_fit (Σ := si_Σ) (wfΣ := si_wfE) bdf_let_sort_typed). Qed.

Lemma T6BDc_lift_typing_lift_sorting_fit_inst :
  lift_sorting (checkingE si_Σ []) (infering_sortE si_Σ []) (j_vdef si_na iv_False si_P).
Proof. exact (T6BDc_lift_typing_lift_sorting_fit (Σ := si_Σ) si_wfE (iv_vdef_False si_Σ [] localenv_nil)). Qed.

Lemma T6BDc_ctx_inst_typing_bd_fit_inst :
  PCUICTyping.ctx_inst (checkingE si_Σ) iv_Γ1 [tRel 0] [vass si_na si_P].
Proof. exact (T6BDc_ctx_inst_typing_bd_fit si_Σ iv_Γ1 [tRel 0] [vass si_na si_P] si_wfE iv_ctx_inst). Qed.

Lemma T6BDc_wf_local_rel_wf_local_bd_fit_inst : wf_local_bd_relE si_Σ bd_ΓFG [vass si_na bd_X].
Proof.
  exact (T6BDc_wf_local_rel_wf_local_bd_fit (Σ := si_Σ) si_wfE
           (wf_local_local_relE si_Σ bd_ΓFG [vass si_na bd_X] bdi_wfη)).
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
