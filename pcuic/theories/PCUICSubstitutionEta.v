(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICEquality
     PCUICReduction PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICSubstitution PCUICTypingEta PCUICClosedTypEta PCUICEtaC1b PCUICClosedBodies
     PCUICWellScopedCumulativityEta PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp PCUICTypingEtaNotions.

(** * Substitution over [typingE]: the E copy of [PCUICSubstitution] (in progress)

  This part records the base lemma of [PCUICSubstitution] whose E form is false,
  [wt_cumul_pb_equalityP]: it is not copied, and its refutation stays registered.

  Base [wt_cumul_pb_equalityP] turns a well-typed cumulativity into [cumulP], a
  closure of one-step reductions and [compare_term], which has no η step. Over the
  η relation that is false. Witness, in the empty environment and the context
  [F : Prop → Prop, G : (Prop → Prop) → Prop]: the types [G (λy:Prop. F y)] and
  [G F] are related (one η step in the argument), both are normal ([F] and [G] are
  assumptions), and [compare_term] never relates a λ to a variable. Both have type
  [Prop] over [typingE] ([wc_witness_typed]).

  The only base consumer, [substitution_wt_cumul_pb], is proved over E by another
  route: A7's [substitution_ws_cumul_pbE] with [wt_cumul_pbE_ws_cumul_pbE]. *)

Section EqualityPFalse.

  #[local] Existing Instance default_checker_flags.

  Definition wc_G_ty : term := tProd c1b_na rf_F (tSort sProp).
  Definition wc_Γ : context := [vass c1b_na wc_G_ty; vass c1b_na rf_F].
  Definition wc_eta_F : term := tLambda c1b_na (tSort sProp) (tApp (tRel 2) (tRel 0)).
  Definition wc_T : term := tApp (tRel 0) wc_eta_F.
  Definition wc_U : term := tApp (tRel 0) (tRel 1).

  Lemma wc_Rel_normal Σ (Γ : context) n v :
    option_map decl_body (nth_error Γ n) = Some None -> red1 Σ Γ (tRel n) v -> False.
  Proof.
    intros hn H. inv_red H.
    match goal with e : option_map decl_body _ = Some (Some _) |- _ => rewrite hn in e; discriminate e end.
  Qed.

  Lemma wc_eta_body_normal Σ v : red1 Σ (wc_Γ ,, vass c1b_na (tSort sProp)) (tApp (tRel 2) (tRel 0)) v -> False.
  Proof.
    intros H. inv_red H.
    - exact (wc_Rel_normal _ (wc_Γ ,, vass c1b_na (tSort sProp)) 2 _ eq_refl ltac:(eassumption)).
    - eapply red_normal_Rel0; eassumption.
  Qed.

  Lemma wc_eta_F_normal Σ v : red1 Σ wc_Γ wc_eta_F v -> False.
  Proof.
    apply red_normal_lam; [intros w; apply red_normal_Sort|intros w; apply wc_eta_body_normal].
  Qed.

  Lemma wc_T_normal Σ v : red1 Σ wc_Γ wc_T v -> False.
  Proof.
    intros H. inv_red H.
    - eapply red_normal_Rel0; eassumption.
    - eapply wc_eta_F_normal; eassumption.
  Qed.

  Lemma wc_U_normal Σ v : red1 Σ wc_Γ wc_U v -> False.
  Proof.
    intros H. inv_red H.
    - eapply red_normal_Rel0; eassumption.
    - exact (wc_Rel_normal _ wc_Γ 1 _ eq_refl ltac:(eassumption)).
  Qed.

  Lemma wc_not_compare Σ φ pb : compare_term Σ φ pb wc_T wc_U -> False.
  Proof.
    intros c. depelim c.
    repeat match goal with h : eq_term_upto_univ_napp _ _ _ _ _ _ _ |- _ => depelim h end.
  Qed.

  (** The witness is typable. *)
  Lemma wc_G_ty_typed (Γ : context) : wf_localE rf_Σ Γ ->
    rf_Σ ;;; Γ |-E wc_G_ty :
      tSort (Sort.sort_of_product (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) (Sort.super sProp)).
  Proof.
    intros h. unfold wc_G_ty. apply typeE_Prod.
    - split; [exact tt|]. eexists. split; [exact (rf_F_typed Γ h)|]. split; reflexivity.
    - apply rf_P_typed. apply localenv_cons_abs; [exact h|].
      split; [exact tt|]. eexists. split; [exact (rf_F_typed Γ h)|]. split; [exact I|reflexivity].
  Qed.

  Lemma wc_wf_Γ : wf_localE rf_Σ wc_Γ.
  Proof.
    apply localenv_cons_abs; [exact rf_wf_Γ|].
    split; [exact tt|]. eexists. split; [exact (wc_G_ty_typed rf_Γ rf_wf_Γ)|]. split; [exact I|reflexivity].
  Qed.

  Lemma wc_wf_Γy : wf_localE rf_Σ (wc_Γ ,, vass c1b_na (tSort sProp)).
  Proof. apply localenv_cons_abs; [exact wc_wf_Γ|exact (rf_P_vass wc_Γ wc_wf_Γ)]. Qed.

  Lemma wc_eta_F_typed : rf_Σ ;;; wc_Γ |-E wc_eta_F : rf_F.
  Proof.
    unfold wc_eta_F, rf_F. apply typeE_Lambda; [exact (rf_P_vass wc_Γ wc_wf_Γ)|].
    apply (typeE_App _ _ (tRel 2) c1b_na (tSort sProp) (tSort sProp)
             (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) (tRel 0)).
    - exact (rf_F_typed _ wc_wf_Γy).
    - exact (typeE_Rel _ _ 2 (vass c1b_na rf_F) wc_wf_Γy eq_refl).
    - exact (typeE_Rel _ _ 0 (vass c1b_na (tSort sProp)) wc_wf_Γy eq_refl).
  Qed.

  Lemma wc_app_typed u : rf_Σ ;;; wc_Γ |-E u : rf_F -> rf_Σ ;;; wc_Γ |-E tApp (tRel 0) u : tSort sProp.
  Proof.
    intros hu.
    exact (typeE_App _ _ (tRel 0) c1b_na rf_F (tSort sProp) _ u (wc_G_ty_typed wc_Γ wc_wf_Γ)
             (typeE_Rel _ _ 0 (vass c1b_na wc_G_ty) wc_wf_Γ eq_refl) hu).
  Qed.

  Lemma wc_T_typed : rf_Σ ;;; wc_Γ |-E wc_T : tSort sProp.
  Proof. exact (wc_app_typed _ wc_eta_F_typed). Qed.

  Lemma wc_U_typed : rf_Σ ;;; wc_Γ |-E wc_U : tSort sProp.
  Proof. exact (wc_app_typed _ (typeE_Rel _ _ 1 (vass c1b_na rf_F) wc_wf_Γ eq_refl)). Qed.

  (** In an environment that meets the refuted statement's premise [wf Σ] (and
      [wfE Σ]), [F : Prop → Prop, G : (Prop → Prop) → Prop] is a well-formed
      context, and [G (λy:Prop. F y)] and [G F] both have type [Prop] in it. *)
  Lemma wc_witness_typed :
    [× wf rf_Σ, wfE rf_Σ, wf_localE rf_Σ wc_Γ,
       rf_Σ ;;; wc_Γ |-E wc_T : tSort sProp & rf_Σ ;;; wc_Γ |-E wc_U : tSort sProp].
  Proof.
    split; [exact (@wf_empty_global_env default_checker_flags)
           |exact (wf_incl_E (@wf_empty_global_env default_checker_flags))
           |exact wc_wf_Γ|exact wc_T_typed|exact wc_U_typed].
  Qed.

  Definition wc_wfE : wfE rf_Σ := wf_incl_E (@wf_empty_global_env default_checker_flags).

  Lemma wc_isType (t : term) : rf_Σ ;;; wc_Γ |-E t : tSort sProp -> isTypeE rf_Σ wc_Γ t.
  Proof. intros h. split; [exact tt|]. exists sProp. split; [exact h|]. split; exact I. Qed.

  Lemma wc_spec : rf_Σ ;;; wc_Γ ⊢ wc_T ≤sE[Conv] wc_U.
  Proof.
    unfold wc_T, wc_U. apply cumulE_App; [apply cumulE_Refl|].
    unfold wc_eta_F. apply cumul_eta_l. apply cumulE_Refl.
  Qed.

  Lemma wc_premise : wt_cumul_pbE Conv rf_Σ wc_Γ wc_T wc_U.
  Proof.
    constructor; [exact (wc_isType _ wc_T_typed)|exact (wc_isType _ wc_U_typed)|].
    apply (wsE_join (cf := default_checker_flags)).
    apply (into_ws_cumul_pbE_spec (wfΣ := @wfE_ClosedBodies _ rf_Σ wc_wfE) wc_spec);
      [exact (wf_local_closed_contextE (Σ := rf_Σ) (wfΣ := wc_wfE) wc_wf_Γ)
      |exact (subject_is_open_termE (Σ := rf_Σ) (wfΣ := wc_wfE) wc_T_typed)
      |exact (subject_is_open_termE (Σ := rf_Σ) (wfΣ := wc_wfE) wc_U_typed)].
  Qed.

  Lemma wc_no_cumulP P : cumulP Conv rf_Σ P wc_Γ wc_T wc_U -> False.
  Proof.
    intros H. inversion H; subst.
    - eapply wc_not_compare; eassumption.
    - match goal with h : red1P _ _ _ wc_T _ |- _ => exact (wc_T_normal _ _ (red1P_red1 h)) end.
    - match goal with h : red1P _ _ _ wc_U _ |- _ => exact (wc_U_normal _ _ (red1P_red1 h)) end.
  Qed.

End EqualityPFalse.

(** **Refuted:** base [wt_cumul_pb_equalityP] over [wt_cumul_pbE], even under the
    stronger premise [wf Σ]. *)
Theorem wt_cumul_pbE_equalityP_false_wf :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wf Σ) pb (Γ : context) T U,
     wt_cumul_pbE pb Σ Γ T U -> cumulP pb Σ (closedP #|Γ| xpredT) Γ T U) -> False.
Proof.
  intros H.
  exact (wc_no_cumulP _ (H default_checker_flags rf_Σ (@wf_empty_global_env default_checker_flags)
                           Conv wc_Γ wc_T wc_U wc_premise)).
Qed.

(** **Refuted:** base [wt_cumul_pb_equalityP] with only [wt_cumul_pb] →
    [wt_cumul_pbE] and [wf] → [wfE] (base's section variables explicit). *)
Theorem wt_cumul_pbE_equalityP_false :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wfE Σ) pb (Γ : context) T U,
     wt_cumul_pbE pb Σ Γ T U -> cumulP pb Σ (closedP #|Γ| xpredT) Γ T U) -> False.
Proof.
  intros H. apply wt_cumul_pbE_equalityP_false_wf.
  intros cf Σ wfΣ. exact (H cf Σ (wf_incl_E wfΣ)).
Qed.
