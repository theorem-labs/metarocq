(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the hypotheses of [Typing/PCUICContextConversionTypEta]

  Each lemma of [Typing/PCUICContextConversionTypEta] that has a premise is applied here
  to a concrete case with every premise proved, so the premises are shown to be jointly
  satisfiable. The environment is [si_Σ] ([PCUICCumulativitySpecEtaClosureInstances]:
  [Inductive I (A : Prop) : Prop := c : I A], well formed for [wf] and [wfE]; [si_wfE],
  [si_cb]). The two contexts are

    [c9_ΓA = [x : Prop; h : (Prop → Prop) → Prop; w : h I]] and
    [c9_ΓB = [x : Prop; h : (Prop → Prop) → Prop; w : h (λy:Prop. I y)]],

  both well formed ([c9_wf_ΓA], [c9_wf_ΓB]). They differ by one η-step in the type of
  [w]: [λy:Prop. I y] contracts to [I] ([c9_eta]). Both types are normal, so no
  β-reduction relates them. Every context premise below relates [c9_ΓB] and [c9_ΓA], in
  the cumulative direction by the η-contraction ([c9_cumul_BA]) or as a conversion
  ([c9_conv_AB]). The typing instances move [w], typed at [h I] in [c9_ΓA], to [c9_ΓB],
  where its declared type is [h (λy. I y)], so the conclusion needs the η-conversion. The
  [match] of [cp_match_typed] ([PCUICTypingEtaCopies1Instances]), weakened into [c9_ΓA],
  moves to [c9_ΓB] the same way ([context_cumulativityE_match_inst]).

  [All2_conv_over_reflE] and [All2_cumul_over_reflE] have no premise, so no instance. No
  instance reaches the [tFix]/[tCoFix] cases of [context_cumulativity_propE], because no
  typed fixpoint is built; [mfix_on_ind_context_cumulativityE], which those cases use,
  has its own instance. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICEquality PCUICCases PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICConfluence
     PCUICContextConversion PCUICClosedBodies PCUICTypingEta PCUICTypingEtaInd PCUICClosedTypEta
     PCUICWeakeningTypEta PCUICEtaDefs PCUICEtaI5 PCUICWellScopedCumulativityEta
     PCUICContextConversionEta PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp
     PCUICCumulativitySpecEtaClosureInstances PCUICTypingEtaCopies1Instances
     PCUICContextConversionTypEta.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

(** ** The two contexts *)

Definition c9_PP : term := tProd si_na si_P si_P.
Definition c9_H : term := tProd si_na c9_PP si_P.
Definition c9_I : term := tInd si_ind [].
(** [h I] and [h (λy:Prop. I y)], with [h] the variable [k]. *)
Definition c9_Ak (k : nat) : term := tApp (tRel k) c9_I.
Definition c9_Bk (k : nat) : term := tApp (tRel k) (sp_eta c9_I).
Definition c9_Γh : context := cp_Γ1 ,, vass si_na c9_H.
Definition c9_ΓA : context := c9_Γh ,, vass si_na (c9_Ak 0).
Definition c9_ΓB : context := c9_Γh ,, vass si_na (c9_Bk 0).

Definition c9_sPP : sort := Sort.sort_of_product (Sort.super sProp) (Sort.super sProp).

(** [Prop → Prop] and [(Prop → Prop) → Prop] are types. *)
Lemma c9_PP_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E c9_PP : tSort c9_sPP.
Proof. exact (cp_arity_typedE Γ). Qed.

Lemma c9_H_typed (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ |-E c9_H : tSort (Sort.sort_of_product c9_sPP (Sort.super sProp)).
Proof.
  intros h. apply typeE_Prod.
  - exact (cp_vass_s Γ si_na c9_PP _ (c9_PP_typed Γ h) eq_refl).
  - apply cp_P_typed. apply localenv_cons_abs; [exact h|].
    exact (cp_vass Γ si_na c9_PP _ (c9_PP_typed Γ h) eq_refl).
Qed.

Lemma c9_wf_Γh : wf_localE si_Σ c9_Γh.
Proof.
  apply localenv_cons_abs; [exact cp_wf_Γ1|].
  exact (cp_vass cp_Γ1 si_na c9_H _ (c9_H_typed cp_Γ1 cp_wf_Γ1) eq_refl).
Qed.

Lemma c9_h_typed (Γ : context) k : wf_localE si_Σ Γ -> nth_error Γ k = Some (vass si_na c9_H) ->
  si_Σ ;;; Γ |-E tRel k : c9_H.
Proof. intros h hk. exact (typeE_Rel _ _ k _ h hk). Qed.

(** [λy:Prop. I y : Prop → Prop]. *)
Lemma c9_eta_I_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E sp_eta c9_I : c9_PP.
Proof.
  intros h. unfold sp_eta, c9_PP. apply typeE_Lambda.
  - exact (cp_vass Γ si_na si_P _ (cp_P_typed Γ h) eq_refl).
  - exact (cp_Ix_typed _ 0 (cp_wf_P Γ h) (cp_rel_P _ 0 (vass si_na si_P) (cp_wf_P Γ h) eq_refl eq_refl)).
Qed.

Lemma c9_A_typed (Γ : context) k : wf_localE si_Σ Γ -> nth_error Γ k = Some (vass si_na c9_H) ->
  si_Σ ;;; Γ |-E c9_Ak k : tSort sProp.
Proof.
  intros h hk.
  exact (typeE_App _ _ (tRel k) si_na c9_PP si_P _ c9_I (c9_H_typed Γ h) (c9_h_typed Γ k h hk)
           (cp_ind_typed Γ h)).
Qed.

Lemma c9_B_typed (Γ : context) k : wf_localE si_Σ Γ -> nth_error Γ k = Some (vass si_na c9_H) ->
  si_Σ ;;; Γ |-E c9_Bk k : tSort sProp.
Proof.
  intros h hk.
  exact (typeE_App _ _ (tRel k) si_na c9_PP si_P _ (sp_eta c9_I) (c9_H_typed Γ h) (c9_h_typed Γ k h hk)
           (c9_eta_I_typed Γ h)).
Qed.

Lemma c9_wf_ΓA : wf_localE si_Σ c9_ΓA.
Proof.
  apply localenv_cons_abs; [exact c9_wf_Γh|].
  exact (cp_vass c9_Γh si_na (c9_Ak 0) sProp (c9_A_typed c9_Γh 0 c9_wf_Γh eq_refl) eq_refl).
Qed.

Lemma c9_wf_ΓB : wf_localE si_Σ c9_ΓB.
Proof.
  apply localenv_cons_abs; [exact c9_wf_Γh|].
  exact (cp_vass c9_Γh si_na (c9_Bk 0) sProp (c9_B_typed c9_Γh 0 c9_wf_Γh eq_refl) eq_refl).
Qed.

(** The η-step: [h (λy. I y)] contracts to [h I]. *)
Lemma c9_eta k : eta1 (c9_Bk k) (c9_Ak k).
Proof. exact (app_eta_r _ _ (tRel k) (eta_red si_na c9_I si_P)). Qed.

Lemma c9_cumul_Γh : cumul_context (@JoinE _) si_Σ c9_Γh c9_Γh.
Proof. eapply All2_fold_refl. intros ? ?. apply cumul_decls_reflE. Qed.

(** [c9_ΓB ≤ c9_ΓA], by the η-contraction. *)
Lemma c9_cumul_BA : cumul_context (@JoinE _) si_Σ c9_ΓB c9_ΓA.
Proof.
  constructor; [exact c9_cumul_Γh|]. constructor; [reflexivity|].
  exact (JoinE_eta1_l si_Σ c9_Γh Cumul _ _ (c9_eta 0)).
Qed.

(** [c9_ΓA = c9_ΓB], by the η-expansion. *)
Lemma c9_conv_AB : conv_context (@JoinE _) si_Σ c9_ΓA c9_ΓB.
Proof.
  constructor.
  - eapply All2_fold_refl. intros ? [na [b|] ty]; constructor; try reflexivity; apply JoinE_refl.
  - constructor; [reflexivity|]. exact (JoinE_eta1_r si_Σ c9_Γh Conv _ _ (c9_eta 0)).
Qed.

(** [w : h I] in [c9_ΓA]. *)
Lemma c9_w_typed : si_Σ ;;; c9_ΓA |-E tRel 0 : lift0 1 (c9_Ak 0).
Proof. exact (typeE_Rel _ _ 0 (vass si_na (c9_Ak 0)) c9_wf_ΓA eq_refl). Qed.

(** ** Instances *)

(** [h (λy. I y) ≤ h I] in [c9_Γh], then weakened by [w : h I]. *)
Lemma c9_spec_BA : cumulSpecE si_Σ c9_Γh (c9_Bk 0) (c9_Ak 0).
Proof.
  unfold cumulSpecE, c9_Bk, c9_Ak, sp_eta.
  apply cumulE_App; [apply cumulE_Refl|apply cumulSpecE_eta_contract].
Qed.

Lemma weakening_cumulSpec0E_inst : cumulSpecE si_Σ c9_ΓA (lift0 1 (c9_Bk 0)) (lift0 1 (c9_Ak 0)).
Proof.
  exact (weakening_cumulSpec0E (Σ := si_Σ) (wfΣ := si_wfE) (Γ := exist c9_Γh eq_refl)
           (Γ'' := exist [vass si_na (c9_Ak 0)] eq_refl)
           (M := exist (c9_Bk 0) eq_refl) (N := exist (c9_Ak 0) eq_refl) 1 eq_refl c9_spec_BA).
Qed.

(** [w : h I] in [c9_ΓA], and [h I ≤ h (λy. I y)] there, by the η-expansion. *)
Lemma wt_cum_ws_cumul_pbE_inst : ws_cumul_pbE Cumul si_Σ c9_ΓA (c9_Ak 1) (c9_Bk 1).
Proof.
  exact (wt_cum_ws_cumul_pbE (Σ := si_Σ) (wfΣ := si_wfE) (t := tRel 0) (s := sProp) c9_w_typed
           (c9_B_typed c9_ΓA 1 c9_wf_ΓA eq_refl) (JoinE_eta1_r si_Σ c9_ΓA Cumul _ _ (c9_eta 1))).
Qed.

Lemma wt_cum_ws_cumul_ctx_pbE_inst : ws_cumul_ctx_pbE Cumul si_Σ c9_ΓB c9_ΓA.
Proof.
  exact (wt_cum_ws_cumul_ctx_pbE (Σ := si_Σ) (wfΣ := si_wfE) Cumul c9_wf_ΓB c9_wf_ΓA c9_cumul_BA).
Qed.

(** [x : Prop] against [x : Type₁]: [compare_term] relates them at [Cumul]
    ([prop_sub_type] holds in [default_checker_flags]). *)
Definition c9_ΓP : context := [vass si_na si_P].
Definition c9_ΓT : context := [vass si_na (tSort Sort.type1)].

Lemma c9_compare_ctx : PCUICContextConversion.compare_context si_Σ Cumul c9_ΓP c9_ΓT.
Proof.
  constructor; [constructor|]. constructor; [reflexivity|]. constructor. cbn. trivial.
Qed.

Lemma eq_context_cumul_SpecE_inst :
  PCUICCumulativitySpec.cumul_pb_context cumulSpecE0 Cumul si_Σ c9_ΓP c9_ΓT.
Proof. exact (eq_context_cumul_SpecE si_Σ Cumul _ _ c9_compare_ctx). Qed.

Lemma eq_context_cumul_Spec_relE_inst : cumul_ctx_rel cumulSpecE0 si_Σ cp_Γ1 c9_ΓP c9_ΓT.
Proof. exact (eq_context_cumul_Spec_relE si_Σ cp_Γ1 _ _ c9_compare_ctx). Qed.

(** The premise [ClosedBodies si_Σ] is [si_cb]. *)
Lemma cumul_context_Algo_SpecE_inst :
  PCUICCumulativitySpec.cumul_pb_context cumulSpecE0 Cumul si_Σ c9_ΓB c9_ΓA.
Proof. exact (cumul_context_Algo_SpecE si_Σ Cumul _ _ wt_cum_ws_cumul_ctx_pbE_inst). Qed.

(** A cofixpoint block over [c9_ΓA] whose declared type [(λy:Prop. I y) x] mentions the
    context's variable [x]; its witness for [check_one_cofix] is [I x], by an η-contraction.
    The block moves to [c9_ΓB]. *)
Definition c9_dtype : term := tApp (sp_eta c9_I) (tRel 2).
Definition c9_witness : term := tApp c9_I (tRel 2).
Definition c9_block : mfixpoint term :=
  [{| dname := si_na; dtype := c9_dtype; dbody := tRel 0; rarg := 0 |}].

Lemma c9_block_on_ind : mfix_on_ind check_one_cofix (conv_witnessE si_Σ c9_ΓA) (fun _ => true) c9_block.
Proof.
  exists si_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [|constructor].
  exists c9_witness. split; [reflexivity|]. split; [reflexivity|].
  apply cumulE_App; [apply cumulSpecE_eta_contract|apply cumulE_Refl].
Qed.

Lemma c9_block_open : All (fun d => is_open_term c9_ΓA (dtype d)) c9_block.
Proof. constructor; [reflexivity|constructor]. Qed.

Lemma mfix_on_ind_context_cumulativityE_inst :
  mfix_on_ind check_one_cofix (conv_witnessE si_Σ c9_ΓB) (fun _ => true) c9_block.
Proof.
  exact (mfix_on_ind_context_cumulativityE (Σ := si_Σ) (wfΣ := si_wfE) c9_wf_ΓA c9_wf_ΓB c9_cumul_BA
           c9_block_open c9_block_on_ind).
Qed.

(** [w], declared [h (λy. I y)] in [c9_ΓB], has the type [h I] it has in [c9_ΓA]. *)
Lemma context_cumulativity_propE_inst : si_Σ ;;; c9_ΓB |-E tRel 0 : lift0 1 (c9_Ak 0).
Proof.
  exact (env_propE_typing context_cumulativity_propE si_Σ si_wfE c9_ΓA _ _ c9_w_typed
           c9_ΓB c9_cumul_BA c9_wf_ΓB).
Qed.

Lemma context_cumulativityE_inst : si_Σ ;;; c9_ΓB |-E tRel 0 : lift0 1 (c9_Ak 0).
Proof.
  exact (context_cumulativityE (Σ := si_Σ) (wfΣ := si_wfE) c9_ΓA c9_w_typed c9_wf_ΓB c9_cumul_BA).
Qed.

Lemma closed_context_cumulativityE_inst : si_Σ ;;; c9_ΓB |-E tRel 0 : lift0 1 (c9_Ak 0).
Proof.
  exact (closed_context_cumulativityE (Σ := si_Σ) (wfΣ := si_wfE) c9_ΓA c9_w_typed c9_wf_ΓB
           wt_cum_ws_cumul_ctx_pbE_inst).
Qed.

Lemma closed_context_cumul_cumulE_inst : cumul_context (@JoinE _) si_Σ c9_ΓB c9_ΓA.
Proof. exact (closed_context_cumul_cumulE (Σ := si_Σ) (wfΣ := si_wfE) wt_cum_ws_cumul_ctx_pbE_inst). Qed.

Lemma wf_conv_context_closedE_inst : ws_cumul_ctx_pbE Conv si_Σ c9_ΓA c9_ΓB.
Proof. exact (wf_conv_context_closedE (Σ := si_Σ) (wfΣ := si_wfE) c9_conv_AB c9_wf_ΓA c9_wf_ΓB). Qed.

Lemma closed_context_conv_convE_inst : conv_context (@JoinE _) si_Σ c9_ΓA c9_ΓB.
Proof. exact (closed_context_conv_convE (Σ := si_Σ) (wfΣ := si_wfE) wf_conv_context_closedE_inst). Qed.

Lemma wf_cumul_context_closedE_inst : ws_cumul_ctx_pbE Cumul si_Σ c9_ΓB c9_ΓA.
Proof. exact (wf_cumul_context_closedE (Σ := si_Σ) (wfΣ := si_wfE) c9_cumul_BA c9_wf_ΓB c9_wf_ΓA). Qed.

Lemma context_conversionE_inst : si_Σ ;;; c9_ΓB |-E tRel 0 : lift0 1 (c9_Ak 0).
Proof.
  exact (context_conversionE (Σ := si_Σ) (wfΣ := si_wfE) c9_ΓA c9_w_typed c9_wf_ΓB c9_conv_AB).
Qed.

Lemma closed_context_conversionE_inst : si_Σ ;;; c9_ΓB |-E tRel 0 : lift0 1 (c9_Ak 0).
Proof.
  exact (closed_context_conversionE (Σ := si_Σ) (wfΣ := si_wfE) c9_ΓA c9_w_typed c9_wf_ΓB
           wf_conv_context_closedE_inst).
Qed.

(** The [match] of [cp_match_typed], typed in [cp_Γ1], weakened into [c9_ΓA] and moved to
    [c9_ΓB]: the [tCase] case of [context_cumulativity_propE]. *)
Definition c9_Δ : context := [vass si_na (c9_Ak 0); vass si_na c9_H].

Lemma c9_match_typed_A : si_Σ ;;; c9_ΓA |-E lift0 2 cp_match : lift0 2 cp_match_ty.
Proof. exact (weakeningE si_Σ cp_Γ1 c9_Δ _ _ si_wfE c9_wf_ΓA cp_match_typed). Qed.

Lemma context_cumulativityE_match_inst : si_Σ ;;; c9_ΓB |-E lift0 2 cp_match : lift0 2 cp_match_ty.
Proof.
  exact (context_cumulativityE (Σ := si_Σ) (wfΣ := si_wfE) c9_ΓA c9_match_typed_A c9_wf_ΓB c9_cumul_BA).
Qed.
