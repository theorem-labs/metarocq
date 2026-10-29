(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the hypotheses of [PCUICWsCumulEtaCtx] and
    [PCUICWsCumulEtaCtxTyp]

  Each lemma of the two files whose conclusion is not [False] is applied here to
  a concrete instance with every premise proved: the environment [si_Σ] of
  [PCUICCumulativitySpecEtaClosureInstances] ([Inductive I (A : Prop) : Prop :=
  c : I A]; [si_wf], [si_wfE], [si_cb]), closed terms ([fi_P := tSort sProp], the
  β-redex [fi_beta], the η-redex [fi_eta]) and small contexts. Where a lemma
  relates two different things, the instance does too: a β-redex against its
  reduct, two contexts whose let-bodies differ, a context at [Cumul].

  The scoping helpers ([on_free_vars_subst_gen_k], [shiftnP_add3],
  [open_app3_inv], [closed_app3_inv]), [mix_ctx_length], [WS_trans],
  [subst0_cons] and [subst0_cons_lift] have no separate instance: each is used by
  an instanced lemma below.

  The lemmas [rf_Rel1_normal], [rf_body_normal], [rf_t_normal], [rf_f_normal],
  [ws_cumul_pbE_red_false] and [ws_cumul_pbE_alt_closed_false] conclude [False]:
  each states that its premises are jointly unsatisfiable, so none has an
  instance. [rf_premise], [rf_wf_sort], [rf_wf_Γ], [rf_f_typed], [rf_t_typed] and
  [rf_witness_typed] are closed facts; [rf_P_typed], [rf_P_vass] and [rf_F_typed]
  are applied in that file to the contexts [[]], [rf_Γ] and [rf_Γ ,, x : Prop],
  each proved well formed there. *)

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICEquality PCUICReduction
     PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICWellScopedCumulativity PCUICSubstitution PCUICConversion PCUICContextConversion
     PCUICEtaDefs PCUICEtaCanon PCUICEtaC1aR PCUICEtaFInst PCUICEtaI5 PCUICEtaI5A2
     PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICWsCumulEtaSubst
     PCUICContextConversionEta PCUICTypingEta PCUICTypingEtaInd PCUICClosedTypEta
     PCUICCumulativitySpecEtaClosureInstances PCUICEtaFracInstances PCUICEtaA6Instances
     PCUICContextSubst PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp PCUICClosedBodies.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

Local Notation WS pb Γ := (ws_cumul_pbE pb si_Σ Γ).

(** ** Concrete data *)

(** Two one-let contexts whose bodies are a β-redex and its reduct. *)
Definition ci_Γd1 : context := [vdef si_na fi_beta fi_P].
Definition ci_Γd2 : context := [vdef si_na fi_P fi_P].

Lemma ci_ctx_d : ws_cumul_ctx_pbE Cumul si_Σ ci_Γd1 ci_Γd2.
Proof.
  constructor; [constructor|]. constructor; [reflexivity|exact (fi_WS_beta Conv)|].
  apply ws_cumul_pbE_refl; reflexivity.
Qed.

(** In [ci_Γd2] the variable unfolds to [Prop]. *)
Lemma ci_Rel0_d2 pb : WS pb ci_Γd2 (tRel 0) fi_P.
Proof.
  apply red_ws_cumul_pbE. split; [reflexivity|reflexivity|].
  apply red1_red. apply (red_rel _ _ 0 fi_P). reflexivity.
Qed.

Lemma ci_untyped_subslet : untyped_subslet [] [fi_beta] [vass si_na fi_P].
Proof. repeat constructor. Qed.

Lemma ci_untyped_subslet' : untyped_subslet [] [fi_P] [vass si_na fi_P].
Proof. repeat constructor. Qed.

Lemma ci_WT : ws_cumul_pbE_terms si_Σ [] [fi_beta] [fi_P].
Proof. constructor; [exact (fi_WS_beta Conv)|constructor]. Qed.

(** ** Scoping projections, [Conv ⊆ Cumul], unscoped context relations *)

Lemma ws_cumul_pbE_is_closed_context_inst : is_closed_context ([] : context).
Proof. exact (ws_cumul_pbE_is_closed_context (fi_WS_beta Conv)). Qed.
Lemma ws_cumul_pbE_is_open_term_left_inst : is_open_term ([] : context) fi_beta.
Proof. exact (ws_cumul_pbE_is_open_term_left (fi_WS_beta Conv)). Qed.
Lemma ws_cumul_pbE_is_open_term_right_inst : is_open_term ([] : context) fi_P.
Proof. exact (ws_cumul_pbE_is_open_term_right (fi_WS_beta Conv)). Qed.
Lemma ws_cumul_pbE_eq_le_inst : WS Cumul [] fi_beta fi_P.
Proof. exact (ws_cumul_pbE_eq_le (fi_WS_beta Conv)). Qed.
Lemma ws_cumul_declsE_closed_inst : is_closed_context ([] : context).
Proof.
  apply (ws_cumul_declsE_closed (pb := Cumul) (Σ := si_Σ) (d := vdef si_na fi_beta fi_P) (d' := vdef si_na fi_P fi_P)).
  constructor; [reflexivity|exact (fi_WS_beta Conv)|]. apply ws_cumul_pbE_refl; reflexivity.
Qed.
Lemma ws_cumul_ctx_pbE_closed_left_inst : is_closed_context ci_Γd1.
Proof. exact (ws_cumul_ctx_pbE_closed_left ci_ctx_d). Qed.
Lemma ws_cumul_ctx_pbE_forget_inst : cumul_pb_context (@JoinE _) Cumul si_Σ ci_Γd1 ci_Γd2.
Proof. exact (ws_cumul_ctx_pbE_forget ci_ctx_d). Qed.
Lemma into_ws_cumul_ctx_pbE_inst : ws_cumul_ctx_pbE Cumul si_Σ ci_Γd1 ci_Γd2.
Proof. apply into_ws_cumul_ctx_pbE; [reflexivity|reflexivity|exact ws_cumul_ctx_pbE_forget_inst]. Qed.
Lemma ws_cumul_ctx_pbE_refl_pb_inst : ws_cumul_ctx_pbE Cumul si_Σ ci_Γd1 ci_Γd1.
Proof. exact (ws_cumul_ctx_pbE_refl_pb (Γ := ci_Γd1) eq_refl). Qed.
Lemma conv_cumul_contextE_inst : ws_cumul_ctx_pbE Cumul si_Σ fi_Γ1 fi_Γb.
Proof. exact (conv_cumul_contextE fi_ctx_P_beta). Qed.
Lemma ws_cumul_ctx_pbE_app_same_inst :
  ws_cumul_ctx_pbE Cumul si_Σ (ci_Γd1 ,,, [vass si_na (tRel 0)]) (ci_Γd2 ,,, [vass si_na (tRel 0)]).
Proof. apply ws_cumul_ctx_pbE_app_same; [reflexivity|exact ci_ctx_d]. Qed.
Lemma cumul_context_app_sameE_inst :
  cumul_context (@JoinE _) si_Σ (ci_Γd1 ,,, [vass si_na (tRel 0)]) (ci_Γd2 ,,, [vass si_na (tRel 0)]).
Proof. exact (cumul_context_app_sameE si_Σ _ _ _ ws_cumul_ctx_pbE_forget_inst). Qed.
Lemma eq_context_upto_names_conv_contextE_inst :
  conv_context (@JoinE _) si_Σ [vass si_na fi_P] [vass (mkBindAnn (nNamed "x") Relevant) fi_P].
Proof. apply eq_context_upto_names_conv_contextE. repeat constructor. Qed.
Lemma eq_term_upto_univ_cumulSpecE_inst : si_Σ ;;; [] ⊢ fi_P ≤sE[Cumul] fi_P.
Proof. apply eq_term_upto_univ_cumulSpecE. reflexivity. Qed.
Lemma conv_indsE_inst :
  ws_cumul_pbE_terms si_Σ [] (inds (inductive_mind si_ind) [] (ind_bodies si_mdecl))
    (inds (inductive_mind si_ind) [] (ind_bodies si_mdecl)).
Proof. apply conv_indsE; [constructor|reflexivity]. Qed.

(** ** Contexts that differ only in assumption types, and context cumulativity *)

Lemma JoinE_bodies_inst : JoinE si_Σ fi_Γb Conv (tRel 0) (tRel 0).
Proof. apply (JoinE_bodies (Γ := fi_Γ1)); [exact (bodies_vass [] si_na si_na fi_P fi_beta)|apply JoinE_refl]. Qed.
Lemma ws_cumul_pbE_bodies_inst : WS Conv fi_Γb (tRel 0) (tRel 0).
Proof.
  apply (ws_cumul_pbE_bodies (Γ := fi_Γ1)); [exact (bodies_vass [] si_na si_na fi_P fi_beta)|reflexivity|].
  apply ws_cumul_pbE_refl; reflexivity.
Qed.
Lemma mix_ctx_bodies_inst :
  upto_domain_r_bodies ci_Γd1 (mix_ctx ci_Γd1 ci_Γd2) × upto_domain_r_bodies (mix_ctx ci_Γd1 ci_Γd2) ci_Γd1.
Proof. exact (mix_ctx_bodies ci_Γd1 ci_Γd2 eq_refl). Qed.
Lemma mix_ctx_closed_inst : is_closed_context (mix_ctx ci_Γd1 ci_Γd2).
Proof. exact (mix_ctx_closed ci_ctx_d). Qed.
Lemma mix_ctx_conv_inst : ws_cumul_ctx_pbE Conv si_Σ (mix_ctx ci_Γd1 ci_Γd2) ci_Γd2.
Proof. exact (mix_ctx_conv ci_ctx_d). Qed.
(** The variable of [ci_Γd1] (body [fi_beta]) unfolds to [Prop] too: the
    conversion moves from [ci_Γd2] along the context cumulativity. *)
Lemma ws_cumul_pbE_ws_cumul_ctx_pb_inst : WS Conv ci_Γd1 (tRel 0) fi_P.
Proof. exact (ws_cumul_pbE_ws_cumul_ctx_pb ci_ctx_d (ci_Rel0_d2 Conv)). Qed.
Lemma ws_cumul_declsE_ws_cumul_ctx_inst :
  ws_cumul_declsE Conv si_Σ ci_Γd1 (vass si_na (tRel 0)) (vass si_na fi_P).
Proof.
  apply (ws_cumul_declsE_ws_cumul_ctx (pb' := Cumul) (Γ := ci_Γd2) ci_ctx_d).
  constructor; [reflexivity|exact (ci_Rel0_d2 Conv)].
Qed.
Lemma ws_cumul_declsE_trans_inst :
  ws_cumul_declsE Conv si_Σ ci_Γd2 (vass si_na (tRel 0)) (vass si_na fi_P).
Proof.
  apply (ws_cumul_declsE_trans (d' := vass si_na fi_P)).
  - constructor; [reflexivity|exact (ci_Rel0_d2 Conv)].
  - constructor; [reflexivity|apply ws_cumul_pbE_refl; reflexivity].
Qed.
Lemma ws_cumul_ctx_pbE_trans_inst : ws_cumul_ctx_pbE Cumul si_Σ ci_Γd1 ci_Γd2.
Proof. exact (ws_cumul_ctx_pbE_trans Cumul _ _ _ ws_cumul_ctx_pbE_refl_pb_inst ci_ctx_d). Qed.
Lemma context_cumulativity_appE_inst :
  ws_cumul_ctx_pbE Conv si_Σ (ci_Γd1 ,,, [vass si_na (tRel 0)]) (ci_Γd1 ,,, [vass si_na fi_P]).
Proof.
  apply (context_cumulativity_appE (Γ := ci_Γd2) ci_ctx_d).
  constructor; [exact (ws_cumul_ctx_pbE_refl_pb (Γ := ci_Γd2) eq_refl)|].
  constructor; [reflexivity|exact (ci_Rel0_d2 Conv)].
Qed.

(** ** Substitution of convertible terms *)

Lemma ws_cumul_pbE_subst1_conv_inst : WS Conv [] ((tRel 0) {0 := fi_beta}) ((tRel 0) {0 := fi_P}).
Proof. apply (ws_cumul_pbE_subst1_conv (Γ := []) (c := tRel 0)); [reflexivity|exact (fi_WS_beta Conv)]. Qed.
Lemma ws_cumul_pbE_subst0_conv_inst : WS Conv [] (subst0 [fi_beta] (tRel 0)) (subst0 [fi_P] (tRel 0)).
Proof. apply (ws_cumul_pbE_subst0_conv (Γ := [])); [reflexivity|exact ci_WT|reflexivity]. Qed.
Lemma ws_cumul_pbE_LetIn_body_inv_inst : WS Conv ([] ,, vdef si_na fi_beta fi_P) (tRel 0) (tRel 0).
Proof.
  apply (ws_cumul_pbE_LetIn_body_inv (na' := si_na) (b' := fi_P) (A' := fi_P) (fi_WS_beta Conv)).
  apply ws_cumul_pbE_LetIn; [reflexivity|exact (fi_WS_beta Conv)|apply ws_cumul_pbE_refl; reflexivity|].
  apply ws_cumul_pbE_refl; reflexivity.
Qed.
(** Under a let-binder whose body mentions the substituted variable. *)
Lemma ws_cumul_pbE_subst_conv_gen_inst :
  WS Conv ([] ,,, subst_context [fi_beta] 0 [vdef si_na (tRel 0) fi_P])
    (subst [fi_beta] 1 (tRel 0)) (subst [fi_P] 1 (tRel 0)).
Proof.
  apply (ws_cumul_pbE_subst_conv_gen (Γ := []) [vdef si_na (tRel 0) fi_P]); [reflexivity|exact ci_WT|reflexivity|reflexivity].
Qed.
Lemma untyped_substitution_ws_cumul_pbE_subst_conv_inst :
  WS Conv ([] ,,, subst_context [fi_beta] 0 [vass si_na (tRel 0)])
    (subst [fi_beta] 1 (tRel 1)) (subst [fi_P] 1 (tRel 1)).
Proof.
  apply (untyped_substitution_ws_cumul_pbE_subst_conv (Γ := []) (Δ := [vass si_na fi_P]) (Δ' := [vass si_na fi_P])
           (Γ' := [vass si_na (tRel 0)]));
    [exact ci_WT|reflexivity|reflexivity|exact ci_untyped_subslet|exact ci_untyped_subslet'|reflexivity].
Qed.
Lemma substitution_ws_cumul_pbE_subst_conv_inst :
  WS Cumul ([] ,,, subst_context [fi_beta] 0 []) (subst [fi_beta] 0 (tRel 0)) (subst [fi_P] 0 (tRel 0)).
Proof.
  apply (substitution_ws_cumul_pbE_subst_conv (Γ := []) (Γ0 := [vass si_na fi_P]) (Γ1 := [vass si_na fi_P]) (Δ := []));
    [exact ci_untyped_subslet|exact ci_untyped_subslet'|exact ci_WT|reflexivity|].
  apply ws_cumul_pbE_refl; reflexivity.
Qed.
Lemma substitution_ws_cumul_ctx_pbE_inst :
  ws_cumul_ctx_pbE Conv si_Σ ([] ,,, subst_context [fi_beta] 0 [vass si_na (tRel 0)])
    ([] ,,, subst_context [fi_P] 0 [vass si_na (tRel 0)]).
Proof.
  apply (substitution_ws_cumul_ctx_pbE (Γ := []) (Δ := [vass si_na fi_P]) (Δ' := [vass si_na fi_P]) (Γ' := [vass si_na (tRel 0)]));
    [exact ci_untyped_subslet|exact ci_untyped_subslet'|exact ci_WT|reflexivity|reflexivity].
Qed.

(** ** The relative context relation *)

Lemma ci_rel : ws_cumul_ctx_pbE_rel Conv si_Σ [] [vass si_na fi_beta] [vass si_na fi_P].
Proof. split; [reflexivity|]. constructor; [constructor|]. constructor; [reflexivity|exact (fi_WS_beta Conv)]. Qed.

Lemma ws_cumul_ctx_pbE_rel_app_inst :
  ws_cumul_ctx_pbE Conv si_Σ ([] ,,, [vass si_na fi_beta]) ([] ,,, [vass si_na fi_P]).
Proof. exact (fst ws_cumul_ctx_pbE_rel_app ci_rel). Qed.
Lemma ws_cumul_ctx_pbE_rel_app_inv_inst : ws_cumul_ctx_pbE_rel Conv si_Σ [] [vass si_na fi_beta] [vass si_na fi_P].
Proof. exact (snd ws_cumul_ctx_pbE_rel_app ws_cumul_ctx_pbE_rel_app_inst). Qed.
Lemma weaken_ws_cumul_pbE_inst : WS Conv (fi_Γ1 ,,, []) fi_beta fi_P.
Proof. exact (weaken_ws_cumul_pbE fi_Γ1 eq_refl (fi_WS_beta Conv)). Qed.
Lemma weaken_ws_cumul_ctx_pbE_rel_inst :
  ws_cumul_ctx_pbE_rel Conv si_Σ (fi_Γ1 ,,, []) [vass si_na fi_beta] [vass si_na fi_P].
Proof. apply (weaken_ws_cumul_ctx_pbE_rel (Γ := fi_Γ1)); [reflexivity|exact ci_rel]. Qed.
Lemma ws_cumul_pbE_it_mkProd_or_LetIn_inst :
  WS Cumul [] (it_mkProd_or_LetIn [vass si_na fi_beta] (tRel 0)) (it_mkProd_or_LetIn [vass si_na fi_P] (tRel 0)).
Proof.
  apply (ws_cumul_pbE_it_mkProd_or_LetIn [] _ _ _ _ ci_rel).
  apply ws_cumul_pbE_refl; reflexivity.
Qed.
Lemma substitution_ws_cumul_ctx_pbE_subst_conv_inst :
  ws_cumul_ctx_pbE_rel Conv si_Σ ([] ,,, subst_context [fi_beta] 0 [])
    (subst_context [fi_beta] 0 [vass si_na (tRel 0)]) (subst_context [fi_P] 0 [vass si_na (tRel 0)]).
Proof.
  apply (substitution_ws_cumul_ctx_pbE_subst_conv (Γ := []) (Γ' := [vass si_na fi_P]) (Γ'0 := [vass si_na fi_P])
           (Γ'' := []) (Δ := [vass si_na (tRel 0)]) (Δ' := [vass si_na (tRel 0)]));
    [|exact ci_WT|exact ci_untyped_subslet|exact ci_untyped_subslet'|reflexivity].
  split; [reflexivity|]. constructor; [constructor|]. constructor; [reflexivity|].
  apply ws_cumul_pbE_refl; reflexivity.
Qed.
Lemma ws_cumul_pbE_terms_subst_inst :
  ws_cumul_pbE_terms si_Σ ([] ,,, subst_context [fi_beta] 0 []) (map (subst [fi_beta] 0) [tRel 0])
    (map (subst [fi_P] 0) [tRel 0]).
Proof.
  apply (ws_cumul_pbE_terms_subst (Γ := []) (Γ' := [vass si_na fi_P]) (Γ'' := [vass si_na fi_P]) (Δ := []));
    [reflexivity|exact ci_untyped_subslet|exact ci_untyped_subslet'|exact ci_WT|].
  constructor; [apply ws_cumul_pbE_refl; reflexivity|constructor].
Qed.
Lemma red_terms_ws_cumul_pbE_terms_inst : ws_cumul_pbE_terms si_Σ [] [fi_beta] [fi_P].
Proof. apply red_terms_ws_cumul_pbE_terms. constructor; [exact fi_closed_red_beta|constructor]. Qed.
Lemma eq_terms_ws_cumul_pbE_terms_inst : ws_cumul_pbE_terms si_Σ [] [fi_P] [fi_P].
Proof. apply eq_terms_ws_cumul_pbE_terms; [reflexivity|reflexivity|reflexivity|]. constructor; [reflexivity|constructor]. Qed.
Lemma subst_instance_ws_cumul_ctx_pbE_rel_inst :
  ws_cumul_ctx_pbE_rel Cumul si_Σ [] (subst_instance [] ci_Γd1) (subst_instance [] ci_Γd1).
Proof. apply subst_instance_ws_cumul_ctx_pbE_rel; [reflexivity|constructor]. Qed.
Lemma weakening_cumul0E_inst :
  JoinE si_Σ ([] ,,, fi_Γ1) Cumul (lift0 #|fi_Γ1| fi_beta) (lift0 #|fi_Γ1| fi_P).
Proof.
  exact (weakening_cumul0E (Γ := exist [] eq_refl) (Γ'' := exist fi_Γ1 eq_refl)
           (M := exist fi_beta eq_refl) (N := exist fi_P eq_refl) _ eq_refl (fi_J_beta Cumul)).
Qed.
Lemma into_ws_cumul_pbE_red_inst : WS Cumul [] fi_beta fi_P.
Proof.
  apply into_ws_cumul_pbE_red. exists fi_P, fi_P. split; [exact fi_closed_red_beta| |reflexivity].
  apply closed_red_refl; reflexivity.
Qed.

(** ** The typed lemmas *)

Lemma ci_wf_sort_P : wf_sort si_Σ sProp.
Proof. cbn; trivial. Qed.

Lemma ci_typeE_P (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E fi_P : tSort (Sort.super sProp).
Proof. intros h. apply typeE_Sort; [exact h|exact ci_wf_sort_P]. Qed.

Lemma ci_isTypeE_P (Γ : context) : wf_localE si_Σ Γ -> on_type (lift_typing typingE) si_Σ Γ fi_P.
Proof. intros h. split; [exact tt|]. exists (Sort.super sProp). split; [exact (ci_typeE_P Γ h)|]. split; exact I. Qed.

Lemma ci_wf_Γ1 : wf_localE si_Σ fi_Γ1.
Proof.
  apply localenv_cons_abs; [constructor|].
  split; [exact tt|]. exists (Sort.super sProp). split; [exact (ci_typeE_P [] localenv_nil)|]. split; [exact I|reflexivity].
Qed.

Lemma on_typeE_scoped_inst : is_closed_context ([] : context) × is_open_term ([] : context) fi_P.
Proof. exact (on_typeE_scoped (Σ := si_Σ) (wfΣ := si_wfE) (ci_isTypeE_P [] localenv_nil)). Qed.
Lemma isType_ws_cumul_pbE_refl_inst : WS Cumul fi_Γ1 fi_P fi_P.
Proof. exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) (wfΣ := si_wfE) fi_Γ1 fi_P (ci_isTypeE_P fi_Γ1 ci_wf_Γ1)). Qed.
Lemma wt_cumul_pbE_inst : wt_cumul_pbE Cumul si_Σ fi_Γ1 fi_P fi_P.
Proof. constructor; [exact (ci_isTypeE_P fi_Γ1 ci_wf_Γ1)|exact (ci_isTypeE_P fi_Γ1 ci_wf_Γ1)|apply JoinE_refl]. Qed.
Lemma wt_cumul_pbE_ws_cumul_pbE_inst : WS Cumul fi_Γ1 fi_P fi_P.
Proof. exact (wt_cumul_pbE_ws_cumul_pbE (Σ := si_Σ) (wfΣ := si_wfE) wt_cumul_pbE_inst). Qed.
Lemma subst_instance_ws_cumul_ctx_pbE_inst :
  ws_cumul_ctx_pbE Cumul si_Σ (subst_instance [] fi_Γ1) (subst_instance [] fi_Γ1).
Proof.
  apply (subst_instance_ws_cumul_ctx_pbE (Σ := si_Σ) (wfΣ := si_wfE) (Δ := fi_Γ1) (u := []) (u' := []) Cumul);
    [exact ci_wf_Γ1|constructor].
Qed.

(** [(λ_:Prop. x) Prop] in the context [x : Prop] β-reduces to [x]. *)
Lemma red_betas0_cb_inst :
  red si_Σ.1 [] (mkApps (it_mkLambda_or_LetIn fi_Γ1 (tRel 0)) [fi_P])
    (subst0 (List.rev [fi_P]) (expand_lets fi_Γ1 (tRel 0))).
Proof. exact (red_betas0_cb si_Σ si_cb [] fi_Γ1 [fi_P] (tRel 0) (tRel 0) eq_refl eq_refl eq_refl (rt_refl _ _)). Qed.
Lemma red_betas_cb_inst :
  red si_Σ.1 [] (mkApps (it_mkLambda_or_LetIn fi_Γ1 (tRel 0)) [fi_P]) (subst0 (mk_ctx_subst fi_Γ1 [fi_P]) (tRel 0)).
Proof. exact (red_betas_cb si_Σ si_cb [] fi_Γ1 [fi_P] (tRel 0) eq_refl eq_refl eq_refl). Qed.
Lemma red_betas_typedE_inst :
  red si_Σ.1 [] (mkApps (it_mkLambda_or_LetIn fi_Γ1 (tRel 0)) [fi_P]) (subst0 (mk_ctx_subst fi_Γ1 [fi_P]) (tRel 0)).
Proof.
  exact (red_betas_typedE si_Σ si_wfE [] fi_Γ1 [fi_P] (tRel 0) _ eq_refl
           (typeE_Rel _ _ 0 (vass si_na fi_P) ci_wf_Γ1 eq_refl)).
Qed.
Lemma conv_betasE_inst :
  si_Σ ;;; [] ⊢ mkApps (it_mkLambda_or_LetIn fi_Γ1 (tRel 0)) [fi_P] ≤sE[Conv] subst0 (mk_ctx_subst fi_Γ1 [fi_P]) (tRel 0).
Proof. exact (conv_betasE si_Σ si_cb [] fi_Γ1 [fi_P] (tRel 0) eq_refl eq_refl eq_refl eq_refl). Qed.
Lemma cumul_decls_reflE_inst : cumul_decls (@JoinE _) si_Σ [] [] (vass si_na fi_P) (vass si_na fi_P).
Proof. apply cumul_decls_reflE. Qed.
(** The local-environment premise holds for any context related to [[]]: [Prop] is
    a type in every well-formed context. *)
Lemma context_cumulativity_wf_appE_inst : wf_localE si_Σ ([] ,,, fi_Γ1).
Proof.
  apply (context_cumulativity_wf_appE si_Σ [] [] fi_Γ1); [constructor|constructor|].
  apply localenv_cons_abs; [constructor|].
  intros Γ' _ wfΓ'. split; [exact tt|]. exists (Sort.super sProp).
  split; [exact (ci_typeE_P Γ' wfΓ')|]. split; [exact I|reflexivity].
Qed.
