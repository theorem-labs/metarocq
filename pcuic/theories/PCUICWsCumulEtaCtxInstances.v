(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the hypotheses of [PCUICWsCumulEtaCtx] and
    [PCUICWsCumulEtaCtxTyp]

  Each lemma of the two files that has a premise and does not conclude [False] is
  applied here to a concrete instance with every premise proved. The environment
  is [si_Σ] of [PCUICCumulativitySpecEtaClosureInstances]
  ([Inductive I (A : Prop) : Prop := c : I A]; [si_wf], [si_wfE], [si_cb]), or for
  the universe lemmas [ci_Σu]: the same declarations, with two bound universe
  levels and the constraint that they are equal. The terms are closed or live in
  small contexts: [fi_P := Prop], the β-redex [fi_beta := (λx:Prop. x) Prop], the
  η-redex [fi_eta := λx:Prop. Prop x], two λ-terms that differ only in a binder
  name, and the proposition [ci_False := ∀P:Prop. P].

  Where a lemma relates two things, the instance relates two different things: an
  η-redex against its contraction (context cumulativity, the general substitution
  lemma, transitivity), a β-redex against its reduct, two contexts whose let-bodies
  differ or whose assumption types differ, two λ-terms that [compare_term] relates
  without being equal, two different universe instances related by the
  environment's constraint (which a valuation satisfies, [ci_Σu_satisfies]), a
  context at [Cumul]. The transitivity instances go through a middle term that
  differs from both ends. The exceptions are the lemmas whose conclusion is
  reflexive by statement ([ws_cumul_ctx_pbE_refl_pb], [cumul_decls_reflE],
  [isType_ws_cumul_pbE_refl]) and the scoping projections.

  [shiftnP_add3], [subst0_cons] and [subst0_cons_lift] have no premise, so no
  instance. The lemmas [rf_Rel1_normal], [rf_body_normal], [rf_t_normal],
  [rf_f_normal], [ws_cumul_pbE_red_false] and [ws_cumul_pbE_alt_closed_false]
  conclude [False]: each states that its premises are jointly unsatisfiable, so
  none has an instance. [rf_premise], [rf_wf_sort], [rf_wf_Γ], [rf_f_typed],
  [rf_t_typed] and [rf_witness_typed] are closed facts.

  [WS_trans] is [PCUICEtaA6]'s; [PCUICWsCumulEtaCtx] carried a second copy of the identical
  compiled statement, which is gone, so the transitivity instances below name
  [PCUICEtaA6.WS_trans].

  One own name SHADOWS a DIFFERENT statement of the same name in this file's import closure:
  [WS_trans_inst], also carried by [PCUICEtaA6Instances]. The two are instances of the one
  [WS_trans] at different chains: [PCUICEtaA6Instances]' is the β-redex against [Prop]
  ([fi_beta] to [fi_P]), this one is the β-redex against the η-redex ([fi_beta] to
  [fi_eta]), through the same middle term. No ascription relates them. Both are kept: each is
  the measured witness its own file's table reads. Every reference to the name in a file that
  has both objects in scope is written qualified. *)

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICEquality PCUICReduction
     PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICWellScopedCumulativity PCUICSubstitution PCUICConversion PCUICContextConversion
     PCUICUnivSubst PCUICWfUniverses
     PCUICEtaDefs PCUICEtaCanon PCUICEtaC1aR PCUICEtaC1b PCUICEtaFInst PCUICEtaI5 PCUICEtaI5A2
     PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICWsCumulEtaSubst
     PCUICContextConversionEta PCUICTypingEta PCUICTypingEtaInd PCUICClosedTypEta
     PCUICCumulativitySpecEtaClosureInstances PCUICEtaFracInstances PCUICEtaA6Instances
     PCUICContextSubst PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp PCUICClosedBodies.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

Local Notation WS pb Γ := (ws_cumul_pbE pb si_Σ Γ).

(** ** Concrete data *)

(** The η-pair: [λx:Prop. Prop x] and its η-contraction [Prop]. *)
Lemma ci_WS_eta pb : WS pb [] fi_eta fi_P.
Proof.
  apply (eta1_ws_cumul_pbE (Σ := si_Σ) (pb := pb) (Γ := []) (t := fi_eta) (u := fi_P));
    [reflexivity|reflexivity|exact fi_eta1].
Qed.

Lemma ci_WS_eta_r pb : WS pb [] fi_P fi_eta.
Proof.
  apply (eta1_ws_cumul_pbE_inv (Σ := si_Σ) (pb := pb) (Γ := []) (t := fi_eta) (u := fi_P));
    [reflexivity|reflexivity|exact fi_eta1].
Qed.

(** Two one-let contexts whose bodies are the η-pair; a third with the body of the
    second and a β-redex as type. *)
Definition ci_Γd1 : context := [vdef si_na fi_eta fi_P].
Definition ci_Γd2 : context := [vdef si_na fi_P fi_P].
Definition ci_Γd3 : context := [vdef si_na fi_P fi_beta].

Lemma ci_ctx_d : ws_cumul_ctx_pbE Cumul si_Σ ci_Γd1 ci_Γd2.
Proof.
  constructor; [constructor|]. constructor; [reflexivity|exact (ci_WS_eta Conv)|].
  apply ws_cumul_pbE_refl; reflexivity.
Qed.

(** In [ci_Γd2] the variable unfolds to [Prop]. *)
Lemma ci_Rel0_d2 pb : WS pb ci_Γd2 (tRel 0) fi_P.
Proof.
  apply red_ws_cumul_pbE. split; [reflexivity|reflexivity|].
  apply red1_red. apply (red_rel _ _ 0 fi_P). reflexivity.
Qed.

Lemma ci_bodies_d23 : upto_domain_r_bodies ci_Γd2 ci_Γd3.
Proof. unfold ci_Γd2, ci_Γd3. apply upto_domain_r_bodies_vdef; [apply upto_domain_r_refl|constructor]. Qed.

Lemma ci_untyped_subslet : untyped_subslet [] [fi_beta] [vass si_na fi_P].
Proof. repeat constructor. Qed.

Lemma ci_untyped_subslet' : untyped_subslet [] [fi_P] [vass si_na fi_P].
Proof. repeat constructor. Qed.

Lemma ci_WT : ws_cumul_pbE_terms si_Σ [] [fi_beta] [fi_P].
Proof. constructor; [exact (fi_WS_beta Conv)|constructor]. Qed.

Lemma ci_WT_eta : ws_cumul_pbE_terms si_Σ [] [fi_eta] [fi_P].
Proof. constructor; [exact (ci_WS_eta Conv)|constructor]. Qed.

(** Two λ-terms that differ only in the binder name. *)
Definition ci_lam : term := tLambda si_na fi_P (tRel 0).
Definition ci_lam' : term := tLambda (mkBindAnn (nNamed "x") Relevant) fi_P (tRel 0).

Lemma ci_eq_lam pb : compare_term si_Σ si_Σ pb ci_lam ci_lam'.
Proof. unfold ci_lam, ci_lam'. eapply eq_Lambda; [reflexivity|reflexivity|constructor]. Qed.

(** ** Scoping helpers *)

Lemma on_free_vars_subst_gen_k_inst : on_free_vars (shiftnP 1 xpred0) (subst [fi_P] 1 (tRel 1)).
Proof. exact (on_free_vars_subst_gen_k xpred0 1 [fi_P] (tRel 1) eq_refl eq_refl). Qed.
Lemma open_app3_inv_inst :
  on_free_vars (shiftnP #|[vass si_na fi_P]| (shiftnP #|[vass si_na fi_P]| (shiftnP #|fi_Γ1| xpred0))) (tRel 2).
Proof. exact (open_app3_inv fi_Γ1 [vass si_na fi_P] [vass si_na fi_P] (tRel 2) eq_refl). Qed.
Lemma closed_app3_inv_inst :
  [× is_closed_context fi_Γ1, on_free_vars_ctx (shiftnP #|fi_Γ1| xpred0) [vass si_na (tRel 0)] &
     on_free_vars_ctx (shiftnP #|[vass si_na (tRel 0)]| (shiftnP #|fi_Γ1| xpred0)) [vass si_na (tRel 1)]].
Proof. exact (closed_app3_inv fi_Γ1 [vass si_na (tRel 0)] [vass si_na (tRel 1)] eq_refl). Qed.

(** ** Scoping projections, [Conv ⊆ Cumul], unscoped context relations *)

Lemma ws_cumul_pbE_is_closed_context_inst : is_closed_context ([] : context).
Proof. exact (ws_cumul_pbE_is_closed_context (fi_WS_beta Conv)). Qed.
Lemma ws_cumul_pbE_is_open_term_left_inst : is_open_term ([] : context) fi_beta.
Proof. exact (ws_cumul_pbE_is_open_term_left (fi_WS_beta Conv)). Qed.
Lemma ws_cumul_pbE_is_open_term_right_inst : is_open_term ([] : context) fi_P.
Proof. exact (ws_cumul_pbE_is_open_term_right (fi_WS_beta Conv)). Qed.
Lemma ws_cumul_pbE_eq_le_inst : WS Cumul [] fi_eta fi_P.
Proof. exact (ws_cumul_pbE_eq_le (ci_WS_eta Conv)). Qed.
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
Lemma eq_term_upto_univ_cumulSpecE_inst : si_Σ ;;; [] ⊢ ci_lam ≤sE[Cumul] ci_lam'.
Proof. apply eq_term_upto_univ_cumulSpecE. exact (ci_eq_lam Cumul). Qed.

(** ** Contexts that differ only in assumption types, and context cumulativity *)

(** [ci_Γd2] and [ci_Γd3] have the same let-body and different types: the join of
    the variable with [Prop] moves from one to the other. *)
Lemma JoinE_bodies_inst : JoinE si_Σ ci_Γd3 Conv (tRel 0) fi_P.
Proof. exact (JoinE_bodies ci_bodies_d23 (wsE_join (ci_Rel0_d2 Conv))). Qed.
Lemma ws_cumul_pbE_bodies_inst : WS Conv ci_Γd3 (tRel 0) fi_P.
Proof. apply (ws_cumul_pbE_bodies ci_bodies_d23); [reflexivity|exact (ci_Rel0_d2 Conv)]. Qed.
Lemma mix_ctx_length_inst : #|mix_ctx ci_Γd1 ci_Γd3| = #|ci_Γd3|.
Proof. exact (mix_ctx_length ci_Γd1 ci_Γd3 eq_refl). Qed.
Lemma mix_ctx_bodies_inst :
  upto_domain_r_bodies ci_Γd1 (mix_ctx ci_Γd1 ci_Γd2) × upto_domain_r_bodies (mix_ctx ci_Γd1 ci_Γd2) ci_Γd1.
Proof. exact (mix_ctx_bodies ci_Γd1 ci_Γd2 eq_refl). Qed.
Lemma mix_ctx_closed_inst : is_closed_context (mix_ctx ci_Γd1 ci_Γd2).
Proof. exact (mix_ctx_closed ci_ctx_d). Qed.
Lemma mix_ctx_conv_inst : ws_cumul_ctx_pbE Conv si_Σ (mix_ctx ci_Γd1 ci_Γd2) ci_Γd2.
Proof. exact (mix_ctx_conv ci_ctx_d). Qed.
(** The variable of [ci_Γd1], whose body is the η-redex [fi_eta], is convertible
    to [Prop] too: the conversion moves from [ci_Γd2] along the context
    cumulativity. *)
Lemma ws_cumul_pbE_ws_cumul_ctx_pb_inst : WS Conv ci_Γd1 (tRel 0) fi_P.
Proof. exact (ws_cumul_pbE_ws_cumul_ctx_pb ci_ctx_d (ci_Rel0_d2 Conv)). Qed.
Lemma ws_cumul_declsE_ws_cumul_ctx_inst :
  ws_cumul_declsE Conv si_Σ ci_Γd1 (vass si_na (tRel 0)) (vass si_na fi_P).
Proof.
  apply (ws_cumul_declsE_ws_cumul_ctx (pb' := Cumul) (Γ := ci_Γd2) ci_ctx_d).
  constructor; [reflexivity|exact (ci_Rel0_d2 Conv)].
Qed.
(** In [ci_Γd2]: the variable against the η-redex [fi_eta] (its let-body [Prop],
    then an η-expansion), and the η-redex against its contraction [Prop]. Each
    step relates two different terms, and the middle term [fi_eta] differs from
    both ends. *)
Lemma ci_WS_Rel0_eta_d2 : WS Conv ci_Γd2 (tRel 0) fi_eta.
Proof.
  apply (PCUICEtaA6.WS_trans (Σ := si_Σ) (wfΣ := si_cb) (u := fi_P)); [exact (ci_Rel0_d2 Conv)|].
  exact (weaken_ws_cumul_pbE (Γ := []) ci_Γd2 eq_refl (ci_WS_eta_r Conv)).
Qed.
Lemma ci_WS_eta_d2 : WS Conv ci_Γd2 fi_eta fi_P.
Proof. exact (weaken_ws_cumul_pbE (Γ := []) ci_Γd2 eq_refl (ci_WS_eta Conv)). Qed.
Lemma ws_cumul_declsE_trans_inst :
  ws_cumul_declsE Conv si_Σ ci_Γd2 (vass si_na (tRel 0)) (vass si_na fi_P).
Proof.
  apply (ws_cumul_declsE_trans (d' := vass si_na fi_eta)).
  - constructor; [reflexivity|exact ci_WS_Rel0_eta_d2].
  - constructor; [reflexivity|exact ci_WS_eta_d2].
Qed.
(** [ci_Γd1] against [ci_Γd2] through [ci_Γd3]: first the let-bodies by the
    η-contraction and the types [Prop] against the β-redex [fi_beta], then the
    types [fi_beta] against its reduct [Prop]. The middle context differs from
    both ends. *)
Lemma ci_ctx_d13 : ws_cumul_ctx_pbE Cumul si_Σ ci_Γd1 ci_Γd3.
Proof.
  constructor; [constructor|].
  constructor; [reflexivity|exact (ci_WS_eta Conv)|exact (fi_WS_beta_r Cumul)].
Qed.
Lemma ci_ctx_d32 : ws_cumul_ctx_pbE Cumul si_Σ ci_Γd3 ci_Γd2.
Proof.
  constructor; [constructor|].
  constructor; [reflexivity|apply ws_cumul_pbE_refl; reflexivity|exact (fi_WS_beta Cumul)].
Qed.
Lemma ws_cumul_ctx_pbE_trans_inst : ws_cumul_ctx_pbE Cumul si_Σ ci_Γd1 ci_Γd2.
Proof. exact (ws_cumul_ctx_pbE_trans Cumul _ _ _ ci_ctx_d13 ci_ctx_d32). Qed.
Lemma context_cumulativity_appE_inst :
  ws_cumul_ctx_pbE Conv si_Σ (ci_Γd1 ,,, [vass si_na (tRel 0)]) (ci_Γd1 ,,, [vass si_na fi_P]).
Proof.
  apply (context_cumulativity_appE (Γ := ci_Γd2) ci_ctx_d).
  constructor; [exact (ws_cumul_ctx_pbE_refl_pb (Γ := ci_Γd2) eq_refl)|].
  constructor; [reflexivity|exact (ci_Rel0_d2 Conv)].
Qed.

(** ** Substitution of convertible terms *)

(** A β-redex, then an η-redex, through [Prop]. *)
Lemma WS_trans_inst : WS Conv [] fi_beta fi_eta.
Proof. exact (PCUICEtaA6.WS_trans (Σ := si_Σ) (wfΣ := si_cb) (fi_WS_beta Conv) (ci_WS_eta_r Conv)). Qed.
Lemma ws_cumul_pbE_subst1_conv_inst : WS Conv [] ((tRel 0) {0 := fi_beta}) ((tRel 0) {0 := fi_P}).
Proof. apply (ws_cumul_pbE_subst1_conv (Γ := []) (c := tRel 0)); [reflexivity|exact (fi_WS_beta Conv)]. Qed.
Lemma ws_cumul_pbE_subst0_conv_inst : WS Conv [] (subst0 [fi_beta] (tRel 0)) (subst0 [fi_P] (tRel 0)).
Proof. apply (ws_cumul_pbE_subst0_conv (Γ := [])); [reflexivity|exact ci_WT|reflexivity]. Qed.

Lemma ci_red_letin_l : si_Σ ;;; [] ⊢ tLetIn si_na fi_beta fi_P (tRel 0) ⇝ fi_P.
Proof.
  split; [reflexivity|reflexivity|].
  eapply rt_trans; [apply rt_step; apply red_zeta|exact fi_red_beta].
Qed.
Lemma ci_red_letin_r : si_Σ ;;; [] ⊢ tLetIn si_na fi_P fi_P fi_P ⇝ fi_P.
Proof. split; [reflexivity|reflexivity|]. apply rt_step. apply red_zeta. Qed.
(** Two let-terms with different bodies, related through their common reduct. *)
Lemma ci_WS_letin : WS Conv [] (tLetIn si_na fi_beta fi_P (tRel 0)) (tLetIn si_na fi_P fi_P fi_P).
Proof.
  apply into_ws_cumul_pbE_red. exists fi_P, fi_P.
  split; [exact ci_red_letin_l|exact ci_red_letin_r|reflexivity].
Qed.
(** The let-codomains [x] and [Prop], in the context [x := (λx:Prop. x) Prop]. *)
Lemma ws_cumul_pbE_LetIn_body_inv_inst : WS Conv ([] ,, vdef si_na fi_beta fi_P) (tRel 0) fi_P.
Proof.
  exact (ws_cumul_pbE_LetIn_body_inv (na' := si_na) (b' := fi_P) (A' := fi_P) (fi_WS_beta Conv) ci_WS_letin).
Qed.
(** Under a let-binder whose body is the substituted variable, the term being that
    variable again: the conclusion relates the η-redex and its contraction. *)
Lemma ws_cumul_pbE_subst_conv_gen_inst :
  WS Conv ([] ,,, subst_context [fi_eta] 0 [vdef si_na (tRel 0) fi_P])
    (subst [fi_eta] 1 (tRel 1)) (subst [fi_P] 1 (tRel 1)).
Proof.
  apply (ws_cumul_pbE_subst_conv_gen (Γ := []) [vdef si_na (tRel 0) fi_P]);
    [reflexivity|exact ci_WT_eta|reflexivity|reflexivity].
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
Lemma eq_terms_ws_cumul_pbE_terms_inst : ws_cumul_pbE_terms si_Σ [] [ci_lam] [ci_lam'].
Proof.
  apply eq_terms_ws_cumul_pbE_terms; [reflexivity|reflexivity|reflexivity|].
  constructor; [exact (ci_eq_lam Conv)|constructor].
Qed.
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

(** ** An environment with a universe constraint *)

(** [si_env], with two bound universe levels and the constraint [l0 = l1]. *)
Definition ci_cstr : UnivConstraint.t := (Level.lvar 0, ConstraintType.Eq, Level.lvar 1).
Definition ci_Σu : global_env_ext :=
  (si_env, Polymorphic_ctx ([nAnon; nAnon], ConstraintSet.singleton ci_cstr)).

Lemma ci_eq_univ :
  eq_universe (global_ext_constraints ci_Σu) (Universe.make' (Level.lvar 0)) (Universe.make' (Level.lvar 1)).
Proof.
  change (eq0_universe (global_ext_constraints ci_Σu) (Universe.make' (Level.lvar 0)) (Universe.make' (Level.lvar 1))).
  intros v hv.
  have hin : ConstraintSet.In ci_cstr (global_ext_constraints ci_Σu).
  { change (ConstraintSet.In ci_cstr (ConstraintSet.union (ConstraintSet.singleton ci_cstr) (global_constraints si_env))).
    apply ConstraintSet.union_spec. left. apply ConstraintSet.singleton_spec. reflexivity. }
  have hs := hv _ hin. unfold ci_cstr in hs. inversion hs; subst.
  rewrite !Universe.val_make'. assumption.
Qed.

(** The constraints of [ci_Σu] are satisfiable: the valuation that sends every
    bound level to [0] satisfies them. So [ci_eq_univ], and every instance below
    that uses it, is not vacuous. *)
Definition ci_val : valuation := {| valuation_mono := fun _ => 1%positive; valuation_poly := fun _ => 0 |}.

Lemma ci_Σu_satisfies : satisfies ci_val (global_ext_constraints ci_Σu).
Proof.
  intros c hc.
  change (ConstraintSet.In c (ConstraintSet.union (ConstraintSet.singleton ci_cstr) (global_constraints si_env))) in hc.
  apply ConstraintSet.union_spec in hc as [hc|hc].
  - apply ConstraintSet.singleton_spec in hc. subst c. unfold ci_cstr. constructor. reflexivity.
  - cbn in hc. now apply ConstraintSet.empty_spec in hc.
Qed.

Lemma ci_Σu_consistent : consistent (global_ext_constraints ci_Σu).
Proof. exists ci_val. exact ci_Σu_satisfies. Qed.

Lemma ci_cmp_inst : cmp_universe_instance (eq_universe (global_ext_constraints ci_Σu)) [Level.lvar 0] [Level.lvar 1].
Proof. constructor; [exact ci_eq_univ|constructor]. Qed.

(** The inductives at the two levels. *)
Lemma conv_indsE_inst :
  ws_cumul_pbE_terms ci_Σu [] (inds (inductive_mind si_ind) [Level.lvar 0] (ind_bodies si_mdecl))
    (inds (inductive_mind si_ind) [Level.lvar 1] (ind_bodies si_mdecl)).
Proof. apply conv_indsE; [exact ci_cmp_inst|reflexivity]. Qed.

(** A context whose type is the universe [l0], at the two instances. *)
Definition ci_Δu : context := [vass si_na (tSort (sType (Universe.make' (Level.lvar 0))))].

Lemma subst_instance_ws_cumul_ctx_pbE_rel_inst :
  ws_cumul_ctx_pbE_rel Cumul ci_Σu [] (subst_instance [Level.lvar 0] ci_Δu) (subst_instance [Level.lvar 1] ci_Δu).
Proof.
  apply (subst_instance_ws_cumul_ctx_pbE_rel (Σ := ci_Σu) (wfΣ := si_cb)); [reflexivity|exact ci_cmp_inst].
Qed.

(** ** The typed lemmas *)

Lemma ci_wf_sort_P : wf_sort si_Σ sProp.
Proof. cbn; trivial. Qed.

Lemma ci_typeE_P (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E fi_P : tSort (Sort.super sProp).
Proof. intros h. apply typeE_Sort; [exact h|exact ci_wf_sort_P]. Qed.

Lemma ci_isTypeE_P (Γ : context) : wf_localE si_Σ Γ -> on_type (lift_typing typingE) si_Σ Γ fi_P.
Proof. intros h. split; [exact tt|]. exists (Sort.super sProp). split; [exact (ci_typeE_P Γ h)|]. split; exact I. Qed.

Lemma ci_vass_P (Γ : context) : wf_localE si_Σ Γ -> lift_typing typingE si_Σ Γ (j_vass si_na fi_P).
Proof. intros h. split; [exact tt|]. exists (Sort.super sProp). split; [exact (ci_typeE_P Γ h)|]. split; [exact I|reflexivity]. Qed.

Lemma ci_vass_s_P (Γ : context) : wf_localE si_Σ Γ -> lift_typing typingE si_Σ Γ (j_vass_s si_na fi_P (Sort.super sProp)).
Proof. intros h. split; [exact tt|]. exists (Sort.super sProp). split; [exact (ci_typeE_P Γ h)|]. split; reflexivity. Qed.

Lemma ci_wf_P (Γ : context) : wf_localE si_Σ Γ -> wf_localE si_Σ (Γ ,, vass si_na fi_P).
Proof. intros h. apply localenv_cons_abs; [exact h|exact (ci_vass_P Γ h)]. Qed.

Lemma ci_wf_Γ1 : wf_localE si_Σ fi_Γ1.
Proof. exact (ci_wf_P [] localenv_nil). Qed.

(** The identity of [Prop], and the proposition [∀P:Prop. P]. *)
Definition ci_id : term := tLambda si_na fi_P (tRel 0).
Definition ci_False : term := tProd si_na fi_P (tRel 0).

Lemma ci_id_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E ci_id : tProd si_na fi_P fi_P.
Proof.
  intros h. unfold ci_id. apply typeE_Lambda; [exact (ci_vass_P Γ h)|].
  exact (typeE_Rel _ _ 0 (vass si_na fi_P) (ci_wf_P Γ h) eq_refl).
Qed.

Lemma ci_Prod_PP_typed (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ |-E tProd si_na fi_P fi_P : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)).
Proof. intros h. apply typeE_Prod; [exact (ci_vass_s_P Γ h)|exact (ci_typeE_P _ (ci_wf_P Γ h))]. Qed.

Lemma ci_app_typed (Γ : context) u : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E u : fi_P ->
  si_Σ ;;; Γ |-E tApp ci_id u : tSort sProp.
Proof.
  intros h hu.
  exact (typeE_App _ _ ci_id si_na fi_P fi_P _ u (ci_Prod_PP_typed Γ h) (ci_id_typed Γ h) hu).
Qed.

Lemma ci_False_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E ci_False : fi_P.
Proof.
  intros h. unfold ci_False.
  exact (typeE_Prod _ _ si_na fi_P (tRel 0) (Sort.super sProp) sProp (ci_vass_s_P Γ h)
           (typeE_Rel _ _ 0 (vass si_na fi_P) (ci_wf_P Γ h) eq_refl)).
Qed.

Lemma ci_on_typeE_Prop (Γ : context) T : si_Σ ;;; Γ |-E T : fi_P -> on_type (lift_typing typingE) si_Σ Γ T.
Proof. intros hT. split; [exact tt|]. exists sProp. split; [exact hT|]. split; exact I. Qed.

Lemma ci_vass_Prop (Γ : context) T : si_Σ ;;; Γ |-E T : fi_P -> lift_typing typingE si_Σ Γ (j_vass si_na T).
Proof. intros hT. split; [exact tt|]. exists sProp. split; [exact hT|]. split; [exact I|reflexivity]. Qed.

Lemma ci_x_typed : si_Σ ;;; fi_Γ1 |-E tRel 0 : fi_P.
Proof. exact (typeE_Rel _ _ 0 (vass si_na fi_P) ci_wf_Γ1 eq_refl). Qed.

Lemma ci_red_id_x : red si_Σ fi_Γ1 (tApp ci_id (tRel 0)) (tRel 0).
Proof. apply rt_step. unfold ci_id. apply red_beta. Qed.

Lemma on_typeE_scoped_inst : is_closed_context ([] : context) × is_open_term ([] : context) fi_P.
Proof. exact (on_typeE_scoped (Σ := si_Σ) (wfΣ := si_wfE) (ci_isTypeE_P [] localenv_nil)). Qed.
Lemma isType_ws_cumul_pbE_refl_inst : WS Cumul fi_Γ1 fi_P fi_P.
Proof. exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) (wfΣ := si_wfE) fi_Γ1 fi_P (ci_isTypeE_P fi_Γ1 ci_wf_Γ1)). Qed.
(** In the context [x : Prop], the types [(λy:Prop. y) x] and [x]. *)
Lemma wt_cumul_pbE_inst : wt_cumul_pbE Cumul si_Σ fi_Γ1 (tApp ci_id (tRel 0)) (tRel 0).
Proof.
  constructor.
  - apply ci_on_typeE_Prop. exact (ci_app_typed fi_Γ1 (tRel 0) ci_wf_Γ1 ci_x_typed).
  - apply ci_on_typeE_Prop. exact ci_x_typed.
  - exact (JoinE_red_l si_Σ fi_Γ1 Cumul _ _ ci_red_id_x).
Qed.
Lemma wt_cumul_pbE_ws_cumul_pbE_inst : WS Cumul fi_Γ1 (tApp ci_id (tRel 0)) (tRel 0).
Proof. exact (wt_cumul_pbE_ws_cumul_pbE (Σ := si_Σ) (wfΣ := si_wfE) wt_cumul_pbE_inst). Qed.

(** The context [x : l0], at the instance [l0], is well formed in [ci_Σu]. *)
Lemma ci_wf_Δu : wf_localE ci_Σu (subst_instance [Level.lvar 0] ci_Δu).
Proof.
  change (wf_localE ci_Σu [vass si_na (subst_instance [Level.lvar 0] (tSort (sType (Universe.make' (Level.lvar 0)))))]).
  apply localenv_cons_abs; [constructor|].
  split; [exact tt|]. eexists. split; [apply typeE_Sort; [constructor|]|].
  - apply/(wf_sort_reflect ci_Σu). reflexivity.
  - split; [exact I|reflexivity].
Qed.

Lemma subst_instance_ws_cumul_ctx_pbE_inst :
  ws_cumul_ctx_pbE Cumul ci_Σu (subst_instance [Level.lvar 0] ci_Δu) (subst_instance [Level.lvar 1] ci_Δu).
Proof.
  exact (subst_instance_ws_cumul_ctx_pbE (Σ := ci_Σu) (wfΣ := si_wfE) (Δ := ci_Δu) Cumul ci_wf_Δu ci_cmp_inst).
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
Proof. exact (red_betas_typedE si_Σ si_wfE [] fi_Γ1 [fi_P] (tRel 0) _ eq_refl ci_x_typed). Qed.
Lemma conv_betasE_inst :
  si_Σ ;;; [] ⊢ mkApps (it_mkLambda_or_LetIn fi_Γ1 (tRel 0)) [fi_P] ≤sE[Conv] subst0 (mk_ctx_subst fi_Γ1 [fi_P]) (tRel 0).
Proof. exact (conv_betasE si_Σ si_cb [] fi_Γ1 [fi_P] (tRel 0) eq_refl eq_refl eq_refl eq_refl). Qed.
Lemma cumul_decls_reflE_inst : cumul_decls (@JoinE _) si_Σ [] [] (vass si_na fi_P) (vass si_na fi_P).
Proof. apply cumul_decls_reflE. Qed.

(** Context cumulativity of a local environment: [x : (λy:Prop. y) (∀P:Prop. P)]
    against [x : ∀P:Prop. P], extended by [z : (λ_:∀P:Prop. P. Prop) x], whose
    type mentions [x]. *)
Definition ci_Γf : context := [vass si_na ci_False].
Definition ci_Γf' : context := [vass si_na (tApp ci_id ci_False)].

Lemma ci_red_False' : red si_Σ [] (tApp ci_id ci_False) ci_False.
Proof. apply rt_step. unfold ci_id. apply red_beta. Qed.

Lemma ci_cumul_ctx_f : cumul_context (@JoinE _) si_Σ ci_Γf' ci_Γf.
Proof.
  constructor; [constructor|]. constructor; [reflexivity|].
  exact (JoinE_red_l si_Σ [] Cumul _ _ ci_red_False').
Qed.

Lemma ci_wf_Γf' : wf_localE si_Σ ci_Γf'.
Proof.
  apply localenv_cons_abs; [constructor|]. apply ci_vass_Prop.
  exact (ci_app_typed [] ci_False localenv_nil (ci_False_typed [] localenv_nil)).
Qed.

(** In every well-formed context cumulative to [ci_Γf], the variable has type
    [∀P:Prop. P]: the declared type is related to it by the cumulativity, which
    [typeE_Cumul] uses after weakening it under the declaration. *)
Lemma ci_x_False_typed_vass na T :
  JoinE si_Σ [] Cumul T ci_False -> wf_localE si_Σ [vass na T] ->
  si_Σ ;;; [vass na T] |-E tRel 0 : ci_False.
Proof.
  intros hj hwf.
  have hT : lift_typing typingE si_Σ [] (j_vass na T).
  { pose proof hwf as hwf'. depelim hwf'. assumption. }
  destruct hT as [_ [s [hTs _]]].
  have hcl : is_closed_context [vass na T] := wf_local_closed_contextE (Σ := si_Σ) (wfΣ := si_wfE) hwf.
  have hF := ci_False_typed _ hwf.
  have hR := typeE_Rel si_Σ [vass na T] 0 (vass na T) hwf eq_refl.
  have hTcl : closedn 0 T := subject_closedE (Σ := si_Σ) (wfΣ := si_wfE) hTs.
  have ws : ws_cumul_pbE Cumul si_Σ [] T ci_False.
  { apply into_ws_cumul_pbE; [exact hj|reflexivity| |reflexivity].
    exact (subject_is_open_termE (Σ := si_Σ) (wfΣ := si_wfE) hTs). }
  have spec : cumulSpecE si_Σ [vass na T] T ci_False :=
    ws_cumul_pbE_forget_spec (Σ := si_Σ) (wfΣ := si_cb)
      (weaken_ws_cumul_pbE (Σ := si_Σ) (wfΣ := si_cb) (Γ := []) [vass na T] hcl ws).
  change (si_Σ ;;; [vass na T] |-E tRel 0 : lift0 1 T) in hR.
  rewrite (lift_closed 1 0 T hTcl) in hR.
  exact (typeE_Cumul _ _ (tRel 0) T ci_False sProp hR hF spec).
Qed.

Lemma ci_x_False_typed (Γ' : context) :
  cumul_context (@JoinE _) si_Σ Γ' ci_Γf -> wf_localE si_Σ Γ' -> si_Σ ;;; Γ' |-E tRel 0 : ci_False.
Proof.
  intros hc hwf.
  unfold ci_Γf, cumul_pb_context in hc. depelim hc.
  match goal with h : All2_fold _ _ [] |- _ => depelim h end.
  unfold cumul_pb_decls in *.
  match goal with h : All_decls_alpha_pb _ _ _ _ |- _ => depelim h end.
  eapply ci_x_False_typed_vass; eassumption.
Qed.

Definition ci_constP : term := tLambda si_na ci_False fi_P.
Definition ci_Δx : context := [vass si_na (tApp ci_constP (tRel 0))].

Lemma ci_wf_sort_super_P : wf_sort si_Σ (Sort.super sProp).
Proof. apply/(wf_sort_reflect si_Σ). reflexivity. Qed.

Lemma ci_Δx_type (Γ' : context) :
  cumul_context (@JoinE _) si_Σ Γ' ci_Γf -> wf_localE si_Σ Γ' ->
  lift_typing typingE si_Σ Γ' (j_vass si_na (tApp ci_constP (tRel 0))).
Proof.
  intros hc hwf.
  have hF := ci_False_typed Γ' hwf.
  have hvF := ci_vass_s_P Γ' hwf.
  have hwfF : wf_localE si_Σ (Γ' ,, vass si_na ci_False).
  { apply localenv_cons_abs; [exact hwf|exact (ci_vass_Prop Γ' ci_False hF)]. }
  have hProd : si_Σ ;;; Γ' |-E tProd si_na ci_False (tSort (Sort.super sProp)) :
      tSort (Sort.sort_of_product sProp (Sort.super (Sort.super sProp))).
  { apply typeE_Prod.
    - split; [exact tt|]. exists sProp. split; [exact hF|]. split; reflexivity.
    - apply typeE_Sort; [exact hwfF|exact ci_wf_sort_super_P]. }
  have hLam : si_Σ ;;; Γ' |-E ci_constP : tProd si_na ci_False (tSort (Sort.super sProp)).
  { unfold ci_constP. apply typeE_Lambda; [exact (ci_vass_Prop Γ' ci_False hF)|].
    exact (ci_typeE_P _ hwfF). }
  split; [exact tt|]. exists (Sort.super sProp). split; [|split; [exact I|reflexivity]].
  exact (typeE_App _ _ ci_constP si_na ci_False (tSort (Sort.super sProp)) _ (tRel 0)
           hProd hLam (ci_x_False_typed Γ' hc hwf)).
Qed.

Lemma context_cumulativity_wf_appE_inst : wf_localE si_Σ (ci_Γf' ,,, ci_Δx).
Proof.
  apply (context_cumulativity_wf_appE si_Σ ci_Γf ci_Γf' ci_Δx);
    [exact ci_cumul_ctx_f|exact ci_wf_Γf'|].
  change (ci_Γf ,,, ci_Δx) with [vass si_na (tApp ci_constP (tRel 0)); vass si_na ci_False].
  apply localenv_cons_abs; [apply localenv_cons_abs; [constructor|]|].
  - intros Γ'' _ wf''. exact (ci_vass_Prop Γ'' ci_False (ci_False_typed Γ'' wf'')).
  - intros Γ'' hc wf''. exact (ci_Δx_type Γ'' hc wf'').
Qed.

(** ** The typing lemmas of the refutation's witness *)

Lemma rf_P_typed_inst : rf_Σ ;;; rf_Γ |-E tSort sProp : tSort (Sort.super sProp).
Proof. exact (rf_P_typed rf_Γ rf_wf_Γ). Qed.
Lemma rf_P_vass_inst : lift_typing typingE rf_Σ rf_Γ (j_vass c1b_na (tSort sProp)).
Proof. exact (rf_P_vass rf_Γ rf_wf_Γ). Qed.
Lemma rf_F_typed_inst :
  rf_Σ ;;; rf_Γ |-E rf_F : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)).
Proof. exact (rf_F_typed rf_Γ rf_wf_Γ). Qed.
