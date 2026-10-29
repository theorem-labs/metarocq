(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the hypotheses of the A1, A5, A7 and K6 lemmas

  Each lemma of A1 ([PCUICWellScopedCumulativityEta]), A5
  ([PCUICConversionEtaCongr]), A7 ([PCUICWsCumulEtaSubst]) and K6
  ([PCUICEtaK6EtaStep]) whose premises are more than [ClosedBodies] and scoping is
  applied here to a concrete instance, with every premise proved. The environment
  is [si_Σ] of [PCUICCumulativitySpecEtaClosureInstances]
  ([Inductive I (A : Prop) : Prop := c : I A]; [si_cb]), and the terms are
  closed: [fi_P := tSort sProp], a β-redex, an η-redex, a case on [I], an empty
  fixpoint, an empty array. *)

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Primitive.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive PCUICLiftSubst PCUICSigmaCalculus PCUICEquality
     PCUICReduction PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICWellScopedCumulativity PCUICSubstitution PCUICSpine
     PCUICEtaDefs PCUICEtaCanon PCUICEtaFInst PCUICEtaFInstEquiv PCUICEtaI5 PCUICEtaI5Trans
     PCUICEtaI5A2 PCUICEtaI5EtaL PCUICEtaK6EtaStep
     PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICWsCumulEtaSubst
     PCUICCumulativitySpecEtaClosureInstances PCUICClosedBodies.

#[local] Existing Instance default_checker_flags.

Local Notation WS pb Γ := (ws_cumul_pbE pb si_Σ Γ).
Local Notation J Γ pb := (JoinE si_Σ Γ pb).

Definition fi_P : term := tSort sProp.
Definition fi_Γ1 : context := [vass si_na fi_P].
Definition fi_beta : term := tApp (tLambda si_na fi_P (tRel 0)) fi_P.
Definition fi_eta : term := tLambda si_na fi_P (tApp (lift0 1 fi_P) (tRel 0)).

Lemma fi_ws pb Γ t : is_closed_context Γ -> is_open_term Γ t -> WS pb Γ t t.
Proof. intros h1 h2. eapply ws_cumul_pbE_refl; [exact h1|exact h2]. Qed.

Ltac fi_ws := apply fi_ws; reflexivity.

Lemma fi_red_beta : red si_Σ [] fi_beta fi_P.
Proof. apply rt_step. exact (red_beta si_Σ [] si_na fi_P (tRel 0) fi_P). Qed.

Lemma fi_closed_red_beta : si_Σ ;;; [] ⊢ fi_beta ⇝ fi_P.
Proof. split; [reflexivity|reflexivity|exact fi_red_beta]. Qed.

Lemma fi_eta1 : eta1 fi_eta fi_P.
Proof. exact (eta_red si_na fi_P fi_P). Qed.

Lemma fi_J_beta pb : J [] pb fi_beta fi_P.
Proof. exact (JoinE_red_l si_Σ [] pb _ _ fi_red_beta). Qed.
Lemma fi_J_beta_r pb : J [] pb fi_P fi_beta.
Proof. exact (JoinE_red_r si_Σ [] pb _ _ fi_red_beta). Qed.
Lemma fi_WS_beta pb : WS pb [] fi_beta fi_P.
Proof. constructor; [reflexivity|reflexivity|reflexivity|exact (fi_J_beta pb)]. Qed.
Lemma fi_WS_beta_r pb : WS pb [] fi_P fi_beta.
Proof. constructor; [reflexivity|reflexivity|reflexivity|exact (fi_J_beta_r pb)]. Qed.
Lemma fi_spec_refl pb : si_Σ ;;; [] ⊢ fi_P ≤sE[pb] fi_P.
Proof.
  exact (I5_join_to_spec si_Σ si_cb [] pb fi_P fi_P eq_refl eq_refl eq_refl (JoinE_refl si_Σ [] pb fi_P)).
Qed.

(** Closes every premise the instances below leave: [ClosedBodies] and [wf], the β-
    and η-facts, reflexive comparisons, scoping by computation, empty lists. *)
Ltac fi_solve :=
  repeat match goal with
  | |- wf _ => exact si_wf
  | |- ClosedBodies _ => exact si_cb
  | |- ws_cumul_pbE _ _ _ fi_beta fi_P => exact (fi_WS_beta _)
  | |- ws_cumul_pbE _ _ _ fi_P fi_beta => exact (fi_WS_beta_r _)
  | |- ws_cumul_pbE _ _ _ ?t ?t => apply fi_ws; reflexivity
  | |- JoinE _ _ _ fi_beta fi_P => exact (fi_J_beta _)
  | |- JoinE _ _ _ fi_P fi_beta => exact (fi_J_beta_r _)
  | |- JoinE _ _ _ ?t ?t => apply JoinE_refl
  | |- red _ _ fi_beta fi_P => exact fi_red_beta
  | |- _ ;;; _ ⊢ fi_beta ⇝ fi_P => exact fi_closed_red_beta
  | |- eta1 fi_eta fi_P => exact fi_eta1
  | |- _ ;;; _ ⊢ fi_P ≤sE[_] fi_P => exact (fi_spec_refl _)
  | |- _ ;;; _ ⊢ ?t ≤[_] ?t => apply ws_cumul_pb_refl; reflexivity
  | |- cumul_Ind_univ _ _ _ _ _ _ => apply si_cumul_Ind_univ
  | |- cumul_Construct_univ _ _ _ _ _ _ _ => apply si_cumul_Construct_univ
  | |- eq_binder_annot _ _ => exact eq_refl
  | |- is_true _ => reflexivity
  | |- _ => first [reflexivity | constructor]
  end.

(** ** A1 *)

Lemma JoinE_red_l_inst : J [] Conv fi_beta fi_P.
Proof. exact (JoinE_red_l si_Σ [] Conv _ _ fi_red_beta). Qed.
Lemma JoinE_red_r_inst : J [] Conv fi_P fi_beta.
Proof. exact (JoinE_red_r si_Σ [] Conv _ _ fi_red_beta). Qed.
Lemma JoinE_eta1_l_inst : J [] Conv fi_eta fi_P.
Proof. exact (JoinE_eta1_l si_Σ [] Conv _ _ fi_eta1). Qed.
Lemma JoinE_eta1_r_inst : J [] Conv fi_P fi_eta.
Proof. exact (JoinE_eta1_r si_Σ [] Conv _ _ fi_eta1). Qed.

Lemma ws_cumul_pbE_forget_inst : J [] Cumul fi_P fi_P.
Proof. unshelve eapply ws_cumul_pbE_forget; fi_solve. Qed.
Lemma ws_cumul_pbE_forget_spec_inst : si_Σ ;;; [] ⊢ fi_P ≤sE[Cumul] fi_P.
Proof. unshelve eapply ws_cumul_pbE_forget_spec; fi_solve. Qed.
Lemma ws_cumul_pbE_is_open_term_inst :
  [&& is_closed_context ([] : context), is_open_term ([] : context) fi_P & is_open_term ([] : context) fi_P].
Proof. exact (ws_cumul_pbE_is_open_term (fi_ws Cumul [] fi_P eq_refl eq_refl)). Qed.
Lemma into_ws_cumul_pbE_inst : WS Conv [] fi_beta fi_P.
Proof. unshelve eapply into_ws_cumul_pbE; fi_solve. Qed.
Lemma into_ws_cumul_pbE_spec_inst : WS Cumul [] fi_P fi_P.
Proof. unshelve eapply into_ws_cumul_pbE_spec; fi_solve. Qed.
Lemma ws_cumul_pbE_spec_iff_inst :
  [× is_closed_context ([] : context), is_open_term ([] : context) fi_P, is_open_term ([] : context) fi_P & si_Σ ;;; [] ⊢ fi_P ≤sE[Cumul] fi_P].
Proof. unshelve eapply ws_cumul_pbE_spec_iff; fi_solve. Qed.
Lemma ws_cumul_pb_incl_E_inst : WS Cumul [] fi_P fi_P.
Proof. unshelve eapply ws_cumul_pb_incl_E; fi_solve. Qed.
Lemma ws_cumul_pbE_sym_pb_inst : WS Cumul [] fi_P fi_beta.
Proof. unshelve eapply ws_cumul_pbE_sym_pb; fi_solve. Qed.
Lemma ws_cumul_pbE_sym_inst : WS Conv [] fi_P fi_beta.
Proof. symmetry. exact into_ws_cumul_pbE_inst. Qed.
Lemma ws_cumul_pbE_trans_inst : WS Conv [] fi_beta fi_eta.
Proof.
  have h2 : WS Conv [] fi_P fi_eta by (unshelve eapply eta1_ws_cumul_pbE_inv; fi_solve).
  exact (ws_cumul_pbE_trans (Σ := si_Σ) (wfΣ := si_cb) _ _ _ (fi_WS_beta Conv) h2).
Qed.
Lemma ws_cumul_eq_pbE_inst : WS Cumul [] fi_beta fi_P.
Proof. unshelve eapply ws_cumul_eq_pbE; fi_solve. Qed.
Lemma red_ws_cumul_pbE_inst : WS Cumul [] fi_beta fi_P.
Proof. unshelve eapply red_ws_cumul_pbE; fi_solve. Qed.
Lemma red_ws_cumul_pbE_inv_inst : WS Cumul [] fi_P fi_beta.
Proof. unshelve eapply red_ws_cumul_pbE_inv; fi_solve. Qed.
Lemma red_ws_cumul_pbE_left_inst : WS Cumul [] fi_beta fi_P.
Proof. unshelve eapply (red_ws_cumul_pbE_left (u := fi_P)); fi_solve. Qed.
Lemma red_ws_cumul_pbE_right_inst : WS Cumul [] fi_P fi_beta.
Proof. unshelve eapply (red_ws_cumul_pbE_right (u := fi_P)); fi_solve. Qed.
Lemma eta1_ws_cumul_pbE_inst : WS Cumul [] fi_eta fi_P.
Proof. unshelve eapply eta1_ws_cumul_pbE; fi_solve. Qed.
Lemma eta1_ws_cumul_pbE_inv_inst : WS Cumul [] fi_P fi_eta.
Proof. unshelve eapply eta1_ws_cumul_pbE_inv; fi_solve. Qed.

(** ** A5 *)

Lemma fi_WT : ws_cumul_pbE_terms si_Σ [] [fi_P] [fi_P].
Proof. constructor; [fi_ws|constructor]. Qed.

Lemma ws_cumul_pbE_Sort_inst : WS Conv [] (tSort sProp) (tSort sProp).
Proof. unshelve eapply ws_cumul_pbE_Sort; fi_solve. Qed.
Lemma ws_cumul_pbE_Const_inst : WS Conv [] (tConst si_kn []) (tConst si_kn []).
Proof. unshelve eapply ws_cumul_pbE_Const; fi_solve. Qed.
Lemma ws_cumul_pbE_Evar_inst : WS Conv [] (tEvar 0 [fi_P]) (tEvar 0 [fi_P]).
Proof. unshelve eapply ws_cumul_pbE_Evar; fi_solve. Qed.
Lemma ws_cumul_pbE_App_inst : WS Conv [] (tApp fi_beta fi_P) (tApp fi_P fi_P).
Proof. unshelve eapply ws_cumul_pbE_App; fi_solve. Qed.
Lemma ws_cumul_pbE_App_l_inst : WS Conv [] (tApp fi_beta fi_P) (tApp fi_P fi_P).
Proof. unshelve eapply ws_cumul_pbE_App_l; fi_solve. Qed.
Lemma ws_cumul_pbE_App_r_inst : WS Conv [] (tApp fi_P fi_beta) (tApp fi_P fi_P).
Proof. unshelve eapply ws_cumul_pbE_App_r; fi_solve. Qed.
Lemma ws_cumul_pbE_mkApps_inst : WS Conv [] (mkApps fi_beta [fi_P]) (mkApps fi_P [fi_P]).
Proof. unshelve eapply ws_cumul_pbE_mkApps; fi_solve. Qed.
Lemma ws_cumul_pbE_mkApps_weak_inst : WS Conv [] (mkApps fi_beta [fi_P]) (mkApps fi_P [fi_P]).
Proof. unshelve eapply ws_cumul_pbE_mkApps_weak; fi_solve. Qed.
Lemma ws_cumul_pbE_Proj_c_inst p : WS Conv [] (tProj p fi_beta) (tProj p fi_P).
Proof. unshelve eapply ws_cumul_pbE_Proj_c; fi_solve. Qed.
Lemma ws_cumul_pbE_Prod_inst : WS Cumul [] (tProd si_na fi_beta fi_P) (tProd si_na fi_P fi_P).
Proof. unshelve eapply ws_cumul_pbE_Prod; fi_solve. Qed.
Lemma ws_cumul_pbE_Prod_l_inst : WS Cumul [] (tProd si_na fi_beta fi_P) (tProd si_na fi_P fi_P).
Proof. unshelve eapply ws_cumul_pbE_Prod_l; fi_solve. Qed.
Lemma ws_cumul_pbE_Prod_r_inst : WS Cumul [] (tProd si_na fi_P fi_P) (tProd si_na fi_P fi_P).
Proof. unshelve eapply ws_cumul_pbE_Prod_r; fi_solve. Qed.
Lemma ws_cumul_pbE_Lambda_inst : WS Cumul [] (tLambda si_na fi_P fi_P) (tLambda si_na (tSort (Sort.super sProp)) fi_P).
Proof. unshelve eapply ws_cumul_pbE_Lambda; fi_solve. Qed.
Lemma ws_cumul_pbE_Lambda_l_inst : WS Cumul [] (tLambda si_na fi_P fi_P) (tLambda si_na (tSort (Sort.super sProp)) fi_P).
Proof. unshelve eapply ws_cumul_pbE_Lambda_l; fi_solve. Qed.
Lemma ws_cumul_pbE_Lambda_r_inst : WS Cumul [] (tLambda si_na fi_P fi_P) (tLambda si_na fi_P fi_P).
Proof. unshelve eapply ws_cumul_pbE_Lambda_r; fi_solve. Qed.
Lemma ws_cumul_pbE_eta_l_inst : WS Cumul [] fi_eta fi_P.
Proof. unshelve eapply ws_cumul_pbE_eta_l; fi_solve. Qed.
Lemma ws_cumul_pbE_eta_r_inst : WS Cumul [] fi_P fi_eta.
Proof. unshelve eapply ws_cumul_pbE_eta_r; fi_solve. Qed.
Lemma ws_cumul_pbE_LetIn_inst : WS Cumul [] (tLetIn si_na fi_P fi_P fi_P) (tLetIn si_na fi_P fi_P fi_P).
Proof. unshelve eapply ws_cumul_pbE_LetIn; fi_solve. Qed.
Lemma ws_cumul_pbE_LetIn_bo_inst : WS Cumul [] (tLetIn si_na fi_P fi_P fi_P) (tLetIn si_na fi_P fi_P fi_P).
Proof. unshelve eapply ws_cumul_pbE_LetIn_bo; fi_solve. Qed.
Lemma ws_cumul_pbE_LetIn_tm_inst : WS Cumul [] (tLetIn si_na fi_beta fi_P fi_P) (tLetIn si_na fi_P fi_P fi_P).
Proof. unshelve eapply ws_cumul_pbE_LetIn_tm; fi_solve. Qed.
Lemma ws_cumul_pbE_LetIn_ty_inst : WS Cumul [] (tLetIn si_na fi_P fi_beta fi_P) (tLetIn si_na fi_P fi_P fi_P).
Proof. unshelve eapply ws_cumul_pbE_LetIn_ty; fi_solve. Qed.
Lemma ws_cumul_pbE_Ind_inst : WS Cumul [] (mkApps (tInd si_ind []) [fi_P]) (mkApps (tInd si_ind []) [fi_P]).
Proof. unshelve eapply ws_cumul_pbE_Ind; fi_solve. Qed.
Lemma ws_cumul_pbE_Construct_inst :
  WS Cumul [] (mkApps (tConstruct si_ind 0 []) [fi_P]) (mkApps (tConstruct si_ind 0 []) [fi_P]).
Proof. unshelve eapply ws_cumul_pbE_Construct; fi_solve. Qed.

Definition fi_arr : array_model term :=
  {| array_level := Level.lzero; array_value := []; array_default := fi_P; array_type := fi_P |}.
Lemma ws_cumul_pbE_Prim_inst :
  WS Cumul [] (tPrim (primArray; primArrayModel fi_arr)) (tPrim (primArray; primArrayModel fi_arr)).
Proof. unshelve eapply ws_cumul_pbE_Prim; fi_solve. Qed.

Definition fi_ci : case_info := {| ci_ind := si_ind; ci_npar := 1; ci_relevance := Relevant |}.
Definition fi_p : predicate term := {| pparams := [fi_P]; puinst := []; pcontext := []; preturn := fi_P |}.

Lemma ws_cumul_pbE_Case_inst : WS Cumul [] (tCase fi_ci fi_p fi_beta []) (tCase fi_ci fi_p fi_P []).
Proof. unshelve eapply ws_cumul_pbE_Case; fi_solve. Qed.
Lemma ws_cumul_pbE_Case_c_inst : WS Cumul [] (tCase fi_ci fi_p fi_beta []) (tCase fi_ci fi_p fi_P []).
Proof. unshelve eapply ws_cumul_pbE_Case_c; fi_solve. Qed.
Lemma ws_cumul_pbE_Case_brs_inst : WS Cumul [] (tCase fi_ci fi_p fi_P []) (tCase fi_ci fi_p fi_P []).
Proof. unshelve eapply ws_cumul_pbE_Case_brs; fi_solve. Qed.
Lemma ws_cumul_pbE_Case_p_inst : WS Cumul [] (tCase fi_ci fi_p fi_P []) (tCase fi_ci fi_p fi_P []).
Proof. unshelve eapply ws_cumul_pbE_Case_p; fi_solve. Qed.
Lemma ws_cumul_pbE_Fix_inst : WS Cumul [] (tFix [] 0) (tFix [] 0).
Proof. unshelve eapply ws_cumul_pbE_Fix; fi_solve. Qed.
Lemma ws_cumul_pbE_CoFix_inst : WS Cumul [] (tCoFix [] 0) (tCoFix [] 0).
Proof. unshelve eapply ws_cumul_pbE_CoFix; fi_solve. Qed.
Lemma ws_cumul_pbE_mkLambda_or_LetIn_codom_inst :
  WS Cumul [] (mkLambda_or_LetIn (vass si_na fi_P) fi_P) (mkLambda_or_LetIn (vass si_na fi_P) fi_P).
Proof. unshelve eapply ws_cumul_pbE_mkLambda_or_LetIn_codom; fi_solve. Qed.
Lemma ws_cumul_pbE_it_mkLambda_or_LetIn_codom_inst :
  WS Cumul [] (it_mkLambda_or_LetIn fi_Γ1 fi_P) (it_mkLambda_or_LetIn fi_Γ1 fi_P).
Proof. unshelve eapply ws_cumul_pbE_it_mkLambda_or_LetIn_codom; fi_solve. Qed.
Lemma ws_cumul_pbE_it_mkProd_or_LetIn_codom_conv_inst :
  WS Cumul [] (it_mkProd_or_LetIn fi_Γ1 fi_P) (it_mkProd_or_LetIn fi_Γ1 fi_P).
Proof. unshelve eapply ws_cumul_pbE_it_mkProd_or_LetIn_codom_conv; fi_solve. Qed.
Lemma ws_cumul_pbE_it_mkProd_or_LetIn_codom_inst :
  WS Cumul [] (it_mkProd_or_LetIn fi_Γ1 fi_P) (it_mkProd_or_LetIn fi_Γ1 fi_P).
Proof. unshelve eapply ws_cumul_pbE_it_mkProd_or_LetIn_codom; fi_solve. Qed.

(** ** A7 *)

Lemma finst_inst_inst σ : eq_term_upto_univ_eta_napp si_Σ.1 (compare_universe si_Σ) (compare_sort si_Σ) Conv 0
  fi_beta.[σ] fi_beta.[σ].
Proof. apply finst_inst. apply compare_term_eta_refl. Qed.
Lemma finst_subst_inst : eq_term_upto_univ_eta_napp si_Σ.1 (compare_universe si_Σ) (compare_sort si_Σ) Conv 0
  (subst [fi_P] 0 (tRel 0)) (subst [fi_P] 0 (tRel 0)).
Proof. apply finst_subst. apply compare_term_eta_refl. Qed.
Lemma finst_lift_inst : eq_term_upto_univ_eta_napp si_Σ.1 (compare_universe si_Σ) (compare_sort si_Σ) Conv 0
  (lift 1 0 (tRel 0)) (lift 1 0 (tRel 0)).
Proof. apply finst_lift. apply compare_term_eta_refl. Qed.

Lemma JoinE_map_inst : J [] Conv fi_beta fi_P.
Proof.
  eapply (JoinE_map si_Σ si_Σ si_cb [] [] (fun x => x)); try reflexivity.
  - intros x y _ h. apply rt_step. exact h.
  - intros x y h. exact h.
  - intros x y e. exact e.
  - intros x y e. exact (RF_canon si_Σ _ _ _ _ e).
  - exact JoinE_red_l_inst.
Qed.

Lemma untyped_substitution_ws_cumul_pbE_inst : WS Cumul [] (subst [fi_P] 0 (tRel 0)) (subst [fi_P] 0 (tRel 0)).
Proof.
  unshelve eapply (untyped_substitution_ws_cumul_pbE (Γ := []) (Δ := [vass si_na fi_P]) (Γ'' := []) (s := [fi_P]));
    fi_solve.
Qed.
Lemma substitution_ws_cumul_pbE_inst : WS Cumul [] (subst [] 0 fi_P) (subst [] 0 fi_P).
Proof.
  unshelve eapply (substitution_ws_cumul_pbE (Γ := []) (Δ := []) (Γ'' := []) (s := [])); fi_solve.
Qed.
Lemma substitution0_ws_cumul_pbE_inst : WS Cumul [] ((tRel 0) {0 := fi_P}) ((tRel 0) {0 := fi_P}).
Proof. unshelve eapply (substitution0_ws_cumul_pbE (na := si_na) (T := fi_P)); fi_solve. Qed.
Lemma substitution0_ws_cumul_pbE_vdef_inst : WS Cumul [] ((tRel 0) {0 := fi_P}) ((tRel 0) {0 := fi_P}).
Proof. unshelve eapply (substitution0_ws_cumul_pbE_vdef (na := si_na) (T := fi_P)); fi_solve. Qed.
Lemma weakening_ws_cumul_pbE_inst :
  WS Cumul ([] ,,, fi_Γ1 ,,, lift_context #|fi_Γ1| 0 []) (lift #|fi_Γ1| #|[] : context| fi_P) (lift #|fi_Γ1| #|[] : context| fi_P).
Proof. unshelve eapply (weakening_ws_cumul_pbE (Γ := []) (Γ' := []) (Γ'' := fi_Γ1)); fi_solve. Qed.
Lemma ws_cumul_pbE_LetIn_bo_pb_inst : WS Cumul [] (tLetIn si_na fi_P fi_P fi_P) (tLetIn si_na fi_P fi_P fi_P).
Proof. unshelve eapply ws_cumul_pbE_LetIn_bo_pb; fi_solve. Qed.
Lemma ws_cumul_pbE_LetIn_pb_inst : WS Cumul [] (tLetIn si_na fi_P fi_P fi_P) (tLetIn si_na fi_P fi_P fi_P).
Proof. unshelve eapply ws_cumul_pbE_LetIn_pb; fi_solve. Qed.
Lemma ws_cumul_pbE_it_mkProd_or_LetIn_codom_pb_inst :
  WS Cumul [] (it_mkProd_or_LetIn [vdef si_na fi_P fi_P] fi_P) (it_mkProd_or_LetIn [vdef si_na fi_P fi_P] fi_P).
Proof. unshelve eapply ws_cumul_pbE_it_mkProd_or_LetIn_codom_pb; fi_solve. Qed.

Lemma eta1_subst_instance_inst : eta1 (subst_instance [] fi_eta) (subst_instance [] fi_P).
Proof. apply eta1_subst_instance. exact fi_eta1. Qed.

Lemma fi_valid_empty : valid_constraints ConstraintSet.empty (subst_instance_cstrs [] ConstraintSet.empty).
Proof.
  unfold valid_constraints; cbn. intros v _ c Hc. exfalso.
  change (ConstraintSet.In c ConstraintSet.empty) in Hc.
  eapply ConstraintSet.empty_spec. exact Hc.
Qed.

Lemma finst_subst_instance_inst :
  eq_term_upto_univ_eta_napp si_Σ.1 (compare_universe ConstraintSet.empty) (compare_sort ConstraintSet.empty) Conv 0
    (subst_instance [] fi_beta) (subst_instance [] fi_beta).
Proof.
  apply (finst_subst_instance si_Σ.1 ConstraintSet.empty ConstraintSet.empty [] fi_valid_empty).
  apply compare_term_eta_refl.
Qed.

(** [si_Σ] has no universe constraints, so instantiating at the empty instance keeps
    every constraint valid. *)
Lemma fi_valid_si :
  valid_constraints (global_ext_constraints (si_Σ.1, Monomorphic_ctx))
    (subst_instance_cstrs [] (global_ext_constraints si_Σ)).
Proof.
  unfold valid_constraints; cbn. intros v _ c Hc. exfalso.
  vm_compute in Hc. inversion Hc.
Qed.

Lemma subst_instance_ws_cumul_pbE_inst :
  ws_cumul_pbE Cumul (si_Σ.1, Monomorphic_ctx) (subst_instance [] []) (subst_instance [] fi_P) (subst_instance [] fi_P).
Proof.
  apply (subst_instance_ws_cumul_pbE (Σ := si_Σ) (wfΣ := si_cb) Monomorphic_ctx []).
  - exact fi_valid_si.
  - fi_ws.
Qed.

(** ** K6 *)

Definition fi_t : term := tApp (lift0 1 fi_P) (tRel 0).

Lemma K6_eta_step_inst : si_Σ ;;; [] ⊢ tLambda si_na fi_P fi_t ≤sE[Cumul] fi_P.
Proof.
  eapply (K6_eta_step si_Σ si_cb [] Cumul si_na fi_P fi_t fi_P); try reflexivity.
  apply JoinE_refl.
Qed.

Lemma K6_eta_step_join_inst : J [] Cumul (tLambda si_na fi_P fi_t) fi_P.
Proof.
  eapply (K6_eta_step_join si_Σ si_cb [] Cumul si_na fi_P fi_t fi_P); try reflexivity.
  apply JoinE_refl.
Qed.
