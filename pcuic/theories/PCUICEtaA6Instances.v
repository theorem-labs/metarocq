(* Distributed under the terms of the MIT license. *)

(** * BET-315 eta lane: proved satisfying instances (FRAC practice) for A6 and A8

  Each lemma of [PCUICEtaA6.v], [PCUICEtaA6Ind.v], [PCUICEtaA6More.v] and
  [PCUICContextConversionEta.v] whose conclusion is not [False] is applied here to
  a concrete instance with every premise proved: S4's environment [si_Σ] (an
  inductive, [si_cb]) or the one-axiom environment [sa_Σ] ([sa_wf]), the rule
  [FInstFollowKernel], closed terms.

  The lemmas that conclude [False] (head clashes: [finst_Sort_Prod],
  [finst_Prod_Sort], [ws_cumul_pbE_Sort_Prod_inv], [ws_cumul_pbE_Prod_Sort_inv],
  [invert_cumul_prod_indE], [invert_cumul_ind_prodE], [invert_cumul_sort_indE],
  [invert_cumul_ind_sortE], [invert_cumul_axiom_indE], [invert_cumul_axiom_prodE],
  [invert_cumul_it_mkProd_or_LetIn_Sort_IndE], [invert_cumul_prim_type_indE],
  [invert_cumul_prim_type_prodE], [mkApps_rigid_not_Prod], [mkApps_rigid_not_Sort],
  [eta_normal_Ind], [eta_normal_Const]) have, by design, no satisfying instance of
  their premises: each IS the statement that the premises are jointly
  unsatisfiable. C4-side. *)

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICEquality PCUICReduction
     PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICWellScopedCumulativity PCUICConversion PCUICContextConversion
     PCUICEtaDefs PCUICEtaCanon PCUICEtaCanonRed PCUICEtaFInst PCUICEtaFInstEquiv PCUICEtaI5 PCUICEtaI5Trans
     PCUICEtaI5A2 PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICWsCumulEtaSubst
     PCUICCumulativitySpecEtaClosureInstances PCUICEtaFracInstances
     PCUICEtaA6 PCUICEtaA6Ind PCUICEtaA6More PCUICContextConversionEta.

#[local] Existing Instance default_checker_flags.

Local Notation r := FInstFollowKernel.

(** ** A one-axiom environment *)

Definition sa_kn : kername := (MPfile ["SInst"], "A").
Definition sa_cb : constant_body :=
  {| cst_type := tSort sProp; cst_body := None; cst_universes := Monomorphic_ctx; cst_relevance := Relevant |}.
Definition sa_env : global_env :=
  {| universes := ContextSet.empty; declarations := [(sa_kn, ConstantDecl sa_cb)];
     retroknowledge := Retroknowledge.empty |}.
Definition sa_Σ : global_env_ext := (sa_env, Monomorphic_ctx).

Lemma sa_wf : wf sa_env.
Proof.
  split.
  - split; [|split].
    + intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
    + intros x Hx.
      change (LevelSet.In x (LevelSet.union (ContextSet.levels ContextSet.empty)
                                            (LevelSet.singleton Level.lzero))) in Hx.
      apply LevelSet.union_spec in Hx as [Hx|Hx].
      * exfalso. eapply LevelSet.empty_spec. exact Hx.
      * apply LevelSet.singleton_spec in Hx. hnf in Hx. subst x. reflexivity.
    + exists si_val. intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
  - (* trunk's wf: the retroknowledge conjunct, then the declarations *)
    split.
    { constructor; cbn; [constructor|intros c []|repeat split; intros c h; discriminate h
                        |intros i h; discriminate h]. }
    apply globenv_decl; [constructor|].
    constructor.
    + constructor.
    + exact si_on_udecl.
    + exact (si_vass [] (mkBindAnn nAnon Relevant) (tSort sProp) _ (si_P_typed [] si_wf_nil) eq_refl).
    + (* on_prim_decl: no operation is registered *)
      cbn. intros op h; discriminate h.
Qed.

(** [sa_wf] gives the confluence spine's premise ([PCUICClosedBodies]), which the η
    chain takes in place of [wf] (W-c). *)
Definition sa_cb : ClosedBodies sa_env := @wf_ClosedBodies _ sa_env sa_wf.
#[local] Existing Instance sa_cb.

Lemma sa_declared : declared_constant sa_Σ sa_kn sa_cb.
Proof. cbn. first [reflexivity | now left]. Qed.

Definition sa_ax : term := tConst sa_kn [].

(** ** Facts the instances use *)

Local Notation WS pb Γ := (ws_cumul_pbE r pb si_Σ Γ).
Local Notation WSa pb Γ := (ws_cumul_pbE r pb sa_Σ Γ).

Lemma sa_ws pb Γ t : is_closed_context Γ -> is_open_term Γ t -> WSa pb Γ t t.
Proof. intros h1 h2. eapply ws_cumul_pbE_refl; [exact h1|exact h2]. Qed.

Definition fi_Γb : context := [vass si_na fi_beta].

Lemma fi_ctx_P_beta : ws_cumul_ctx_pbE r Conv si_Σ fi_Γ1 fi_Γb.
Proof. constructor; [constructor|]. constructor; [reflexivity|exact (fi_WS_beta_r Conv)]. Qed.

Lemma fi_red_ctx : si_Σ ⊢ fi_Γb ⇝ fi_Γ1.
Proof. constructor; [constructor|]. constructor. exact fi_closed_red_beta. Qed.

Lemma fi_Prod_eta1 : eta1 (tProd si_na fi_eta fi_P) (tProd si_na fi_P fi_P).
Proof. apply prod_eta_l. exact fi_eta1. Qed.

Lemma fi_App_eta1 : eta1 (tApp (tInd si_ind []) fi_eta) (tApp (tInd si_ind []) fi_P).
Proof. apply app_eta_r. exact fi_eta1. Qed.

Lemma fi_LetIn_eta1 : eta1 (tLetIn si_na fi_eta fi_P fi_P) (tLetIn si_na fi_P fi_P fi_P).
Proof. apply letin_eta_def. exact fi_eta1. Qed.

Definition fi_prim_cb : constant_body :=
  {| cst_type := tSort Sort.type0; cst_body := None; cst_universes := Monomorphic_ctx; cst_relevance := Relevant |}.

Lemma fi_J_Prod pb : JoinE r si_Σ [] pb (tProd si_na fi_beta fi_P) (tProd si_na fi_P fi_P).
Proof. apply JoinE_red_l. apply rt_step. apply prod_red_l. exact (red_beta _ _ si_na fi_P (tRel 0) fi_P). Qed.

Lemma fi_J_LetIn pb : JoinE r si_Σ [] pb (tLetIn si_na fi_P fi_P fi_P) fi_P.
Proof. apply JoinE_red_l. apply rt_step. exact (red_zeta _ _ si_na fi_P fi_P fi_P). Qed.
Lemma fi_J_LetIn_r pb : JoinE r si_Σ [] pb fi_P (tLetIn si_na fi_P fi_P fi_P).
Proof. apply JoinE_red_r. apply rt_step. exact (red_zeta _ _ si_na fi_P fi_P fi_P). Qed.

Ltac a6_solve :=
  repeat match goal with
  | |- wf _ => first [exact si_wf | exact sa_wf]
  | |- ClosedBodies _ => first [exact si_cb | exact sa_cb]
  | |- declared_constant sa_Σ _ _ => exact sa_declared
  | |- cst_body sa_cb = None => reflexivity
  | |- ws_cumul_pbE _ _ si_Σ _ fi_beta fi_P => exact (fi_WS_beta _)
  | |- ws_cumul_pbE _ _ si_Σ _ fi_P fi_beta => exact (fi_WS_beta_r _)
  | |- ws_cumul_pbE _ _ si_Σ _ _ _ => apply fi_ws; reflexivity
  | |- ws_cumul_pbE _ _ sa_Σ _ _ _ => apply sa_ws; reflexivity
  | |- JoinE _ _ _ _ (tProd si_na fi_beta fi_P) (tProd si_na fi_P fi_P) => exact (fi_J_Prod _)
  | |- JoinE _ _ _ _ (tLetIn si_na fi_P fi_P fi_P) fi_P => exact (fi_J_LetIn _)
  | |- JoinE _ _ _ _ fi_P (tLetIn si_na fi_P fi_P fi_P) => exact (fi_J_LetIn_r _)
  | |- JoinE _ _ _ _ fi_beta fi_P => exact (fi_J_beta _)
  | |- JoinE _ _ _ _ fi_P fi_beta => exact (fi_J_beta_r _)
  | |- JoinE _ _ _ _ _ _ => apply JoinE_refl
  | |- red _ _ fi_beta fi_P => exact fi_red_beta
  | |- _ ;;; _ ⊢ fi_beta ⇝ fi_P => exact fi_closed_red_beta
  | |- _ ;;; _ ⊢ _ ⇝ _ => apply closed_red_refl; reflexivity
  | |- ws_cumul_ctx_pbE _ _ _ fi_Γ1 fi_Γb => exact fi_ctx_P_beta
  | |- si_Σ ⊢ fi_Γb ⇝ fi_Γ1 => exact fi_red_ctx
  | |- eta1 fi_eta fi_P => exact fi_eta1
  | |- eta1 (tProd si_na fi_eta fi_P) _ => exact fi_Prod_eta1
  | |- eta1 (tApp (tInd si_ind []) fi_eta) _ => exact fi_App_eta1
  | |- eta1 (tLetIn si_na fi_eta fi_P fi_P) _ => exact fi_LetIn_eta1
  | |- red1 _ _ fi_beta fi_P => exact (red_beta _ _ si_na fi_P (tRel 0) fi_P)
  | |- clos_refl_trans _ _ _ => apply rt_refl
  | |- eq_term_upto_univ_eta_napp _ _ _ _ _ _ _ _ => apply compare_term_eta_refl
  | |- eq_binder_annot _ _ => exact eq_refl
  | |- is_true _ => reflexivity
  | |- _ => first [reflexivity | constructor]
  end.

(** ** A6 part 1 *)

Lemma chain_Sort_inst : tSort sProp = tSort sProp.
Proof. exact (chain_Sort (Σ := si_Σ) [] sProp _ ltac:(apply rt_refl)). Qed.
Lemma chain_Prod_inst : ∑ na' A' B', [× tProd si_na fi_P fi_P = tProd na' A' B', eq_binder_annot si_na na',
    clos_refl_trans (be_step si_Σ []) fi_eta A' & clos_refl_trans (be_step si_Σ (fi_Γ1)) fi_P B'].
Proof.
  have := chain_Prod (Σ := si_Σ) [] si_na fi_eta fi_P (tProd si_na fi_P fi_P)
            ltac:(apply rt_step; right; exact fi_Prod_eta1).
  intros (na' & A' & B' & [e h1 h2 h3]). exists na', A', B'. split; try assumption.
  (* the codomain context is [vass si_na fi_eta]; the statement's is [fi_Γ1] by BE_ctx *)
  exact (BE_ctx si_Σ _ _ _ _ (bodies_vass [] si_na si_na fi_eta fi_P) h3).
Qed.
Lemma red1_Prod_inv_inst :
  (∑ A', red1 si_Σ [] fi_beta A' × (tProd si_na fi_P fi_P = tProd si_na A' fi_P)) +
  (∑ B', red1 si_Σ ([] ,, vass si_na fi_beta) fi_P B' × (tProd si_na fi_P fi_P = tProd si_na fi_beta B')).
Proof. apply red1_Prod_inv. apply prod_red_l. exact (red_beta _ _ si_na fi_P (tRel 0) fi_P). Qed.
Lemma eta1_Prod_inv_inst :
  (∑ A', eta1 fi_eta A' × (tProd si_na fi_P fi_P = tProd si_na A' fi_P)) +
  (∑ B', eta1 fi_P B' × (tProd si_na fi_P fi_P = tProd si_na fi_eta B')).
Proof. apply eta1_Prod_inv. exact fi_Prod_eta1. Qed.
Lemma finst_Sort_l_inst : ∑ s', (tSort sProp = tSort s') × compare_sort si_Σ Cumul sProp s'.
Proof. unshelve eapply (finst_Sort_l (r := r) Cumul 0); a6_solve. Qed.
Lemma finst_Sort_r_inst : ∑ s', (tSort sProp = tSort s') × compare_sort si_Σ Cumul s' sProp.
Proof. unshelve eapply (finst_Sort_r (r := r) Cumul 0); a6_solve. Qed.
Lemma finst_Prod_l_inst : ∑ na' A' B', [× tProd si_na fi_P fi_P = tProd na' A' B', eq_binder_annot si_na na',
    eq_term_upto_univ_eta_napp r si_Σ.1 (compare_universe si_Σ) (compare_sort si_Σ) Conv 0 fi_P A'
    & eq_term_upto_univ_eta_napp r si_Σ.1 (compare_universe si_Σ) (compare_sort si_Σ) Cumul 0 fi_P B'].
Proof. unshelve eapply (finst_Prod_l (Σ := si_Σ) (r := r) Cumul 0); a6_solve. Qed.
Lemma finst_Prod_r_inst : ∑ na' A' B', [× tProd si_na fi_P fi_P = tProd na' A' B', eq_binder_annot na' si_na,
    eq_term_upto_univ_eta_napp r si_Σ.1 (compare_universe si_Σ) (compare_sort si_Σ) Conv 0 A' fi_P
    & eq_term_upto_univ_eta_napp r si_Σ.1 (compare_universe si_Σ) (compare_sort si_Σ) Cumul 0 B' fi_P].
Proof. unshelve eapply (finst_Prod_r (Σ := si_Σ) (r := r) Cumul 0); a6_solve. Qed.
Lemma canon_Prod_comp_inst : canon fi_P = fi_P × canon fi_P = fi_P.
Proof. apply (canon_Prod_comp (canon_na si_na)). reflexivity. Qed.
Lemma chain_canonical_inst : canon fi_P = fi_P.
Proof. exact (chain_canonical (Σ := si_Σ) [] fi_P fi_P eq_refl ltac:(apply rt_refl)). Qed.
Lemma open_Prod_inv_inst : is_open_term ([] : context) fi_P × is_open_term fi_Γ1 fi_P.
Proof. apply (open_Prod_inv [] si_na). reflexivity. Qed.
Lemma chain_open_inst : is_open_term ([] : context) fi_P.
Proof. exact (chain_open (Σ := si_Σ) (wfΣ := si_cb) [] fi_P fi_P eq_refl eq_refl ltac:(apply rt_refl)). Qed.
Lemma closed_red_of_inst : si_Σ ;;; [] ⊢ fi_beta ⇝ fi_P.
Proof. exact (closed_red_of (Σ := si_Σ) (Γ := []) (t := fi_beta) eq_refl eq_refl fi_red_beta). Qed.
Lemma WS_trans_inst : WS Conv [] fi_beta fi_P.
Proof. unshelve eapply (WS_trans (u := fi_P)); a6_solve. Qed.

Lemma ws_cumul_pbE_Sort_inv_inst : compare_sort si_Σ Cumul sProp sProp.
Proof. unshelve eapply (ws_cumul_pbE_Sort_inv (Σ := si_Σ) (r := r) (Γ := [])); a6_solve. Qed.
Lemma ws_cumul_pbE_Sort_l_inv_inst :
  ∑ s', clos_refl_trans (union (R_c si_Σ []) eta1) (canon fi_P) (tSort s') × compare_sort si_Σ Cumul sProp s'.
Proof. unshelve eapply (ws_cumul_pbE_Sort_l_inv (r := r)); a6_solve. Qed.
Lemma ws_cumul_pbE_Sort_r_inv_inst :
  ∑ s', clos_refl_trans (union (R_c si_Σ []) eta1) (canon fi_P) (tSort s') × compare_sort si_Σ Cumul s' sProp.
Proof. unshelve eapply (ws_cumul_pbE_Sort_r_inv (r := r)); a6_solve. Qed.
Lemma ws_cumul_pbE_Prod_l_inv_inst :
  ∑ na' dom' codom', [× clos_refl_trans (union (R_c si_Σ []) eta1) (canon (tProd si_na fi_P fi_P)) (tProd na' dom' codom'),
     eq_binder_annot si_na na', WS Conv [] fi_P dom' & WS Cumul fi_Γ1 fi_P codom'].
Proof. unshelve eapply (ws_cumul_pbE_Prod_l_inv (Σ := si_Σ) (wfΣ := si_cb) (r := r)); a6_solve. Qed.
Lemma ws_cumul_pbE_Prod_r_inv_inst :
  ∑ na' dom' codom', [× clos_refl_trans (union (R_c si_Σ []) eta1) (canon (tProd si_na fi_P fi_P)) (tProd na' dom' codom'),
     eq_binder_annot si_na na', WS Conv [] dom' fi_P & WS Cumul fi_Γ1 codom' fi_P].
Proof. unshelve eapply (ws_cumul_pbE_Prod_r_inv (Σ := si_Σ) (wfΣ := si_cb) (r := r)); a6_solve. Qed.
Lemma ws_cumul_pbE_Prod_Prod_inv_inst :
  [× eq_binder_annot si_na si_na, WS Conv [] fi_beta fi_P & WS Cumul fi_Γ1 fi_P fi_P].
Proof. unshelve eapply (ws_cumul_pbE_Prod_Prod_inv (Σ := si_Σ) (r := r)); a6_solve. Qed.
Lemma cumul_Prod_invE_inst : [× eq_binder_annot si_na si_na, WS Conv [] fi_beta fi_P & WS Cumul fi_Γ1 fi_P fi_P].
Proof. unshelve eapply (cumul_Prod_invE (Σ := si_Σ) (r := r)); a6_solve. Qed.
Lemma conv_Prod_invE_inst : [× eq_binder_annot si_na si_na, WS Conv [] fi_beta fi_P & WS Conv fi_Γ1 fi_P fi_P].
Proof. unshelve eapply (conv_Prod_invE (Σ := si_Σ) (r := r)); a6_solve. Qed.
Lemma Prod_conv_cum_invE_inst :
  eq_binder_annot si_na si_na /\ ∥ WS Conv [] fi_beta fi_P ∥ /\ ∥ WS Cumul fi_Γ1 fi_P fi_P ∥.
Proof. eapply (Prod_conv_cum_invE (Σ := si_Σ) (r := r)). constructor. unshelve eapply ws_cumul_pbE_Prod; a6_solve. Qed.
Lemma ws_cumul_pbE_red_r_inv_inst : WS Cumul [] fi_P fi_P.
Proof. unshelve eapply (ws_cumul_pbE_red_r_inv (Σ := si_Σ) (wfΣ := si_cb) fi_beta); a6_solve. Qed.
Lemma ws_cumul_pbE_red_l_inv_inst : WS Cumul [] fi_P fi_P.
Proof. unshelve eapply (ws_cumul_pbE_red_l_inv (Σ := si_Σ) (wfΣ := si_cb) fi_beta); a6_solve. Qed.
Lemma conv_cum_red_invE_inst : WS Cumul [] fi_P fi_P.
Proof. unshelve eapply (conv_cum_red_invE (Σ := si_Σ) (wfΣ := si_cb) Cumul [] fi_beta fi_beta); a6_solve. Qed.
Lemma ws_cumul_pbE_terms_red_inv_inst : ws_cumul_pbE_terms r si_Σ [] [fi_P] [fi_P].
Proof.
  unshelve eapply (ws_cumul_pbE_terms_red_inv (Σ := si_Σ) (wfΣ := si_cb) (ts := [fi_beta]) (ts' := [fi_beta]));
    a6_solve.
Qed.
Lemma ws_cumul_pbE_LetIn_l_inv_inst : WS Cumul [] (subst10 fi_P fi_P) fi_P.
Proof. unshelve eapply (ws_cumul_pbE_LetIn_l_inv (Σ := si_Σ) (wfΣ := si_cb) (na := si_na) (ty := fi_P)); a6_solve. Qed.
Lemma ws_cumul_pbE_LetIn_r_inv_inst : WS Cumul [] fi_P (subst10 fi_P fi_P).
Proof. unshelve eapply (ws_cumul_pbE_LetIn_r_inv (Σ := si_Σ) (wfΣ := si_cb) (na := si_na) (ty := fi_P)); a6_solve. Qed.
Lemma ws_cumul_pbE_LetIn_r_inv_canon_inst :
  ∑ b', clos_refl_trans (union (R_c si_Σ []) eta1) (canon fi_P) b' × WS Cumul [] b' (fi_P {0 := fi_P}).
Proof.
  unshelve eapply (ws_cumul_pbE_LetIn_r_inv_canon (Σ := si_Σ) (wfΣ := si_cb) (na := si_na) (ty := fi_P)); a6_solve.
Qed.
Lemma ws_cumul_pbE_Lambda_inv_inst : WS Cumul fi_Γ1 fi_P fi_P.
Proof.
  unshelve eapply (ws_cumul_pbE_Lambda_inv (Σ := si_Σ) (wfΣ := si_cb) (r := r) Cumul [] si_na si_na fi_P fi_P);
    a6_solve.
Qed.
Lemma Lambda_conv_cum_invE_inst : ∥ WS Cumul fi_Γ1 fi_P fi_P ∥.
Proof.
  unshelve eapply (Lambda_conv_cum_invE (Σ := si_Σ) (wfΣ := si_cb) (r := r) Cumul [] si_na si_na fi_P fi_P).
  constructor. unshelve eapply ws_cumul_pbE_Lambda; a6_solve.
Qed.

(** ** A6 part 2 *)

Definition fi_I : term := mkApps (tInd si_ind []) [fi_P].
Definition sa_A : term := mkApps sa_ax [fi_P].

Lemma mkApps_head_inj_inst : tInd si_ind [] = tInd si_ind [] /\ [fi_P] = [fi_P].
Proof. exact (mkApps_head_inj (tInd si_ind []) (tInd si_ind []) [fi_P] [fi_P] eq_refl eq_refl eq_refl). Qed.
Lemma eta1_tApp_inv_inst :
  (∑ f', eta1 (tInd si_ind []) f' × (tApp (tInd si_ind []) fi_P = tApp f' fi_eta)) +
  (∑ a', eta1 fi_eta a' × (tApp (tInd si_ind []) fi_P = tApp (tInd si_ind []) a')).
Proof. apply eta1_tApp_inv. exact fi_App_eta1. Qed.
Lemma eta1_mkApps_rigid_inv_inst :
  ∑ l', (tApp (tInd si_ind []) fi_P = mkApps (tInd si_ind []) l') × OnOne2 eta1 [fi_eta] l'.
Proof. exact (eta1_mkApps_rigid_inv (tInd si_ind []) [fi_eta] _ (eta_normal_Ind si_ind []) fi_App_eta1). Qed.
Lemma chain_mkApps_Ind_inst :
  ∑ l', (fi_I = mkApps (tInd si_ind []) l') × All2 (fun a a' => clos_refl_trans (be_step si_Σ []) a a') [fi_P] l'.
Proof. unshelve eapply (chain_mkApps_Ind (Σ := si_Σ) (wfΣ := si_cb) []); a6_solve. Qed.
Lemma chain_mkApps_Const_inst :
  ∑ l', (sa_A = mkApps sa_ax l') × All2 (fun a a' => clos_refl_trans (be_step sa_Σ []) a a') [fi_P] l'.
Proof. unshelve eapply (chain_mkApps_Const (Σ := sa_Σ) (wfΣ := sa_cb) [] sa_kn sa_cb); a6_solve. Qed.
Lemma finst_tApp_l_inst : ∑ f' a', [× tApp fi_P fi_P = tApp f' a',
    eq_term_upto_univ_eta_napp r si_Σ.1 (compare_universe si_Σ) (compare_sort si_Σ) Cumul 1 fi_P f'
    & eq_term_upto_univ_eta_napp r si_Σ.1 (compare_universe si_Σ) (compare_sort si_Σ) Conv 0 fi_P a'].
Proof. unshelve eapply (finst_tApp_l (Σ := si_Σ) (r := r) Cumul 0); a6_solve. Qed.
Lemma finst_tApp_r_inst : ∑ f' a', [× tApp fi_P fi_P = tApp f' a',
    eq_term_upto_univ_eta_napp r si_Σ.1 (compare_universe si_Σ) (compare_sort si_Σ) Cumul 1 f' fi_P
    & eq_term_upto_univ_eta_napp r si_Σ.1 (compare_universe si_Σ) (compare_sort si_Σ) Conv 0 a' fi_P].
Proof. unshelve eapply (finst_tApp_r (Σ := si_Σ) (r := r) Cumul 0); a6_solve. Qed.
Lemma finst_mkApps_Ind_l_inst : ∑ u' l', [× fi_I = mkApps (tInd si_ind u') l',
    cmp_global_instance_finst r si_Σ.1 (compare_universe si_Σ) Cumul (IndRef si_ind) (#|[fi_P]| + 0) [] u'
    & All2 (eq_term_upto_univ_eta_napp r si_Σ.1 (compare_universe si_Σ) (compare_sort si_Σ) Conv 0) [fi_P] l'].
Proof. unshelve eapply (finst_mkApps_Ind_l (Σ := si_Σ) (r := r) Cumul 0); a6_solve. Qed.
Lemma finst_mkApps_Ind_r_inst : ∑ u' l', [× fi_I = mkApps (tInd si_ind u') l',
    cmp_global_instance_finst r si_Σ.1 (compare_universe si_Σ) Cumul (IndRef si_ind) (#|[fi_P]| + 0) u' []
    & All2 (eq_term_upto_univ_eta_napp r si_Σ.1 (compare_universe si_Σ) (compare_sort si_Σ) Conv 0) l' [fi_P]].
Proof. unshelve eapply (finst_mkApps_Ind_r (Σ := si_Σ) (r := r) Cumul 0); a6_solve. Qed.
Lemma finst_mkApps_Const_l_inst : ∑ u' l', [× sa_A = mkApps (tConst sa_kn u') l',
    cmp_universe_instance (compare_universe sa_Σ Conv) [] u'
    & All2 (eq_term_upto_univ_eta_napp r sa_Σ.1 (compare_universe sa_Σ) (compare_sort sa_Σ) Conv 0) [fi_P] l'].
Proof. unshelve eapply (finst_mkApps_Const_l (Σ := sa_Σ) (r := r) Cumul 0); a6_solve. Qed.
Lemma finst_mkApps_Const_r_inst : ∑ u' l', [× sa_A = mkApps (tConst sa_kn u') l',
    cmp_universe_instance (compare_universe sa_Σ Conv) u' []
    & All2 (eq_term_upto_univ_eta_napp r sa_Σ.1 (compare_universe sa_Σ) (compare_sort sa_Σ) Conv 0) l' [fi_P]].
Proof. unshelve eapply (finst_mkApps_Const_r (Σ := sa_Σ) (r := r) Cumul 0); a6_solve. Qed.
Lemma ws_cumul_pbE_Ind_l_inv_inst : ∑ ui' l', [× clos_refl_trans (union (R_c si_Σ []) eta1) (canon fi_I) (mkApps (tInd si_ind ui') l'),
    cmp_global_instance_finst r si_Σ.1 (compare_universe si_Σ) Cumul (IndRef si_ind) #|[fi_P]| [] ui'
    & All2 (WS Conv []) [fi_P] l'].
Proof. unshelve eapply (ws_cumul_pbE_Ind_l_inv (Σ := si_Σ) (wfΣ := si_cb) (r := r)); a6_solve. Qed.
Lemma ws_cumul_pbE_Ind_r_inv_inst : ∑ ui' l', [× clos_refl_trans (union (R_c si_Σ []) eta1) (canon fi_I) (mkApps (tInd si_ind ui') l'),
    cmp_global_instance_finst r si_Σ.1 (compare_universe si_Σ) Cumul (IndRef si_ind) #|[fi_P]| ui' []
    & ws_cumul_pbE_terms r si_Σ [] l' [fi_P]].
Proof. unshelve eapply (ws_cumul_pbE_Ind_r_inv (Σ := si_Σ) (wfΣ := si_cb) (r := r)); a6_solve. Qed.
Lemma ws_cumul_pbE_Ind_inv_inst :
  [× si_ind = si_ind, cmp_global_instance_finst r si_Σ.1 (compare_universe si_Σ) Cumul (IndRef si_ind) #|[fi_P]| [] [],
     is_closed_context ([] : context) & ws_cumul_pbE_terms r si_Σ [] [fi_P] [fi_P]].
Proof. unshelve eapply (ws_cumul_pbE_Ind_inv (Σ := si_Σ) (wfΣ := si_cb) (r := r)); a6_solve. Qed.
Lemma invert_cumul_ind_indE_inst :
  (eqb si_ind si_ind * cmp_global_instance_finst r si_Σ.1 (compare_universe si_Σ) Cumul (IndRef si_ind) #|[fi_P]| [] []
   * ws_cumul_pbE_terms r si_Σ [] [fi_P] [fi_P]).
Proof. unshelve eapply (invert_cumul_ind_indE (Σ := si_Σ) (wfΣ := si_cb) (r := r)); a6_solve. Qed.
Lemma ws_cumul_pbE_Axiom_l_inv_inst :
  ∑ u' args', [× clos_refl_trans (union (R_c sa_Σ []) eta1) (canon sa_A) (mkApps (tConst sa_kn u') args'),
    All2 (WSa Conv []) [fi_P] args' & cmp_universe_instance (compare_universe sa_Σ Conv) [] u'].
Proof. unshelve eapply (ws_cumul_pbE_Axiom_l_inv (Σ := sa_Σ) (wfΣ := sa_cb) (r := r) (cdecl := sa_cb)); a6_solve. Qed.
Lemma ws_cumul_pbE_Axiom_r_inv_inst :
  ∑ u' args', [× clos_refl_trans (union (R_c sa_Σ []) eta1) (canon sa_A) (mkApps (tConst sa_kn u') args'),
    All2 (WSa Conv []) args' [fi_P] & cmp_universe_instance (compare_universe sa_Σ Conv) u' []].
Proof. unshelve eapply (ws_cumul_pbE_Axiom_r_inv (Σ := sa_Σ) (wfΣ := sa_cb) (r := r) (cdecl := sa_cb)); a6_solve. Qed.

(** ** A6 part 3 *)

Lemma prim_type_spine_inst (i : PrimInt63.int) :
  ∑ u args, prim_type (primInt; primIntModel i) sa_kn = mkApps (tConst sa_kn u) args.
Proof. apply prim_type_spine. Qed.
Lemma primitive_invariants_body_inst : cst_body fi_prim_cb = None.
Proof. apply (primitive_invariants_body primInt). split; reflexivity. Qed.
Lemma eta1_LetIn_inv_inst :
  (∑ b', eta1 fi_eta b' × (tLetIn si_na fi_P fi_P fi_P = tLetIn si_na b' fi_P fi_P))
  + (∑ A', eta1 fi_P A' × (tLetIn si_na fi_P fi_P fi_P = tLetIn si_na fi_eta A' fi_P))
  + (∑ t', eta1 fi_P t' × (tLetIn si_na fi_P fi_P fi_P = tLetIn si_na fi_eta fi_P t')).
Proof. apply eta1_LetIn_inv. exact fi_LetIn_eta1. Qed.
Lemma canon_it_mkProd_or_LetIn_Ind_inst : ∑ ctx', canon (it_mkProd_or_LetIn fi_Γ1 fi_I)
    = it_mkProd_or_LetIn ctx' (mkApps (tInd si_ind []) (map canon [fi_P])).
Proof. apply canon_it_mkProd_or_LetIn_Ind. Qed.
Lemma eta1_it_mkProd_or_LetIn_Ind_inst :
  ∑ ctx' args', tApp (tInd si_ind []) fi_P = it_mkProd_or_LetIn ctx' (mkApps (tInd si_ind []) args').
Proof. exact (eta1_it_mkProd_or_LetIn_Ind [] si_ind [] [fi_eta] _ fi_App_eta1). Qed.
Lemma conv_sort_invE_inst : eq_sort (global_ext_constraints si_Σ) sProp sProp.
Proof. unshelve eapply (conv_sort_invE (Σ := si_Σ) (r := r) []); a6_solve. Qed.
Lemma ws_cumul_pbE_LetIn_inv_inst : WS Cumul [] (fi_P {0 := fi_P}) (fi_P {0 := fi_P}).
Proof.
  unshelve eapply (ws_cumul_pbE_LetIn_inv (Σ := si_Σ) (wfΣ := si_cb) (r := r) (na := si_na) (na' := si_na)
                     (ty := fi_P) (ty' := fi_P)); a6_solve.
Qed.
Lemma ws_cumul_pbE_Prod_Prod_inv_l_inst :
  [× eq_binder_annot si_na si_na, WS Conv [] fi_beta fi_P & WS Cumul ([] ,, vass si_na fi_beta) fi_P fi_P].
Proof. unshelve eapply (ws_cumul_pbE_Prod_Prod_inv_l (Σ := si_Σ) (r := r)); a6_solve. Qed.
Lemma ws_cumul_pbE_LetIn_l_inv_alt_inst : WS Conv ([] ,, vdef si_na fi_P fi_P) fi_P (lift0 1 fi_P).
Proof. unshelve eapply (ws_cumul_pbE_LetIn_l_inv_alt (Σ := si_Σ) (wfΣ := si_cb) (r := r)); a6_solve. Qed.
Lemma chain_it_mkProd_or_LetIn_mkApps_Ind_inst :
  ∑ ctx' args', canon (it_mkProd_or_LetIn fi_Γ1 fi_I) = it_mkProd_or_LetIn ctx' (mkApps (tInd si_ind []) args').
Proof. unshelve eapply (chain_it_mkProd_or_LetIn_mkApps_Ind (Σ := si_Σ) (wfΣ := si_cb) [] fi_Γ1 si_ind [] [fi_P]);
    a6_solve. Qed.

(** ** A8 *)

Lemma WS8_trans_inst : WS Conv [] fi_beta fi_P.
Proof. unshelve eapply (WS8_trans (Σ := si_Σ) (wfΣ := si_cb) (u := fi_P)); a6_solve. Qed.
Lemma it_mkProd_ctx_congr_inst : WS Conv [] (it_mkProd_or_LetIn fi_Γ1 fi_P) (it_mkProd_or_LetIn fi_Γb fi_P).
Proof. unshelve eapply (it_mkProd_ctx_congr (Σ := si_Σ)); a6_solve. Qed.
Lemma letin_body_inv_inst : WS Cumul ([] ,, vdef si_na fi_P fi_P) fi_P fi_P.
Proof. unshelve eapply (letin_body_inv (Σ := si_Σ) (wfΣ := si_cb)); a6_solve. Qed.
Lemma mkProd_or_LetIn_inv_inst : WS Cumul ([] ,, vass si_na fi_P) fi_P fi_P.
Proof. unshelve eapply (mkProd_or_LetIn_inv (Σ := si_Σ) (wfΣ := si_cb)); a6_solve. Qed.
Lemma it_mkProd_inv_inst : WS Cumul ([] ,,, fi_Γ1) fi_P fi_P.
Proof. unshelve eapply (it_mkProd_inv (Σ := si_Σ) (wfΣ := si_cb)); a6_solve. Qed.
Lemma ws_cumul_pbE_ws_cumul_ctx_inst : WS Cumul fi_Γb (tRel 0) (tRel 0).
Proof. unshelve eapply (ws_cumul_pbE_ws_cumul_ctx (Σ := si_Σ) (wfΣ := si_cb) (Γ := fi_Γ1)); a6_solve. Qed.
Lemma ws_cumul_ctx_pbE_refl_inst : ws_cumul_ctx_pbE r Conv si_Σ fi_Γ1 fi_Γ1.
Proof. unshelve eapply (ws_cumul_ctx_pbE_refl (Σ := si_Σ)); a6_solve. Qed.
Lemma ws_cumul_ctx_pbE_sym_inst : ws_cumul_ctx_pbE r Conv si_Σ fi_Γb fi_Γ1.
Proof. unshelve eapply (ws_cumul_ctx_pbE_sym (Σ := si_Σ) (wfΣ := si_cb)); a6_solve. Qed.
Lemma closed_red_ctx_ctx_inst : ws_cumul_ctx_pbE r Conv si_Σ fi_Γb fi_Γ1.
Proof. unshelve eapply (closed_red_ctx_ctx (Σ := si_Σ) (wfΣ := si_cb)); a6_solve. Qed.
Lemma ws_cumul_pbE_red_ctx_inv_inst : WS Cumul fi_Γb (tRel 0) (tRel 0).
Proof. unshelve eapply (ws_cumul_pbE_red_ctx_inv (Σ := si_Σ) (wfΣ := si_cb) (Γ := fi_Γ1)); a6_solve. Qed.
Lemma cumul_red_ctx_invE_inst : WS Cumul fi_Γb (tRel 0) (tRel 0).
Proof. unshelve eapply (cumul_red_ctx_invE (Σ := si_Σ) (wfΣ := si_cb) (Γ := fi_Γ1)); a6_solve. Qed.
Lemma conv_cum_red_conv_invE_inst : WS Cumul fi_Γ1 (tRel 0) (tRel 0).
Proof.
  unshelve eapply (conv_cum_red_conv_invE (Σ := si_Σ) (wfΣ := si_cb) Cumul fi_Γ1 fi_Γb (tRel 0) (tRel 0));
    a6_solve.
Qed.
