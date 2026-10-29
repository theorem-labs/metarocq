(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the hypotheses of [PCUICSREtaConv]

  Each lemma of [PCUICSREtaConv] that has a premise is applied here to a concrete instance with
  every premise proved. The environment is [si_Σ] of [PCUICCumulativitySpecEtaClosureInstances]
  ([Inductive I (A : Prop) : Prop := c : I A]; [si_cb], [si_wfE]). The terms are those of
  [PCUICEtaFracInstances] and [PCUICWsCumulEtaCtxInstances]: [fi_P := Prop], the β-redex
  [fi_beta := (λx:Prop. x) Prop], the η-redex [fi_eta := λx:Prop. Prop x], the identity [ci_id]
  of [Prop], [ci_False := ∀P:Prop. P], two λ-terms [ci_lam], [ci_lam'] that differ only in a
  binder name.

  Where a lemma relates two things, the instance relates two different things: a β-redex against
  its reduct, an η-redex against its contraction, two contexts that differ in a let-body or in an
  assumption type or in a binder name, two types that differ by a β-step. The exceptions are the
  lemmas whose conclusion is reflexive by statement ([ws_cumul_pbE_meta_refl],
  [wt_cumul_pb_reflE], [wt_terms_ws_cumul_pbE]) and [declared_inductive_closed_params_instE],
  which has no relation in it. [ws_cumul_ctx_pbE_cons_inv] is an inversion helper; its instance
  is the context pair of [sc_ctx_conv]. The reduction lemmas are applied to a β-step in a domain
  ([red_it_mkProd_or_LetIn_smash_cb], [red_has_rec_arg_cb], [closed_red_from_empty_cb]) and to the
  unfolding of a let-bound variable ([red_expand_let_cb], [red_expand_letE]).
  [substitution_ws_cumul_pbE_subslet] substitutes [ci_False] for [x : Prop] in the β-pair
  [(λy:Prop. y) x ≤ x]. *)

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICLiftSubst PCUICEquality
     PCUICReduction PCUICOnOne PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICWellScopedCumulativity PCUICSubstitution PCUICContextSubst PCUICConfluence PCUICConversion
     PCUICContextConversion
     PCUICEtaI5 PCUICWellScopedCumulativityEta PCUICConversionEtaCongr
     PCUICContextConversionEta PCUICTypingEta PCUICTypingEtaInd PCUICClosedTypEta
     PCUICCumulativitySpecEtaClosureInstances PCUICEtaFracInstances
     PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp PCUICWsCumulEtaCtxInstances PCUICClosedBodies
     PCUICSREtaConv PCUICSubstitutionEta.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

Local Notation WS pb Γ := (ws_cumul_pbE pb si_Σ Γ).

(** ** Concrete data *)

(** One-assumption contexts whose types are the β-pair. *)
Definition sc_Γb : context := [vass si_na fi_beta].

Lemma sc_ctx_beta : ws_cumul_ctx_pbE Conv si_Σ ([] ,,, sc_Γb) ([] ,,, fi_Γ1).
Proof. constructor; [constructor|]. constructor; [reflexivity|exact (fi_WS_beta Conv)]. Qed.

(** One-let contexts whose bodies are the η-pair, at [Conv]. *)
Definition sc_Γd1 : context := [vdef si_na fi_eta fi_P].
Definition sc_Γd2 : context := [vdef si_na fi_P fi_P].

Lemma sc_ctx_conv : ws_cumul_ctx_pbE Conv si_Σ ([] ,,, sc_Γd1) ([] ,,, sc_Γd2).
Proof.
  constructor; [constructor|]. constructor; [reflexivity|exact (ci_WS_eta Conv)|].
  apply ws_cumul_pbE_refl; reflexivity.
Qed.

Lemma sc_rel_d : ws_cumul_ctx_pbE_rel Conv si_Σ [] sc_Γd1 sc_Γd2.
Proof.
  split; [reflexivity|]. constructor; [constructor|].
  constructor; [reflexivity|exact (ci_WS_eta Conv)|]. apply ws_cumul_pbE_refl; reflexivity.
Qed.

(** One step of context reduction: the type [fi_beta] reduces to [fi_P]. *)
Lemma sc_one : OnOne2_local_env (fun Δ : context => on_one_decl (red1 si_Σ ([] ,,, Δ))) sc_Γb fi_Γ1.
Proof.
  apply onone2_localenv_cons_abs. cbn. split; [reflexivity|].
  exact (red_beta si_Σ _ si_na fi_P (tRel 0) fi_P).
Qed.

(** ** Items 1-2 *)

Lemma ws_cumul_ctx_pbE_cons_inv_inst :
  ws_cumul_ctx_pbE Conv si_Σ [] [] × ws_cumul_declsE Conv si_Σ [] (vdef si_na fi_eta fi_P) (vdef si_na fi_P fi_P).
Proof. exact (ws_cumul_ctx_pbE_cons_inv sc_ctx_conv). Qed.

(** [λx:(λy:Prop. y) Prop. λz:Prop. Prop z] and [λx:Prop. Prop]. *)
Lemma ws_cumul_pbE_it_mkLambda_or_LetIn_inst :
  WS Cumul [] (it_mkLambda_or_LetIn sc_Γb fi_eta) (it_mkLambda_or_LetIn fi_Γ1 fi_P).
Proof.
  apply (ws_cumul_pbE_it_mkLambda_or_LetIn (Γ := []) sc_ctx_beta).
  apply eta1_ws_cumul_pbE; [reflexivity|reflexivity|exact fi_eta1].
Qed.

(** Substituting the β-pair into [x : Rel 0]. *)
Lemma substitution_ws_cumul_ctx_pbE_red_subst_inst :
  ws_cumul_ctx_pbE Conv si_Σ ([] ,,, subst_context [fi_beta] 0 [vass si_na (tRel 0)])
    ([] ,,, subst_context [fi_P] 0 [vass si_na (tRel 0)]).
Proof.
  apply (substitution_ws_cumul_ctx_pbE_red_subst (Γ := []) (Δ := [vass si_na fi_P])).
  - reflexivity.
  - constructor; [exact fi_closed_red_beta|constructor].
  - exact ci_untyped_subslet.
Qed.

(** Two contexts whose types [compare_term] relates without being equal. *)
Lemma eq_context_upto_ws_cumul_ctx_pbE_inst :
  ws_cumul_ctx_pbE Cumul si_Σ [vass si_na ci_lam] [vass si_na ci_lam'].
Proof.
  apply eq_context_upto_ws_cumul_ctx_pbE; [reflexivity|reflexivity|].
  constructor; [constructor|]. constructor; [reflexivity|exact (ci_eq_lam Cumul)].
Qed.

(** ** Item 3 *)

(** The fixpoint witness: a declared type [fi_beta], witness [fi_eta], reduct [fi_P]. *)
Definition sc_check : def term -> option kername := fun _ => Some si_kn.
Definition sc_d : def term := {| dname := si_na; dtype := fi_beta; dbody := fi_P; rarg := 0 |}.

Lemma sc_body_on : mfix_body_on sc_check (conv_witnessE si_Σ []) si_kn sc_d.
Proof.
  exists fi_eta. split; [reflexivity|]. split; [reflexivity|].
  exact (ws_cumul_pbE_forget_spec (ws_cumul_pbE_trans _ _ _ (fi_WS_beta Conv) (ci_WS_eta_r Conv))).
Qed.

Lemma mfix_body_on_red_typeE_inst :
  mfix_body_on sc_check (conv_witnessE si_Σ []) si_kn (def_with_type sc_d fi_P).
Proof. exact (mfix_body_on_red_typeE (d := sc_d) fi_closed_red_beta sc_body_on). Qed.

Lemma mfix_on_ind_red1_typeE_inst :
  mfix_on_ind sc_check (conv_witnessE si_Σ []) (fun _ => true) [def_with_type sc_d fi_P].
Proof.
  apply (mfix_on_ind_red1_typeE [] [sc_d]).
  - constructor. split; [exact fi_closed_red_beta|reflexivity].
  - exists si_kn. split; [discriminate|]. split; [|reflexivity].
    constructor; [exact sc_body_on|constructor].
Qed.

Lemma conv_context_rel_relnE_inst : forall acc n, reln acc n sc_Γd1 = reln acc n sc_Γd2.
Proof. exact (conv_context_rel_relnE [] sc_Γd1 sc_Γd2 sc_rel_d). Qed.

Lemma conv_context_rel_to_extended_listE_inst : to_extended_list sc_Γd1 = to_extended_list sc_Γd2.
Proof. exact (conv_context_rel_to_extended_listE sc_rel_d). Qed.

(** Two contexts that differ only in a binder name. *)
Lemma eq_context_alpha_convE_inst :
  ws_cumul_ctx_pbE_rel Conv si_Σ [] [vass si_na fi_P] [vass (mkBindAnn (nNamed "x") Relevant) fi_P].
Proof. apply eq_context_alpha_convE; [repeat constructor|reflexivity|reflexivity]. Qed.

Definition sc_nas : list aname := [mkBindAnn (nNamed "x") Relevant].

Lemma conv_ctx_set_binder_nameE_inst :
  ws_cumul_ctx_pbE_rel Conv si_Σ [] (map2 set_binder_name sc_nas sc_Γd1) (map2 set_binder_name sc_nas sc_Γd2).
Proof.
  apply conv_ctx_set_binder_nameE; [repeat constructor|repeat constructor|exact sc_rel_d].
Qed.

Lemma red_one_decl_red_ctx_cb_inst : red_ctx si_Σ ([] ,,, sc_Γb) ([] ,,, fi_Γ1).
Proof. exact (red_one_decl_red_ctx_cb (Γ := []) (Δ := sc_Γb) (Δ' := fi_Γ1) eq_refl sc_one). Qed.

Lemma into_closed_red_ctx_cb_inst : closed_red_ctx si_Σ ([] ,,, sc_Γb) ([] ,,, fi_Γ1).
Proof. exact (into_closed_red_ctx_cb (Γ := [] ,,, sc_Γb) (Δ := [] ,,, fi_Γ1) eq_refl red_one_decl_red_ctx_cb_inst). Qed.

Lemma red_one_decl_red_context_cb_inst : closed_red_ctx si_Σ ([] ,,, sc_Γb) ([] ,,, fi_Γ1).
Proof. exact (red_one_decl_red_context_cb (Γ := []) (Δ := sc_Γb) (Δ' := fi_Γ1) eq_refl sc_one). Qed.

Lemma red_one_decl_ws_cumul_ctx_pbE_inst : ws_cumul_ctx_pbE Conv si_Σ ([] ,,, sc_Γb) ([] ,,, fi_Γ1).
Proof. exact (red_one_decl_ws_cumul_ctx_pbE (Γ := []) (Δ := sc_Γb) (Δ' := fi_Γ1) eq_refl sc_one). Qed.

Lemma ws_cumul_pbE_meta_refl_inst : WS Conv [] fi_P fi_P.
Proof. exact (ws_cumul_pbE_meta_refl (Σ := si_Σ) (Γ := []) (T := fi_P) (U := fi_P) eq_refl eq_refl eq_refl). Qed.

Lemma ws_cumul_pbE_eq_trans_inst : WS Conv [] fi_beta fi_P.
Proof. exact (ws_cumul_pbE_eq_trans (fi_WS_beta Conv) eq_refl). Qed.

Lemma eq_ws_cumul_pbE_trans_inst : WS Conv [] fi_beta fi_P.
Proof. exact (eq_ws_cumul_pbE_trans eq_refl (fi_WS_beta Conv)). Qed.

Lemma ws_cumul_pbE_terms_eq_trans_inst : ws_cumul_pbE_terms si_Σ [] [fi_beta] [fi_P].
Proof. exact (ws_cumul_pbE_terms_eq_trans ci_WT eq_refl). Qed.

Lemma eq_ws_cumul_pbE_terms_trans_inst : ws_cumul_pbE_terms si_Σ [] [fi_beta] [fi_P].
Proof. exact (eq_ws_cumul_pbE_terms_trans eq_refl ci_WT). Qed.

(** Weakening the η-pair of let-bodies under [x : Prop]. *)
Lemma weakening_ws_cumul_ctx_pbE_inst :
  ws_cumul_ctx_pbE Conv si_Σ ([] ,,, fi_Γ1 ,,, lift_context #|fi_Γ1| 0 sc_Γd1)
    ([] ,,, fi_Γ1 ,,, lift_context #|fi_Γ1| 0 sc_Γd2).
Proof.
  apply (weakening_ws_cumul_ctx_pbE (Γ := []) sc_ctx_conv).
  exact (ws_cumul_ctx_pbE_refl_pb (Γ := [] ,,, fi_Γ1) eq_refl).
Qed.

Lemma sc_closed_red1_beta : closed_red1 si_Σ [] fi_beta fi_P.
Proof. split; [reflexivity|reflexivity|exact (red_beta si_Σ [] si_na fi_P (tRel 0) fi_P)]. Qed.

Lemma closed_red1_ws_cumul_pbE_inst : WS Conv [] fi_beta fi_P.
Proof. exact (closed_red1_ws_cumul_pbE sc_closed_red1_beta). Qed.

(** *** The typed lemmas *)

Lemma wt_cumul_pb_reflE_inst : WS Conv fi_Γ1 (tRel 0) (tRel 0).
Proof. exact (wt_cumul_pb_reflE (Σ := si_Σ) (wfΣ := si_wfE) ci_x_typed). Qed.

Lemma wt_terms_ws_cumul_pbE_inst : ws_cumul_pbE_terms si_Σ fi_Γ1 [tRel 0] [tRel 0].
Proof.
  apply (wt_terms_ws_cumul_pbE (Σ := si_Σ) (wfΣ := si_wfE)).
  constructor; [exists fi_P; exact ci_x_typed|constructor].
Qed.

(** The context [x : Prop, h : (λy:Prop. y) x]: [h] has a type that β-reduces to [x]. *)
Definition sc_Γh : context := fi_Γ1 ,, vass si_na (tApp ci_id (tRel 0)).

Lemma sc_wf_Γh : wf_localE si_Σ sc_Γh.
Proof.
  apply localenv_cons_abs; [exact ci_wf_Γ1|]. apply ci_vass_Prop.
  exact (ci_app_typed fi_Γ1 (tRel 0) ci_wf_Γ1 ci_x_typed).
Qed.

Lemma sc_h_typed : si_Σ ;;; sc_Γh |-E tRel 0 : tApp ci_id (tRel 1).
Proof. exact (typeE_Rel _ _ 0 (vass si_na (tApp ci_id (tRel 0))) sc_wf_Γh eq_refl). Qed.

Lemma sc_x_typed : si_Σ ;;; sc_Γh |-E tRel 1 : fi_P.
Proof. exact (typeE_Rel _ _ 1 (vass si_na fi_P) sc_wf_Γh eq_refl). Qed.

Lemma sc_red_h : red si_Σ sc_Γh (tApp ci_id (tRel 1)) (tRel 1).
Proof. apply rt_step. unfold ci_id. apply red_beta. Qed.

Lemma type_Cumul_altE_inst : si_Σ ;;; sc_Γh |-E tRel 0 : tRel 1.
Proof.
  exact (type_Cumul_altE (Σ := si_Σ) (wfΣ := si_wfE) sc_Γh (tRel 0) (tApp ci_id (tRel 1)) (tRel 1)
           sc_h_typed (ci_on_typeE_Prop _ _ sc_x_typed) (JoinE_red_l si_Σ sc_Γh Cumul _ _ sc_red_h)).
Qed.

(** The typed substitution [x := ∀P:Prop. P] and the β-pair [(λy:Prop. y) x ≤ x] under [x : Prop];
    substituting gives the β-pair [(λy:Prop. y) (∀P:Prop. P) ≤ ∀P:Prop. P]. *)
Lemma sc_subslet_False : subsletE si_Σ [] [ci_False] fi_Γ1.
Proof. constructor; [constructor|]. rewrite subst_empty. exact (ci_False_typed [] localenv_nil). Qed.

Lemma sc_WS_id_x : WS Cumul ([] ,,, fi_Γ1 ,,, []) (tApp ci_id (tRel 0)) (tRel 0).
Proof.
  apply red_ws_cumul_pbE. split; [reflexivity|reflexivity|].
  apply rt_step. unfold ci_id. apply red_beta.
Qed.

Lemma substitution_ws_cumul_pbE_subslet_inst : WS Cumul [] (tApp ci_id ci_False) ci_False.
Proof.
  exact (substitution_ws_cumul_pbE_subslet (Σ := si_Σ) (wfΣ := si_wfE) (Γ := []) (Γ'' := [])
           sc_subslet_False sc_WS_id_x).
Qed.

(** ** Environment and reduction facts *)

Lemma declared_inductive_closed_params_instE_inst : closed_ctx (subst_instance [Level.lzero] (ind_params si_mdecl)).
Proof.
  exact (declared_inductive_closed_params_instE (Σ := si_Σ) (wfΣ := si_wfE) (u := [Level.lzero])
           si_declared_inductive).
Qed.

(** The let [z := ∀P:Prop. P : Prop]: the variable [z] unfolds to its body. *)
Lemma sc_wf_let : wf_localE si_Σ ([] ,,, [vdef si_na ci_False fi_P]).
Proof.
  apply localenv_cons_def; [constructor|].
  split; [exact (ci_False_typed [] localenv_nil)|].
  exists (Sort.super sProp). split; [exact (ci_typeE_P [] localenv_nil)|]. split; [exact I|reflexivity].
Qed.

Lemma red_expand_let_cb_inst :
  si_Σ ;;; [] ,, vdef si_na ci_False fi_P ⊢ tRel 0 ⇝ lift0 1 (subst1 ci_False 0 (tRel 0)).
Proof.
  exact (red_expand_let_cb (Σ := si_Σ) (Γ := []) (na := si_na) (b := ci_False) (ty := fi_P) (t := tRel 0)
           eq_refl eq_refl).
Qed.

Lemma red_expand_letE_inst :
  si_Σ ;;; [] ,, vdef si_na ci_False fi_P ⊢ tRel 0 ⇝ lift0 1 (subst1 ci_False 0 (tRel 0)).
Proof.
  exact (red_expand_letE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := []) (na := si_na) (b := ci_False) (ty := fi_P)
           (t := tRel 0) sc_wf_let eq_refl).
Qed.

(** The β-reduction [fi_beta ⇝ fi_P] in the empty context, moved into [x : Prop]. *)
Lemma closed_red_from_empty_cb_inst : si_Σ ;;; fi_Γ1 ⊢ fi_beta ⇝ fi_P.
Proof.
  exact (closed_red_from_empty_cb (Σ := si_Σ) (Γ := fi_Γ1) (M := fi_beta) (N := fi_P) eq_refl eq_refl fi_red_beta).
Qed.

(** [Π x:(λy:Prop. y) Prop. Prop] reduces to [Π x:Prop. Prop] in its domain. *)
Lemma sc_red_prod : si_Σ ;;; [] ⊢ it_mkProd_or_LetIn sc_Γb fi_P ⇝ tProd si_na fi_P fi_P.
Proof.
  split; [reflexivity|reflexivity|]. apply rt_step. cbn. apply prod_red_l.
  exact (red_beta si_Σ [] si_na fi_P (tRel 0) fi_P).
Qed.

Lemma red_it_mkProd_or_LetIn_smash_cb_inst :
  ∑ ctx' t' d,
    [× decompose_prod_assum [] (tProd si_na fi_P fi_P) = (ctx', t'),
       nth_error (List.rev (smash_context [] ctx')) 0 = Some d &
       si_Σ ;;; [] ,,, skipn (#|smash_context [] sc_Γb| - 0) (smash_context [] sc_Γb)
         ⊢ decl_type (vass si_na fi_beta) ⇝ decl_type d].
Proof.
  exact (red_it_mkProd_or_LetIn_smash_cb [] sc_Γb fi_P (tProd si_na fi_P fi_P) 0 (vass si_na fi_beta)
           sc_red_prod eq_refl).
Qed.

Definition sc_dp : def term :=
  {| dname := si_na; dtype := it_mkProd_or_LetIn sc_Γb fi_P; dbody := fi_P; rarg := 0 |}.

Lemma red_has_rec_arg_cb_inst : has_rec_arg (def_with_type sc_dp (tProd si_na fi_P fi_P)).
Proof. exact (red_has_rec_arg_cb (d := sc_dp) sc_red_prod eq_refl). Qed.
