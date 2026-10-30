(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the hypotheses of [PCUICSREtaConv]

  Each lemma of [PCUICSREtaConv] that has a premise is applied here to a concrete instance with
  every premise proved. The environment is [si_Σ] of [PCUICCumulativitySpecEtaClosureInstances]
  ([Inductive I (A : Prop) : Prop := c : I A]; [si_cb], [si_wfE]). The terms are those of
  [PCUICEtaFracInstances] and [PCUICWsCumulEtaCtxInstances]: [fi_P := Prop], the β-redex
  [fi_beta := (λx:Prop. x) Prop], the η-redex [fi_eta := λx:Prop. Prop x], the identity [ci_id]
  of [Prop], [ci_False := ∀P:Prop. P], two λ-terms [ci_lam], [ci_lam'] that differ only in a
  binder name.

  Where a lemma relates two things, the instance relates two different things, and its NONDEGEN
  lemma states the difference: [(λx:Prop. x) Prop] against [Prop], [λx:Prop. Prop x] against
  [Prop], two contexts that differ in a let-body, in an assumption type or in a binder name, two
  types [(λy:Prop. y) x] and [x]. Each instance carries its tag (the instance-gate grammar); the
  lemmas that are degenerate by their statement are tagged IMPOSSIBLE at their instance.
  [conv_context_rel_relnE] and [conv_context_rel_to_extended_listE] run on two contexts with a
  let above an assumption, whose [reln] output is not empty ([sc_Γm_reln_nondeg]).
  [declared_inductive_closed_params_instE] has no relation in it; its instance has a non-empty
  parameter context. [ws_cumul_ctx_pbE_cons_inv] is an inversion helper; its instance is the
  context pair of [sc_ctx_conv]. The reduction lemmas are applied to the reduction of
  [Π x:(λy:Prop. y) Prop. Prop] to [Π x:Prop. Prop] ([red_it_mkProd_or_LetIn_smash_cb],
  [red_has_rec_arg_cb]), to that of [(λy:Prop. y) Prop] to [Prop] ([closed_red_from_empty_cb]),
  and to the unfolding of a let-bound variable ([red_expand_let_cb], [red_expand_letE]).

  WITNESSES: sc_*
  (the concrete contexts, definitions and derivations [sc_*] that the instances use; the NONDEGEN
  lemmas among them are classified by their tags) *)

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
     PCUICSREtaConv.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

Local Notation WS pb Γ := (ws_cumul_pbE pb si_Σ Γ).

(** ** Concrete data *)

(** One-assumption contexts with the types [(λy:Prop. y) Prop] and [Prop]. *)
Definition sc_Γb : context := [vass si_na fi_beta].

Lemma sc_ctx_beta : ws_cumul_ctx_pbE Conv si_Σ ([] ,,, sc_Γb) ([] ,,, fi_Γ1).
Proof. constructor; [constructor|]. constructor; [reflexivity|exact (fi_WS_beta Conv)]. Qed.

(** The contexts [x : (λy:Prop. y) Prop] and [x : Prop] differ. *)
Lemma sc_Γb_differs : sc_Γb <> fi_Γ1.
Proof. discriminate. Qed.

(** One-let contexts whose bodies are [λx:Prop. Prop x] and [Prop], at [Conv]. *)
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

(** Mixed contexts: the let [z := λx:Prop. Prop x : Prop] / [z := Prop : Prop] above the
    assumption [x : (λy:Prop. y) Prop] / [x : Prop]. *)
Definition sc_Γm1 : context := [vdef si_na fi_eta fi_P; vass si_na fi_beta].
Definition sc_Γm2 : context := [vdef si_na fi_P fi_P; vass si_na fi_P].

Lemma sc_rel_m : ws_cumul_ctx_pbE_rel Conv si_Σ [] sc_Γm1 sc_Γm2.
Proof.
  split; [reflexivity|]. constructor.
  - constructor; [constructor|]. constructor; [reflexivity|exact (fi_WS_beta Conv)].
  - constructor; [reflexivity| |].
    + apply eta1_ws_cumul_pbE; [reflexivity|reflexivity|exact fi_eta1].
    + apply ws_cumul_pbE_refl; reflexivity.
Qed.

(** What [reln] reads of [sc_Γm1]: it keeps the assumption and skips the let, whose index shift
    the output shows ([tRel (n + 1)]), so the output is not empty; and the two related contexts
    differ. *)
Lemma sc_Γm_reln_nondeg :
  [/\ (forall acc n, reln acc n sc_Γm1 = tRel (n + 1) :: acc),
      to_extended_list sc_Γm1 = [tRel 1] &
      sc_Γm1 <> sc_Γm2].
Proof. split; [intros acc n; reflexivity|reflexivity|discriminate]. Qed.

(** One step of context reduction: the type [fi_beta] reduces to [fi_P]. *)
Lemma sc_one : OnOne2_local_env (fun Δ : context => on_one_decl (red1 si_Σ ([] ,,, Δ))) sc_Γb fi_Γ1.
Proof.
  apply onone2_localenv_cons_abs. cbn. split; [reflexivity|].
  exact (red_beta si_Σ _ si_na fi_P (tRel 0) fi_P).
Qed.

(** ** Items 1-2 *)

(** The two head declarations differ in their body: [λx:Prop. Prop x] against [Prop]. *)
Lemma ws_cumul_ctx_pbE_cons_inv_inst_nondeg : vdef si_na fi_eta fi_P <> vdef si_na fi_P fi_P.
Proof. discriminate. Qed.

(** INSTANCE NONDEGEN PCUICSREtaConvInstances.ws_cumul_ctx_pbE_cons_inv_inst_nondeg *)
Lemma ws_cumul_ctx_pbE_cons_inv_inst :
  ws_cumul_ctx_pbE Conv si_Σ [] [] × ws_cumul_declsE Conv si_Σ [] (vdef si_na fi_eta fi_P) (vdef si_na fi_P fi_P).
Proof.
  exact (ws_cumul_ctx_pbE_cons_inv (d := vdef si_na fi_eta fi_P) (d' := vdef si_na fi_P fi_P) sc_ctx_conv).
Qed.

(** The contexts [x : (λy:Prop. y) Prop] and [x : Prop] differ, and the bodies [λz:Prop. Prop z]
    and [Prop] differ. *)
Lemma ws_cumul_pbE_it_mkLambda_or_LetIn_inst_nondeg : sc_Γb <> fi_Γ1 /\ fi_eta <> fi_P.
Proof. split; discriminate. Qed.

(** [λx:(λy:Prop. y) Prop. λz:Prop. Prop z] and [λx:Prop. Prop].
    INSTANCE NONDEGEN PCUICSREtaConvInstances.ws_cumul_pbE_it_mkLambda_or_LetIn_inst_nondeg *)
Lemma ws_cumul_pbE_it_mkLambda_or_LetIn_inst :
  WS Cumul [] (it_mkLambda_or_LetIn sc_Γb fi_eta) (it_mkLambda_or_LetIn fi_Γ1 fi_P).
Proof.
  apply (ws_cumul_pbE_it_mkLambda_or_LetIn (Γ := []) (Δ1 := sc_Γb) (Δ2 := fi_Γ1) sc_ctx_beta).
  apply eta1_ws_cumul_pbE; [reflexivity|reflexivity|exact fi_eta1].
Qed.

(** [x → x] over [x : Prop]: the variable [x] occurs in the domain and under the binder. *)
Definition sc_x_to_x : term := tProd si_na (tRel 0) (tRel 1).

(** The type [x → x] is not a bare variable; substituting [(λy:Prop. y) Prop] for [x] gives
    [(λy:Prop. y) Prop → (λy:Prop. y) Prop], and substituting [Prop] gives [Prop → Prop]; each
    result is not the term substituted, and the two results differ. *)
Lemma substitution_ws_cumul_ctx_pbE_red_subst_inst_nondeg :
  [/\ (forall k, sc_x_to_x <> tRel k),
      subst_context [fi_beta] 0 [vass si_na sc_x_to_x] = [vass si_na (tProd si_na fi_beta fi_beta)],
      subst_context [fi_P] 0 [vass si_na sc_x_to_x] = [vass si_na (tProd si_na fi_P fi_P)],
      tProd si_na fi_beta fi_beta <> fi_beta /\ tProd si_na fi_P fi_P <> fi_P &
      tProd si_na fi_beta fi_beta <> tProd si_na fi_P fi_P].
Proof. split; [intros k; discriminate|reflexivity|reflexivity|split; discriminate|discriminate]. Qed.

(** Substituting [(λy:Prop. y) Prop] and [Prop], related by [fi_closed_red_beta], for [x] in
    [x' : x → x] ([sc_x_to_x]); the results are given by
    [substitution_ws_cumul_ctx_pbE_red_subst_inst_nondeg].
    INSTANCE NONDEGEN PCUICSREtaConvInstances.substitution_ws_cumul_ctx_pbE_red_subst_inst_nondeg *)
Lemma substitution_ws_cumul_ctx_pbE_red_subst_inst :
  ws_cumul_ctx_pbE Conv si_Σ ([] ,,, subst_context [fi_beta] 0 [vass si_na sc_x_to_x])
    ([] ,,, subst_context [fi_P] 0 [vass si_na sc_x_to_x]).
Proof.
  apply (substitution_ws_cumul_ctx_pbE_red_subst (Γ := []) (Δ := [vass si_na fi_P])
           (s := [fi_beta]) (s' := [fi_P])).
  - reflexivity.
  - constructor; [exact fi_closed_red_beta|constructor].
  - exact ci_untyped_subslet.
Qed.

(** The two types differ (in a binder name). *)
Lemma eq_context_upto_ws_cumul_ctx_pbE_inst_nondeg : ci_lam <> ci_lam'.
Proof. discriminate. Qed.

(** Two contexts whose types [compare_term] relates without being equal.
    INSTANCE NONDEGEN PCUICSREtaConvInstances.eq_context_upto_ws_cumul_ctx_pbE_inst_nondeg *)
Lemma eq_context_upto_ws_cumul_ctx_pbE_inst :
  ws_cumul_ctx_pbE Cumul si_Σ [vass si_na ci_lam] [vass si_na ci_lam'].
Proof.
  apply (eq_context_upto_ws_cumul_ctx_pbE (Γ := [vass si_na ci_lam]) (Γ' := [vass si_na ci_lam']));
    [reflexivity|reflexivity|].
  constructor; [constructor|]. constructor; [reflexivity|exact (ci_eq_lam Cumul)].
Qed.

(** ** Item 3 *)

(** The fixpoint witness: a declared type [fi_beta], witness [fi_eta], reduct [fi_P]. *)
Definition sc_check : def term -> option kername := fun _ => Some si_kn.
Definition sc_d : def term := {| dname := si_na; dtype := fi_beta; dbody := fi_P; rarg := 0 |}.

(** Retyping [sc_d], whose declared type is [(λy:Prop. y) Prop], at [Prop] changes the
    definition. *)
Lemma sc_d_retyped_differs : def_with_type sc_d fi_P <> sc_d.
Proof. discriminate. Qed.

Lemma sc_body_on : mfix_body_on sc_check (conv_witnessE si_Σ []) si_kn sc_d.
Proof.
  exists fi_eta. split; [reflexivity|]. split; [reflexivity|].
  exact (ws_cumul_pbE_forget_spec (ws_cumul_pbE_trans _ _ _ (fi_WS_beta Conv) (ci_WS_eta_r Conv))).
Qed.

(* INSTANCE NONDEGEN PCUICSREtaConvInstances.sc_d_retyped_differs *)
Lemma mfix_body_on_red_typeE_inst :
  mfix_body_on sc_check (conv_witnessE si_Σ []) si_kn (def_with_type sc_d fi_P).
Proof. exact (mfix_body_on_red_typeE (d := sc_d) fi_closed_red_beta sc_body_on). Qed.

(* INSTANCE NONDEGEN PCUICSREtaConvInstances.sc_d_retyped_differs *)
Lemma mfix_on_ind_red1_typeE_inst :
  mfix_on_ind sc_check (conv_witnessE si_Σ []) (fun _ => true) [def_with_type sc_d fi_P].
Proof.
  apply (mfix_on_ind_red1_typeE [] [sc_d]).
  - constructor. split; [exact fi_closed_red_beta|reflexivity].
  - exists si_kn. split; [discriminate|]. split; [|reflexivity].
    constructor; [exact sc_body_on|constructor].
Qed.

(** [reln] on the mixed contexts related by [sc_rel_m]: the output is [tRel (n + 1) :: acc], not
    empty, and the two contexts differ ([sc_Γm_reln_nondeg]).
    INSTANCE NONDEGEN PCUICSREtaConvInstances.sc_Γm_reln_nondeg *)
Lemma conv_context_rel_relnE_inst : forall acc n, reln acc n sc_Γm1 = reln acc n sc_Γm2.
Proof. exact (conv_context_rel_relnE [] sc_Γm1 sc_Γm2 sc_rel_m). Qed.

(** [to_extended_list] on the same contexts: the output is [[tRel 1]] ([sc_Γm_reln_nondeg]).
    INSTANCE NONDEGEN PCUICSREtaConvInstances.sc_Γm_reln_nondeg *)
Lemma conv_context_rel_to_extended_listE_inst : to_extended_list sc_Γm1 = to_extended_list sc_Γm2.
Proof. exact (conv_context_rel_to_extended_listE (Δ := sc_Γm1) (Δ' := sc_Γm2) sc_rel_m). Qed.

(** Two contexts that differ only in a binder name.
    INSTANCE IMPOSSIBLE: the premise [eq_context_upto_names Δ Δ'] forces each pair of declarations to have identical types (and bodies), only the binder names may differ ([eq_decl_upto_names]), and the proof of [eq_context_alpha_convE] relates each type (and body) to itself by [ws_cumul_pbE_refl]; so in every instance and environment every declaration comparison of the conclusion is reflexive. *)
Lemma eq_context_alpha_convE_inst :
  ws_cumul_ctx_pbE_rel Conv si_Σ [] [vass si_na fi_P] [vass (mkBindAnn (nNamed "x") Relevant) fi_P].
Proof.
  apply (eq_context_alpha_convE [] [vass si_na fi_P] [vass (mkBindAnn (nNamed "x") Relevant) fi_P]);
    [repeat constructor|reflexivity|reflexivity].
Qed.

Definition sc_nas : list aname := [mkBindAnn (nNamed "x") Relevant].

(** The renaming changes the context, and the two related contexts differ in the let-body. *)
Lemma conv_ctx_set_binder_nameE_inst_nondeg :
  map2 set_binder_name sc_nas sc_Γd1 <> sc_Γd1 /\ sc_Γd1 <> sc_Γd2.
Proof. split; discriminate. Qed.

(* INSTANCE NONDEGEN PCUICSREtaConvInstances.conv_ctx_set_binder_nameE_inst_nondeg *)
Lemma conv_ctx_set_binder_nameE_inst :
  ws_cumul_ctx_pbE_rel Conv si_Σ [] (map2 set_binder_name sc_nas sc_Γd1) (map2 set_binder_name sc_nas sc_Γd2).
Proof.
  apply (conv_ctx_set_binder_nameE [] sc_Γd1 sc_Γd2 sc_nas);
    [repeat constructor|repeat constructor|exact sc_rel_d].
Qed.

(* INSTANCE NONDEGEN PCUICSREtaConvInstances.sc_Γb_differs *)
Lemma red_one_decl_red_ctx_cb_inst : red_ctx si_Σ ([] ,,, sc_Γb) ([] ,,, fi_Γ1).
Proof. exact (red_one_decl_red_ctx_cb (Γ := []) (Δ := sc_Γb) (Δ' := fi_Γ1) eq_refl sc_one). Qed.

(* INSTANCE NONDEGEN PCUICSREtaConvInstances.sc_Γb_differs *)
Lemma into_closed_red_ctx_cb_inst : closed_red_ctx si_Σ ([] ,,, sc_Γb) ([] ,,, fi_Γ1).
Proof. exact (into_closed_red_ctx_cb (Γ := [] ,,, sc_Γb) (Δ := [] ,,, fi_Γ1) eq_refl red_one_decl_red_ctx_cb_inst). Qed.

(* INSTANCE NONDEGEN PCUICSREtaConvInstances.sc_Γb_differs *)
Lemma red_one_decl_red_context_cb_inst : closed_red_ctx si_Σ ([] ,,, sc_Γb) ([] ,,, fi_Γ1).
Proof. exact (red_one_decl_red_context_cb (Γ := []) (Δ := sc_Γb) (Δ' := fi_Γ1) eq_refl sc_one). Qed.

(* INSTANCE NONDEGEN PCUICSREtaConvInstances.sc_Γb_differs *)
Lemma red_one_decl_ws_cumul_ctx_pbE_inst : ws_cumul_ctx_pbE Conv si_Σ ([] ,,, sc_Γb) ([] ,,, fi_Γ1).
Proof. exact (red_one_decl_ws_cumul_ctx_pbE (Γ := []) (Δ := sc_Γb) (Δ' := fi_Γ1) eq_refl sc_one). Qed.

(* INSTANCE IMPOSSIBLE: the premise T = U makes both sides of the conclusion the same term, in every instance and environment *)
Lemma ws_cumul_pbE_meta_refl_inst : WS Conv [] fi_P fi_P.
Proof. exact (ws_cumul_pbE_meta_refl (Σ := si_Σ) (Γ := []) (T := fi_P) (U := fi_P) eq_refl eq_refl eq_refl). Qed.

(* This instance relates the β-pair [fi_beta], [fi_P].
   INSTANCE IMPOSSIBLE: the premise U = V makes the conclusion the first premise (T related to U), in every instance and environment *)
Lemma ws_cumul_pbE_eq_trans_inst : WS Conv [] fi_beta fi_P.
Proof. exact (ws_cumul_pbE_eq_trans (fi_WS_beta Conv) eq_refl). Qed.

(* This instance relates the β-pair [fi_beta], [fi_P].
   INSTANCE IMPOSSIBLE: the premise T = U makes the conclusion the second premise (U related to V), in every instance and environment *)
Lemma eq_ws_cumul_pbE_trans_inst : WS Conv [] fi_beta fi_P.
Proof. exact (eq_ws_cumul_pbE_trans eq_refl (fi_WS_beta Conv)). Qed.

(* This instance relates [[fi_beta]] with [[fi_P]].
   INSTANCE IMPOSSIBLE: the premise U = V makes the conclusion the first premise (T related to U), in every instance and environment *)
Lemma ws_cumul_pbE_terms_eq_trans_inst : ws_cumul_pbE_terms si_Σ [] [fi_beta] [fi_P].
Proof. exact (ws_cumul_pbE_terms_eq_trans ci_WT eq_refl). Qed.

(* This instance relates [[fi_beta]] with [[fi_P]].
   INSTANCE IMPOSSIBLE: the premise T = U makes the conclusion the second premise (U related to V), in every instance and environment *)
Lemma eq_ws_cumul_pbE_terms_trans_inst : ws_cumul_pbE_terms si_Σ [] [fi_beta] [fi_P].
Proof. exact (eq_ws_cumul_pbE_terms_trans eq_refl ci_WT). Qed.

(** Over [x : Prop], the let-contexts [z := (λy:Prop. y) x : Prop] and [z := x : Prop]: their
    bodies are a β-pair that refers to [x]. *)
Definition sc_Δo1 : context := [vdef si_na (tApp ci_id (tRel 0)) fi_P].
Definition sc_Δo2 : context := [vdef si_na (tRel 0) fi_P].

Lemma sc_closed_red1_open : closed_red1 si_Σ fi_Γ1 (tApp ci_id (tRel 0)) (tRel 0).
Proof. split; [reflexivity|reflexivity|exact (red_beta si_Σ fi_Γ1 si_na fi_P (tRel 0) (tRel 0))]. Qed.

Lemma sc_ctx_open : ws_cumul_ctx_pbE Conv si_Σ (fi_Γ1 ,,, sc_Δo1) (fi_Γ1 ,,, sc_Δo2).
Proof.
  constructor; [exact (ws_cumul_ctx_pbE_refl_pb (Γ := fi_Γ1) eq_refl)|].
  constructor; [reflexivity|exact (closed_red1_ws_cumul_pbE sc_closed_red1_open)|].
  apply ws_cumul_pbE_refl; reflexivity.
Qed.

(** The lift by [#|fi_Γ1|] changes [sc_Δo1] (its body refers to [x]); the two contexts
    [z := (λy:Prop. y) x : Prop] and [z := x : Prop] differ, and so do their two lifts, which end
    the two contexts the instance relates. *)
Lemma weakening_ws_cumul_ctx_pbE_inst_nondeg :
  lift_context #|fi_Γ1| 0 sc_Δo1 <> sc_Δo1 /\ sc_Δo1 <> sc_Δo2 /\
  lift_context #|fi_Γ1| 0 sc_Δo1 <> lift_context #|fi_Γ1| 0 sc_Δo2.
Proof. split; [discriminate|split; discriminate]. Qed.

(** Weakening the let-contexts [z := (λy:Prop. y) x : Prop] and [z := x : Prop] by [w : Prop],
    inserted between [x : Prop] and [z].
    INSTANCE NONDEGEN PCUICSREtaConvInstances.weakening_ws_cumul_ctx_pbE_inst_nondeg *)
Lemma weakening_ws_cumul_ctx_pbE_inst :
  ws_cumul_ctx_pbE Conv si_Σ (fi_Γ1 ,,, fi_Γ1 ,,, lift_context #|fi_Γ1| 0 sc_Δo1)
    (fi_Γ1 ,,, fi_Γ1 ,,, lift_context #|fi_Γ1| 0 sc_Δo2).
Proof.
  apply (weakening_ws_cumul_ctx_pbE (Γ := fi_Γ1) (Δ := fi_Γ1) sc_ctx_open).
  exact (ws_cumul_ctx_pbE_refl_pb (Γ := fi_Γ1 ,,, fi_Γ1) eq_refl).
Qed.

Lemma sc_closed_red1_beta : closed_red1 si_Σ [] fi_beta fi_P.
Proof. split; [reflexivity|reflexivity|exact (red_beta si_Σ [] si_na fi_P (tRel 0) fi_P)]. Qed.

(** The two related terms differ: [(λy:Prop. y) Prop] and [Prop]. *)
Lemma closed_red1_ws_cumul_pbE_inst_nondeg : fi_beta <> fi_P.
Proof. discriminate. Qed.

(* INSTANCE NONDEGEN PCUICSREtaConvInstances.closed_red1_ws_cumul_pbE_inst_nondeg *)
Lemma closed_red1_ws_cumul_pbE_inst : WS Conv [] fi_beta fi_P.
Proof. exact (closed_red1_ws_cumul_pbE (t := fi_beta) (u := fi_P) sc_closed_red1_beta). Qed.

(** *** The typed lemmas *)

(* INSTANCE IMPOSSIBLE: the conclusion relates the term t with itself, in every instance and environment *)
Lemma wt_cumul_pb_reflE_inst : WS Conv fi_Γ1 (tRel 0) (tRel 0).
Proof. exact (wt_cumul_pb_reflE (Σ := si_Σ) (wfΣ := si_wfE) ci_x_typed). Qed.

(* INSTANCE IMPOSSIBLE: the conclusion relates the list ts with itself, in every instance and environment *)
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

(** The type [(λy:Prop. y) x] of [h] and the type [x] it is moved to differ. *)
Lemma type_Cumul_altE_inst_nondeg : tApp ci_id (tRel 1) <> tRel 1.
Proof. discriminate. Qed.

(* INSTANCE NONDEGEN PCUICSREtaConvInstances.type_Cumul_altE_inst_nondeg *)
Lemma type_Cumul_altE_inst : si_Σ ;;; sc_Γh |-E tRel 0 : tRel 1.
Proof.
  exact (type_Cumul_altE (Σ := si_Σ) (wfΣ := si_wfE) sc_Γh (tRel 0) (tApp ci_id (tRel 1)) (tRel 1)
           sc_h_typed (ci_on_typeE_Prop _ _ sc_x_typed) (JoinE_red_l si_Σ sc_Γh Cumul _ _ sc_red_h)).
Qed.

(** ** Environment and reduction facts *)

(** The parameter context [A : Prop] of [I] is not empty: the closedness is checked on a
    declaration. *)
Lemma declared_inductive_closed_params_instE_inst_nondeg : ind_params si_mdecl <> [].
Proof. discriminate. Qed.

(** [closed_ctx] is a boolean, so it computes on every concrete parameter context; [I] is
    monomorphic, so [subst_instance [Set]] leaves its parameters unchanged.
    INSTANCE NONDEGEN PCUICSREtaConvInstances.declared_inductive_closed_params_instE_inst_nondeg *)
Lemma declared_inductive_closed_params_instE_inst : closed_ctx (subst_instance [Level.lzero] (ind_params si_mdecl)).
Proof.
  exact (declared_inductive_closed_params_instE (Σ := si_Σ) (wfΣ := si_wfE) (mdecl := si_mdecl)
           (u := [Level.lzero]) si_declared_inductive).
Qed.

(** The let [z := ∀P:Prop. P : Prop]: the variable [z] unfolds to its body. *)
Lemma sc_wf_let : wf_localE si_Σ ([] ,,, [vdef si_na ci_False fi_P]).
Proof.
  apply localenv_cons_def; [constructor|].
  split; [exact (ci_False_typed [] localenv_nil)|].
  exists (Sort.super sProp). split; [exact (ci_typeE_P [] localenv_nil)|]. split; [exact I|reflexivity].
Qed.

(** [lift0 1 (subst1 ci_False 0 (tRel 0))], which is the let-body [∀P:Prop. P] lifted, is not
    [z] ([tRel 0]). *)
Lemma sc_let_unfolds : lift0 1 (subst1 ci_False 0 (tRel 0)) <> tRel 0.
Proof. discriminate. Qed.

(* INSTANCE NONDEGEN PCUICSREtaConvInstances.sc_let_unfolds *)
Lemma red_expand_let_cb_inst :
  si_Σ ;;; [] ,, vdef si_na ci_False fi_P ⊢ tRel 0 ⇝ lift0 1 (subst1 ci_False 0 (tRel 0)).
Proof.
  exact (red_expand_let_cb (Σ := si_Σ) (Γ := []) (na := si_na) (b := ci_False) (ty := fi_P) (t := tRel 0)
           eq_refl eq_refl).
Qed.

(* INSTANCE NONDEGEN PCUICSREtaConvInstances.sc_let_unfolds *)
Lemma red_expand_letE_inst :
  si_Σ ;;; [] ,, vdef si_na ci_False fi_P ⊢ tRel 0 ⇝ lift0 1 (subst1 ci_False 0 (tRel 0)).
Proof.
  exact (red_expand_letE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := []) (na := si_na) (b := ci_False) (ty := fi_P)
           (t := tRel 0) sc_wf_let eq_refl).
Qed.

(** The target context [x : Prop] is not the empty context the reduction starts in, and the two
    terms of the reduction, [(λy:Prop. y) Prop] and [Prop], differ. *)
Lemma closed_red_from_empty_cb_inst_nondeg : fi_Γ1 <> [] /\ fi_beta <> fi_P.
Proof. split; discriminate. Qed.

(** The reduction [fi_beta ⇝ fi_P] in the empty context, moved into [x : Prop].
    INSTANCE NONDEGEN PCUICSREtaConvInstances.closed_red_from_empty_cb_inst_nondeg *)
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

(** The two products [Π x:(λy:Prop. y) Prop. Prop] and [Π x:Prop. Prop] differ (in their
    domain). *)
Lemma red_it_mkProd_or_LetIn_smash_cb_inst_nondeg : it_mkProd_or_LetIn sc_Γb fi_P <> tProd si_na fi_P fi_P.
Proof. discriminate. Qed.

(* INSTANCE NONDEGEN PCUICSREtaConvInstances.red_it_mkProd_or_LetIn_smash_cb_inst_nondeg *)
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

(** Retyping [sc_dp] at [Π x:Prop. Prop] changes the definition. *)
Lemma red_has_rec_arg_cb_inst_nondeg : def_with_type sc_dp (tProd si_na fi_P fi_P) <> sc_dp.
Proof. discriminate. Qed.

(** [has_rec_arg] is a boolean on the type of the definition, so it computes on every concrete
    definition; the type here, [Π x:(λy:Prop. y) Prop. Prop], is replaced by [Π x:Prop. Prop],
    which changes the definition.
    INSTANCE NONDEGEN PCUICSREtaConvInstances.red_has_rec_arg_cb_inst_nondeg *)
Lemma red_has_rec_arg_cb_inst : has_rec_arg (def_with_type sc_dp (tProd si_na fi_P fi_P)).
Proof. exact (red_has_rec_arg_cb (d := sc_dp) sc_red_prod eq_refl). Qed.
