(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the lemmas of [PCUICProgressEta] (row T6)

  **The forecast classes are section variables**, as in [PCUICClassificationEtaInstances]: the
  four classes of [PCUICClassificationEta] and [ProgForecastCopy18]. The environments are
  [si_Σ] ([Inductive I (A : Prop) : Prop := c : I A]) and [Σ_po] (the primitive integers,
  [PCUICEtaPrimOpInstance]).

  **Non-degeneracy.**
  - [typing_spine_pred_strengthenE_inst] strengthens a spine of [∀P. P] to the β-redex
    [(λx:Prop. x) (∀P. P)] ([sri_A]).
  - [inversion_mkAppsE_inst] (the sized inversion) runs on the β-redex [(λx:Prop. x) (∀P. P)].
  - [progressE_inst] (through [progress_env_propE] and the induction principle
    [typing_ind_envE], [typing_ind_env_app_sizeE]) and [typing_value_head_nappE_inst] /
    [typing_value_headE_inst] find the β-step of [(λx:Prop. x) (∀P. P)].
  - [eval_tCaseE_inst]: the closed [match c (∀P. P) with c x => c x end] ([pgi_match]), which
    evaluates by ι.
  - [whnf_progressE_inst], [classificationE_inst]: the normal forms [∀P. P] and [c (∀P. P)].
  - The constructor-arity lemmas run on [c (∀P. P) : I (∀P. P)].
  - [typing_spine_lengthE_inst]: the spine of [c] applied to [∀P. P].

  **Conclusions that force an empty spine.** [typing_spine_sortE], [typing_spine_axiomE] and
  [typing_spine_prim_typeE] conclude [args = []]: an instance can only have an empty spine
  (IMPOSSIBLE otherwise, which is what each proves). Their instances have it.

  **Helpers run by the instances above:** [typing_ind_envE], [typing_ind_env_app_sizeE] (by
  [progressE_inst]), [declared_constructor_ind_declE] (also its own instance). *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICReduction PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICClosedBodies PCUICTypingEta
     PCUICTypingEtaInd PCUICTypingEtaNotions PCUICCumulativitySpecEtaClosureInstances PCUICEtaDefs
     PCUICEtaI5 PCUICWellScopedCumulativity PCUICWellScopedCumulativityEta PCUICEtaA6 PCUICEquality
     PCUICConversionEtaCongr PCUICEtaFInst PCUICClosedTypEta PCUICWsCumulEtaCtxTyp
     PCUICInversionEtaInstances PCUICWcbvEval PCUICNormal PCUICConversion PCUICContextConversion
     PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICSpineEta PCUICValidityEta PCUICSREta
     PCUICEtaC1b PCUICEtaPrimOpInstance PCUICSREtaInstances
     PCUICClassification PCUICClassificationEta PCUICClassificationEtaInstances
     PCUICProgress PCUICProgressEta.
From Equations.Type Require Import Relation.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.
#[local] Existing Instance si_wfE.
#[local] Existing Instance iv_po_wfE.

(** ** Derivations, without any class *)

(** [∀P:Prop. P] and [c (∀P:Prop. P)] are [red1]-normal, in any environment and context. *)
Lemma pgi_False_normal Σ Γ v : red1 Σ Γ iv_False v -> False.
Proof.
  unfold iv_False. intros H. inv_red H.
  - eapply red_normal_Sort; eassumption.
  - eapply red_normal_Rel0; eassumption.
Qed.

Lemma pgi_Construct_normal Σ Γ i n u v : red1 Σ Γ (tConstruct i n u) v -> False.
Proof. intros H. inv_red H. Qed.

Lemma pgi_cF_normal Σ Γ v : red1 Σ Γ sri_cF v -> False.
Proof.
  unfold sri_cF. intros H. inv_red H; try discriminate.
  - eapply pgi_Construct_normal; eassumption.
  - eapply pgi_False_normal; eassumption.
Qed.

(** A spine of [∀P:Prop. P] with the trivial predicate. *)
Lemma pgi_sp_pred : typing_spine_predE si_Σ [] (fun _ _ _ => True) iv_False [iv_False] iv_False.
Proof.
  eapply (type_spine_pred_consE _ _ _ iv_False iv_False [] si_na si_P (tRel 0) iv_False sProp).
  - exact (cli_False_isType [] localenv_nil).
  - exact I.
  - exact (cli_False_refl [] localenv_nil).
  - exact I.
  - econstructor; [exact (cli_False_isType [] localenv_nil)|exact (cli_False_isType [] localenv_nil)|].
    exact (cli_False_refl [] localenv_nil).
  Unshelve.
  - exact (iv_False_typed si_Σ [] localenv_nil).
  - exact (iv_False_typed si_Σ [] localenv_nil).
Qed.

Lemma pgi_A_ws : ws_cumul_pbE Cumul si_Σ [] sri_A iv_False.
Proof.
  apply (red_ws_cumul_pbE (Σ := si_Σ)).
  exact (closed_red_of (Σ := si_Σ) (Γ := []) (t := sri_A) eq_refl eq_refl (red1_red _ _ _ _ (sri_beta []))).
Qed.

(** The spine of [c] applied to [∀P:Prop. P]. *)
Lemma pgi_cstr_isType : isTypeE si_Σ [] (tProd si_na si_P (tApp (tInd si_ind []) (tRel 0))).
Proof. exact (has_sort_isTypeE _ (iv_cstr_prod_typed [] localenv_nil)). Qed.

Lemma pgi_IF_isType : isTypeE si_Σ [] iv_IF.
Proof. exact (has_sort_isTypeE _ (iv_IF_typed [] localenv_nil)). Qed.

Lemma pgi_sp_cstr :
  PCUICAritiesEta.typing_spineE si_Σ []
    (it_mkProd_or_LetIn [vass si_na si_P] (mkApps (tInd si_ind []) [tRel 0])) [iv_False] iv_IF.
Proof.
  eapply (@type_spine_consE _ _ _ _ iv_False [] si_na si_P (tApp (tInd si_ind []) (tRel 0)) iv_IF).
  - exact pgi_cstr_isType.
  - exact pgi_cstr_isType.
  - exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) [] _ pgi_cstr_isType).
  - exact (iv_False_typed si_Σ [] localenv_nil).
  - econstructor; [exact pgi_IF_isType|exact pgi_IF_isType|].
    exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) [] _ pgi_IF_isType).
Qed.

Lemma pgi_sp_sort : PCUICAritiesEta.typing_spineE si_Σ [] (tSort sProp) [] (tSort sProp).
Proof.
  have h : isTypeE si_Σ [] (tSort sProp) := has_sort_isTypeE _ (iv_P_typed si_Σ [] localenv_nil).
  econstructor; [exact h|exact h|exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) [] _ h)].
Qed.

(** The closed [match c (∀P. P) as z in I x return I x with c => c x end]. *)
Definition pgi_match : term := Eval cbn in iv_match {0 := iv_False}.
Definition pgi_match_ty : term := Eval cbn in iv_match_ty {0 := iv_False}.

Lemma pgi_match_typed : si_Σ ;;; [] |-E pgi_match : pgi_match_ty.
Proof. exact (substitution0E (Σ := si_Σ) (wfΣ := si_wfE) (Γ := []) iv_match_typed (iv_False_typed si_Σ [] localenv_nil)). Qed.

Lemma pgi_match_eval : eval si_Σ pgi_match sri_cF.
Proof.
  eapply (eval_iota _ iv_ci sri_cF 0 si_mdecl si_idecl si_cdecl [] [iv_False]).
  - exact cli_cF_eval.
  - reflexivity.
  - exact (declared_constructor_to_gen (wfΣ := si_wf) si_declared_constructor).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact cli_cF_eval.
Qed.

(** [Σ_po]: the type of the literal [1] is the primitive integer type, a constant without body. *)
#[local] Instance pgi_po_cb : ClosedBodies Σ_po0 := @wfE_ClosedBodies _ Σ_po0 iv_po_wfE.

Section ProgressEtaInstances.

(* FORECAST-ONLY: the four classes of [PCUICClassificationEta] and [ProgForecastCopy18]; delete
   each when its copy lands. *)
Context {V16 : ValForecastCopy16} {F16 : SRForecastCopy16} {F18 : SRForecastCopy18}
  {C16 : ClassifForecastCopy16} {P18 : ProgForecastCopy18}.

Definition eval_tCaseE_inst := eval_tCaseE (Σ := si_Σ) _ _ _ _ _ _ si_wfE pgi_match_typed pgi_match_eval.

Definition typing_spine_pred_strengthenE_inst :=
  typing_spine_pred_strengthenE (Σ := si_Σ) (wfΣ := si_wfE) pgi_sp_pred (cli_False_isType [] localenv_nil)
    sri_A sri_A_isType pgi_A_ws.

Definition inversion_mkAppsE_inst :=
  PCUICProgressEta.inversion_mkAppsE (Σ := si_Σ) (wfΣ := si_wfE) (f := iv_id) (u := [iv_False])
    (Sort.super sProp) (iv_app_typed si_Σ [] localenv_nil) (iv_P_typed si_Σ [] localenv_nil).

Definition typing_spine_lengthE_inst : #|[iv_False]| <= context_assumptions [vass si_na si_P] :=
  typing_spine_lengthE (Σ := si_Σ) (wfΣ := si_wfE) [] [vass si_na si_P] si_ind [] [tRel 0] [iv_False] iv_IF pgi_sp_cstr.

Definition declared_constructor_ind_declE_inst :=
  declared_constructor_ind_declE (Σ := si_Σ) (wfΣ := si_wfE) si_declared_constructor.

Definition typing_constructor_arity_exactE_inst : #|[iv_False]| = cstr_arity si_mdecl si_cdecl :=
  typing_constructor_arity_exactE (Σ := si_Σ) (wfΣ := si_wfE) (args := [iv_False]) (indices := [iv_False])
    si_declared_constructor sri_cF_typed.

Definition typing_constructor_arityE_inst : #|[iv_False]| <= cstr_arity si_mdecl si_cdecl :=
  typing_constructor_arityE (Σ := si_Σ) (wfΣ := si_wfE) (args := [iv_False]) si_declared_constructor sri_cF_typed.

Definition typing_spine_sortE_inst : @nil term = [] :=
  typing_spine_sortE (Σ := si_Σ) (wfΣ := si_wfE) [] sProp [] (tSort sProp) pgi_sp_sort.

Lemma pgi_int_isType : isTypeE Σ_po [] (prim_type iv_one po_int_kn).
Proof. exact (validityE (Σ := Σ_po) (wfΣ := iv_po_wfE) iv_prim_typed). Qed.

Lemma pgi_sp_int : PCUICAritiesEta.typing_spineE Σ_po [] (prim_type iv_one po_int_kn) [] (prim_type iv_one po_int_kn).
Proof.
  econstructor; [exact pgi_int_isType|exact pgi_int_isType|].
  exact (isType_ws_cumul_pbE_refl (Σ := Σ_po) [] _ pgi_int_isType).
Qed.

Definition typing_spine_prim_typeE_inst : @nil term = [] :=
  typing_spine_prim_typeE (Σ := Σ_po) (wfΣ := iv_po_wfE) [] iv_one po_int_kn po_int_body [] _ eq_refl
    iv_po_declared_int (conj eq_refl eq_refl) pgi_sp_int.

Definition typing_spine_axiomE_inst : @nil term = [] :=
  typing_spine_axiomE (Σ := Σ_po) (wfΣ := iv_po_wfE) [] po_int_kn [] po_int_body [] [] _
    iv_po_declared_int eq_refl eq_refl pgi_sp_int.

Definition typing_value_head_nappE_inst :=
  typing_value_head_nappE (Σ := si_Σ) (wfΣ := si_wfE) iv_id [] iv_False si_P eq_refl
    (iv_app_typed si_Σ [] localenv_nil) (value_atomic _ _ (atomic_atom _ _ eq_refl)) eq_refl
    (value_atomic _ _ (atomic_atom _ _ eq_refl)).

Definition typing_value_headE_inst :=
  typing_value_headE (Σ := si_Σ) (wfΣ := si_wfE) iv_id [] iv_False si_P
    (iv_app_typed si_Σ [] localenv_nil) (value_atomic _ _ (atomic_atom _ _ eq_refl)) eq_refl
    (value_atomic _ _ (atomic_atom _ _ eq_refl)).

Definition progress_env_propE_inst :=
  env_propE_typing progress_env_propE si_Σ si_wfE [] _ _ (iv_app_typed si_Σ [] localenv_nil)
    cli_axiom_free eq_refl (iv_app_typed si_Σ [] localenv_nil).

Definition progressE_inst :=
  progressE si_Σ (tApp iv_id iv_False) si_P cli_axiom_free si_wfE (iv_app_typed si_Σ [] localenv_nil).

Definition whnf_progressE_inst :=
  whnf_progressE si_Σ iv_False si_P cli_axiom_free si_wfE (iv_False_typed si_Σ [] localenv_nil)
    (fun h => let (t', r) := h in pgi_False_normal _ _ _ r).

Definition classificationE_inst :=
  classificationE si_Σ sri_cF si_ind [] [iv_False] cli_axiom_free si_wfE
    (fun h => let (t', r) := h in pgi_cF_normal _ _ _ r) sri_cF_typed.

End ProgressEtaInstances.
