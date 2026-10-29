(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the lemmas of [PCUICValidityEta], and the two T2a contracts

  **The contracts.** The two fields of the checker's [T2a_facts]
  ([safechecker/theories/PCUICTypingEtaHyps.v], branch [wip/etak-k7-2026-10-29] @ [0bbee83d]) and
  the two fields of [SRForecastT2a] ([PCUICSREta.v]) are copied here verbatim and inhabited by
  [validityE] and [inversion_mkAppsE]: [T2a_inversion_mkApps_fit], [T2a_validity_fit],
  [SR_T2a_validityE_fit], [SR_T2a_inversion_mkAppsE_fit]. They take the forecast classes of
  [PCUICValidityEta] as premises, as the two lemmas do.

  **The instances.** Each lemma family of [PCUICValidityEta] with a premise has an instance below,
  in [si_Σ] ([PCUICCumulativitySpecEtaClosureInstances]: [Inductive I (A : Prop) : Prop := c : I A])
  or [iv_Σ] ([PCUICInversionEtaInstances]: a coinductive record with one projection), using the
  derivations of [PCUICInversionEtaInstances]:
  - a lemma that needs no forecast class is APPLIED to concrete premises, each proved;
  - a lemma that needs a forecast class ([validity_envE], [validityE], [inversion_mkAppsE],
    [type_App'E], [type_mkApps_arityE], [declared_projection_typeE]) cannot be applied without
    an instance of that class, so its instance states the premises AND the conclusion at
    concrete arguments, each proved without the lemma and without any class.
  The copy lemmas of copies 10, 12 and 14 that [PCUICValidityEta] proved before those copies
  landed are gone from it; their instances are in [PCUICTypingEtaCopies2Instances].
  The derivation of [validityE_inst] ends in an η step: in the context
  [g : Prop → Prop, k : (Prop → Prop) → Prop, y : k g] the variable [y] is typed at
  [k (λx:Prop. g x)] ([iv_rel_typed]). *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICCases PCUICEquality PCUICArities PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
     PCUICTypingEtaNotions PCUICClosedTypEta PCUICClosedBodies PCUICEtaI5 PCUICWellScopedCumulativityEta
     PCUICWfUniversesEta PCUICWsCumulEtaCtxTyp
     PCUICCumulativitySpecEtaClosureInstances PCUICInversionEtaInstances
     PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICSpineEta PCUICValidityEta.

Local Notation " Σ ;;; Γ ⊢E t ≤ u " := (ws_cumul_pbE Cumul Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢E  t  ≤  u") : type_scope.

(** ** The T2a contracts, verbatim, inhabited by the E lemmas *)

Section ContractFit.

  Context {V16 : ValForecastCopy16}.

  (** The checker's [T2a_facts] (its section variable [{cf : checker_flags}] made a [Context]). *)
  Section Checker.
    Context {cf : checker_flags}.

    Definition T2a_inversion_mkApps_fit :
      forall {Σ : global_env_ext} {wfΣ : wfE Σ.1} {Γ : context} {f : term} {u : list term} {T : term}, Σ;;; Γ |-E mkApps f u : T -> ∑ A : term, Σ;;; Γ |-E f : A × typing_spineE Σ Γ A u T
      := fun Σ wfΣ Γ f u T h => inversion_mkAppsE (wfΣ := wfΣ) h.

    Definition T2a_validity_fit :
      forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t : term} {T : term}, Σ;;; Γ |-E t : T -> isTypeE Σ Γ T
      := fun Σ wfΣ Γ t T h => validityE (wfΣ := wfΣ) h.
  End Checker.

  (** [SRForecastT2a] of [PCUICSREta.v]: the text of its two fields. *)
  Definition SR_T2a_validityE_fit :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ t T},
    Σ ;;; Γ |-E t : T -> isTypeE Σ Γ T
    := fun cf Σ wfΣ Γ t T h => validityE (wfΣ := wfΣ) h.

  Definition SR_T2a_inversion_mkAppsE_fit :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ.1} {Γ f u T},
    Σ ;;; Γ |-E mkApps f u : T ->
    ∑ A, Σ ;;; Γ |-E f : A × typing_spineE Σ Γ A u T
    := fun cf Σ wfΣ Γ f u T h => inversion_mkAppsE (wfΣ := wfΣ) h.

End ContractFit.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

(** ** Lemmas without a forecast premise, applied *)

Definition iv_keta_isType : isTypeE si_Σ iv_Γk iv_keta := has_sort_isTypeE _ iv_keta_typed.
Definition iv_P_isType (Γ : context) (h : wf_localE si_Σ Γ) : isTypeE si_Σ Γ si_P :=
  has_sort_isTypeE _ (iv_P_typed si_Σ Γ h).
Definition iv_PP_isType : isTypeE si_Σ [] iv_PP := has_sort_isTypeE _ (iv_PP_typed si_Σ [] localenv_nil).

(** [isType_weaken_fullE], [isType_extendsE]: [si_env] extends itself. *)
Definition isType_weaken_fullE_inst : isTypeE (si_env, si_Σ.2) iv_Γk iv_keta :=
  isType_weaken_fullE si_Σ si_env si_wfE si_wfE (extends_refl si_env) iv_Γk (tRel 0) iv_keta iv_keta_isType.

Definition isType_extendsE_inst : isTypeE (si_env, Monomorphic_ctx) iv_Γk iv_keta :=
  isType_extendsE si_env si_env Monomorphic_ctx si_wfE si_wfE (extends_refl si_env) iv_Γk iv_keta iv_keta_isType.

Definition isType_Sort_invE_inst : wf_sort si_Σ sProp :=
  isType_Sort_invE (Σ := si_Σ) si_wfE (iv_P_isType iv_Γk iv_wf_Γk).

(** [Prop → Prop] is a well-formed arity at the declaration [I]. *)
Lemma isWfArity_subst_instance_declE_inst :
  isWfArityE si_Σ (subst_instance [] []) (subst_instance [] si_arity).
Proof.
  refine (isWfArity_subst_instance_declE (Σ := si_Σ) (Γ := []) (T := si_arity) (c := si_kn)
            (decl := InductiveDecl si_mdecl) (u := []) si_wfE eq_refl _ eq_refl).
  split; [exact iv_PP_isType|].
  exists [vass si_na si_P], sProp. reflexivity.
Qed.

Definition isType_weakeningE_inst : isTypeE si_Σ iv_Γk si_P :=
  isType_weakeningE (Σ := si_Σ) si_wfE iv_wf_Γk (iv_P_isType [] localenv_nil).

Lemma type_ctx_wf_univE_inst : wf_sort si_Σ (Sort.super sProp).
Proof.
  apply (type_ctx_wf_univE si_Σ [] [vass si_na si_P] (Sort.super sProp)).
  split; [exact (typing_wf_sortE (Σ := si_Σ) si_wfE (iv_P_typed si_Σ [] localenv_nil))|].
  exact (iv_vass_s si_Σ [] si_na si_P (Sort.super sProp) (iv_P_typed si_Σ [] localenv_nil) eq_refl).
Qed.

Definition validity_wf_localE_inst :=
  validity_wf_localE (Σ := si_Σ) iv_Γg [vass si_na (tApp (tRel 0) (tRel 1)); vass si_na iv_K]
    (All_local_env_app_inv (Γ := iv_Γg) (Γ' := [vass si_na (tApp (tRel 0) (tRel 1)); vass si_na iv_K])
       iv_wf_Γk).2.

Definition wf_local_validityE_inst :=
  wf_local_validityE (Σ := si_Σ) (wfΣ := si_wfE) iv_Γg [vass si_na (tApp (tRel 0) (tRel 1)); vass si_na iv_K]
    iv_wf_Γk.

(** ** Lemmas with a forecast premise: premises and conclusion at concrete arguments *)

(** [validity_envE]'s first component holds in every [wfE] environment, by the sort part of each
    judgment (no validity needed). *)
Lemma wfE_validity_global {Σ : global_env} (wfΣ : wfE Σ) :
  on_global_env cumulSpecE0
    (fun Σ Γ j => lift_sorting (fun _ T => isTypeE Σ Γ T) (fun _ s => wf_sort Σ s) j) Σ.
Proof.
  revert Σ wfΣ. apply on_global_env_impl.
  intros Σ Γ [[tm|] ty u r] wfΣ _ (htm & s & hs & e); cbn in *.
  - split; [exact (has_sort_isTypeE s hs)|]. exists s. split; [exact (typing_wf_sortE wfΣ hs)|exact e].
  - split; [exact tt|]. exists s. split; [exact (typing_wf_sortE wfΣ hs)|exact e].
Qed.

(** [validity_envE] and [validityE] at the η derivation [iv_rel_typed]. *)
Lemma validityE_inst :
  [× wfE si_Σ, si_Σ ;;; iv_Γk |-E tRel 0 : iv_keta & isTypeE si_Σ iv_Γk iv_keta].
Proof. split; [exact si_wfE|exact iv_rel_typed|exact iv_keta_isType]. Qed.

Lemma validity_envE_inst :
  on_global_env cumulSpecE0
    (fun Σ Γ j => lift_sorting (fun _ T => isTypeE Σ Γ T) (fun _ s => wf_sort Σ s) j) si_Σ.1 *
  (wf_localE si_Σ iv_Γk * isTypeE si_Σ iv_Γk iv_keta).
Proof.
  split; [exact (wfE_validity_global si_wfE)|].
  split; [exact iv_wf_Γk|exact iv_keta_isType].
Qed.

Definition iv_PP_refl : si_Σ ;;; [] ⊢E iv_PP ≤ iv_PP :=
  isType_ws_cumul_pbE_refl (Σ := si_Σ) (wfΣ := si_wfE) (pb := Cumul) [] iv_PP iv_PP_isType.

Definition iv_P_refl : si_Σ ;;; [] ⊢E si_P ≤ si_P :=
  isType_ws_cumul_pbE_refl (Σ := si_Σ) (wfΣ := si_wfE) (pb := Cumul) [] si_P (iv_P_isType [] localenv_nil).

(** [inversion_mkAppsE] at [(λx:Prop. x) (∀P:Prop. P) : Prop]. *)
Lemma inversion_mkAppsE_inst :
  (si_Σ ;;; [] |-E mkApps iv_id [iv_False] : si_P) ×
  ∑ A, si_Σ ;;; [] |-E iv_id : A × typing_spineE si_Σ [] A [iv_False] si_P.
Proof.
  split; [exact (iv_app_typed si_Σ [] localenv_nil)|].
  exists iv_PP. split; [exact (iv_id_typed si_Σ [] localenv_nil)|].
  eapply (@type_spine_consE _ _ _ iv_PP iv_False [] si_na si_P si_P si_P iv_PP_isType iv_PP_isType iv_PP_refl
            (iv_False_typed si_Σ [] localenv_nil)).
  exact (type_spine_nilE _ _ _ _ (iv_P_isType [] localenv_nil) (iv_P_isType [] localenv_nil) iv_P_refl).
Qed.

Lemma type_App'E_inst :
  [× si_Σ ;;; [] |-E iv_id : tProd si_na si_P si_P, si_Σ ;;; [] |-E iv_False : si_P &
     si_Σ ;;; [] |-E tApp iv_id iv_False : si_P {0 := iv_False}].
Proof.
  split; [exact (iv_id_typed si_Σ [] localenv_nil)|exact (iv_False_typed si_Σ [] localenv_nil)|].
  exact (iv_app_typed si_Σ [] localenv_nil).
Qed.

(** [type_mkApps_arityE] at [I (∀P:Prop. P) : Prop], along the arity [Prop → Prop]. *)
Lemma type_mkApps_arityE_inst :
  [× si_Σ ;;; [] |-E tInd si_ind [] : si_arity,
     arity_spineE si_Σ [] si_arity [iv_False] (tSort sProp) &
     si_Σ ;;; [] |-E mkApps (tInd si_ind []) [iv_False] : tSort sProp].
Proof.
  split; [exact (iv_ind_typed [] localenv_nil)| |].
  - exact (arity_spine_assE _ _ iv_False [] si_na si_P (tSort sProp) (tSort sProp)
             (iv_False_typed si_Σ [] localenv_nil) (arity_spine_nilE _ _ (tSort sProp))).
  - exact (iv_IX_typed [] iv_False localenv_nil (iv_False_typed si_Σ [] localenv_nil)).
Qed.

(** [declared_projection_typeE] at the projection [f] of [R]: its type [A] is a type in the
    context [A : Prop, r : R A]. *)
Lemma declared_projection_typeE_inst :
  wfE iv_Σ.1 × declared_projection iv_Σ iv_proj iv_mdecl iv_idecl iv_cdecl iv_pdecl ×
  let u := abstract_instance (ind_universes iv_mdecl) in
  isTypeE (iv_Σ.1, ind_universes iv_mdecl)
    ((vass {| binder_name := nNamed iv_idecl.(ind_name); binder_relevance := iv_idecl.(ind_relevance) |}
        (mkApps (tInd iv_proj.(proj_ind) u) (to_extended_list (smash_context [] (ind_params iv_mdecl)))))::
      smash_context [] (ind_params iv_mdecl)) iv_pdecl.(proj_type).
Proof.
  split; [exact iv_wfE|split; [exact iv_declared_projection|]].
  have wfA : wf_localE iv_Σ [vass si_na si_P] := iv_wf_P iv_Σ [] localenv_nil.
  have hR : iv_Σ ;;; [vass si_na si_P] |-E iv_R (tRel 0) : si_P.
  { exact (iv_RX_typed _ (tRel 0) wfA (typeE_Rel _ _ 0 (vass si_na si_P) wfA eq_refl)). }
  have wfAr := iv_wf_vass iv_Σ [vass si_na si_P]
    {| binder_name := nNamed iv_idecl.(ind_name); binder_relevance := iv_idecl.(ind_relevance) |}
    (iv_R (tRel 0)) sProp wfA hR eq_refl.
  exact (has_sort_isTypeE sProp (typeE_Rel _ _ 1 (vass si_na si_P) wfAr eq_refl)).
Qed.
