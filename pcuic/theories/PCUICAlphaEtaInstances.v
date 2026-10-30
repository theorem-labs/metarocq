(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the lemmas of [PCUICAlphaEta] (row T6)

  **The environment** is [si_Σ] ([PCUICCumulativitySpecEtaClosureInstances]:
  [Inductive I (A : Prop) : Prop := c : I A], with [si_wfE]); the derivations are those of
  [PCUICInversionEtaInstances], in particular the η-typed variable
  [g : Prop → Prop, k : (Prop → Prop) → Prop, y : k g ⊢ y : k (λ_:Prop. g _)] ([iv_rel_typed]).

  **The α-variants.** [al_Γk] is [iv_Γk] with the variable [y] named [x] (it is anonymous in
  [iv_Γk]); [al_keta] is [iv_keta] with the binder of [λ_:Prop. g _] named [x]; [al_mfix] is the
  fixpoint [iv_mfix] with its name and both binders named [x]; [al_id] and [al_PP] are [λ_:Prop. _]
  and [Prop → Prop] with the binder named [x]. Each differs syntactically from its original
  ([al_Γk_differs], [al_keta_differs], [al_mfix_differs]).

  **Every lemma** is applied to these, every premise proved here. [typing_alpha_propE] and its
  corollaries (which use [validityE] of T2a and a copy-18b lemma) are applied in section
  [AlphaClassInstances], whose [Context] held T1's forecast class until copy 18b landed
  (frac/eta 3e6b422d); the class is deleted and no lemma takes one.

  **Non-degeneracy.** Every instance relates two syntactically different terms, contexts or
  fixpoints, except [cmp_global_instance_empty_eq_inst]: that lemma concludes [u = u'] from a
  comparison that is equality, so an instance with [u ≠ u'] is IMPOSSIBLE (a property of the
  statement). [eq_context_conversionE_inst] and [typing_alpha_propE_inst] move the η derivation
  [iv_rel_typed] into the renamed context. [inst_case_predicate_context_eqE_inst] relates the two
  different constructions [case_predicate_context] and [inst_case_predicate_context] of the
  [match] predicate [iv_mp]. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICCases PCUICEquality PCUICReduction PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICClosedBodies PCUICTypingEta PCUICTypingEtaNotions PCUICEtaCanon PCUICEtaI5
     PCUICWellScopedCumulativityEta PCUICContextConversionEta PCUICWsCumulEtaCtx
     PCUICCumulativitySpecEtaClosureInstances PCUICInversionEtaInstances
     PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICSpineEta PCUICValidityEta PCUICSREta
     PCUICAlpha PCUICAlphaEta.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

(** ** The α-variants, without any class *)

Definition al_xna : aname := mkBindAnn (nNamed "x") Relevant.
Definition al_Γk : context := [vass al_xna (tApp (tRel 0) (tRel 1)); vass si_na iv_K; vass si_na iv_PP].
Definition al_eta_g : term := tLambda al_xna si_P (tApp (tRel 3) (tRel 0)).
Definition al_keta : term := tApp (tRel 1) al_eta_g.
Definition al_id : term := tLambda al_xna si_P (tRel 0).
Definition al_PP : term := tProd al_xna si_P si_P.
Definition al_fix_ty : term := tProd al_xna iv_IF iv_IF.
Definition al_mfix : mfixpoint term :=
  [{| dname := al_xna; dtype := al_fix_ty; dbody := tLambda al_xna iv_IF (tRel 0); rarg := 0 |}].

Lemma al_Γk_differs : iv_Γk <> al_Γk.
Proof. discriminate. Qed.

Lemma al_keta_differs : iv_keta <> al_keta.
Proof. discriminate. Qed.

Lemma al_mfix_differs : iv_mfix <> al_mfix.
Proof. discriminate. Qed.

Lemma al_Γk_alpha : iv_Γk ≡Γ al_Γk.
Proof. constructor; [reflexivity|]. constructor; [exact eq_refl|reflexivity]. Qed.

Lemma al_Γk_names : eq_context_upto_names al_Γk iv_Γk.
Proof. constructor; [|reflexivity]. constructor. exact eq_refl. Qed.

Lemma al_keta_alpha : iv_keta ≡' al_keta.
Proof. constructor; [constructor|]. constructor; [exact eq_refl|reflexivity|reflexivity]. Qed.

Lemma al_PP_alpha : iv_PP ≡α al_PP.
Proof. constructor; [exact eq_refl|reflexivity|reflexivity]. Qed.

Lemma al_mfix_alpha : eq_mfixpoint upto_names' iv_mfix al_mfix.
Proof.
  constructor; [|constructor]. cbn.
  split; [constructor; [exact eq_refl|reflexivity|reflexivity]|].
  split; [constructor; [exact eq_refl|reflexivity|reflexivity]|].
  split; reflexivity.
Qed.

(** ** The other lemmas, applied *)

(** IMPOSSIBLE to make non-reflexive: the conclusion is [u = u'] (see the header). *)
Definition cmp_global_instance_empty_eq_inst : ([] : Instance.t) = [] :=
  cmp_global_instance_empty_eq Conv (IndRef si_ind) 0 [] [] ltac:(cbn; constructor).

Definition eq_term_upto_names_upto_domain_r_inst : upto_domain_r iv_keta al_keta :=
  eq_term_upto_names_upto_domain_r Conv 0 iv_keta al_keta al_keta_alpha.

Definition upto_names_canon_eq_inst : canon iv_keta = canon al_keta :=
  upto_names_canon_eq iv_keta al_keta al_keta_alpha.

(** [k (λ_:Prop. g _)] and [k (λx:Prop. g x)] joined in [iv_Γk]. *)
Definition upto_names_JoinE_inst : JoinE si_Σ iv_Γk Cumul iv_keta al_keta :=
  upto_names_JoinE si_Σ iv_Γk Cumul iv_keta al_keta al_keta_alpha.

(** The conversion witness of [iv_mfix] transported to the renamed fixpoint. *)
Lemma upto_names_mfix_on_indE_inst :
  mfix_on_ind check_one_fix (conv_witnessE si_Σ []) (fun mind => check_recursivity_kind (lookup_env si_Σ) mind Finite) al_mfix.
Proof.
  refine (upto_names_mfix_on_indE (Σ := si_Σ) (wfΣ := si_wfE) [] check_one_fix _ iv_mfix al_mfix
            rarg_check_one_fix eq_refl _ al_mfix_alpha iv_wf_fix.2.2).
  constructor; [reflexivity|constructor].
Qed.

Definition eq_context_upto_conv_context_relE_inst : ws_cumul_ctx_pbE_rel Conv si_Σ [] iv_Γk al_Γk :=
  eq_context_upto_conv_context_relE (Σ := si_Σ) (wfΣ := si_wfE) [] iv_Γk al_Γk eq_refl eq_refl al_Γk_alpha.

Definition inst_case_predicate_context_eqE_inst :
  eq_context_upto_names (case_predicate_context si_ind si_mdecl si_idecl iv_mp) (inst_case_predicate_context iv_mp) :=
  inst_case_predicate_context_eqE (Σ := si_Σ) (wfΣ := si_wfE) iv_wf_mp
    (PCUICEtaCanon.eq_context_upto_names_refl' (ind_predicate_context si_ind si_mdecl si_idecl)).

Definition wf_local_eq_context_upto_namesE_inst : wf_localE si_Σ ([] ,,, al_Γk) :=
  wf_local_eq_context_upto_namesE (Σ := si_Σ) (wfΣ := si_wfE) (Γ := []) (Δ := iv_Γk) iv_wf_Γk al_Γk_names.

Definition al_wf_Γk : wf_localE si_Σ al_Γk := wf_local_eq_context_upto_namesE_inst.

(** The η derivation [y : k (λ_:Prop. g _)] moved into the renamed context. *)
Definition eq_context_conversionE_inst : si_Σ ;;; al_Γk |-E tRel 0 : iv_keta :=
  eq_context_conversionE (Σ := si_Σ) (wfΣ := si_wfE) iv_rel_typed al_Γk_alpha al_wf_Γk.

Definition upto_names_conv_contextE_inst : conv_context (@JoinE _) si_Σ iv_Γk al_Γk :=
  upto_names_conv_contextE si_Σ iv_Γk al_Γk al_Γk_alpha.

Definition al_keta_isType : isTypeE si_Σ iv_Γk iv_keta := has_sort_isTypeE _ iv_keta_typed.

Definition isType_eq_context_conversionE_inst : isTypeE si_Σ al_Γk iv_keta :=
  isType_eq_context_conversionE (Σ := si_Σ) (wfΣ := si_wfE) al_keta_isType al_Γk_alpha al_wf_Γk.

(** Inversion of [upto_names] at the concrete terms below: a sort has only itself as α-variant. *)
Ltac al_inv :=
  repeat match goal with
  | H : eq_term_upto_univ_napp _ _ _ _ _ (tSort _) _ |- _ => depelim H
  | H : eq_term_upto_univ_napp _ _ _ _ _ (tRel _) _ |- _ => depelim H
  end; cbn in *; subst.

(** Every α-variant of [Prop → Prop] is a type, and every α-variant of [λ_:Prop. _] has type
    [Prop → Prop]: the premise of [lift_judgment_alphaE], proved by inversion of [upto_names]. *)
Lemma al_PP_variants Γ : wf_localE si_Σ Γ ->
  forall u, upto_names' iv_PP u -> si_Σ ;;; Γ |-E u : tSort iv_sPP.
Proof.
  intros h u e. unfold iv_PP in e. depelim e. unfold si_P in *. al_inv.
  match goal with H : eq_binder_annot _ _ |- _ => rename H into hna end.
  refine (typeE_Prod _ _ na' si_P si_P (Sort.super sProp) (Sort.super sProp) _ _).
  - exact (iv_vass_s si_Σ Γ na' si_P _ (iv_P_typed si_Σ Γ h) hna).
  - exact (iv_P_typed si_Σ _ (iv_wf_vass si_Σ Γ na' si_P _ h (iv_P_typed si_Σ Γ h) hna)).
Qed.

Lemma al_id_variants Γ : wf_localE si_Σ Γ ->
  forall u, upto_names' iv_id u -> si_Σ ;;; Γ |-E u : iv_PP.
Proof.
  intros h u e. unfold iv_id in e. depelim e. unfold si_P in *. al_inv.
  match goal with H : eq_binder_annot _ _ |- _ => rename H into hna end.
  have w := iv_wf_vass si_Σ Γ na' si_P _ h (iv_P_typed si_Σ Γ h) hna.
  eapply typeE_Cumul with (A := tProd na' si_P si_P).
  - apply typeE_Lambda.
    + exact (iv_vass si_Σ Γ na' si_P _ (iv_P_typed si_Σ Γ h) hna).
    + exact (typeE_Rel _ _ 0 (vass na' si_P) w eq_refl).
  - exact (iv_PP_typed si_Σ Γ h).
  - apply eq_term_upto_univ_cumulSpecE. constructor; [exact (eq_sym hna)|reflexivity|reflexivity].
Qed.

Lemma lift_judgment_alphaE_inst : lift_typing typingE si_Σ [] (Judge (Some al_id) al_PP None None).
Proof.
  eapply (lift_judgment_alphaE (tm := Some iv_id) (t := iv_PP)).
  - split; [exact (al_id_variants [] localenv_nil)|].
    exists iv_sPP. split; [exact (al_PP_variants [] localenv_nil)|]. split; exact I.
  - cbn. constructor; [exact eq_refl|reflexivity|reflexivity].
  - exact al_PP_alpha.
Qed.

Definition type_Cumul'E_inst : si_Σ ;;; iv_Γk |-E tRel 0 : iv_keta :=
  PCUICAlphaEta.type_Cumul'E iv_kg iv_y_typed al_keta_isType iv_spec_eta.

Lemma al_PP_isWfArity : isWfArityE si_Σ [] iv_PP.
Proof.
  split; [exact (has_sort_isTypeE _ (iv_PP_typed si_Σ [] localenv_nil))|].
  exists [vass si_na si_P], sProp. reflexivity.
Qed.

(** ** The main theorem's family (it took T1's forecast class until copy 18b landed) *)

Section AlphaClassInstances.

  (** The η derivation, through the main theorem's typing component, into the renamed context. *)
  Definition typing_alpha_propE_inst : si_Σ ;;; al_Γk |-E tRel 0 : iv_keta :=
    (typing_alpha_propE si_Σ si_wfE iv_Γk (tRel 0) iv_keta iv_rel_typed).2.2 al_Γk (tRel 0)
      ltac:(reflexivity) al_Γk_alpha.

  Definition typing_alphaE_inst : si_Σ ;;; iv_Γk |-E al_keta : si_P :=
    typing_alphaE (Σ := si_Σ) (wfΣ := si_wfE) iv_keta_typed al_keta_alpha.

  Definition wf_local_alphaE_inst : wf_localE si_Σ al_Γk :=
    PCUICAlphaEta.wf_local_alphaE (Σ := si_Σ) (wfΣ := si_wfE) iv_wf_Γk al_Γk_alpha.

  Definition isType_alphaE_inst : isTypeE si_Σ iv_Γk al_keta :=
    isType_alphaE (Σ := si_Σ) (wfΣ := si_wfE) iv_Γk iv_keta al_keta al_keta_isType al_keta_alpha.

  Definition isType_alpha_ctxE_inst : isTypeE si_Σ al_Γk al_keta :=
    isType_alpha_ctxE (Σ := si_Σ) (wfΣ := si_wfE) al_keta_isType al_Γk_alpha al_keta_alpha.

  Definition isWfArity_alphaE_inst : isWfArityE si_Σ [] al_PP :=
    isWfArity_alphaE (Σ := si_Σ) (wfΣ := si_wfE) al_PP_isWfArity al_PP_alpha.

End AlphaClassInstances.
