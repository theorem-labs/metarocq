(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the lemmas of [PCUICClassificationEta] (row T6)

  **No forecast class.** The lemmas of [PCUICClassificationEta] took T1's [SRForecastCopy18]
  (copy 18b) as a premise until copy 18b landed (frac/eta 3e6b422d); the class is deleted, so the
  instances below, in section [ClassificationEtaInstances] (which held it), apply the lemmas with
  no class. Every derivation each instance needs is built here or taken from the landed instance
  files.

  **The environments** are [si_Σ] ([PCUICCumulativitySpecEtaClosureInstances]:
  [Inductive I (A : Prop) : Prop := c : I A]) and [iv_Σ] ([PCUICInversionEtaInstances]: the
  [CoFinite] record [R]).

  **Non-degeneracy.**
  - The arity corollaries (Class A' rows) and [isArity_typing_spineE] run on the type
    [cli_T := Π _ : Prop. z] in the context [z := Prop : Type] ([cli_Γz]): [cli_T] is not an
    arity (its codomain is the variable [z]) and reaches the arity [Prop → Prop] only by
    unfolding [z]. i20 ([invert_cumul_arity_rE_inst]) runs T8 [Prod_r] on [cli_T] and T8
    [Sort_r] on the codomain [z]; i21 ([invert_cumul_arity_lE_inst]) runs
    [PCUICPrincipalityEta.T8_Prod_l_plug] and this file's [T8_Sort_l_plug] (the [_l] forms
    derived from the proved [_r] ones) the same way; x2, x3 and [isArity_typing_spineE] run
    i21/i20 on it.
  - The (co)fixpoint witness lemmas run on declared types on which the check FAILS:
    [bdf_fxty 0] (domain the β-redex [(λ B. I B) A], [bdf_check_fix_dtypeβ]) and [bdf_RFβ]
    (the β-redex [(λ B. R B) (∀P. P)], [bdf_check_cofix_dtypeβ]); the typed-reduct route
    finds the reduct on which it passes. [wf_fixpoint_spineE_inst] applies the fixpoint to the
    argument [c A], typed at the β-redex domain, and reads back its type at the inductive.
  - [typing_cofix_coindE_inst]: a cofixpoint whose declared type is the β-redex [bdf_RFβ],
    typed at [R (∀P. P)] by conversion.
  - The spine lemmas run on [∀P:Prop. P] applied to [∀P:Prop. P], and the smash lemmas on the
    let-in [let z := ∀P. P in z].
  - [arity_spine_len_subst_inst] substitutes [∀P. P] for the free variable of the arity
    [let z := x : Prop in Π _ : x. Prop] ([cli_open_arity]), which changes the let body and the
    product domain ([cli_open_arity_subst_differs]).
  - Evaluation: [cli_eval] is the β-step [(λx:Prop. x) (∀P. P) ⇓ ∀P. P];
    [eval_classificationE_inst] evaluates [c (∀P. P)] by [eval_construct].

  **Rows without an instance, with the reason.**
  - IMPOSSIBLE (the conclusion is [False]: the lemma states that its premises cannot hold
    together; as in base): [Is_conv_to_Arity_indE], [typing_spine_arity_mkApps_IndE],
    [typing_spine_more_invE], [typing_varE], [typing_evarE], [invert_ind_indE],
    [invert_fix_indE], [wh_neutral_empty_genE], [wh_neutral_emptyE].
  - Refutations ([invert_cumul_arity_lE_untyped_false], [invert_cumul_arity_rE_untyped_false]):
    theorems, not hypotheses; no instance applies.
  - Helpers run by the instances above: [T8_Sort_l_plug], [PCUICPrincipalityEta.T8_Prod_l_plug]
    and [PCUICPrincipalityEta.chain_ws_cumul_pbE_Conv] (inside i21's instance; their own
    instances are in [PCUICPrincipalityEtaInstances]), [arity_spine_len] and
    [arity_spine_len_subst] (inside i20's and i21's; [arity_spine_len_subst_inst] too).

  **A row whose instance is degenerate by the statement.** [check_recursivity_kind_injE]:
  IMPOSSIBLE to make non-reflexive. The conclusion is the equality [rk = rk'], and in every
  environment [Σ] (the section premise [wfE Σ] included) both premises check the field
  [ind_finite] of the same declaration [mind] of [lookup_env Σ], so [rk] and [rk'] are both that
  field. The instance is at [Finite], the [ind_finite] of [I] in [si_Σ]. *)

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
     PCUICSREtaInstances BDTypingEtaInstances BDFromPCUICEtaInstances PCUICClassification PCUICClassificationEta.
From MetaRocq.PCUIC Require PCUICWfUniverses.
From Equations.Type Require Import Relation.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.
#[local] Existing Instance si_wfE.
#[local] Existing Instance iv_wfE.
#[local] Instance cli_iv_cb : ClosedBodies iv_env := @wfE_ClosedBodies _ iv_env iv_wfE.

(** ** Derivations, without any class *)

(** The context [z := Prop : Type]. *)
Definition cli_Γz : context := [vdef si_na si_P (tSort (Sort.super sProp))].

Lemma cli_Type_typed (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ |-E tSort (Sort.super sProp) : tSort (Sort.super (Sort.super sProp)).
Proof. intros h. apply typeE_Sort; [exact h|apply PCUICWfUniverses.wf_sort_super; cbn; trivial]. Qed.

Lemma cli_wf_Γz : wf_localE si_Σ cli_Γz.
Proof.
  apply localenv_cons_def; [constructor|].
  exact (iv_vdef si_Σ [] si_na si_P (tSort (Sort.super sProp)) _ (iv_P_typed si_Σ [] localenv_nil)
           (cli_Type_typed [] localenv_nil) eq_refl).
Qed.

(** [Π _ : Prop. z]: not an arity; it reduces to the arity [Prop → Prop] by unfolding [z]. *)
Definition cli_T : term := tProd si_na si_P (tRel 1).

Lemma cli_T_typed :
  si_Σ ;;; cli_Γz |-E cli_T : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)).
Proof.
  apply typeE_Prod.
  - exact (iv_vass_s si_Σ cli_Γz si_na si_P _ (iv_P_typed si_Σ cli_Γz cli_wf_Γz) eq_refl).
  - exact (typeE_Rel _ _ 1 (vdef si_na si_P (tSort (Sort.super sProp))) (iv_wf_P si_Σ cli_Γz cli_wf_Γz) eq_refl).
Qed.

Lemma cli_T_isType : isTypeE si_Σ cli_Γz cli_T.
Proof. exact (has_sort_isTypeE _ cli_T_typed). Qed.

Lemma cli_PP_isType : isTypeE si_Σ cli_Γz iv_PP.
Proof. exact (has_sort_isTypeE _ (iv_PP_typed si_Σ cli_Γz cli_wf_Γz)). Qed.

Lemma cli_T_not_arity : isArity cli_T = false.
Proof. reflexivity. Qed.

Lemma cli_T_red : red1 si_Σ cli_Γz cli_T iv_PP.
Proof. apply prod_red_r. exact (red_rel si_Σ (cli_Γz ,, vass si_na si_P) 1 si_P eq_refl). Qed.

Lemma cli_T_closed_red : si_Σ ;;; cli_Γz ⊢ cli_T ⇝ iv_PP.
Proof. exact (closed_red_of (Σ := si_Σ) (Γ := cli_Γz) (t := cli_T) eq_refl eq_refl (red1_red _ _ _ _ cli_T_red)). Qed.

Lemma cli_ws_r : ws_cumul_pbE Cumul si_Σ cli_Γz cli_T iv_PP.
Proof. exact (red_ws_cumul_pbE (Σ := si_Σ) cli_T_closed_red). Qed.

Lemma cli_ws_l : ws_cumul_pbE Cumul si_Σ cli_Γz iv_PP cli_T.
Proof. exact (red_ws_cumul_pbE_inv (Σ := si_Σ) cli_T_closed_red). Qed.

Lemma cli_PP_conv : Is_conv_to_Arity si_Σ cli_Γz iv_PP.
Proof.
  exists iv_PP. split; [|reflexivity]. sq.
  exact (closed_red_refl (Σ := si_Σ) cli_Γz iv_PP eq_refl eq_refl).
Qed.

(** The spine of [∀P:Prop. P] applied to [∀P:Prop. P]. *)
Lemma cli_False_isType (Γ : context) : wf_localE si_Σ Γ -> isTypeE si_Σ Γ iv_False.
Proof. intros h. exact (has_sort_isTypeE _ (iv_False_typed si_Σ Γ h)). Qed.

Lemma cli_False_refl (Γ : context) : wf_localE si_Σ Γ -> ws_cumul_pbE Cumul si_Σ Γ iv_False iv_False.
Proof. intros h. exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) Γ iv_False (cli_False_isType Γ h)). Qed.

Lemma cli_sp_nil : PCUICAritiesEta.typing_spineE si_Σ [] iv_False [] iv_False.
Proof.
  econstructor; [exact (cli_False_isType [] localenv_nil)|exact (cli_False_isType [] localenv_nil)|].
  exact (cli_False_refl [] localenv_nil).
Qed.

Lemma cli_sp_one : PCUICAritiesEta.typing_spineE si_Σ [] iv_False [iv_False] iv_False.
Proof.
  eapply (@PCUICAritiesEta.type_spine_consE _ _ _ iv_False iv_False [] si_na si_P (tRel 0) iv_False).
  - exact (cli_False_isType [] localenv_nil).
  - exact (cli_False_isType [] localenv_nil).
  - exact (cli_False_refl [] localenv_nil).
  - exact (iv_False_typed si_Σ [] localenv_nil).
  - exact cli_sp_nil.
Qed.

Lemma cli_wf_ΓΔ : wf_localE si_Σ ([] ,,, [vass si_na si_P]).
Proof. exact (iv_wf_P si_Σ [] localenv_nil). Qed.

(** The spine of the let-in [let z := ∀P:Prop. P in z] (no argument), at [∀P:Prop. P]. *)
Lemma cli_let_ws : ws_cumul_pbE Cumul si_Σ [] bdf_let iv_False.
Proof.
  apply (red_ws_cumul_pbE (Σ := si_Σ)).
  exact (closed_red_of (Σ := si_Σ) (Γ := []) (t := bdf_let) eq_refl eq_refl
           (red1_red _ _ _ _ (red_zeta _ _ si_na iv_False si_P (tRel 0)))).
Qed.

Lemma cli_sp_let : PCUICAritiesEta.typing_spineE si_Σ [] (it_mkProd_or_LetIn [vdef si_na iv_False si_P] (tRel 0)) [] iv_False.
Proof.
  econstructor; [exact (has_sort_isTypeE _ bdf_let_sort_typed)|exact (cli_False_isType [] localenv_nil)|].
  exact cli_let_ws.
Qed.

(** The fixpoint [bdf_fmfix] applied to [c A], typed at its β-redex domain [(λ B. I B) A]. *)
Definition cli_cA : term := tApp (tConstruct si_ind 0 []) (tRel 0).

Lemma cli_cA_typed_I : si_Σ ;;; bd_Γ1 |-E cli_cA : tApp (tInd si_ind []) (tRel 0).
Proof.
  exact (typeE_App _ _ (tConstruct si_ind 0 []) si_na si_P (tApp (tInd si_ind []) (tRel 0)) _ (tRel 0)
           (iv_cstr_prod_typed bd_Γ1 bd_wfE_Γ1) (iv_cstr_typed bd_Γ1 bd_wfE_Γ1)
           (typeE_Rel _ _ 0 (vass si_na si_P) bd_wfE_Γ1 eq_refl)).
Qed.

Lemma cli_cA_typed : si_Σ ;;; bd_Γ1 |-E cli_cA : bdf_Dk 0.
Proof.
  eapply (typeE_Cumul _ _ cli_cA (tApp (tInd si_ind []) (tRel 0)) _ sProp).
  - exact cli_cA_typed_I.
  - exact (bdf_dom_typed bd_Γ1 0 bd_wfE_Γ1 eq_refl).
  - apply (ws_cumul_pbE_forget_spec (pb := Cumul)).
    apply (red_ws_cumul_pbE_inv (Σ := si_Σ)).
    exact (closed_red_of (Σ := si_Σ) (Γ := bd_Γ1) (t := bdf_Dk 0) eq_refl eq_refl
             (red1_red _ _ _ _ (red_beta _ _ si_na si_P (tApp (tInd si_ind []) (tRel 0)) (tRel 0)))).
Qed.

Lemma cli_fxty_isType : isTypeE si_Σ bd_Γ1 (bdf_fxty 0).
Proof. exact (has_sort_isTypeE _ (bdf_fxty_typed bd_Γ1 0 bd_wfE_Γ1 eq_refl)). Qed.

Lemma cli_IA_isType : isTypeE si_Σ bd_Γ1 (tApp (tInd si_ind []) (tRel 0)).
Proof.
  exact (has_sort_isTypeE _ (iv_IX_typed bd_Γ1 (tRel 0) bd_wfE_Γ1
                               (typeE_Rel _ _ 0 (vass si_na si_P) bd_wfE_Γ1 eq_refl))).
Qed.

Lemma cli_fix_sp_nil : PCUICAritiesEta.typing_spineE si_Σ bd_Γ1 (bdf_fxty 0) [] (bdf_fxty 0).
Proof.
  econstructor; [exact cli_fxty_isType|exact cli_fxty_isType|].
  exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) bd_Γ1 (bdf_fxty 0) cli_fxty_isType).
Qed.

Lemma cli_fix_sp_cA :
  PCUICAritiesEta.typing_spineE si_Σ bd_Γ1 (bdf_fxty 0) [cli_cA] (tApp (tInd si_ind []) (tRel 0)).
Proof.
  eapply (@PCUICAritiesEta.type_spine_consE _ _ _ (bdf_fxty 0) cli_cA [] si_na (bdf_Dk 0)
            (tApp (tInd si_ind []) (tRel 1)) (tApp (tInd si_ind []) (tRel 0))).
  - exact cli_fxty_isType.
  - exact cli_fxty_isType.
  - exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) bd_Γ1 (bdf_fxty 0) cli_fxty_isType).
  - exact cli_cA_typed.
  - econstructor; [exact cli_IA_isType|exact cli_IA_isType|].
    exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) bd_Γ1 _ cli_IA_isType).
Qed.

(** The cofixpoint [bdf_cmfix] of [iv_Σ]; its declared type is the β-redex [bdf_RFβ]. *)
Lemma cli_RFβ_isType : isTypeE iv_Σ iv_Γc bdf_RFβ.
Proof. exact (has_sort_isTypeE _ (bdf_RFβ_typed iv_Γc iv_wf_Γc)). Qed.

Lemma cli_cofix_sp_nil : PCUICAritiesEta.typing_spineE iv_Σ iv_Γc bdf_RFβ [] bdf_RFβ.
Proof.
  econstructor; [exact cli_RFβ_isType|exact cli_RFβ_isType|].
  exact (isType_ws_cumul_pbE_refl (Σ := iv_Σ) iv_Γc bdf_RFβ cli_RFβ_isType).
Qed.

Lemma cli_cofix_typed_R : iv_Σ ;;; iv_Γc |-E mkApps (tCoFix bdf_cmfix 0) [] : mkApps (tInd iv_ind []) [iv_False].
Proof.
  eapply (typeE_Cumul _ _ _ bdf_RFβ _ sProp).
  - exact bdf_cofix_typed.
  - exact (iv_RF_typed iv_Γc iv_wf_Γc).
  - apply (ws_cumul_pbE_forget_spec (pb := Cumul)).
    apply (red_ws_cumul_pbE (Σ := iv_Σ)).
    exact (closed_red_of (Σ := iv_Σ) (Γ := iv_Γc) (t := bdf_RFβ) eq_refl eq_refl (bdf_RFβ_red iv_Γc)).
Qed.

(** Evaluation: [(λx:Prop. x) (∀P:Prop. P) ⇓ ∀P:Prop. P]. *)
Lemma cli_eval : eval si_Σ (tApp iv_id iv_False) iv_False.
Proof.
  eapply eval_beta; [apply eval_atom; reflexivity|apply eval_atom; reflexivity|].
  apply eval_atom; reflexivity.
Qed.

(** [c (∀P:Prop. P)] is a value, and evaluates to itself. *)
Lemma cli_cF_value : value si_Σ sri_cF.
Proof.
  change sri_cF with (mkApps (tConstruct si_ind 0 []) [iv_False]).
  eapply value_app_nonnil; [|discriminate|constructor; [|constructor]].
  - eapply value_head_cstr with (mdecl := si_mdecl) (idecl := si_idecl) (cdecl := si_cdecl); [|cbn; lia].
    exact (declared_constructor_to_gen (wfΣ := si_wf) si_declared_constructor).
  - apply value_atomic, atomic_atom. reflexivity.
Qed.

Lemma cli_cF_eval : eval si_Σ sri_cF sri_cF.
Proof.
  change sri_cF with (tApp (tConstruct si_ind 0 []) iv_False) at 1.
  change sri_cF with (mkApps (tConstruct si_ind 0 []) ([] ++ [iv_False])).
  eapply eval_construct with (mdecl := si_mdecl) (idecl := si_idecl) (cdecl := si_cdecl);
    [| |cbn; lia|apply eval_atom; reflexivity].
  - exact (declared_constructor_to_gen (wfΣ := si_wf) si_declared_constructor).
  - apply eval_atom; reflexivity.
Qed.

Lemma cli_axiom_free : axiom_free si_Σ.
Proof.
  intros c decl h. exfalso. red in h. cbn in h.
  destruct h as [h|h]; [discriminate h|exact h].
Qed.

Lemma cli_notCoInductive : notCoInductive si_Σ si_ind.
Proof. intros h. vm_compute in h. discriminate h. Qed.

Section ClassificationEtaInstances.

(** ** The arity corollaries, Class A' *)

Definition invert_cumul_arity_rE_inst : Is_conv_to_Arity si_Σ cli_Γz cli_T :=
  invert_cumul_arity_rE (Σ := si_Σ) (wfΣ := si_wfE) cli_Γz cli_T iv_PP eq_refl cli_ws_r cli_T_isType.

Definition invert_cumul_arity_lE_inst : Is_conv_to_Arity si_Σ cli_Γz cli_T :=
  invert_cumul_arity_lE (Σ := si_Σ) (wfΣ := si_wfE) cli_Γz iv_PP cli_T eq_refl cli_ws_l cli_T_isType.

Definition invert_cumul_arity_l_genE_inst : Is_conv_to_Arity si_Σ cli_Γz cli_T :=
  invert_cumul_arity_l_genE (Σ := si_Σ) (wfΣ := si_wfE) cli_Γz iv_PP cli_T cli_PP_conv cli_ws_l cli_T_isType.

Definition invert_cumul_arity_r_genE_inst : Is_conv_to_Arity si_Σ cli_Γz cli_T :=
  invert_cumul_arity_r_genE (Σ := si_Σ) (wfΣ := si_wfE) cli_Γz iv_PP cli_T cli_PP_conv cli_ws_r cli_T_isType.

Definition isArity_typing_spineE_inst : Is_conv_to_Arity si_Σ cli_Γz cli_T :=
  isArity_typing_spineE (Σ := si_Σ) (wfΣ := si_wfE) cli_wf_Γz
    (PCUICAritiesEta.type_spine_nilE _ _ iv_PP cli_T cli_PP_isType cli_T_isType cli_ws_l) cli_PP_conv.

(** [let z := x : Prop in Π _ : x. Prop], with [x] free (de Bruijn index 0 outside the let):
    an arity whose let body and product domain mention [x]. The substitution [x := ∀P. P]
    changes the term ([cli_open_arity_subst_differs]); the lemma's induction runs its [tLetIn]
    and [tProd] cases, at the lifted indices 0 and 1. *)
Definition cli_open_arity : term := tLetIn si_na (tRel 0) si_P (tProd si_na (tRel 1) (tSort sProp)).

Lemma cli_open_arity_subst_differs : subst [iv_False] 0 cli_open_arity <> cli_open_arity.
Proof. discriminate. Qed.

Definition arity_spine_len_subst_inst :
  arity_spine_len (subst [iv_False] 0 cli_open_arity) = arity_spine_len cli_open_arity :=
  arity_spine_len_subst [iv_False] 0 cli_open_arity eq_refl.

(** ** The (co)fixpoint witness, at declared types on which the check fails *)

Definition mfix_on_ind_spine_witnessE_fix_inst :=
  mfix_on_ind_spine_witnessE_fix (Σ := si_Σ) si_wfE (ok := fun mind => check_recursivity_kind (lookup_env si_Σ) mind Finite)
    bd_Γ1 bdf_fmfix 0 bdf_fix_dβ [] (bdf_fxty 0) bdf_wf_fix.2.2 eq_refl cli_fxty_isType cli_fix_sp_nil.

Definition mfix_on_ind_spine_witnessE_cofix_inst :=
  mfix_on_ind_spine_witnessE_cofix (Σ := iv_Σ) iv_wfE
    (ok := fun mind => check_recursivity_kind (lookup_env iv_Σ) mind CoFinite)
    iv_Γc bdf_cmfix 0 bdf_cofix_dβ [] bdf_RFβ bdf_wf_cofix eq_refl cli_RFβ_isType cli_cofix_sp_nil.

Definition wf_fixpoint_spineE_inst :=
  wf_fixpoint_spineE (Σ := si_Σ) si_wfE bd_Γ1 bdf_fmfix 0 bdf_fix_dβ [cli_cA] _
    bdf_wf_fix eq_refl cli_fxty_isType cli_fix_sp_cA.

Definition wf_cofixpoint_spineE_inst :=
  wf_cofixpoint_spineE (Σ := iv_Σ) iv_wfE iv_Γc bdf_cmfix 0 bdf_cofix_dβ [] bdf_RFβ
    bdf_wf_cofix eq_refl cli_RFβ_isType cli_cofix_sp_nil.

Definition typing_cofix_coindE_inst :
  check_recursivity_kind (lookup_env iv_Σ) (inductive_mind iv_ind) CoFinite :=
  typing_cofix_coindE (Σ := iv_Σ) (wfΣ := iv_wfE) cli_cofix_typed_R.

(** ** Spines and smashing *)

Definition cumul_it_mkProd_or_LetIn_smashE_inst :=
  cumul_it_mkProd_or_LetIn_smashE (Σ := si_Σ) si_wfE [] [vdef si_na iv_False si_P] (tRel 0) eq_refl eq_refl.

Definition typing_spine_smashE_inst :=
  typing_spine_smashE (Σ := si_Σ) si_wfE [] [vdef si_na iv_False si_P] (tRel 0) [] iv_False cli_sp_let.

Definition typing_spine_nth_errorE_inst :=
  PCUICClassificationEta.typing_spine_nth_errorE (Σ := si_Σ) si_wfE [] [vass si_na si_P] (tRel 0)
    [iv_False] iv_False 0 iv_False (vass si_na si_P) (assumption_context_vass _ _ _ assumption_context_nil)
    cli_wf_ΓΔ cli_sp_one eq_refl eq_refl.

Definition typing_spine_all_invE_inst :=
  typing_spine_all_invE (Σ := si_Σ) si_wfE [] [vass si_na si_P] (tRel 0) [iv_False] iv_False cli_sp_one eq_refl.

Definition typing_spine_nth_error_NoneE_inst :=
  typing_spine_nth_error_NoneE (Σ := si_Σ) si_wfE [] [vass si_na si_P] (tRel 0) [] iv_False
    (assumption_context_vass _ _ _ assumption_context_nil) cli_wf_ΓΔ cli_sp_nil eq_refl.

Definition typing_spine_nth_error_None_prodE_inst :=
  typing_spine_nth_error_None_prodE (Σ := si_Σ) si_wfE [] [vass si_na si_P] (tRel 0) [] iv_False 0
    (vass si_na si_P) (assumption_context_vass _ _ _ assumption_context_nil) cli_wf_ΓΔ cli_sp_nil
    eq_refl eq_refl.

(** ** Classification and evaluation *)

(** IMPOSSIBLE to make non-reflexive, by the statement: the conclusion is [rk = rk'] (see the
    header). *)
Definition check_recursivity_kind_injE_inst : Finite = Finite :=
  check_recursivity_kind_injE (Σ := si_Σ) (wfΣ := si_wfE) (mind := si_kn) (rk := Finite) (rk' := Finite)
    eq_refl eq_refl.

Definition wt_closed_red_reflE_inst := wt_closed_red_reflE (Σ := si_Σ) (wfΣ := si_wfE) bdf_x_ind_typed.

Definition value_whnfE_inst := value_whnfE (Σ := si_Σ) (wfΣ := si_wfE) sri_cF eq_refl cli_cF_value.

Definition eval_whneE_inst :=
  eval_whneE (Σ := si_Σ) (wfΣ := si_wfE) (tApp iv_id iv_False) iv_False eq_refl cli_eval.

Definition eval_closed_cb_inst : closed iv_False :=
  eval_closed_cb si_Σ (tApp iv_id iv_False) iv_False eq_refl cli_eval.

Definition whnf_classification'E_inst :=
  whnf_classification'E (Σ := si_Σ) (wfΣ := si_wfE) sri_cF si_ind [] [iv_False] eq_refl
    (whnf_cstrapp _ _ _ _ _ _ [iv_False]) sri_cF_typed.

Definition whnf_classificationE_inst :=
  whnf_classificationE (Σ := si_Σ) (wfΣ := si_wfE) sri_cF si_ind [] [iv_False] cli_axiom_free
    (whnf_cstrapp _ _ _ _ _ _ [iv_False]) sri_cF_typed.

Definition ind_whnf_classification'E_inst :=
  ind_whnf_classification'E (Σ := si_Σ) (wfΣ := si_wfE) sri_cF si_ind [] [iv_False] eq_refl
    cli_notCoInductive sri_cF_typed (whnf_cstrapp _ _ _ _ _ _ [iv_False]).

Definition ind_whnf_classificationE_inst :=
  ind_whnf_classificationE (Σ := si_Σ) (wfΣ := si_wfE) sri_cF si_ind [] [iv_False] cli_axiom_free
    cli_notCoInductive sri_cF_typed (whnf_cstrapp _ _ _ _ _ _ [iv_False]).

Definition fix_app_is_constructorE_inst :=
  fix_app_is_constructorE (Σ := si_Σ) (wfΣ := si_wfE) sri_fix_app_typed eq_refl.

Definition wcbveval_redE_inst : red si_Σ [] (tApp iv_id iv_False) iv_False :=
  wcbveval_redE (Σ := si_Σ) (wfΣ := si_wfE) _ _ _ (iv_app_typed si_Σ [] localenv_nil) cli_eval.

Definition subject_reduction_evalE_inst : si_Σ ;;; [] |-E iv_False : si_P :=
  subject_reduction_evalE (Σ := si_Σ) (wfΣ := si_wfE) (iv_app_typed si_Σ [] localenv_nil) cli_eval.

Definition value_classificationE_inst :=
  value_classificationE (Σ := si_Σ) (wfΣ := si_wfE) (i := si_ind) (u := []) (args := [iv_False])
    sri_cF_typed cli_cF_value.

Definition eval_classificationE_inst :=
  eval_classificationE (Σ := si_Σ) (wfΣ := si_wfE) (i := si_ind) (u := []) (args := [iv_False])
    sri_cF_typed sri_cF cli_cF_eval.

End ClassificationEtaInstances.
