(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the hypotheses of [PCUICCasesHelperEta]

  Every lemma of [PCUICCasesHelperEta] is applied here to a concrete instance with every
  premise proved. Three environments are used, each already built by an earlier copy:

  - [si_Σ] ([PCUICCumulativitySpecEtaClosureInstances]): [Inductive I (A : Prop) : Prop := c : I A],
    one parameter, no index, one constructor with no argument. In the context
    [iv_Γk := [y : k g; k : (Prop → Prop) → Prop; g : Prop → Prop]]
    ([PCUICInversionEtaInstances]) the discriminee [c (k g) : I (k g)] of copy 18b's [match] is
    accepted at the predicate's parameter [k (λx:Prop. g x)] ONLY through one η step
    ([c18b_disc_typed]). The whole [type_Case_*] family is instantiated there, so each of its
    instances carries that η step in its typing premise.
  - [c18b_sΓ := iv_Γk ,, (z := y : k (λx:Prop. g x))] in [si_Σ] (copy 18b): a context whose
    well-formedness holds the η step, used where the only typing premise is a [wf_localE] or a
    [spine_substE] over a sort-typed parameter.
  - [c17_Σ] (copy 17): [si_env] plus an axiom whose type is typed only through the η step, so
    [wfE c17_Σ.1] itself holds one. It is used for the lemmas whose only non-syntactic premise
    is the environment.
  - [iv_Σ] ([PCUICInversionEtaInstances]) with copy 18a's telescope [c18_tel], whose last entry
    is typed only through the η step, for the weakening lemmas.

  No instance is WEAK: every one of the fifteen carries a real η step in a premise. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICEquality PCUICCases PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICReduction
     PCUICUnivSubst PCUICUnivSubstitutionConv PCUICContextSubst PCUICSigmaCalculus PCUICClosedBodies
     PCUICWellScopedCumulativity PCUICConversion PCUICWeakeningEnv PCUICCasesHelper
     PCUICTypingEta PCUICTypingEtaInd PCUICClosedTypEta PCUICWeakeningEnvTypEta PCUICWeakeningTypEta
     PCUICTypingEtaNotions PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta
     PCUICWellScopedCumulativityEta PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp
     PCUICEtaI5 PCUICEtaJoinSpec PCUICValidityEta
     PCUICCumulativitySpecEtaClosureInstances PCUICInversionEtaInstances
     PCUICSpineEta PCUICInductivesEta PCUICInductiveInversionEta PCUICInductiveInversionEtaB
     PCUICTypingEtaCopy18aInstances PCUICTypingEtaCopy18bInstances PCUICTypingEtaCopy17Instances.
From MetaRocq.PCUIC Require Import PCUICCasesHelperEta.
From Equations.Prop Require Import DepElim.

#[local] Existing Instance default_checker_flags.

#[local] Existing Instance si_cb.

Definition c21_rf_cb : ClosedBodies rf_Σ := @wfE_ClosedBodies _ rf_Σ wc_wfE.
Definition c21_iv_cb : ClosedBodies iv_env := @wfE_ClosedBodies _ iv_env iv_wfE.
Definition c21_c17_cb : ClosedBodies c17_env := @wfE_ClosedBodies _ c17_env c17_wfE.
#[local] Existing Instance c21_rf_cb.
#[local] Existing Instance c21_iv_cb.
#[local] Existing Instance c21_c17_cb.

(** ** The environment extensions used as [wf_extE] *)

Lemma c21_si_wf_extE : wf_extE si_Σ.
Proof. split; [exact si_wfE|exact si_on_udecl]. Qed.

Lemma c21_c17_wf_extE : wf_extE c17_Σ.
Proof. split; [exact c17_wfE|exact si_on_udecl]. Qed.

Lemma c21_c17_declared_constructor :
  declared_constructor c17_Σ (si_ind, 0) si_mdecl si_idecl si_cdecl.
Proof. split; [exact c17_declared_inductive|reflexivity]. Qed.

(** ** [weakening0E]: the context is copy 18a's η telescope *)

Definition weakening0E_inst :=
  @weakening0E _ iv_Σ c18b_Γ iv_False si_P iv_wfE c18b_wf
    (iv_False_typed iv_Σ [] localenv_nil).

(** ** [weakening_type_local_ctxE]: the same η context *)

Lemma c21_tlc : type_local_ctx (lift_typing typingE) iv_Σ c18b_Γ [] sProp.
Proof. exact I. Qed.

Definition weakening_type_local_ctxE_inst :=
  weakening_type_local_ctxE iv_Σ c18b_Γ [] [] sProp iv_wfE c18b_wf c21_tlc.

(** ** [wf_local_expand_lets0E]: the η telescope, split at its end *)

Definition wf_local_expand_lets0E_inst :=
  wf_local_expand_lets0E (Σ := iv_Σ) iv_wfE c18b_Γ [] c18b_wf.

(** ** [AritiesToGeneration_typing_spineE]: the empty spine, whose comparison IS the η step

  [k g] and [k (λx:Prop. g x)] are related by one η step and by no reduction or syntactic
  comparison, so the specification spine this returns is built on that step. *)

Lemma c21_isT_kg : isTypeE si_Σ iv_Γk iv_kg.
Proof. exact (has_sort_isTypeE _ c18b_kg_typed). Qed.

Lemma c21_isT_keta : isTypeE si_Σ iv_Γk iv_keta.
Proof. exact (has_sort_isTypeE _ iv_keta_typed). Qed.

Definition c21_spine_eta : PCUICAritiesEta.typing_spineE si_Σ iv_Γk iv_kg [] iv_keta :=
  type_spine_nilE _ _ iv_kg iv_keta c21_isT_kg c21_isT_keta (c18b_ws_eta si_Σ Cumul).

Definition AritiesToGeneration_typing_spineE_inst :=
  AritiesToGeneration_typing_spineE si_Σ iv_Γk iv_kg [] iv_keta c21_spine_eta.

(** ** [isType_liftE]: the η telescope again, at [n = 0] *)

Definition isType_liftE_inst :=
  PCUICCasesHelperEta.isType_liftE (Σ := iv_Σ) (n := 0) (Γ := c18b_Γ) (Δ := []) (ty := iv_False)
    (Nat.le_0_l _) iv_wfE c18b_wf c18b_isT_False.

(** ** [pre_case_predicate_context_gen_indpred_ctxE]

  The parameter context of [I] is [A : Prop], so no η step can appear in the subslet itself
  (a type η-related to [tSort sProp] IS [tSort sProp]: no η rule produces a sort). The step is
  in the spine substitution's domain context [c18b_sΓ], whose [wf_localE] field types [z := y]
  at [k (λx:Prop. g x)] through the η step. *)

Definition c21_par : term := lift0 1 iv_keta.

Lemma c21_par_typed : si_Σ ;;; c18b_sΓ |-E c21_par : si_P.
Proof.
  exact (weakeningE si_Σ iv_Γk [vdef si_na (tRel 0) iv_keta] iv_keta si_P si_wfE c18b_swf
           iv_keta_typed).
Qed.

Lemma c21_wf_sP : wf_localE si_Σ (c18b_sΓ ,, vass si_na si_P).
Proof. exact (iv_wf_P si_Σ c18b_sΓ c18b_swf). Qed.

Definition c21_sp : spine_substE si_Σ c18b_sΓ [c21_par] [c21_par] [vass si_na si_P].
Proof.
  constructor.
  - exact c18b_swf.
  - exact c21_wf_sP.
  - exact (context_subst_ass [] [] [] si_na si_P c21_par context_subst_nil).
  - exact (subslet_ass_tipE c21_par_typed).
Defined.

Lemma c21_cu : consistent_instance_ext si_Σ (ind_universes si_mdecl) [].
Proof. reflexivity. Qed.

Definition pre_case_predicate_context_gen_indpred_ctxE_inst :=
  pre_case_predicate_context_gen_indpred_ctxE si_ind si_mdecl si_idecl [c21_par] []
    si_Σ c18b_sΓ c21_sp c21_cu.

(** ** The three branch-type lemmas, in [c17_Σ]

  Their only non-syntactic premise is the environment, so the η step is the one [wfE c17_env]
  itself holds: the constant of [c17_env] has the closed type [c17_P'], which is typed only
  through the η step of copy 15's kit. *)

Definition c21_predctx : context := [vass si_na si_P].

Lemma c21_beta_len : #|cstr_indices si_cdecl| + 1 = context_assumptions c21_predctx.
Proof. reflexivity. Qed.

Definition case_branch_type_betaE_inst :=
  case_branch_type_betaE c17_Σ [] si_ind si_mdecl [si_P] [] c21_predctx si_P 0 si_cdecl
    c17_wfE Logic.eq_refl Logic.eq_refl Logic.eq_refl c21_beta_len.

Definition case_branch_type_conv_betaE_inst :=
  case_branch_type_conv_betaE c17_Σ [] si_ind si_mdecl si_idecl [si_P] [] c21_predctx si_P 0
    si_cdecl c17_wfE Logic.eq_refl Logic.eq_refl Logic.eq_refl Logic.eq_refl Logic.eq_refl
    c21_beta_len c17_declared_inductive c21_c17_declared_constructor.

Lemma c21_isT_predctx : isTypeE c17_Σ ([] ,,, c21_predctx) si_P.
Proof.
  exact (has_sort_isTypeE _ (iv_P_typed c17_Σ ([] ,,, c21_predctx)
           (iv_wf_P c17_Σ [] localenv_nil))).
Qed.

Lemma c21_wf_cstr_ctx :
  wf_localE c17_Σ ([] ,,, pre_case_branch_context_gen si_ind si_mdecl si_cdecl [si_P] []).
Proof. exact localenv_nil. Qed.

Definition case_branch_type_beta_typedE_inst :=
  case_branch_type_beta_typedE c17_Σ [] si_ind si_mdecl [si_P] [] c21_predctx si_P 0 si_cdecl
    c17_wfE c21_isT_predctx c21_wf_cstr_ctx c21_beta_len.

(** ** [cstr_indices_lengthE]: the η step is the one [wfE c17_env] holds *)

Definition cstr_indices_lengthE_inst :=
  @cstr_indices_lengthE _ c17_Σ c17_wfE (si_ind, 0) si_mdecl si_idecl si_cdecl
    c21_c17_declared_constructor.

(** ** [isType_mkApps_Ind_inv_spineE]: the η step is in [wf_extE c17_Σ] *)

Lemma c21_arity_typed :
  c17_Σ ;;; [] |-E si_arity : tSort iv_sPP.
Proof.
  (* [si_arity] is [tProd si_na si_P (tSort sProp)], and [si_P] IS [tSort sProp], so this is
     [iv_PP] of [PCUICInversionEtaInstances]. *)
  exact (iv_PP_typed c17_Σ [] localenv_nil).
Qed.

Lemma c21_I_False_typed : c17_Σ ;;; [] |-E tApp (tInd si_ind []) iv_False : si_P.
Proof.
  exact (typeE_App _ _ (tInd si_ind []) si_na si_P (tSort sProp) _ iv_False
           c21_arity_typed (c17_I_typed [] localenv_nil)
           (iv_False_typed c17_Σ [] localenv_nil)).
Qed.

Lemma c21_isT_I_False : isTypeE c17_Σ [] (mkApps (tInd si_ind []) ([iv_False] ++ [])).
Proof. exact (has_sort_isTypeE _ c21_I_False_typed). Qed.

Definition isType_mkApps_Ind_inv_spineE_inst :=
  isType_mkApps_Ind_inv_spineE si_ind si_mdecl si_idecl [iv_False] [] [] c17_Σ []
    c21_c17_wf_extE c17_declared_inductive Logic.eq_refl c21_isT_I_False.

(** ** Copy 18b's [match], whose discriminee is typed through one η step

  [make_case_pred si_ind si_mdecl si_idecl [k (λx:Prop. g x)] [] (lift0 1 (I (k (λx. g x))))]
  is copy 18b's predicate [c18b_p], and [make_br] of its single constructor is [c18b_br], so
  [make_case …] is copy 18b's [c18b_match]. The discriminee [c (k g)] is accepted at
  [I (k (λx:Prop. g x))] only through the η step ([c18b_disc_typed]). *)

Definition c21_rettyp : term := lift0 1 c18b_Ieta.
Definition c21_p : predicate term :=
  make_case_pred si_ind si_mdecl si_idecl [iv_keta] [] c21_rettyp.
Definition c21_pctx : context := case_predicate_context si_ind si_mdecl si_idecl c21_p.
Definition c21_ptm : term := it_mkLambda_or_LetIn c21_pctx (preturn c21_p).

Lemma c21_pctx_wf : wf_localE si_Σ (iv_Γk ,,, c21_pctx).
Proof. exact c18b_wf_pctx. Qed.

Lemma c21_pret : wf_localE si_Σ (iv_Γk ,,, c21_pctx) ->
  si_Σ ;;; iv_Γk ,,, c21_pctx |-E preturn c21_p : tSort sProp.
Proof. move=> _. exact c18b_pret_typed. Qed.

Lemma c21_elim : is_allowed_elimination si_Σ (ind_kelim si_idecl) sProp.
Proof. cbn; trivial. Qed.

Lemma c21_relevance : isSortRel (sProp : sort) (ind_relevance si_idecl).
Proof. reflexivity. Qed.

Lemma c21_fin :
  (isCoFinite (ind_finite si_mdecl) ==> on_free_vars (strengthenP 0 1 xpredT) c21_rettyp) = true.
Proof. reflexivity. Qed.

Lemma c21_brs_beta :
  All2i
    (fun (i : nat) (cdecl : constructor_body) (brt : term) =>
      let br := make_br si_ind si_mdecl cdecl brt in
      let brctxty := case_branch_type si_ind si_mdecl si_idecl c21_p br c21_ptm i cdecl in
        wf_localE si_Σ (iv_Γk ,,, brctxty.1) ->
        typingE si_Σ (iv_Γk ,,, brctxty.1) brctxty.2 (tSort sProp) ->
        typingE si_Σ (iv_Γk ,,, brctxty.1) (bbody br) brctxty.2)
    0 (ind_ctors si_idecl) [c18b_ceta].
Proof. constructor; [|constructor]. move=> /= _ _. exact c18b_br_typed. Qed.

Definition type_Case_helperE_inst :=
  type_Case_helperE si_ind si_mdecl si_idecl [iv_keta] [] c18b_ckg c21_rettyp [c18b_ceta] []
    sProp si_Σ iv_Γk c21_si_wf_extE si_declared_inductive Logic.eq_refl c18b_disc_typed
    c21_pret c21_elim c21_relevance c21_fin Logic.eq_refl c21_brs_beta.

(** ** [type_betasE]: the β-redex of that [match]'s motive

  The application whose typing the lemma reads is the one [validityE] gives for the [match]'s
  own type, so the η step of the discriminee is in its derivation. *)

Lemma c21_redex_typed :
  ∑ s, si_Σ ;;; iv_Γk |-E mkApps c21_ptm ([] ++ [c18b_ckg]) : tSort s.
Proof.
  have h := (validityE (Σ := si_Σ) (wfΣ := si_wfE) type_Case_helperE_inst).
  exists h.2.π1. exact h.2.π2.1.
Qed.

Lemma c21_betas_len : #|[] ++ [c18b_ckg]| = context_assumptions c21_pctx.
Proof. reflexivity. Qed.

Definition type_betasE_inst :=
  @type_betasE _ si_Σ si_wfE iv_Γk c21_pctx ([] ++ [c18b_ckg]) (preturn c21_p) (tSort sProp)
    (tSort c21_redex_typed.π1) c21_betas_len c18b_pret_typed c21_redex_typed.π2.

(** ** [type_Case_subst_helperE] and [type_Case_simple_subst_helperE]

  With no index and a constructor with no argument, the substituted branch type is
  [I (k (λx:Prop. g x))] itself, and the substituted return type is the same. *)

Lemma c21_brs_subst :
  All2i
    (fun (i : nat) (cdecl : constructor_body) (brt : term) =>
      let br := make_br si_ind si_mdecl cdecl brt in
      let brctx := case_branch_context si_ind si_mdecl c21_p br cdecl in
      let brty := case_branch_type_subst si_ind si_mdecl c21_p c21_pctx c21_rettyp i cdecl in
      wf_localE si_Σ (iv_Γk ,,, brctx) ->
      typingE si_Σ (iv_Γk ,,, brctx) brty (tSort sProp) ->
      typingE si_Σ (iv_Γk ,,, brctx) (bbody br) brty)
    0 (ind_ctors si_idecl) [c18b_ceta].
Proof. constructor; [|constructor]. move=> /= _ _. exact c18b_ceta_typed. Qed.

Definition type_Case_subst_helperE_inst :=
  type_Case_subst_helperE si_ind si_mdecl si_idecl [iv_keta] [] c18b_ckg c21_rettyp
    [c18b_ceta] [] sProp si_Σ iv_Γk c21_si_wf_extE si_declared_inductive Logic.eq_refl
    c18b_disc_typed c21_pret c21_elim c21_relevance c21_fin Logic.eq_refl c21_brs_subst.

Lemma c21_brs_simple :
  All2i
    (fun (i : nat) (cdecl : constructor_body) (brt : term) =>
      let br := make_br si_ind si_mdecl cdecl brt in
      let brctx := case_branch_context si_ind si_mdecl c21_p br cdecl in
      let brty := lift0 #|brctx| c18b_Ieta in
      wf_localE si_Σ (iv_Γk ,,, brctx) ->
      typingE si_Σ (iv_Γk ,,, brctx) brty (tSort sProp) ->
      typingE si_Σ (iv_Γk ,,, brctx) (bbody br) brty)
    0 (ind_ctors si_idecl) [c18b_ceta].
Proof. constructor; [|constructor]. move=> /= _ _. exact c18b_ceta_typed. Qed.

Definition type_Case_simple_subst_helperE_inst :=
  type_Case_simple_subst_helperE si_ind si_mdecl si_idecl [iv_keta] [] c18b_ckg c18b_Ieta
    [c18b_ceta] [] sProp si_Σ iv_Γk c21_si_wf_extE si_declared_inductive Logic.eq_refl
    c18b_disc_typed c18b_Ieta_typed c21_elim c21_relevance Logic.eq_refl c21_brs_simple.
