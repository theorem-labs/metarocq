(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the lemmas of [PCUICProgressEta] (row T6)

  **No forecast class.** The class of [PCUICClassificationEta] and [ProgForecastCopy18] were
  section variables here until copy 18b landed (frac/eta 3e6b422d); both are deleted. The environments are
  [si_Σ] ([Inductive I (A : Prop) : Prop := c : I A]) and [Σ_po] (the primitive integers,
  [PCUICEtaPrimOpInstance]).

  **Non-degeneracy.**
  - [typing_spine_pred_strengthenE_inst] strengthens a spine of [∀P. P] to the β-redex
    [(λx:Prop. x) (∀P. P)] ([sri_A]).
  - [inversion_mkAppsE_inst] (the sized inversion) runs on the β-redex [(λx:Prop. x) (∀P. P)].
  - [progressE_inst] (through [progress_env_propE] and the induction principle
    [typing_ind_envE], [typing_ind_env_app_sizeE]) and [typing_value_head_nappE_inst] /
    [typing_value_headE_inst] find the β-step of [(λx:Prop. x) (∀P. P)].
  - [eval_tCaseE_inst]: the closed [match (let y := ∀P. P in c y) with c x => c x end]
    ([pgi_match_let]): its scrutinee is a let-in, not a constructor application, so it evaluates
    by ζ, then ι.
  - [whnf_progressE_inst]: the normal form [∀P. P]. [classificationE_inst]: the normal
    constructor application [c (∀P. P)], at [extraction_checker_flags], the flags its statement
    is fixed to (as base's), in [si_Σ] proved [wfE] at those flags (section
    [ClassificationFlags]).
  - The constructor-arity lemmas run on [c (∀P. P) : I (∀P. P)].
  - [typing_spine_lengthE_inst]: the spine of [c] applied to [∀P. P].

  **Rows degenerate by the statement** ([typing_spine_sortE], [typing_spine_axiomE],
  [typing_spine_prim_typeE]): tagged IMPOSSIBLE at each instance. Each instance is tagged for the
  instance gate (its non-degeneracy lemma, or the reason) in the comment directly above it.

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

(** Declarations of this file that are neither instances nor non-degeneracy lemmas (instance gate):
    WITNESSES: pgx_* pgi_* *)

(** ** [si_env] and [c (∀P. P)] at [config.extraction_checker_flags], for [classificationE]

  [classificationE] binds no [checker_flags]: like base [PCUICProgress.classification], it is
  stated at [PCUICProgressEta]'s [Local Existing Instance config.extraction_checker_flags]. The
  landed [si_wf] and the typings of the instance files are at [default_checker_flags]. The two
  configurations differ in [prop_sub_type] and [lets_in_constructor_types] (both [true] in
  [default_checker_flags], both [false] in [extraction_checker_flags]), so [wf] does not carry
  over: configuration weakening ([config.impl]) goes from [false] to [true], not back. So the
  declaration of [Inductive I (A : Prop) : Prop := c : I A] is checked again here, at
  [extraction_checker_flags], by the steps of [si_wf]
  ([PCUICCumulativitySpecEtaClosureInstances]). No step uses [prop_sub_type] (no cumulativity
  step), and [on_lets_in_type] holds because [c] has no argument. The section's instance ends
  with the section, before the file's [default_checker_flags]. *)
Section ClassificationFlags.

  #[local] Existing Instance config.extraction_checker_flags.

  Lemma pgx_vass (Γ : context) (na : aname) A s :
    si_Σ0 ;;; Γ |- A : tSort s -> isSortRel s na.(binder_relevance) ->
    lift_typing typing si_Σ0 Γ (j_vass na A).
  Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [exact I|exact r]. Qed.

  Lemma pgx_vass_s (Γ : context) (na : aname) A s :
    si_Σ0 ;;; Γ |- A : tSort s -> isSortRel s na.(binder_relevance) ->
    lift_typing typing si_Σ0 Γ (j_vass_s na A s).
  Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [reflexivity|exact r]. Qed.

  Lemma pgx_P_typed (Γ : context) : wf_local si_Σ0 Γ -> si_Σ0 ;;; Γ |- si_P : tSort (Sort.super sProp).
  Proof. intros h. apply type_Sort; [exact h|cbn; trivial]. Qed.

  Lemma pgx_wf_P (Γ : context) : wf_local si_Σ0 Γ -> wf_local si_Σ0 (Γ ,, vass si_na si_P).
  Proof.
    intros h. apply localenv_cons_abs; [exact h|].
    exact (pgx_vass _ si_na _ _ (pgx_P_typed Γ h) eq_refl).
  Qed.

  Lemma pgx_arity_typed (Γ : context) : wf_local si_Σ0 Γ ->
    si_Σ0 ;;; Γ |- si_arity : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)).
  Proof.
    intros h. apply type_Prod.
    - exact (pgx_vass_s _ si_na _ _ (pgx_P_typed Γ h) eq_refl).
    - apply type_Sort; [exact (pgx_wf_P Γ h)|cbn; trivial].
  Qed.

  Lemma pgx_wf_Γi : wf_local si_Σ0 si_Γi.
  Proof.
    apply localenv_cons_abs; [constructor|].
    exact (pgx_vass _ (mkBindAnn (nNamed "I") rel_of_Type) _ _ (pgx_arity_typed [] localenv_nil) eq_refl).
  Qed.

  Lemma pgx_ctype_typed :
    si_Σ0 ;;; si_Γi |- cstr_type si_cdecl : tSort (Sort.sort_of_product (Sort.super sProp) sProp).
  Proof.
    have w2 := pgx_wf_P si_Γi pgx_wf_Γi.
    apply type_Prod.
    - exact (pgx_vass_s _ si_na _ _ (pgx_P_typed si_Γi pgx_wf_Γi) eq_refl).
    - refine (type_App _ _ (tRel 1) si_na si_P (tSort sProp)
                (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) (tRel 0) _ _ _).
      + exact (pgx_arity_typed _ w2).
      + exact (type_Rel _ _ 1 (vass (mkBindAnn (nNamed "I") rel_of_Type) si_arity) w2 eq_refl).
      + exact (type_Rel _ _ 0 (vass si_na si_P) w2 eq_refl).
  Qed.

  Lemma pgx_on_constructor :
    on_constructor cumulSpec0 (lift_typing typing) si_Σ0 si_mdecl 0 si_idecl [] si_cdecl [].
  Proof.
    unshelve econstructor.
    - reflexivity.
    - reflexivity.
    - exact (pgx_vass _ (mkBindAnn nAnon Relevant) _ _ pgx_ctype_typed eq_refl).
    - exact tt.
    - constructor.
    - cbn. eapply pos_ass.
      + apply pos_arg_closed. reflexivity.
      + exact (pos_concl _ _ _ [vass si_na si_P] [tRel 0] (All_cons (x := tRel 0) (eq_refl : is_true (closedn 1 (tRel 0))) All_nil)).
    - intros v e. discriminate e.
    - (* [lets_in_constructor_types] is [false] here: [c] has no argument, so no let *)
      reflexivity.
  Qed.

  Lemma pgx_on_ind_body :
    on_ind_body cumulSpec0 (lift_typing typing) si_Σ0 si_kn si_mdecl 0 si_idecl.
  Proof.
    unshelve econstructor.
    - exact [[]].
    - exists (tSort sProp). split; [reflexivity|].
      apply PCUICArityRed.arity_red_sort. apply PCUICArityRed.whd_stop. reflexivity.
    - exact (pgx_vass _ (mkBindAnn nAnon rel_of_Type) _ _ (pgx_arity_typed [] localenv_nil) eq_refl).
    - exact (pgx_vass _ (mkBindAnn nAnon rel_of_Type) _ _ (pgx_arity_typed [] localenv_nil) eq_refl).
    - constructor; [exact pgx_on_constructor|constructor].
    - exact I.
    - reflexivity.
    - reflexivity.
    - exact I.
  Qed.

  Lemma pgx_on_inductive : on_inductive cumulSpec0 (lift_typing typing) si_Σ0 si_kn si_mdecl.
  Proof.
    constructor.
    - constructor; [exact pgx_on_ind_body|constructor].
    - exact (pgx_wf_P [] localenv_nil).
    - reflexivity.
    - reflexivity.
  Qed.

  (** [si_env] is well formed at [extraction_checker_flags] ([si_on_udecl] binds no flags). *)
  Lemma pgx_wf : @wf config.extraction_checker_flags si_env.
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
    - split.
      { constructor; cbn; [constructor|intros c []|repeat split; intros c h; discriminate h
                          |intros i h; discriminate h]. }
      apply globenv_decl; [constructor|].
      constructor.
      + constructor.
      + exact si_on_udecl.
      + exact pgx_on_inductive.
      + cbn. intros i h; discriminate h.
  Qed.

  Definition pgx_wfE : @wfE config.extraction_checker_flags si_env := wf_incl_E pgx_wf.

  (** [c (∀P. P) : I (∀P. P)] over [typingE] in [si_Σ], at [extraction_checker_flags]. *)
  Lemma pgx_P_typedE (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E si_P : tSort (Sort.super sProp).
  Proof. intros h. apply typeE_Sort; [exact h|cbn; trivial]. Qed.

  Lemma pgx_vassE (Γ : context) : wf_localE si_Σ Γ -> lift_typing typingE si_Σ Γ (j_vass si_na si_P).
  Proof.
    intros h. split; [exact tt|]. exists (Sort.super sProp).
    split; [exact (pgx_P_typedE Γ h)|]. split; [exact I|reflexivity].
  Qed.

  Lemma pgx_vassE_s (Γ : context) :
    wf_localE si_Σ Γ -> lift_typing typingE si_Σ Γ (j_vass_s si_na si_P (Sort.super sProp)).
  Proof.
    intros h. split; [exact tt|]. exists (Sort.super sProp).
    split; [exact (pgx_P_typedE Γ h)|]. split; reflexivity.
  Qed.

  Lemma pgx_wf_PE (Γ : context) : wf_localE si_Σ Γ -> wf_localE si_Σ (Γ ,, vass si_na si_P).
  Proof. intros h. apply localenv_cons_abs; [exact h|exact (pgx_vassE Γ h)]. Qed.

  Lemma pgx_PP_typedE (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E iv_PP : tSort iv_sPP.
  Proof.
    intros h. unfold iv_PP, iv_sPP. apply typeE_Prod; [exact (pgx_vassE_s Γ h)|].
    exact (pgx_P_typedE _ (pgx_wf_PE Γ h)).
  Qed.

  Lemma pgx_False_typedE (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E iv_False : si_P.
  Proof.
    intros h. unfold iv_False.
    exact (typeE_Prod _ _ si_na si_P (tRel 0) (Sort.super sProp) sProp (pgx_vassE_s Γ h)
             (typeE_Rel _ _ 0 (vass si_na si_P) (pgx_wf_PE Γ h) eq_refl)).
  Qed.

  Lemma pgx_ind_typedE (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E tInd si_ind [] : si_arity.
  Proof. intros h. exact (typeE_Ind _ _ si_ind [] si_mdecl si_idecl h si_declared_inductive eq_refl). Qed.

  Lemma pgx_cstr_typedE (Γ : context) : wf_localE si_Σ Γ ->
    si_Σ ;;; Γ |-E tConstruct si_ind 0 [] : tProd si_na si_P (tApp (tInd si_ind []) (tRel 0)).
  Proof.
    intros h.
    exact (typeE_Construct _ _ si_ind 0 [] si_mdecl si_idecl si_cdecl h si_declared_constructor eq_refl).
  Qed.

  Lemma pgx_cstr_prod_typedE (Γ : context) : wf_localE si_Σ Γ ->
    si_Σ ;;; Γ |-E tProd si_na si_P (tApp (tInd si_ind []) (tRel 0))
      : tSort (Sort.sort_of_product (Sort.super sProp) sProp).
  Proof.
    intros h. apply typeE_Prod; [exact (pgx_vassE_s Γ h)|].
    have w := pgx_wf_PE Γ h.
    exact (typeE_App _ _ (tInd si_ind []) si_na si_P si_P _ (tRel 0) (pgx_PP_typedE _ w)
             (pgx_ind_typedE _ w) (typeE_Rel _ _ 0 (vass si_na si_P) w eq_refl)).
  Qed.

  Lemma pgx_cF_typedE : @typingE config.extraction_checker_flags si_Σ [] sri_cF iv_IF.
  Proof.
    exact (typeE_App _ _ (tConstruct si_ind 0 []) si_na si_P (tApp (tInd si_ind []) (tRel 0)) _ iv_False
             (pgx_cstr_prod_typedE [] localenv_nil) (pgx_cstr_typedE [] localenv_nil)
             (pgx_False_typedE [] localenv_nil)).
  Qed.

End ClassificationFlags.

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
  refine (type_spine_pred_consE _ _ _ iv_False iv_False [] si_na si_P (tRel 0) iv_False sProp
            (cli_False_isType [] localenv_nil) (iv_False_typed si_Σ [] localenv_nil) I
            (cli_False_refl [] localenv_nil) (iv_False_typed si_Σ [] localenv_nil) I _).
  econstructor; [exact (cli_False_isType [] localenv_nil)|exact (cli_False_isType [] localenv_nil)|].
  exact (cli_False_refl [] localenv_nil).
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
  eapply (@PCUICAritiesEta.type_spine_consE _ _ _ _ iv_False [] si_na si_P (tApp (tInd si_ind []) (tRel 0)) iv_IF).
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

(** The closed [match (let y := ∀P. P in c y) as z in I x return I x with c => c x end]
    ([pgi_match_let]). Its scrutinee is a let-in, not a constructor application: it reaches
    [c (∀P. P)] by a ζ step, then the match takes its branch by ι. [pgi_match_let] is
    [pgi_match_let_open] at [x := ∀P. P]: the [match] [iv_match] of [PCUICInversionEtaInstances],
    in [iv_Γ1 = [x : Prop]], with the scrutinee [let y := x in c y] in place of [c x]. That
    scrutinee has, by the LetIn rule, the let-in type [let y := x in I y] ([pgi_disc_let_ty]),
    which reduces to [I x] by ζ ([PCUICPrincipalityEtaInstances.principal_typeE_case_inst] runs
    T8 [Ind_r] on it). *)
Definition pgi_disc_let : term := tLetIn si_na (tRel 0) si_P (tApp (tConstruct si_ind 0 []) (tRel 0)).
Definition pgi_disc_let_ty : term := tLetIn si_na (tRel 0) si_P (iv_Ix 0).

Lemma pgi_disc_let_letin_typed : si_Σ ;;; iv_Γ1 |-E pgi_disc_let : pgi_disc_let_ty.
Proof.
  have hd := iv_vdef si_Σ iv_Γ1 si_na (tRel 0) si_P _ iv_x_typed (iv_P_typed si_Σ iv_Γ1 iv_wf_Γ1) eq_refl.
  have w : wf_localE si_Σ (iv_Γ1 ,, vdef si_na (tRel 0) si_P) := localenv_cons_def iv_wf_Γ1 hd.
  unfold pgi_disc_let, pgi_disc_let_ty. apply typeE_LetIn; [exact hd|].
  exact (typeE_App _ _ (tConstruct si_ind 0 []) si_na si_P (tApp (tInd si_ind []) (tRel 0)) _ (tRel 0)
           (iv_cstr_prod_typed _ w) (iv_cstr_typed _ w)
           (typeE_Rel _ _ 0 (vdef si_na (tRel 0) si_P) w eq_refl)).
Qed.

Lemma pgi_disc_let_typed : si_Σ ;;; iv_Γ1 |-E pgi_disc_let : iv_Ix 0.
Proof.
  refine (typeE_Cumul _ _ pgi_disc_let pgi_disc_let_ty (iv_Ix 0) sProp pgi_disc_let_letin_typed
            iv_Ix0_typed _).
  apply (ws_cumul_pbE_forget_spec (pb := Cumul)).
  apply (red_ws_cumul_pbE (Σ := si_Σ)).
  exact (closed_red_of (Σ := si_Σ) (Γ := iv_Γ1) (t := pgi_disc_let_ty) eq_refl eq_refl
           (red1_red _ _ _ _ (PCUICReduction.red_zeta _ _ si_na (tRel 0) si_P (iv_Ix 0)))).
Qed.

Definition pgi_match_let_open : term := tCase iv_ci iv_mp pgi_disc_let [iv_br].
Definition pgi_match_let_open_ty : term :=
  mkApps (it_mkLambda_or_LetIn (case_predicate_context si_ind si_mdecl si_idecl iv_mp) (preturn iv_mp))
    ([] ++ [pgi_disc_let]).

Lemma pgi_match_let_open_typed : si_Σ ;;; iv_Γ1 |-E pgi_match_let_open : pgi_match_let_open_ty.
Proof.
  eapply (typeE_Case _ _ iv_ci iv_mp pgi_disc_let [iv_br] [] sProp si_mdecl si_idecl).
  - exact si_declared_inductive.
  - exact iv_pret_typed.
  - exact pgi_disc_let_typed.
  - exact iv_case_side.
  - exact iv_case_brs.
Qed.

Definition pgi_match_let : term := Eval cbn in pgi_match_let_open {0 := iv_False}.
Definition pgi_match_let_ty : term := Eval cbn in pgi_match_let_open_ty {0 := iv_False}.

Lemma pgi_match_let_typed : si_Σ ;;; [] |-E pgi_match_let : pgi_match_let_ty.
Proof.
  exact (substitution0E (Σ := si_Σ) (wfΣ := si_wfE) (Γ := []) pgi_match_let_open_typed
           (iv_False_typed si_Σ [] localenv_nil)).
Qed.

(** [let y := ∀P. P in c y] evaluates to [c (∀P. P)] by ζ. *)
Lemma pgi_disc_let_eval : eval si_Σ (pgi_disc_let {0 := iv_False}) sri_cF.
Proof.
  change (eval si_Σ (tLetIn si_na iv_False si_P (tApp (tConstruct si_ind 0 []) (tRel 0))) sri_cF).
  eapply eval_zeta; [eapply eval_atom; reflexivity|exact cli_cF_eval].
Qed.

Lemma pgi_match_let_eval : eval si_Σ pgi_match_let sri_cF.
Proof.
  eapply (eval_iota _ iv_ci _ 0 si_mdecl si_idecl si_cdecl [] [iv_False]).
  - exact pgi_disc_let_eval.
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

(** The scrutinee of [pgi_match_let] is a let-in, not a constructor application. *)
Lemma eval_tCaseE_inst_nondeg : isConstruct_app (pgi_disc_let {0 := iv_False}) = false.
Proof. reflexivity. Qed.

(** [eval_tCaseE] on [pgi_match_let]: its scrutinee is not a constructor application
    ([eval_tCaseE_inst_nondeg]), so the reduction the lemma returns, to the match on
    [c (∀P. P)], is not reflexive (ζ).
    INSTANCE NONDEGEN PCUICProgressEtaInstances.eval_tCaseE_inst_nondeg *)
Definition eval_tCaseE_inst :=
  eval_tCaseE (Σ := si_Σ) _ _ (pgi_disc_let {0 := iv_False}) _ _ _ si_wfE pgi_match_let_typed
    pgi_match_let_eval.

(** The type the spine is moved to, [(λx:Prop. x) (∀P. P)] ([sri_A]), is not [∀P. P]. *)
Lemma typing_spine_pred_strengthenE_inst_nondeg : sri_A <> iv_False.
Proof. discriminate. Qed.

(** INSTANCE NONDEGEN PCUICProgressEtaInstances.typing_spine_pred_strengthenE_inst_nondeg *)
Definition typing_spine_pred_strengthenE_inst :=
  typing_spine_pred_strengthenE (Σ := si_Σ) (wfΣ := si_wfE) pgi_sp_pred (cli_False_isType [] localenv_nil)
    sri_A sri_A_isType pgi_A_ws.

(** [(λx:Prop. x) (∀P. P)] is a β-redex: its head [iv_id] is an abstraction and its spine is
    not empty. The sized inversion runs its non-empty-spine case on it; it is not a value, so
    progress and the value-head lemmas find its β step. *)
Lemma pgi_beta_redex_nondeg : isLambda iv_id /\ [iv_False] <> [].
Proof. split; [reflexivity|discriminate]. Qed.

(** INSTANCE NONDEGEN PCUICProgressEtaInstances.pgi_beta_redex_nondeg *)
Definition inversion_mkAppsE_inst :=
  PCUICProgressEta.inversion_mkAppsE (Σ := si_Σ) (wfΣ := si_wfE) (f := iv_id) (u := [iv_False])
    (Sort.super sProp) (iv_app_typed si_Σ [] localenv_nil) (iv_P_typed si_Σ [] localenv_nil).

(** The spine of [c] is not empty and reaches the bound: one argument, one assumption. *)
Lemma typing_spine_lengthE_inst_nondeg :
  0 < #|[iv_False]| /\ #|[iv_False]| = context_assumptions [vass si_na si_P].
Proof. split; [exact (le_n 1)|reflexivity]. Qed.

(** INSTANCE NONDEGEN PCUICProgressEtaInstances.typing_spine_lengthE_inst_nondeg *)
Definition typing_spine_lengthE_inst : #|[iv_False]| <= context_assumptions [vass si_na si_P] :=
  typing_spine_lengthE (Σ := si_Σ) (wfΣ := si_wfE) [] [vass si_na si_P] si_ind [] [tRel 0] [iv_False] iv_IF pgi_sp_cstr.

(** [I] is the last (only) body of its block: the bound [inductive_ind ind < #|ind_bodies|] is
    reached. *)
Lemma declared_constructor_ind_declE_inst_nondeg :
  S (inductive_ind si_ind) = #|ind_bodies si_mdecl|.
Proof. reflexivity. Qed.

(** INSTANCE NONDEGEN PCUICProgressEtaInstances.declared_constructor_ind_declE_inst_nondeg *)
Definition declared_constructor_ind_declE_inst :=
  declared_constructor_ind_declE (Σ := si_Σ) (wfΣ := si_wfE) (ind := si_ind) (mdecl := si_mdecl)
    si_declared_constructor.

(** [c] is applied to one argument: the equation is [1 = 1], not [0 = 0]. *)
Lemma typing_constructor_arity_exactE_inst_nondeg : 0 < #|[iv_False]|.
Proof. exact (le_n 1). Qed.

(** INSTANCE NONDEGEN PCUICProgressEtaInstances.typing_constructor_arity_exactE_inst_nondeg *)
Definition typing_constructor_arity_exactE_inst : #|[iv_False]| = cstr_arity si_mdecl si_cdecl :=
  typing_constructor_arity_exactE (Σ := si_Σ) (wfΣ := si_wfE) (args := [iv_False]) (indices := [iv_False])
    si_declared_constructor sri_cF_typed.

(** [c] is applied to one argument, its full arity: the bound is reached. *)
Lemma typing_constructor_arityE_inst_nondeg :
  0 < #|[iv_False]| /\ #|[iv_False]| = cstr_arity si_mdecl si_cdecl.
Proof. split; [exact (le_n 1)|reflexivity]. Qed.

(** INSTANCE NONDEGEN PCUICProgressEtaInstances.typing_constructor_arityE_inst_nondeg *)
Definition typing_constructor_arityE_inst : #|[iv_False]| <= cstr_arity si_mdecl si_cdecl :=
  typing_constructor_arityE (Σ := si_Σ) (wfΣ := si_wfE) (args := [iv_False]) si_declared_constructor sri_cF_typed.

(** INSTANCE IMPOSSIBLE: the conclusion is [args = []]: a sort is never convertible to a product, so in every environment a spine on [tSort s] has no argument and every instance concludes [[] = []]. *)
Definition typing_spine_sortE_inst : @nil term = [] :=
  typing_spine_sortE (Σ := si_Σ) (wfΣ := si_wfE) [] sProp [] (tSort sProp) pgi_sp_sort.

Lemma pgi_int_isType : isTypeE Σ_po [] (prim_type iv_one po_int_kn).
Proof. exact (validityE (Σ := Σ_po) (wfΣ := iv_po_wfE) iv_prim_typed). Qed.

Lemma pgi_sp_int : PCUICAritiesEta.typing_spineE Σ_po [] (prim_type iv_one po_int_kn) [] (prim_type iv_one po_int_kn).
Proof.
  econstructor; [exact pgi_int_isType|exact pgi_int_isType|].
  exact (isType_ws_cumul_pbE_refl (Σ := Σ_po) [] _ pgi_int_isType).
Qed.

(** INSTANCE IMPOSSIBLE: the conclusion is [args = []]: a primitive type [prim_type prim prim_ty] is an application of the bodiless, non-operation constant [prim_ty], never convertible to a product, so in every environment its spine has no argument and every instance concludes [[] = []]. *)
Definition typing_spine_prim_typeE_inst : @nil term = [] :=
  typing_spine_prim_typeE (Σ := Σ_po) (wfΣ := iv_po_wfE) [] iv_one po_int_kn po_int_body [] _
    ltac:(reflexivity) iv_po_declared_int ltac:(split; reflexivity) pgi_sp_int.

(** INSTANCE IMPOSSIBLE: the conclusion is [args' = []]: an application of a constant with no body that is no primitive operation is never convertible to a product, so in every environment its spine has no argument and every instance concludes [[] = []]. *)
Definition typing_spine_axiomE_inst : @nil term = [] :=
  typing_spine_axiomE (Σ := Σ_po) (wfΣ := iv_po_wfE) [] po_int_kn [] po_int_body [] [] _
    iv_po_declared_int ltac:(reflexivity) ltac:(vm_compute; reflexivity) pgi_sp_int.

Lemma pgi_False_value : value si_Σ iv_False.
Proof. apply value_atomic, atomic_atom. reflexivity. Qed.

Lemma pgi_id_value : value si_Σ (mkApps iv_id []).
Proof. apply value_atomic, atomic_atom. reflexivity. Qed.

(** INSTANCE NONDEGEN PCUICProgressEtaInstances.pgi_beta_redex_nondeg *)
Definition typing_value_head_nappE_inst :=
  typing_value_head_nappE (Σ := si_Σ) (wfΣ := si_wfE) iv_id [] iv_False si_P eq_refl
    (iv_app_typed si_Σ [] localenv_nil) pgi_False_value eq_refl pgi_id_value.

(** INSTANCE NONDEGEN PCUICProgressEtaInstances.pgi_beta_redex_nondeg *)
Definition typing_value_headE_inst :=
  typing_value_headE (Σ := si_Σ) (wfΣ := si_wfE) iv_id [] iv_False si_P
    (iv_app_typed si_Σ [] localenv_nil) pgi_False_value eq_refl pgi_id_value.

(** INSTANCE NONDEGEN PCUICProgressEtaInstances.pgi_beta_redex_nondeg *)
Definition progress_env_propE_inst :=
  env_propE_typing progress_env_propE si_Σ si_wfE [] (tApp iv_id iv_False) si_P
    (iv_app_typed si_Σ [] localenv_nil) cli_axiom_free eq_refl (iv_app_typed si_Σ [] localenv_nil).

(** INSTANCE NONDEGEN PCUICProgressEtaInstances.pgi_beta_redex_nondeg *)
Definition progressE_inst :=
  progressE si_Σ (tApp iv_id iv_False) si_P cli_axiom_free si_wfE (iv_app_typed si_Σ [] localenv_nil).

(** [whnf_progressE] on the normal form [∀P. P]: its normality ([pgi_False_normal], every
    [red1] step from it is refuted by inversion through its domain and codomain) is the premise
    the lemma turns into [whnf].
    INSTANCE NONDEGEN PCUICProgressEtaInstances.pgi_False_normal *)
Definition whnf_progressE_inst :=
  whnf_progressE si_Σ iv_False si_P cli_axiom_free si_wfE (iv_False_typed si_Σ [] localenv_nil)
    (fun h => let (t', r) := h in pgi_False_normal _ _ _ r).

(** The head of [c (∀P. P)] is read off an application: it is [c], not the term itself. *)
Lemma classificationE_inst_nondeg : PCUICAstUtils.head sri_cF <> sri_cF.
Proof. discriminate. Qed.

(** [classificationE], at its statement's flags [config.extraction_checker_flags] (as base's):
    the constructor application [c (∀P. P)], [red1]-normal ([pgi_cF_normal]), typed at
    [I (∀P. P)] over [typingE] ([pgx_cF_typedE]) in [si_Σ], which is proved [wfE] at those flags
    ([pgx_wfE], section [ClassificationFlags]). [whnf_progressE] turns the normality into [whnf],
    and [whnf_classificationE] reads the head [c] off the typed normal form.
    INSTANCE NONDEGEN PCUICProgressEtaInstances.classificationE_inst_nondeg *)
Definition classificationE_inst :=
  classificationE si_Σ sri_cF si_ind [] [iv_False] cli_axiom_free pgx_wfE
    (fun h => let (t', r) := h in pgi_cF_normal _ _ _ r) pgx_cF_typedE.

End ProgressEtaInstances.
