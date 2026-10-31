(* Distributed under the terms of the MIT license. *)

(* NONDEGEN tags: an INSTANCE NONDEGEN tag is a reader judgment backed by a compiled nontriviality
   lemma, not a mechanical guarantee.
   Measured reader miss rate: at least 17 of 60 sampled instances (28.3%, 95% upper bound 39.4%), seed 202610301905: the union of the verdicts held by two independent reviews (Opus 5: 10 of 60; Opus 5.5: 15 of 60, 6 of its verdicts borderline at confidence 0.5-0.6). The 17 sampled misses are corrected at this head, but the sample estimates the rate over ALL instance tags: a comparable share of the unsampled instances is expected to be wrong and is NOT corrected. *)

(** * Satisfying instances of the lemmas of [PCUICProgressEta] (row T6)

  **No forecast class.** The class of [PCUICClassificationEta] and [ProgForecastCopy18] were
  section variables here until copy 18b landed (frac/eta 3e6b422d); both are deleted. The environments are
  [si_Σ] ([Inductive I (A : Prop) : Prop := c : I A]) and [Σ_po] (the primitive integers,
  [PCUICEtaPrimOpInstance]).

  **Non-degeneracy.**
  - [typing_spine_pred_strengthenE_inst] applies the lemma to the spine [pgi_sp_T0] of
    [∀X:Prop. Type₀] (built with the head step [pgi_PT0_PT1], [Type₀ ≤ Type₁] in the codomain)
    and to [Prop → Prop] with [Prop ≤ Type₀] in the codomain ([pgi_PP_PT0]); it returns a spine of
    [Prop → Prop]. The three products [Prop → Prop], [∀X:Prop. Type₀] and [∀X:Prop. Type₁] are
    pairwise distinct ([typing_spine_pred_strengthenE_inst_nondeg]).
  - [inversion_mkAppsE_inst] (the sized inversion) runs on the β-redex [(λx:Prop. x) (∀P. P)],
    whose spine [[∀P. P]] is not empty.
  - [progressE_inst] (through [progress_env_propE] and the induction principle [typing_ind_envE],
    [typing_ind_env_app_sizeE]), [progress_env_propE_inst], [typing_value_head_nappE_inst] and
    [typing_value_headE_inst] run on [(λx:Prop. x → x) (∀P. P)] ([sri_xx_redex]), whose redex body
    uses its variable inside a product: it is not a value, and its WCBV step goes to
    [(∀P. P) → ∀P. P], neither the argument nor the redex ([progressE_inst_nondeg]): the value
    disjunct of the sum each returns is empty.
  - [eval_tCaseE_inst]: the closed [match (let y := ∀P. P in c y) with c x => c x end]
    ([pgi_match_let]): its scrutinee is a let-in, not a constructor application
    ([eval_tCaseE_inst_nondeg]), so the reduction the lemma returns, to a match on a constructor
    application, is not reflexive.
  - [whnf_progressE_inst] and [classificationE_inst]: the [red1]-normal constructor application
    [c (∀P. P)], an application whose head [c] is not the term itself; [classificationE_inst] at
    [extraction_checker_flags], the flags its statement is fixed to (as base's), in [si_Σ] proved
    [wfE] at those flags (section [ClassificationFlags]).
  - The constructor-arity lemmas run on [c (∀P. P) : I (∀P. P)].
  - [typing_spine_lengthE_inst]: the spine of [c] applied to [∀P. P].
  - [typing_ind_envE_closedn_inst], [typing_ind_env_app_sizeE_closedn_inst]: the two induction
    principles with predicates that are not [unit] (the subject, the judgment and the context are
    scoped), every case proved in general (section [ClosednInduction]).

  **Rows degenerate by the statement**, tagged IMPOSSIBLE at each instance: [typing_spine_sortE],
  [typing_spine_axiomE], [typing_spine_prim_typeE] (the conclusion is forced), and
  [declared_constructor_ind_declE] (its proof reads the conclusion off its own premise). Each
  instance is tagged for the instance gate (its non-degeneracy lemma, or the reason) in the
  comment directly above it.

  **Helpers run by the instances above:** [typing_ind_envE], [typing_ind_env_app_sizeE] (also by
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

(** ** [typing_ind_envE] and [typing_ind_env_app_sizeE] with predicates that are not [unit]

  [typing_ind_envE_closedn_inst] and [typing_ind_env_app_sizeE_closedn_inst] instantiate the two
  induction principles of [PCUICProgressEta], at any flags, with
  - [pgi_cl_P]: the subject is scoped by its context, [closedn #|Γ| t];
  - [pgi_cl_Pj]: the judgment's term (if any) and type are scoped,
    [lift_wfb_term (closedn #|Γ|) j];
  - [pgi_cl_PΓ]: the context is closed, [closed_ctx Γ].
  Each of the 17 case hypotheses is proved in general by a [pgi_cl_] lemma, stated as the
  principle states it. The two principles share every case but the application spine, where
  [typing_ind_env_app_sizeE] passes one more hypothesis (the sized induction hypothesis), which
  [pgi_cl_app] does not use. The spine case reads the scoping of every argument off the
  [typing_spine_predE] premise ([pgi_cl_spine]); the [tCase] case uses [wfE Σ] for the
  closedness of the inductive's predicate and branch contexts ([declared_minductive_closedE]);
  the [tPrim] case reads the array hypotheses. Each of the three predicates is false on some
  input ([pgi_cl_nondeg]). *)

Section ClosednInduction.

  Context {cf : checker_flags}.

  Definition pgi_cl_P : global_env_ext -> context -> term -> term -> Type :=
    fun _ Γ t _ => is_true (closedn #|Γ| t).

  Definition pgi_cl_Pj : global_env_ext -> context -> judgment -> Type :=
    fun _ Γ j => is_true (lift_wfb_term (closedn #|Γ|) j).

  Definition pgi_cl_PΓ : global_env_ext -> context -> Type :=
    fun _ Γ => is_true (closed_ctx Γ).

  (** Each of the three predicates is false on some input: the subject [tRel 0] is not scoped in
      the empty context, the context [[_ : tRel 0]] is not closed, and the judgment [_ : tRel 0]
      is not scoped in the empty context. *)
  Lemma pgi_cl_nondeg :
    (pgi_cl_P si_Σ [] (tRel 0) si_P -> False) ×
    (pgi_cl_PΓ si_Σ [vass si_na (tRel 0)] -> False) ×
    (pgi_cl_Pj si_Σ [] (j_vass si_na (tRel 0)) -> False).
  Proof. split; [|split]; intros h; vm_compute in h; discriminate h. Qed.

  Lemma pgi_cl_ctx_args {Q : context -> term -> term -> Type} {Γ inst Δ} :
    PCUICTyping.ctx_inst Q Γ inst Δ -> (forall t T, Q Γ t T -> is_true (closedn #|Γ| t)) ->
    is_true (forallb (closedn #|Γ|) inst).
  Proof.
    intros h hQ. induction h as [|na t i inst' Δ' hi _ IH|na b t inst' Δ' _ IH].
    - reflexivity.
    - change (is_true (closedn #|Γ| i && forallb (closedn #|Γ|) inst')).
      apply/andP; split; [exact (hQ _ _ hi)|exact IH].
    - exact IH.
  Qed.

  Lemma pgi_cl_spine {Σ : global_env_ext} {Γ : context} {Q : forall t T, Σ ;;; Γ |-E t : T -> Type}
    {T L B} :
    typing_spine_predE Σ Γ Q T L B ->
    (forall t T (H : Σ ;;; Γ |-E t : T), Q t T H -> is_true (closedn #|Γ| t)) ->
    is_true (forallb (closedn #|Γ|) L).
  Proof.
    intros h hQ.
    induction h as [ty ty' _ _ _|ty hd tl na A B0 B' s' _ H' _ _ Hhd hhd _ IH]; [reflexivity|].
    change (is_true (closedn #|Γ| hd && forallb (closedn #|Γ|) tl)).
    apply/andP; split; [exact (hQ _ _ _ hhd)|exact IH].
  Qed.

  (** *** The 17 cases, each as the principle states it *)

  Lemma pgi_cl_judgment :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ.1) (Γ : context) j,
      lift_typing_conj (typingE Σ) (pgi_cl_P Σ) Γ j -> pgi_cl_Pj Σ Γ j.
  Proof.
    intros Σ wfΣ Γ j (Htm & s & (_ & Hty) & _).
    change (is_true (option_default (closedn #|Γ|) (j_term j) true && closedn #|Γ| (j_typ j))).
    apply/andP; split; [|exact Hty].
    revert Htm. case: (j_term j) => [tm|] /= Htm; [exact (snd Htm)|reflexivity].
  Qed.

  Lemma pgi_cl_context :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ),
      All_local_env_over (typingE Σ) (fun Γ wfΓ t T tyT => pgi_cl_P Σ Γ t T) Γ wfΓ ->
      All_local_env (pgi_cl_Pj Σ) Γ -> pgi_cl_PΓ Σ Γ.
  Proof.
    intros Σ wfΣ Γ wfΓ hover hall. clear hover wfΓ.
    change (is_true (closed_ctx Γ)).
    induction hall as [|Δ na t _ IH h|Δ na b t _ IH h].
    - reflexivity.
    - have hs : is_true (closedn #|Δ| t) := h.
      change (is_true (closed_ctx Δ && closedn (#|Δ| + 0) t)). rewrite Nat.add_0_r.
      apply/andP; split; [exact IH|exact hs].
    - have hs : is_true (closedn #|Δ| b && closedn #|Δ| t) := h.
      change (is_true (closed_ctx Δ && (closedn (#|Δ| + 0) b && closedn (#|Δ| + 0) t))).
      rewrite Nat.add_0_r.
      apply/andP; split; [exact IH|exact hs].
  Qed.

  Lemma pgi_cl_rel :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (n : nat) decl,
      nth_error Γ n = Some decl ->
      pgi_cl_PΓ Σ Γ ->
      pgi_cl_P Σ Γ (tRel n) (lift0 (S n) decl.(decl_type)).
  Proof.
    intros Σ wfΣ Γ wfΓ n decl h _. change (is_true (Nat.ltb n #|Γ|)).
    apply Nat.ltb_lt. exact (nth_error_Some_length h).
  Qed.

  Lemma pgi_cl_sort :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (u : sort),
      pgi_cl_PΓ Σ Γ ->
      wf_sort Σ u ->
      pgi_cl_P Σ Γ (tSort u) (tSort (Sort.super u)).
  Proof. intros; exact (@eq_refl bool true). Qed.

  Lemma pgi_cl_prod :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (na : aname)
           (t b : term) (s1 s2 : sort),
      pgi_cl_PΓ Σ Γ ->
      lift_typing typingE Σ Γ (j_vass_s na t s1) ->
      pgi_cl_Pj Σ Γ (j_vass_s na t s1) ->
      Σ ;;; Γ,, vass na t |-E b : tSort s2 ->
      pgi_cl_P Σ (Γ,, vass na t) b (tSort s2) ->
      pgi_cl_P Σ Γ (tProd na t b) (tSort (Sort.sort_of_product s1 s2)).
  Proof.
    intros Σ wfΣ Γ wfΓ na t b s1 s2 _ _ hj _ hb.
    have hj' : is_true (closedn #|Γ| t) := hj.
    have hb' : is_true (closedn (S #|Γ|) b) := hb.
    change (is_true (closedn #|Γ| t && closedn (S #|Γ|) b)).
    apply/andP; split; [exact hj'|exact hb'].
  Qed.

  Lemma pgi_cl_lambda :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (na : aname)
           (t b bty : term),
      pgi_cl_PΓ Σ Γ ->
      lift_typing typingE Σ Γ (j_vass na t) ->
      pgi_cl_Pj Σ Γ (j_vass na t) ->
      Σ ;;; Γ,, vass na t |-E b : bty -> pgi_cl_P Σ (Γ,, vass na t) b bty ->
      pgi_cl_P Σ Γ (tLambda na t b) (tProd na t bty).
  Proof.
    intros Σ wfΣ Γ wfΓ na t b bty _ _ hj _ hb.
    have hj' : is_true (closedn #|Γ| t) := hj.
    have hb' : is_true (closedn (S #|Γ|) b) := hb.
    change (is_true (closedn #|Γ| t && closedn (S #|Γ|) b)).
    apply/andP; split; [exact hj'|exact hb'].
  Qed.

  Lemma pgi_cl_letin :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (na : aname)
           (b b_ty b' b'_ty : term),
      pgi_cl_PΓ Σ Γ ->
      lift_typing typingE Σ Γ (j_vdef na b b_ty) ->
      pgi_cl_Pj Σ Γ (j_vdef na b b_ty) ->
      Σ ;;; Γ,, vdef na b b_ty |-E b' : b'_ty ->
      pgi_cl_P Σ (Γ,, vdef na b b_ty) b' b'_ty ->
      pgi_cl_P Σ Γ (tLetIn na b b_ty b') (tLetIn na b b_ty b'_ty).
  Proof.
    intros Σ wfΣ Γ wfΓ na b b_ty b' b'_ty _ _ hj _ hb.
    have hj' : is_true (closedn #|Γ| b && closedn #|Γ| b_ty) := hj.
    have hb' : is_true (closedn (S #|Γ|) b') := hb.
    change (is_true (closedn #|Γ| b && closedn #|Γ| b_ty && closedn (S #|Γ|) b')).
    apply/andP; split; [exact hj'|exact hb'].
  Qed.

  Lemma pgi_cl_app :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (t : term) T B L s,
      pgi_cl_PΓ Σ Γ ->
      Σ ;;; Γ |-E T : tSort s -> pgi_cl_P Σ Γ T (tSort s) ->
      forall (Ht : Σ ;;; Γ |-E t : T), pgi_cl_P Σ Γ t T ->
      typing_spine_predE Σ Γ (fun u ty H => Σ ;;; Γ |-E u : ty × pgi_cl_P Σ Γ u ty) T L B ->
      pgi_cl_P Σ Γ (mkApps t L) B.
  Proof.
    intros Σ wfΣ Γ wfΓ t T B L s _ _ _ _ ht hsp.
    change (is_true (closedn #|Γ| (mkApps t L))).
    rewrite PCUICClosed.closedn_mkApps. apply/andP; split; [exact ht|].
    exact (pgi_cl_spine hsp (fun _ _ _ q => snd q)).
  Qed.

  Lemma pgi_cl_const :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) cst u
           (decl : constant_body),
      on_global_env cumulSpecE0 pgi_cl_Pj Σ.1 ->
      pgi_cl_PΓ Σ Γ ->
      declared_constant Σ.1 cst decl ->
      consistent_instance_ext Σ decl.(cst_universes) u ->
      pgi_cl_P Σ Γ (tConst cst u) (subst_instance u (cst_type decl)).
  Proof. intros; exact (@eq_refl bool true). Qed.

  Lemma pgi_cl_ind :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (ind : inductive) u
           mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl),
      on_global_env cumulSpecE0 pgi_cl_Pj Σ.1 ->
      pgi_cl_PΓ Σ Γ ->
      consistent_instance_ext Σ mdecl.(ind_universes) u ->
      pgi_cl_P Σ Γ (tInd ind u) (subst_instance u (ind_type idecl)).
  Proof. intros; exact (@eq_refl bool true). Qed.

  Lemma pgi_cl_construct :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (ind : inductive)
           (i : nat) u mdecl idecl cdecl (isdecl : declared_constructor Σ.1 (ind, i) mdecl idecl cdecl),
      on_global_env cumulSpecE0 pgi_cl_Pj Σ.1 ->
      pgi_cl_PΓ Σ Γ ->
      consistent_instance_ext Σ mdecl.(ind_universes) u ->
      pgi_cl_P Σ Γ (tConstruct ind i u) (type_of_constructor mdecl cdecl (ind, i) u).
  Proof. intros; exact (@eq_refl bool true). Qed.

  Lemma pgi_cl_case :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ) (Γ : context) (wfΓ : wf_localE Σ Γ),
    forall (ci : case_info) p c brs indices ps mdecl idecl
      (isdecl : declared_inductive Σ.1 ci.(ci_ind) mdecl idecl),
      on_global_env cumulSpecE0 pgi_cl_Pj Σ.1 ->
      pgi_cl_PΓ Σ Γ ->
      mdecl.(ind_npars) = ci.(ci_npar) ->
      eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
      let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
      wf_predicate mdecl idecl p ->
      consistent_instance_ext Σ (ind_universes mdecl) p.(puinst) ->
      forall pret : Σ ;;; Γ ,,, predctx |-E p.(preturn) : tSort ps,
      pgi_cl_P Σ (Γ ,,, predctx) p.(preturn) (tSort ps) ->
      wf_localE Σ (Γ ,,, predctx) ->
      pgi_cl_PΓ Σ (Γ ,,, predctx) ->
      is_allowed_elimination Σ idecl.(ind_kelim) ps ->
      PCUICTyping.ctx_inst (Prop_conj typingE pgi_cl_P Σ) Γ (p.(pparams) ++ indices)
        (List.rev (subst_instance p.(puinst) (mdecl.(ind_params) ,,, idecl.(ind_indices) : context))) ->
      Σ ;;; Γ |-E c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices) ->
      pgi_cl_P Σ Γ c (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices)) ->
      implb (isCoFinite mdecl.(ind_finite)) (on_free_vars (strengthenP 0 1 ssrbool.xpredT) p.(preturn)) = true ->
      let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
      wf_branches idecl brs ->
      All2i (fun i cdecl br =>
        (eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl)) ×
        let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
        (pgi_cl_PΓ Σ (Γ ,,, brctxty.1) ×
          (Prop_conj typingE pgi_cl_P Σ (Γ ,,, brctxty.1) br.(bbody) brctxty.2) ×
          (Prop_conj typingE pgi_cl_P) Σ (Γ ,,, brctxty.1) brctxty.2 (tSort ps))) 0 idecl.(ind_ctors) brs ->
      pgi_cl_P Σ Γ (tCase ci p c brs) (mkApps ptm (indices ++ [c])).
  Proof.
    intros Σ wfΣ Γ wfΓ ci p c brs indices ps mdecl idecl isdecl _ _ _ heqctx predctx hwfp _ _ hret
      _ _ _ hpars _ hc _ ptm hwfbrs hbrs.
    pose proof (declared_minductive_closedE (wfΣ := wfΣ) (proj1 isdecl)) as hcl.
    pose proof (declared_minductive_ind_nparsE (wfΣ := wfΣ) (proj1 isdecl)) as hnp.
    pose proof (declared_inductive_closed_constructorsE (wfΣ := wfΣ) isdecl) as hctors.
    pose proof (wf_predicate_length_pars hwfp) as hlenp.
    rewrite hnp in hlenp.
    have hpi : is_true (forallb (closedn #|Γ|) (pparams p ++ indices)) :=
      pgi_cl_ctx_args hpars (fun _ _ h => snd h).
    rewrite forallb_app in hpi. move/andP: hpi => [hpp _].
    change (is_true (test_predicate_k (fun _ => true) closedn #|Γ| p && closedn #|Γ| c &&
                     test_branches_k p closedn #|Γ| brs)).
    apply/andP; split; [apply/andP; split|].
    - change (is_true (forallb (closedn #|Γ|) (pparams p) &&
                       test_context_k closedn #|pparams p| (pcontext p) &&
                       closedn (#|pcontext p| + #|Γ|) (preturn p))).
      apply/andP; split; [apply/andP; split|].
      + exact hpp.
      + rewrite (PCUICClosedConv.closedn_ctx_alpha heqctx) hlenp.
        exact (PCUICClosed.closed_ind_predicate_context isdecl hcl).
      + have e : #|Γ ,,, predctx| = #|pcontext p| + #|Γ|.
        { rewrite app_context_length. f_equal. exact (case_predicate_context_length (ci := ci) hwfp). }
        have hret' : is_true (closedn #|Γ ,,, predctx| (preturn p)) := hret.
        rewrite e in hret'. exact hret'.
    - exact hc.
    - pose proof (All2i_All_mix_left hctors
        (All2i_All2_mix_left (Forall2_All2 (P := wf_branch) _ _ hwfbrs) hbrs)) as hb.
      clear -hb hcl hlenp.
      induction hb as [|i cdecl br cdecls brs' [hcc [hwb hR]] _ IH]; [reflexivity|].
      change (is_true (test_branch_k p closedn #|Γ| br && forallb (test_branch_k p closedn #|Γ|) brs')).
      apply/andP; split; [|exact IH].
      destruct hR as (heqb & hR). cbv zeta in hR. destruct hR as (_ & (_ & hbody) & _).
      change (is_true (test_context_k closedn #|pparams p| (bcontext br) &&
                       closedn (#|bcontext br| + #|Γ|) (bbody br))).
      apply/andP; split.
      + rewrite (PCUICClosedConv.closedn_ctx_alpha heqb) hlenp.
        exact (closed_cstr_branch_context_genE hcl hcc).
      + have hbody' : is_true (closedn #|Γ ,,, (case_branch_type (ci_ind ci) mdecl idecl p br ptm i cdecl).1|
                                 (bbody br)) := hbody.
        rewrite app_context_length case_branch_type_fst (case_branch_context_length hwb) in hbody'.
        exact hbody'.
  Qed.

  Lemma pgi_cl_proj :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (p : projection)
           (c : term) u mdecl idecl cdecl pdecl (isdecl : declared_projection Σ.1 p mdecl idecl cdecl pdecl)
           args,
      on_global_env cumulSpecE0 pgi_cl_Pj Σ.1 -> pgi_cl_PΓ Σ Γ ->
      Σ ;;; Γ |-E c : mkApps (tInd p.(proj_ind) u) args ->
      pgi_cl_P Σ Γ c (mkApps (tInd p.(proj_ind) u) args) ->
      #|args| = ind_npars mdecl ->
      pgi_cl_P Σ Γ (tProj p c) (subst0 (c :: List.rev args) (subst_instance u pdecl.(proj_type))).
  Proof.
    intros Σ wfΣ Γ wfΓ p c u mdecl idecl cdecl pdecl isdecl args _ _ _ hc _.
    have hc' : is_true (closedn #|Γ| c) := hc.
    exact hc'.
  Qed.

  Lemma pgi_cl_fix :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ)
           (mfix : list (def term)) (n : nat) decl,
      let types := fix_context mfix in
      fix_guard Σ Γ mfix ->
      nth_error mfix n = Some decl ->
      pgi_cl_PΓ Σ (Γ ,,, types) ->
      All (on_def_type (lift_typing typingE Σ) Γ) mfix ->
      All (on_def_type (pgi_cl_Pj Σ) Γ) mfix ->
      All (on_def_body (lift_typing typingE Σ) types Γ) mfix ->
      All (on_def_body (pgi_cl_Pj Σ) types Γ) mfix ->
      wf_fixpointE Σ Γ mfix ->
      pgi_cl_P Σ Γ (tFix mfix n) decl.(dtype).
  Proof.
    intros Σ wfΣ Γ wfΓ mfix n decl types _ _ _ _ htys _ hbodies _.
    change (is_true (forallb (test_def (closedn #|Γ|) (closedn (#|mfix| + #|Γ|))) mfix)).
    apply All_forallb. eapply All_impl; [exact (All_mix htys hbodies)|]. intros d [hty hbody].
    have hty' : is_true (closedn #|Γ| (dtype d)) := hty.
    have hbody' : is_true (closedn #|Γ ,,, fix_context mfix| (dbody d) &&
                           closedn #|Γ ,,, fix_context mfix| (lift0 #|fix_context mfix| (dtype d))) := hbody.
    move/andP: hbody' => [hb _]. rewrite app_context_length fix_context_length in hb.
    change (is_true (closedn #|Γ| (dtype d) && closedn (#|mfix| + #|Γ|) (dbody d))).
    apply/andP; split; [exact hty'|exact hb].
  Qed.

  Lemma pgi_cl_cofix :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ)
           (mfix : list (def term)) (n : nat) decl,
      let types := fix_context mfix in
      cofix_guard Σ Γ mfix ->
      nth_error mfix n = Some decl ->
      pgi_cl_PΓ Σ (Γ ,,, types) ->
      All (on_def_type (lift_typing typingE Σ) Γ) mfix ->
      All (on_def_type (pgi_cl_Pj Σ) Γ) mfix ->
      All (on_def_body (lift_typing typingE Σ) types Γ) mfix ->
      All (on_def_body (pgi_cl_Pj Σ) types Γ) mfix ->
      wf_cofixpointE Σ Γ mfix ->
      pgi_cl_P Σ Γ (tCoFix mfix n) decl.(dtype).
  Proof.
    intros Σ wfΣ Γ wfΓ mfix n decl types _ _ _ _ htys _ hbodies _.
    change (is_true (forallb (test_def (closedn #|Γ|) (closedn (#|mfix| + #|Γ|))) mfix)).
    apply All_forallb. eapply All_impl; [exact (All_mix htys hbodies)|]. intros d [hty hbody].
    have hty' : is_true (closedn #|Γ| (dtype d)) := hty.
    have hbody' : is_true (closedn #|Γ ,,, fix_context mfix| (dbody d) &&
                           closedn #|Γ ,,, fix_context mfix| (lift0 #|fix_context mfix| (dtype d))) := hbody.
    move/andP: hbody' => [hb _]. rewrite app_context_length fix_context_length in hb.
    change (is_true (closedn #|Γ| (dtype d) && closedn (#|mfix| + #|Γ|) (dbody d))).
    apply/andP; split; [exact hty'|exact hb].
  Qed.

  Lemma pgi_cl_prim :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (p : prim_val)
           prim_ty cdecl,
      pgi_cl_PΓ Σ Γ ->
      primitive_constant Σ (prim_val_tag p) = Some prim_ty ->
      declared_constant Σ prim_ty cdecl ->
      primitive_invariants (prim_val_tag p) cdecl ->
      primitive_typing_hyps (typingE Σ) Σ Γ p ->
      primitive_typing_hyps (pgi_cl_P Σ) Σ Γ p ->
      pgi_cl_P Σ Γ (tPrim p) (prim_type p prim_ty).
  Proof.
    intros Σ wfΣ Γ wfΓ p prim_ty cdecl _ _ _ _ _ hp.
    destruct hp as [i|f|s|a _ hty hdef hvalue]; try exact (@eq_refl bool true).
    change (is_true (forallb (closedn #|Γ|) (array_value a) && closedn #|Γ| (array_default a) &&
                     closedn #|Γ| (array_type a))).
    apply/andP; split; [apply/andP; split|].
    - exact (All_forallb (closedn #|Γ|) _ hvalue).
    - exact hdef.
    - exact hty.
  Qed.

  Lemma pgi_cl_cumul :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (t A B : term) s,
      pgi_cl_PΓ Σ Γ ->
      Σ ;;; Γ |-E t : A ->
      pgi_cl_P Σ Γ t A ->
      Σ ;;; Γ |-E B : tSort s ->
      pgi_cl_P Σ Γ B (tSort s) ->
      cumulSpecE Σ Γ A B ->
      pgi_cl_P Σ Γ t B.
  Proof.
    intros Σ wfΣ Γ wfΓ t A B s _ _ ht _ _ _.
    have ht' : is_true (closedn #|Γ| t) := ht.
    exact ht'.
  Qed.

  (** *** The two instances *)

  (** [typing_ind_envE] with the scoping predicates [pgi_cl_P], [pgi_cl_Pj], [pgi_cl_PΓ], every
      case proved in general; each of the three predicates is false on some input
      ([pgi_cl_nondeg]).
      INSTANCE NONDEGEN PCUICProgressEtaInstances.pgi_cl_nondeg
      TARGET PCUICProgressEta.typing_ind_envE *)
  Lemma typing_ind_envE_closedn_inst : @env_propE cf pgi_cl_P pgi_cl_Pj pgi_cl_PΓ.
  Proof.
    exact (@typing_ind_envE cf pgi_cl_P pgi_cl_Pj pgi_cl_PΓ pgi_cl_judgment pgi_cl_context
             pgi_cl_rel pgi_cl_sort pgi_cl_prod pgi_cl_lambda pgi_cl_letin pgi_cl_app pgi_cl_const
             pgi_cl_ind pgi_cl_construct pgi_cl_case pgi_cl_proj pgi_cl_fix pgi_cl_cofix pgi_cl_prim
             pgi_cl_cumul).
  Qed.

  (** [typing_ind_env_app_sizeE] with the same predicates and cases; its application case passes
      the sized induction hypothesis too, which [pgi_cl_app] does not use. Each of the three
      predicates is false on some input ([pgi_cl_nondeg]).
      INSTANCE NONDEGEN PCUICProgressEtaInstances.pgi_cl_nondeg
      TARGET PCUICProgressEta.typing_ind_env_app_sizeE *)
  Lemma typing_ind_env_app_sizeE_closedn_inst : @env_propE cf pgi_cl_P pgi_cl_Pj pgi_cl_PΓ.
  Proof.
    exact (@typing_ind_env_app_sizeE cf pgi_cl_P pgi_cl_Pj pgi_cl_PΓ pgi_cl_judgment pgi_cl_context
             pgi_cl_rel pgi_cl_sort pgi_cl_prod pgi_cl_lambda pgi_cl_letin
             (fun Σ wfΣ Γ wfΓ t T B L s hΓ hT pT Ht pt _ hsp =>
                pgi_cl_app Σ wfΣ Γ wfΓ t T B L s hΓ hT pT Ht pt hsp)
             pgi_cl_const pgi_cl_ind pgi_cl_construct pgi_cl_case pgi_cl_proj pgi_cl_fix
             pgi_cl_cofix pgi_cl_prim pgi_cl_cumul).
  Qed.

End ClosednInduction.

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

(** [∀X:Prop. Type₀] and [∀X:Prop. Type₁]: the product [Prop → Prop] ([iv_PP]) at two larger
    codomain sorts. *)
Definition pgi_PT0 : term := tProd si_na si_P (tSort Sort.type0).
Definition pgi_PT1 : term := tProd si_na si_P (tSort Sort.type1).

Lemma pgi_T0_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E tSort Sort.type0 : tSort (Sort.super Sort.type0).
Proof. intros h. exact (typeE_Sort _ _ Sort.type0 h (PCUICWfUniverses.wf_sort_type0 _)). Qed.

Lemma pgi_T1_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E tSort Sort.type1 : tSort (Sort.super Sort.type1).
Proof. intros h. exact (typeE_Sort _ _ Sort.type1 h (PCUICWfUniverses.wf_sort_type1 _)). Qed.

Lemma pgi_T1_isType : isTypeE si_Σ [] (tSort Sort.type1).
Proof. exact (has_sort_isTypeE _ (pgi_T1_typed [] localenv_nil)). Qed.

Lemma pgi_PT0_typed :
  si_Σ ;;; [] |-E pgi_PT0 : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super Sort.type0)).
Proof.
  unfold pgi_PT0. apply typeE_Prod.
  - exact (iv_vass_s si_Σ [] si_na si_P _ (iv_P_typed si_Σ [] localenv_nil) eq_refl).
  - exact (pgi_T0_typed _ (iv_wf_P si_Σ [] localenv_nil)).
Qed.

Lemma pgi_PT1_typed :
  si_Σ ;;; [] |-E pgi_PT1 : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super Sort.type1)).
Proof.
  unfold pgi_PT1. apply typeE_Prod.
  - exact (iv_vass_s si_Σ [] si_na si_P _ (iv_P_typed si_Σ [] localenv_nil) eq_refl).
  - exact (pgi_T1_typed _ (iv_wf_P si_Σ [] localenv_nil)).
Qed.

(** [Prop → Prop ≤ ∀X:Prop. Type₀]: [Prop ≤ Type₀] in the codomain ([prop_sub_type]). *)
Lemma pgi_PP_PT0 : ws_cumul_pbE Cumul si_Σ [] iv_PP pgi_PT0.
Proof.
  unfold iv_PP, pgi_PT0. apply ws_cumul_pbE_Prod_r.
  apply ws_cumul_pbE_Sort; [reflexivity|exact eq_refl].
Qed.

(** [∀X:Prop. Type₀ ≤ ∀X:Prop. Type₁]: [Type₀ ≤ Type₁] in the codomain. *)
Lemma pgi_PT0_PT1 : ws_cumul_pbE Cumul si_Σ [] pgi_PT0 pgi_PT1.
Proof.
  unfold pgi_PT0, pgi_PT1. apply ws_cumul_pbE_Prod_r.
  apply ws_cumul_pbE_Sort; [reflexivity|].
  hnf. intros v _.
  first [cbn; lia | vm_compute; intros hh; discriminate hh | vm_compute; congruence].
Qed.

(** A spine of [∀X:Prop. Type₀] applied to [∀P:Prop. P], with the trivial predicate; its head step
    is [∀X:Prop. Type₀ ≤ ∀X:Prop. Type₁] ([pgi_PT0_PT1]). *)
Lemma pgi_sp_T0 : typing_spine_predE si_Σ [] (fun _ _ _ => True) pgi_PT0 [iv_False] (tSort Sort.type1).
Proof.
  refine (type_spine_pred_consE _ _ _ pgi_PT0 iv_False [] si_na si_P (tSort Sort.type1) (tSort Sort.type1) _
            (has_sort_isTypeE _ pgi_PT0_typed) pgi_PT1_typed I pgi_PT0_PT1
            (iv_False_typed si_Σ [] localenv_nil) I _).
  econstructor; [exact pgi_T1_isType|exact pgi_T1_isType|].
  exact (isType_ws_cumul_pbE_refl (Σ := si_Σ) [] _ pgi_T1_isType).
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
    ([pgi_match_let]). Its scrutinee is a let-in, not a constructor application; it evaluates to
    [c (∀P. P)] ([pgi_disc_let_eval]), and so does the match ([pgi_match_let_eval]).
    [pgi_match_let] is [pgi_match_let_open] at [x := ∀P. P]: the [match] [iv_match] of
    [PCUICInversionEtaInstances], in [iv_Γ1 = [x : Prop]], with the scrutinee [let y := x in c y]
    in place of [c x]. That scrutinee has the let-in type [let y := x in I y] ([pgi_disc_let_ty],
    [pgi_disc_let_letin_typed]) and the type [I x] ([pgi_disc_let_typed]); the let-in type is
    chosen for T8 [Ind_r] ([PCUICPrincipalityEtaInstances.principal_typeE_case_inst]). *)
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

(** The scrutinee of [pgi_match_let], [let y := ∀P. P in c y], is not a constructor application:
    [isConstruct_app] is false on it, and it is no [mkApps (tConstruct ind c u) args]. *)
Lemma eval_tCaseE_inst_nondeg :
  isConstruct_app (pgi_disc_let {0 := iv_False}) = false /\
  (forall ind c u args, pgi_disc_let {0 := iv_False} <> mkApps (tConstruct ind c u) args).
Proof.
  split; [reflexivity|].
  intros ind c u args.
  induction args as [|a args _] using rev_ind; [cbn; discriminate|].
  rewrite mkApps_app. cbn. discriminate.
Qed.

(** [eval_tCaseE] on [pgi_match_let]. Its scrutinee is no constructor application
    ([eval_tCaseE_inst_nondeg]), while the match the returned reduction ends in has the scrutinee
    [mkApps (tConstruct …) args]: the reduction is not reflexive.
    INSTANCE NONDEGEN PCUICProgressEtaInstances.eval_tCaseE_inst_nondeg *)
Definition eval_tCaseE_inst :=
  eval_tCaseE (Σ := si_Σ) _ _ (pgi_disc_let {0 := iv_False}) _ _ _ si_wfE pgi_match_let_typed
    pgi_match_let_eval.

(** The three products [Prop → Prop] ([iv_PP]), [∀X:Prop. Type₀] and [∀X:Prop. Type₁] are pairwise
    distinct, and so are their codomain sorts. The premise [pgi_PP_PT0] steps from the first to the
    second ([Prop ≤ Type₀]), the input spine's head step [pgi_PT0_PT1] from the second to the third
    ([Type₀ ≤ Type₁]). No term involved is a β-redex. *)
Lemma typing_spine_pred_strengthenE_inst_nondeg :
  [× iv_PP <> pgi_PT0, pgi_PT0 <> pgi_PT1, iv_PP <> pgi_PT1,
     sProp <> Sort.type0, Sort.type0 <> Sort.type1 & sProp <> Sort.type1].
Proof. split; intros h; vm_compute in h; discriminate h. Qed.

(** INSTANCE NONDEGEN PCUICProgressEtaInstances.typing_spine_pred_strengthenE_inst_nondeg *)
Definition typing_spine_pred_strengthenE_inst :=
  typing_spine_pred_strengthenE (Σ := si_Σ) (wfΣ := si_wfE) pgi_sp_T0 (has_sort_isTypeE _ pgi_PT0_typed)
    iv_PP (has_sort_isTypeE _ (iv_PP_typed si_Σ [] localenv_nil)) pgi_PP_PT0.

Lemma pgi_False_value : value si_Σ iv_False.
Proof. apply value_atomic, atomic_atom. reflexivity. Qed.

Lemma pgi_xx_lam_value : value si_Σ (mkApps sri_xx_lam []).
Proof. apply value_atomic, atomic_atom. reflexivity. Qed.

(** [(λx:Prop. x) (∀P. P)]: its head [iv_id] is an abstraction and its spine [[∀P. P]] is not
    empty; it is not a value; it takes a WCBV step to [∀P. P]. *)
Lemma pgi_beta_redex_nondeg :
  [× isLambda iv_id, [iv_False] <> [],
     (PCUICWcbvEval.value si_Σ (tApp iv_id iv_False) -> False)
   & si_Σ ⊢ tApp iv_id iv_False ⇝ᵥ iv_False].
Proof.
  split.
  - reflexivity.
  - discriminate.
  - intros hv.
    destruct (PCUICWcbvEval.value_mkApps_inv si_Σ iv_id [iv_False] eq_refl hv) as [[e _]|[_ hh _]].
    + discriminate e.
    + have h := PCUICWcbvEval.value_head_spec si_Σ _ _ hh. cbn in h. discriminate h.
  - apply PCUICWcbvEval.wcbv_red_beta. exact pgi_False_value.
Qed.

(** INSTANCE NONDEGEN PCUICProgressEtaInstances.pgi_beta_redex_nondeg
    TARGET PCUICProgressEta.inversion_mkAppsE *)
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

(** [declared_constructor_ind_declE] on the declared constructor [c] of [I] ([si_declared_constructor]).
    INSTANCE IMPOSSIBLE: the target's proof is one destruct of its declared_constructor premise and nth_error_Some_length on the nth_error inside it, so in every environment the bound inductive_ind ind < #|ind_bodies mdecl| of every instance is read off that instance's own premise *)
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

(** [(λx:Prop. x → x) (∀P. P)] ([sri_xx_redex], the application of [sri_xx_lam] to [∀P. P]): the
    body of its head uses the variable inside a product. It is not a value, and it takes a WCBV step
    to [(∀P. P) → ∀P. P] ([sri_xx_reduct]), which is neither the argument [∀P. P] nor the redex. So
    the value disjunct of the sum that [progressE], [progress_env_propE], [typing_value_head_nappE]
    and [typing_value_headE] return on it is empty, and the step they return does not give back a
    piece of the input. *)
Lemma progressE_inst_nondeg :
  [× sri_x_to_x <> tRel 0, mkApps sri_xx_lam ([] ++ [iv_False]) = sri_xx_redex,
     (PCUICWcbvEval.value si_Σ sri_xx_redex -> False),
     si_Σ ⊢ sri_xx_redex ⇝ᵥ sri_xx_reduct, sri_xx_reduct <> iv_False
   & sri_xx_reduct <> sri_xx_redex].
Proof.
  split.
  - intros h; vm_compute in h; discriminate h.
  - reflexivity.
  - intros hv.
    destruct (PCUICWcbvEval.value_mkApps_inv si_Σ sri_xx_lam [iv_False] eq_refl hv) as [[e _]|[_ hh _]].
    + discriminate e.
    + have h := PCUICWcbvEval.value_head_spec si_Σ _ _ hh. try unfold sri_xx_lam in h. cbn in h. discriminate h.
  - exact (PCUICWcbvEval.wcbv_red_beta _ si_na si_P sri_x_to_x iv_False pgi_False_value).
  - intros h; vm_compute in h; discriminate h.
  - intros h; vm_compute in h; discriminate h.
Qed.

(** INSTANCE NONDEGEN PCUICProgressEtaInstances.progressE_inst_nondeg *)
Definition typing_value_head_nappE_inst :=
  typing_value_head_nappE (Σ := si_Σ) (wfΣ := si_wfE) sri_xx_lam [] iv_False si_P eq_refl
    (sri_xx_redex_typed [] localenv_nil) pgi_False_value eq_refl pgi_xx_lam_value.

(** INSTANCE NONDEGEN PCUICProgressEtaInstances.progressE_inst_nondeg *)
Definition typing_value_headE_inst :=
  typing_value_headE (Σ := si_Σ) (wfΣ := si_wfE) sri_xx_lam [] iv_False si_P
    (sri_xx_redex_typed [] localenv_nil) pgi_False_value eq_refl pgi_xx_lam_value.

(** INSTANCE NONDEGEN PCUICProgressEtaInstances.progressE_inst_nondeg *)
Definition progress_env_propE_inst :=
  env_propE_typing progress_env_propE si_Σ si_wfE [] sri_xx_redex si_P
    (sri_xx_redex_typed [] localenv_nil) cli_axiom_free eq_refl (sri_xx_redex_typed [] localenv_nil).

(** INSTANCE NONDEGEN PCUICProgressEtaInstances.progressE_inst_nondeg *)
Definition progressE_inst :=
  progressE si_Σ sri_xx_redex si_P cli_axiom_free si_wfE (sri_xx_redex_typed [] localenv_nil).

(** The input of [whnf_progressE_inst], [c (∀P. P)], is an application: its head [c] is not the
    term itself. *)
Lemma whnf_progressE_inst_nondeg : PCUICAstUtils.head sri_cF <> sri_cF.
Proof. discriminate. Qed.

(** [whnf_progressE] on the constructor application [c (∀P. P)] ([sri_cF]), typed at
    [I (∀P. P)] ([sri_cF_typed]) and [red1]-normal ([pgi_cF_normal]), the premise the lemma turns
    into [whnf]. The term is an application: its head [c] is not the term itself
    ([whnf_progressE_inst_nondeg]).
    INSTANCE NONDEGEN PCUICProgressEtaInstances.whnf_progressE_inst_nondeg *)
Definition whnf_progressE_inst :=
  whnf_progressE si_Σ sri_cF iv_IF cli_axiom_free si_wfE sri_cF_typed
    (fun h => let (t', r) := h in pgi_cF_normal _ _ _ r).

(** The head of [c (∀P. P)] is read off an application: it is [c], not the term itself;
    [construct_cofix_discr] is false on the term and true on its head. *)
Lemma classificationE_inst_nondeg :
  [× PCUICAstUtils.head sri_cF <> sri_cF,
     PCUICViews.construct_cofix_discr sri_cF = false
   & PCUICViews.construct_cofix_discr (PCUICAstUtils.head sri_cF) = true].
Proof. split; [discriminate|vm_compute; reflexivity|vm_compute; reflexivity]. Qed.

(** [classificationE], at its statement's flags [config.extraction_checker_flags] (as base's):
    the constructor application [c (∀P. P)], [red1]-normal ([pgi_cF_normal]), typed at
    [I (∀P. P)] over [typingE] ([pgx_cF_typedE]) in [si_Σ], which is proved [wfE] at those flags
    ([pgx_wfE], section [ClassificationFlags]). Its conclusion [construct_cofix_discr (head t)]
    is about the head: [construct_cofix_discr] is false on [c (∀P. P)] itself and true on its
    head [c] ([classificationE_inst_nondeg]).
    INSTANCE NONDEGEN PCUICProgressEtaInstances.classificationE_inst_nondeg *)
Definition classificationE_inst :=
  classificationE si_Σ sri_cF si_ind [] [iv_False] cli_axiom_free pgx_wfE
    (fun h => let (t', r) := h in pgi_cF_normal _ _ _ r) pgx_cF_typedE.

End ProgressEtaInstances.
