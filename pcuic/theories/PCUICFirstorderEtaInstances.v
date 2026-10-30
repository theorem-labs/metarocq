(* Distributed under the terms of the MIT license. *)

(* NONDEGEN tags: an INSTANCE NONDEGEN tag is a reader judgment backed by a compiled nontriviality
   lemma; the measured reader miss rate is recorded in lanes/eta/meta/reader-catch-rate.tsv. *)

(** * Satisfying instances of the lemmas of [PCUICFirstorderEta] (row T6)

  **The environment.** [fo_env] declares [Inductive N : Type@{Set+1} := z : N | s : N -> N]
  ([fo_mdecl]). It is first order ([fo_firstorder]): base's [firstorder_oneind] wants a sort
  that is not a single level, so [N] lives in [Sort.type1], not in [Set]. [fo_wf] proves it
  well-formed for base typing, [fo_wfE] for the η typing ([wf_incl_E]). [fo_env2] declares the
  same body a second time under [fo_kn2] on top of [fo_env], a strict extension, for the two
  extension lemmas. The declaration lemmas are stated for any checking environment [Σ0], so
  [fo_env2]'s second declaration reuses them.

  **No forecast class.** The main theorem, [firstorder_argsE] and
  [instantiated_typing_spine_firstorder_spineE] took T1's [SRForecastCopy18] until copy 18b
  landed (frac/eta 3e6b422d); the class is deleted, as in [PCUICClassificationEtaInstances].

  **Non-degeneracy.** Each instance carries its tag: NONDEGEN with the lemma that states why it
  is more than a trivial case, or IMPOSSIBLE with the property of the statement.
  - [firstorder_value_specE_inst]: the value [s z] (an application with an argument,
    [fo_sz_nondeg]) of type [N]; the theorem gives it as a first-order value.
    [firstorder_argsE_inst] and [typing_spine_arity_spineE_inst] run on the spine of [s]'s type
    ([fo_s_spine]: [Π _ : N. N] applied to [z]); [instantiated_typing_spine_firstorder_spineE_inst]
    on its arity spine.
  - [firstorder_value_indsE_inst]: the induction principle on the value [s z], built directly
    ([fo_sz_value]), with the predicate "is closed": the step it is given uses the induction
    hypothesis on the constructor's arguments ([fo_closed_step]), and [s z] has an argument.
  - [firstorder_spine_letE_inst]: the first-order spine of [Π _ : N. N] on [[z]]
    ([instantiated_typing_spine_firstorder_spineE_inst]) moved to the type
    [let X := N : Type1 in X → X]; the substitution [X := N] into the body [X → X] gives
    [N → N], neither the substituted [N] nor the body, and the let-type ζ-reduces to it in one
    step ([fo_letNN_nondeg]).
  - [isType_context_conversionE_inst]: the type [X], a variable, in the contexts
    [X : let _ := N : Type1 in Type1] and [X : Type1], which differ; the first declared type
    ζ-reduces to the second in one step ([fo_ctx_nondeg]).
  - [plookup_env_extendsE_inst], [firstorder_mutind_extE_inst]: [fo_env] ⊂ [fo_env2], strict.
  - [firstorder_ind_propositionalE_inst]: [N] is first order, with a constructor that takes an
    argument ([s]), and not propositional.

  **Rows without a non-reflexive instance** are tagged IMPOSSIBLE at their declaration, with the
  reason: [firstorder_value_alphaE_inst], and [fo_invert_cumul_Sort_IndE_inst] for
  [PCUICEtaA6More.invert_cumul_it_mkProd_or_LetIn_Sort_IndE] (used by the main theorem in place
  of a copy; also recorded in [PCUICEtaA6Instances]). *)

From Stdlib Require Import ssreflect ssrbool List Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICReduction
     PCUICTyping PCUICArityRed
     PCUICEquality PCUICAlpha PCUICWellScopedCumulativity PCUICFirstorder PCUICWfUniverses
     PCUICTypingEta PCUICTypingEtaNotions PCUICClosedBodies PCUICClosedTypEta
     PCUICCumulativitySpecEtaClosureInstances
     PCUICInversionEtaInstances PCUICWellScopedCumulativityEta PCUICContextConversionEta
     PCUICWsCumulEtaCtxTyp PCUICAritiesEta PCUICSpineEta PCUICValidityEta PCUICSREta
     PCUICClassificationEta PCUICFirstorderEta.
From MetaRocq.PCUIC Require PCUICWcbvEval PCUICEtaA6More.
From MetaRocq.PCUIC.Syntax Require PCUICClosed.
From Equations.Type Require Import Relation.

#[local] Existing Instance default_checker_flags.

(** The declarations of this file that are neither instances nor nondegeneracy lemmas: the
    environment [fo_Σ] and its typing derivations.
    WITNESSES: fo_* *)

(** ** The environment *)

Definition fo_kn : kername := (MPfile ["FoInst"], "N").
Definition fo_kn2 : kername := (MPfile ["FoInst"], "N2").
Definition fo_ind : inductive := {| inductive_mind := fo_kn; inductive_ind := 0 |}.
Definition fo_na : aname := mkBindAnn nAnon Relevant.
Definition fo_T : term := tSort Sort.type1.
Definition fo_N : term := tInd fo_ind [].

Definition fo_cz : constructor_body :=
  {| cstr_name := "z"; cstr_args := []; cstr_indices := []; cstr_type := tRel 0; cstr_arity := 0 |}.
Definition fo_cs : constructor_body :=
  {| cstr_name := "s"; cstr_args := [vass fo_na (tRel 0)]; cstr_indices := [];
     cstr_type := tProd fo_na (tRel 0) (tRel 1); cstr_arity := 1 |}.

Definition fo_idecl : one_inductive_body :=
  {| ind_name := "N"; ind_indices := []; ind_sort := Sort.type1; ind_type := fo_T;
     ind_kelim := IntoAny; ind_ctors := [fo_cz; fo_cs]; ind_projs := []; ind_relevance := Relevant |}.

Definition fo_mdecl : mutual_inductive_body :=
  {| ind_finite := Finite; ind_npars := 0; ind_params := []; ind_bodies := [fo_idecl];
     ind_universes := Monomorphic_ctx; ind_variance := None |}.

Definition fo_env : global_env :=
  {| universes := ContextSet.empty; declarations := [(fo_kn, InductiveDecl fo_mdecl)];
     retroknowledge := Retroknowledge.empty |}.
Definition fo_Σ : global_env_ext := (fo_env, Monomorphic_ctx).

Definition fo_env2 : global_env :=
  {| universes := ContextSet.empty;
     declarations := [(fo_kn2, InductiveDecl fo_mdecl); (fo_kn, InductiveDecl fo_mdecl)];
     retroknowledge := Retroknowledge.empty |}.
Definition fo_Σ2 : global_env_ext := (fo_env2, Monomorphic_ctx).

(** ** The declaration is well-formed, in any checking environment *)

Section Decl.
  Context (Σ0 : global_env_ext).

  Lemma fo_vass (Γ : context) (na : aname) A s :
    Σ0 ;;; Γ |- A : tSort s -> isSortRel s na.(binder_relevance) ->
    lift_typing typing Σ0 Γ (j_vass na A).
  Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [exact I|exact r]. Qed.

  Lemma fo_vass_s (Γ : context) (na : aname) A s :
    Σ0 ;;; Γ |- A : tSort s -> isSortRel s na.(binder_relevance) ->
    lift_typing typing Σ0 Γ (j_vass_s na A s).
  Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [reflexivity|exact r]. Qed.

  Lemma fo_T_typed (Γ : context) : wf_local Σ0 Γ -> Σ0 ;;; Γ |- fo_T : tSort (Sort.super Sort.type1).
  Proof. intros h. apply type_Sort; [exact h|apply wf_sort_type1]. Qed.

  Definition fo_Γi : context := arities_context [fo_idecl].

  Lemma fo_wf_Γi : wf_local Σ0 fo_Γi.
  Proof.
    apply localenv_cons_abs; [constructor|].
    exact (fo_vass _ (mkBindAnn (nNamed "N") rel_of_Type) _ _ (fo_T_typed [] localenv_nil) eq_refl).
  Qed.

  (** [N] in the arities context, and under one more assumption [x : N]. *)
  Lemma fo_rel0_typed : Σ0 ;;; fo_Γi |- tRel 0 : tSort Sort.type1.
  Proof. exact (type_Rel _ _ 0 (vass (mkBindAnn (nNamed "N") rel_of_Type) fo_T) fo_wf_Γi eq_refl). Qed.

  Lemma fo_wf_Γi_x : wf_local Σ0 (fo_Γi ,, vass fo_na (tRel 0)).
  Proof. apply localenv_cons_abs; [exact fo_wf_Γi|exact (fo_vass _ fo_na _ _ fo_rel0_typed eq_refl)]. Qed.

  Lemma fo_cs_type_typed :
    Σ0 ;;; fo_Γi |- tProd fo_na (tRel 0) (tRel 1) : tSort (Sort.sort_of_product Sort.type1 Sort.type1).
  Proof.
    apply type_Prod.
    - exact (fo_vass_s _ fo_na _ _ fo_rel0_typed eq_refl).
    - exact (type_Rel _ _ 1 (vass (mkBindAnn (nNamed "N") rel_of_Type) fo_T) fo_wf_Γi_x eq_refl).
  Qed.

  Lemma fo_mdecl_at : mdecl_at_i fo_mdecl fo_idecl [] 0.
  Proof. unfold mdecl_at_i, fo_mdecl; cbn. split; [lia|split; [lia|reflexivity]]. Qed.

  Lemma fo_on_cz : on_constructor cumulSpec0 (lift_typing typing) Σ0 fo_mdecl 0 fo_idecl [] fo_cz [].
  Proof.
    unshelve econstructor.
    - reflexivity.
    - reflexivity.
    - exact (fo_vass _ (mkBindAnn nAnon Relevant) _ _ fo_rel0_typed eq_refl).
    - exact tt.
    - constructor.
    - cbn. exact (pos_concl _ _ _ [] [] All_nil).
    - intros v e. discriminate e.
    - destruct lets_in_constructor_types; [exact I|reflexivity].
  Qed.

  Lemma fo_on_cs :
    on_constructor cumulSpec0 (lift_typing typing) Σ0 fo_mdecl 0 fo_idecl [] fo_cs [Sort.type1].
  Proof.
    unshelve econstructor.
    - reflexivity.
    - reflexivity.
    - exact (fo_vass _ (mkBindAnn nAnon Relevant) _ _ fo_cs_type_typed eq_refl).
    - split; [exact tt|exact (fo_vass_s _ fo_na _ _ fo_rel0_typed eq_refl)].
    - constructor.
    - cbn. eapply pos_ass.
      + exact (pos_arg_concl _ fo_mdecl _ _ [] 0 fo_idecl eq_refl All_nil fo_mdecl_at).
      + exact (pos_concl _ _ _ [vass fo_na (tRel 0)] [] All_nil).
    - intros v e. discriminate e.
    - destruct lets_in_constructor_types; [exact I|reflexivity].
  Qed.

  Lemma fo_on_ind_body : on_ind_body cumulSpec0 (lift_typing typing) Σ0 fo_kn fo_mdecl 0 fo_idecl.
  Proof.
    unshelve econstructor.
    - exact [[]; [Sort.type1]].
    - exists fo_T. split; [reflexivity|]. apply arity_red_sort. apply whd_stop. reflexivity.
    - exact (fo_vass _ (mkBindAnn nAnon rel_of_Type) _ _ (fo_T_typed [] localenv_nil) eq_refl).
    - exact (fo_vass _ (mkBindAnn nAnon rel_of_Type) _ _ (fo_T_typed [] localenv_nil) eq_refl).
    - constructor; [exact fo_on_cz|constructor; [exact fo_on_cs|constructor]].
    - exact I.
    - cbn. split; [|exact I].
      constructor; [constructor|constructor; [constructor; [reflexivity|constructor]|constructor]].
    - reflexivity.
    - exact I.
  Qed.

  Lemma fo_on_inductive : on_inductive cumulSpec0 (lift_typing typing) Σ0 fo_kn fo_mdecl.
  Proof.
    constructor.
    - constructor; [exact fo_on_ind_body|constructor].
    - exact localenv_nil.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma fo_on_inductive2 : on_inductive cumulSpec0 (lift_typing typing) Σ0 fo_kn2 fo_mdecl.
  Proof.
    constructor.
    - constructor; [|constructor].
      destruct fo_on_ind_body. unshelve econstructor; eassumption.
    - exact localenv_nil.
    - reflexivity.
    - reflexivity.
  Qed.
End Decl.

Lemma fo_univs_wf : on_global_univs (universes fo_env).
Proof.
  split; [|split].
  - intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
  - intros x Hx.
    change (LevelSet.In x (LevelSet.union (ContextSet.levels ContextSet.empty)
                                          (LevelSet.singleton Level.lzero))) in Hx.
    apply LevelSet.union_spec in Hx as [Hx|Hx].
    + exfalso. eapply LevelSet.empty_spec. exact Hx.
    + apply LevelSet.singleton_spec in Hx. hnf in Hx. subst x. reflexivity.
  - exists si_val. intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
Qed.

Lemma fo_wf : wf fo_env.
Proof.
  split; [exact fo_univs_wf|].
  split.
  { constructor; cbn; [constructor|intros c []|repeat split; intros c h; discriminate h
                      |intros i h; discriminate h]. }
  apply globenv_decl; [constructor|].
  constructor.
  - constructor.
  - exact si_on_udecl.
  - exact (fo_on_inductive _).
  - cbn. intros i h; discriminate h.
Qed.

Lemma fo_wf2 : wf fo_env2.
Proof.
  split; [exact fo_univs_wf|].
  split.
  { constructor; cbn; [constructor|intros c []|repeat split; intros c h; discriminate h
                      |intros i h; discriminate h]. }
  apply globenv_decl.
  - apply globenv_decl; [constructor|].
    constructor.
    + constructor.
    + exact si_on_udecl.
    + exact (fo_on_inductive _).
    + cbn. intros i h; discriminate h.
  - constructor.
    + constructor; [|constructor]. cbn. intros e. inversion e.
    + exact si_on_udecl.
    + exact (fo_on_inductive2 _).
    + cbn. intros i h; discriminate h.
Qed.

Definition fo_wfE : wfE fo_env := wf_incl_E fo_wf.
Definition fo_wfE2 : wfE fo_env2 := wf_incl_E fo_wf2.

Lemma fo_declared : declared_inductive fo_Σ fo_ind fo_mdecl fo_idecl.
Proof. split; [left; reflexivity|reflexivity]. Qed.

Lemma fo_declared_cz : declared_constructor fo_Σ (fo_ind, 0) fo_mdecl fo_idecl fo_cz.
Proof. split; [exact fo_declared|reflexivity]. Qed.

Lemma fo_declared_cs : declared_constructor fo_Σ (fo_ind, 1) fo_mdecl fo_idecl fo_cs.
Proof. split; [exact fo_declared|reflexivity]. Qed.

Lemma fo_firstorder : firstorder_ind fo_Σ (firstorder_env fo_Σ) fo_ind.
Proof. reflexivity. Qed.

Lemma fo_not_prop : ~~ isPropositional fo_Σ fo_ind.
Proof. reflexivity. Qed.

(** ** Typing in [fo_Σ] over [typingE], without any class *)

Lemma fo_T_typedE (Γ : context) : wf_localE fo_Σ Γ -> fo_Σ ;;; Γ |-E fo_T : tSort (Sort.super Sort.type1).
Proof. intros h. apply typeE_Sort; [exact h|apply wf_sort_type1]. Qed.

Lemma fo_N_typed (Γ : context) : wf_localE fo_Σ Γ -> fo_Σ ;;; Γ |-E fo_N : fo_T.
Proof. intros h. exact (typeE_Ind _ _ fo_ind [] fo_mdecl fo_idecl h fo_declared eq_refl). Qed.

Lemma fo_z_typed (Γ : context) : wf_localE fo_Σ Γ -> fo_Σ ;;; Γ |-E tConstruct fo_ind 0 [] : fo_N.
Proof. intros h. exact (typeE_Construct _ _ fo_ind 0 [] fo_mdecl fo_idecl fo_cz h fo_declared_cz eq_refl). Qed.

Lemma fo_s_typed (Γ : context) : wf_localE fo_Σ Γ ->
  fo_Σ ;;; Γ |-E tConstruct fo_ind 1 [] : tProd fo_na fo_N fo_N.
Proof. intros h. exact (typeE_Construct _ _ fo_ind 1 [] fo_mdecl fo_idecl fo_cs h fo_declared_cs eq_refl). Qed.

Lemma fo_NN_typed (Γ : context) : wf_localE fo_Σ Γ ->
  fo_Σ ;;; Γ |-E tProd fo_na fo_N fo_N : tSort (Sort.sort_of_product Sort.type1 Sort.type1).
Proof.
  intros h. apply typeE_Prod.
  - exact (iv_vass_s fo_Σ Γ fo_na fo_N Sort.type1 (fo_N_typed Γ h) eq_refl).
  - exact (fo_N_typed _ (iv_wf_vass fo_Σ Γ fo_na fo_N Sort.type1 h (fo_N_typed Γ h) eq_refl)).
Qed.

Definition fo_sz : term := mkApps (tConstruct fo_ind 1 []) [tConstruct fo_ind 0 []].

Lemma fo_sz_typed : fo_Σ ;;; [] |-E fo_sz : mkApps fo_N [].
Proof.
  exact (typeE_App _ _ _ fo_na fo_N fo_N _ _ (fo_NN_typed [] localenv_nil) (fo_s_typed [] localenv_nil)
           (fo_z_typed [] localenv_nil)).
Qed.

Lemma fo_sz_wcbv_value : PCUICWcbvEval.value fo_Σ fo_sz.
Proof.
  eapply PCUICWcbvEval.value_app.
  - eapply (PCUICWcbvEval.value_head_cstr _ _ fo_ind 1 [] fo_mdecl fo_idecl fo_cs).
    + split; [split; reflexivity|reflexivity].
    + cbn. lia.
  - constructor; [|constructor]. constructor. constructor. reflexivity.
Qed.

Lemma fo_N_isType (Γ : context) : wf_localE fo_Σ Γ -> isTypeE fo_Σ Γ fo_N.
Proof. intros h. exact (has_sort_isTypeE _ (fo_N_typed Γ h)). Qed.

Lemma fo_N_refl (pb : conv_pb) : ws_cumul_pbE pb fo_Σ [] fo_N fo_N.
Proof. exact (ws_cumul_pbE_refl (Σ := fo_Σ) (Γ := []) (t := fo_N) eq_refl eq_refl). Qed.

(** The spine of [s]'s type on [z], and its arity spine. *)
Lemma fo_s_spine :
  PCUICAritiesEta.typing_spineE fo_Σ [] (type_of_constructor fo_mdecl fo_cs (fo_ind, 1) [])
    [tConstruct fo_ind 0 []] (mkApps (tInd fo_ind []) []).
Proof.
  have hNN : isTypeE fo_Σ [] (tProd fo_na fo_N fo_N) := has_sort_isTypeE _ (fo_NN_typed [] localenv_nil).
  econstructor.
  - exact hNN.
  - exact hNN.
  - exact (isType_ws_cumul_pbE_refl (Σ := fo_Σ) (wfΣ := fo_wfE) [] _ hNN).
  - exact (fo_z_typed [] localenv_nil).
  - econstructor; [exact (fo_N_isType [] localenv_nil)|exact (fo_N_isType [] localenv_nil)|exact (fo_N_refl Cumul)].
Qed.

(** The spine consumes one product: the type [Π _ : N. N] is not its result [N], and the argument
    list [[z]] is not empty. *)
Lemma fo_s_spine_nondeg : tProd fo_na fo_N fo_N <> fo_N /\ [tConstruct fo_ind 0 []] <> [].
Proof. split; intros h; vm_compute in h; discriminate h. Qed.

(** The value [s z], built directly. *)
Lemma fo_z_value : firstorder_valueE fo_Σ [] (tConstruct fo_ind 0 []).
Proof.
  exact (firstorder_value_CE fo_Σ [] fo_ind 0 [] [] [] [] (fo_z_typed [] localenv_nil) (@Forall_nil _ _) fo_not_prop).
Qed.

Lemma fo_sz_value : firstorder_valueE fo_Σ [] fo_sz.
Proof.
  exact (firstorder_value_CE fo_Σ [] fo_ind 1 [] [] [tConstruct fo_ind 0 []] [] fo_sz_typed
           (@Forall_cons _ _ _ _ fo_z_value (@Forall_nil _ _)) fo_not_prop).
Qed.

(** The value [s z] has an argument: it is not a bare constructor. *)
Lemma fo_sz_nondeg : (decompose_app fo_sz).2 <> [].
Proof. intros h; vm_compute in h; discriminate h. Qed.

(** The step of "is closed": a constructor applied to closed arguments is closed. *)
Lemma fo_closed_step i n ui (args : list term) :
  Forall (fun t => is_true (closedn 0 t)) args -> is_true (closedn 0 (mkApps (tConstruct i n ui) args)).
Proof.
  intros h. rewrite PCUICClosed.closedn_mkApps /=.
  induction h as [|x l hx _ IH]; [reflexivity|].
  cbn in hx |- *. rewrite hx. exact IH.
Qed.

(** [let X := N : Type1 in X → X]: the let-bound [X] occurs in the domain and the codomain of the
    body. *)
Definition fo_letNN : term := tLetIn fo_na fo_N fo_T (tProd fo_na (tRel 0) (tRel 1)).

Lemma fo_letNN_typed : fo_Σ ;;; [] |-E fo_letNN : tSort (Sort.sort_of_product Sort.type1 Sort.type1).
Proof.
  have hdef : lift_typing typingE fo_Σ [] (j_vdef fo_na fo_N fo_T) :=
    iv_vdef fo_Σ [] fo_na fo_N fo_T _ (fo_N_typed [] localenv_nil) (fo_T_typedE [] localenv_nil) eq_refl.
  have hΓ' : wf_localE fo_Σ ([] ,, vdef fo_na fo_N fo_T) by (apply localenv_cons_def; [constructor|exact hdef]).
  have hX : fo_Σ ;;; [] ,, vdef fo_na fo_N fo_T |-E tRel 0 : tSort Sort.type1 :=
    typeE_Rel _ _ 0 (vdef fo_na fo_N fo_T) hΓ' eq_refl.
  have hΓ'' := iv_wf_vass fo_Σ _ fo_na (tRel 0) Sort.type1 hΓ' hX eq_refl.
  have hlet : fo_Σ ;;; [] |-E fo_letNN
      : tLetIn fo_na fo_N fo_T (tSort (Sort.sort_of_product Sort.type1 Sort.type1)) :=
    typeE_LetIn _ _ fo_na fo_N fo_T (tProd fo_na (tRel 0) (tRel 1)) _ hdef
      (typeE_Prod _ _ fo_na (tRel 0) (tRel 1) Sort.type1 Sort.type1
         (iv_vass_s fo_Σ _ fo_na (tRel 0) Sort.type1 hX eq_refl)
         (typeE_Rel _ _ 1 (vdef fo_na fo_N fo_T) hΓ'' eq_refl)).
  eapply (type_ws_cumul_pbE (Σ := fo_Σ) (cbΣ := wfE_ClosedBodies fo_Σ (wfΣ := fo_wfE)) (pb := Cumul) _ hlet).
  - apply has_sort_isTypeE with (s := Sort.super (Sort.sort_of_product Sort.type1 Sort.type1)).
    apply typeE_Sort; [constructor|].
    apply/(PCUICWfUniverses.wf_sort_reflect fo_Σ). reflexivity.
  - eapply (red_ws_cumul_pbE (Σ := fo_Σ) (wfΣ := wfE_ClosedBodies fo_Σ (wfΣ := fo_wfE))).
    constructor; [reflexivity|exact (type_is_open_termE (Σ := fo_Σ) (wfΣ := fo_wfE) hlet)|].
    apply rt_step. apply red_zeta.
Qed.

(** [firstorder_spine_letE] on [fo_letNN] with the argument [z]: the substitution [X := N] into the
    body [X → X] gives [N → N], which is not the substituted [N] and not the body; the let-type is
    not [N → N] and ζ-reduces to it in one step; the argument list is not empty. *)
Lemma fo_letNN_nondeg :
  (tProd fo_na (tRel 0) (tRel 1)) {0 := fo_N} = tProd fo_na fo_N fo_N /\
  tProd fo_na fo_N fo_N <> fo_N /\ tProd fo_na fo_N fo_N <> tProd fo_na (tRel 0) (tRel 1) /\
  fo_letNN <> tProd fo_na fo_N fo_N /\ ∥ red1 fo_Σ [] fo_letNN (tProd fo_na fo_N fo_N) ∥ /\
  [tConstruct fo_ind 0 []] <> [].
Proof.
  split; [vm_compute; reflexivity|].
  split; [intros h; vm_compute in h; discriminate h|].
  split; [intros h; vm_compute in h; discriminate h|].
  split; [intros h; vm_compute in h; discriminate h|].
  split; [constructor; exact (red_zeta _ _ fo_na fo_N fo_T (tProd fo_na (tRel 0) (tRel 1)))|discriminate].
Qed.

(** [let _ := N : Type1 in Type1] is the sort [Type1] behind a let. *)
Definition fo_letT : term := tLetIn fo_na fo_N fo_T fo_T.

Lemma fo_T1_typedE (Γ : context) : wf_localE fo_Σ Γ ->
  fo_Σ ;;; Γ |-E tSort (Sort.super Sort.type1) : tSort (Sort.super (Sort.super Sort.type1)).
Proof. intros h. apply typeE_Sort; [exact h|apply wf_sort_super, wf_sort_type1]. Qed.

Lemma fo_letT_typed (Γ : context) : wf_localE fo_Σ Γ ->
  fo_Σ ;;; Γ |-E fo_letT : tSort (Sort.super Sort.type1).
Proof.
  intros h.
  have hdef : lift_typing typingE fo_Σ Γ (j_vdef fo_na fo_N fo_T) :=
    iv_vdef fo_Σ Γ fo_na fo_N fo_T _ (fo_N_typed Γ h) (fo_T_typedE Γ h) eq_refl.
  have hΓ' : wf_localE fo_Σ (Γ ,, vdef fo_na fo_N fo_T) by (apply localenv_cons_def; [exact h|exact hdef]).
  have hlet : fo_Σ ;;; Γ |-E fo_letT : tLetIn fo_na fo_N fo_T (tSort (Sort.super Sort.type1)) :=
    typeE_LetIn _ _ fo_na fo_N fo_T fo_T (tSort (Sort.super Sort.type1)) hdef (fo_T_typedE _ hΓ').
  have hcl : is_closed_context Γ := wf_local_closed_contextE (Σ := fo_Σ) (wfΣ := fo_wfE) h.
  eapply (type_ws_cumul_pbE (Σ := fo_Σ) (cbΣ := wfE_ClosedBodies fo_Σ (wfΣ := fo_wfE)) (pb := Cumul) _ hlet).
  - exact (has_sort_isTypeE _ (fo_T1_typedE Γ h)).
  - eapply (red_ws_cumul_pbE (Σ := fo_Σ) (wfΣ := wfE_ClosedBodies fo_Σ (wfΣ := fo_wfE))).
    constructor; [exact hcl|exact (type_is_open_termE (Σ := fo_Σ) (wfΣ := fo_wfE) hlet)|].
    apply rt_step. apply red_zeta.
Qed.

(** The variable [X : let _ := N : Type1 in Type1] is a type, of sort [Type1]. *)
Lemma fo_wf_letT : wf_localE fo_Σ [vass fo_na fo_letT].
Proof.
  exact (iv_wf_vass fo_Σ [] fo_na fo_letT (Sort.super Sort.type1) localenv_nil
           (fo_letT_typed [] localenv_nil) eq_refl).
Qed.

Lemma fo_X_typed : fo_Σ ;;; [vass fo_na fo_letT] |-E tRel 0 : fo_T.
Proof.
  have hrel : fo_Σ ;;; [vass fo_na fo_letT] |-E tRel 0 : fo_letT :=
    typeE_Rel _ _ 0 (vass fo_na fo_letT) fo_wf_letT eq_refl.
  eapply (type_ws_cumul_pbE (Σ := fo_Σ) (cbΣ := wfE_ClosedBodies fo_Σ (wfΣ := fo_wfE)) (pb := Cumul) _ hrel).
  - exact (has_sort_isTypeE _ (fo_T_typedE _ fo_wf_letT)).
  - eapply (red_ws_cumul_pbE (Σ := fo_Σ) (wfΣ := wfE_ClosedBodies fo_Σ (wfΣ := fo_wfE))).
    constructor; [exact (wf_local_closed_contextE (Σ := fo_Σ) (wfΣ := fo_wfE) fo_wf_letT)
                 |exact (type_is_open_termE (Σ := fo_Σ) (wfΣ := fo_wfE) hrel)|].
    apply rt_step. apply red_zeta.
Qed.

(** The two contexts of [X] differ, and the first declared type ζ-reduces to the second in one
    step. *)
Lemma fo_ctx_nondeg : [vass fo_na fo_letT] <> [vass fo_na fo_T] /\ ∥ red1 fo_Σ [] fo_letT fo_T ∥.
Proof.
  split; [intros h; vm_compute in h; discriminate h|].
  constructor. exact (red_zeta _ _ fo_na fo_N fo_T fo_T).
Qed.

(** ** The lemmas that never took a class *)

(** The induction principle on the value [s z], with the predicate "is closed": the step passed
    to it uses the induction hypothesis on the constructor's arguments ([fo_closed_step]), and
    [s z] has an argument ([fo_sz_nondeg]).
    INSTANCE NONDEGEN PCUICFirstorderEtaInstances.fo_sz_nondeg *)
Definition firstorder_value_indsE_inst : is_true (closedn 0 fo_sz) :=
  firstorder_value_indsE fo_Σ [] (fun t => is_true (closedn 0 t))
    (fun i n ui _ args _ _ _ hP _ => fo_closed_step i n ui args hP)
    fo_sz fo_sz_value.

(** [N] has a constructor, [s : N → N], that takes an argument. *)
Lemma fo_idecl_nondeg : In fo_cs (ind_ctors fo_idecl) /\ cstr_args fo_cs <> [].
Proof. split; [cbn; right; left; reflexivity|intros h; vm_compute in h; discriminate h]. Qed.

(** [N] is first order, hence not propositional.
    INSTANCE NONDEGEN PCUICFirstorderEtaInstances.fo_idecl_nondeg *)
Definition firstorder_ind_propositionalE_inst : ~~ isPropositional fo_Σ fo_ind :=
  firstorder_ind_propositionalE (Σ := fo_Σ) (wfΣ := fo_wfE) fo_ind fo_mdecl fo_idecl fo_declared fo_firstorder.

(** The typing spine of [Π _ : N. N] on [[z]], as an arity spine.
    INSTANCE NONDEGEN PCUICFirstorderEtaInstances.fo_s_spine_nondeg *)
Definition typing_spine_arity_spineE_inst :
  PCUICSpineEta.arity_spineE fo_Σ [] (tProd fo_na fo_N fo_N) [tConstruct fo_ind 0 []] fo_N :=
  typing_spine_arity_spineE (Σ := fo_Σ) (wfΣ := fo_wfE) [] [vass fo_na fo_N] _ _ fo_ind [] [] fo_s_spine.

Lemma fo_ctxT_conv : ws_cumul_ctx_pbE Conv fo_Σ [vass fo_na fo_letT] [vass fo_na fo_T].
Proof.
  constructor; [constructor|]. unfold ws_cumul_declsE. constructor; [reflexivity|].
  eapply (red_ws_cumul_pbE (Σ := fo_Σ) (wfΣ := wfE_ClosedBodies fo_Σ (wfΣ := fo_wfE))).
  constructor; [reflexivity|exact (subject_is_open_termE (Σ := fo_Σ) (wfΣ := fo_wfE) (fo_letT_typed [] localenv_nil))|].
  apply rt_step. apply red_zeta.
Qed.

(** The variable [X] is a type in [X : let _ := N : Type1 in Type1], hence in [X : Type1]: the
    typing of [X] reads the declaration that the conversion changes.
    INSTANCE NONDEGEN PCUICFirstorderEtaInstances.fo_ctx_nondeg *)
Definition isType_context_conversionE_inst : isTypeE fo_Σ [vass fo_na fo_T] (tRel 0) :=
  isType_context_conversionE (Σ := fo_Σ) (wfΣ := fo_wfE) (Γ := [vass fo_na fo_letT])
    (Δ := [vass fo_na fo_T]) (T := tRel 0) (has_sort_isTypeE _ fo_X_typed) fo_ctxT_conv
    (iv_wf_vass fo_Σ [] fo_na fo_T (Sort.super Sort.type1) localenv_nil (fo_T_typedE [] localenv_nil) eq_refl).

Lemma fo_ext : strictly_extends_decls fo_env fo_env2.
Proof. split; [reflexivity| |reflexivity]. exists [(fo_kn2, InductiveDecl fo_mdecl)]. reflexivity. Qed.

(** The extension is strict: it puts the declaration [N2] in front of [fo_env]'s declarations,
    under the name [fo_kn2], which is not [N]'s, so a lookup of [N] passes it. *)
Lemma fo_ext_nondeg :
  declarations fo_Σ2.1 <> declarations fo_Σ.1 /\ fo_kn2 <> fo_kn /\
  declarations fo_Σ2.1 = (fo_kn2, InductiveDecl fo_mdecl) :: declarations fo_Σ.1.
Proof.
  split; [intros h; vm_compute in h; discriminate h|].
  split; [intros h; vm_compute in h; discriminate h|reflexivity].
Qed.

(** The lookup of [N] in [fo_env], read in its strict extension [fo_env2].
    INSTANCE NONDEGEN PCUICFirstorderEtaInstances.fo_ext_nondeg *)
Definition plookup_env_extendsE_inst :
  plookup_env (firstorder_env' (declarations fo_env2)) fo_kn = Some true :=
  plookup_env_extendsE (Σ := fo_env2) (Σ' := fo_env) fo_kn true fo_ext fo_wfE2 eq_refl.

(** [N]'s declaration is first order in [fo_Σ], hence in its strict extension [fo_Σ2].
    INSTANCE NONDEGEN PCUICFirstorderEtaInstances.fo_ext_nondeg *)
Definition firstorder_mutind_extE_inst :
  @firstorder_mutind (firstorder_env fo_Σ2) fo_mdecl :=
  firstorder_mutind_extE (Σ := fo_Σ2) (Σ' := fo_Σ) fo_mdecl fo_ext fo_wfE2 eq_refl.

(** [s z] against itself.
    INSTANCE IMPOSSIBLE: the conclusion is t = t', so every instance has t' = t (and a first-order value has no binders, so t ≡α t' is already t = t') *)
Definition firstorder_value_alphaE_inst : fo_sz = fo_sz :=
  firstorder_value_alphaE fo_Σ fo_sz fo_sz (upto_names_ref fo_sz) fo_sz_value.

(** The inversion that the main theorem uses in place of a copy, at [fo_Σ]: the arity
    [Π _ : N. Type1] is never related to [N], at any [pb].
    INSTANCE IMPOSSIBLE: the conclusion is False: an arity that ends in a sort is never related to an inductive type, so the lemma's cumulativity premise (here at fo_Σ, for every pb) cannot hold; its other premise (ClosedBodies fo_Σ, from fo_wfE) holds and is discharged
    TARGET PCUICEtaA6More.invert_cumul_it_mkProd_or_LetIn_Sort_IndE *)
Definition fo_invert_cumul_Sort_IndE_inst :
  forall pb, ws_cumul_pbE pb fo_Σ [] (it_mkProd_or_LetIn [vass fo_na fo_N] (tSort Sort.type1))
                          (mkApps (tInd fo_ind []) []) -> False :=
  fun pb h => PCUICEtaA6More.invert_cumul_it_mkProd_or_LetIn_Sort_IndE
                (Σ := fo_Σ) (wfΣ := wfE_ClosedBodies fo_Σ (wfΣ := fo_wfE)) h.

(** ** The lemmas that took T1's forecast class until copy 18b landed *)

Section FirstorderEtaInstances.

(** The arity spine of [Π _ : N. N] on [[z]], as a first-order spine.
    INSTANCE NONDEGEN PCUICFirstorderEtaInstances.fo_s_spine_nondeg *)
Definition instantiated_typing_spine_firstorder_spineE_inst :
  firstorder_spineE fo_Σ [] (tProd fo_na fo_N fo_N) [tConstruct fo_ind 0 []] fo_N :=
  instantiated_typing_spine_firstorder_spineE (Σ := fo_Σ) (wfΣ := fo_wfE) [] _ _ _
    (instantiated_tProd (Σ := fo_Σ) [] fo_na fo_N fo_ind [] [] fo_firstorder
       (fun x => instantiated_mkApps (Σ := fo_Σ) [] fo_ind [] []))
    typing_spine_arity_spineE_inst
    (has_sort_isTypeE _ (fo_NN_typed [] localenv_nil)).

(** The first-order spine of [Π _ : N. N] on [[z]] ([instantiated_typing_spine_firstorder_spineE_inst]),
    moved to the let-type [let X := N : Type1 in X → X]; the substitution [X := N] into [X → X]
    gives [N → N], neither the substituted [N] nor the body ([fo_letNN_nondeg]).
    INSTANCE NONDEGEN PCUICFirstorderEtaInstances.fo_letNN_nondeg *)
Definition firstorder_spine_letE_inst : firstorder_spineE fo_Σ [] fo_letNN [tConstruct fo_ind 0 []] fo_N :=
  firstorder_spine_letE (Σ := fo_Σ) (wfΣ := fo_wfE) (na := fo_na) (a := fo_N) (A := fo_T)
    (B := tProd fo_na (tRel 0) (tRel 1)) instantiated_typing_spine_firstorder_spineE_inst
    (has_sort_isTypeE _ fo_letNN_typed).

(** The spine of [s]'s type on [[z]].
    INSTANCE NONDEGEN PCUICFirstorderEtaInstances.fo_s_spine_nondeg *)
Definition firstorder_argsE_inst :
  firstorder_spineE fo_Σ [] (type_of_constructor fo_mdecl fo_cs (fo_ind, 1) [])
    [tConstruct fo_ind 0 []] (mkApps (tInd fo_ind []) []) :=
  firstorder_argsE (Σ := fo_Σ) (wfΣ := fo_wfE) (args := [tConstruct fo_ind 0 []]) fo_declared_cs
    fo_s_spine fo_firstorder.

(** The main theorem on the value [s z].
    INSTANCE NONDEGEN PCUICFirstorderEtaInstances.fo_sz_nondeg *)
Definition firstorder_value_specE_inst : firstorder_valueE fo_Σ [] fo_sz :=
  firstorder_value_specE fo_Σ fo_sz fo_ind [] [] fo_wfE localenv_nil fo_sz_typed fo_sz_wcbv_value
    fo_firstorder.

End FirstorderEtaInstances.
