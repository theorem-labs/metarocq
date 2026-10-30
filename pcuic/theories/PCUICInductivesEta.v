(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 CRelationClasses ProofIrrelevance.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICWeakeningConv PCUICWeakeningTyp
     PCUICSigmaCalculus PCUICInstDef PCUICInstConv PCUICContextSubst
     PCUICRenameDef PCUICRenameConv PCUICRenameTyp
     PCUICSubstitution PCUICOnFreeVars PCUICClosed PCUICClosedConv PCUICClosedTyp
     PCUICCumulativity PCUICGeneration PCUICReduction PCUICWellScopedCumulativity
     PCUICEquality PCUICConfluence PCUICParallelReductionConfluence
     PCUICContextConversion PCUICUnivSubstitutionConv
     PCUICUnivSubstitutionTyp
     PCUICConversion PCUICGlobalEnv PCUICInversion PCUICContexts PCUICArities
     PCUICParallelReduction PCUICWfUniverses PCUICSpine PCUICClosedBodies PCUICInductives
     PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
     PCUICTypingEtaNotions PCUICClosedTypEta PCUICWeakeningEnvTypEta PCUICRenameTypEta
     PCUICWeakeningTypEta PCUICUnivSubstitutionTypEta PCUICContextConversionTypEta
     PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta
     PCUICWellScopedCumulativityEta PCUICContextConversionEta PCUICConversionEtaCongr
     PCUICWsCumulEtaSubst PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp PCUICEtaA6 PCUICEtaA6More
     PCUICEtaI5 PCUICInversionEta PCUICSREtaConv PCUICSpineEta.
From MetaRocq.PCUIC Require PCUICWfUniversesEta.

From Stdlib Require Import ssreflect ssrbool.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

(** * Inductive declarations, projections and case predicates over [typingE]

  The E copy of [PCUICInductives]. Each declaration of the base file that mentions typing,
  [wf_local], [wf], [isType], [isTypeRel], [subslet], the spines or the cumulativity (in its
  statement, or through the [wf] variable of its section) is copied; its E name is the base name
  with the suffix [E], and its statement is the base statement with only the relations renamed:
  [typing] → [typingE], [wf_local] → [wf_localE], [wf] → [wfE], [isType] → [isTypeE],
  [isTypeRel] → [isTypeRelE], [subslet] → [subsletE], [typing_spine] → [typing_spineE] (the one
  of [PCUICAritiesEta]), [spine_subst] / [arity_spine] → [spine_substE] / [arity_spineE] (of
  [PCUICSpineEta]), [wf_subslet] → [wf_subsletE] (here), [Σ ;;; Γ ⊢ t = u] →
  [Σ ;;; Γ ⊢E t = u]. Reduction ([Σ ;;; Γ ⊢ t ⇝ u], [red]) is unchanged. Implicit status,
  binder names and positions are base's; section premises are base's ([Proof using] kept).

  The record [wf_subsletE] (fields [wf_subslet_ctxE], [wf_subslet_subsletE], the latter a
  coercion as in base) is the canonical one. [conv_ctx_reflE] is the twin of
  [PCUICCumulativity.conv_ctx_refl], the instance that base's [Hint Resolve conv_ctx_refl :
  pcuic] resolves to; it is a global instance, as base's, and this file registers it and
  [isType_introE] in [pcuic] as base registers [conv_ctx_refl] and [isType_intro]. Base's
  [Arguments] of [subst_context] and [it_mkProd_or_LetIn] and its [Hint Rewrite … : len] lines
  are about syntactic functions; they act through the import of [PCUICInductives] and are not
  repeated.

  Proof routes that differ from base (statements are twins): [closed_red_from_emptyE] and
  [red_it_mkProd_or_LetIn_smashE] are the corollaries, through [wfE_ClosedBodies], of
  [PCUICSREtaConv]'s [closed_red_from_empty_cb] and [red_it_mkProd_or_LetIn_smash_cb];
  [declared_projectionsE] takes the identity of the abstract instance on the parameters from
  [subst_abstract_instance_idE], compares the two sorts by [ws_cumul_pbE_Sort] and takes the
  closedness of [inds] from [closed_inds] (no premise); [invert_type_mkApps_indE] scopes the
  conversion premise of [typeE_Cumul] by [into_ws_cumul_pbE_spec]; [subslet_extended_substE]
  uses [meta_convE].

  Two names of this file SHADOW a DIFFERENT statement of the same name in its import closure,
  as in base: [subslet_extended_substE]
  (here the twin of [PCUICInductives.subslet_extended_subst], over [smash_context [] Δ] alone;
  [PCUICContextsEta]'s is the twin of [PCUICContexts.subslet_extended_subst], over
  [Γ ,,, smash_context [] Δ]) and [isType_it_mkProd_or_LetInE] (here the twin of
  [PCUICInductives.isType_it_mkProd_or_LetIn], which reads a [type_local_ctx] and a
  [wf_sort]; [PCUICAritiesEta]'s is the twin of
  [PCUICArities.isType_it_mkProd_or_LetIn], which reads a [sorts_local_ctx] and an [isTypeE];
  a third object of that name is [PCUICInductiveInversionEtaB]'s, declared in that file's
  header, as base has three). No ascription relates any two of them. Where both files are in
  scope, refer to them qualified.

  Not copied: the declarations that mention none of the relations (used from base, which this
  file imports), among them [nth_errror_arities_context], whose section premise [wf] its base
  proof does not use. *)

Local Set SimplIsCbn.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(** The twin of [PCUICCumulativity.conv_ctx_refl] (the instance that base's [Hint Resolve
    conv_ctx_refl : pcuic] resolves to): reflexivity of context conversion over [JoinE], a global
    instance as base's. *)
#[global] Instance conv_ctx_reflE {cf : checker_flags} (Σ : global_env_ext) :
  CRelationClasses.Reflexive (All2_fold (cumul_pb_decls (@JoinE cf) Conv Σ)).
Proof.
  intros Γ. eapply PCUICConfluence.All2_fold_refl. intros ? [na [b|] ty]; constructor; try reflexivity; apply JoinE_refl.
Qed.
#[global]
Hint Resolve conv_ctx_reflE : pcuic.

(** The twin of [PCUICCumulativity.cumul_ctx_refl], beside the conversion form above:
    reflexivity of context cumulativity over [JoinE], a global instance as base's. *)
#[global] Instance cumul_ctx_reflE {cf : checker_flags} (Σ : global_env_ext) :
  CRelationClasses.Reflexive (All2_fold (cumul_pb_decls (@JoinE cf) Cumul Σ)).
Proof.
  intros Γ. eapply PCUICConfluence.All2_fold_refl. intros ? d; apply cumul_decls_reflE.
Qed.

Lemma wf_arities_context_instE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {mind mdecl u} :
  declared_minductive Σ mind mdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_localE Σ (arities_context mdecl.(ind_bodies))@[u].
Proof.
  intros decli cu.
  unshelve eapply declared_minductive_to_gen in decli; eauto.
  eapply wf_local_instantiateE; tea. cbn.
  eapply wf_arities_contextE; tea.
  unshelve eapply declared_minductive_from_gen; eauto.
Qed.

Lemma instantiate_indsE {cf:checker_flags} {Σ} {wfΣ : wfE Σ.1} {u mind mdecl} :
  declared_minductive Σ.1 mind mdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  subst_instance u
     (inds mind (abstract_instance (PCUICEnvironment.ind_universes mdecl))
        (ind_bodies mdecl)) =
  inds mind u (ind_bodies mdecl).
Proof.
  intros declm cu.
  rewrite subst_instance_inds.
  f_equal. eapply subst_instance_id_mdecl; eauto.
Qed.

Section OnInductives.
  Context {cf : checker_flags} {Σ : global_env} {wfΣ : wfE Σ} {mdecl ind idecl}
    (decli : declared_inductive Σ ind mdecl idecl).

  Lemma declared_inductive_arity_isTypeRelE :
    isTypeRelE (Σ, ind_universes mdecl) []
      (it_mkProd_or_LetIn (ind_params mdecl ,,, ind_indices idecl) (tSort (ind_sort idecl))) rel_of_Type.
  Proof using decli wfΣ.
    eapply on_declared_inductiveE in decli as [onmind oib].
    rewrite it_mkProd_or_LetIn_app.
    exact (oib.(onArityRed)).
  Qed.

  Lemma on_minductive_wf_params_indicesE : wf_localE (Σ, ind_universes mdecl) (ind_params mdecl ,,, ind_indices idecl).
  Proof using decli wfΣ.
    pose proof declared_inductive_arity_isTypeRelE as X.
    destruct X as (_ & s & Hs & _).
    eapply it_mkProd_or_LetIn_wf_localE in Hs.
    now rewrite app_context_nil_l in Hs.
  Qed.

  (** The declared type reduces to the arity built from the parameters,
      indices and sort ([ind_arity_red]); it is no longer syntactically equal
      to it. *)
  Lemma declared_inductive_typeE :
    red Σ [] (ind_type idecl) (it_mkProd_or_LetIn (ind_params mdecl ,,, ind_indices idecl) (tSort (ind_sort idecl))).
  Proof using decli wfΣ.
    eapply on_declared_inductiveE in decli as [onmind oib].
    rewrite it_mkProd_or_LetIn_app.
    exact (ind_arity_red_red oib).
  Qed.

End OnInductives.

(** A reduction between closed terms in the empty context holds in every closed context. *)
Lemma closed_red_from_emptyE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ M N} :
  is_closed_context Γ -> closed M -> red Σ [] M N -> Σ ;;; Γ ⊢ M ⇝ N.
Proof. intros; eapply closed_red_from_empty_cb; tea; typeclasses eauto. Qed.

Lemma isType_introE {cf:checker_flags} {Σ Γ T s} : Σ ;;; Γ |-E T : tSort s -> isTypeE Σ Γ T.
Proof.
  eapply has_sort_isTypeE.
Qed.
#[global]
Hint Resolve isType_introE : pcuic.

Section OnInductives.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {mdecl ind idecl}
    (decli : declared_inductive Σ ind mdecl idecl).

  Lemma on_minductive_wf_params_indices_instE (u : Instance.t) :
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_localE Σ (subst_instance u (ind_params mdecl ,,, ind_indices idecl)).
  Proof using decli wfΣ.
    intros.
    unshelve eapply declared_inductive_to_gen in decli; eauto.
    eapply (wf_local_instantiateE _ (MRProd.proj1 decli)); eauto.
    eapply on_minductive_wf_params_indicesE.
    unshelve eapply declared_inductive_from_gen; eauto.
  Qed.

  Lemma on_inductive_instE Γ u :
    wf_localE Σ Γ ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    isTypeRelE Σ Γ (it_mkProd_or_LetIn (subst_instance u (ind_params mdecl ,,, idecl.(ind_indices)))
          (tSort (subst_instance_sort u idecl.(ind_sort)))) rel_of_Type.
  Proof using decli wfΣ.
    move=> wfΓ cext.
    pose proof (declared_inductive_arity_isTypeRelE (wfΣ := wfΣ) decli) as ar.
    eapply lift_typing_weaken_ctxE with (Γ := []) => //.
    rewrite -(subst_instance_it_mkProd_or_LetIn u _ (tSort _)).
    eapply (lift_typing_subst_instance_declE Σ [] _ _ (InductiveDecl mdecl) u wfΣ) in ar; cbn in ar; tas.
    unshelve eapply declared_inductive_to_gen in decli; eauto.
  Qed.

  Lemma declared_inductive_valid_typeE Γ u :
    wf_localE Σ Γ ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    isTypeRelE Σ Γ (subst_instance u idecl.(ind_type)) rel_of_Type.
  Proof using decli wfΣ.
    move=> wfΓ cext.
    destruct (on_declared_inductiveE decli) as [onmind oib].
    pose proof (oib.(onArity)) as ar.
    eapply lift_typing_weaken_ctxE with (Γ := []) => //.
    eapply (lift_typing_subst_instance_declE Σ [] _ _ (InductiveDecl mdecl) u wfΣ) in ar; cbn in ar; tas.
    unshelve eapply declared_inductive_to_gen in decli; eauto.
  Qed.

  Lemma declared_inductive_type_closed_redE Γ u :
    wf_localE Σ Γ ->
    Σ ;;; Γ ⊢ subst_instance u (ind_type idecl) ⇝
      subst_instance u (it_mkProd_or_LetIn (ind_params mdecl ,,, ind_indices idecl) (tSort (ind_sort idecl))).
  Proof using decli wfΣ.
    move=> wfΓ.
    destruct (on_declared_inductiveE decli) as [onmind oib].
    eapply closed_red_from_emptyE; first by eapply wf_local_closed_contextE.
    - rewrite closedn_subst_instance.
      have h := oib.(onArity).
      eapply isTypeRelE_isTypeE in h.
      exact (isType_closedE (Σ := (Σ.1, ind_universes mdecl)) (Γ := []) h).
    - exact (red_subst_instance _ [] u _ _ (declared_inductive_typeE (wfΣ := wfΣ) decli)).
  Qed.

  Lemma declared_inductive_type_ws_cumulE Γ u :
    wf_localE Σ Γ ->
    Σ ;;; Γ ⊢E subst_instance u (ind_type idecl) =
      subst_instance u (it_mkProd_or_LetIn (ind_params mdecl ,,, ind_indices idecl) (tSort (ind_sort idecl))).
  Proof using decli wfΣ.
    move=> wfΓ. eapply red_ws_cumul_pbE.
    now eapply declared_inductive_type_closed_redE.
  Qed.

  Lemma isType_ind_arity_instE Γ u :
    wf_localE Σ Γ ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    isTypeE Σ Γ (subst_instance u (it_mkProd_or_LetIn (ind_params mdecl ,,, ind_indices idecl) (tSort (ind_sort idecl)))).
  Proof using decli wfΣ.
    move=> wfΓ cu. rewrite subst_instance_it_mkProd_or_LetIn /=.
    eapply isTypeRelE_isTypeE. now eapply on_inductive_instE.
  Qed.

  Lemma typing_spine_ind_typeE Γ u args T :
    wf_localE Σ Γ ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    PCUICAritiesEta.typing_spineE Σ Γ (subst_instance u (it_mkProd_or_LetIn (ind_params mdecl ,,, ind_indices idecl) (tSort (ind_sort idecl)))) args T ->
    PCUICAritiesEta.typing_spineE Σ Γ (subst_instance u (ind_type idecl)) args T.
  Proof using decli wfΣ.
    move=> wfΓ cu sp.
    eapply typing_spine_strengthenE; [exact sp| |].
    - eapply isTypeRelE_isTypeE, declared_inductive_valid_typeE; tea.
    - eapply ws_cumul_pbE_eq_le. now eapply declared_inductive_type_ws_cumulE.
  Qed.

  (** [tInd ind u] has the arity built from the parameters, indices and sort of
      its declaration, to which its declared type reduces ([ind_arity_red]). *)
  Lemma type_Ind_arity_formE Γ u :
    wf_localE Σ Γ ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    Σ ;;; Γ |-E tInd ind u :
      subst_instance u (it_mkProd_or_LetIn (ind_params mdecl ,,, ind_indices idecl) (tSort (ind_sort idecl))).
  Proof using decli wfΣ.
    move=> wfΓ cu.
    eapply (type_ws_cumul_pbE (pb := Conv)); [eapply typeE_Ind; tea| |].
    - now eapply isType_ind_arity_instE.
    - now eapply declared_inductive_type_ws_cumulE.
  Qed.

  Lemma typing_spine_ind_type_invE Γ u args T :
    wf_localE Σ Γ ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    PCUICAritiesEta.typing_spineE Σ Γ (subst_instance u (ind_type idecl)) args T ->
    PCUICAritiesEta.typing_spineE Σ Γ (subst_instance u (it_mkProd_or_LetIn (ind_params mdecl ,,, ind_indices idecl) (tSort (ind_sort idecl)))) args T.
  Proof using decli wfΣ.
    move=> wfΓ cu sp.
    eapply typing_spine_strengthenE; [exact sp| |].
    - now eapply isType_ind_arity_instE.
    - eapply ws_cumul_pbE_eq_le. symmetry. now eapply declared_inductive_type_ws_cumulE.
  Qed.

  Local Definition oiE := (on_declared_inductiveE decli).1.
  Local Definition oibE := (on_declared_inductiveE decli).2.

  Lemma on_inductive_sortE : wf_sort (Σ.1, ind_universes mdecl) (ind_sort idecl).
  Proof using decli wfΣ.
    pose proof (oibE.(onArityRed)) as ar.
    destruct ar as (_ & s & ar & _).
    eapply PCUICWfUniversesEta.typing_wf_universesE in ar; auto.
    move/andP: ar => [].
    rewrite wf_universes_it_mkProd_or_LetIn => /andP [] _.
    now rewrite wf_universes_it_mkProd_or_LetIn => /andP [] _ /= /wf_sort_reflect.
  Qed.

  Lemma on_inductive_sort_instE u :
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_sort Σ (subst_instance u (ind_sort idecl)).
  Proof using decli wfΣ.
    generalize on_inductive_sortE => wf.
    destruct Σ. intros cu.
    eapply PCUICWfUniversesEta.wf_sort_instantiateE; eauto.
    now eapply consistent_instance_ext_wf.
  Qed.

  Lemma isType_mkApps_IndE {Γ puinst args inst} :
    consistent_instance_ext Σ (ind_universes mdecl) puinst ->
    spine_substE Σ Γ args inst (subst_instance puinst (ind_params mdecl ,,, ind_indices idecl)) ->
    Σ ;;; Γ |-E mkApps (tInd ind puinst) args : tSort (subst_instance puinst (ind_sort idecl)).
  Proof using decli wfΣ.
    intros cu sp.
    eapply PCUICSpineEta.type_mkAppsE; tea.
    econstructor; eauto. apply sp.
    eapply typing_spine_ind_typeE; [apply sp|exact cu|].
    rewrite subst_instance_it_mkProd_or_LetIn.
    eapply wf_arity_spine_typing_spineE; tea.
    split.
    rewrite -subst_instance_it_mkProd_or_LetIn.
    eapply isType_ind_arity_instE; tea.
    apply sp.
    eapply arity_spine_it_mkProd_or_LetIn_SortE.
    2:reflexivity. 2:exact sp.
    now eapply on_inductive_sort_instE.
  Qed.
End OnInductives.

(** * Projections *)

Lemma untyped_subslet_projsE {cf:checker_flags} (Σ : global_env_ext) i mdecl idecl :
  forall (wfΣ : wfE Σ.1)
  (Hdecl : declared_inductive Σ.1 i mdecl idecl),
  match ind_ctors idecl return Type with
  | [cs] =>
    on_projections mdecl (inductive_mind i) (inductive_ind i)
     idecl (ind_indices idecl) cs ->
     forall Γ t u,
     let indsubst := inds (inductive_mind i) u (ind_bodies mdecl) in
     untyped_subslet Γ
     (projs_inst i (ind_npars mdecl) (context_assumptions (cstr_args cs)) t)
     (smash_context []
        (subst_context (inds (inductive_mind i) u (ind_bodies mdecl))
           #|ind_params mdecl| (subst_instance u (cstr_args cs))))
  | _ => True
  end.
Proof.
  intros wfΣ Hdecl.
  destruct ind_ctors as [|cs []] eqn:Heq; trivial.
  intros onp. simpl. intros Γ t u.
  rewrite (smash_context_subst []).
  destruct onp.
  assert (#|PCUICEnvironment.ind_projs idecl| >=
  PCUICEnvironment.context_assumptions (cstr_args cs)). lia.
  clear on_projs_all.
  induction (cstr_args cs) as [|[? [] ?] ?].
  - simpl. constructor.
  - simpl. apply IHc. now simpl in H.
  - simpl. rewrite smash_context_acc /=.
    rewrite subst_context_snoc.
    rewrite /subst_decl {2}/map_decl /=.
    simpl in H. constructor. apply IHc. lia.
Qed.

Record wf_subsletE {cf} Σ Γ s Δ :=
  { wf_subslet_ctxE : wf_localE Σ (Γ ,,, Δ);
    wf_subslet_subsletE :> subsletE Σ Γ s Δ }.

Lemma wf_subslet_domE {cf} {Σ Γ s Δ} :
  wf_subsletE Σ Γ s Δ -> wf_localE Σ Γ.
Proof.
  intros [wf _]. now eapply All_local_env_app_inv in wf.
Qed.

Lemma isType_it_mkProd_or_LetIn_invE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Δ T} :
  isTypeE Σ Γ (it_mkProd_or_LetIn Δ T) ->
  isTypeE Σ (Γ ,,, Δ) T.
Proof.
  intros HT; apply lift_sorting_it_impl_gen with HT => // Hs.
  now eapply inversion_it_mkProd_or_LetInE in Hs.
Qed.

Lemma isType_it_mkProd_or_LetIn_substE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Δ args inst T} :
  isTypeE Σ Γ (it_mkProd_or_LetIn Δ T) ->
  spine_substE Σ Γ args inst Δ ->
  isTypeE Σ Γ (subst0 inst T).
Proof.
  intros isty sp.
  eapply isType_substE. exact sp.
  now eapply isType_it_mkProd_or_LetIn_invE in isty.
Qed.

Lemma subslet_extended_substE {cf:checker_flags} Σ Δ :
  wfE Σ.1 ->
  wf_localE Σ Δ ->
  subsletE Σ (smash_context [] Δ) (extended_subst Δ 0) Δ.
Proof.
  move=> wfΣ wfΔ.
  induction Δ as [|[na [d|] ?] ?] in wfΔ |- *; simpl; auto; depelim wfΔ.
  * constructor.
  * apply unlift_TermTyp in l.
    rewrite extended_subst_length. rewrite lift_closed. fvs.
    constructor. auto. specialize (IHΔ wfΔ).
    eapply weaken_ctxE in l. 3:eapply wf_local_smash_contextE; eauto. 2:auto.
    eapply (substitutionE (Δ := [])) in l. eapply l. all:auto.
  * rewrite smash_context_acc. simpl.
    rewrite /map_decl /= /map_decl /=. simpl.
    eassert (isTypeRelE Σ (smash_context [] Δ) (subst0 (extended_subst Δ 0) decl_type) _).
    { apply lift_sorting_it_impl_gen with l => // Hs.
      eapply weaken_ctxE in Hs. 3:eapply wf_local_smash_contextE; eauto. 2:auto.
      eapply (substitutionE (Δ := [])) in Hs. eapply Hs. all:auto. }
    rewrite lift_closed. fvs.
    rewrite (lift_extended_subst _ 1).
    rewrite -{4}(PCUICClosed.closed_ctx_lift 1 0 Δ); fvs.
    constructor.
    { eapply (subslet_liftE _ [_]); eauto.
      constructor; tas. eapply wf_local_smash_contextE; auto. }
    { eapply meta_convE.
      econstructor.
      rewrite smash_context_acc /=. constructor; tas.
      apply wf_local_smash_contextE; auto.
      reflexivity.
      simpl.
      rewrite distr_lift_subst. f_equal.
      rewrite lift_closed //. autorewrite with len; fvs. }
Qed.

Lemma context_subst_to_extended_list_kE {cf:checker_flags} Σ Δ :
  wfE Σ.1 ->
  wf_localE Σ Δ ->
  context_subst Δ
    (ListDef.map (subst0 (extended_subst Δ 0)) (to_extended_list_k Δ 0))
      (extended_subst Δ 0).
Proof.
  move=> wfΣ wfΔ.
  generalize 0 at 1 4.
  induction Δ as [|[na [d|] ?] ?] in wfΔ |- *; simpl; auto;
  depelim wfΔ.
  * apply unlift_TermTyp in l.
    intros n. rewrite extended_subst_length. rewrite lift_closed. fvs.
    rewrite (reln_lift 1 0).
    rewrite map_map_compose map_subst_lift1.
    autorewrite with len.
    constructor. apply IHΔ; auto.
  * intros n. rewrite reln_acc.
    simpl.
    rewrite reln_acc /= map_app app_nil_r.
    rewrite (reln_lift 1 0).
    rewrite map_map_compose map_subst_lift1.
    simpl. constructor. now apply IHΔ.
Qed.

Lemma spine_subst_smash_invE {cf : checker_flags} {Σ : global_env_ext} (Δ : context) :
  wfE Σ.1 ->
  wf_localE Σ Δ ->
  spine_substE Σ (smash_context [] Δ)
    (to_extended_list (smash_context [] Δ)) (extended_subst Δ 0) Δ.
Proof.
  move=> wfΣ wfΔ.
  split; auto.
  - eapply wf_local_smash_contextE; auto.
  - eapply PCUICWeakeningTypEta.weaken_wf_localE; auto. apply wf_local_smash_contextE; auto.
  - remember #|Δ| as n.
    rewrite /to_extended_list.
    rewrite -extended_subst_to_extended_list_k.
    eapply context_subst_to_extended_list_kE; eauto.
  - now apply PCUICInductivesEta.subslet_extended_substE.
Qed.

Lemma wf_projection_context_genE {cf:checker_flags} {Σ : global_env_ext} {mdecl ind idecl cdecl} :
  wfE Σ.1 ->
  declared_inductive Σ ind mdecl idecl ->
  on_projections mdecl (inductive_mind ind) (inductive_ind ind)
    idecl (ind_indices idecl) cdecl ->
  wf_localE (Σ.1, ind_universes mdecl) (projection_context_gen ind mdecl idecl).
Proof.
  intros wfΣ hdecl onps.
  pose proof (on_declared_inductiveE hdecl) as [onmib oib]; auto.
  have wfpars : wf_localE (Σ.1, ind_universes mdecl) (ind_params mdecl).
  { now apply onParams in onmib. }
  have wfsmpars : wf_localE (Σ.1, ind_universes mdecl) (smash_context [] (ind_params mdecl)).
  { now apply wf_local_smash_contextE. }
  constructor => //.
  eapply has_sort_isTypeRelE. 1: apply oib.(ind_relevance_compat).
  eapply PCUICSpineEta.type_mkAppsE. econstructor; eauto.
  eapply consistent_instance_ext_abstract_instanceE; eauto with pcuic.
  eapply declared_inductive_wf_global_extE; eauto with pcuic.
  set (u := abstract_instance (ind_universes mdecl)).
  destruct hdecl; eauto.
  have wfext : wf_ext_wkE (Σ.1, ind_universes mdecl).
  { eapply declared_inductive_wf_ext_wkE; eauto. eapply hdecl. }
  have X : isTypeE (Σ.1, ind_universes mdecl) []
    (it_mkProd_or_LetIn (ind_params mdecl ,,, ind_indices idecl) (tSort (ind_sort idecl))).
  { eapply isTypeRelE_isTypeE, (declared_inductive_arity_isTypeRelE (wfΣ := wfΣ) hdecl). }
  eapply (typing_spine_ind_typeE (Σ := (Σ.1, ind_universes mdecl)) hdecl); [exact wfsmpars| |].
  { eapply consistent_instance_ext_abstract_instanceE; eauto with pcuic.
    all: try (eapply declared_inductive_wf_global_extE; eauto with pcuic; eapply hdecl). }
  rewrite (isType_subst_instance_idE _ _ _ wfext X).
  rewrite it_mkProd_or_LetIn_app in X |- *.
  rewrite -(app_nil_r (to_extended_list _)).
  eapply typing_spine_it_mkProd_or_LetIn'E; auto.
  eapply spine_subst_smash_invE; tea.
  destruct onps. destruct (ind_indices idecl). cbn.
  eapply typing_spine_reflE. eapply isType_SortE; tea.
  now eapply on_inductive_sortE.
  now cbn in *.
  eapply isType_weakenE; auto; exact X.
Qed.

Lemma declared_constructor_wf_pars_argsE
  {cf:checker_flags} {Σ : global_env_ext} {ind i mdecl idecl cdecl} {wfΣ : wfE Σ.1} :
  declared_constructor Σ (ind, i) mdecl idecl cdecl ->
  wf_localE (Σ.1, ind_universes mdecl)
    (ind_params mdecl ,,, subst_context
    (inds (inductive_mind ind) (abstract_instance (ind_universes mdecl))
       (ind_bodies mdecl)) #|ind_params mdecl| (cstr_args cdecl)).
Proof.
  intros onc.
  epose proof (on_declared_constructorE onc) as [[onmib oib] [cs []]].
  eapply on_cargs in o.
  eapply sorts_local_ctx_wf_localE in o.
  2:{ eapply PCUICWeakeningTypEta.weaken_wf_localE => //.
      now eapply wf_arities_context'E.
      now eapply onParams in onmib. }
  rewrite -app_context_assoc -[_ ,,, _]app_context_nil_l app_context_assoc in o.
  eapply (substitution_wf_localE (Γ := [])) in o.
  2:eapply subslet_inds_genE, onc.
  rewrite app_context_nil_l in o.
  rewrite subst_context_app in o.
  rewrite PCUICSpine.closed_ctx_subst in o.
  eapply declared_inductive_closed_paramsE, onc.
  now rewrite Nat.add_0_r in o.
Qed.

Lemma wf_projection_arg_ctxE {cf:checker_flags} {Σ : global_env_ext} {mdecl ind idecl cdecl} :
  wfE Σ.1 ->
  declared_constructor Σ (ind, 0) mdecl idecl cdecl ->
  on_projections mdecl (inductive_mind ind) (inductive_ind ind)
    idecl (ind_indices idecl) cdecl ->
  forall k,
  wf_localE (Σ.1, ind_universes mdecl)
    (projection_context_gen ind mdecl idecl ,,, projection_arg_ctx ind mdecl cdecl k).
Proof.
  intros wfΣ decli onps k.
  rewrite /projection_arg_ctx.
  rewrite subst_context_lift_context_comm //.
  rewrite /projection_context_gen.
  eapply (weakening_wf_localE (Γ'' := [_])).
  2:eapply wf_projection_context_genE; tea. 2:apply decli.
  rewrite - !skipn_subst_context.
  eapply All_local_env_app_skipn.
  rewrite -(smash_context_subst []) /=.
  rewrite -(smash_context_subst []) /=.
  rewrite subst_context_nil.
  rewrite subst_context_extended_subst_expand.
  { eapply declared_constructor_wf_pars_argsE in decli.
    eapply closed_wf_localE in decli => //.
    rewrite closedn_ctx_app in decli.
    now move/andP: decli => []. }
  rewrite -(expand_lets_smash_context _ []).
  rewrite -smash_context_app_expand. eapply wf_local_smash_contextE.
  destruct onps.
  pose proof (on_declared_inductiveE decli) as [onmib oib]; auto.
  have onpars := onParams onmib.
  have oncstr := onConstructors oib.
  destruct (ind_ctors idecl) as [|? []] eqn:hctors; try discriminate.
  red in oncstr. depelim oncstr.
  depelim oncstr.
  now eapply declared_constructor_wf_pars_argsE.
Qed.

Lemma declared_projections_subslet_indE {cf:checker_flags} {Σ : global_env_ext} {mdecl ind idecl} :
  forall (wfΣ : wfE Σ.1) (Hdecl : declared_inductive Σ ind mdecl idecl),
  let u := abstract_instance (ind_universes mdecl) in
  let indb:= {|
          binder_name := nNamed (ind_name idecl);
          binder_relevance := ind_relevance idecl |} in
  forall c, ind_ctors idecl = [c] ->
  Alli (fun (i : nat) (_ : PCUICEnvironment.context_decl) =>
     ∑ pdecl, nth_error (ind_projs idecl) (context_assumptions (cstr_args c) - Datatypes.S i) =
            Some pdecl) 0 (smash_context [] (cstr_args c)) ->
  forall i: nat,
  let indsubst:= inds (inductive_mind ind)
                (abstract_instance (ind_universes mdecl))
                (ind_bodies mdecl) in
  forall (IH: forall i0 : nat,
       i0 < i ->
       forall x,
       nth_error (ind_projs idecl) i0 = Some x ->
      isTypeE (Σ.1, ind_universes mdecl)
           (smash_context [] (ind_params mdecl),,
            vass indb
              (mkApps (tInd ind (abstract_instance (ind_universes mdecl)))
                 (to_extended_list (smash_context [] (ind_params mdecl))))) x.(proj_type)
         × (∑ decl : PCUICEnvironment.context_decl,
              [× nth_error (smash_context [] (cstr_args c))
                  (context_assumptions (cstr_args c) - Datatypes.S i0) = Some decl,
                isTypeE (Σ.1, ind_universes mdecl)
                (arities_context (ind_bodies mdecl),,, ind_params mdecl,,,
                 skipn (context_assumptions (cstr_args c) - i0)
                   (smash_context [] (cstr_args c))) (decl_type decl),
                wf_localE (Σ.1, ind_universes mdecl)
                  (arities_context (ind_bodies mdecl),,, ind_params mdecl,,,
                   smash_context [] (cstr_args c)),
               projection_type mdecl ind i0 (decl_type decl) = x.(proj_type) &
               projection_type mdecl ind i0 (decl_type decl) =
               projection_type' mdecl ind i0 (decl_type decl)])),
  on_projections mdecl (inductive_mind ind) (inductive_ind ind)
    idecl (ind_indices idecl) c ->
  i <= context_assumptions (cstr_args c) ->
  context_assumptions (ind_params mdecl) = ind_npars mdecl ->
  #|ind_projs idecl| = context_assumptions (cstr_args c) ->
  wf_subsletE (Σ.1, ind_universes mdecl)
  (projection_context_gen ind mdecl idecl)
  (projs ind (ind_npars mdecl) i)
  (subst_context (extended_subst (ind_params mdecl) 0) 1
     (lift_context 1 0
        (subst_context indsubst #|ind_params mdecl|
           (skipn (context_assumptions (cstr_args c) - i)
              (smash_context [] (cstr_args c)))))).
Proof.
  intros.
  split.
  { eapply wf_projection_arg_ctxE; tea. split => //.
    now rewrite H. }
  induction i as [|i IHi].
  - rewrite Nat.sub_0_r.
    rewrite MRList.skipn_all2.
    autorewrite with len; simpl; auto.
    constructor.
  - forward IHi.
    intros. eapply IH. lia. auto.
    forward IHi by lia. simpl in IHi.
    destruct (skipn (context_assumptions (cstr_args c) - Datatypes.S i)
      (smash_context [] (cstr_args c))) eqn:eqargs.
    apply (f_equal (@Datatypes.length _)) in eqargs.
    autorewrite with len in eqargs.
    rewrite MRList.length_skipn in eqargs.
    autorewrite with len in eqargs. simpl in eqargs. lia.
    rewrite subst_context_snoc lift_context_snoc subst_context_snoc.
    simpl.
    destruct c0 as [? [] ?].
    * simpl in eqargs.
      pose proof (@smash_context_assumption_context [] (cstr_args c)).
      forward H3 by constructor.
      eapply assumption_context_skipn in H3.
      rewrite -> eqargs in H3. exfalso; inv H3.
    * apply skipn_eq_cons in eqargs as [Hnth eqargs].
      constructor.
      + replace (Datatypes.S (context_assumptions (cstr_args c) - (Datatypes.S i)))
          with (context_assumptions (cstr_args c) - i) in eqargs by lia.
        rewrite eqargs in IHi. cbn.
        apply IHi.
      + rewrite /lift_decl /=; len.
        specialize (IH i).
        forward IH by lia; len.
        eapply (f_equal (@Datatypes.length _)) in eqargs.
        rewrite MRList.length_skipn in eqargs.
        autorewrite with len in eqargs. simpl in eqargs.
        eapply nth_error_alli in X; eauto. simpl in X.
        destruct X as [pdecl Hnth'].
        replace ((context_assumptions (cstr_args c) -
          (Datatypes.S (context_assumptions (cstr_args c) - (Datatypes.S i)))))
          with i in eqargs, Hnth' by lia. rewrite -eqargs.
        rewrite /lift_decl /subst_decl. simpl; len.
        erewrite (commut_lift_subst_rec _ _ 1 (i + #|ind_params mdecl|) i).
        2:lia.
        specialize (IH _ Hnth').
        eapply meta_convE. econstructor.
        split; eauto. split; eauto. simpl.
        rewrite H //. split => //.
        apply Hnth'.
        eapply meta_convE. econstructor.
        destruct IH as [(_ & s & isTy & _) _].
        now eapply typingE_wf_local in isTy.
        simpl. reflexivity. simpl.
        rewrite lift_mkApps. simpl. destruct ind; simpl.
        reflexivity. autorewrite with len.
        simpl.
        rewrite context_assumptions_smash_context /= //.
        assert(subst_instance (abstract_instance (ind_universes mdecl)) pdecl.(proj_type) = pdecl.(proj_type)) as ->.
        { eapply (isType_subst_instance_idE (Σ.1, ind_universes mdecl)); eauto with pcuic.
          eapply declared_inductive_wf_ext_wkE; eauto with pcuic.
          destruct Hdecl; eauto. eapply IH.    }
        destruct IH as [isTy [decl [nthdecl _ _ eqpdecl ptyeq]]].
        move ptyeq at bottom.
        rewrite nthdecl in Hnth. noconf Hnth. simpl in ptyeq.
        rewrite -eqpdecl. simpl.
        rewrite ptyeq. unfold projection_type'.
        fold indsubst. destruct ind as [mind ind]; simpl in *.
        set (projsubst := projs {| inductive_mind := mind; inductive_ind := ind |} (ind_npars mdecl) i) in *.
        rewrite -eqpdecl in isTy.
        eapply isType_closedE in isTy.
        simpl in isTy. autorewrite with len in isTy. simpl in isTy.
        rewrite ptyeq in isTy.
        unfold projection_type' in isTy.
        erewrite (commut_lift_subst_rec _ _ 1 (i + #|ind_params mdecl|) i) in isTy by lia.
        erewrite (commut_lift_subst_rec _ _ 1 (i + #|ind_params mdecl|) i) by lia.
        rewrite (PCUICInductives.subst_id _ (({|
          decl_name := indb;
          decl_body := None;
          decl_type := mkApps
                        (tInd
                            {| inductive_mind := mind; inductive_ind := ind |}
                            u)
                        (to_extended_list
                            (smash_context [] (ind_params mdecl))) |}
          :: smash_context [] (ind_params mdecl)))).
        ++ simpl. autorewrite with len.
          rewrite context_assumptions_smash_context //.
        ++ constructor. apply smash_context_assumption_context; constructor.
        ++ unfold to_extended_list, to_extended_list_k.  simpl.
          rewrite -reln_lift /= (reln_acc [_]) rev_app_distr /= //.
        ++ now rewrite (Nat.add_1_r i).
Qed.

Lemma declared_projectionsE {cf:checker_flags} {Σ : global_env_ext} {mdecl ind idecl} :
  forall (wfΣ : wfE Σ.1) (Hdecl : declared_inductive Σ ind mdecl idecl),
  let u := abstract_instance (ind_universes mdecl) in
  match ind_ctors idecl return Type with
  | [cs] =>
    on_projections mdecl (inductive_mind ind) (inductive_ind ind)
      idecl (ind_indices idecl) cs ->
    Alli (fun i pdecl =>
    isTypeE (Σ.1, ind_universes mdecl) (projection_context_gen ind mdecl idecl) pdecl.(proj_type) *
      ∑ decl,
        [× nth_error (smash_context [] (cstr_args cs))
          (context_assumptions (cstr_args cs) - Datatypes.S i) = Some decl,
        isTypeE (Σ.1, ind_universes mdecl)
         (arities_context (ind_bodies mdecl),,, ind_params mdecl,,,
          skipn (context_assumptions (cstr_args cs) - i)
            (smash_context [] (cstr_args cs))) (decl_type decl),
        wf_localE (Σ.1, ind_universes mdecl)
          (arities_context (ind_bodies mdecl) ,,,
            ind_params mdecl ,,, smash_context [] (cstr_args cs)),
        (projection_type mdecl ind i decl.(decl_type) = pdecl.(proj_type)) &
        (projection_type mdecl ind i decl.(decl_type) =
            projection_type' mdecl ind  i decl.(decl_type))])%type
      0 (ind_projs idecl)
  | _ => True
  end.
Proof.
  intros wfΣ decli u.
  set oib := declared_inductive_invE weaken_env_prop_typingE wfΣ wfΣ decli.
  unfold projection_context_gen.
  set indb := {| binder_name := _ |}.
  destruct (ind_ctors idecl) as [|? []] eqn:Heq; try contradiction; auto.
  intros onps.
  eapply forall_nth_error_Alli.
  set (eos := CoreTactics.the_end_of_the_section).
  intros i. Subterm.rec_wf_rel IH i Peano.lt. clear eos.
  rename pr1 into i. simpl; clear H0.
  set (p := mkProjection ind (ind_npars mdecl) i).
  intros pdecl Hp. simpl.
  assert (hnth': nth_error (ind_ctors idecl) 0 = Some c) by
    (rewrite Heq //).
  set(isdecl := (conj (conj decli hnth') (conj Hp Logic.eq_refl)) :
      declared_projection Σ.1 p mdecl idecl c pdecl).
  destruct (on_declared_projectionE isdecl) as [oni onp].
  set (declared_inductive_invE _ _ _ _) as oib' in onp.
  change oib' with oib in *. clear oib'.
  simpl in onp.
  have onpars := onParams (declared_minductive_invE weaken_env_prop_typingE wfΣ wfΣ decli.p1).
  have parslen := onNpars (declared_minductive_invE weaken_env_prop_typingE wfΣ wfΣ decli.p1).
  simpl in onp.
  destruct onp as [[[wfargs onProjs] Hp2] onp].
  red in onp.
  destruct (nth_error (smash_context [] _) _) eqn:Heq'; try contradiction.
  destruct onp as [onna onp].
  rewrite {}onp.
  apply on_projections_decl in onps.
  assert(projslen : #|ind_projs idecl| = (context_assumptions (cstr_args c))).
  { now destruct onProjs. }
  assert (some_proj :#|ind_projs idecl| > 0).
  { destruct isdecl as [ [] []]. now apply nth_error_Some_length in H1. }
  simpl.
  assert (wfarities : wf_localE (Σ.1, ind_universes mdecl)
      (arities_context (ind_bodies mdecl))).
  { eapply wf_arities_contextE; eauto.
    destruct isdecl as [[[] ?] ?]; eauto. }
  destruct (ind_cunivs oib) as [|? []] eqn:hequ => //.
  eapply PCUICClosedConv.sorts_local_ctx_All_local_env in wfargs.
  2:{ eapply All_local_env_app; auto.
      red in onpars. eapply (All_local_env_impl _ _ _ onpars).
      intros. apply lift_typing_impl with (1 := X); intros ? Hs.
      eapply weaken_ctxE; auto. }
  pose proof wfargs as X.
  rewrite -(app_context_nil_l (arities_context _)) in X.
  rewrite -app_context_assoc in X.
  eapply (substitution_wf_localE (Γ := [])) in X; auto.
  2:{ eapply subslet_inds_genE; eauto. }
  rewrite app_context_nil_l in X.
  move: X.
  rewrite subst_context_app.
  rewrite (PCUICSpine.closed_ctx_subst _ _ (ind_params mdecl)).
  red in onpars. eapply closed_wf_localE; [|eauto]. auto.
  assert (parsu : subst_instance u (ind_params mdecl) = ind_params mdecl).
  { red in onpars. eapply (env_propE_wf_local subst_abstract_instance_idE (Σ.1, ind_universes mdecl)); eauto.
    eapply declared_inductive_wf_ext_wkE; eauto with pcuic.
    destruct decli; eauto. }
  assert (typeu : subst_instance u (ind_type idecl) = ind_type idecl).
  { eapply (subst_instance_ind_type_idE Σ.1); eauto. }
  assert (sortu : subst_instance u (ind_sort idecl) = ind_sort idecl).
  { apply (subst_instance_ind_sort_idE Σ mdecl ind idecl); eauto. }
  pose proof (spine_subst_to_extended_list_kE (Σ := (Σ.1, ind_universes mdecl))
    (Δ := ind_params mdecl) (Γ := [])).
  assert (wf_localE (Σ.1, ind_universes mdecl) (ind_params mdecl)). auto.
  forward X. rewrite app_context_nil_l; auto.
  rewrite app_context_nil_l in X.
  rewrite PCUICClosed.closed_ctx_lift in X.
  red in onpars. eapply closed_wf_localE; [|eauto]. auto.
  assert(wf_localE (Σ.1, ind_universes mdecl) (ind_params mdecl ,,
      vass {| binder_name := nNamed (ind_name idecl); binder_relevance := idecl.(ind_relevance) |}
      (mkApps (tInd ind u) (to_extended_list (ind_params mdecl))))).
  { constructor. auto. eapply has_sort_isTypeRelE.
    1: apply oib.(ind_relevance_compat).
    eapply PCUICSpineEta.type_mkAppsE. econstructor; eauto.
    destruct isdecl as []; eauto. subst u.
    eapply consistent_instance_ext_abstract_instanceE; eauto with pcuic.
    eapply declared_inductive_wf_global_extE; eauto with pcuic.
    destruct decli; eauto.
    have wfext : wf_ext_wkE (Σ.1, ind_universes mdecl).
    { eapply declared_inductive_wf_ext_wkE; eauto. eapply decli. }
    have X1 : isTypeE (Σ.1, ind_universes mdecl) []
      (it_mkProd_or_LetIn (ind_params mdecl) (it_mkProd_or_LetIn (ind_indices idecl) (tSort (ind_sort idecl))))@[u].
    { have h := oib.(onArityRed). eapply isTypeRelE_isTypeE in h.
      rewrite /u (isType_subst_instance_idE _ _ _ wfext h). exact h. }
    eapply (typing_spine_ind_typeE (Σ := (Σ.1, ind_universes mdecl)) decli); [assumption| |].
    { subst u. eapply consistent_instance_ext_abstract_instanceE; eauto with pcuic.
      all: try (eapply declared_inductive_wf_global_extE; eauto with pcuic; eapply decli). }
    rewrite it_mkProd_or_LetIn_app.
    rewrite subst_instance_it_mkProd_or_LetIn.
    rewrite -(app_nil_r (to_extended_list _)).
    eapply typing_spine_it_mkProd_or_LetIn'E ; auto.
    rewrite parsu. eapply X.
    constructor.
    cbn.
    eapply isType_it_mkProd_or_LetIn_substE.
    2:eapply X. eapply isType_weakenE => //.
    rewrite -parsu - !subst_instance_it_mkProd_or_LetIn /= //.
    eapply isType_SortE. 2:pcuic.
    eapply on_inductive_sortE; eauto.
    simpl in oib.
    pose proof (onProjs.(on_projs_noidx _ _ _ _ _ _)).
    destruct (ind_indices idecl); simpl in H; try discriminate.
    simpl. rewrite [subst_instance_sort _ _]sortu.
    eapply ws_cumul_pbE_Sort.
    now eapply wf_local_closed_contextE in X0.
    reflexivity.
    rewrite -subst_instance_it_mkProd_or_LetIn.
    eapply isType_weakenE => //; exact X1. }
  intros wf.
  generalize (weakening_wf_localE (Γ'':=[_]) wf X1).
  simpl; clear X1 wf.
  move/wf_local_smash_contextE => /=.
  rewrite smash_context_app /= smash_context_acc.

  set(indsubst := (inds (inductive_mind ind)
    (abstract_instance (PCUICEnvironment.ind_universes mdecl))
    (PCUICEnvironment.ind_bodies mdecl))) in *.
  set (projsubst :=  (projs {| inductive_mind := inductive_mind ind;
      inductive_ind := inductive_ind ind |}
    (PCUICEnvironment.ind_npars mdecl) i)) in *.
  rewrite lift_context_app. simpl.
  rewrite [subst_context _ _ (_ ++ _)]subst_context_app.
  rewrite PCUICLiftSubst.lift_context_length /=.
  simpl. unfold app_context. simpl.
  rewrite lift_context_snoc /= /lift_decl /map_decl /=.
  simpl. rewrite lift_mkApps. simpl.
  rewrite {3}/subst_context /fold_context_k /= /map_decl /= subst_mkApps /=.
  rewrite /to_extended_list PCUICSpine.lift_to_extended_list_k.
  rewrite extended_subst_to_extended_list_k.
  fold (to_extended_list (smash_context [] (ind_params mdecl))).
  intros wfl.
  rewrite PCUICClosed.closed_ctx_lift in wfl.
  { eapply closedn_smash_context.
    eapply closed_wf_localE in wfargs; auto.
    rewrite closedn_ctx_app in wfargs.
    simpl in wfargs; autorewrite with len in wfargs.
    move/andP: wfargs => [_ clargs].
    clear -isdecl wfΣ clargs.
    eapply (closedn_ctx_lift 1).
    rewrite Nat.add_0_r.
    eapply (closedn_ctx_subst 0 #|ind_params mdecl|).
    now unfold indsubst; rewrite inds_length.
    unfold indsubst.
    eapply closed_inds. }
  rewrite -app_assoc in wfl.
  apply All_local_env_app_inv in wfl as [wfctx wfsargs].
  rewrite smash_context_app in Heq'.
  rewrite smash_context_acc in Heq'.
  rewrite nth_error_app_lt in Heq'.
  autorewrite with len. lia.
  set (idx := context_assumptions (cstr_args c) - Datatypes.S i) in *.
  unshelve epose proof ((nth_error_Some' _ idx).2 _) as (c2 & hidx); cycle -1.
  eapply @All_local_env_nth_error with (n := idx) (2 := hidx) in wfsargs as onnth.
  2: autorewrite with len; simpl. 2: lia.
  simpl in onnth. red in onnth. cbn in onnth.
  assert(decl_body c2 = None).
  { apply nth_error_assumption_context in hidx; auto.
    rewrite /subst_context /lift_context.
    apply assumption_context_fold, smash_context_assumption_context. constructor. }
  rewrite H in onnth.
  destruct onnth as (_ & s & Hs & _).
  Ltac havefst H :=
    match goal with
    |- ?T × _ => have H : T; [|split => //]
    end.
  eapply (substitutionE (Σ := (Σ.1, ind_universes mdecl)) (Γ := _ :: _) (Γ' := skipn _ _) (s := projsubst) (Δ := []))
    in Hs; auto.
  2:{ subst projsubst.
    rewrite (smash_context_lift []).
    rewrite (smash_context_subst []).
    rewrite -(firstn_skipn (Datatypes.S idx) (smash_context [] (cstr_args c))).
    rewrite subst_context_app lift_context_app subst_context_app.
    len.
    rewrite skipn_all_app_eq.
    len.
    rewrite firstn_length_le; auto. rewrite smash_context_length.
    simpl. lia. destruct ind; cbn in *.
    replace (Datatypes.S idx) with (context_assumptions (cstr_args c) - i); try lia.
    eapply (declared_projections_subslet_indE wfΣ decli _ Heq onps i IH); tas. lia. }
  simpl in Hs.
  rewrite nth_error_subst_context in Heq'.
  autorewrite with len in Heq'. simpl in Heq'.
  epose proof (nth_error_lift_context_eq _ (smash_context [] (ind_params mdecl))).
  autorewrite with len in H0.
  erewrite H0 in Heq'. simpl in Heq'. clear H0.
  rewrite !option_map_two in Heq'.
  apply option_map_Some in Heq' as [arg [nthidx eq]].
  rewrite nth_error_subst_context in hidx.
  autorewrite with len in hidx. simpl in hidx.
  rewrite (smash_context_lift []) in hidx.
  rewrite (smash_context_subst []) in hidx.
  rewrite (nth_error_lift_context_eq _ [vass indb (mkApps (tInd ind u) [])]) in hidx.
  simpl in hidx. autorewrite with len in hidx.
  rewrite nth_error_subst_context in hidx. autorewrite with len in hidx.
  simpl in hidx.
  rewrite !option_map_two in hidx.
  assert(clarg : closedn (i + #|ind_params mdecl| + #|ind_bodies mdecl|) (decl_type arg)).
  { assert(wfargs' : wf_localE (Σ.1, ind_universes mdecl)
      (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,,
      smash_context [] (cstr_args c))).
    { apply All_local_env_app; auto.
      now apply All_local_env_app_inv in wfargs as [wfindpars wfargs].
      apply wf_local_rel_smash_contextE; auto. }
    eapply closed_wf_localE in wfargs'; auto.
    eapply (closedn_ctx_decl (n:=idx)) in wfargs'; eauto.
    2:{ rewrite nth_error_app_lt. autorewrite with len. simpl; lia.
        now eapply nthidx. }
    move/andP: wfargs' => [_ clty].
    eapply closed_upwards; eauto.
    autorewrite with len; simpl. simpl in idx. lia. }
  rewrite nthidx in hidx. simpl in hidx. noconf hidx. simpl in *.
  subst c0.
  destruct ind as [mind ind]; simpl in *.
  autorewrite with len. simpl.
  revert Hs.
  assert(context_assumptions (cstr_args c) - Datatypes.S idx = i) as -> by lia.
  intros Hs.
  assert (projection_type mdecl {| inductive_mind := mind; inductive_ind := ind |}
      i (decl_type arg) =
    projection_type' mdecl {| inductive_mind := mind; inductive_ind := ind |} i
        (decl_type arg)).
  { eapply nth_error_Some_length in nthidx.
    autorewrite with len in nthidx. simpl in nthidx.
    unfold projection_type, projection_type'. simpl.
    fold indsubst projsubst.
    rewrite distr_subst.
    f_equal.
    { clear. subst projsubst. induction i; simpl; auto.
      f_equal. auto. }
    rewrite /projsubst projs_length.
    replace (context_assumptions (cstr_args c) - Datatypes.S idx + 1) with
    (context_assumptions (cstr_args c) - idx) by lia.
    simpl in idx.
    epose proof (commut_lift_subst_rec _ _ 1 (i + ind_npars mdecl) i).
    rewrite -Nat.add_1_r Nat.add_assoc. erewrite <-H0. 2:lia.
    clear H0.
    epose proof (commut_lift_subst_rec _ _ 1 i i) as hs.
    rewrite Nat.add_1_r in hs. rewrite <- hs; try lia. clear hs. f_equal.
    rewrite distr_subst_rec.
    clear H.
    rewrite map_subst_closedn.
    rewrite -parslen.
    eapply closedn_extended_subst. eapply closed_wf_localE. 2:eauto. auto.
    f_equal. autorewrite with len.
    epose proof (commut_lift_subst_rec _ _ (ind_npars mdecl) (i + #|ind_params mdecl|)
      (i + #|ind_params mdecl|)) as hs.
    rewrite parslen. erewrite <-hs. 2:lia.
    rewrite lift_closed; auto.
    apply (closedn_subst _ 0).
    unfold indsubst.
    exact (@closed_inds {| inductive_mind := mind; inductive_ind := ind |} mdecl _).
    simpl. eapply subject_closedE in Hs.
    now rewrite /indsubst inds_length. }
  split.
  unfold projection_type in H0.
  rewrite H0. eapply has_sort_isTypeE; eauto.
  rewrite -/indb in Hs.
  rewrite /projection_type' -/indb -/indsubst -/projsubst.
  rewrite Nat.add_1_r in Hs. exact Hs.
  exists arg. split; auto.
  2:{ apply wf_local_smash_endE; auto. }
  eapply wf_local_smash_endE in wfargs.
  eapply All_local_env_app_skipn with (n:=context_assumptions (cstr_args c) - Datatypes.S i) in wfargs.
  epose proof (wf_local_nth_isTypeRelE (d:=arg) (n:=0) wfargs).
  rewrite skipn_app in X1.
  rewrite MRList.length_skipn in X1. len.
  rewrite nth_error_app_lt // in X1. rewrite MRList.length_skipn. len. len.
  rewrite MRList.nth_error_skipn Nat.add_0_r nthidx in X1.
  forward X1 by reflexivity.
  len in X1. rewrite /idx in X1.
  rewrite MRList.skipn_skipn in X1.
  assert (context_assumptions (cstr_args c) - Datatypes.S i + 1 =
    context_assumptions (cstr_args c) - i) by lia.
  rewrite H1 in X1.
  rewrite [skipn _ (_ ,,, _)]skipn_0_eq in X1.
  assert (context_assumptions (cstr_args c) > 0). lia. lia.
  apply isTypeRelE_isTypeE in X1.
  apply X1.
Qed.

Lemma declared_projections_subsletE {cf:checker_flags} {Σ : global_env_ext} {mdecl ind idecl} :
  forall (wfΣ : wfE Σ.1) (Hdecl : declared_inductive Σ ind mdecl idecl),
  let u := abstract_instance (ind_universes mdecl) in
  let indsubst:= inds (inductive_mind ind)
          (abstract_instance (ind_universes mdecl))
          (ind_bodies mdecl) in
  forall c, ind_ctors idecl = [c] ->
  on_projections mdecl (inductive_mind ind) (inductive_ind ind) idecl (ind_indices idecl) c ->
  forall i, i <= context_assumptions (cstr_args c) ->
  wf_subsletE (Σ.1, ind_universes mdecl)
    (projection_context_gen ind mdecl idecl)
    (projs ind (ind_npars mdecl) i)
    (subst_context (extended_subst (ind_params mdecl) 0) 1
      (lift_context 1 0
          (subst_context indsubst #|ind_params mdecl|
             (skipn (context_assumptions (cstr_args c) - i)
                (smash_context [] (cstr_args c)))))).
Proof.
  intros wfΣ decli u indsubst c hctors onps i hi.
  eapply declared_projections_subslet_indE; tea.
  now apply on_projections_decl in onps.
  intros.
  move: (declared_projectionsE wfΣ decli).
  rewrite hctors. intros IH. cbn in IH.
  forward IH by tas. eapply nth_error_alli in IH; tea.
  now cbn in IH.
  now rewrite (declared_minductive_ind_nparsE decli).
  eapply onps.
Qed.

Lemma declared_projection_typeE {cf:checker_flags} {Σ : global_env_ext} {mdecl idecl p cdecl pdecl} :
  wfE Σ.1 ->
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  let u := abstract_instance (ind_universes mdecl) in
  isTypeE (Σ.1, ind_universes mdecl)
    ((vass {| binder_name := nNamed idecl.(ind_name); binder_relevance := idecl.(ind_relevance) |} (mkApps (tInd p.(proj_ind) u)
          (to_extended_list (smash_context [] (ind_params mdecl)))))::
        smash_context [] (ind_params mdecl)) pdecl.(proj_type).
Proof.
  intros wfΣ declp.
  destruct (on_declared_projectionE declp) as [oni onp].
  specialize (declared_projectionsE wfΣ (let (x , _) := declp in x.p1)).
  set(oib := declared_inductive_invE _ _ _ _) in *.
  intros onprojs u.
  clearbody oib.
  simpl in *.
  destruct oni.
  destruct (ind_ctors idecl) as [|? []] => //.
  destruct onp as [[[? ?] ?] ?].
  destruct (ind_cunivs oib) as [|? []] => //.
  forward onprojs. noconf e. intuition auto.
  destruct declp as [decli [Hnth Hpars]].
  eapply nth_error_alli in onprojs; eauto.
  simpl in onprojs. intuition auto.
Qed.

Lemma declared_projection_type_and_eqE {cf:checker_flags} {Σ : global_env_ext} {mdecl idecl p cdecl pdecl} :
  forall (wfΣ : wfE Σ.1) (Hdecl : declared_projection Σ p mdecl idecl cdecl pdecl),
  let u := abstract_instance (ind_universes mdecl) in
  (ind_ctors idecl = [cdecl]) *
  isTypeE (Σ.1, ind_universes mdecl)
    ((vass {| binder_name := nNamed idecl.(ind_name); binder_relevance := idecl.(ind_relevance) |}
      (mkApps (tInd p.(proj_ind) u)
          (to_extended_list (smash_context [] (ind_params mdecl)))))::
      smash_context [] (ind_params mdecl)) pdecl.(proj_type) *
  ∑ decl,
    [× nth_error (smash_context [] (cstr_args cdecl))
      (context_assumptions (cstr_args cdecl) - Datatypes.S p.(proj_arg)) = Some decl,
      isTypeE (Σ.1, ind_universes mdecl)
        (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,,
          skipn (context_assumptions (cstr_args cdecl) - p.(proj_arg))
            (smash_context [] (cstr_args cdecl))) decl.(decl_type),
      (wf_localE (Σ.1, ind_universes mdecl)
        (arities_context (ind_bodies mdecl) ,,,
          ind_params mdecl ,,, smash_context [] (cstr_args cdecl))),
      (projection_type mdecl p.(proj_ind) p.(proj_arg) decl.(decl_type) = pdecl.(proj_type)) &
      (projection_type mdecl p.(proj_ind) p.(proj_arg) decl.(decl_type) =
        projection_type' mdecl p.(proj_ind) p.(proj_arg) decl.(decl_type))%type].
Proof.
  intros wfΣ declp.
  destruct (on_declared_projectionE declp) as [oni onp].
  specialize (declared_projectionsE wfΣ (let (x, _) := declp in x.p1)).
  set(oib := declared_inductive_invE _ _ _ _) in *.
  intros onprojs u.
  clearbody oib.
  destruct oni.
  destruct (ind_ctors idecl) as [|? []] => //. noconf e.
  destruct onp as [[[? ?] ?] ?].
  set (cu := ind_cunivs _) in y.
  destruct cu as [|? []] in y => //. simpl in *.
  forward onprojs. intuition auto.
  destruct declp as [decli [Hnth Hpars]].
  eapply nth_error_alli in onprojs; eauto.
  simpl in onprojs. intuition auto.
Qed.

Lemma type_local_ctx_cumE {cf:checker_flags} {Σ Γ Δ s s'} :
  wfE Σ.1 -> wf_sort Σ s' ->
  leq_sort (global_ext_constraints Σ) s s' ->
  type_local_ctx (PCUICTyping.lift_typing typingE) Σ Γ Δ s ->
  type_local_ctx (PCUICTyping.lift_typing typingE) Σ Γ Δ s'.
Proof.
  intros wfΣ wfs leqs.
  induction Δ as [|[na [b|] ty] Δ]; simpl; auto;
  intros []; split; auto.
  destruct l as (_ & ss & Hs & <- & Her).
  split; cbn; eexists; split; [|split; eauto using leq_relevance].
  eapply typeE_Cumul; eauto.
  econstructor; pcuic.
  now eapply cumulE_Sort.
Qed.

Lemma type_local_ctx_wfE {cf:checker_flags} {Σ Γ Δ s} :
  wfE Σ.1 ->
  type_local_ctx (PCUICTyping.lift_typing typingE) Σ Γ Δ s ->
  wf_sort Σ s.
Proof.
  intros wfΣ.
  induction Δ as [|[na [b|] ty] Δ]; simpl; intuition auto.
Qed.

Lemma isType_it_mkProd_or_LetInE {cf:checker_flags} Σ Γ Δ s s':
  wfE Σ.1 ->
  wf_localE Σ Γ ->
  type_local_ctx (PCUICTyping.lift_typing typingE) Σ Γ Δ s ->
  wf_sort Σ s' ->
  isTypeE Σ Γ (it_mkProd_or_LetIn Δ (tSort s')).
Proof.
  move=> wfΣ wfΓ wfΔ wfs.
  eapply isType_introE.
  eapply type_it_mkProd_or_LetInE. 2:tea.
  eapply type_local_ctx_wfE; eauto.
  econstructor; pcuic.
  eapply type_local_ctx_All_local_env; eauto.
Qed.

Lemma isType_it_mkProd_or_LetIn_smashE {cf:checker_flags} Σ Γ Δ s :
  wfE Σ.1 ->
  isTypeE Σ Γ (it_mkProd_or_LetIn Δ (tSort s)) ->
  isTypeE Σ Γ (it_mkProd_or_LetIn (smash_context [] Δ) (tSort s)).
Proof.
  intros wfΣ HT.
  apply lift_sorting_it_impl_gen with HT => // Hu. set (u := HT.2.π1) in *; clearbody u. clear HT.
  revert Γ u Hu.
  induction Δ as [|[na [b|] ty] Δ] using ctx_length_rev_ind; simpl in *; auto;
  rewrite !it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=; rewrite smash_context_app; intros Γ u Hu.
  - simpl.
    assert (wfu := PCUICWfUniversesEta.typing_wf_sortE wfΣ Hu).
    eapply inversion_LetInE in Hu as (T & wfty & HT & hlt); auto.
    eapply substitution_letE in HT; auto.
    rewrite /subst1 subst_it_mkProd_or_LetIn /= in HT.
    specialize (X (subst_context [b] 0 Δ) ltac:(autorewrite with len; lia)).
    eapply ws_cumul_pbE_LetIn_l_inv in hlt; eauto.
    eapply type_ws_cumul_pbE in HT. 3:eauto.
    2:{ eapply isType_SortE. all: pcuic. }
    specialize (X _ _ HT).
    now rewrite -smash_context_subst /= subst_context_nil.
  - simpl. rewrite it_mkProd_or_LetIn_app. simpl.
    assert (wfu := PCUICWfUniversesEta.typing_wf_sortE wfΣ Hu).
    eapply inversion_ProdE in Hu as (s1 & s2 & wfty & Ht & hlt); auto.
    specialize (X Δ ltac:(reflexivity)).
    specialize (X _ _ Ht).
    eapply type_ws_cumul_pbE; eauto.
    econstructor; tas. apply unlift_TypUniv in wfty.
    eapply isType_introE. econstructor; pcuic.
Qed.

Lemma typing_spine_to_extended_listE {cf:checker_flags} Σ Δ u s :
  wfE Σ.1 ->
  isTypeE Σ [] (subst_instance u (it_mkProd_or_LetIn Δ (tSort s))) ->
  PCUICAritiesEta.typing_spineE Σ (smash_context [] (subst_instance u Δ))
    (subst_instance u (it_mkProd_or_LetIn Δ (tSort s)))
    (to_extended_list (smash_context [] (subst_instance u Δ)))
    (tSort (subst_instance_sort u s)).
Proof.
  move=> wfΣ wfΔ.
  apply wf_arity_spine_typing_spineE; auto.
  rewrite subst_instance_it_mkProd_or_LetIn in wfΔ |- *.
  split.
  eapply isType_weakenE; auto.
  eapply wf_local_smash_contextE; pcuic.
  now eapply isType_it_mkProd_or_LetIn_wf_localE in wfΔ; auto; rewrite app_context_nil_l in wfΔ.
  rewrite -(app_nil_r (to_extended_list (smash_context [] (subst_instance u Δ)))).
  eapply arity_spine_it_mkProd_or_LetInE; auto.
  2:{ constructor. }
  eapply spine_subst_smash_invE; eauto.
  eapply isType_it_mkProd_or_LetIn_invE in wfΔ; pcuic.
  rewrite app_context_nil_l in wfΔ.
  now eapply isType_wf_localE.
Qed.

Lemma wf_projection_contextE {cf:checker_flags} (Σ : global_env_ext) {mdecl idecl p cdecl pdecl u} :
  wfE Σ.1 ->
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_localE Σ (projection_context p.(proj_ind) mdecl idecl u).
Proof.
  move=> wfΣ decli.
  pose proof (on_declared_projectionE decli) as [[onmind eqctr] onind].
  set (oib := declared_inductive_invE _ _ _ _) in *. clearbody oib.
  simpl in onind; destruct ind_ctors as [|? []] => //. noconf eqctr.
  destruct onind as [[[_ onps] Hpe] onp].
  move=> cu.
  assert(wfparams : wf_localE Σ (subst_instance u (ind_params mdecl))).
  { eapply on_minductive_wf_paramsE; eauto. eapply decli. }
  assert(wfsmash : wf_localE Σ (smash_context [] (subst_instance u (ind_params mdecl)))).
  { eapply wf_local_smash_contextE; auto. }
  constructor; auto. red.
  eapply has_sort_isTypeRelE with (s := subst_instance_sort u (ind_sort idecl)).
  1: rewrite relevance_subst_eq; apply oib.(ind_relevance_compat).
  eapply PCUICSpineEta.type_mkAppsE. econstructor; eauto. eapply decli.p1.
  eapply (typing_spine_ind_typeE decli); [exact wfsmash|exact cu|].
  rewrite it_mkProd_or_LetIn_app.
  pose proof (on_projs_noidx _ _ _ _ _ _ onps).
  destruct (ind_indices idecl) eqn:eqind; try discriminate.
  simpl.
  eapply typing_spine_to_extended_listE; eauto.
  pose proof (on_inductive_instE decli _ u localenv_nil).
  rewrite eqind in X. simpl in X.
  eapply isTypeRelE_isTypeE.
  now rewrite subst_instance_it_mkProd_or_LetIn.
Qed.

Lemma invert_type_mkApps_indE {cf:checker_flags} Σ Γ ind u args T mdecl idecl :
  wfE Σ.1 ->
  declared_inductive Σ.1 ind mdecl idecl ->
  Σ ;;; Γ |-E mkApps (tInd ind u) args : T ->
  (PCUICAritiesEta.typing_spineE Σ Γ (subst_instance u (ind_type idecl)) args T)
  * consistent_instance_ext Σ (ind_universes mdecl) u.
Proof.
  intros wfΣ decli.
  intros H; dependent induction H; solve_discr.
  - destruct args using rev_case; solve_discr. noconf H2.
    rewrite mkApps_app in H2. simpl in H2.
    noconf H2. clear IHtypingE1 IHtypingE3.
    specialize (IHtypingE2 _ _ _ _ _ _ _ wfΣ decli Logic.eq_refl) as [IH cu];
      split; auto.
    destruct (on_declared_inductiveE decli) as [onmind oib].
    eapply typing_spine_appE; eauto.
  - unshelve epose proof (d' := declared_inductive_to_gen d);
    unshelve epose proof (decli' := declared_inductive_to_gen decli); eauto.
    destruct (declared_inductive_inj d' decli') as [-> ->].
    clear decli. split; auto.
    destruct (on_declared_inductiveE d) as [onmind oib].
    pose proof (oib.(onArity)) as ar.
    apply typing_spine_reflE.
    exact (declared_inductive_valid_typeE d _ _ a c).
  - specialize (IHtypingE1 _ _ wfΣ decli) as [IH cu]; split; auto.
    eapply typing_spine_weaken_conclE; tea.
    + match goal with
      | c : cumulSpecE _ _ ?A ?B, hA : typingE _ _ _ ?A, hB : typingE _ _ ?B (tSort _)
        |- ws_cumul_pbE _ _ _ ?A ?B =>
        exact (into_ws_cumul_pbE_spec c (typing_closed_contextE hA) (type_is_open_termE hA)
                 (subject_is_open_termE hB))
      end.
    + eapply has_sort_isTypeE; tea.
Qed.

Lemma isType_mkApps_Ind_invE {cf:checker_flags} {Σ Γ ind u args} (wfΣ : wfE Σ.1)
  {mdecl idecl} (declm : declared_inductive Σ.1 ind mdecl idecl) :
  wf_localE Σ Γ ->
  isTypeE Σ Γ (mkApps (tInd ind u) args) ->
  ∑ parsubst argsubst,
    let parctx := (subst_instance u (ind_params mdecl)) in
    let argctx := (subst_context parsubst 0 (subst_instance u (idecl.(ind_indices)))) in
    [× spine_substE Σ Γ (firstn (ind_npars mdecl) args) parsubst parctx,
      spine_substE Σ Γ (skipn (ind_npars mdecl) args) argsubst argctx,
      #|firstn (ind_npars mdecl) args| = ind_npars mdecl,
      #|skipn (ind_npars mdecl) args| = context_assumptions idecl.(ind_indices) &
      consistent_instance_ext Σ (ind_universes mdecl) u].
Proof.
  move=> wfΓ isTypeE.
  destruct isTypeE as (_ & s & Hs & _).
  eapply invert_type_mkApps_indE in Hs as [tyargs cu]; eauto.
  set (decli' := on_declared_inductiveE declm).
  rename declm into decli.
  destruct decli' as [declm decli'].
  eapply (typing_spine_ind_type_invE decli) in tyargs; tea.
  rewrite it_mkProd_or_LetIn_app in tyargs.
  pose proof (decli'.(onArityRed)) as ar.
  destruct ar as (_ & s' & ar & _). cbn in ar.
  rewrite !subst_instance_it_mkProd_or_LetIn in tyargs.
  simpl in tyargs. rewrite -it_mkProd_or_LetIn_app in tyargs.
  eapply arity_typing_spineE in tyargs as [argslen leqs [instsubst [wfdom wfcodom cs subs]]] => //.
  apply context_subst_app in cs as [argsubst parsubst].
  eexists _, _. move=> parctx argctx.
  rewrite context_assumptions_subst_instance in argsubst, parsubst.
  rewrite declm.(onNpars) in argsubst, parsubst.
  eapply subslet_app_invE in subs as [subp suba].
  rewrite subst_instance_length in subp, suba.
  subst parctx argctx.
  repeat split; eauto; rewrite ?subst_instance_length => //.
  rewrite app_context_assoc in wfcodom. now apply All_local_env_app_inv in wfcodom as [? ?].
  simpl.
  eapply substitution_wf_localE; eauto. now rewrite app_context_assoc in wfcodom.
  rewrite !lengths in argslen.
  move: (context_subst_length2 parsubst).
  now rewrite !lengths (declared_minductive_ind_nparsE decli).
  move: (context_subst_length2 argsubst).
  now rewrite !lengths.
Qed.

Lemma isType_mkApps_Ind_inv'E {cf:checker_flags} {Σ Γ ind u args} (wfΣ : wfE Σ.1)
  {mdecl idecl} (declm : declared_inductive Σ.1 ind mdecl idecl) :
  wf_localE Σ Γ ->
  isTypeE Σ Γ (mkApps (tInd ind u) args) ->
  ∑ pars indices parsubst argsubst,
    let parctx := (subst_instance u (ind_params mdecl)) in
    let argctx := (subst_context parsubst 0 (subst_instance u (idecl.(ind_indices)))) in
    [× args = pars ++ indices,
      spine_substE Σ Γ pars parsubst parctx,
      spine_substE Σ Γ indices argsubst argctx,
      #|pars| = ind_npars mdecl,
      #|indices| = context_assumptions idecl.(ind_indices) &
      consistent_instance_ext Σ (ind_universes mdecl) u].
Proof.
  move=> wfΓ isTypeE.
  destruct isTypeE as (_ & s & Hs & _).
  eapply invert_type_mkApps_indE in Hs as [tyargs cu]; eauto.
  set (decli' := on_declared_inductiveE declm).
  rename declm into decli.
  destruct decli' as [declm decli'].
  eapply (typing_spine_ind_type_invE decli) in tyargs; tea.
  rewrite it_mkProd_or_LetIn_app in tyargs.
  pose proof (decli'.(onArityRed)) as ar.
  destruct ar as (_ & s' & ar & _). cbn in ar.
  rewrite !subst_instance_it_mkProd_or_LetIn in tyargs.
  simpl in tyargs. rewrite -it_mkProd_or_LetIn_app in tyargs.
  eapply arity_typing_spineE in tyargs as [argslen leqs [instsubst [wfdom wfcodom cs subs]]] => //.
  apply context_subst_app in cs as [argsubst parsubst].
  eexists (firstn (ind_npars mdecl) args), (skipn (ind_npars mdecl) args), _, _.
  move=> parctx argctx.
  rewrite context_assumptions_subst_instance in argsubst, parsubst.
  rewrite declm.(onNpars) in argsubst, parsubst.
  eapply subslet_app_invE in subs as [subp suba].
  rewrite subst_instance_length in subp, suba.
  subst parctx argctx.
  repeat split; eauto; rewrite ?subst_instance_length => //.
  now rewrite firstn_skipn.
  rewrite app_context_assoc in wfcodom. now apply All_local_env_app_inv in wfcodom as [? ?].
  simpl.
  eapply substitution_wf_localE; eauto. now rewrite app_context_assoc in wfcodom.
  rewrite !lengths in argslen.
  move: (context_subst_length2 parsubst).
  now rewrite !lengths (declared_minductive_ind_nparsE decli).
  move: (context_subst_length2 argsubst).
  now rewrite !lengths.
Qed.

Lemma projection_subsletE {cf:checker_flags} Σ Γ mdecl idecl u c p cdecl pdecl args :
  declared_projection Σ.1 p mdecl idecl cdecl pdecl ->
  wfE Σ.1 ->
  Σ ;;; Γ |-E c : mkApps (tInd p.(proj_ind) u) args ->
  isTypeE Σ Γ (mkApps (tInd p.(proj_ind) u) args) ->
  subsletE Σ Γ (c :: List.rev args) (projection_context p.(proj_ind) mdecl idecl u).
Proof.
  intros declp wfΣ Hc Ha.
  destruct (on_declared_projectionE declp) as [[onind eqctr] y].
  destruct (isType_mkApps_Ind_invE wfΣ (let (x, _) := declp in x.p1) (typingE_wf_local Hc) Ha) as
    [parsubst [argsubst [sppars spargs cu]]].
  unfold projection_context.
  set (oib := declared_inductive_invE _ _ _ _) in *. clearbody oib.
  simpl in y.
  destruct (ind_ctors idecl) as [|ctors []] => //. noconf eqctr.
  destruct y as [[[_ onps] ?] ?].
  pose proof (on_projs_noidx _ _ _ _ _ _ onps).
  pose proof (onNpars onind).
  pose proof (context_subst_length2 spargs).
  rewrite context_assumptions_fold in H1.
  autorewrite with len in H1.
  destruct (ind_indices idecl); try discriminate.
  simpl in H1. rewrite List.length_skipn in H1.
  assert(#|args| = ind_npars mdecl).
  { pose proof (context_subst_length2 sppars).
    autorewrite with len in H2.
    rewrite H0 in H2.
    apply firstn_length_le_inv in H2. lia. }
  rewrite -H2 in sppars.
  rewrite firstn_all in sppars.
  eapply spine_subst_smashE in sppars; auto.
  constructor. apply sppars.
  rewrite subst_mkApps /=.
  rewrite /argsubst in H1.
  now rewrite (spine_subst_subst_to_extended_list_kE sppars).
Qed.

Lemma red_it_mkProd_or_LetIn_smashE {cf} {Σ} {wfΣ : wfE Σ} Γ ctx t u n c :
  Σ ;;; Γ ⊢ it_mkProd_or_LetIn ctx t ⇝ u ->
  nth_error (List.rev (smash_context [] ctx)) n = Some c ->
  ∑ ctx' t' d,
    [× (decompose_prod_assum [] u = (ctx', t')),
       (nth_error (List.rev (smash_context [] ctx')) n = Some d) &
        Σ ;;; Γ ,,, skipn (#|smash_context [] ctx| - n) (smash_context [] ctx) ⊢ decl_type c ⇝ decl_type d ].
Proof. intros; eapply red_it_mkProd_or_LetIn_smash_cb; tea; typeclasses eauto. Qed.

Lemma red_it_mkProd_or_LetIn_mkApps_IndE {cf} {Σ} {wfΣ : wfE Σ} {Γ ctx ind u args v} :
  Σ ;;; Γ ⊢ it_mkProd_or_LetIn ctx (mkApps (tInd ind u) args) ⇝ v ->
  ∑ ctx' args', v = it_mkProd_or_LetIn ctx' (mkApps (tInd ind u) args').
Proof. intros; eapply red_it_mkProd_or_LetIn_mkApps_Ind_cb; tea; typeclasses eauto. Qed.

(** * Lifting a reduction of a (co)fixpoint's recursive argument type to its whole type

  A checker finds the inductive of a fixpoint's recursive argument by reducing that
  argument's type in its own context, and the inductive of a cofixpoint by reducing
  the conclusion of its type. The lemmas below turn such a reduction into a reduction
  of the whole declared type whose [check_one_fix] / [check_one_cofix] gives the
  inductive block. *)

(** The closed-reduction form of base [red_it_mkProd_or_LetIn_assum_nth]. *)
Lemma closed_red_it_mkProd_or_LetIn_assum_nthE {cf} {Σ} {wfΣ : wfE Σ} Γ sctx T n c A' :
  assumption_context sctx ->
  is_open_term Γ (it_mkProd_or_LetIn sctx T) ->
  nth_error (List.rev sctx) n = Some c ->
  Σ ;;; Γ ,,, skipn (#|sctx| - n) sctx ⊢ decl_type c ⇝ A' ->
  ∑ sctx',
    [× assumption_context sctx',
       #|sctx'| = #|sctx|,
       nth_error (List.rev sctx') n = Some (vass (decl_name c) A'),
       (forall i, i <> n -> nth_error (List.rev sctx') i = nth_error (List.rev sctx) i) &
       Σ ;;; Γ ⊢ it_mkProd_or_LetIn sctx T ⇝ it_mkProd_or_LetIn sctx' T].
Proof.
  intros ass op hnth hred.
  have clΓ : is_closed_context Γ.
  { move: (clrel_ctx hred). rewrite on_free_vars_ctx_app => /andP[] //. }
  destruct (red_it_mkProd_or_LetIn_assum_nth (Σ := Σ) Γ sctx T n c A' ass hnth (clrel_rel hred))
    as [sctx' [ass' hlen hnth' hother r]].
  exists sctx'; split; try assumption.
  now apply into_closed_red.
Qed.

(** A type reduces to the product over its smashed context. *)
Lemma red_it_mkProd_or_LetIn_to_smashE {cf} {Σ} {wfΣ : wfE Σ} Γ Δ T :
  is_closed_context Γ ->
  is_open_term Γ (it_mkProd_or_LetIn Δ T) ->
  Σ ;;; Γ ⊢ it_mkProd_or_LetIn Δ T ⇝ it_mkProd_or_LetIn (smash_context [] Δ) (expand_lets Δ T).
Proof.
  intros clΓ clt.
  eapply into_closed_red => //.
  clear clΓ clt.
  induction Δ in Γ, T |- * using ctx_length_rev_ind; simpl; auto.
  - rewrite expand_lets_nil. reflexivity.
  - rewrite smash_context_app_expand /=.
    destruct d as [na [b|] ty].
    * rewrite expand_lets_vdef {1}it_mkProd_or_LetIn_app /= subst_context_nil app_context_nil_l.
      rewrite expand_lets_smash_context /= expand_lets_k_ctx_nil.
      rewrite /expand_lets_ctx /expand_lets_k_ctx /= subst_empty lift0_id lift0_context.
      rewrite /mkProd_or_LetIn /=.
      etransitivity.
      + eapply red1_red, red_zeta.
      + rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r.
        now eapply X; len.
    * rewrite expand_lets_vass it_mkProd_or_LetIn_app /=.
      rewrite it_mkProd_or_LetIn_app /=.
      eapply red_prod. reflexivity.
      rewrite expand_lets_smash_context /= expand_lets_k_ctx_nil.
      rewrite expand_lets_ctx_assumption_context. repeat constructor.
      now eapply X.
Qed.

(** The fixpoint lift: a reduction of the recursive argument's type, in its own context,
    to an applied inductive gives a reduct of the declared type on which [check_one_fix]
    finds that inductive's block. *)
Lemma red_rec_arg_check_one_fixE {cf} {Σ} {wfΣ : wfE Σ} Γ d ctx concl c ind u args :
  is_open_term Γ (dtype d) ->
  decompose_prod_assum [] (dtype d) = (ctx, concl) ->
  nth_error (List.rev (smash_context [] ctx)) (rarg d) = Some c ->
  Σ ;;; Γ ,,, skipn (#|smash_context [] ctx| - rarg d) (smash_context [] ctx) ⊢
    decl_type c ⇝ mkApps (tInd ind u) args ->
  has_rec_arg d ×
  ∑ ty, (Σ ;;; Γ ⊢ dtype d ⇝ ty) × (check_one_fix (def_with_type d ty) = Some (inductive_mind ind)).
Proof.
  intros op decomp hnth hred.
  have clΓ : is_closed_context Γ.
  { move: (clrel_ctx hred). rewrite on_free_vars_ctx_app => /andP[] //. }
  have eqty := decompose_prod_assum_it_mkProd_or_LetIn _ _ _ _ decomp.
  cbn in eqty.
  have r1 : Σ ;;; Γ ⊢ dtype d ⇝ it_mkProd_or_LetIn (smash_context [] ctx) (expand_lets ctx concl).
  { rewrite eqty. apply red_it_mkProd_or_LetIn_to_smashE => //. now rewrite -eqty. }
  have ass : assumption_context (smash_context [] ctx).
  { apply smash_context_assumption_context; constructor. }
  destruct (closed_red_it_mkProd_or_LetIn_assum_nthE Γ _ _ _ _ _ ass (closed_red_open_right_cb r1) hnth hred)
    as [sctx' [ass' hlen hnth' _ r2]].
  split.
  - have hlt := nth_error_Some_length hnth. rewrite List.length_rev smash_context_length /= in hlt.
    rewrite /has_rec_arg decomp /=. now apply Nat.ltb_lt.
  - exists (it_mkProd_or_LetIn sctx' (expand_lets ctx concl)). split.
    + now transitivity (it_mkProd_or_LetIn (smash_context [] ctx) (expand_lets ctx concl)).
    + eapply check_one_fix_it_mkProd_or_LetIn_assum; [exact ass'|exact hnth'|reflexivity].
Qed.

Lemma wf_local_expand_letsE {cf} {Σ} {wfΣ : wfE Σ} {Γ Δ Γ'} :
  wf_localE Σ (Γ ,,, Δ ,,, Γ') ->
  wf_localE Σ (Γ ,,, smash_context [] Δ ,,, expand_lets_ctx Δ Γ').
Proof.
  intros hwf.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  destruct (All_local_env_app_inv hwf) as [wfΓΔ _].
  rewrite -app_context_assoc in hwf.
  eapply (weakening_wf_localE (Γ'' := smash_context [] Δ)) in hwf.
  len in hwf. simpl in hwf. simpl.
  2:{ eapply wf_local_smash_endE; pcuic. }
  rewrite lift_context_app app_context_assoc Nat.add_0_r in hwf.
  eapply substitution_wf_localE in hwf; tea.
  now eapply PCUICContextsEta.subslet_extended_substE.
Qed.

Lemma typing_expand_lets_genE {cf} {Σ} {wfΣ : wfE Σ} {Γ Δ Γ' t T} :
  Σ ;;; Γ ,,, Δ ,,, Γ' |-E t : T ->
  Σ ;;; Γ ,,, smash_context [] Δ ,,, expand_lets_ctx Δ Γ' |-E
    expand_lets_k Δ #|Γ'| t : expand_lets_k Δ #|Γ'| T.
Proof.
  intros Ht.
  rewrite /expand_lets /expand_lets_k.
  pose proof (typingE_wf_local Ht).
  rewrite -app_context_assoc in Ht.
  eapply (weakening_typingE (Γ'' := smash_context [] Δ)) in Ht.
  len in Ht. simpl in Ht. simpl.
  2:{ eapply wf_local_smash_endE; pcuic. now apply All_local_env_app_inv in X. }
  rewrite lift_context_app app_context_assoc Nat.add_0_r in Ht.
  eapply substitutionE in Ht; tea.
  2:{ eapply PCUICContextsEta.subslet_extended_substE. now apply All_local_env_app_inv in X. }
  now len in Ht.
Qed.

Lemma map_subst_let_expand_k_to_extended_list_liftE {cf} {Σ s Γ Δ k} :
  spine_substE Σ Γ s (List.rev s) (smash_context [] Δ) ->
  ListDef.map (subst_let_expand_k (List.rev s) Δ k) (to_extended_list_k Δ k) = ListDef.map (lift0 k) s.
Proof.
  intros sp.
  eapply spine_subst_subst_to_extended_list_kE in sp.
  rewrite /subst_let_expand_k.
  rewrite -map_map_compose.
  rewrite expand_lets_k_to_extended_list_k.
  rewrite -{2}(Nat.add_0_r k).
  rewrite PCUICLiftSubst.lift_to_extended_list_k -{2}sp !map_map_compose.
  apply MRList.map_ext. intros x.
  now rewrite commut_lift_subst_rec.
Qed.

Lemma map_subst_let_expand_to_extended_listE {cf} {Σ s Γ Δ} :
  spine_substE Σ Γ s (List.rev s) (smash_context [] Δ) ->
  ListDef.map (subst_let_expand (List.rev s) Δ) (to_extended_list Δ) = s.
Proof.
  intros sp.
  specialize (map_subst_let_expand_k_to_extended_list_liftE (k:=0) sp).
  now rewrite map_lift0.
Qed.

Lemma subslet_smash_contextE {cf} {Σ} {wfΣ : wfE Σ} {Γ Δ Γ' Δ' s} :
  subsletE Σ (Γ ,,, Δ ,,, Γ') s Δ' ->
  subsletE Σ (Γ ,,, smash_context [] Δ ,,, expand_lets_ctx Δ Γ')
    (ListDef.map (expand_lets_k Δ #|Γ'|) s) (expand_lets_k_ctx Δ #|Γ'| Δ').
Proof.
  induction 1.
  * simpl. constructor.
  * simpl. rewrite /expand_lets_k_ctx lift_context_snoc subst_context_snoc.
    constructor. apply IHX. len.
    rewrite Nat.add_assoc. fold (expand_lets_k Δ (#|Δ0| + #|Γ'|) T).
    eapply typing_expand_lets_genE in t0.
    rewrite expand_lets_k_subst_comm in t0.
    now rewrite -(subslet_lengthE X).
  * simpl. rewrite /expand_lets_k_ctx lift_context_snoc subst_context_snoc.
    len. rewrite /subst_decl /lift_decl /map_decl /=.
    eapply subslet_defE. apply IHX. len.
    rewrite !Nat.add_assoc.
    fold (expand_lets_k Δ (#|Δ0| + #|Γ'|) t).
    fold (expand_lets_k Δ (#|Δ0| + #|Γ'|) T).
    eapply typing_expand_lets_genE in t0.
    rewrite !expand_lets_k_subst_comm in t0.
    now rewrite -(subslet_lengthE X).
    now rewrite expand_lets_k_subst_comm -(subslet_lengthE X) Nat.add_assoc.
Qed.

Lemma spine_subst_expand_letsE {cf Σ} {wfΣ : wfE Σ} {Γ Δ Γ'} {inst s Δ'} :
  spine_substE Σ (Γ ,,, Δ ,,, Γ') inst s Δ' ->
  spine_substE Σ (Γ ,,, smash_context [] Δ ,,, expand_lets_ctx Δ Γ')
    (ListDef.map (expand_lets_k Δ #|Γ'|) inst) (ListDef.map (expand_lets_k Δ #|Γ'|) s)
    (expand_lets_k_ctx Δ #|Γ'| Δ').
Proof.
  intros [].
  split.
  * rewrite -app_context_assoc.
    rewrite smash_context_app_expand_acc.
    eapply All_local_env_app_inv in spine_dom_wfE as [wfΔ wfΓ'].
    eapply All_local_env_app. now apply All_local_env_app_inv in wfΔ.
    eapply wf_local_rel_smash_context_genE; tea.
  * eapply All_local_env_app_inv in spine_codom_wfE as [wfΔ wfΓ'].
    rewrite - !app_context_assoc -expand_lets_ctx_app.
    apply All_local_env_app_inv in wfΔ as [].
    eapply All_local_env_app.
    now apply All_local_env_app_inv in a as [].
    rewrite smash_context_app_expand_acc.
    apply wf_local_rel_smash_context_genE; tea.
    eapply All_local_rel_app; tea.
  * rewrite /expand_lets_k_ctx /expand_lets_k -map_map_compose -[ListDef.map (fun t => _) s]map_map_compose.
    eapply subst_context_subst.
    now eapply lift_context_subst.
  * now eapply subslet_smash_contextE.
Qed.

(* We show that the derived predicate of a case is always well-typed, for *any*
  instance of the parameters (not just the ones from a well-formed predicate). *)
Lemma wf_ind_predicateE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ} {ci : case_info}
  {mdecl idecl} u :
  wf_localE Σ Γ ->
  declared_inductive Σ ci mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_localE Σ (Γ ,,, smash_context [] (ind_params mdecl)@[u] ,,, (ind_predicate_context ci mdecl idecl)@[u]).
Proof.
  move=> wfΓ isdecl cu.
  rewrite /pre_case_predicate_context_gen /inst_case_context /ind_predicate_context /=.
  set (iass := {| decl_name := _ |}).
  cbn.
  rewrite [subst_instance_context _ _]subst_instance_expand_lets_ctx.
  unshelve epose proof (on_inductive_instE isdecl _ _ _ cu); tea.
  rewrite -/(subst_context_let_expand _ _ _).
  rewrite subst_instance_app_ctx in X.
  destruct X as (_ & s & Hs & _ & Her).
  eapply type_it_mkProd_or_LetIn_invE in Hs as (idxs & inds & [sortsidx sortind leq]).
  set (idxctx := smash_context [] (ind_params mdecl)@[u] ,,, expand_lets_ctx (ind_params mdecl)@[u] (ind_indices idecl)@[u]) in *.
  have tyass : Σ ;;; Γ ,,, idxctx |-E (decl_type iass)@[u] : tSort (ind_sort idecl)@[u].
  { pose proof (on_inductive_sort_instE isdecl _ cu).
    rewrite /iass /=.
    have wfidxctx : wf_localE Σ (Γ ,,, idxctx).
    { rewrite /idxctx. rewrite app_context_assoc.
      apply wf_local_expand_letsE. rewrite -app_context_assoc.
      eapply PCUICWeakeningTypEta.weaken_wf_localE => //. rewrite -subst_instance_app_ctx.
      eapply on_minductive_wf_params_indices_instE; tea.
    }
    generalize wfidxctx. rewrite {1}/idxctx {1}app_context_assoc => wfidxctx'.
    rewrite subst_instance_mkApps /=; cbn.
    erewrite subst_instance_id_mdecl; tea.
    have isTyar : isTypeE Σ (Γ ,,, idxctx)
      (subst_instance u (it_mkProd_or_LetIn (ind_params mdecl ,,, ind_indices idecl) (tSort (ind_sort idecl))))
      by eapply isType_ind_arity_instE; tea.
    eapply pre_type_mkApps_arityE.
    { eapply (type_ws_cumul_pbE (pb := Conv)); [econstructor; tea|exact isTyar|].
      now eapply declared_inductive_type_ws_cumulE. }
    { exact isTyar. }
    rewrite it_mkProd_or_LetIn_app !subst_instance_it_mkProd_or_LetIn
      subst_instance_to_extended_list subst_instance_app_ctx
      subst_instance_smash.
    rewrite /to_extended_list to_extended_list_k_app.
    rewrite Nat.add_0_r. len.
    eapply arity_spine_it_mkProd_or_LetIn_smashE.
    - rewrite -(PCUICClosed.closed_ctx_lift #|ind_indices idecl| 0 (ind_params mdecl)@[u]).
      { rewrite closedn_subst_instance_context.
        eapply (declared_inductive_closed_paramsE isdecl). }
      rewrite (smash_context_lift []).
      rewrite /idxctx app_context_assoc.
      rewrite to_extended_list_k_lift_context.
      replace #|ind_indices idecl| with (#|ind_indices idecl| + 0) by lia.
      rewrite PCUICLiftSubst.lift_to_extended_list_k Nat.add_0_r.
      rewrite -List.map_rev.
      relativize #|ind_indices idecl|.
      eapply subslet_liftE; tea => //; len. 2:len.
      epose proof (spine_subst_to_extended_list_kE (Γ := Γ) (Δ := smash_context [] (ind_params mdecl)@[u])); tea.
      forward X.
      { apply wf_local_smash_endE, PCUICWeakeningTypEta.weaken_wf_localE => //. eapply (on_minductive_wf_paramsE isdecl); tea. }
      destruct X. len in inst_subsletE.
      rewrite PCUICClosed.closed_ctx_lift in inst_subsletE => //.
      apply closedn_smash_context.
      rewrite closedn_subst_instance_context.
      apply (declared_inductive_closed_paramsE isdecl).
      rewrite all_rels_smash in inst_subsletE.
      { apply smash_context_assumption_context. constructor. }
      apply inst_subsletE.
    - have clpars : closed_ctx (ind_params mdecl).
      { apply (declared_inductive_closed_paramsE isdecl). }
      have clinds : closedn_ctx #|(ind_params mdecl)| (ind_indices idecl)@[u].
      { epose proof (declared_inductive_closed_pars_indicesE isdecl).
        len. rewrite closedn_subst_instance_context.
        rewrite closedn_ctx_app in H0. now move/andP: H0. }
      rewrite PCUICInductives.subst_let_expand_it_mkProd_or_LetIn /=. simpl.
      eapply arity_spine_it_mkProd_or_LetIn_SortE => //. reflexivity.
      rewrite /subst_context_let_expand.
      relativize (subst_context _ _ _).
      rewrite /idxctx app_context_assoc.
      rewrite subst_instance_expand_lets_ctx.
      eapply spine_subst_to_extended_list_kE => //; len.
      rewrite distr_lift_subst_context PCUICClosed.closed_ctx_lift //.
      rewrite PCUICClosed.closed_ctx_lift //; len. cbn. len.
      rewrite PCUICClosed.closed_ctx_lift //.
      rewrite subst_map_lift_lift_context; len => //.
      rewrite -extended_subst_to_extended_list_k -List.map_rev.
      replace #|ind_indices idecl| with (#|ind_indices idecl| + 0) by len.
      rewrite PCUICLiftSubst.lift_to_extended_list_k Nat.add_0_r.
      rewrite -List.map_rev map_map_compose.
      setoid_rewrite subst_lift_subst.
      rewrite -map_map_compose List.map_rev extended_subst_to_extended_list_k List.map_rev
         -PCUICLiftSubst.lift_to_extended_list_k Nat.add_0_r
         -subst_context_map_subst_expand_lets; len.
      rewrite subst_extended_lift //; len. now rewrite closedn_subst_instance_context.
      rewrite (lift_extended_subst _ #|ind_indices _|) subst_map_lift_lift_context; len. }
  constructor => //.
  2:{ eapply has_sort_isTypeRelE.
    2: rewrite /idxctx app_context_assoc in tyass; tea.
    rewrite relevance_subst_eq.
    pose proof (on_declared_inductiveE isdecl) as [onmind oib]. apply oib.(ind_relevance_compat). }
  apply typingE_wf_local in tyass.
  rewrite /idxctx app_context_assoc in tyass => //.
Qed.

(* We show that the derived predicate of a case is always well-typed, for *any*
  instance of the parameters (not just the ones from a well-formed predicate). *)
Lemma isType_case_predicateE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ} {ci : case_info}
  {mdecl idecl} u params ps :
  wf_localE Σ Γ ->
  declared_inductive Σ ci mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_sort Σ ps ->
  spine_substE Σ Γ params (List.rev params) (smash_context [] (subst_instance u (ind_params mdecl))) ->
  isTypeE Σ Γ
    (it_mkProd_or_LetIn
      (pre_case_predicate_context_gen ci mdecl idecl params u)
      (tSort ps)).
Proof.
  move=> wfΓ isdecl cu wfps sp.
  pose proof (on_declared_inductiveE isdecl) as [onmind oib].
  rewrite /pre_case_predicate_context_gen /inst_case_context /ind_predicate_context /=.
  set (iass := {| decl_name := _ |}).
  cbn.
  rewrite [ListDef.map (map_decl _) _]subst_instance_expand_lets_ctx.
  rewrite subst_context_snoc /=. len.
  unshelve epose proof (on_inductive_instE isdecl _ _ _ cu); tea.
  rewrite -/(subst_context_let_expand _ _ _).
  rewrite subst_instance_app_ctx in X.
  destruct X as (_ & s & Hs & _).
  eapply isType_it_mkProd_or_LetIn_appE in Hs.
  2:eapply sp.
  rewrite PCUICInductives.subst_let_expand_it_mkProd_or_LetIn in Hs.
  eapply type_it_mkProd_or_LetIn_invE in Hs as (idxs & inds & [sortsidx sortind leq]).
  eapply has_sort_isTypeE with (s := sort_of_products (subst_instance u (ind_sort idecl) :: idxs)
    (Sort.super ps)).
  set (idxctx := subst_context_let_expand _ _ _) in *.
  have tyass : Σ ;;; Γ ,,, idxctx |-E
    subst (List.rev params) #|ind_indices idecl| (decl_type iass)@[u] : tSort (ind_sort idecl)@[u].
  { pose proof (on_inductive_sort_instE isdecl _ cu).
    rewrite /iass /=.
    have wfidxctx : wf_localE Σ (Γ ,,, idxctx) by pcuic.
    rewrite subst_instance_mkApps /=; cbn.
    erewrite subst_instance_id_mdecl; tea.
    rewrite subst_mkApps. cbn.
    have isTyar : isTypeE Σ (Γ ,,, idxctx)
      (subst_instance u (it_mkProd_or_LetIn (ind_params mdecl ,,, ind_indices idecl) (tSort (ind_sort idecl))))
      by eapply isType_ind_arity_instE; tea.
    eapply pre_type_mkApps_arityE.
    { eapply (type_ws_cumul_pbE (pb := Conv)); [econstructor; tea|exact isTyar|].
      now eapply declared_inductive_type_ws_cumulE. }
    { exact isTyar. }
    rewrite it_mkProd_or_LetIn_app !subst_instance_it_mkProd_or_LetIn
      subst_instance_to_extended_list subst_instance_app_ctx
      subst_instance_smash.
    (* rewrite -it_mkProd_or_LetIn_app. *)
    rewrite /to_extended_list to_extended_list_k_app.
    rewrite map_app Nat.add_0_r. len.
    eapply arity_spine_it_mkProd_or_LetIn_smashE.
    erewrite subst_to_extended_list_k.
    2:{ eapply make_context_subst_spec_inv.
        rewrite List.rev_involutive. cbn.
        eapply sp. }
    len.
    rewrite -(PCUICClosed.closed_ctx_lift #|ind_indices idecl| 0 (ind_params mdecl)@[u]).
    { rewrite closedn_subst_instance_context.
      eapply (declared_inductive_closed_paramsE isdecl). }
    rewrite (smash_context_lift []) -List.map_rev.
    relativize #|ind_indices idecl|.
    eapply subslet_liftE; tea.
    apply sp. len.
    rewrite PCUICInductives.subst_let_expand_it_mkProd_or_LetIn /=.
    eapply arity_spine_it_mkProd_or_LetIn_SortE => //. reflexivity.
    rewrite -subst_instance_to_extended_list_k.
    rewrite /expand_lets_ctx /expand_lets_k_ctx.
    rewrite to_extended_list_k_subst to_extended_list_k_lift_context.
    rewrite PCUICContexts.map_subst_instance_to_extended_list_k.
    rewrite -to_extended_list_k_map_subst. lia.
    relativize (subst_context_let_expand (List.rev (ListDef.map _ _)) _ _).
    relativize (to_extended_list_k _ _).
    eapply spine_subst_to_extended_list_kE; tea.
    rewrite [reln [] _ _]to_extended_list_subst_context_let_expand.
    apply PCUICLiftSubst.map_subst_instance_to_extended_list_k.
    rewrite subst_context_let_expand_length subst_instance_length.
    rewrite /subst_context_let_expand.
    rewrite distr_lift_subst_context List.map_rev.
    rewrite PCUICClosed.closed_ctx_lift //.
    pose proof (PCUICContextSubst.context_subst_length2 sp).
    rewrite context_assumptions_smash_context /= in H0. len in H0. len.
    rewrite H0.
    relativize (context_assumptions _).
    eapply (PCUICClosed.closedn_ctx_expand_lets 0); len.
    rewrite closedn_subst_instance_context.
    apply (declared_inductive_closed_paramsE isdecl).
    2:len.
    epose proof (declared_inductive_closed_pars_indicesE isdecl).
    rewrite closedn_ctx_app in H1.
    rewrite closedn_subst_instance_context.
    move/andP: H1 => [] //.
    f_equal. f_equal.
    erewrite subst_to_extended_list_k => //.
    eapply make_context_subst_spec_inv. rewrite List.rev_involutive. cbn. apply sp. }
  set (sdecl := subst_decl _ _ _).
  rewrite -(it_mkProd_or_LetIn_app [sdecl]).
  eapply type_it_mkProd_or_LetIn_sortsE; tea.
  constructor => //. repeat (eexists; tea). apply relevance_subst, oib.(ind_relevance_compat).
  constructor => //. simpl.
  constructor => //.
  now eapply sorts_local_ctx_wf_localE; tea.
  repeat (eexists; tea).
  apply relevance_subst, oib.(ind_relevance_compat).
Qed.

Lemma arity_spine_case_predicateE {cf: checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ} {ci : case_info}
  {mdecl idecl} {u params indices ps} {c} :
  wf_localE Σ Γ ->
  declared_inductive Σ ci mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_sort Σ ps ->
  spine_substE Σ Γ params (List.rev params)
    (smash_context [] (subst_instance u (ind_params mdecl))) ->
  spine_substE Σ Γ indices (List.rev indices)
    (subst_context_let_expand (List.rev params)
        (subst_instance u (ind_params mdecl))
        (smash_context [] (subst_instance u (ind_indices idecl)))) ->
  Σ ;;; Γ |-E c : mkApps (tInd ci u) (params ++ indices) ->
  arity_spineE Σ Γ
    (it_mkProd_or_LetIn
      (pre_case_predicate_context_gen ci mdecl idecl params u)
      (tSort ps))
    (indices ++ [c]) (tSort ps).
Proof.
  move=> wfΓ isdecl cu wfps sppars spidx Hc.
  rewrite /pre_case_predicate_context_gen /inst_case_context /ind_predicate_context.
  rewrite subst_instance_cons subst_instance_expand_lets_ctx.
  rewrite subst_context_snoc /=. len.
  eapply arity_spine_it_mkProd_or_LetIn_smashE; tea.
  rewrite (smash_context_subst []).
  rewrite /subst_context_let_expand (expand_lets_smash_context _ [])
    expand_lets_k_ctx_nil /= in spidx; cbn.
  apply spidx. rewrite subst_let_expand_tProd /=.
  constructor.
  2:econstructor.
  set (ictx := subst_instance u _).
  eapply meta_convE; tea.
  rewrite subst_instance_mkApps subst_mkApps /=.
  erewrite subst_instance_id_mdecl; tea.
  rewrite subst_let_expand_mkApps subst_let_expand_tInd.
  f_equal.
  rewrite !subst_instance_to_extended_list subst_instance_app_ctx.
  rewrite /to_extended_list to_extended_list_k_app !map_app. f_equal.
  len.
  erewrite subst_to_extended_list_k => //.
  2:{ eapply make_context_subst_spec_inv. rewrite List.rev_involutive.
      rewrite subst_instance_smash.
      eapply sppars. }
  rewrite -{1}[params](List.map_id params).
  rewrite map_map_compose; eapply MRList.map_ext => x.
  setoid_rewrite subst_let_expand_lift_id; auto.
  now rewrite /ictx; len.
  rewrite /ictx /expand_lets_ctx /expand_lets_k_ctx; len.
  pose proof (PCUICContextSubst.context_subst_length2 spidx).
  rewrite /subst_context_let_expand in H. now len in H.
  (* Should be a lemma *)
  rewrite -subst_context_map_subst_expand_lets.
  rewrite /ictx; len.
  pose proof (PCUICContextSubst.context_subst_length2 sppars).
  now rewrite context_assumptions_smash_context /= in H; len in H.
  rewrite /subst_let_expand /expand_lets /expand_lets_k.
  rewrite -map_map_compose.
  rewrite -{1}(spine_subst_subst_to_extended_list_kE spidx).
  f_equal. len.
  rewrite to_extended_list_k_subst /expand_lets_ctx /expand_lets_k_ctx.
  rewrite !to_extended_list_k_subst to_extended_list_k_lift_context.
  rewrite -map_map_compose. simpl. len.
  set (ctx := subst_context _ _ _).
  rewrite -subst_instance_to_extended_list_k.
  rewrite to_extended_list_k_subst to_extended_list_k_lift_context.
  rewrite PCUICContexts.map_subst_instance_to_extended_list_k.
  rewrite -to_extended_list_k_map_subst. lia.
  relativize (context_assumptions (ind_indices idecl)).
  relativize #|ind_indices idecl|.
  relativize (to_extended_list_k (ind_indices idecl) _).
  erewrite map_subst_extended_subst_lift_to_extended_list_k => //.
  rewrite -(subst_instance_smash _ _ []).
  rewrite /ctx. rewrite (smash_context_subst []).
  rewrite /to_extended_list to_extended_list_k_subst //.
  rewrite subst_instance_smash //.
  rewrite /ctx /to_extended_list to_extended_list_k_subst.
  now rewrite PCUICLiftSubst.map_subst_instance_to_extended_list_k. len.
  len.
Qed.

Lemma inductive_ind_ind_bodies_lengthE `{cf:checker_flags}
  Σ ind mib oib
  (wfΣ : wfE Σ)
  (inddecl: declared_inductive Σ ind mib oib) :
  inductive_ind ind < #|ind_bodies mib|.
Proof.
  unshelve eapply declared_inductive_to_gen in inddecl; eauto.
  move: (declared_inductive_lookup_gen inddecl).
  rewrite /lookup_inductive /lookup_inductive_gen (PCUICLookup.declared_minductive_lookup_gen (PCUICGlobalEnv.declared_inductive_minductive inddecl)).
  remember (nth_error _ _) as o eqn:eo; symmetry in eo.
  move: o eo=> [io|] // /nth_error_Some_length //.
Qed.
