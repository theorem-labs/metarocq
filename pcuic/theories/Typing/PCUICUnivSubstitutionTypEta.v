(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect CRelationClasses.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Universes uGraph.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICOnFreeVars
     PCUICLiftSubst PCUICEquality PCUICUnivSubst
     PCUICCases PCUICCumulativity PCUICTyping PCUICReduction PCUICWeakeningEnv PCUICWeakeningEnvTyp
     PCUICClosed PCUICPosition PCUICGuardCondition PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
     PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICCumulativitySpecEtaClosure
     PCUICTypingEta PCUICTypingEtaInd PCUICWeakeningEnvTypEta PCUICTypingEtaNotions.

From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

(** * Universe substitution for typing derivations over [typingE]

  The E copy of [Typing/PCUICUnivSubstitutionTyp]. Each lemma of the base file
  that mentions typing, cumulativity, [wf_local] or [wf] is copied, and its
  statement is the base statement with only the relations renamed: [typing] →
  [typingE], [wf_local] → [wf_localE], [wf] → [wfE], [wf_ext] → [wf_extE],
  [cumulSpec0] → [cumulSpecE0], [conv_witness] → [conv_witnessE], [env_prop] →
  [env_propE], [isType]/[isTypeRel] → [isTypeE]/[isTypeRelE]
  ([PCUICTypingEtaNotions]), [wf_ext_wk] → [wf_ext_wkE], [wf_global_ext] →
  [wf_global_extE].

  Copied (the E name is the base name with the suffix [E]):
  [conv_decls_subst_instanceE], [cumul_decls_subst_instanceE],
  [conv_ctx_subst_instanceE], [subst_instance_ws_cumul_ctx_pbE_rel],
  [subst_instance_mfix_on_indE], [typing_subst_instanceE],
  [typing_subst_instance'E], [typing_subst_instance_wf_localE],
  [typing_subst_instance''E], [typing_subst_instance_ctxE],
  [typing_subst_instance_declE], [wf_local_instantiate_polyE],
  [wf_local_instantiateE], [lift_typing_subst_instance_declE],
  [isType_subst_instance_declE], [isTypeRel_subst_instance_declE],
  [wf_local_subst_instanceE], [wf_local_subst_instance_declE],
  [isTypeRel_subst_instance_idE], [isType_subst_instance_idE],
  [subst_instance_ind_sort_idE], [subst_instance_ind_type_idE].

  [subst_instance_ws_cumul_ctx_pbE_rel] here is the twin of this base file's
  [subst_instance_ws_cumul_ctx_pb_rel], over cumulative contexts. It is a
  different lemma from [PCUICWsCumulEtaCtx.subst_instance_ws_cumul_ctx_pbE_rel],
  the twin of [PCUICConversion.subst_instance_ws_cumul_ctx_pb_rel], exactly as the
  two base lemmas of that name are different.

  Not copied: [cumulSpec_subst_instance] and [convSpec_subst_instance], whose
  twins [cumulSpecE_subst_instance] and [convSpecE_subst_instance] are in
  [PCUICCumulativitySpecEtaClosure]; [compare_sort_subst_instance],
  [subst_instance_prim_type], [subst_instance_prim_val_tag] and
  [isArity_subst_instance], which mention none of the relations and are used from
  the base file.

  The base proofs use lemmas of [Conversion/PCUICUnivSubstitutionConv] that take
  [wf], [wf_ext_wk] or a typing derivation. Their E twins are copied in the first
  section, by the same rule: [wf_ext_wkE] and [wf_global_extE] (definitions),
  [wf_ext_wkE_wf], [not_var_global_levelsE], [not_var_global_ext_levelsE],
  [levels_global_constraintE], [levels_global_ext_constraintE],
  [monomorphic_global_constraintE], [monomorphic_global_constraint_extE],
  [consistent_ext_trans_polymorphic_case_auxE],
  [consistent_ext_trans_polymorphic_casesE], [consistent_ext_transE],
  [consistent_instance_valid_constraintsE], [All_local_env_over_subst_instanceE],
  [in_var_global_extE], [wf_universe_subst_instanceE], [wf_sort_subst_instanceE],
  [declared_inductive_wf_ext_wkE], [declared_inductive_wf_global_extE],
  [consistent_instance_ext_subst_absE], [in_global_ext_subst_abs_levelE],
  [consistent_instance_ext_subst_abs_univE], [consistent_instance_ext_subst_abs_indsE],
  [subst_abstract_instance_idE], [typed_subst_abstract_instanceE]. The other
  lemmas of that file are used from it. *)

Implicit Types (cf : checker_flags).

Local Set Keyed Unification.

Set Default Goal Selector "!".

Local Ltac aa := rdest; eauto with univ_subst.

(** ** E twins of the environment lemmas of [Conversion/PCUICUnivSubstitutionConv] *)

Lemma not_var_global_levelsE {cf : checker_flags} {Σ} (hΣ : wfE Σ) :
  LS.For_all (negb ∘ Level.is_var) (global_levels Σ).
Proof.
  destruct hΣ as [onu ond]. apply onu.
Qed.

Definition wf_ext_wkE {cf : checker_flags} (Σ : global_env_ext)
  := wfE Σ.1 × on_udecl_prop Σ.1 Σ.2.

Lemma wf_ext_wkE_wf {cf:checker_flags} Σ : wf_ext_wkE Σ -> wfE Σ.
Proof. intro H; apply H. Qed.

#[global]
Hint Resolve wf_ext_wkE_wf : core.

Lemma not_var_global_ext_levelsE {cf : checker_flags} Σ (hΣ : wf_ext_wkE (Σ, Monomorphic_ctx)) :
  LS.For_all (negb ∘ Level.is_var) (global_ext_levels (Σ, Monomorphic_ctx)).
Proof. apply hΣ. Qed.

Lemma levels_global_constraintE {cf : checker_flags} Σ (hΣ : wfE Σ) c :
  CS.In c (global_constraints Σ)
  -> LS.In c.1.1 (global_levels Σ)
    /\ LS.In c.2 (global_levels Σ).
Proof.
  intros inc.
  destruct hΣ. destruct o. specialize (H c inc).
  destruct c as [[l eq] r]; apply H.
Qed.

Lemma levels_global_ext_constraintE {cf : checker_flags} Σ φ (hΣ : wf_ext_wkE (Σ, φ)) c :
  CS.In c (global_ext_constraints (Σ, φ))
  -> LS.In c.1.1 (global_ext_levels (Σ, φ))
    /\ LS.In c.2 (global_ext_levels (Σ, φ)).
Proof.
  intro H. apply CS.union_spec in H; simpl in H.
  destruct hΣ as [hΣ Hφ], H as [Hc|H]; simpl in *.
  - red in Hφ. unfold global_ext_levels. simpl.
    destruct c as [[l1 c] l2]; exact (Hφ _ Hc).
  - apply levels_global_constraintE in H; tas.
    split; apply LS.union_spec; right; apply H.
Qed.

Lemma monomorphic_global_constraintE {cf : checker_flags} Σ (hΣ : wfE Σ) c :
  CS.In c (global_constraints Σ)
  -> is_monomorphic_cstr c.
Proof.
  intros H. apply levels_global_constraintE in H; tas.
  apply andb_and. split; destruct H as [H1 H2].
  - now apply not_var_global_levelsE in H1.
  - now apply not_var_global_levelsE in H2.
Qed.

Lemma monomorphic_global_constraint_extE {cf : checker_flags} Σ
      (hΣ : wf_ext_wkE (Σ, Monomorphic_ctx)) c :
  CS.In c (global_ext_constraints (Σ, Monomorphic_ctx))
  -> is_monomorphic_cstr c.
Proof.
  intros H. apply levels_global_ext_constraintE in H; tas.
  apply andb_and. split; destruct H as [H1 H2].
  - now apply not_var_global_ext_levelsE in H1.
  - now apply not_var_global_ext_levelsE in H2.
Qed.

#[global] Hint Resolve monomorphic_global_constraintE monomorphic_global_constraint_extE
  : univ_subst.

Lemma consistent_ext_trans_polymorphic_case_auxE {cf : checker_flags} {Σ φ1 φ2 φ' udecl inst inst'} :
  wf_ext_wkE (Σ, Polymorphic_ctx (φ1, φ2)) ->
  valid_constraints0 (global_ext_constraints (Σ, Polymorphic_ctx (φ1, φ2)))
                     (subst_instance_cstrs inst udecl) ->
  valid_constraints0 (global_ext_constraints (Σ, φ'))
                     (subst_instance_cstrs inst' φ2) ->
  valid_constraints0 (global_ext_constraints (Σ, φ'))
                     (subst_instance_cstrs
                        (subst_instance inst' inst) udecl).
Proof.
  intros [HΣ Hφ] H3 H2.
  intros v Hv. rewrite <- subst_instance_cstrs_two.
  apply satisfies_subst_instance_ctr; tas. apply H3.
  apply satisfies_union; simpl. split.
  - apply satisfies_subst_instance_ctr; auto.
  - apply satisfies_subst_instance_ctr; tas.
    rewrite equal_subst_instance_cstrs_mono; aa.
    apply satisfies_union in Hv. apply Hv.
Qed.

Lemma consistent_ext_trans_polymorphic_casesE {cf : checker_flags} Σ φ φ' udecl inst inst' :
  wf_ext_wkE (Σ, φ) ->
  consistent_instance_ext (Σ, φ) (Polymorphic_ctx udecl) inst ->
  consistent_instance_ext (Σ, φ') φ inst' ->
  consistent_instance_ext (Σ, φ') (Polymorphic_ctx udecl)
                          (subst_instance inst' inst).
Proof.
  intros HΣφ [H [H0 H1]] H2.
  repeat split.
  2: now rewrite subst_instance_instance_length.
  + rewrite forallb_map. apply forallb_forall.
    intros l Hl.
    eapply forallb_forall in H; tea. clear -H H2 Hl.
    apply LevelSet_mem_union in H. destruct H as [H|H].
    2: { destruct l; simpl; try (apply LevelSet_mem_union; right; assumption).
         apply consistent_instance_declared in H2.
         apply (forallb_nth' n Level.lzero) in H2.
         destruct H2 as [[? [H2 ?]]|H2]; rewrite H2; tas.
         apply LS.mem_spec, global_ext_levels_InSet. }
    *  destruct l; simpl.
       -- apply LS.mem_spec, global_ext_levels_InSet.
       -- apply LS.mem_spec in H.
          destruct φ as [|[φ1 φ2]]; simpl in *.
          { now apply LevelSetFact.empty_iff in H. }
          now apply monomorphic_level_notin_AUContext in H.
       -- apply consistent_instance_declared in H2.
          apply (forallb_nth' n Level.lzero) in H2.
          destruct H2 as [[? [H2 ?]]|H2]; rewrite H2; tas.
          apply LS.mem_spec, global_ext_levels_InSet.
  + unfold consistent_instance_ext, consistent_instance in H2.
    unfold valid_constraints in *; destruct check_univs; [|trivial].
    destruct φ as [|[φ1 φ2]]; simpl in *.
    * intros v Hv. rewrite <- subst_instance_cstrs_two.
      apply satisfies_subst_instance_ctr; tas.
      apply H1. apply satisfies_subst_instance_ctr; tas.
      rewrite equal_subst_instance_cstrs_mono; aa.
      apply satisfies_union; simpl; split.
      -- intros c Hc. now apply Hv.
      -- apply satisfies_union in Hv; apply Hv.
    * destruct H2 as [_ [_ H2]].
      eapply consistent_ext_trans_polymorphic_case_auxE; try eassumption.
Qed.

Lemma consistent_ext_transE {cf : checker_flags} Σ φ φ' udecl inst inst' :
  wf_ext_wkE (Σ, φ) ->
  consistent_instance_ext (Σ, φ) udecl inst ->
  consistent_instance_ext (Σ, φ') φ inst' ->
  consistent_instance_ext (Σ, φ') udecl (subst_instance inst' inst).
Proof.
  intros HΣφ H1 H2. destruct udecl as [|udecl].
  - (* udecl monomorphic *)
    cbn; now len.
  - (* udecl polymorphic *)
    eapply consistent_ext_trans_polymorphic_casesE; eassumption.
Qed.

#[global] Hint Resolve consistent_ext_transE : univ_subst.

Lemma consistent_instance_valid_constraintsE {cf : checker_flags} Σ φ u univs :
  wf_ext_wkE (Σ, φ) ->
  consistent_instance_ext (Σ, univs) φ u ->
  valid_constraints (global_ext_constraints (Σ, univs))
                    (subst_instance_cstrs u (global_ext_constraints (Σ, φ))).
Proof.
  intros HΣ HH.
  unfold valid_constraints; case_eq check_univs; [intro Hcf|trivial].
  intros v Hv. apply satisfies_subst_instance_ctr; tas.
  apply satisfies_union; simpl; split.
  - destruct φ as [|[φ1 φ2]].
    + cbn. apply satisfies_subst_instance_ctr; tas.
      rewrite equal_subst_instance_cstrs_mono; aa.
      * intros x hin. csets.
      * intros x hin. csets.
    + destruct HH as [_ [_ H1]].
      unfold valid_constraints in H1; rewrite Hcf in H1.
      apply satisfies_subst_instance_ctr; aa.
  - apply satisfies_subst_instance_ctr; tas.
    apply satisfies_union in Hv. destruct HΣ.
    rewrite equal_subst_instance_cstrs_mono; aa.
Qed.

#[global] Hint Resolve consistent_instance_valid_constraintsE : univ_subst.

Lemma All_local_env_over_subst_instanceE {cf : checker_flags} Σ Γ (wfΓ : wf_localE Σ Γ) :
  All_local_env_over (typingE Σ)
                     (fun Γ0 (_ : wf_localE Σ Γ0) t T (_ : Σ;;; Γ0 |-E t : T) =>
       forall u univs, wf_ext_wkE Σ ->
                  consistent_instance_ext (Σ.1, univs) Σ.2 u ->
                  (Σ.1, univs) ;;; subst_instance u Γ0
                  |-E subst_instance u t : subst_instance u T)
                     Γ wfΓ ->
  forall u univs,
    wf_ext_wkE Σ ->
    consistent_instance_ext (Σ.1, univs) Σ.2 u ->
    wf_localE (Σ.1, univs) (subst_instance u Γ).
Proof.
  induction 1; simpl; rewrite /subst_instance /=; constructor; cbn in *; auto.
  all: eapply lift_sorting_fu_it_impl with (tu := tu); cbn in *; eauto using relevance_subst.
Qed.

#[global] Hint Resolve All_local_env_over_subst_instanceE : univ_subst.

Lemma in_var_global_extE {cf : checker_flags} n Σ :
  wfE Σ.1 ->
  LevelSet.In (Level.lvar n) (global_ext_levels Σ) ->
  LevelSet.In (Level.lvar n) (levels_of_udecl Σ.2).
Proof.
  intros wfΣ Hin.
  eapply LevelSet.union_spec in Hin.
  destruct Hin; auto.
  eapply not_var_global_levelsE in wfΣ.
  specialize (wfΣ (Level.lvar n) H).
  now simpl in wfΣ.
Qed.

Lemma wf_universe_subst_instanceE {cf : checker_flags} (Σ : global_env_ext) univs ui u :
   wfE Σ ->
   wf_universe Σ u ->
   consistent_instance_ext (Σ.1, univs) Σ.2 ui ->
   wf_universe (Σ.1, univs) (subst_instance ui u).
Proof.
  intros wfΣ Hl Hu e [[l n] [inl ->]]%In_subst_instance.
  destruct l as [|s|n']; simpl; auto.
  - apply global_ext_levels_InSet.
  - specialize (Hl (Level.level s, n) inl).
    simpl in Hl. apply monomorphic_level_in_global_ext in Hl.
    eapply LS.union_spec. now right.
  - specialize (Hl (Level.lvar n', n) inl).
    eapply LS.union_spec in Hl as [Hl|Hl].
    + red in Hu.
      unfold levels_of_udecl in Hl.
      destruct Σ.2.
      * simpl in Hu.
        destruct u; try discriminate. lsets.
      * destruct Hu as [declu [us vc]].
        unfold subst_instance. simpl.
        destruct (nth_error ui n') eqn:hnth.
        2: simpl; apply global_ext_levels_InSet.
        eapply forallb_Forall in declu.
        eapply nth_error_forall in declu; eauto.
        simpl in declu. now eapply LS.mem_spec in declu.
    + now apply not_var_global_levelsE in Hl.
Qed.

Lemma wf_sort_subst_instanceE {cf : checker_flags} (Σ : global_env_ext) univs ui s :
   wfE Σ ->
   wf_sort Σ s ->
   consistent_instance_ext (Σ.1, univs) Σ.2 ui ->
   wf_sort (Σ.1, univs) (subst_instance ui s).
Proof.
  destruct s as [| | u]; cbnr.
  apply wf_universe_subst_instanceE.
Qed.

Definition wf_global_extE {cf : checker_flags} Σ ext := wf_ext_wkE (Σ, ext).

Lemma subst_instance_case_branch_typeE {cf : checker_flags} {Σ} {wfΣ : wfE Σ} u (ci : case_info) mdecl idecl p predctx br i cdecl :
  let ptm :=
    it_mkLambda_or_LetIn predctx (preturn p)
  in
  let p' := subst_instance u p in
  let ptm' :=
    it_mkLambda_or_LetIn
      (subst_instance u predctx)
      (preturn p') in
  case_branch_type ci mdecl idecl
     (subst_instance u p)
     (map_branch (subst_instance u) id br)
     ptm' i cdecl =
  map_pair (subst_instance u) (subst_instance u)
  (case_branch_type ci mdecl idecl p br ptm i cdecl).
Proof.
  intros ptm p' ptm'.
  rewrite /case_branch_type /case_branch_type_gen /map_pair /=.
  rewrite subst_instance_case_branch_context //.
  f_equal; substu.
  f_equal.
  rewrite map_app. f_equal.
  + rewrite !map_map_compose. apply map_ext => x.
    substu.
    rewrite [subst_instance u (List.rev _)]map_rev. f_equal.
    rewrite /expand_lets_k. len.
    rewrite ?subst_instance_two ?subst_instance_two_context //.
  + simpl. f_equal.
    substu. rewrite map_app /= //.
    rewrite subst_instance_to_extended_list to_extended_list_subst_instance.
    do 2 f_equal.
    rewrite !map_map_compose. now setoid_rewrite <-subst_instance_lift.
Qed.

From Stdlib Require Import Morphisms.
From Stdlib Require Import ssreflect.

Section SubstIdentityConvE.
  Context `{cf:checker_flags}.
  Local Set SimplIsCbn.

  Lemma declared_inductive_wf_ext_wkE Σ mdecl mind :
    wfE Σ ->
    declared_minductive Σ mind mdecl ->
    wf_ext_wkE (Σ, ind_universes mdecl).
  Proof using Type.
    intros wfΣ decli. eapply declared_minductive_to_gen in decli.
    epose proof (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl) wfΣ decli); eauto.
    red. simpl. split; auto.
    Unshelve. all:eauto.
  Qed.

  Lemma declared_inductive_wf_global_extE Σ mdecl mind :
    wfE Σ ->
    declared_minductive Σ mind mdecl ->
    wf_global_extE Σ (ind_universes mdecl).
  Proof using Type.
    intros wfΣ decli. eapply declared_minductive_to_gen in decli.
    split; auto.
    epose proof (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl) wfΣ decli); eauto.
    Unshelve. all:eauto.
  Qed.

  Hint Resolve declared_inductive_wf_ext_wkE declared_inductive_wf_global_extE : pcuic.

  Lemma consistent_instance_ext_subst_absE Σ decl u :
    wf_ext_wkE Σ ->
    consistent_instance_ext Σ decl u ->
    subst_instance (abstract_instance Σ.2) u = u.
  Proof using Type.
    intros [wfΣ onu] cu.
    destruct decl.
    - simpl in cu. destruct u; simpl in *; try discriminate; auto.
    - destruct cu as [decl' [sizeu vc]].
      clear sizeu vc.
      induction u; simpl; auto.
      move/andb_and: decl' => [ina au]. specialize (IHu au).
      rewrite [List.map _ u]IHu. f_equal. clear au.
      destruct a; simpl; auto.
      eapply LevelSet.mem_spec in ina.
      eapply in_var_global_extE in ina; auto.
      destruct (udecl_prop_in_var_poly onu ina) as [[univs csts] eq].
      rewrite eq in IHu, ina |- *. simpl in *.
      rewrite mapi_unfold in IHu, ina |- *.
      eapply LevelSet_In_fold_right_add in ina.
      eapply In_unfold_inj in ina; try congruence.
      eapply (nth_error_unfold Level.lvar) in ina.
      now rewrite (nth_error_nth _ _ _ ina).
  Qed.

  Lemma in_global_ext_subst_abs_levelE Σ l :
    wf_ext_wkE Σ ->
    LevelSet.In (LevelExpr.get_level l) (global_ext_levels Σ) ->
    subst_instance (abstract_instance Σ.2) l = l.
  Proof using Type.
    intros [wfΣ onu] cu.
    destruct l; auto.
    destruct t; auto.
    eapply in_var_global_extE in cu; eauto.
    eapply udecl_prop_in_var_poly in onu as [[ctx cstrs] eq]; eauto.
    rewrite eq. simpl.
    rewrite eq in cu. simpl in cu.
    apply LevelSet_In_fold_right_add in cu.
    unfold AUContext.repr in *. rewrite (mapi_unfold Level.lvar) in cu |- *.
    destruct nth_error eqn:hnth.
    * apply nth_error_unfold_inv in hnth. subst; auto.
    * apply nth_error_None in hnth. rewrite unfold_length in hnth.
      apply In_unfold_inj in cu; try lia. congruence.
  Qed.

  Lemma consistent_instance_ext_subst_abs_univE Σ u :
    wf_ext_wkE Σ ->
    wf_sort Σ u ->
    subst_instance_sort (abstract_instance Σ.2) u = u.
  Proof using Type.
    intros wf cu.
    destruct u; simpl; auto. f_equal.
    apply NonEmptySetFacts.eq_univ'.
    simpl in cu.
    intros l.
    rewrite In_subst_instance.
    split.
    - intros [x [inx ->]].
      specialize (cu _ inx).
      unfold subst_instance.
      apply in_global_ext_subst_abs_levelE in cu; eauto.
      unfold subst_instance in cu. now rewrite cu.
    - intros inl.
      specialize (cu _ inl). exists l; split; auto.
      now rewrite in_global_ext_subst_abs_levelE.
  Qed.

  Lemma consistent_instance_ext_subst_abs_indsE Σ decl ind u bodies :
    wf_ext_wkE Σ ->
    consistent_instance_ext Σ decl u ->
    subst_instance (abstract_instance Σ.2) (inds ind u bodies) =
      (inds ind u bodies).
  Proof using Type.
    intros wf cu.
    unfold inds. generalize #|bodies|.
    induction n; simpl; auto. rewrite IHn; f_equal.
    now rewrite [subst_instance_instance _ _](consistent_instance_ext_subst_absE _ _ _ wf cu).
  Qed.

  Lemma subst_abstract_instance_idE :
    env_propE (fun Σ Γ t T =>
        wf_ext_wkE Σ ->
        let u := abstract_instance (snd Σ) in
        subst_instance u t = t × subst_instance u T = T)
        (fun Σ _ j => wf_ext_wkE Σ ->
        let u := abstract_instance (snd Σ) in
        lift_wfu_term (fun t => subst_instance u t = t) (fun t => subst_instance u t = t) j)
        (fun Σ Γ =>
        wf_ext_wkE Σ ->
        let u := abstract_instance (snd Σ) in
        subst_instance u Γ = Γ).
  Proof using Type.
    eapply typingE_ind_env; intros; simpl in *; auto.
    { apply lift_typing_subjtyp with (1 := X). 2: intros s Hs; now depelim Hs.
      intros ?? []; auto. }

    { apply All_local_env_cst in X0. clear -X0 X1.
      eapply All2_eq, All2_map_left. apply All_All2 with (1 := X0) => decl IH.
      destruct IH as (? & ? & ?), decl as [na bo ty]; tas; unfold map_decl; cbn in *.
      f_equal; tas. destruct bo => //. cbn in *. now f_equal. }

    all: try ((subst u || subst u0); split; [f_equal|]; intuition eauto).

    1:{ rewrite subst_instance_lift. f_equal.
      generalize H. rewrite -H1 /subst_instance /= nth_error_map H /= => [=].
      intros Hdecl. now rewrite -{2}Hdecl. }

    all: try match goal with H : lift_wfu_term _ _ _ |- _ => destruct H as (Htm & Hty & Hs); cbn in Htm, Hty, Hs end.
    all:try (solve [f_equal; eauto; try congruence]).
    all:try (rewrite ?subst_instance_two; f_equal; eapply consistent_instance_ext_subst_absE; eauto).

    - now rewrite consistent_instance_ext_subst_abs_univE.

    - rewrite consistent_instance_ext_subst_abs_univE //.
      now apply wf_sort_super.

    - rewrite product_subst_instance. do 2 f_equal; tas.
      now noconf b0.

    - intuition auto. noconf a; noconf b; noconf b0.
      rewrite subst_instance_subst /= /subst1.
      repeat (f_equal; simpl; auto).

    - rewrite /type_of_constructor subst_instance_subst subst_instance_two.
      erewrite consistent_instance_ext_subst_absE; eauto. f_equal.
      eapply consistent_instance_ext_subst_abs_indsE; eauto.

    - solve_all; simpl in *.
      * rewrite subst_instance_mkApps /= /subst_instance /= in b0.
        eapply mkApps_nApp_inj in b0 as [Hi Hpars] => //.
        now noconf Hi.
      * rewrite subst_instance_mkApps /= /subst_instance /= in b0.
        eapply mkApps_nApp_inj in b0 as [Hi Hpars] => //.
        rewrite map_app in Hpars.
        eapply app_inj in Hpars as [Hpars hinds]. 2:now len.
        rewrite -{2}(map_id (pparams p)) in Hpars.
        now apply map_eq_inj in Hpars.

    - solve_all.

    - rewrite subst_instance_mkApps. f_equal.
      * rewrite /ptm.
        rewrite subst_instance_it_mkLambda_or_LetIn.
        rewrite subst_instance_app in H.
        eapply app_inj in H as []; [|now len].
        rewrite H. now f_equal.
      * rewrite map_app.
        rewrite subst_instance_mkApps /= /subst_instance /= in b0.
        eapply mkApps_nApp_inj in b0 as [Hi Hpars] => //.
        rewrite map_app in Hpars.
        eapply app_inj in Hpars as [Hpars hinds]. 2:now len.
        now rewrite hinds /= a0.
    - rewrite subst_instance_subst /=.
      rewrite /subst_instance /=.
      rewrite subst_instance_mkApps in b.
      eapply mkApps_nApp_inj in b as [Hi Hpars] => //.
      f_equal.
      * rewrite a; f_equal.
        rewrite /subst_instance_list. now rewrite map_rev Hpars.
      * rewrite [subst_instance_constr _ _]subst_instance_two.
        noconf Hi. now rewrite [subst_instance _ u]H.
    - solve_all.
      + destruct a0 as (_ & X & _); tas.
      + destruct b as (X & _); tas.
    - eapply nth_error_all in X0 as (_ & X0 & _); tea.
    - solve_all.
      + destruct a0 as (_ & X & _); tas.
      + destruct b as (X & _); tas.
    - eapply nth_error_all in X0 as (_ & X0 & _); tea.
    - destruct p as [? []]; cbnr. do 2 f_equal.
      depelim X0. specialize (hty X1); specialize (hdef X1).
      unfold mapu_array_model; destruct a; cbn -[Universe.make'] in *.
      f_equal; intuition eauto.
      * rewrite /subst_instance subst_instance_universe_make in b.
        now injection b as e.
      * solve_all.
    - depelim X0; cbn => //=. depelim X. simp prim_type. cbn. f_equal; intuition eauto.
      do 2 f_equal.
      cbn -[Universe.make'] in b.
      rewrite /subst_instance subst_instance_universe_make in b.
      now injection b as e.
  Qed.

  Lemma typed_subst_abstract_instanceE Σ Γ t T :
    wf_ext_wkE Σ ->
    Σ ;;; Γ |-E t : T ->
    let u := abstract_instance Σ.2 in
    subst_instance u t = t.
  Proof using Type.
    intros [wfΣ onu] H. eapply (env_propE_typing subst_abstract_instance_idE) in H as [H H']; eauto.
    split; auto.
  Qed.

End SubstIdentityConvE.

(** ** The copy of [Typing/PCUICUnivSubstitutionTyp] *)

Section SubstIdentity.
  Context `{cf:checker_flags}.

Lemma conv_decls_subst_instanceE (Σ : global_env_ext) {Γ Γ'} u univs d d' :
  valid_constraints (global_ext_constraints (Σ.1, univs))
    (subst_instance_cstrs u Σ) ->
  conv_decls cumulSpecE0 Σ Γ Γ' d d' ->
  conv_decls cumulSpecE0 (Σ.1, univs) (subst_instance u Γ) (subst_instance u Γ')
    (subst_instance u d) (subst_instance u d').
Proof using Type.
  intros valid Hd; depelim Hd; constructor; tas;
    eapply convSpecE_subst_instance; tea.
Qed.

Lemma cumul_decls_subst_instanceE (Σ : global_env_ext) {Γ Γ'} u univs d d' :
  valid_constraints (global_ext_constraints (Σ.1, univs))
    (subst_instance_cstrs u Σ) ->
  cumul_decls cumulSpecE0 Σ Γ Γ' d d' ->
  cumul_decls cumulSpecE0 (Σ.1, univs) (subst_instance u Γ) (subst_instance u Γ')
    (subst_instance u d) (subst_instance u d').
Proof using Type.
  intros valid Hd; depelim Hd; constructor; tas;
    (eapply convSpecE_subst_instance || eapply cumulSpecE_subst_instance); tea.
Qed.

Lemma conv_ctx_subst_instanceE (Σ : global_env_ext) {Γ Γ'} u univs :
  valid_constraints (global_ext_constraints (Σ.1, univs)) (subst_instance_cstrs u Σ) ->
  conv_context cumulSpecE0 Σ Γ Γ' ->
  conv_context cumulSpecE0 (Σ.1, univs) (subst_instance u Γ) (subst_instance u Γ').
Proof using Type.
  intros valid.
  intros; eapply All2_fold_map, All2_fold_impl; tea => ? ? d d'.
  now eapply conv_decls_subst_instanceE.
Qed.

Lemma subst_instance_ws_cumul_ctx_pbE_rel (Σ : global_env_ext) {Γ Γ'} u univs :
  valid_constraints (global_ext_constraints (Σ.1, univs)) (subst_instance_cstrs u Σ) ->
  cumul_context cumulSpecE0 Σ Γ Γ' ->
  cumul_context cumulSpecE0 (Σ.1, univs) (subst_instance u Γ) (subst_instance u Γ').
Proof using Type.
  intros valid.
  intros; eapply All2_fold_map, All2_fold_impl; tea => ? ? d d'.
  now eapply cumul_decls_subst_instanceE.
Qed.

(** Universe instantiation carries the witness of every body; [check] is one
    of [check_one_fix] and [check_one_cofix] ([subst_instance_check_one_fix],
    [subst_instance_check_one_cofix]). *)
Lemma subst_instance_mfix_on_indE (Σ : global_env_ext) Γ u univs check ok mfix :
  (forall d, check (map_def (subst_instance u) (subst_instance u) d) = check d) ->
  valid_constraints (global_ext_constraints (Σ.1, univs)) (subst_instance_cstrs u Σ) ->
  mfix_on_ind check (conv_witnessE Σ Γ) ok mfix ->
  mfix_on_ind check (conv_witnessE (Σ.1, univs) (subst_instance u Γ)) ok
    (map (map_def (subst_instance u) (subst_instance u)) mfix).
Proof using Type.
  intros hc valid.
  eapply mfix_on_ind_map; [exact (All_True mfix)| |easy].
  intros d m _ [ty [hcd [hop hconv]]].
  exists (subst_instance u ty); split; [|split].
  - rewrite map_def_with_type. now rewrite hc.
  - move: hop. rewrite !on_free_vars_subst_instance.
    now rewrite length_map.
  - now eapply convSpecE_subst_instance.
Qed.

Hint Resolve subst_instance_cstrs_two
     satisfies_equal_sets satisfies_subsets : univ_subst.
Hint Resolve monomorphic_global_constraintE monomorphic_global_constraint_extE : univ_subst.
Hint Unfold CS.For_all : univ_subst.
Hint Resolve consistent_ext_transE : univ_subst.
Hint Resolve consistent_instance_valid_constraintsE : univ_subst.
Hint Rewrite subst_instance_extended_subst : substu.
Hint Rewrite expand_lets_subst_instance : substu.
Hint Rewrite subst_instance_subst_context subst_instance_lift_context
  subst_instance_lift subst_instance_mkApps
  subst_instance_subst
  subst_instance_it_mkProd_or_LetIn
  subst_instance_it_mkLambda_or_LetIn
  subst_instance_inds
  : substu.
Ltac substu := autorewrite with substu.
Hint Rewrite subst_instance_expand_lets_ctx : substu.
Hint Resolve subst_instance_wf_predicate
  subst_instance_wf_branch subst_instance_wf_branches : pcuic.
Hint Resolve All_local_env_over_subst_instanceE : univ_subst.
Hint Resolve declared_inductive_wf_ext_wkE declared_inductive_wf_global_extE : pcuic.


Lemma typing_subst_instanceE :
  env_propE (fun Σ Γ t T => forall u univs,
                wf_ext_wkE Σ ->
                consistent_instance_ext (Σ.1, univs) Σ.2 u ->
                (Σ.1,univs) ;;; subst_instance u Γ
                |-E subst_instance u t : subst_instance u T)
          (fun Σ Γ j => forall u univs,
            wf_ext_wkE Σ ->
            consistent_instance_ext (Σ.1, univs) Σ.2 u ->
            lift_typing (fun Σ Γ t T =>
            (Σ.1,univs) ;;; Γ@[u] |-E t@[u] : T@[u]) Σ Γ j)
          (fun Σ Γ => forall u univs,
          wf_ext_wkE Σ ->
          consistent_instance_ext (Σ.1, univs) Σ.2 u ->
          wf_localE (Σ.1,univs) (subst_instance u Γ)).
Proof using Type.
  apply typingE_ind_env; intros Σ wfΣ Γ wfΓ; cbn  -[Universe.make] in *.
  - intros X ????.
    apply lift_typing_impl with (1 := X) => t T [_ IH].
    now eapply IH.
  - rewrite /subst_instance /=.
    intros _; clear wfΓ.
    induction 1 using All_local_env_ind1. 1: constructor.
    intros. simpl.
    apply All_local_env_snoc. 1: now apply IHX.
    eapply lift_typing_mapu with (u := None) => //; auto using relevance_subst_opt.

  - intros n decl eq X u univs wfΣ' H. rewrite subst_instance_lift.
    rewrite map_decl_type. econstructor; aa.
    unfold subst_instance, map_context.
    now rewrite nth_error_map eq.
  - intros l X Hl u univs wfΣ' H.
    rewrite subst_instance_univ_super.
    + econstructor.
      * aa.
      * now apply wf_sort_subst_instanceE.
  - intros n t0 b s1 s2 X X0 X1 X2 X3 u univs wfΣ' H.
    rewrite product_subst_instance; aa. econstructor.
    + eapply lift_typing_mapu with (tm := None) (u := Some _) => //;
      auto using relevance_subst_opt.
    + eapply X3; eauto.
  - intros n t0 b bty X X0 X1 X2 X3 u univs wfΣ' H.
    econstructor.
    + eapply lift_typing_mapu with (tm := None) (u := None) => //;
      auto using relevance_subst_opt.
    + eapply X3; aa.
  - intros n b b_ty b' b'_ty X X0 X1 X2 X3 u univs wfΣ' H.
    econstructor; eauto.
    + eapply lift_typing_mapu with (tm := Some _) (u := None) => //;
      auto using relevance_subst_opt.
    + eapply X3; aa.
  - intros t0 na A B s u X X0 X1 X2 X3 X4 X5 u0 univs wfΣ' H.
    rewrite subst_instance_subst. cbn. econstructor.
    + eapply X1; eauto.
    + eapply X3; eauto.
    + eapply X5; eauto.
  - intros. rewrite subst_instance_two. econstructor; [aa|aa|].
    clear X X0; cbn in *.
    eapply consistent_ext_transE; eauto.
  - intros. rewrite subst_instance_two. econstructor; [aa|aa|].
    clear X X0; cbn in *.
    eapply consistent_ext_transE; eauto.
  - intros. refine (@eq_rect term _ (typingE _ _ _) _ _ _). 1: econstructor; aa.
    clear.
    unfold type_of_constructor; cbn.
    rewrite subst_instance_subst. f_equal.
    + unfold inds. induction #|ind_bodies mdecl|. 1: reflexivity.
      cbn. now rewrite IHn.
    + symmetry; apply subst_instance_two.

  - intros ci p c brs args u mdecl idecl isdecl hΣ hΓ indnp eqpctx wfp cup
      wfpctx pty Hpty Hcpc kelim hrel
      IHctxi Hc IHc notCoFinite wfbrs hbrs i univs wfext cu.
    assert (notCoFinite' : implb (isCoFinite (ind_finite mdecl))
      (on_free_vars (strengthenP 0 1 ssrbool.xpredT) (preturn (subst_instance i p))) = true).
    { change (preturn (subst_instance i p)) with (subst_instance i (preturn p)).
      now rewrite on_free_vars_subst_instance. }
    rewrite subst_instance_mkApps subst_instance_it_mkLambda_or_LetIn map_app.
    cbn.
    change (subst_instance i (preturn p)) with (preturn (subst_instance i p)).
    change (subst_instance i (pcontext p)) with (pcontext (subst_instance i p)).
    change (map_predicate _ _ _ _ _) with (subst_instance i p).
    rewrite subst_instance_case_predicate_context.
    eapply typeE_Case with (p:=subst_instance i p)
                          (ps:=subst_instance_sort i u); eauto with pcuic.
    3,4: constructor; eauto with pcuic.
    + rewrite -subst_instance_case_predicate_context - !subst_instance_app_ctx.
      eapply Hpty; eauto.
    + eapply IHc in cu => //.
      now rewrite subst_instance_mkApps map_app in cu.
    + simpl. eapply consistent_ext_transE; tea.
    + now rewrite -subst_instance_case_predicate_context -subst_instance_app_ctx.
    + cbn in *.
      eapply is_allowed_elimination_subst_instance; aa.
    + now apply relevance_subst.
    + move: IHctxi. simpl.
      rewrite -subst_instance_app.
      rewrite -subst_instance_two_context.
      rewrite -[List.rev (subst_instance i _)]map_rev.
      clear -wfext cu. induction 1; try destruct t0; cbn; constructor; simpl; eauto.
      all:now rewrite -(subst_instance_subst_telescope i [_]).
    + rewrite -{1}(map_id (ind_ctors idecl)).
      eapply All2i_map. eapply All2i_impl; eauto.
      cbn -[case_branch_type case_branch_context subst_instance].
      intros k cdecl br (hctx & hcbctx & (hbod & ihbod) & hbty & ihbty).
      rewrite case_branch_type_fst.
      rewrite - !subst_instance_case_branch_context - !subst_instance_app_ctx.
      rewrite -subst_instance_case_predicate_context subst_instance_case_branch_typeE.
      repeat split; [auto..| |].
      * specialize (ihbod i univs wfext cu).
        cbn. eapply ihbod.
      * specialize (ihbty i univs wfext cu).
        cbn. eapply ihbty.
  - intros p c u mdecl idecl cdecl pdecl isdecl args X X0 X1 X2 H u0 univs wfΣ' H0.
    rewrite subst_instance_subst. cbn.
    rewrite !subst_instance_two.
    rewrite {6}/subst_instance /subst_instance_list /=.
    rewrite map_rev.
    econstructor; eauto. 2:now rewrite length_map.
    eapply X2 in H0; tas. rewrite subst_instance_mkApps in H0.
    eassumption.

  - intros mfix n decl H H0 H1 X IHX X0 IHX0 wffix u univs wfΣ'.
    rewrite (map_dtype _ (subst_instance u)). econstructor.
    + specialize (H1 u univs wfΣ' H2).
      rewrite subst_instance_app in H1.
      now eapply All_local_env_app_inv in H1 as [].
    + now eapply fix_guard_subst_instance.
    + rewrite nth_error_map H0. reflexivity.
    + apply All_map, (All_impl IHX); simpl. intros d X1.
      eapply lift_typing_mapu with (tm := None) (u := None); cbn; eauto using relevance_subst_opt.
    + eapply All_map, (All_impl IHX0); simpl. intros d X1.
      unfold map_def at 2, on_def_body. cbn.
      rewrite -fix_context_subst_instance /app_context -(subst_instance_app u (fix_context mfix) Γ) -/(app_context Γ _).
      rewrite -subst_instance_lift length_map.
      eapply lift_typing_mapu with (tm := Some _) (u := None); cbn; eauto using relevance_subst_opt.
    + destruct wffix as (isl & hra & hon). split; [|split].
      { rewrite forallb_map. refine (forallb_impl _ _ _ _ isl). intros x _ hx.
        now eapply isLambda_subst_instance. }
      { rewrite forallb_map. refine (forallb_impl _ _ _ _ hra). intros x _ hx.
        cbv beta. now rewrite subst_instance_has_rec_arg. }
      eapply subst_instance_mfix_on_indE; [exact (subst_instance_check_one_fix u)|aa|exact hon].

  - intros mfix n decl H H0 H1 X IHX X0 IHX0 wffix u univs wfΣ'.
    rewrite (map_dtype _ (subst_instance u)). econstructor.
    + specialize (H1 u univs wfΣ' H2).
      rewrite subst_instance_app in H1.
      now eapply All_local_env_app_inv in H1 as [].
    + now eapply cofix_guard_subst_instance.
    + rewrite nth_error_map H0. reflexivity.
    + apply All_map, (All_impl IHX); simpl. intros d X1.
      eapply lift_typing_mapu with (tm := None) (u := None); cbn; eauto using relevance_subst_opt.
    + eapply All_map, (All_impl IHX0); simpl. intros d X1.
      unfold map_def at 2, on_def_body. cbn.
      rewrite -fix_context_subst_instance /app_context -(subst_instance_app u (fix_context mfix) Γ) -/(app_context Γ _).
      rewrite -subst_instance_lift length_map.
      eapply lift_typing_mapu with (tm := Some _) (u := None); cbn; eauto using relevance_subst_opt.
    + eapply subst_instance_mfix_on_indE; [exact (subst_instance_check_one_cofix u)|aa|exact wffix].

  - intros.
    rewrite subst_instance_prim_type.
    econstructor.
    + eauto.
    + now rewrite subst_instance_prim_val_tag.
    + exact H0.
    + now rewrite subst_instance_prim_val_tag.
    + destruct p as [? []]; depelim X1; constructor; eauto.
      * rewrite -subst_instance_universe_make. eapply wf_universe_subst_instanceE => //.
      * cbn -[Universe.make'] in hty.
        specialize (hty u univs).
        rewrite /subst_instance subst_instance_universe_make in hty. now eapply hty.
      * cbn. solve_all.

  - intros t0 A B X X0 X1 X2 X3 X4 cum u univs wfΣ' H.
    econstructor.
    + eapply X2; aa.
    + eapply X4; aa.
    + eapply cumulSpecE_subst_instance; aa.
Qed.

Lemma typing_subst_instance'E Σ φ Γ t T u univs :
  wf_ext_wkE (Σ, univs) ->
  (Σ, univs) ;;; Γ |-E t : T ->
  consistent_instance_ext (Σ, φ) univs u ->
  (Σ, φ) ;;; subst_instance u Γ
            |-E subst_instance u t : subst_instance u T.
Proof using Type.
  intros X X0 X1.
  eapply (typing_subst_instanceE (Σ, univs)); tas. apply X.
Qed.

Lemma typing_subst_instance_wf_localE Σ φ Γ u univs :
  wf_ext_wkE (Σ, univs) ->
  wf_localE (Σ, univs) Γ ->
  consistent_instance_ext (Σ, φ) univs u ->
  wf_localE (Σ, φ) (subst_instance u Γ).
Proof using Type.
  intros X X0 X1.
  eapply (env_propE_wf_local typing_subst_instanceE (Σ, univs)); tas. 1: apply X.
Qed.

Lemma typing_subst_instance''E Σ φ Γ t T u univs :
  wf_ext_wkE (Σ, univs) ->
  (Σ, univs) ;;; Γ |-E t : T ->
  consistent_instance_ext (Σ, φ) univs u ->
  (Σ, φ) ;;; subst_instance u Γ
            |-E subst_instance u t : subst_instance u T.
Proof using Type.
  intros X X0 X1.
  eapply (typing_subst_instanceE (Σ, univs)); tas. 1: apply X.
Qed.

Lemma typing_subst_instance_ctxE (Σ : global_env_ext) Γ t T ctx u :
  wfE Σ.1 ->
  on_udecl_prop Σ (Polymorphic_ctx ctx) ->
  (Σ.1, Polymorphic_ctx ctx) ;;; Γ |-E t : T ->
  consistent_instance_ext Σ (Polymorphic_ctx ctx) u ->
  Σ ;;; subst_instance u Γ
            |-E subst_instance u t : subst_instance u T.
Proof using Type.
  destruct Σ as [Σ φ]. intros X X0 X1.
  eapply typing_subst_instance''E; tea.
  split; tas.
Qed.

Lemma typing_subst_instance_declE Σ Γ t T c decl u :
  wfE Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  (Σ.1, universes_decl_of_decl decl) ;;; Γ |-E t : T ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  Σ ;;; subst_instance u Γ
            |-E subst_instance u t : subst_instance u T.
Proof using Type.
  destruct Σ as [Σ φ]. intros X X0 X1 X2.
  eapply typing_subst_instance''E; tea.
  split; tas.
  eapply weaken_lookup_on_global_env'; tea.
Qed.

Lemma wf_local_instantiate_polyE {Σ ctx Γ u} :
  wf_extE (Σ.1, Polymorphic_ctx ctx) ->
  consistent_instance_ext Σ (Polymorphic_ctx ctx) u ->
  wf_localE (Σ.1, Polymorphic_ctx ctx) Γ ->
  wf_localE Σ (subst_instance u Γ).
Proof using Type.
  intros wfΣ Huniv wf.
  epose proof (typeE_Sort _ _ sProp wf) as ty. forward ty.
  - now simpl.
  - eapply typing_subst_instance_ctxE in ty;
    cbn; eauto using typingE_wf_local.
    * apply wfΣ.
    * destruct wfΣ. now eapply on_udecl_on_udecl_prop.
Qed.

Lemma wf_local_instantiateE {Σ} {decl : global_decl} {Γ u c} :
  wfE Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  wf_localE (Σ.1, universes_decl_of_decl decl) Γ ->
  wf_localE Σ (subst_instance u Γ).
Proof using Type.
  intros wfΣ Hdecl Huniv wf.
  epose proof (typeE_Sort _ _ sProp wf) as ty. forward ty.
  - now simpl.
  - eapply typing_subst_instance_declE in ty;
    cbn; eauto using typingE_wf_local.
Qed.

Lemma lift_typing_subst_instance_declE Σ Γ j c decl u :
  wfE Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  lift_typing typingE (Σ.1, universes_decl_of_decl decl) Γ j ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  lift_typing typingE Σ (subst_instance u Γ) {| j_term := option_map (subst_instance u) (j_term j); j_typ := subst_instance u (j_typ j);
                                               j_univ := option_map (subst_instance u) (j_univ j); j_rel := j_rel j |}.
Proof.
  intros wfΣ look Hj cu.
  eapply lift_typing_fu_impl with (1 := Hj) => //; auto using relevance_subst_opt.
  intros ?? Hs; now eapply typing_subst_instance_declE.
Qed.

Lemma isType_subst_instance_declE Σ Γ T c decl u :
  wfE Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  isTypeE (Σ.1, universes_decl_of_decl decl) Γ T ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  isTypeE Σ (subst_instance u Γ) (subst_instance u T).
Proof using Type.
  apply lift_typing_subst_instance_declE.
Qed.

Lemma isTypeRel_subst_instance_declE Σ Γ T r c decl u :
  wfE Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  isTypeRelE (Σ.1, universes_decl_of_decl decl) Γ T r ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  isTypeRelE Σ (subst_instance u Γ) (subst_instance u T) r.
Proof using Type.
  apply lift_typing_subst_instance_declE.
Qed.

Lemma wf_local_subst_instanceE Σ Γ ext u :
  wf_global_extE Σ.1 ext ->
  consistent_instance_ext Σ ext u ->
  wf_localE (Σ.1, ext) Γ ->
  wf_localE Σ (subst_instance u Γ).
Proof using Type.
  destruct Σ as [Σ φ]. intros X X0 X1. simpl in *.
  induction X1; cbn; constructor; auto.
  all: eapply lift_typing_fu_impl with (1 := t0) => //= ?? Hs; auto using relevance_subst_opt.
  all: eapply typing_subst_instance''E in Hs; eauto; apply X.
Qed.

Lemma wf_local_subst_instance_declE Σ Γ c decl u :
  wfE Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  wf_localE (Σ.1, universes_decl_of_decl decl) Γ ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  wf_localE Σ (subst_instance u Γ).
Proof using Type.
  destruct Σ as [Σ φ]. intros X X0 X1 X2.
  induction X1; cbn; constructor; auto.
  all: eapply lift_typing_fu_impl with (1 := t0) => // ?? Hs; auto using relevance_subst_opt.
  all: eapply typing_subst_instance_declE in Hs; eauto; apply X.
Qed.

  Lemma isTypeRel_subst_instance_idE Σ Γ T r :
    wf_ext_wkE Σ ->
    let u := abstract_instance Σ.2 in
    isTypeRelE Σ Γ T r -> subst_instance u T = T.
  Proof using Type.
    intros wf_ext u isT.
    destruct isT as (_ & s & Hs & _).
    eapply typed_subst_abstract_instanceE in Hs; auto.
  Qed.

  Lemma isType_subst_instance_idE Σ Γ T :
    wf_ext_wkE Σ ->
    let u := abstract_instance Σ.2 in
    isTypeE Σ Γ T -> subst_instance u T = T.
  Proof using Type.
    intros wf_ext u isT.
    destruct isT as (_ & s & Hs & _).
    eapply typed_subst_abstract_instanceE in Hs; auto.
  Qed.

  Lemma subst_instance_ind_sort_idE Σ mdecl ind idecl :
    wfE Σ ->
    declared_inductive Σ ind mdecl idecl ->
    let u := abstract_instance (ind_universes mdecl) in
    subst_instance_sort u (ind_sort idecl) = ind_sort idecl.
  Proof using Type.
    intros wfΣ decli u.
    pose proof (on_declared_inductiveE decli) as [onmind oib].
    pose proof (onArityRed oib) as ona.
    apply isTypeRel_subst_instance_idE in ona.
    2:split; simpl; auto.
    - rewrite !subst_instance_it_mkProd_or_LetIn in ona.
      eapply (f_equal (destArity [])) in ona.
      rewrite !destArity_it_mkProd_or_LetIn in ona. simpl in ona. noconf ona.
      simpl in H; noconf H. apply H0.
    - destruct decli as [declm _].
      eapply declared_inductive_wf_global_extE in declm; auto.
      destruct declm. apply o.
  Qed.

  Lemma subst_instance_ind_type_idE Σ mdecl ind idecl :
    wfE Σ ->
    declared_inductive Σ ind mdecl idecl ->
    let u := abstract_instance (ind_universes mdecl) in
    subst_instance u (ind_type idecl) = ind_type idecl.
  Proof using Type.
    intros wfΣ decli u.
    pose proof (on_declared_inductiveE decli) as [_ oib].
    pose proof (onArity oib) as ona.
    apply isTypeRel_subst_instance_idE in ona; eauto.
    destruct decli as [declm _].
    eapply declared_inductive_wf_global_extE in declm; auto.
  Qed.

End SubstIdentity.
