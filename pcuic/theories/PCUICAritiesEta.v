(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import CRelationClasses ProofIrrelevance ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Universes BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICUnivSubstitutionConv
     PCUICCumulativity PCUICPosition PCUICEquality PCUICSigmaCalculus
     PCUICReduction PCUICOnFreeVars PCUICClosed PCUICClosedBodies
     PCUICWeakeningEnvConv PCUICWeakeningEnv PCUICSubstitution PCUICWfUniverses PCUICContexts PCUICArities PCUICUtils
     PCUICWellScopedCumulativity
     PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd PCUICTypingEtaNotions
     PCUICClosedTypEta PCUICWeakeningEnvTypEta PCUICRenameTypEta PCUICWeakeningTypEta
     PCUICUnivSubstitutionTypEta PCUICWfUniversesEta PCUICSubstitutionEta PCUICContextsEta
     PCUICWellScopedCumulativityEta PCUICContextConversionEta PCUICEtaA6 PCUICEtaJoinSpec
     PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp PCUICInversionEta.
From MetaRocq.PCUIC Require PCUICGenerationEta.

From Equations.Prop Require Import DepElim.
From Equations.Type Require Import Relation_Properties.
From Equations Require Import Equations.

(** * Arities and typing spines over [typingE]

  The E copy of [PCUICArities]. Each lemma of the base file that mentions typing,
  cumulativity, [wf_local] or [wf] is copied, and its statement is the base
  statement with only the relations renamed: [typing] → [typingE], [wf_local] →
  [wf_localE], [wf] → [wfE], [isType] / [isTypeRel] → [isTypeE] / [isTypeRelE],
  [subslet] → [subsletE], [Σ ;;; Γ ⊢ A ≤[pb] B] ([ws_cumul_pb]) →
  [ws_cumul_pbE pb Σ Γ A B], [Σ ⊢ Γ ≤[pb] Γ'] → [ws_cumul_ctx_pbE pb Σ Γ Γ'],
  [ws_cumul_ctx_pb_rel] → [ws_cumul_ctx_pbE_rel], [cumulSpec] → [cumulSpecE].

  Copied (the E name is the base name with the suffix [E]): [isType_SortE] (and its
  hint), [wf_typing_spineE], the canonical [typing_spineE] (constructors
  [type_spine_nilE], [type_spine_consE]; [Derive Signature NoConfusion]),
  [typing_spine_isType_codomE], [subslet_inds_genE], [ws_cumul_ctx_pb_vassE],
  [ws_cumul_ctx_pb_appE], [isType_tProdE], [type_ws_cumul_pbE],
  [isType_tLetIn_redE], [isType_tLetIn_domE], [wf_local_assE], [wf_local_defE],
  [isType_applyE], [typing_spine_letin_invE], [typing_spine_letinE],
  [typing_spine_weaken_conclE], [typing_spine_prodE], [typing_spine_WAT_conclE],
  [typing_spine_isType_domE], [type_mkProd_or_LetInE], [type_it_mkProd_or_LetInE],
  [type_it_mkProd_or_LetIn_sortsE], [isType_it_mkProd_or_LetInE],
  [subslet_app_closedE], [subslet_app_invE], [subslet_indsE], [weaken_subsletE],
  [isType_substitution_it_mkProd_or_LetInE], [on_minductive_wf_paramsE],
  [it_mkProd_or_LetIn_wf_localE], [isType_it_mkProd_or_LetIn_wf_localE],
  [isType_weakenE].

  [type_ws_cumul_pbE] is NOT a twin: it ADDS [ClosedBodies Σ]. Base
  [type_ws_cumul_pb] turns [ws_cumul_pb] into the spec relation with no environment
  premise; over η that step ([ws_cumul_pbE_forget_spec]) needs closed bodies.

  [wf_typing_spineE] is the twin of base [wf_typing_spine], which base defines
  BEFORE its own [typing_spine], so it refers to [PCUICGeneration.typing_spine];
  its twin refers to [PCUICGenerationEta.typing_spineE] (required, not imported).

  The inversions come from [PCUICInversionEta] ([inversion_ProdE],
  [inversion_LetInE]), as base's come from [PCUICInversion]. Copied from
  [Conversion/PCUICUnivSubstitutionConv] for the proofs here (no E copy of that
  file exists): [subst_instance_level_absE] and
  [consistent_instance_ext_abstract_instanceE].

  Proof routes that differ from base (statements are twins): [isType_tLetIn_redE]
  goes through A6's [ws_cumul_pbE_LetIn_l_inv] in place of base's
  [ws_cumul_pb_Sort_r_inv] and [invert_red_letin]; [typing_spine_prodE] closes the
  head comparison by [isType_ws_cumul_pbE_refl].

  Not copied: [invert_cumul_arity_l] (a later row); [isArity_it_mkProd_or_LetIn],
  [sort_of_products], [leq_sort_sort_of_products_mon] and
  [subst_telescope_subst_instance], which mention none of the relations and are
  used from base; the notation [isWAT] (base's [isWfArity typing] has no use); the
  section-local hints and the local [pcuic] tactic of base's section, which are
  restated locally. *)

Implicit Types cf : checker_flags.

Lemma isType_SortE {cf:checker_flags} {Σ Γ s} :
  wf_sort Σ s ->
  wf_localE Σ Γ ->
  isTypeE Σ Γ (tSort s).
Proof.
  intros wfs wfΓ.
  eapply has_sort_isTypeE.
  econstructor; eauto.
Qed.
#[global] Hint Resolve isType_SortE : pcuic.

Definition wf_typing_spineE {cf} {Σ Γ T args T'} :=
  isTypeE Σ Γ T × PCUICGenerationEta.typing_spineE Σ Γ T args T'.

Inductive typing_spineE {cf} Σ (Γ : context) : term -> list term -> term -> Type :=
| type_spine_nilE ty ty' :
    isTypeE Σ Γ ty ->
    isTypeE Σ Γ ty' ->
    ws_cumul_pbE Cumul Σ Γ ty ty' ->
    typing_spineE Σ Γ ty [] ty'

| type_spine_consE ty hd tl na A B B' :
    isTypeE Σ Γ ty ->
    isTypeE Σ Γ (tProd na A B) ->
    ws_cumul_pbE Cumul Σ Γ ty (tProd na A B) ->
    Σ ;;; Γ |-E hd : A ->
    typing_spineE Σ Γ (subst10 hd B) tl B' ->
    typing_spineE Σ Γ ty (hd :: tl) B'.

Derive Signature NoConfusion for typing_spineE.

Lemma typing_spine_isType_codomE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ T args U} :
  typing_spineE Σ Γ T args U -> isTypeE Σ Γ U.
Proof.
  induction 1; auto.
Qed.

(* The base proof runs under [Set SimplIsCbn] (set in its file). *)
Section AbstractInstanceE.
Local Set SimplIsCbn.

Lemma subst_instance_level_absE {cf : checker_flags} l n Σ :
  wfE Σ ->
  LevelSet.In l (LevelSet.union
   (fold_right LevelSet.add LevelSet.empty
      (unfold n Level.lvar)) (global_levels Σ)) ->
  subst_instance_level (unfold n Level.lvar) l = l.
Proof using Type.
  intros wfΣ lin.
  eapply LevelSet.union_spec in lin.
  destruct lin.
  - apply LevelSet_In_fold_right_add in H.
    destruct l; simpl; auto.
    eapply In_unfold_inj in H; [|congruence].
    pose proof (proj1 (nth_error_unfold Level.lvar n n0) H).
    now rewrite (nth_error_nth _ _ _ H0).
  - eapply not_var_global_levelsE in wfΣ.
    specialize (wfΣ l H). simpl in wfΣ.
    destruct l => //.
Qed.

Lemma consistent_instance_ext_abstract_instanceE {cf : checker_flags} Σ udecl :
  wfE Σ ->
  wf_global_extE Σ udecl ->
  consistent_instance_ext (Σ, udecl) udecl (abstract_instance udecl).
Proof using Type.
  intros wfΣ wf_glob_ext.
  red. red.
  destruct udecl as [|[univs cst]] eqn:indu.
  { simpl. reflexivity. }
  split; [|split].
  - simpl abstract_instance.
    eapply forallb_mapi => //.
    intros i Hi. unfold global_ext_levels.
    apply LevelSet.mem_spec, LevelSet.union_spec. left.
    unfold levels_of_udecl. simpl.
    rewrite (mapi_unfold Level.lvar).
    eapply LevelSet_In_fold_right_add.
    induction #|univs| in i, Hi |- *; try lia.
    simpl. eapply in_or_app. destruct (eq_dec i n).
    * subst. right; simpl; auto.
    * left; apply IHn; lia.
  - now rewrite mapi_length.
  - simpl. rewrite (mapi_unfold Level.lvar).
    assert(CS.Equal (subst_instance_cstrs (unfold #|univs| Level.lvar) cst) cst).
    { unfold CS.Equal; intros a.
      unfold subst_instance_cstrs.
      red in wf_glob_ext.
      destruct wf_glob_ext as [_ wfext].
      unfold on_udecl_prop in wfext.
      simpl constraints_of_udecl in wfext.
      simpl levels_of_udecl in wfext.
      rewrite (mapi_unfold Level.lvar) in wfext.
      clear indu.
      simpl fst in wfext.
      revert wfext.
      eapply ConstraintSetProp.fold_rec_weak; auto.
      2:reflexivity.
      * intros s s' a' eqs H.
        intros Hf.
        rewrite <- eqs in Hf. rewrite -eqs; auto.
      * intros x a0 s nin equiv.
        intros cadd.
        eapply CS_For_all_add in cadd as [cadd Ps].
        specialize (equiv Ps). clear Ps.
        destruct x as [[l c] r]. destruct cadd as [inl inr].
        unfold subst_instance_cstr. simpl.
        eapply subst_instance_level_absE in inl; auto.
        eapply subst_instance_level_absE in inr; auto.
        rewrite inl inr.
        rewrite !CS.add_spec.
        intuition auto. }
    unfold valid_constraints. destruct check_univs; auto.
    unfold valid_constraints0. simpl.
    unfold satisfies.
    intros v. rewrite H.
    eapply CS_For_all_union.
Qed.

End AbstractInstanceE.

Lemma subslet_inds_genE {cf} {Σ : global_env} {wfΣ : wfE Σ} ind mdecl idecl :
  declared_inductive Σ ind mdecl idecl ->
  let u := abstract_instance (ind_universes mdecl) in
  subsletE (Σ, ind_universes mdecl) [] (inds (inductive_mind ind) u (ind_bodies mdecl))
    (arities_context (ind_bodies mdecl)).
Proof.
  intros isdecl u.
  unfold inds.
  pose proof (proj1 isdecl) as declm'.
  apply (on_declared_minductiveE wfΣ) in declm' as [oind oc]; auto.
  clear oc.
  assert (Alli (fun i x =>
  (Σ, ind_universes mdecl) ;;; [] |-E tInd {| inductive_mind := inductive_mind ind; inductive_ind := i |} u : (ind_type x)) 0 (ind_bodies mdecl)).
  { apply forall_nth_error_Alli. intros.
    eapply Alli_nth_error in oind; eauto. simpl in oind.
    destruct oind. destruct onArity as (_ & s & Hs & _).
    have decli : declared_inductive Σ {| inductive_mind := inductive_mind ind; inductive_ind := i |} mdecl x.
    { split; [exact (proj1 isdecl)|exact H]. }
    eapply typeE_Cumul; [|exact Hs|].
    - econstructor; [constructor|exact decli|].
      eapply consistent_instance_ext_abstract_instanceE; [exact wfΣ|].
      exact (declared_inductive_wf_global_extE Σ mdecl (inductive_mind ind) wfΣ (proj1 isdecl)).
    - rewrite (subst_instance_ind_type_idE Σ _ {| inductive_mind := inductive_mind ind; inductive_ind := i |} _ wfΣ decli).
      apply cumulE_Refl. }
  clear oind.
  revert X. clear onNpars.
  generalize (le_n #|ind_bodies mdecl|).
  generalize (ind_bodies mdecl) at 1 3 4 5.
  induction l using rev_ind; simpl; first constructor.
  rewrite /subst_instance /= /map_context.
  simpl. rewrite /arities_context rev_map_spec /=.
  rewrite map_app /= rev_app_distr /=.
  rewrite /= length_app /= Nat.add_1_r.
  constructor.
  - rewrite -rev_map_spec. apply IHl; try lia.
    eapply Alli_app in X; intuition auto.
  - eapply Alli_app in X as [oind Hx].
    depelim Hx. clear Hx.
    rewrite Nat.add_0_r in t.
    rewrite subst_closedn; auto.
    exact (type_closedE (Σ := (Σ, ind_universes mdecl)) (wfΣ := wfΣ) t).
Qed.

(** Base [type_ws_cumul_pb], with [ClosedBodies Σ] ADDED (see the header). *)
Lemma type_ws_cumul_pbE {cf:checker_flags} {Σ : global_env_ext} {cbΣ : ClosedBodies Σ} {pb Γ t} T {U} :
  Σ ;;; Γ |-E t : T ->
  isTypeE Σ Γ U ->
  ws_cumul_pbE pb Σ Γ T U ->
  Σ ;;; Γ |-E t : U.
Proof.
  intros.
  eapply typeE_Cumul; tea. apply X0.2.π2.1.
  destruct pb.
  - eapply ws_cumul_pbE_eq_le in X1.
    exact (ws_cumul_pbE_forget_spec X1).
  - exact (ws_cumul_pbE_forget_spec X1).
Qed.

Section WfEnv.
  Context {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}.

  Lemma ws_cumul_ctx_pb_vassE {Γ Γ' na na' A A'} le :
    eq_binder_annot na na' ->
    ws_cumul_ctx_pbE le Σ Γ Γ' ->
    ws_cumul_pbE le Σ Γ A A' ->
    ws_cumul_ctx_pbE le Σ (Γ ,, vass na A) (Γ' ,, vass na' A').
  Proof using Type.
    repeat (constructor; auto).
  Qed.

  Lemma ws_cumul_ctx_pb_appE {le Γ Γ' Δ Δ'} :
    #|Δ| = #|Δ'| ->
    ws_cumul_ctx_pbE le Σ (Γ ,,, Δ) (Γ' ,,, Δ') <~>
    ws_cumul_ctx_pbE le Σ Γ Γ' × ws_cumul_ctx_pbE_rel le Σ Γ Δ Δ'.
  Proof using wfΣ.
    move => hlen; split.
    - move/All2_fold_app_inv. move/(_ hlen) => [] onΓ onΔ; split => //.
      split; [exact (ws_cumul_ctx_pbE_closed_left onΓ)|exact onΔ].
    - move=> [] onΓ [_ onΔ].
      apply All2_fold_app; auto.
  Qed.

  Lemma isType_tProdE {Γ} {na A B} :
    isTypeE Σ Γ (tProd na A B) <~> (isTypeRelE Σ Γ A na.(binder_relevance) × isTypeE Σ (Γ,, vass na A) B).
  Proof.
    split; intro HH.
    - destruct HH as (_ & s & H & _).
      apply (inversion_ProdE Σ wfΣ) in H. destruct H as [s1 [s2 [HA [HB Hs]]]].
      apply lift_sorting_forget_univ in HA.
      split; [exact HA|]. eapply has_sort_isTypeE; exact HB.
    - destruct HH as [HA HB].
      pose proof (lift_sorting_extract HA).
      destruct HB as (_ & sB & HB & _).
      eapply has_sort_isTypeE.
      econstructor; eassumption.
  Defined.

  Lemma isType_tLetIn_redE {Γ} (HΓ : wf_localE Σ Γ) {na t A B}
    : isTypeE Σ Γ (tLetIn na t A B) -> isTypeE Σ Γ (B {0:=t}).
  Proof using wfΣ.
    intro HH.
    apply lift_sorting_it_impl_gen with HH => // H.
    assert (Hs := typing_wf_sortE wfΣ H).
    apply (inversion_LetInE Σ wfΣ) in H. destruct H as (A' & Ht & HB & H).
    eapply (type_ws_cumul_pbE (pb:=Cumul)) with (A' {0 := t}).
    - eapply substitution_letE in HB; eauto.
    - exact (isType_SortE Hs HΓ).
    - exact (ws_cumul_pbE_LetIn_l_inv H).
  Qed.

  Lemma isType_tLetIn_domE {Γ} (HΓ : wf_localE Σ Γ) {na t A B}
    : isTypeE Σ Γ (tLetIn na t A B) -> Σ ;;; Γ |-E t : A.
  Proof using wfΣ.
    intros (_ & s & H & _).
    apply (inversion_LetInE Σ wfΣ) in H. destruct H as (A' & Ht & HB & H). now eapply unlift_TermTyp.
  Qed.

  Lemma wf_local_assE {Γ na A} :
    wf_localE Σ Γ ->
    isTypeRelE Σ Γ A na.(binder_relevance) ->
    wf_localE Σ (Γ ,, vass na A).
  Proof using Type.
    intros. apply localenv_cons_abs; tas.
  Qed.

  Lemma wf_local_defE {Γ na d ty} :
    wf_localE Σ Γ ->
    isTypeRelE Σ Γ ty na.(binder_relevance) ->
    Σ ;;; Γ |-E d : ty ->
    wf_localE Σ (Γ ,, vdef na d ty).
  Proof using Type.
    intros. apply localenv_cons_def; tas.
    split; tas. apply X0.
  Qed.

  Hint Resolve wf_local_assE wf_local_defE : pcuic.
  Hint Transparent snoc : pcuic.

  Lemma isType_applyE {Γ na A B t} :
    isTypeE Σ Γ (tProd na A B) ->
    Σ ;;; Γ |-E t : A ->
    isTypeE Σ Γ (B {0 := t}).
  Proof using wfΣ.
    move/isType_tProdE => [hA hB] ht.
    exact (isType_substE (Δ := [vass na A]) (subslet_ass_tipE ht) hB).
  Qed.

  Hint Resolve isType_wf_localE : pcuic.

  Lemma typing_spine_letin_invE {Γ na b B T args S} :
    typing_spineE Σ Γ (tLetIn na b B T) args S ->
    typing_spineE Σ Γ (T {0 := b}) args S.
  Proof using wfΣ.
    intros Hsp.
    depelim Hsp.
    - constructor; auto.
      + eapply isType_tLetIn_redE; [eapply isType_wf_localE|]; eassumption.
      + now eapply ws_cumul_pbE_LetIn_l_inv.
    - econstructor; eauto.
      + eapply isType_tLetIn_redE; [eapply isType_wf_localE|]; eassumption.
      + now eapply ws_cumul_pbE_LetIn_l_inv.
  Qed.

  (** The ζ step of an [isTypeE] let-in, as a well-scoped cumulativity. *)
  Lemma ws_cumul_pbE_zetaE {pb Γ na b B T} :
    isTypeE Σ Γ (tLetIn na b B T) -> ws_cumul_pbE pb Σ Γ (tLetIn na b B T) (T {0 := b}).
  Proof using wfΣ.
    intros h. destruct (on_typeE_scoped h) as [hΓ hT].
    eapply red_ws_cumul_pbE. split; [exact hΓ|exact hT|].
    apply red1_red, red_zeta.
  Qed.

  Lemma typing_spine_letinE {Γ na b B T args S} :
    isTypeE Σ Γ (tLetIn na b B T) ->
    typing_spineE Σ Γ (T {0 := b}) args S ->
    typing_spineE Σ Γ (tLetIn na b B T) args S.
  Proof using wfΣ.
    intros Hty Hsp.
    depelim Hsp.
    - constructor; auto.
      etransitivity; [exact (ws_cumul_pbE_zetaE Hty)|eassumption].
    - econstructor; eauto.
      etransitivity; [exact (ws_cumul_pbE_zetaE Hty)|eassumption].
  Qed.

  Lemma typing_spine_weaken_conclE {Γ T args S S'} :
    typing_spineE Σ Γ T args S ->
    ws_cumul_pbE Cumul Σ Γ S S' ->
    isTypeE Σ Γ S' ->
    typing_spineE Σ Γ T args S'.
  Proof using wfΣ.
    intros Hsp. induction Hsp in S' |- *; intros cum isT.
    - constructor; auto. etransitivity; eassumption.
    - econstructor; eauto.
  Qed.

  Lemma typing_spine_prodE {Γ na b B T args S} :
    typing_spineE Σ Γ (T {0 := b}) args S ->
    isTypeE Σ Γ (tProd na B T) ->
    Σ ;;; Γ |-E b : B ->
    typing_spineE Σ Γ (tProd na B T) (b :: args) S.
  Proof using wfΣ.
    intros Hsp Hprod Hb.
    eapply type_spine_consE; [exact Hprod|exact Hprod| |exact Hb|exact Hsp].
    apply isType_ws_cumul_pbE_refl; exact Hprod.
  Qed.

  Lemma typing_spine_WAT_conclE {Γ T args S} :
    typing_spineE Σ Γ T args S ->
    isTypeE Σ Γ S.
  Proof using Type.
    induction 1; auto.
  Qed.

  Lemma typing_spine_isType_domE {Γ T args S} :
    typing_spineE Σ Γ T args S ->
    isTypeE Σ Γ T.
  Proof using Type.
    induction 1; auto.
  Qed.

  Lemma type_mkProd_or_LetInE {Γ} d {u t s} :
    lift_typing typingE Σ Γ (j_decl_s d (Some u)) ->
    Σ ;;; Γ ,, d |-E t : tSort s ->
    match decl_body d return Type with
    | Some b => Σ ;;; Γ |-E mkProd_or_LetIn d t : tSort s
    | None => Σ ;;; Γ |-E mkProd_or_LetIn d t : tSort (Sort.sort_of_product u s)
    end.
  Proof using wfΣ.
    destruct d as [na [b|] dty] => [Hd Ht|Hd Ht]; rewrite /mkProd_or_LetIn /=.
    - have wf := typingE_wf_local Ht.
      depelim wf.
      eapply typeE_Cumul.
      + econstructor; eauto.
      + apply typeE_Sort; [assumption|exact (typing_wf_sortE wfΣ Ht)].
      + eapply convSpecE_cumulSpecE, red1_cumulSpecE. constructor.
    - have wf := typingE_wf_local Ht.
      depelim wf; clear l.
      eapply typeE_Prod; eauto.
  Qed.

  Lemma type_it_mkProd_or_LetInE {Γ Γ' u t s} :
    wf_sort Σ u ->
    type_local_ctx (lift_typing typingE) Σ Γ Γ' u ->
    Σ ;;; Γ ,,, Γ' |-E t : tSort s ->
    Σ ;;; Γ |-E it_mkProd_or_LetIn Γ' t : tSort (Sort.sort_of_product u s).
  Proof using wfΣ.
    revert Γ u s t.
    induction Γ'; simpl; auto; move=> Γ u s t wfu equ Ht.
    - eapply typeE_Cumul; [exact Ht| |].
      + apply typeE_Sort; [exact (typingE_wf_local Ht)|].
        apply wf_sort_product; [exact wfu|exact (typing_wf_sortE wfΣ Ht)].
      + apply cumulE_Sort. apply leq_sort_product.
    - specialize (IHΓ' Γ  u (Sort.sort_of_product u s)); auto.
      unfold app_context in Ht.
      have wfΓ : wf_localE Σ Γ.
      { apply typingE_wf_local in Ht. depelim Ht; eapply All_local_env_app_inv in Ht; intuition auto. }
      eapply typeE_Cumul.
      + eapply IHΓ'; auto.
        * destruct a as [na [b|] ty]; intuition auto.
        * destruct a as [na [b|] ty]; cbn; destruct equ as (? & Hdecl).
          { apply typingE_wf_local in Ht as XX. inversion XX; subst.
            pose proof (lift_sorting_extract Hdecl).
            eapply (type_mkProd_or_LetInE {| decl_body := Some b |}); eauto.
            eapply typeE_Cumul; eauto.
            - apply typeE_Sort; [assumption|].
              apply wf_sort_product; [exact wfu|exact (typing_wf_sortE wfΣ Ht)].
            - eapply cumulE_Sort. eapply leq_sort_product. }
          eapply (type_mkProd_or_LetInE {| decl_body := None |}) => /=; eauto.
      + apply typeE_Sort; [exact wfΓ|].
        apply wf_sort_product; [exact wfu|].
        exact (typing_wf_sortE wfΣ Ht).
      + now rewrite sort_of_product_twice.
  Qed.

  Lemma type_it_mkProd_or_LetIn_sortsE {Γ Γ' us t s} :
    sorts_local_ctx (lift_typing typingE) Σ Γ Γ' us ->
    Σ ;;; Γ ,,, Γ' |-E t : tSort s ->
    Σ ;;; Γ |-E it_mkProd_or_LetIn Γ' t : tSort (sort_of_products us s).
  Proof using wfΣ.
    revert Γ us s t.
    induction Γ'; simpl; auto; move=> Γ us s t equ Ht.
    - destruct us => //.
    - destruct a as [na [b|] ty]; intuition auto.
      * eapply IHΓ'; eauto.
        pose proof (lift_sorting_extract b0).
        eapply (type_mkProd_or_LetInE {| decl_body := Some b |}); eauto.
      * destruct us => //. destruct equ.
        simpl.
        eapply IHΓ'; eauto.
        apply (type_mkProd_or_LetInE {| decl_body := None |}) => /=; eauto.
  Qed.

  Lemma isType_it_mkProd_or_LetInE {Γ Γ' us t} :
    sorts_local_ctx (lift_typing typingE) Σ Γ Γ' us ->
    isTypeE Σ (Γ ,,, Γ') t ->
    isTypeE Σ Γ (it_mkProd_or_LetIn Γ' t).
  Proof using cf Σ wfΣ.
    move=> equs [_ [s [ttyp _]]]; eapply @has_sort_isTypeE with (s := sort_of_products us s).
    apply: type_it_mkProd_or_LetIn_sortsE=> //.
  Qed.

  Lemma subslet_app_closedE {Γ s s' Δ Δ'} :
    subsletE Σ Γ s Δ ->
    subsletE Σ Γ s' Δ' ->
    closed_ctx Δ ->
    subsletE Σ Γ (s ++ s') (Δ' ,,, Δ).
  Proof using Type.
    induction 1 in s', Δ'; simpl; auto; move=> sub' => /andb_and [clctx clt];
    try constructor; auto.
    - pose proof (subslet_lengthE X). rewrite Nat.add_0_r in clt.
      rewrite /= -H in clt.
      rewrite subst_app_simpl /= (subst_closedn s') //.
    - pose proof (subslet_lengthE X). rewrite Nat.add_0_r in clt.
      rewrite /= -H in clt. move/andb_and: clt => [clt clT].
      replace (subst0 s t) with (subst0 (s ++ s') t).
      + constructor; auto.
        rewrite !subst_app_simpl /= !(subst_closedn s') //.
      + rewrite !subst_app_simpl /= !(subst_closedn s') //.
  Qed.

  Hint Constructors subsletE : core pcuic.

  Lemma subslet_app_invE {Γ Δ Δ' s} :
    subsletE Σ Γ s (Δ ,,, Δ') ->
    subsletE Σ Γ (skipn #|Δ'| s) Δ *
    subsletE Σ Γ (firstn #|Δ'| s) (subst_context (skipn #|Δ'| s) 0 Δ').
  Proof using Type.
    intros sub. split.
    - induction Δ' in Δ, s, sub |- *; simpl; first by rewrite skipn_0.
      depelim sub; rewrite skipn_S; auto.
    - induction Δ' in Δ, s, sub |- *; simpl; first by constructor.
      destruct s; depelim sub.
      * rewrite subst_context_snoc. constructor; eauto.
        rewrite skipn_S Nat.add_0_r /=.
        assert(#|Δ'| = #|firstn #|Δ'| s|).
        { pose proof (subslet_lengthE sub).
          rewrite app_context_length in H.
          rewrite firstn_length_le; lia. }
        rewrite {3}H.
        rewrite -subst_app_simpl.
        now rewrite firstn_skipn.
      * rewrite subst_context_snoc.
        rewrite skipn_S Nat.add_0_r /=.
        rewrite /subst_decl /map_decl /=.
        specialize (IHΔ' _ _ sub).
        epose proof (cons_let_defE _ _ _ _ _ (subst (skipn #|Δ'| s0) #|Δ'| t0)
        (subst (skipn #|Δ'| s0) #|Δ'| T) IHΔ').
        assert(#|Δ'| = #|firstn #|Δ'| s0|).
        { pose proof (subslet_lengthE sub).
          rewrite app_context_length in H.
          rewrite firstn_length_le; lia. }
        rewrite {3 6}H in X.
        rewrite - !subst_app_simpl in X.
        rewrite !firstn_skipn in X.
        specialize (X t1).
        rewrite {3}H in X.
        now rewrite - !subst_app_simpl firstn_skipn in X.
  Qed.

  Lemma subslet_indsE {ind u mdecl idecl} :
    declared_inductive Σ.1 ind mdecl idecl ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    subsletE Σ [] (inds (inductive_mind ind) u (ind_bodies mdecl))
      (subst_instance u (arities_context (ind_bodies mdecl))).
  Proof using wfΣ.
    intros isdecl univs.
    unfold inds.
    pose proof (proj1 isdecl) as declm.
    apply (on_declared_minductiveE wfΣ) in declm as [oind oc]; auto.
    clear oc.
    assert (Alli (fun i x =>
      Σ ;;; [] |-E tInd {| inductive_mind := inductive_mind ind; inductive_ind := i |} u : subst_instance u (ind_type x)) 0 (ind_bodies mdecl)).
    { apply forall_nth_error_Alli.
      intros i x hnth.
      econstructor; [constructor| |exact univs].
      split; [exact (proj1 isdecl)|exact hnth]. }
    clear oind.
    revert X. clear onNpars.
    generalize (le_n #|ind_bodies mdecl|).
    generalize (ind_bodies mdecl) at 1 3 4 5.
    induction l using rev_ind; simpl; first constructor.
    rewrite /subst_instance /= /map_context.
    simpl. rewrite /arities_context rev_map_spec /=.
    rewrite map_app /= rev_app_distr /=.
    rewrite {1}/map_decl /= length_app /= Nat.add_1_r.
    constructor.
    - rewrite -rev_map_spec. apply IHl; try lia.
      eapply Alli_app in X; intuition auto.
    - eapply Alli_app in X as [oind Hx].
      depelim Hx. clear Hx.
      rewrite Nat.add_0_r in t.
      rewrite subst_closedn; auto.
      exact (type_closedE (wfΣ := wfΣ) t).
  Qed.

  Lemma weaken_subsletE {s Δ Γ} :
    wf_localE Σ Γ ->
    subsletE Σ [] s Δ -> subsletE Σ Γ s Δ.
  Proof using wfΣ.
    intros wfΔ.
    induction 1; constructor; auto.
    + eapply (weaken_ctxE (Γ:=[]) Γ); eauto.
    + eapply (weaken_ctxE (Γ:=[]) Γ); eauto.
  Qed.

  Set Default Goal Selector "1".

  Lemma isType_substitution_it_mkProd_or_LetInE {Γ Δ T s} :
    subsletE Σ Γ s Δ ->
    isTypeE Σ Γ (it_mkProd_or_LetIn Δ T) ->
    isTypeE Σ Γ (subst0 s T).
  Proof using wfΣ.
    intros sub HT.
    apply lift_sorting_it_impl_gen with HT => // Hs.
    set (s' := HT.2.π1) in *; clearbody s'. clear HT.
    revert Γ s sub Hs.
    generalize (le_n #|Δ|).
    generalize #|Δ| at 2.
    induction n in Δ, T |- *.
    - destruct Δ; simpl; intros; try (exfalso; lia).
      depelim sub.
      rewrite subst_empty; auto.
    - destruct Δ using rev_ind; try clear IHΔ.
      + intros Hn Γ s sub; now depelim sub; rewrite subst_empty.
      + rewrite length_app Nat.add_1_r /= => Hn Γ s sub.
      pose proof (subslet_lengthE sub). rewrite length_app /= Nat.add_1_r in H.
      have Hl : #|l| = #|firstn #|l| s|.
      { rewrite firstn_length_le; lia. }
      destruct x as [na [b|] ty] => /=;
      rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.

      intros Hs.
      assert (wfs' := typing_wf_sortE wfΣ Hs).
      eapply (inversion_LetInE Σ wfΣ) in Hs as (T' & wfT' & HT' & hlt).
      eapply substitution_letE in HT'; auto.
      eapply ws_cumul_pbE_LetIn_l_inv in hlt; auto.
      pose proof (subslet_app_invE sub) as [subl subr].
      depelim subl. depelim subl. rewrite subst_empty in H0. rewrite H0 in subr.
      specialize (IHn (subst_context [b] 0 l) (subst [b] #|l| T) ltac:(rewrite subst_context_length; lia)).
      specialize (IHn _ _ subr).
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in HT'.
      rewrite !subst_empty in t0.
      forward IHn.
      eapply typeE_Cumul. eapply HT'.
      apply typeE_Sort; [exact (typingE_wf_local t0)|exact wfs'].
      exact (ws_cumul_pbE_forget_spec hlt). rewrite {2}Hl in IHn.
      now rewrite -subst_app_simpl -H0 firstn_skipn in IHn.

      intros Hs.
      assert (wfs' := typing_wf_sortE wfΣ Hs).
      eapply (inversion_ProdE Σ wfΣ) in Hs as (s1 & s2 & wfty & Hty & hlt).
      pose proof (subslet_app_invE sub) as [subl subr].
      depelim subl; depelim subl. rewrite subst_empty in t0. rewrite H0 in subr.
      epose proof (substitution0E Hty t0).
      specialize (IHn (subst_context [t] 0 l) (subst [t] #|l| T)).
      forward IHn. rewrite subst_context_length; lia.
      specialize (IHn _ _ subr).
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in X.
      forward IHn.
      eapply typeE_Cumul. simpl in X. eapply X.
      apply typeE_Sort; [exact (typingE_wf_local t0)|exact wfs'].
      eapply ws_cumul_pbE_Sort_inv in hlt. eapply cumulE_Sort.
      transitivity (Sort.sort_of_product s1 s2).
      eapply leq_sort_product. auto.
      rewrite {2}Hl in IHn.
      now rewrite -subst_app_simpl -H0 firstn_skipn in IHn.
  Qed.

  Lemma on_minductive_wf_paramsE {ind mdecl} {u} :
    declared_minductive Σ.1 ind mdecl ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_localE Σ (subst_instance u (ind_params mdecl)).
  Proof using wfΣ.
    intros.
    unshelve epose proof (declared_minductive_to_gen H); eauto with pcuic.
    eapply (wf_local_instantiateE (decl := InductiveDecl mdecl)); eauto.
    eapply (on_declared_minductiveE wfΣ) in H; auto.
    now apply onParams in H.
  Qed.

  Lemma it_mkProd_or_LetIn_wf_localE {Γ Δ T U} :
    Σ ;;; Γ |-E it_mkProd_or_LetIn Δ T : U -> wf_localE Σ (Γ ,,, Δ).
  Proof using wfΣ.
    move: Γ T U.
    induction Δ using rev_ind => Γ T U.
    + simpl. intros. now eapply typingE_wf_local in X.
    + rewrite it_mkProd_or_LetIn_app.
      destruct x as [na [b|] ty]; cbn; move=> H.
      * apply (inversion_LetInE Σ wfΣ) in H as (A & wfty & HT & hlt).
        eapply All_local_env_app. 1: eapply unlift_TermTyp in wfty; eapply typingE_wf_local; eassumption.
        eapply All_local_env_app. repeat (constructor; tea).
        apply IHΔ in HT.
        eapply All_local_env_app_inv in HT. intuition auto.
        eapply All_local_env_impl; eauto. simpl. intros.
        now rewrite app_context_assoc.
      * apply (inversion_ProdE Σ wfΣ) in H as (s1 & s2 & wfty & HT & hlt).
        eapply All_local_env_app. 1: eapply unlift_TypUniv in wfty; cbn in wfty; eapply typingE_wf_local; eassumption.
        eapply All_local_env_app. apply lift_sorting_forget_univ in wfty. repeat (constructor; tea).
        apply IHΔ in HT.
        eapply All_local_env_app_inv in HT. intuition auto.
        eapply All_local_env_impl; eauto. simpl. intros.
        now rewrite app_context_assoc.
  Qed.

  Lemma isType_it_mkProd_or_LetIn_wf_localE {Γ Δ T} :
    isTypeE Σ Γ (it_mkProd_or_LetIn Δ T) -> wf_localE Σ (Γ ,,, Δ).
  Proof using wfΣ.
    intros (_ & s & Hs & _).
    now eapply it_mkProd_or_LetIn_wf_localE in Hs.
  Qed.

  Lemma isType_weakenE {Γ T} :
    wf_localE Σ Γ ->
    isTypeE Σ [] T ->
    isTypeE Σ Γ T.
  Proof using wfΣ.
    intros wfΓ HT.
    apply lift_typing_impl with (1 := HT) => ?? hs.
    eapply (weaken_ctxE Γ) in hs; eauto.
  Qed.

End WfEnv.
