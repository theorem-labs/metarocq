(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From Stdlib Require Import CRelationClasses ProofIrrelevance.
From MetaRocq.Common Require Import config Universes BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping
     PCUICEquality PCUICCumulativity PCUICReduction
     PCUICContextSubst PCUICUnivSubstitutionConv
     PCUICClosed PCUICSigmaCalculus PCUICSubstitution PCUICContexts
     PCUICWeakeningConv PCUICUtils
     PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd PCUICTypingEtaNotions
     PCUICRenameTypEta PCUICWeakeningTypEta PCUICUnivSubstitutionTypEta PCUICSubstitutionEta.

From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
From Equations.Type Require Import Relation_Properties.
From Stdlib Require Import ssreflect ssrbool.

(** * Contexts over [typingE]

  The E copy of [PCUICContexts]. Each lemma of the base file that mentions
  typing, cumulativity, [wf_local] or [wf] is copied, and its statement is the
  base statement with only the relations renamed: [typing] → [typingE],
  [wf_local] → [wf_localE], [wf_local_rel] → [wf_local_relE], [wf] → [wfE],
  [cumulSpec0] → [cumulSpecE0], [subslet] → [subsletE].

  Copied (the E name is the base name with the suffix [E]):
  [conv_context_smashE], [type_local_ctx_wf_localE], [sorts_local_ctx_wf_localE],
  [instantiate_minductiveE], [type_local_ctx_instantiateE],
  [sorts_local_ctx_instantiateE], [subst_type_local_ctxE], [subst_sorts_local_ctxE],
  [weaken_type_local_ctxE], [weaken_sorts_local_ctxE],
  [wf_local_rel_smash_context_genE], [wf_local_rel_smash_contextE],
  [wf_local_smash_endE], [wf_local_rel_emptyE], [wf_local_smash_contextE],
  [subslet_liftE], [subslet_extended_substE], [typing_expand_letsE].

  Not copied: every other declaration of the base file, which mentions none of the
  relations ([smash_context_*], [to_extended_list_*], [reln_*],
  [context_subst_*], [subst_let_expand*], [untyped_subslet_lift],
  [untyped_subslet_extended_subst], [type_local_ctx_wf] and [sorts_local_ctx_app]
  generic in the predicate, and the rest); they are used from the base file.
  Base's [Derive Signature for subslet] has its twin in [PCUICSubstitutionEta],
  beside [subsletE]. *)

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Lemma conv_context_smashE {cf:checker_flags} Σ Γ Δ Δ' :
  assumption_context Δ ->
  All2_fold (fun Δ Δ' => conv_decls cumulSpecE0 Σ (Γ ,,, Δ) (Γ ,,, Δ')) Δ Δ' ->
  assumption_context Δ'.
Proof.
  intros Hass Hconv.
  induction Hass in Δ', Hconv |- *. depelim Hconv. constructor.
  depelim Hconv. depelim c; constructor; auto.
Qed.

Lemma type_local_ctx_wf_localE {cf:checker_flags} Σ Γ Δ s :
  wf_localE Σ Γ ->
  type_local_ctx (lift_typing typingE) Σ Γ Δ s ->
  wf_localE Σ (Γ ,,, Δ).
Proof.
  induction Δ; simpl; auto.
  destruct a as [na [b|] ty];
  intros wfΓ wfctx; constructor; intuition auto. now eapply lift_sorting_forget_univ.
Qed.

Lemma sorts_local_ctx_wf_localE {cf:checker_flags} Σ Γ Δ s :
  wf_localE Σ Γ ->
  sorts_local_ctx (lift_typing typingE) Σ Γ Δ s ->
  wf_localE Σ (Γ ,,, Δ).
Proof.
  induction Δ in s |- *; simpl; auto.
  destruct a as [na [b|] ty];
  intros wfΓ wfctx; constructor; intuition auto. pcuic.
  destruct s => //. destruct wfctx; eauto.
  destruct s => //. destruct wfctx. now eapply lift_sorting_forget_univ.
Qed.

Lemma instantiate_minductiveE {cf:checker_flags} Σ ind mdecl u Γ t T :
  wfE Σ.1 ->
  declared_minductive Σ.1 ind mdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  (Σ.1, ind_universes mdecl) ;;; Γ |-E t : T ->
  Σ ;;; subst_instance u Γ |-E subst_instance u t : subst_instance u T.
Proof.
  intros wfΣ isdecl Hu Ht.
  unshelve eapply declared_minductive_to_gen in isdecl; eauto.
  red in isdecl. eapply typing_subst_instance_declE in isdecl; eauto.
Qed.

Lemma type_local_ctx_instantiateE {cf:checker_flags} Σ ind mdecl Γ Δ u s :
  wfE Σ.1 ->
  declared_minductive Σ.1 ind mdecl ->
  type_local_ctx (lift_typing typingE) (Σ.1, ind_universes mdecl) Γ Δ s ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  type_local_ctx (lift_typing typingE) Σ (subst_instance u Γ) (subst_instance u Δ) (subst_instance_sort u s).
Proof.
  intros Hctx Hu.
  induction Δ; simpl in *; intuition auto.
  { destruct Σ as [Σ univs]. eapply (wf_sort_subst_instanceE (Σ, ind_universes mdecl)); eauto. }
  destruct a as [na [b|] ty]; simpl; destruct X as (Hwfctx & Hj); split; eauto.
  all: eapply lift_typing_fu_impl with (1 := Hj) => //= ?? Hs; auto using relevance_subst_opt.
  all: eapply instantiate_minductiveE in Hs; eauto.
  all: now rewrite subst_instance_app in Hs.
Qed.

Lemma sorts_local_ctx_instantiateE {cf:checker_flags} Σ ind mdecl Γ Δ u s :
  wfE Σ.1 ->
  declared_minductive Σ.1 ind mdecl ->
  sorts_local_ctx (lift_typing typingE) (Σ.1, ind_universes mdecl) Γ Δ s ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  sorts_local_ctx (lift_typing typingE) Σ (subst_instance u Γ) (subst_instance u Δ)
    (List.map (subst_instance_sort u) s).
Proof.
  intros Hctx Hu.
  induction Δ in s |- *; simpl in *; intuition auto.
  1: destruct s; simpl; intuition eauto.
  destruct a as [na [b|] ty]; simpl.
  2: destruct s => //=.
  all: destruct X as (Hwfctx & Hj); split; eauto.
  all: eapply lift_typing_fu_impl with (1 := Hj) => //= ?? Hs; auto using relevance_subst_opt.
  all: eapply instantiate_minductiveE in Hs; eauto.
  all: now rewrite subst_instance_app in Hs.
Qed.

Lemma subst_type_local_ctxE {cf:checker_flags} Σ Γ Δ Δ' s ctxs :
  wfE Σ.1 ->
  wf_localE Σ (Γ ,,, Δ) ->
  type_local_ctx (lift_typing typingE) Σ (Γ ,,, Δ) Δ' ctxs ->
  subsletE Σ Γ s Δ ->
  type_local_ctx (lift_typing typingE) Σ Γ (subst_context s 0 Δ') ctxs.
Proof.
  intros wfΣ wfΓ X Hs. revert X.
  induction Δ'; simpl; auto.
  rewrite subst_context_snoc /= /subst_decl /map_decl /= Nat.add_0_r.
  destruct a as [na [b|] ty]; simpl.
  all: intros [X Hj]; split; eauto.
  all: apply lift_typing_f_impl with (1 := Hj) => //= ?? HT.
  all: now eapply substitutionE in HT.
Qed.

Lemma subst_sorts_local_ctxE {cf:checker_flags} Σ Γ Δ Δ' s ctxs :
  wfE Σ.1 ->
  wf_localE Σ (Γ ,,, Δ) ->
  sorts_local_ctx (lift_typing typingE) Σ (Γ ,,, Δ) Δ' ctxs ->
  subsletE Σ Γ s Δ ->
  sorts_local_ctx (lift_typing typingE) Σ Γ (subst_context s 0 Δ') ctxs.
Proof.
  intros wfΣ wfΓ X Hs. revert X.
  induction Δ' in ctxs |- *; simpl; auto.
  rewrite subst_context_snoc /= /subst_decl /map_decl /= Nat.add_0_r.
  destruct a as [na [b|] ty]; simpl. 2: destruct ctxs => //=.
  all: intros [X Hj]; split; eauto.
  all: apply lift_typing_f_impl with (1 := Hj) => //= ?? HT.
  all: now eapply substitutionE in HT.
Qed.

Lemma weaken_type_local_ctxE {cf:checker_flags} Σ Γ Γ' Δ ctxs :
  wfE Σ.1 ->
  wf_localE Σ Γ ->
  type_local_ctx (lift_typing typingE) Σ Γ' Δ ctxs ->
  type_local_ctx (lift_typing typingE) Σ (Γ ,,, Γ') Δ ctxs.
Proof.
  intros wfΣ wfΓ.
  induction Δ; simpl; auto.
  rewrite -app_context_assoc.
  destruct a as [na [b|] ty]; simpl.
  all: intros [X Hj]; split; eauto.
  all: apply lift_typing_impl with (1 := Hj) => //= ?? HT.
  all: eapply (weaken_ctxE Γ); auto.
Qed.

Lemma weaken_sorts_local_ctxE {cf:checker_flags} Σ Γ Γ' Δ ctxs :
  wfE Σ.1 ->
  wf_localE Σ Γ ->
  sorts_local_ctx (lift_typing typingE) Σ Γ' Δ ctxs ->
  sorts_local_ctx (lift_typing typingE) Σ (Γ ,,, Γ') Δ ctxs.
Proof.
  intros wfΣ wfΓ.
  induction Δ in ctxs |- *; simpl; auto.
  rewrite -app_context_assoc.
  destruct a as [na [b|] ty]; simpl. 2: destruct ctxs => //.
  all: intros [X Hj]; split; eauto.
  all: apply lift_typing_impl with (1 := Hj) => //= ?? HT.
  all: eapply (weaken_ctxE Γ); auto.
Qed.

Section WfEnvE.
  Context {cf} {Σ} {wfΣ : wfE Σ}.

  Lemma wf_local_rel_smash_context_genE {Γ Δ Δ'} :
    wf_localE Σ (Δ' ,,, Γ) ->
    wf_local_relE Σ (Δ' ,,, Γ) Δ ->
    wf_local_relE Σ Δ' (smash_context Δ Γ).
  Proof using wfΣ.
    induction Γ in Δ |- *; simpl; auto.
    intros wfΓ wfΔ. depelim wfΓ; simpl.
    - apply IHΓ; auto. eapply All_local_env_app; auto.
      + constructor; auto.
      + eapply All_local_env_impl; eauto. simpl; intros.
        now rewrite app_context_assoc.
    - apply IHΓ; auto.
      apply All_local_env_fold, All_local_env_impl with (1 := wfΔ).
      intros Γ' j X.
      apply lift_typing_f_impl with (1 := X) => // ?? HT.
      rewrite Nat.add_0_r.
      eapply (substitutionE (Γ':=[vdef na b t]) (s := [b])) in HT; eauto.
      rewrite -{1}(subst_empty 0 b).
      repeat constructor.
      rewrite !subst_empty.
      now eapply unlift_TermTyp.
  Qed.

  Lemma wf_local_rel_smash_contextE {Γ Δ} :
    wf_localE Σ (Δ ,,, Γ) ->
    wf_local_relE Σ Δ (smash_context [] Γ).
  Proof using wfΣ.
    intros. eapply wf_local_rel_smash_context_genE; eauto. constructor.
  Qed.

  Lemma wf_local_smash_endE Γ Δ :
    wf_localE Σ (Γ ,,, Δ) -> wf_localE Σ (Γ ,,, smash_context [] Δ).
  Proof using wfΣ.
    intros wf.
    apply All_local_env_app.
    now apply All_local_env_app_inv in wf.
    eapply wf_local_rel_smash_contextE; auto.
  Qed.

  Lemma wf_local_rel_emptyE Γ : wf_local_relE Σ [] Γ <~> wf_localE Σ Γ.
  Proof using Type.
    split.
    - intros h. eapply (All_local_env_impl _ _ _ h). pcuicfo.
      red in X |- *. now rewrite app_context_nil_l in X.
    - intros h. eapply (All_local_env_impl _ _ _ h). pcuicfo.
      red in X |- *. now rewrite app_context_nil_l.
  Qed.

  Lemma wf_local_smash_contextE {Γ} :
    wf_localE Σ Γ -> wf_localE Σ (smash_context [] Γ).
  Proof using wfΣ.
    intros; apply wf_local_rel_emptyE. eapply wf_local_rel_smash_contextE.
      rewrite ?app_context_nil_l; eauto.
  Qed.

End WfEnvE.

Lemma subslet_liftE {cf} {Σ} {wfΣ : wfE Σ} (Γ Δ : context) s Δ' :
  wf_localE Σ (Γ ,,, Δ) ->
  subsletE Σ Γ s Δ' ->
  subsletE Σ (Γ ,,, Δ) (map (lift0 #|Δ|) s) (lift_context #|Δ| 0 Δ').
Proof.
  move=> wfl.
  induction 1; rewrite ?lift_context_snoc /=; try constructor; auto.
  simpl.
  rewrite -(subslet_lengthE X).
  rewrite -distr_lift_subst. apply weakeningE; eauto.

  rewrite -(subslet_lengthE X).
  rewrite distr_lift_subst. constructor; auto.
  rewrite - !distr_lift_subst. apply weakeningE; eauto.
Qed.

Lemma subslet_extended_substE {cf} {Σ} {wfΣ : wfE Σ} Γ Δ :
  wf_localE Σ (Γ ,,, Δ) ->
  subsletE Σ (Γ ,,, smash_context [] Δ)
    (extended_subst Δ 0)
    (lift_context (context_assumptions Δ) 0 Δ).
Proof.
  move=> wfΔ.
  eapply All_local_env_app_inv in wfΔ as [wfΓ wfΔ].
  induction Δ as [|[na [d|] ?] ?] in wfΔ |- *; simpl; try constructor.
  * depelim wfΔ. repeat red in l, l0.
    specialize (IHΔ wfΔ).
    rewrite lift_context_snoc /lift_decl /= /map_decl /=.
    len.
    constructor => //.
    apply unlift_TermTyp in l.
    eapply (weakening_typingE (Γ'' := smash_context [] Δ)) in l.
    len in l. simpl in l. simpl.
    2:{ eapply wf_local_smash_endE. now eapply All_local_env_app. }
    eapply (substitutionE (Δ := [])) in l; tea.
  * rewrite smash_context_acc. simpl.
    rewrite /map_decl /= /map_decl /=. simpl.
    depelim wfΔ.
    specialize (IHΔ wfΔ).
    rewrite lift_context_snoc /lift_decl /= /map_decl /=.
    assert (wf_localE Σ (Γ ,,, smash_context [] Δ)).
    { eapply wf_local_smash_endE. now eapply All_local_env_app. }
    assert (wf_localE Σ (Γ ,,, smash_context [] Δ ,, mkdecl na None
        (subst0 (extended_subst Δ 0) (lift (context_assumptions Δ) #|Δ| decl_type)))).
    { simpl. constructor; tas.
      eapply lift_typing_f_impl with (f := fun t => _ (_ t)) (1 := l) => // ?? Hs.
      eapply (weakening_typingE (Γ'' := smash_context [] Δ)) in Hs; tas.
      len in Hs.
      now eapply (substitutionE (Δ := [])) in Hs.
    }
    constructor.
    - rewrite (lift_extended_subst _ 1).
      rewrite -(lift_context_lift_context 1 _).
      eapply (subslet_liftE _ [_]); eauto.
    - eapply meta_convE.
      econstructor; tas.
      reflexivity.
      simpl. rewrite (lift_extended_subst _ 1).
      rewrite distr_lift_subst. f_equal. len.
      now rewrite simpl_lift; try lia.
Qed.

Lemma typing_expand_letsE {cf} {Σ} {wfΣ : wfE Σ} Γ Δ t T :
  Σ ;;; Γ ,,, Δ |-E t : T ->
  Σ ;;; Γ ,,, smash_context [] Δ |-E expand_lets Δ t : expand_lets Δ T.
Proof.
  intros Ht.
  rewrite /expand_lets /expand_lets_k.
  pose proof (typingE_wf_local Ht).
  eapply (weakening_typingE (Γ'' := smash_context [] Δ)) in Ht.
  len in Ht. simpl in Ht. simpl.
  2:{ eapply wf_local_smash_endE; eassumption. }
  eapply (substitutionE (Δ := [])) in Ht; tea.
  now eapply subslet_extended_substE.
Qed.
