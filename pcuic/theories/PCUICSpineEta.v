(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Utf8 CRelationClasses ProofIrrelevance.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Universes BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICSigmaCalculus
     PCUICUnivSubst PCUICTyping PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
     PCUICCumulativity PCUICPosition PCUICEquality
     PCUICInversion PCUICCumulativity PCUICReduction
     PCUICCasesContexts
     PCUICConfluence PCUICParallelReductionConfluence PCUICConversion PCUICContextConversion
     PCUICContextConversionTyp
     PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICClosed PCUICClosedTyp PCUICSubstitution PCUICContextSubst
     PCUICWellScopedCumulativity
     PCUICWeakeningConv PCUICWeakeningTyp PCUICGeneration PCUICUtils PCUICContexts
     PCUICArities PCUICClosedBodies PCUICSpine
     PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
     PCUICTypingEtaNotions PCUICClosedTypEta PCUICWeakeningEnvTypEta PCUICRenameTypEta
     PCUICWeakeningTypEta PCUICUnivSubstitutionTypEta PCUICContextConversionTypEta
     PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta
     PCUICWellScopedCumulativityEta PCUICContextConversionEta PCUICConversionEtaCongr
     PCUICWsCumulEtaSubst PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp PCUICEtaA6 PCUICEtaA6More
     PCUICInversionEta PCUICSREtaConv.
From MetaRocq.PCUIC Require PCUICWfUniversesEta.

From Equations.Prop Require Import DepElim.
From Equations.Type Require Import Relation_Properties.
From Equations Require Import Equations.
From Stdlib Require Import ssreflect ssrbool.

(** * Spines over [typingE]

  The E copy of [PCUICSpine]. Each declaration of the base file that mentions typing,
  [wf_local], [wf], [isType], [subslet], the spines or the cumulativity is copied; its E name is
  the base name with the suffix [E], and its statement is the base statement with only the
  relations renamed: [typing] → [typingE], [wf_local] → [wf_localE], [wf] → [wfE], [isType] →
  [isTypeE], [wf_local_rel] → [wf_local_relE], [ctx_inst Σ] → [ctx_instE Σ], [subslet] →
  [subsletE], [typing_spine] → [typing_spineE] (the one of [PCUICAritiesEta]), [spine_subst],
  [arity_spine], [wf_arity_spine], [ctx_inst_sub] → their E definitions here,
  [Σ ;;; Γ ⊢ t ≤[pb] u] → [Σ ;;; Γ ⊢E t ≤[pb] u], [Σ ⊢ Γ ≤[pb] Δ] →
  [ws_cumul_ctx_pbE pb Σ Γ Δ], [ws_cumul_ctx_pb_rel] → [ws_cumul_ctx_pbE_rel],
  [ws_cumul_pb_terms] → [ws_cumul_pbE_terms]. Implicit status, binder names and positions are
  base's; section premises are base's ([Proof using] kept).

  The E definitions [spine_substE] (with its fields, [Arguments], coercions and hint),
  [arity_spineE] ([Derive Signature]), [wf_arity_spineE] and [ctx_inst_subE] are the canonical
  ones; the notations [spnilE], [spconsE] and the [Arguments] of [type_spine_consE] are the
  twins of base's.

  [type_mkAppsE] is NOT a twin: it ADDS [ClosedBodies Σ] (its comment says why).
  [substitution_ws_cumul_pbE_typed] is the twin of [PCUICConversion.substitution_ws_cumul_pb]
  (over [subsletE] and [wfE]); the name [substitution_ws_cumul_pbE] is
  [PCUICWsCumulEtaSubst]'s untyped lemma.

  Proof routes that differ from base (statements are twins): [type_it_mkProd_or_LetIn_invE]
  inverts the let-in by [ws_cumul_pbE_LetIn_l_inv] and then expands the let ([red_expand_letE])
  and weakens, with no comparison of reducts; [wf_arity_spine_typing_spineE] builds its ζ step
  by [red_ws_cumul_pbE]; [arity_spine_it_mkProd_or_LetIn_SortE] compares the two sorts by
  [ws_cumul_pbE_Sort]; [ctx_inst_eq_contextE] includes [compare_term] in the spec
  ([eq_term_upto_univ_cumulSpecE], [into_ws_cumul_pbE_spec]); [all_rels_substE] weakens the
  reduction under [ClosedBodies]
  ([weakening_red_cb]); [ws_cumul_pb_terms_ws_cumul_ctxE] uses [ws_cumul_pbE_ws_cumul_ctx_pb].

  Not copied: [red_expand_let] (its E twin [red_expand_letE] is [PCUICSREtaConv]'s), the
  declarations that mention none of the relations (used from base, which this file imports),
  and base's global [Hint Rewrite all_rels_length : len] and [Derive Signature for ctx_inst],
  which act through that import. *)

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(* The E twins of the lemmas below carry no global hint, while base registers each lemma
   globally; the proofs of this file see them through these local registrations. *)
(* replays base's global hint isType_ws_cumul_pb_refl (PCUICWellScopedCumulativity.v:289); removed when the E file registers it globally *)
#[local] Hint Immediate isType_ws_cumul_pbE_refl : pcuic.
(* replays base's global hint ws_cumul_pb_refl (PCUICWellScopedCumulativity.v:353); removed when the E file registers it globally *)
#[local] Hint Immediate ws_cumul_pbE_refl : pcuic.
(* replays base's global hint isType_is_open_term (PCUICContextConversion.v:1022); removed when the E file registers it globally *)
#[local] Hint Resolve isType_is_open_termE : fvs.
(* replays base's global hint isTypeRel_is_open_term (PCUICContextConversion.v:1022); removed when the E file registers it globally *)
#[local] Hint Resolve isTypeRel_is_open_termE : fvs.
(* replays base's global hint Extern 4 (wf_local _ ?Γ) (PCUICTyping.v:632); removed when the E file registers it globally *)
#[local] Hint Extern 4 (wf_localE _ ?Γ) =>
  match goal with
  | [ H : typingE _ _ _ _ |- _ ] => exact (typingE_wf_local H)
  | [ H : lift_typing0 (typingE _ _) _ |- _ ] => exact (lift_typingE_wf_local H)
  | [ H : PCUICEnvTyping.lift_typing (typingE _ _) _ |- _ ] => exact (lift_typingE_wf_local H)
  end : pcuic.
(* replays base's global hint typing_wf_local (PCUICTyping.v:641); removed when the E file registers it globally *)
#[local] Hint Resolve typingE_wf_local : wf.
(* replays base's global hint lift_typing_wf_local (PCUICTyping.v:644); removed when the E file registers it globally *)
#[local] Hint Resolve lift_typingE_wf_local : wf.
(* replays base's global hint wf_local_app_l (PCUICTyping.v:613); removed when the E file registers it globally *)
#[local] Hint Immediate wf_localE_app_l : wf.

Ltac splits := repeat split.

Notation spnilE isty isty' w := (type_spine_nilE _ isty isty' w).
Arguments type_spine_consE {cf Σ Γ ty hd tl na A B B'} : rename.

Notation spconsE isty isty' w tyhd sp := (@type_spine_consE _ _ _ _ _ _ _ _ _ _ isty isty' w tyhd sp).

Lemma typing_spine_eqE {cf:checker_flags} Σ Γ ty s s' ty' :
  s = s' ->
  typing_spineE Σ Γ ty s ty' ->
  typing_spineE Σ Γ ty s' ty'.
Proof. now intros ->. Qed.

Import PCUICOnFreeVars.

Lemma weakening_closed_redE {cf} {Σ} {wfΣ : wfE Σ} {Γ Γ' Γ'' M N} :
  Σ ;;; Γ ,,, Γ' ⊢ M ⇝ N ->
  is_closed_context (Γ ,,, Γ'') ->
  Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' ⊢ lift #|Γ''| #|Γ'| M ⇝ lift #|Γ''| #|Γ'| N.
Proof. intros; eapply weakening_closed_red_cb; tea; typeclasses eauto. Qed.

Lemma subslet_eq_context_alphaE {cf} {Σ Γ s Δ Δ'} :
  eq_context_upto_names Δ Δ' →
  subsletE Σ Γ s Δ →
  subsletE Σ Γ s Δ'.
Proof.
  intros eq subs.
  induction subs in Δ', eq |- *; depelim eq; try constructor.
  * depelim e; constructor; auto.
  * depelim e; subst; constructor; auto.
Qed.

Lemma wf_local_alphaE {cf} {Σ} {wfΣ : wfE Σ} Γ Γ' : eq_context_upto_names Γ Γ' ->
  wf_localE Σ Γ ->
  wf_localE Σ Γ'.
Proof.
  induction 1; intros h; depelim h; try constructor; auto.
  all:depelim r; constructor; subst; auto.
  all: rewrite -e.
  all: eapply lift_typing_impl; tea; intros t' T Hty.
  all: eapply context_conversionE; eauto.
  all: now apply eq_context_upto_names_conv_contextE.
Qed.

Lemma subslet_eq_context_alpha_domE {cf} {Σ} {wfΣ : wfE Σ} {Γ Γ' s Δ} :
  eq_context_upto_names Γ Γ' →
  subsletE Σ Γ s Δ →
  subsletE Σ Γ' s Δ.
Proof.
  intros eq subs.
  induction subs in Γ', eq |- *; try constructor.
  * now apply IHsubs.
  * eapply context_conversionE; tea.
    eapply wf_local_alphaE; tea. eapply typingE_wf_local in t0. exact t0.
    now eapply eq_context_upto_names_conv_contextE.
  * now eapply IHsubs.
  * eapply context_conversionE; tea.
    eapply wf_local_alphaE; tea. eapply typingE_wf_local in t0. exact t0.
    now eapply eq_context_upto_names_conv_contextE.
Qed.

Lemma subslet_appE {cf:checker_flags} Σ Γ s s' Δ Δ' :
  subsletE Σ Γ s (subst_context s' 0 Δ) ->
  subsletE Σ Γ s' Δ' ->
  subsletE Σ Γ (s ++ s') (Δ' ,,, Δ).
Proof.
induction Δ in s, s', Δ' |- *; simpl; auto; move=> sub'.
- depelim sub'. auto.
- rewrite subst_context_snoc in sub' => sub''.
  move:(subslet_lengthE sub') => /=.
  rewrite /snoc /= subst_context_length /= => Hlen.
  destruct a as [na [b|] ty].
  * depelim sub'; simpl in t0, Hlen.
    rewrite -subst_app_simpl' /=. lia.
    constructor. eauto.
    now rewrite - !subst_app_simpl' in t0; try lia.
  * rewrite /subst_decl /map_decl /snoc /= in sub'.
    depelim sub'; simpl in Hlen.
    rewrite - !subst_app_simpl' in t0; try lia.
    simpl; constructor; eauto.
Qed.

Lemma subslet_skipnE {cf:checker_flags} Σ Γ s Δ n :
  subsletE Σ Γ s Δ ->
  subsletE Σ Γ (skipn n s) (skipn n Δ).
Proof.
  induction n in s, Δ |- *.
  - now rewrite !skipn_0.
  - intros H; depelim H.
    * rewrite !skipn_nil. constructor.
    * rewrite !skipn_S. auto.
    * rewrite !skipn_S. auto.
Qed.

Lemma ctx_inst_instE {cf:checker_flags} Σ ext u Γ i Δ  :
  wf_global_extE Σ.1 ext ->
  ctx_instE (Σ.1, ext) Γ i Δ ->
  consistent_instance_ext Σ ext u ->
  ctx_instE Σ (subst_instance u Γ)
    (map (subst_instance u) i)
    (subst_instance u Δ).
Proof.
  intros wfext ctxi cu.
  induction ctxi; simpl; constructor; auto.
  * destruct Σ as [Σ univs].
    eapply (typing_subst_instance''E Σ); eauto.
  * rewrite (subst_telescope_subst_instance u [i]).
    apply IHctxi.
  * rewrite (subst_telescope_subst_instance u [b]).
    apply IHctxi.
Qed.

Record spine_substE {cf:checker_flags} Σ Γ inst s (Δ : context) := mkSpineSubstE {
  spine_dom_wfE : wf_localE Σ Γ;
  spine_codom_wfE : wf_localE Σ (Γ ,,, Δ);
  inst_ctx_substE :> context_subst Δ inst s;
  inst_subsletE :> subsletE Σ Γ s Δ }.
Arguments inst_ctx_substE {cf Σ Γ inst s Δ}.
Arguments inst_subsletE {cf Σ Γ inst s Δ}.
#[global]
Hint Resolve inst_ctx_substE inst_subsletE : pcuic.

Lemma spine_subst_eqE {cf:checker_flags} {Σ Γ inst s Δ Δ'} :
  spine_substE Σ Γ inst s Δ ->
  Δ = Δ' ->
  spine_substE Σ Γ inst s Δ'.
Proof.
  now intros sp ->.
Qed.

Lemma spine_subst_inj_substE {cf:checker_flags} {Σ Γ inst s s' Δ} :
  spine_substE Σ Γ inst s Δ ->
  spine_substE Σ Γ inst s' Δ ->
  s = s'.
Proof.
  intros [_ _ c _] [_ _ c' _].
  induction c in s', c' |- *; depelim c'; simpl; auto.
  apply app_inj_tail in H as [-> ->].
  f_equal; eauto.
  specialize (IHc _ c'). now subst.
Qed.

Inductive arity_spineE {cf : checker_flags} (Σ : global_env_ext) (Γ : context) :
  term -> list term -> term -> Type :=
| arity_spine_nilE ty : arity_spineE Σ Γ ty [] ty
| arity_spine_convE ty ty' : isTypeE Σ Γ ty' ->
  Σ ;;; Γ ⊢E ty ≤ ty' -> arity_spineE Σ Γ ty [] ty'
| arity_spine_defE : forall (tl : list term)
                      (na : aname) (A a B B' : term),
                    arity_spineE Σ Γ (B {0 := a}) tl B' ->
                    arity_spineE Σ Γ (tLetIn na a A B) tl B'
| arity_spine_assE : forall (hd : term) (tl : list term)
                      (na : aname) (A B B' : term),
                    Σ;;; Γ |-E hd : A ->
                    arity_spineE Σ Γ (B {0 := hd}) tl B' ->
                    arity_spineE Σ Γ (tProd na A B) (hd :: tl) B'.

Derive Signature for arity_spineE.

Record wf_arity_spineE {cf:checker_flags} Σ Γ T args T' :=
{ wf_arity_spine_wfE : isTypeE Σ Γ T;
  wf_arity_spine_spineE : arity_spineE Σ Γ T args T' }.

#[global] Hint Resolve isType_wf_localE : pcuic.

Section WfEnv.
  Context {cf} {Σ : global_env_ext} {wfΣ : wfE Σ}.

  (** [PCUICConversion.substitution_ws_cumul_pb] over [subsletE] (the E relation has no such
      lemma): the substituted terms are open in [Γ] by [subsletE_open_terms]. *)
  Lemma substitution_ws_cumul_pbE_typed {pb Γ Γ' Γ'' s M N} :
    subsletE Σ Γ s Γ' ->
    Σ ;;; Γ ,,, Γ' ,,, Γ'' ⊢E M ≤[pb] N ->
    Σ ;;; Γ ,,, subst_context s 0 Γ'' ⊢E subst s #|Γ''| M ≤[pb] subst s #|Γ''| N.
  Proof using wfΣ.
    intros hs h. eapply untyped_substitution_ws_cumul_pbE; tea.
    - exact (subslet_untyped_subsletE _ _ _ _ hs).
    - exact (subsletE_open_terms hs).
  Qed.

  Lemma typing_spine_strengthenE {Γ T args U} :
    typing_spineE Σ Γ T args U ->
    forall T',
    isTypeE Σ Γ T' ->
    Σ ;;; Γ ⊢E T' ≤ T ->
    typing_spineE Σ Γ T' args U.
  Proof using wfΣ.
    induction 1 in |- *; intros T' isTy redT.
    - constructor; eauto. transitivity ty; auto.
    - specialize (IHX (B {0 := hd})).
      pose proof (isType_applyE i0 t); tea.
      forward IHX by pcuic.
      forward IHX by (eapply isType_ws_cumul_pbE_refl; tea).
      eapply type_spine_consE; eauto.
      etransitivity; eauto.
  Qed.

  Lemma typing_spine_reflE {Γ T} :
    isTypeE Σ Γ T ->
    typing_spineE Σ Γ T [] T.
  Proof using wfΣ.
    intros isty. constructor; auto.
    eauto with pcuic.
  Qed.

  Lemma inversion_mkApps_directE {Γ f u T} :
    isTypeE Σ Γ T ->
    Σ ;;; Γ |-E mkApps f u : T ->
    ∑ A s', Σ ;;; Γ |-E f : A × Σ ;;; Γ |-E A : tSort s' × typing_spineE Σ Γ A u T.
  Proof using wfΣ.
    induction u in f, T |- *. simpl. intros.
    { destruct X as (_ & s & X & _). exists T, s. intuition pcuic. eapply typing_spine_reflE. eapply has_sort_isTypeE; eauto. }
    intros HT Hf. simpl in Hf.
    destruct u. simpl in Hf, IHu.
    - edestruct @inversion_App_sizeE with (H := Hf) as (na' & A' & B' & s & Hf' & Ha & HA & _ & _ & _ & HA'''); tea.
      eexists _, _; intuition eauto.
      econstructor; eauto with pcuic.
      eapply isType_ws_cumul_pbE_refl; eapply has_sort_isTypeE; eauto.
      econstructor. all:eauto with pcuic.

      eapply inversion_ProdE in HA as (? & ? & ? & ? & ?); tea.
      eapply isType_substE. econstructor. econstructor. rewrite subst_empty; eauto.
      econstructor; cbn; eauto.
    - specialize (IHu (tApp f a) T).
      unshelve epose proof (IHu _ Hf) as [T' [s' [H' [H''' H'']]]]; tea.
      edestruct @inversion_App_sizeE with (H := H') as (na' & A' & B' & s & Hf' & Ha & HA & _ & _ & _ & HA'''); tea.
      exists (tProd na' A' B'). exists s. intuition; eauto.
      econstructor; eauto with wf.
      1,2: pcuic. 1:eapply isType_ws_cumul_pbE_refl; pcuic.

      eapply typing_spine_strengthenE; tea.

      eapply inversion_ProdE in HA as (? & ? & ? & ? & ?); tea.
      eapply isType_substE. econstructor. econstructor. rewrite subst_empty; eauto.
      econstructor; cbn; eauto.
  Qed.

  Lemma subst_type_local_ctxE {Γ Γ' Δ Δ' s ctxs} :
    wf_localE Σ (Γ ,,, Δ ,,, Γ') ->
    type_local_ctx (lift_typing typingE) Σ (Γ ,,, Δ ,,, Γ') Δ' ctxs ->
    subsletE Σ Γ s Δ ->
    type_local_ctx (lift_typing typingE) Σ (Γ ,,, subst_context s 0 Γ') (subst_context s #|Γ'| Δ') ctxs.
  Proof using wfΣ.
    induction Δ' in Γ' |- *; simpl; auto.
    destruct a as [na [b|] ty];
      rewrite subst_context_snoc /= /subst_decl /map_decl /=;
      simpl; intuition auto.
    2: rename b into b0.
    all: rewrite -app_context_assoc in b0.
    all: eapply lift_typing_substitutionE in b0; tea.
    all: rewrite subst_context_app app_context_assoc Nat.add_0_r in b0.
    all: now rewrite app_context_length in b0.
  Qed.

  Lemma subst_sorts_local_ctxE {Γ Γ' Δ Δ' s ctxs} :
    wf_localE Σ (Γ ,,, Δ ,,, Γ') ->
    sorts_local_ctx (lift_typing typingE) Σ (Γ ,,, Δ ,,, Γ') Δ' ctxs ->
    subsletE Σ Γ s Δ ->
    sorts_local_ctx (lift_typing typingE) Σ (Γ ,,, subst_context s 0 Γ') (subst_context s #|Γ'| Δ') ctxs.
  Proof using wfΣ.
    induction Δ' in Γ', ctxs |- *; simpl; auto.
    destruct a as [na [b|] ty]; rewrite subst_context_snoc /= /subst_decl /map_decl /=;
      intuition auto.
    2: destruct ctxs => //=; destruct X0 as (a & b0); split; eauto.
    all: rewrite -app_context_assoc in b0.
    all: eapply lift_typing_substitutionE in b0; tea.
    all: rewrite subst_context_app app_context_assoc Nat.add_0_r in b0.
    all: now rewrite app_context_length in b0.
  Qed.

  Lemma wf_arity_spine_typing_spineE {Γ T args T'} :
    wf_arity_spineE Σ Γ T args T' ->
    typing_spineE Σ Γ T args T'.
  Proof using wfΣ.
    intros [wf sp].
    have wfΓ := isType_wf_localE wf.
    induction sp; try constructor; auto; pcuic.
    - eapply typing_spine_strengthenE; eauto.
      2:{ eapply red_ws_cumul_pbE.
          eapply into_closed_red; [apply red1_red; constructor|eauto with fvs|].
          now eapply isType_is_open_termE. }
      now eapply isType_tLetIn_redE in wf.
    - econstructor; eauto with pcuic.
      apply IHsp. now eapply isType_applyE in wf => //.
  Qed.

  Import PCUICConversion.

  Lemma arity_typing_spineE {Γ Γ' s inst s'} :
    typing_spineE Σ Γ (it_mkProd_or_LetIn Γ' (tSort s)) inst (tSort s') ->
    [× (#|inst| = context_assumptions Γ'), leq_sort (global_ext_constraints Σ) s s' &
      ∑ instsubst, spine_substE Σ Γ inst instsubst Γ'].
  Proof using wfΣ.
    revert s inst s'.
    (* assert (wf_local Σ Γ). now apply wf_local_app_l in wfΓ'. move X after wfΓ'.
    rename X into wfΓ. *)
    generalize (le_n #|Γ'|).
    generalize (#|Γ'|) at 2.
    induction n in Γ' |- *.
    - destruct Γ' using rev_ind; try clear IHΓ'; simpl; intros len s inst s' Hsp.
      + dependent elimination Hsp as [spnilE _ _ cum|spconsE isty isty' cum tyhd sp].
        ++ split=>//.
          now eapply ws_cumul_pbE_Sort_inv in cum.
          exists []. split; try constructor; eauto with pcuic.
          all:now eapply isType_wf_localE.
        ++ now eapply ws_cumul_pbE_Sort_Prod_inv in cum.
      + rewrite length_app /= in len; exfalso; lia.
    - intros len s inst s' Hsp.
      destruct Γ' using rev_ind; try clear IHΓ'.
      -- dependent elimination Hsp as [spnilE _ _ cum|spconsE isty isty' cum tyhd sp].
        1:split; auto.
        --- now eapply ws_cumul_pbE_Sort_inv in cum.
        --- exists []; split; try constructor; auto.
            all:now eapply isType_wf_localE.
        --- now eapply ws_cumul_pbE_Sort_Prod_inv in cum.
      -- rewrite length_app /= in len.
        destruct x as [na [b|] ty]; simpl in *; rewrite /mkProd_or_LetIn /= in Hsp.
        + rewrite context_assumptions_app /= Nat.add_0_r.
          assert (Hsp' := Hsp).
          rewrite it_mkProd_or_LetIn_app /= in Hsp'.
          eapply typing_spine_letin_invE in Hsp'; auto.
          rewrite /subst1 subst_it_mkProd_or_LetIn /= in Hsp'.
          eapply typing_spine_isType_domE in Hsp.
          eapply isType_it_mkProd_or_LetIn_wf_localE in Hsp.
          specialize (IHn (subst_context [b] 0 l)).
          forward IHn by rewrite subst_context_length; lia.
          specialize (IHn s inst s' Hsp').
          rewrite context_assumptions_subst in IHn.
          destruct IHn as [instlen leq [instsubst [wfdom wfcodom cs subi]]].
          split => //.
          exists (instsubst ++ [subst0 [] b]).
          split; auto.
          * apply context_subst_app_inv. cbn.
            rewrite !skipn_0 {1}subst_empty.
            assert(#|l| <= n) by lia.
            pose proof (context_subst_length cs). rewrite subst_context_length in H0.
            rewrite !firstn_app_left //.
            split. now rewrite H0 skipn_all_app.
            rewrite H0 skipn_all_app. repeat constructor.
          * apply subslet_appE; rewrite !subst_empty //.
            eapply subslet_def_tipE.
            rewrite app_context_assoc /= in Hsp.
            apply wf_localE_app_l in Hsp. depelim Hsp. now eapply unlift_TermTyp.
        + rewrite context_assumptions_app /=.
          assert (Hsp' := Hsp).
          rewrite it_mkProd_or_LetIn_app in Hsp'.
          dependent elimination Hsp' as [spnilE typ tys cum|type_spine_consE typ tys cum tyhd sp].
          { now eapply ws_cumul_pbE_Prod_Sort_inv in cum. }
          eapply ws_cumul_pbE_Prod_Prod_inv in cum as [eqna conva cumulB].
          eapply (substitution_ws_cumul_pbE_typed (Γ' := [vass na0 A]) (Γ'':=[]) (s := [hd0])) in cumulB; auto.
          rewrite /subst1 subst_it_mkProd_or_LetIn /= in cumulB.
          specialize (IHn (subst_context [hd0] 0 l)).
          forward IHn by rewrite subst_context_length; lia.
          specialize (IHn s tl0 s'). 2:pcuic.
          rewrite context_assumptions_subst in IHn.
          assert (Σ ;;; Γ |-E hd0 : ty).
          { eapply type_ws_cumul_pbE; tea.
            eapply isType_tProdE in typ as []; eauto with pcuic.
            symmetry; pcuic. }
          eapply typing_spine_strengthenE in sp.
          3:eapply cumulB.
          2:{ cbn in *.
              eapply isType_applyE in typ; tea.
              now rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in typ. }
          all:pcuic.
          destruct X0 as [instlen leq [instsubst [wfdom wfcodom cs subi]]].
          split=> /= //; try lia.
          exists (instsubst ++ [hd0]).
          eapply typing_spine_isType_domE in Hsp.
          eapply isType_it_mkProd_or_LetIn_wf_localE in Hsp.
          split; auto.
          * apply context_subst_app_inv. cbn.
            rewrite !skipn_S skipn_0.
            assert(#|l| <= n) by lia.
            pose proof (context_subst_length cs). rewrite subst_context_length in H0.
            rewrite !firstn_app_left //.
            split. now rewrite H0 skipn_all_app.
            rewrite H0 skipn_all_app. apply (context_subst_ass _ []). constructor.
          * apply subslet_appE => //. now apply subslet_ass_tipE.
  Qed.

(*Lemma typing_spine_it_mkProd_or_LetIn_gen {Γ Δ : context} {T args s s' args' T'} :
  make_context_subst (List.rev Δ) args s' = Some s ->
  typing_spine Σ Γ (subst0 s T) args' T' ->
  #|args| = context_assumptions Δ ->
  subslet Σ Γ s Δ ->
  isType Σ Γ (it_mkProd_or_LetIn Δ T) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T'.
Proof.
  induction Δ using ctx_length_rev_ind in args, args', s, s', T |- *.
  - cbn. destruct args => // => [= <-].
    intros Hsp _ Hsub ist. cbn. depelim Hsub. rewrite subst_empty in Hsp. auto.
  - intros Hsub Hsp Hargs subs.
    rewrite context_assumptions_app in Hargs.
    destruct d as [na [b|] ty]; simpl in *.
    * rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= => Hty.
      rewrite Nat.add_0_r in Hargs.
      rewrite rev_app_distr in Hsub. simpl in Hsub.
      specialize (X (subst_context [b] 0 Γ0) ltac:(len; lia) (subst [b] #|Γ0| T)). _ _ _ _ _ Hsub Hsp Hargs).
      forward X.
      now rewrite it_mkProd_or_LetIn_app /=.
      eapply typing_spine_letin; auto.
      pose proof (subslet_app_inv subs) as.
      eapply isType_substitution_it_mkProd_or_LetIn
      p
      rewrite /subst1.
      now rewrite -subst_app_simpl.
    * rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
      rewrite rev_app_distr in Hsub.
      simpl in Hsub. destruct args; try discriminate.
      simpl in Hargs. rewrite Nat.add_1_r in Hargs. noconf Hargs.
      intros subs. rewrite app_context_assoc in subs.
      specialize (IHn Δ _ T args s _ ltac:(lia) Hsub Hsp H subs).
      intros Har.
      forward IHn. now rewrite it_mkProd_or_LetIn_app.
      eapply subslet_app_inv in subs as [subsl subsr].
      depelim subsl.
      have Hskip := make_context_subst_skipn Hsub.
      rewrite List.length_rev in Hskip. rewrite Hskip in H0; noconf H0.
      simpl; eapply typing_spine_prod; auto; first
      now rewrite /subst1 -subst_app_simpl.
      eapply isType_substitution_it_mkProd_or_LetIn in Har; eauto.
Qed.*)

  Lemma typing_spine_it_mkProd_or_LetIn_genE {Γ Δ Δ' : context} {T args s s' args' T'} :
    make_context_subst (List.rev Δ) args s' = Some s ->
    typing_spineE Σ Γ (subst0 s T) args' T' ->
    #|args| = context_assumptions Δ ->
    subsletE Σ Γ s (Δ' ,,, Δ) ->
    isTypeE Σ Γ (subst0 s' (it_mkProd_or_LetIn Δ T)) ->
    typing_spineE Σ Γ (subst0 s' (it_mkProd_or_LetIn Δ T)) (args ++ args') T'.
  Proof using wfΣ.
    generalize (le_n #|Δ|).
    generalize (#|Δ|) at 2.
    induction n in Δ, Δ', args, s, s', T |- *.
    - destruct Δ using rev_ind.
      + intros le Hsub Hsp.
        destruct args; simpl; try discriminate.
        simpl in Hsub. now depelim Hsub.
      + rewrite length_app /=; intros; exfalso; lia.
    - destruct Δ using rev_ind.
      1:intros le Hsub Hsp; destruct args; simpl; try discriminate;
      simpl in Hsub; now depelim Hsub.
      clear IHΔ.
      rewrite length_app /=; intros Hlen Hsub Hsp Hargs.
      rewrite context_assumptions_app in Hargs.
      destruct x as [na [b|] ty]; simpl in *.
      * rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
        rewrite Nat.add_0_r in Hargs.
        rewrite rev_app_distr in Hsub. simpl in Hsub.
        intros subs isty. rewrite app_context_assoc in subs.
        specialize (IHn l _ T args s _ ltac:(lia) Hsub Hsp Hargs subs).
        forward IHn.
        { eapply isType_tLetIn_redE in isty; pcuic.
          move: isty. rewrite /subst1 -subst_app_simpl //. }
        eapply typing_spine_letinE; auto.
        rewrite /subst1.
        now rewrite -subst_app_simpl.
      * rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
        rewrite rev_app_distr in Hsub.
        simpl in Hsub. destruct args; try discriminate.
        simpl in Hargs. rewrite Nat.add_1_r in Hargs. noconf Hargs.
        intros subs. rewrite app_context_assoc in subs.
        specialize (IHn l _ T args s _ ltac:(lia) Hsub Hsp H subs).
        intros Har.
        eapply subslet_app_invE in subs as [subsl subsr].
        depelim subsl.
        have Hskip := make_context_subst_skipn Hsub.
        rewrite List.length_rev in Hskip. rewrite Hskip in H0; noconf H0.
        forward IHn.
        { eapply isType_applyE in Har; tea.
          now move: Har; rewrite /subst1 -subst_app_simpl. }
        simpl; eapply typing_spine_prodE; auto; first
        now rewrite /subst1 -subst_app_simpl.
  Qed.

  Lemma typing_spine_it_mkProd_or_LetInE {Γ Δ T args s args' T'} :
    make_context_subst (List.rev Δ) args [] = Some s ->
    typing_spineE Σ Γ (subst0 s T) args' T' ->
    #|args| = context_assumptions Δ ->
    subsletE Σ Γ s Δ ->
    isTypeE Σ Γ (it_mkProd_or_LetIn Δ T) ->
    typing_spineE Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T'.
  Proof using wfΣ.
    intros.
    pose proof (@typing_spine_it_mkProd_or_LetIn_genE Γ Δ [] T args s [] args' T'); auto.
    now rewrite subst_empty app_context_nil_l in X2.
  Qed.

  Lemma typing_spine_it_mkProd_or_LetIn'E {Γ Δ T args s args' T'} :
    spine_substE Σ Γ args s Δ ->
    typing_spineE Σ Γ (subst0 s T) args' T' ->
    isTypeE Σ Γ (it_mkProd_or_LetIn Δ T) ->
    typing_spineE Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T'.
  Proof using wfΣ.
    intros. destruct X as [spine_dom_wf0 spine_codom_wf0 inst_ctx_subst0 inst_subslet0].
    eapply typing_spine_it_mkProd_or_LetInE; eauto.
    eapply make_context_subst_spec_inv. now rewrite List.rev_involutive.
    now pose proof (context_subst_length2 inst_ctx_subst0).
  Qed.

  Lemma typing_spine_it_mkProd_or_LetIn_close_make_substE {Γ Δ T args s} :
    make_context_subst (List.rev Δ) args [] = Some s ->
    #|args| = context_assumptions Δ ->
    subsletE Σ Γ s Δ ->
    isTypeE Σ Γ (it_mkProd_or_LetIn Δ T) ->
    typing_spineE Σ Γ (it_mkProd_or_LetIn Δ T) args (subst0 s T).
  Proof using wfΣ.
    intros.
    pose proof (@typing_spine_it_mkProd_or_LetIn_genE Γ Δ [] T args s [] []); auto.
    rewrite app_nil_r subst_empty in X1. apply X1; eauto.
    eapply isType_substitution_it_mkProd_or_LetInE in X0; tea.
    constructor; pcuic.
    now rewrite app_context_nil_l.
  Qed.

  Lemma typing_spine_it_mkProd_or_LetIn_closeE {Γ Δ T args s T'} :
    spine_substE Σ Γ args s Δ ->
    isTypeE Σ Γ (it_mkProd_or_LetIn Δ T) ->
    T' = (subst0 s T) ->
    typing_spineE Σ Γ (it_mkProd_or_LetIn Δ T) args T'.
  Proof using wfΣ.
    intros [spine_dom_wf0 spine_codom_wf0 inst_ctx_subst0 inst_subslet0] H ->.
    eapply typing_spine_it_mkProd_or_LetIn_close_make_substE; eauto.
    eapply make_context_subst_spec_inv.
    now rewrite List.rev_involutive.
    now eapply context_subst_length2 in inst_ctx_subst0.
  Qed.

  Lemma spine_subst_convE {Γ inst insts Δ inst' insts' Δ'} :
    spine_substE Σ Γ inst insts Δ ->
    spine_substE Σ Γ inst' insts' Δ' ->
    ws_cumul_ctx_pbE_rel Conv Σ Γ Δ Δ' ->
    ws_cumul_pbE_terms Σ Γ inst inst' ->
    ws_cumul_pbE_terms Σ Γ insts insts'.
  Proof using wfΣ.
    move=> [_ wf cs sl] [_ wf' cs' sl'] [clΓ cv].
    move: inst insts cs wf sl inst' insts' cs' sl'.
    induction cv; intros; depelim cs; depelim cs'.
    1:constructor; auto.
    all:depelim p.
    - apply All2_app_r in X as (?&?).
      depelim sl; depelim sl'; depelim wf; depelim wf'.
      specialize (IHcv wf' _ _ cs wf sl _ _ cs' sl' a1).
      constructor; auto.
    - depelim sl; depelim sl'; depelim wf; depelim wf'.
      specialize (IHcv wf' _ _ cs wf sl _ _ cs' sl' X).
      constructor; auto.
      eapply (substitution_ws_cumul_pbE_subst_conv (Δ := [])); eauto using subslet_untyped_subsletE with fvs.
  Qed.

  Lemma spine_subst_substE {Γ Γ0 Γ' i s Δ sub} :
    spine_substE Σ (Γ ,,, Γ0 ,,, Γ') i s Δ ->
    subsletE Σ Γ sub Γ0 ->
    spine_substE Σ (Γ ,,, subst_context sub 0 Γ')
      (map (subst sub #|Γ'|) i) (map (subst sub #|Γ'|) s)
      (subst_context sub #|Γ'| Δ).
  Proof using wfΣ.
    move=> [wfl wfΔ cs subl] subs.
    split.
    eapply substitution_wf_localE; eauto.
    pose proof (subst_context_app sub 0 Γ' Δ). rewrite Nat.add_0_r in H. rewrite -app_context_assoc -H.
    clear H.
    eapply substitution_wf_localE; eauto. now rewrite app_context_assoc.
    clear subl wfl wfΔ.
    induction cs in Γ, Γ0, Γ', subs |- *; rewrite ?subst_context_snoc ?map_app; simpl; try constructor.
    eapply IHcs; eauto.
    specialize (IHcs _ _ Γ' subs).
    epose proof (context_subst_def _ _ _ na (subst sub (#|Γ1| + #|Γ'|) b) (subst sub (#|Γ1| + #|Γ'|) t) IHcs).
    rewrite /subst_decl /map_decl /=.
    rewrite distr_subst.
    now rewrite (context_subst_length cs) in X |- *.
    clear cs wfΔ.
    induction subl; rewrite ?subst_context_snoc ?map_app; simpl; try constructor; auto.
    - eapply substitutionE in t0; eauto. simpl.
      rewrite -(subslet_lengthE subl).
      now rewrite -distr_subst.
    - eapply substitutionE in t0; eauto. simpl.
      rewrite -(subslet_lengthE subl).
      rewrite !distr_subst in t0.
      epose proof (cons_let_defE _  _ _ _ _  _ _ IHsubl t0).
      now rewrite - !distr_subst in X.
  Qed.

  Lemma spine_subst_subst_firstE {Γ Γ' i s Δ sub} :
    spine_substE Σ (Γ ,,, Γ') i s Δ ->
    subsletE Σ [] sub Γ ->
    spine_substE Σ (subst_context sub 0 Γ') (map (subst sub #|Γ'|) i) (map (subst sub #|Γ'|) s)
    (subst_context sub #|Γ'| Δ).
  Proof using wfΣ.
    move=> sp subs.
    epose proof (@spine_subst_substE [] Γ Γ' i s Δ sub).
    rewrite !app_context_nil_l in X. apply X; auto.
  Qed.

  Lemma weaken_subsletE {s Δ Γ Γ'} :
    wf_localE Σ Γ -> wf_localE Σ Γ' ->
    subsletE Σ Γ' s Δ -> subsletE Σ (Γ ,,, Γ') s Δ.
  Proof using wfΣ.
    intros wfΔ wfΓ'.
    induction 1; constructor; auto.
    + eapply (weaken_ctxE Γ); eauto.
    + eapply (weaken_ctxE Γ); eauto.
  Qed.

  Lemma spine_subst_weakenE {Γ i s Δ Γ'} :
    wf_localE Σ Γ' ->
    spine_substE Σ Γ i s Δ ->
    spine_substE Σ (Γ' ,,, Γ) i s Δ.
  Proof using wfΣ.
    move=> wfl [cs subl].
    split; auto.
    eapply weaken_wf_localE => //.
    rewrite -app_context_assoc. eapply weaken_wf_localE => //.
    eapply weaken_subsletE; eauto.
  Qed.

  Lemma spine_subst_app_invE {Γ Δ Δ' inst inst' insts} :
    #|inst| = context_assumptions Δ ->
    spine_substE Σ Γ (inst ++ inst') insts (Δ ,,, Δ') ->
    spine_substE Σ Γ inst (skipn #|Δ'| insts) Δ *
    spine_substE Σ Γ inst' (firstn #|Δ'| insts) (subst_context (skipn #|Δ'| insts) 0 Δ').
  Proof using wfΣ.
    intros len sp.
    destruct sp as [wfdom wfcodom cs subs].
    eapply context_subst_app in cs as [csl csr].
    rewrite skipn_all_app_eq in csl => //.
    rewrite firstn_app_left in csr => //.
    eapply subslet_app_invE in subs as [sl sr].
    split; split; auto. rewrite app_context_assoc in wfcodom.
    now eapply All_local_env_app_inv in wfcodom as [? ?].
    eapply substitution_wf_localE; eauto.
    now rewrite app_context_assoc in wfcodom.
  Qed.

  Lemma spine_subst_smash_app_invE {Γ Δ Δ' δ δ'} :
    #|δ| = context_assumptions Δ ->
    spine_substE Σ Γ (δ ++ δ') (List.rev (δ ++ δ')) (smash_context [] (Δ ,,, Δ')) ->
    spine_substE Σ Γ δ (List.rev δ) (smash_context [] Δ) ×
    spine_substE Σ Γ δ' (List.rev δ')
      (subst_context_let_expand (List.rev δ) Δ (smash_context [] Δ')).
  Proof using wfΣ.
    intros hδ sp.
    rewrite smash_context_app_expand in sp.
    eapply spine_subst_app_invE in sp; eauto.
    2:{ rewrite context_assumptions_smash_context /= //. }
    rewrite expand_lets_ctx_length smash_context_length /= in sp.
    destruct sp as [sppars spidx].
    assert (lenidx : context_assumptions Δ' = #|δ'|).
    { pose proof (PCUICContextSubst.context_subst_length2 spidx). len in H. }
    assert (firstn (context_assumptions Δ')
          (List.rev (δ ++ δ')) = List.rev δ').
    { rewrite List.rev_app_distr.
      now rewrite firstn_app_left // List.length_rev. }
    assert (skipn (context_assumptions Δ')
      (List.rev (δ ++ δ')) = List.rev δ).
    { rewrite List.rev_app_distr.
      erewrite (skipn_all_app_eq) => //; rewrite List.length_rev //. }
    rewrite H H0 in spidx, sppars.
    split => //.
  Qed.

  Lemma spine_subst_instE {ext u Γ i s Δ}  :
    wf_global_extE Σ.1 ext ->
    spine_substE (Σ.1, ext) Γ i s Δ ->
    consistent_instance_ext Σ ext u ->
    spine_substE Σ (subst_instance u Γ)
      (map (subst_instance u) i)
      (map (subst_instance u) s)
      (subst_instance u Δ).
  Proof using wfΣ.
    intros wfext [wfdom wfcodom cs subsl] cu.
    split.
    eapply wf_local_subst_instanceE; eauto.
    rewrite -subst_instance_app_ctx.
    eapply wf_local_subst_instanceE; eauto.
    clear -cs cu wfext wfΣ.
    induction cs; simpl; rewrite ?map_app; try constructor; auto.
    rewrite subst_instance_cons; simpl.
    rewrite subst_instance_subst.
    constructor; auto.

    clear -subsl cu wfΣ wfext.
    induction subsl; simpl; rewrite ?subst_instance_subst; constructor; auto.
    * destruct Σ as [Σ' univs].
      rewrite -subst_instance_subst.
      eapply (typing_subst_instance''E Σ'); simpl; eauto.
    * rewrite - !subst_instance_subst. simpl.
      destruct Σ as [Σ' univs].
      eapply (typing_subst_instance''E Σ'); simpl; eauto.
  Qed.

  Lemma spine_subst_weakeningE {Γ i s Δ Γ'} :
    wf_localE Σ (Γ ,,, Γ') ->
    spine_substE Σ Γ i s Δ ->
    spine_substE Σ (Γ ,,, Γ') (map (lift0 #|Γ'|) i) (map (lift0 #|Γ'|) s) (lift_context #|Γ'| 0 Δ).
  Proof using wfΣ.
    move=> wfl [cs subl].
    split; auto.
    eapply weakening_wf_localE; eauto.
    now apply context_subst_lift.
    now apply subslet_liftE.
  Qed.

  Lemma ctx_inst_substE {Γ Γ0 Γ' i Δ sub} :
    ctx_instE Σ (Γ ,,, Γ0 ,,, Γ') i Δ ->
    subsletE Σ Γ sub Γ0 ->
    ctx_instE Σ (Γ ,,, subst_context sub 0 Γ') (map (subst sub #|Γ'|) i) (subst_telescope sub #|Γ'| Δ).
  Proof using wfΣ.
    move=> ctxinst subs.
    induction ctxinst in sub, subs |- *.
    - simpl; intros; constructor; auto.
    - intros. rewrite subst_telescope_cons; simpl; constructor.
      * simpl. eapply substitutionE; eauto.
      * specialize (IHctxinst _ subs).
        now rewrite (subst_telescope_comm [i]).
    - intros. rewrite subst_telescope_cons; simpl; constructor.
      specialize (IHctxinst _ subs).
      now rewrite (subst_telescope_comm [b]).
  Qed.

  Lemma ctx_inst_weakenE {Γ i Δ Γ'} :
    wf_localE Σ Γ' ->
    ctx_instE Σ Γ i Δ ->
    ctx_instE Σ (Γ' ,,, Γ) i Δ.
  Proof using wfΣ.
    move=> wfl subl.
    induction subl; constructor; auto.
    now eapply (weaken_ctxE Γ').
  Qed.

  (* The constructors are qualified: [PCUICSpine], imported here, declares a lemma named
     [ctx_inst_ass]. *)
  Fixpoint ctx_inst_subE {cf:checker_flags} {Σ Γ Δ args} (c : ctx_instE Σ Γ args Δ) {struct c} : list term :=
    match c return _ with
    | PCUICTyping.ctx_inst_nil => []
    | PCUICTyping.ctx_inst_ass na t i inst Δ P c => ctx_inst_subE c ++ [i]
    | PCUICTyping.ctx_inst_def na b t inst Δ c => ctx_inst_subE c ++ [b]
    end.

  Lemma ctx_inst_sub_specE {Γ Δ args} (c : ctx_instE Σ Γ args Δ) :
    make_context_subst Δ args [] = Some (ctx_inst_subE c).
  Proof using Type.
    induction c; simpl; auto.
    now apply (make_context_subst_tele [] [i]) in IHc.
    apply (make_context_subst_tele [] [b]) in IHc.
    now rewrite subst_empty.
  Qed.

  Hint Extern 0 => lia : lia.

  Lemma arity_spine_it_mkProd_or_LetInE {Γ Δ T args s args' T'} :
    spine_substE Σ Γ args s Δ ->
    arity_spineE Σ Γ (subst0 s T) args' T' ->
    arity_spineE Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T'.
  Proof using Type.
    intros sp asp. destruct sp as [wfΓ _ cs subsl].
    move: Δ args s T cs subsl asp.
    induction Δ using ctx_length_rev_ind => args s T cs subsl asp.
    - depelim cs. depelim  subsl.
      now rewrite subst_empty in asp.
    - rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
      destruct d as [na [b|] ty]; simpl in *.
      * constructor. rewrite /subst1 subst_it_mkProd_or_LetIn.
        rewrite Nat.add_0_r.
        apply subslet_app_invE in subsl as [subsl subsl'].
        depelim subsl; depelim subsl.
        apply context_subst_app in cs as [cs cs'].
        simpl in *. rewrite skipn_0 in cs.
        specialize (X (subst_context (skipn #|Γ0| s) 0 Γ0) ltac:(now autorewrite with len) _ _
          (subst [b] #|Γ0| T) cs subsl').
        rewrite subst_empty in H.
        rewrite H in X. apply X.
        rewrite -subst_app_simpl'.
        apply subslet_lengthE in subsl'.
        now autorewrite with len in subsl'.
        rewrite -H.  now rewrite firstn_skipn.
      * apply subslet_app_invE in subsl as [subsl subsl'].
        depelim subsl; depelim subsl.
        apply context_subst_app in cs as [cs cs'].
        simpl in *.
        destruct args. depelim cs'.
        depelim cs'. discriminate.
        simpl in *. rewrite skipn_S skipn_0 in cs.
        rewrite subst_empty in t0.
        depelim cs'; depelim cs'. simpl in H; noconf H.
        rewrite H1 in H0. noconf H0.
        constructor; auto.
        rewrite /subst1 subst_it_mkProd_or_LetIn.
        rewrite Nat.add_0_r.
        specialize (X (subst_context (skipn #|Γ0| s) 0 Γ0) ltac:(now autorewrite with len) _ _
        (subst [t1] #|Γ0| T) cs subsl').
        rewrite -{1}H1. apply X.
        rewrite -subst_app_simpl'.
        apply subslet_lengthE in subsl'.
        now autorewrite with len in subsl'.
        rewrite -H1. now rewrite firstn_skipn.
  Qed.

  Lemma spine_subst_is_closed_contextE Γ args inst ctx :
    spine_substE Σ Γ args inst ctx ->
    is_closed_context Γ.
  Proof using wfΣ.
    now move=> [] /wf_local_closed_contextE.
  Qed.

  Lemma spine_subst_is_closed_context_codomE Γ args inst ctx :
    spine_substE Σ Γ args inst ctx ->
    is_closed_context (Γ ,,, ctx).
  Proof using wfΣ.
    now move=> [] _ /wf_local_closed_contextE.
  Qed.
  Hint Resolve spine_subst_is_closed_contextE spine_subst_is_closed_context_codomE : fvs.

  Lemma arity_spine_it_mkProd_or_LetIn_SortE {Γ ctx s s' args inst} :
    wf_sort Σ s' ->
    leq_sort Σ s s' ->
    spine_substE Σ Γ args inst ctx ->
    arity_spineE Σ Γ (it_mkProd_or_LetIn ctx (tSort s)) args (tSort s').
  Proof using wfΣ.
    intros wfs le sp. rewrite -(app_nil_r args).
    eapply arity_spine_it_mkProd_or_LetInE => //.
    eauto. constructor.
    eapply isType_SortE; eauto.
    eapply sp. simpl.
    apply ws_cumul_pbE_Sort; [eauto with pcuic fvs|exact le].
  Qed.

  Lemma ctx_inst_subst_lengthE {Γ} {Δ : context} {args} (c : ctx_instE Σ Γ args Δ) :
    #|ctx_inst_subE c| = #|Δ|.
  Proof using Type.
    induction c; simpl; auto; try lia;
    rewrite length_app IHc subst_telescope_length /=; lia.
  Qed.

  Lemma ctx_inst_appE {Γ} {Δ : context} {Δ' args args'}
    (dom : ctx_instE Σ Γ args Δ) :
    ctx_instE Σ Γ args' (subst_telescope (ctx_inst_subE dom) 0 Δ') ->
    ctx_instE Σ Γ (args ++ args') (Δ ++ Δ').
  Proof using Type.
    induction dom in args', Δ' |- *; simpl.
    - now rewrite subst_telescope_empty.
    - rewrite subst_app_telescope /= ctx_inst_subst_lengthE /= subst_telescope_length Nat.add_0_r /=.
      move/IHdom => IH.
      constructor => //.
      now rewrite subst_telescope_app Nat.add_0_r.
    - rewrite subst_app_telescope /= ctx_inst_subst_lengthE /= subst_telescope_length Nat.add_0_r /=.
      move/IHdom => IH.
      constructor => //.
      now rewrite subst_telescope_app Nat.add_0_r.
  Qed.

  Lemma ctx_inst_app_invE {Γ} {Δ : context} {Δ' args}
    (c : ctx_instE Σ Γ args (Δ ++ Δ')) :
    ∑ (dom : ctx_instE Σ Γ (firstn (context_assumptions Δ) args) Δ),
      ctx_instE Σ Γ (skipn (context_assumptions Δ) args) (subst_telescope (ctx_inst_subE dom) 0 Δ').
  Proof using Type.
    revert args Δ' c.
    induction Δ using ctx_length_ind; intros.
    simpl. unshelve eexists. constructor.
    simpl. rewrite skipn_0. now rewrite subst_telescope_empty.
    depelim c; simpl.
    - specialize (X (subst_telescope [i] 0 Γ0) ltac:(now rewrite /subst_telescope mapi_length)).
      rewrite subst_telescope_app in c.
      specialize (X _ _ c).
      rewrite context_assumptions_subst_telescope in X.
      destruct X as [dom codom].
      unshelve eexists.
      constructor; auto. simpl.
      pose proof (ctx_inst_sub_specE dom) as Hsub.
      simpl in *. rewrite Nat.add_0_r in codom. rewrite skipn_S.
      rewrite subst_app_telescope.
      apply make_context_subst_length in Hsub.
      rewrite subst_telescope_length Nat.add_0_r in Hsub.
      now rewrite Hsub Nat.add_0_r.
    - specialize (X (subst_telescope [b] 0 Γ0) ltac:(now rewrite /subst_telescope mapi_length)).
      rewrite subst_telescope_app in c.
      specialize (X _ _ c).
      rewrite context_assumptions_subst_telescope in X.
      destruct X as [dom codom].
      unshelve eexists.
      constructor; auto. simpl.
      pose proof (ctx_inst_sub_specE dom) as Hsub.
      simpl in *. rewrite Nat.add_0_r in codom.
      rewrite subst_app_telescope.
      apply make_context_subst_length in Hsub.
      rewrite subst_telescope_length Nat.add_0_r in Hsub.
      now rewrite Hsub Nat.add_0_r.
  Qed.

  Lemma ctx_inst_sub_eqE {Γ} {Δ : context} {Δ' args args'} (c : ctx_instE Σ Γ args Δ) (d : ctx_instE Σ Γ args' Δ') :
    args' = args ->
    Δ = Δ' -> ctx_inst_subE c = ctx_inst_subE d.
  Proof using Type.
    intros -> ->. induction c; depelim d; auto; simpl in *; now rewrite (IHc d).
  Qed.

  Lemma ctx_inst_app_subE {Γ} {Δ : context} {Δ' args} (c : ctx_instE Σ Γ args (Δ ++ Δ')) :
    let (dom, codom) := ctx_inst_app_invE c in
    ctx_inst_subE c = ctx_inst_subE codom ++ ctx_inst_subE dom.
  Proof using Type.
    destruct (ctx_inst_app_invE c).
    induction Δ using ctx_length_ind in Δ', c, x, args, c0 |- *. simpl in *. depelim x. simpl in *.
    rewrite app_nil_r; apply ctx_inst_sub_eqE. now rewrite skipn_0.
    now rewrite subst_telescope_empty.
    simpl in *. destruct d as [na [b|] ty]; simpl in *.
    depelim c; simpl in *.
    depelim x; simpl in *.
    injection H0. discriminate. injection H0. discriminate.
    specialize (H (subst_telescope [b] 0 Γ0) ltac:(now rewrite /subst_telescope mapi_length)).
    revert c. rewrite subst_telescope_app.
    intros c.
    specialize (H  _ _ c). simpl in *.
    revert H. rewrite context_assumptions_subst_telescope.
    intros.
    specialize (H x).
    revert c0. rewrite subst_app_telescope.
    rewrite (ctx_inst_subst_lengthE x) subst_telescope_length.
    intros c1.
    now rewrite (H c1) app_assoc.

    depelim c; depelim x; simpl in *.
    specialize (H (subst_telescope [i] 0 Γ0) ltac:(now rewrite /subst_telescope mapi_length)).
    revert c. rewrite subst_telescope_app. intros c.
    specialize (H _ _ c). simpl in *.
    revert H. rewrite context_assumptions_subst_telescope.
    intros.
    specialize (H x).
    revert c0. rewrite subst_app_telescope.
    rewrite (ctx_inst_subst_lengthE x) subst_telescope_length.
    intros c1.
    now rewrite (H c1) app_assoc.
  Qed.

  Lemma ctx_inst_defE {Γ args na b t} (c : ctx_instE Σ Γ args [vdef na b t]) :
    ((args = []) * (ctx_inst_subE c = [b]))%type.
  Proof using Type.
    depelim c; simpl in c. depelim c; simpl in *. constructor; simpl in *; auto.
  Qed.

  Lemma ctx_inst_assE {Γ args na t} (c : ctx_instE Σ Γ args [vass na t]) :
    ∑ i, ((args = [i]) * (typingE Σ Γ i t) * (ctx_inst_subE c = [i]))%type.
  Proof using Type.
    depelim c; simpl in *.
    depelim c. exists i; constructor; auto.
  Qed.

  Lemma ctx_inst_spine_substE {Γ Δ args} :
    wf_localE Σ (Γ ,,, Δ) ->
    forall ci : ctx_instE Σ Γ args (List.rev Δ),
    spine_substE Σ Γ args (ctx_inst_subE ci) Δ.
  Proof using wfΣ.
    move=> wfΔ ci.
    pose proof (ctx_inst_sub_specE ci) as msub.
    eapply make_context_subst_spec in msub.
    rewrite List.rev_involutive in msub.
    split; pcuic. now eapply All_local_env_app_inv in wfΔ as [].
    move: ci msub.
    induction Δ in wfΔ, args |- *.
    simpl. intros ci. depelim ci. constructor.
    intros. simpl in ci.
    pose proof (ctx_inst_app_subE ci).
    destruct (ctx_inst_app_invE ci). rewrite H in msub |- *.
    clear ci H.
    simpl in c.
    apply (@context_subst_app [a]) in msub.
    simpl in msub.
    destruct a as [na [b|] ty]; simpl in *.
    - pose proof (ctx_inst_defE c) as [Hargs Hinst].
      rewrite Hinst in msub |- *. simpl in *.
      destruct msub as [subl subr].
      rewrite skipn_S skipn_0 in subr.
      generalize dependent x. rewrite context_assumptions_rev.
      intros.
      depelim wfΔ.
      specialize (IHΔ _ wfΔ _ subr). constructor; auto.
      apply unlift_TermTyp in l.
      eapply (substitutionE (Δ := [])); eauto.
    - pose proof (ctx_inst_assE c) as [i [[Hargs Hty] Hinst]].
      rewrite Hinst in msub |- *. simpl in *.
      destruct msub as [subl subr].
      rewrite skipn_S skipn_0 in subr subl.
      generalize dependent x. rewrite context_assumptions_rev.
      intros.
      depelim wfΔ.
      specialize (IHΔ _ wfΔ _ subr). constructor; auto.
  Qed.

  Lemma spine_subst_ctx_instE {Γ Δ args s} :
    spine_substE Σ Γ args s Δ ->
    ctx_instE Σ Γ args (List.rev Δ).
  Proof using Type.
    move=> [wfd _ cs subsl].
    induction subsl in args, cs |- *.
    - depelim cs. constructor.
    - depelim cs.
      specialize (IHsubsl _ cs).
      unshelve eapply ctx_inst_appE; tea. cbn.
      rewrite /map_decl /=. repeat constructor.
      pose proof (ctx_inst_sub_specE IHsubsl) as msub.
      eapply make_context_subst_spec in msub.
      rewrite List.rev_involutive in msub.
      now pose proof (context_subst_fun cs msub); subst s.
    - depelim cs.
      specialize (IHsubsl _ cs). cbn.
      rewrite -(app_nil_r args).
      unshelve eapply ctx_inst_appE; tea. cbn.
      rewrite /map_decl /=. repeat constructor.
  Qed.

End WfEnv.

Lemma all_rels_substE {cf:checker_flags} Σ Δ Γ t :
  wfE Σ.1 -> wf_localE Σ (Γ ,,, Δ) ->
  red Σ.1 (Γ ,,, Δ) t (subst0 (all_rels Δ 0 #|Δ|) (lift #|Δ| #|Δ| t)).
Proof.
  intros wfΣ wf.
  assert(forall Γ' t (wf : wf_localE Σ Γ'),
    ((All_local_env_over (typingE Σ)
      (fun Γ' wfΓ' t T _ =>
        forall Γ Δ, Γ' = Γ ,,, Δ ->
        red Σ.1 (Γ ,,, Δ) t (subst0 (all_rels Δ 0 #|Δ|) (lift #|Δ| #|Δ| t)))
        Γ' wf) *
        (match t with
        | Some t => forall Γ Δ, Γ' = Γ ,,, Δ ->
            red Σ.1 (Γ ,,, Δ) t (subst0 (all_rels Δ 0 #|Δ|) (lift #|Δ| #|Δ| t))
        | None => unit  end))).
  clear t Δ Γ wf. intros Γ' t.
  Subterm.rec_wf_rel IH (Γ', t) (Subterm.lexprod (precompose lt (@length context_decl))
     (precompose lt (fun x => match x with Some t => S (PCUICSize.size t) | None => 0 end))).
  simpl.
  rename pr1 into cf.
  rename pr0 into Σ.
  rename pr2 into wfΣ.
  rename pr3 into Γ.
  rename pr4 into t. clear H0.
  intros wf.
  split.
  - specialize (IH cf Σ wfΣ).
    destruct wf.
    constructor.
    constructor.
    apply (IH Γ t ltac:(left; simpl; lia) wf).
    intros; subst Γ.
    now apply (IH (Γ0 ,,, Δ) (Some t0) ltac:(left; simpl; lia) wf).
    constructor; auto.
    apply (IH Γ t ltac:(left; simpl; lia) wf).
    intros.
    now apply (IH Γ (Some b) ltac:(left; simpl; lia) wf).
    now apply (IH Γ (Some t0) ltac:(left; simpl; lia) wf).

  - destruct t; [|exact tt].
    intros Γ0 Δ ->.
    rename Γ0 into Γ.
    specialize (IH cf Σ).
    assert (All_local_env_over (typingE Σ)
    (fun (Γ'0 : PCUICEnvironment.context) (_ : wf_localE Σ Γ'0)
       (t T : term) (_ : Σ;;; Γ'0 |-E t : T) =>
     forall Γ Δ : context,
     Γ'0 = Γ ,,, Δ ->
     red Σ.1 (Γ ,,, Δ) t (subst0 (all_rels Δ 0 #|Δ|) (lift #|Δ| #|Δ| t)))
    _ wf).
    { specialize (IH wfΣ (Γ ,,, Δ) None).
      forward IH. simpl. right. lia.
      apply (IH wf). }
    clear IH.

  change (Γ ,,, Δ) with (Γ ,,, Δ ,,, []).
  rewrite -{3}(Nat.add_0_r #|Δ|).
  change 0 with #|@nil context_decl| at 2 3.
  generalize (@nil context_decl) as Δ'.

  induction t using term_ind_size_app; try solve [constructor]; intros Δ'.
  * simpl.
     destruct (leb_spec_Set (#|Δ|  +#|Δ'|) n); simpl.
    **
      elim: leb_spec_Set => Hle.
      destruct (nth_error_spec (all_rels Δ 0 #|Δ|) (#|Δ| + n - #|Δ'|));
      rewrite all_rels_length in l0 |- *. lia.
      assert (#|Δ| + n - #|Δ| = n) as -> by lia.
      reflexivity. lia.
    **
      elim: leb_spec_Set => Hle.
      destruct (nth_error_spec (all_rels Δ 0 #|Δ|) (n - #|Δ'|));
      rewrite all_rels_length in l0 |- *; try lia.
      eapply nth_error_all_rels_spec in e.
      destruct e as [decl [Hnth Hdecl]].
      destruct decl as [? [?|] ?]; simpl in Hdecl; subst x.
      assert (n = #|Δ'| + (n - #|Δ'|)). lia.
      rewrite {1}H.
      change (tRel  (#|Δ'| + (n - #|Δ'|))) with
          (lift0 #|Δ'| (tRel (n - #|Δ'|))).
      eapply (weakening_red_cb (Γ' := [])); auto.
      { erewrite on_free_vars_ctx_on_ctx_free_vars; tea.
        clear X.
        now eapply wf_local_closed_contextE in wf. }
      { cbn. rewrite /PCUICOnFreeVars.shiftnP length_app. nat_compare_specs => //. }
      simpl.
      set (i := n - #|Δ'|) in *. clearbody i.
      clear l Hle H.

      etransitivity.
      + eapply red1_red. constructor.
        rewrite nth_error_app_lt; auto.
        rewrite Hnth. reflexivity.
      + rewrite -{1 3 4}(firstn_skipn (S i) Δ).
        rewrite app_context_assoc.
        assert (Hf:#|firstn (S i) Δ| = S i) by now rewrite firstn_length_le; lia.
        rewrite length_app Hf.
        rewrite all_rels_lift.
        erewrite <-(simpl_lift _ _ _ _ #|skipn (S i) Δ|); try lia.

        epose proof (distr_lift_subst (lift #|skipn (S i) Δ| (#|Δ| - S i) t)
        (all_rels (skipn (S i) Δ) 0 #|skipn (S i) Δ|) (S i) 0).
        rewrite Nat.add_0_r in H.
        autorewrite with len in H.
        rewrite -{}H.
        rewrite -{3 4}Hf.
        eapply (weakening_red_cb (Γ' := [])); auto. simpl.
        { clear X; apply wf_local_closed_contextE in wf.
          move: wf.
          erewrite on_free_vars_ctx_on_ctx_free_vars.
          rewrite !on_free_vars_ctx_app => /andP[] onΓ. erewrite onΓ => /=.
          rewrite -{1}(firstn_skipn (S i) Δ) on_free_vars_ctx_app => /andP[] //.
        }
        { clear X; eapply (All_local_env_nth_error (n:=i)) in wf.
          2: rewrite nth_error_app_lt; eassumption.
          rewrite skipn_app in wf.
          replace (S i - #|Δ|) with 0 in wf. 2:lia.
          rewrite skipn_0 in wf.
          rewrite /= in wf.
          move: wf => [] /subject_closedE //.
          rewrite is_open_term_closedE //. }
        rewrite length_skipn; simpl.
        apply All_local_env_over_2 in X.
        eapply (All_local_env_nth_error (n:=i)) in X.
        2: rewrite nth_error_app_lt; eassumption.
        destruct X as ((Hb & Xb) & s & (Ht & Xt) & _).
        specialize (Xb Γ (skipn (S i) Δ)).
        forward Xb. rewrite skipn_app. unfold app_context. f_equal.
        assert(S i - #|Δ| = 0) by lia. rewrite H. apply skipn_0.
        now rewrite length_skipn in Xb; try lia.
        now rewrite length_skipn.
      + simpl. assert(#|Δ'| + (n - #|Δ'|) = n) as -> by lia.
        reflexivity.
      + reflexivity.

  * simpl; eapply red_evar.
    do 2 apply All2_map_right.
    apply (All_All2 X0); auto.

  * simpl. eapply red_prod. auto.
    specialize (IHt2 (Δ' ,, vass n t1)).
    now rewrite -Nat.add_succ_r.

  * simpl; eapply red_abs; auto.
    rewrite -Nat.add_succ_r.
    eapply (IHt2 (Δ' ,, vass n _)).

  * simpl; eapply red_letin; auto.
    rewrite -Nat.add_succ_r.
    eapply (IHt3 (Δ' ,, vdef n _ _)).

  * simpl; eapply red_app; auto.
  * simpl. rewrite map_branches_k_map_branches_k.
    relativize (subst_predicate _ _ _).
    eapply red_case.
    5:{ reflexivity. }
    all:auto.
    + rewrite map_map_compose.
      apply All2_map_right. solve_all.
    + destruct X0 as [? [? ?]].
      specialize (r (Δ' ,,, inst_case_predicate_context p)).
      rewrite app_context_assoc in r. len in r.
      cbn. relativize (#|pcontext p| + (_ + _)). eapply r. lia.
    + red in X1 |- *.
      eapply All2_map_right; cbn; solve_all.
      eapply All_All2; tea.
      cbn; intros; solve_all.
      specialize (b (Δ' ,,, inst_case_branch_context p x)).
      rewrite app_context_assoc in b.
      len. rewrite -Nat.add_assoc (Nat.add_comm #|Δ|) Nat.add_assoc.
      relativize (#|bcontext x| + _). rewrite Nat.add_comm. eapply b.
      now len.

  * simpl; eapply red_proj_c. auto.

  * simpl; eapply red_fix_congr.
    do 2 eapply All2_map_right.
    eapply (All_All2 X0); simpl; intuition auto.
    rewrite length_map.
    specialize (b (Δ' ,,, fix_context m)).
    autorewrite with len in b.
    rewrite Nat.add_shuffle3.
    now rewrite app_context_assoc in b.

  * simpl. eapply red_cofix_congr.
    do 2 eapply All2_map_right.
    eapply (All_All2 X0); simpl; intuition auto.
    rewrite length_map.
    specialize (b (Δ' ,,, fix_context m)).
    autorewrite with len in b.
    rewrite Nat.add_shuffle3.
    now rewrite app_context_assoc in b.

  * cbn. destruct p as [? []]; cbn => //=.
    eapply red_primArray_congr; cbn in *; intuition eauto. solve_all.
- specialize (X (Γ ,,, Δ)  (Some t) wf). simpl in X.
  apply X. reflexivity.
Qed.

(** NOT a twin: [type_mkAppsE] ADDS [ClosedBodies Σ]. Base [type_mkApps] (in base's second
    section [WfEnv], whose [wf Σ] its proof does not use) has no environment premise; the E
    proof turns [ws_cumul_pbE] into the spec relation through [type_ws_cumul_pbE], which needs
    closed bodies ([ws_cumul_pbE_forget_spec]). It is stated here, outside the section, so that
    its premise is exactly [ClosedBodies Σ] and not the section's [wfE Σ]. *)
Lemma type_mkAppsE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ}
  {Γ t u T t_ty} :
  Σ ;;; Γ |-E t : t_ty ->
  typing_spineE Σ Γ t_ty u T ->
  Σ ;;; Γ |-E mkApps t u : T.
Proof.
  intros Ht Hsp.
  revert t Ht. induction Hsp; simpl; auto.
  intros t Ht. eapply type_ws_cumul_pbE; eauto.

  intros.
  specialize (IHHsp (tApp t0 hd)). apply IHHsp.
  destruct i as (_ & s & Hs & _).
  eapply typeE_App; eauto. eapply i0.2.π2.1.
  eapply type_ws_cumul_pbE; eauto.
Qed.

Section WfEnv.
  Context {cf} {Σ} {wfΣ : wfE Σ}.

  Lemma all_rels_subst_liftE {Δ Γ Δ' t} :
    wf_localE Σ (Γ ,,, Δ) ->
    is_closed_context (Γ ,,, Δ ,,, Δ') ->
    is_open_term (Γ ,,, Δ) t ->
    Σ ;;; Γ ,,, Δ ,,, Δ' ⊢E lift0 #|Δ'| t =
      subst0 (all_rels Δ #|Δ'| (#|Δ| + #|Δ'|)) (lift (#|Δ| + #|Δ'|) #|Δ| t).
  Proof using wfΣ.
    intros.
    rewrite Nat.add_comm.
    erewrite <-(simpl_lift _ _ _ _ #|Δ|); try lia.
    rewrite all_rels_lift.
    have dl := distr_lift_subst (lift #|Δ| #|Δ| t) (all_rels Δ 0 #|Δ|) #|Δ'| 0.
    rewrite Nat.add_0_r in dl.
    rewrite -{2}(all_rels_length Δ 0 #|Δ|) -{}dl.
    eapply (weakening_ws_cumul_pbE (Γ'' := Δ') (Γ' := [])) => // /=.
    apply red_ws_cumul_pbE.
    apply into_closed_red => //.
    eapply all_rels_substE; auto => //.
    eauto with fvs.
  Qed.

  Lemma spine_subst_to_extended_list_kE {Δ Γ : context} :
    wf_localE Σ (Γ ,,, Δ) ->
    spine_substE Σ (Γ ,,, Δ) (reln [] 0 Δ) (all_rels Δ 0 #|Δ|)
      (lift_context #|Δ| 0 Δ).
  Proof using wfΣ.
    move=> wf.
    assert (wf_localE Σ (Γ,,, Δ,,, lift_context #|Δ| 0 Δ)).
    { apply weakening_wf_localE; auto. }
    split; auto.
    { clear wf X.
      generalize 0 at 2 3.
      induction Δ at 2 3 4; intros n; rewrite ?lift_context_snoc0; simpl; auto.
      destruct a as [na [?|] ?]  => /=;
      rewrite /lift_decl /= /map_decl /=.
      specialize (IHc (S n)).
      eapply (context_subst_def _ _ _ _ (lift #|Δ| (#|c| + 0) t)) in IHc.
      rewrite Nat.add_1_r.
      rewrite all_rels_length.
      rewrite Nat.add_0_r in IHc |- *.
      apply IHc.
      rewrite reln_acc.
      constructor.
      specialize (IHc (S n)).
      now rewrite Nat.add_1_r. }

    move: X.
    generalize (@eq_refl _ Δ).
    change Δ with ([] ++ Δ) at 1 5.
    change 0 with (length (@nil context_decl)) at 2.
    generalize (@nil context_decl).
    induction Δ at 1 5 7 10; rewrite /= => l eql.
    - constructor.
    - specialize (IHc (l ++ [a])).
      rewrite -app_assoc in IHc. specialize (IHc eql).
      destruct a as [na [?|] ?]  => /=;
      rewrite lift_context_snoc /lift_decl /map_decl /=.
      * rewrite length_app /= Nat.add_1_r in IHc.
        rewrite all_rels_length Nat.add_0_r.
        intros X. specialize (IHc X).
        constructor; auto.
        assert (Some (Some t) = option_map decl_body (nth_error Δ #|l|)).
        destruct (nth_error_spec Δ #|l|).
        rewrite -eql in e.
        rewrite nth_error_app_ge in e. lia.
        rewrite Nat.sub_diag in e. simpl in e. noconf e. simpl. reflexivity.
        rewrite -eql in l0. autorewrite with len in l0. simpl in l0. lia.
        eapply (substitutionE (Δ := []) IHc); auto.
        rewrite lift_context0_app !app_context_assoc in X. cbn in X.
        eapply All_local_env_app_inv in X as [].
        rewrite lift_context_snoc0 Nat.add_0_r /= in a. cbn in a.
        depelim a. now apply unlift_TermTyp in l0.
      * rewrite length_app /= Nat.add_1_r in IHc.
        intros Hwf. specialize (IHc Hwf).
        constructor; auto.

        pose proof wf as wf'.
        rewrite -eql in wf'.
        rewrite !app_context_assoc in wf'.
        apply wf_localE_app_l in wf'. depelim wf'.
        rewrite Nat.add_0_r.
        eapply type_ws_cumul_pbE.
        constructor. auto.
        rewrite -eql nth_error_app_lt ?length_app /=; try lia.
        rewrite nth_error_app_ge // ?Nat.sub_diag //.
        apply lift_sorting_forget_rel in l0.
        apply lift_sorting_f_it_impl with (f := fun t => _ (_ t)) (tu := l0) => // Hs.
        set (s := l0.2.π1).
        change (tSort s) with
          (subst0 (all_rels c (S #|l|) #|Δ|) (lift #|Δ| #|c| (tSort s))).
        { eapply (substitutionE (Γ' := lift_context #|Δ| 0 c) (Δ := [])); cbn; auto.
          change (tSort s) with (lift #|Δ| #|c| (tSort s)).
          eapply (weakening_typingE); eauto. }
        eapply ws_cumul_pbE_eq_le. simpl.
        rewrite -{1}eql. simpl.
        rewrite !app_context_assoc.
        rewrite /app_context !app_assoc.

        epose proof (@all_rels_subst_liftE c Γ
        (l ++ [{|decl_name := na; decl_body := None; decl_type := decl_type|}]) decl_type).
        assert (#|Δ| = #|c| + S #|l|).
        { rewrite -eql. autorewrite with len. simpl. lia. }
        rewrite H. rewrite length_app /= in X.
        rewrite Nat.add_1_r in X.
        unfold app_context in X.
        rewrite !app_tip_assoc /= in X.
        rewrite -app_assoc.
        forward X by auto.
        apply X; auto. all:eauto with fvs.
        rewrite -app_tip_assoc app_assoc -[(l ++ _) ++ _]app_assoc eql.
        eapply All_local_env_app_inv in Hwf as []. eauto with fvs.
  Qed.

  Lemma type_it_mkProd_or_LetIn_invE {Γ Δ t s} :
    Σ ;;; Γ |-E it_mkProd_or_LetIn Δ t : tSort s ->
    ∑ Δs ts,
      [× sorts_local_ctx (lift_typing typingE) Σ Γ Δ Δs,
          Σ ;;; Γ ,,, Δ |-E t : tSort ts,
          wf_sort Σ s &
          leq_sort Σ (sort_of_products Δs ts) s].
  Proof using wfΣ.
    intros h. revert Γ t s h.
    induction Δ; intros.
    - exists [], s; splits. apply h. eauto with pcuic. apply leq_sort_refl.
    - destruct a as [na [b|] ty]; simpl in *;
      rewrite /mkProd_or_LetIn /= in h.
      * specialize (IHΔ _ _ _ h) as (Δs & ts & [sorts IHΔ leq]).
        exists Δs, ts.
        pose proof (PCUICWfUniversesEta.typing_wf_sortE _ IHΔ) as wfts.
        eapply inversion_LetInE in IHΔ as (T & wfty & HT & hlt); auto.
        split; eauto.
        eapply (type_ws_cumul_pbE (pb:=Cumul)). eapply HT. apply isType_SortE; pcuic.
        (* Base inverts the let-in and then compares reducts ([ws_cumul_pb_Sort_r_inv],
           [ws_cumul_pb_red]). Over η: the let-in inversion [ws_cumul_pbE_LetIn_l_inv], then
           the ζ-expansion of [T] under the let ([red_expand_letE]) and weakening of the
           inverted comparison by the let. *)
        eapply ws_cumul_pbE_LetIn_l_inv in hlt.
        have wfΓd := typingE_wf_local HT.
        transitivity (lift0 1 (T {0 := b})).
        { eapply red_ws_cumul_pbE. eapply red_expand_letE; tea.
          eapply type_closedE in HT. rewrite -is_open_term_closedE //. }
        change (tSort ts) with (lift0 1 (tSort ts)).
        eapply (weakening_ws_cumul_pbE (Γ := Γ ,,, Δ) (Γ' := []) (Γ'' := [_])) in hlt;
          [exact hlt|].
        eauto with fvs.

      * specialize (IHΔ _ _ _ h) as (Δs & ts & [sorts IHΔ leq]).
        eapply inversion_ProdE in IHΔ as (s1 & s2 & wfty & Ht & hlt); tea.
        exists (s1 :: Δs), s2. split; tea. split; tas.
        eapply ws_cumul_pbE_Sort_inv in hlt.
        transitivity (sort_of_products Δs ts); auto using leq_sort_product.
        simpl. eapply leq_sort_sort_of_products_mon.
        eapply Forall2_same. reflexivity.
        exact: hlt.
  Qed.

  Lemma inversion_it_mkProd_or_LetInE {Γ Δ t s} :
    Σ ;;; Γ |-E it_mkProd_or_LetIn Δ t : tSort s ->
    Σ ;;; Γ ,,, Δ |-E t : tSort s.
  Proof using wfΣ.
    move/type_it_mkProd_or_LetIn_invE => [Δs [ts [hΔ ht hs leq]]].
    eapply typeE_Cumul; tea. eapply typeE_Sort; pcuic.
    eapply cumulE_Sort.
    transitivity (sort_of_products Δs ts); auto using leq_sort_product.
    apply leq_sort_sort_of_products.
  Qed.

  Lemma isType_it_mkProd_or_LetIn_appE {Γ Δ Δ' args T s} :
    Σ ;;; Γ |-E it_mkProd_or_LetIn (Δ ,,, Δ') T : tSort s ->
    subsletE Σ Γ args (smash_context [] Δ) ->
    Σ ;;; Γ |-E subst_let_expand args Δ (it_mkProd_or_LetIn Δ' T) : tSort s.
  Proof using wfΣ.
    intros Hs sub.
    move: Hs. rewrite it_mkProd_or_LetIn_app.
    move/inversion_it_mkProd_or_LetInE => Hs.
    eapply typing_expand_letsE in Hs.
    eapply (substitutionE (Δ := [])) in Hs; tea.
  Qed.

  Lemma ctx_inst_sub_to_extended_list_kE Γ args Δ :
    forall inst : ctx_instE Σ Γ args Δ,
    map (subst0 (ctx_inst_subE inst)) (to_extended_list_k (List.rev Δ) 0) = args.
  Proof using Type.
    induction inst; simpl; rewrite /to_extended_list_k; auto.
    rewrite reln_app. simpl.
    have len := ctx_inst_subst_lengthE inst0.
    rewrite subst_telescope_length in len.
    rewrite List.length_rev.
    f_equal.
    rewrite nth_error_app_ge. lia.
    assert(#|Δ| + 0 - 0 - #|ctx_inst_subE inst0| = 0) as -> by lia.
    cbn. apply lift0_id.
    rewrite -{2}IHinst.
    rewrite -map_subst_app_simpl.
    rewrite -map_map_compose. f_equal.
    simpl. unfold to_extended_list_k.
    epose proof (reln_subst [] [i] (List.rev Δ) 0). simpl in H.
    rewrite subst_context_telescope in H.
    rewrite List.rev_involutive in H. rewrite H.
    now rewrite List.length_rev len.

    rewrite reln_app. simpl.
    have len := ctx_inst_subst_lengthE inst0.
    rewrite subst_telescope_length in len.
    rewrite -{2}IHinst.
    rewrite -map_subst_app_simpl.
    rewrite -map_map_compose. f_equal.
    simpl. unfold to_extended_list_k.
    epose proof (reln_subst [] [b] (List.rev Δ) 0). simpl in H.
    rewrite subst_context_telescope in H.
    rewrite List.rev_involutive in H. rewrite H.
    now rewrite List.length_rev len.
  Qed.

  Lemma spine_subst_subst_to_extended_list_kE {Γ args s Δ} :
    spine_substE Σ Γ args s Δ ->
    map (subst0 s) (to_extended_list_k Δ 0) = args.
  Proof using Type.
    intros [_ _ sub _].
    rewrite /to_extended_list_k.
    rewrite -(map_lift0 args).
    generalize 0 at 1 2 3.
    induction sub; simpl; auto.
    intros n.
    rewrite reln_acc.
    rewrite !map_app.
    simpl. rewrite Nat.leb_refl Nat.sub_diag /=.
    simpl.
    f_equal. rewrite -IHsub.
    rewrite reln_lift.
    rewrite (reln_lift 1).
    rewrite -{4}(Nat.add_0_r n).
    rewrite (reln_lift n 0).
    rewrite !map_map_compose.
    apply map_ext.
    intros x. rewrite (subst_app_decomp [a] s).
    f_equal. simpl.
    rewrite -(commut_lift_subst_rec _ _ _ 0)  //.
    rewrite simpl_subst_k //.

    intros n.
    rewrite -IHsub.
    rewrite reln_lift.
    rewrite (reln_lift 1).
    rewrite -{4}(Nat.add_0_r n).
    rewrite (reln_lift n 0).
    rewrite !map_map_compose.
    apply map_ext.
    intros x. rewrite (subst_app_decomp [subst0 s b] s).
    f_equal. simpl.
    rewrite -(commut_lift_subst_rec _ _ _ 0)  //.
    rewrite simpl_subst_k //.
  Qed.

  Lemma spine_subst_subst_to_extended_list_k_genE {Γ args s Δ Δ'} :
    spine_substE Σ Γ args s Δ ->
    to_extended_list_k Δ 0 = to_extended_list_k Δ' 0 ->
    map (subst0 s) (to_extended_list_k Δ' 0) = args.
  Proof using Type.
    intros sp <-; eapply spine_subst_subst_to_extended_list_kE; eauto.
  Qed.

  Lemma arity_spine_eqE {Γ T T'} :
    isTypeE Σ Γ T' ->
    T = T' -> arity_spineE Σ Γ T [] T'.
  Proof using Type. intros H ->; constructor;auto. Qed.

  Lemma typing_spine_wf_localE {Γ T args T'} :
    typing_spineE Σ Γ T args T' ->
    wf_localE Σ Γ.
  Proof using Type.
    move/typing_spine_isType_domE; pcuic.
  Qed.
  Hint Resolve typing_spine_wf_localE : pcuic.

  Lemma substitution_ws_cumul_pb_vassE {pb : conv_pb} {Γ} {a na ty M N} :
    Σ ;;; Γ |-E a : ty ->
    Σ ;;; Γ,, vass na ty ⊢E M ≤[pb] N ->
    Σ ;;; Γ ⊢E M{0 := a} ≤[pb] N{0 := a}.
  Proof using wfΣ.
    intros ha hm.
    eapply (substitution_ws_cumul_pbE_typed (Γ' := [vass na ty]) (s := [a]) (Γ'':=[])); eauto with pcuic.
  Qed.

  Lemma substitution_ws_cumul_pb_vdefE {pb : conv_pb} {Γ} {a na ty M N} :
    wf_localE Σ (Γ ,, vdef na a ty) ->
    Σ ;;; Γ,, vdef na a ty ⊢E M ≤[pb] N ->
    Σ ;;; Γ ⊢E M{0 := a} ≤[pb]  N{0 := a}.
  Proof using wfΣ.
    intros ha hm.
    eapply (substitution_ws_cumul_pbE_typed (Γ' := [vdef na a ty]) (s := [a]) (Γ'':=[])); eauto with pcuic.
    eapply subslet_def_tipE. depelim ha. now apply unlift_TermTyp in l.
  Qed.

  Lemma typing_spine_invE {Γ Δ : context} {T args args' T'} :
    #|args| = context_assumptions Δ ->
    typing_spineE Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T' ->
    ∑ args_sub,
      spine_substE Σ Γ args args_sub Δ *
      typing_spineE Σ Γ (subst0 args_sub T) args' T'.
  Proof using wfΣ.
    intros len.
    revert args len T.
    induction Δ as [|d Δ] using ctx_length_rev_ind; intros args. simpl.
    destruct args; simpl; try discriminate.
    - intros _ T sp; exists []. split; [repeat constructor|.. ]; auto; rewrite ?subst_empty //.
      all:pcuic.
    - rewrite context_assumptions_app => eq T sp.
      assert (wfΓΔ := isType_it_mkProd_or_LetIn_wf_localE (Δ := Δ ++ [d])
        (typing_spine_isType_domE sp)).
      rewrite it_mkProd_or_LetIn_app in sp.
      destruct d as [? [b|] ?]; simpl in *.
      + rewrite Nat.add_0_r in eq.
        eapply typing_spine_letin_invE in sp => //.
        rewrite /subst1 subst_it_mkProd_or_LetIn in sp.
        specialize (X (subst_context [b] 0 Δ) ltac:(now autorewrite with len)).
        specialize (X args ltac:(now rewrite context_assumptions_subst)).
        rewrite Nat.add_0_r in sp.
        destruct (X _ sp) as [args_sub [sps sp']].
        exists (args_sub ++ [b]); split; auto; [constructor|..]; pcuic.
        * eapply context_subst_app_inv.
          simpl. rewrite skipn_0.
          move: (context_subst_length sps).
          len.
          move=> eq'. rewrite eq'.
          rewrite skipn_all_app firstn_app_left //.
          split; auto. apply sps. rewrite -{2}(subst_empty 0 b).
          constructor. constructor.
        * eapply subslet_appE => //. eapply sps.
          rewrite -{1}(subst_empty 0 b).
          repeat constructor. rewrite !subst_empty.
          eapply All_local_env_app_inv in wfΓΔ as [_ wf].
          eapply All_local_env_app_inv in wf as [wfd _].
          depelim wfd. now eapply unlift_TermTyp.
        * rewrite subst_app_simpl.
          move: (context_subst_length sps).
          now  autorewrite with len => <-.

      + rewrite /mkProd_or_LetIn /= in sp.
        destruct args as [|a args]; simpl in eq; try lia.
        specialize (X (subst_context [a] 0 Δ) ltac:(now autorewrite with len)).
        specialize (X args ltac:(now rewrite context_assumptions_subst)).
        specialize (X (subst [a] #|Δ| T)).
        dependent elimination sp as [spconsE isty isty' e tyhd sp].
        eapply ws_cumul_pbE_Prod_Prod_inv in e as [eqna conv cum]; auto.
        eapply (substitution_ws_cumul_pb_vassE (a:=hd0)) in cum; auto.
        assert (Σ ;;; Γ |-E hd0 : decl_type).
        { eapply (type_ws_cumul_pbE (pb:=Conv)); tea. 2:now symmetry.
          now eapply isType_tProdE in isty as []; eauto with pcuic. }
        eapply isType_applyE in isty; tea.
        eapply typing_spine_strengthenE in sp. 3:tea. 2:tas.
        rewrite /subst1 subst0_it_mkProd_or_LetIn in sp; auto.
        specialize (X sp).
        destruct X as [args_sub [sps sp']].
        exists (args_sub ++ [hd0]); split; auto; [constructor|..]; pcuic.
        * eapply context_subst_app_inv.
          simpl. rewrite skipn_S skipn_0.
          move: (context_subst_length sps). len.
          move=> eq'. rewrite eq'.
          rewrite skipn_all_app firstn_app_left //.
          split; auto. apply sps.
          eapply (context_subst_ass _ []). constructor.
        * eapply subslet_appE => //. eapply sps.
          rewrite -{1}(subst_empty 0 hd0).
          repeat constructor. now rewrite !subst_empty.
        * rewrite subst_app_simpl.
          move: (context_subst_length sps).
          now autorewrite with len => <-.
  Qed.

  Arguments ctx_inst_nil {typing} {Γ}.
  Arguments PCUICTyping.ctx_inst_ass {typing} {Γ} {na t i inst Δ}.
  Arguments PCUICTyping.ctx_inst_def {typing} {Γ} {na b t inst Δ}.

  Lemma spine_subst_ctx_inst_subE {Γ args argsub Δ} (sp : spine_substE Σ Γ args argsub Δ) :
    ctx_inst_subE (spine_subst_ctx_instE sp) = argsub.
  Proof using Type.
    set (ci := spine_subst_ctx_instE sp).
    pose proof (ctx_inst_sub_specE ci).
    eapply make_context_subst_spec in H. rewrite List.rev_involutive in H.
    now rewrite (context_subst_fun sp H).
  Qed.

  Lemma typing_spine_ctx_instE {Γ Δ : context} {T args args' T'} :
    #|args| = context_assumptions Δ ->
    typing_spineE Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T' ->
    ∑ argsi : ctx_instE Σ Γ args (List.rev Δ),
      typing_spineE Σ Γ (subst0 (ctx_inst_subE argsi) T) args' T'.
  Proof using wfΣ.
    move=> len /(typing_spine_invE len) [argsub [sp Hargs']].
    exists (spine_subst_ctx_instE sp).
    now rewrite spine_subst_ctx_inst_subE.
  Qed.

  Lemma typing_spine_appE {Γ ty args na A B arg} :
    typing_spineE Σ Γ ty args (tProd na A B) ->
    Σ ;;; Γ |-E arg : A ->
    typing_spineE Σ Γ ty (args ++ [arg]) (B {0 := arg}).
  Proof using wfΣ.
    intros H; revert arg.
    dependent induction H.
    - intros arg Harg. simpl. econstructor; eauto.
      eapply isType_applyE in i0; tea.
      constructor; auto. eauto with fvs pcuic.
    - intros arg Harg.
      econstructor; eauto.
  Qed.

  Lemma typing_spine_nth_errorE {Γ Δ T args n arg concl} :
    typing_spineE Σ Γ (it_mkProd_or_LetIn Δ T) args concl ->
    nth_error args n = Some arg ->
    (n < context_assumptions Δ) ->
    ∑ decl, (nth_error (smash_context [] Δ) (context_assumptions Δ - S n) = Some decl) *
      (Σ ;;; Γ |-E arg : subst0 (List.rev (firstn n args)) (decl_type decl)).
  Proof using wfΣ.
    revert n args T.
    induction Δ using ctx_length_rev_ind => /= // n args T.
    - simpl. lia.
    - rewrite it_mkProd_or_LetIn_app context_assumptions_app.
      destruct d as [na [b|] ty]; simpl.
      + move=> sp. rewrite /= Nat.add_0_r. simpl.
        eapply typing_spine_letin_invE in sp => //.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
        specialize (X (subst_context [b] 0 Γ0) ltac:(len; lia) n args _ sp).
        rewrite context_assumptions_subst in X.
        move=> Hnth Hn. specialize (X Hnth Hn) as [decl [nthsmash Hty]].
        exists decl; split; auto.
        rewrite smash_context_app. simpl.
        now rewrite -(smash_context_subst []) /= subst_context_nil.
      + simpl.
        move=> sp.
        dependent elimination sp as [spnilE _ _ _|spconsE isty isty' e e' sp]; rewrite ?nth_error_nil //.
        destruct n as [|n']; simpl.
        * move=> [=] eq; subst hd0.
          move=> Hctx. exists {| decl_name := na; decl_body := None; decl_type := ty |}.
          rewrite smash_context_app. simpl.
          rewrite nth_error_app_ge; rewrite smash_context_length /=. lia.
          assert(context_assumptions Γ0 + 1 - 1 - context_assumptions Γ0 = 0) as -> by lia.
          split; auto. rewrite subst_empty.
          pose proof (isType_wf_localE isty).
          eapply ws_cumul_pbE_Prod_Prod_inv in e as [conv cum]; auto.
          eapply (type_ws_cumul_pbE (pb:=Conv)); eauto.
          eapply isType_tProdE in isty as [dom codom]; eauto with pcuic. cbn in *.
          now symmetry.
        * move=> Hnth Hn'.
          pose proof (isType_wf_localE isty).
          eapply isType_tProdE in isty as [dom' codom']; auto. cbn in *.
          eapply ws_cumul_pbE_Prod_Prod_inv in e as [conv cum e]; auto. simpl in codom'.
          assert (Σ ;;; Γ |-E hd0 : ty).
          { eapply (type_ws_cumul_pbE (pb:=Conv)); eauto with pcuic. now symmetry. }
          unshelve eapply (isType_substE (Δ:=[vass na ty]) (s := [hd0])) in codom'.
          2:{ now eapply subslet_ass_tipE. }
          specialize (X (subst_context [hd0] 0 Γ0) ltac:(autorewrite with len; lia)).
          eapply substitution_ws_cumul_pb_vassE in e; tea.
          specialize (X n' tl0 (subst [hd0] #|Γ0| T)).
          forward X.
          rewrite -subst0_it_mkProd_or_LetIn.
          eapply typing_spine_strengthenE; eauto.
          specialize (X Hnth).
          forward X by (rewrite context_assumptions_subst; lia).
          destruct X as [decl [Hnth' Hty]].
          rewrite (smash_context_subst []) nth_error_subst_context in Hnth'.
          rewrite smash_context_app. simpl.
          rewrite context_assumptions_subst in Hnth'.
          replace (context_assumptions Γ0  + 1 - S (S n')) with
            (context_assumptions Γ0 - S n') by lia.
          rewrite nth_error_app_context_lt ?smash_context_length. lia.
          destruct (nth_error (smash_context [] Γ0) _) eqn:Heq; try discriminate.
          simpl in Hnth'. exists c; split; auto.
          noconf Hnth'.
          rewrite /= smash_context_length /= in Hty.
          replace ((context_assumptions Γ0 - S (context_assumptions Γ0 - S n') + 0))
            with n' in Hty by lia.
          rewrite subst_app_simpl /= List.length_rev firstn_length_le.
          now eapply nth_error_Some_length in Hnth.
          assumption.
  Qed.

  Import PCUICInstDef PCUICInstConv.

  Local Open Scope sigma.

  Lemma spine_subst_smashE {Γ inst s Δ} :
    spine_substE Σ Γ inst s Δ ->
    spine_substE Σ Γ inst (List.rev inst) (smash_context [] Δ).
  Proof using wfΣ.
    intros [spine_dom_wf0 spine_codom_wf0 inst_ctx_subst0 inst_subslet0].
    assert (context_subst (smash_context [] Δ) inst (List.rev inst)).
    { apply closed_wf_localE in spine_dom_wf0.
      clear -inst_ctx_subst0 spine_dom_wf0. induction inst_ctx_subst0.
      constructor. rewrite List.rev_app_distr /=.
      rewrite smash_context_acc. simpl.
      constructor. auto.
      simpl. rewrite smash_context_acc. simpl. auto.
      auto. }
    split; auto.
    - eapply All_local_env_app; auto.
      eapply wf_local_rel_smash_contextE; auto.
    - induction inst_subslet0 in inst, inst_ctx_subst0, spine_codom_wf0 |- *.
      depelim inst_ctx_subst0.
      + constructor.
      + depelim inst_ctx_subst0.
        simpl. rewrite smash_context_acc.
        simpl. rewrite List.rev_app_distr.
        depelim spine_codom_wf0.
        constructor. now apply IHinst_subslet0.
        eapply meta_convE. eauto.
        simpl.
        autorewrite with sigma.
        apply inst_ext.
        unfold Upn. rewrite subst_consn_compose.
        autorewrite with sigma.
        apply subst_consn_proper.
        2:{ (rewrite subst_consn_shiftn; try now autorewrite with len); [].
            autorewrite with sigma.
            rewrite subst_consn_shiftn //.
            rewrite List.length_rev.
            now apply context_subst_length2 in inst_ctx_subst0. }
        clear -inst_ctx_subst0.
        rewrite map_inst_idsn. now autorewrite with len.
        now apply context_subst_extended_subst.
      + simpl. rewrite smash_context_acc.
        simpl. depelim spine_codom_wf0.
        depelim inst_ctx_subst0; apply IHinst_subslet0; auto.
  Qed.

  Lemma ctx_inst_sub_substE {Γ Δ : context} {args} :
    forall ci : ctx_instE Σ Γ args (List.rev Δ),
    ctx_inst_subE ci = map (subst0 (List.rev args)) (extended_subst Δ 0).
  Proof using Type.
    intros ci.
    pose proof (ctx_inst_sub_specE ci).
    eapply make_context_subst_spec in H.
    revert H. generalize (ctx_inst_subE ci). clear ci.
    intros l cs.
    apply context_subst_extended_subst in cs.
    rewrite List.rev_involutive in cs.
    rewrite cs. apply map_ext => t.
    now rewrite subst0_inst.
  Qed.

  Lemma typing_spine_ctx_inst_smashE {Γ Δ : context} {T args args' T'} :
    #|args| = context_assumptions Δ ->
    typing_spineE Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T' ->
    spine_substE Σ Γ args (List.rev args) (smash_context [] Δ) *
      typing_spineE Σ Γ (subst_let_expand (List.rev args) Δ T) args' T'.
  Proof using wfΣ.
    intros.
    pose proof (typing_spine_isType_domE X).
    eapply isType_it_mkProd_or_LetIn_wf_localE in X0.
    eapply typing_spine_ctx_instE in X as [argsi sp]; tea.
    unshelve epose proof (ctx_inst_spine_substE _ argsi).
    1: now pcuic.
    pose proof (spine_subst_smashE X). split => //.
    rewrite (ctx_inst_sub_substE argsi) in sp.
    rewrite /subst_let_expand.
    rewrite /expand_lets /expand_lets_k /=.
    rewrite distr_subst. len.
    rewrite simpl_subst_k. now len.
    assumption.
  Qed.

  Lemma arity_spine_it_mkProd_or_LetIn_smashE {Γ Δ T args args' T'} :
    subsletE Σ Γ (List.rev args) (smash_context [] Δ) ->
    arity_spineE Σ Γ (subst_let_expand (List.rev args) Δ T) args' T' ->
    arity_spineE Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T'.
  Proof using Type.
    intros subsl asp.
    rewrite /subst_let_expand /expand_lets /expand_lets_k in asp.
    move: Δ T args subsl asp.
    induction Δ using ctx_length_rev_ind => T args subsl asp.
    - simpl in subsl. simpl in asp. rewrite subst_empty lift0_id in asp. depelim subsl.
      rewrite /= H !subst_empty in asp. destruct args => //.
      simpl in H. apply (f_equal (@List.length _)) in H. simpl in H.
      rewrite length_app /= in H. lia.
    - rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
      destruct d as [na [b|] ty]; simpl in *.
      * constructor. rewrite /subst1 subst_it_mkProd_or_LetIn.
        rewrite Nat.add_0_r.
        rewrite smash_context_app smash_context_acc /= in subsl.
        rewrite  lift0_id /= subst_context_nil app_nil_r
          lift0_context in subsl.
        rewrite -(smash_context_subst []) /= subst_context_nil in subsl.
        rewrite subst_empty in subsl.
        apply (X (subst_context [b] 0 Γ0) ltac:(now autorewrite with len)
          (subst [b] #|Γ0| T) _ subsl).
        rewrite extended_subst_app /= in asp.
        rewrite !subst_empty lift0_id lift0_context in asp.
        erewrite subst_app_simpl' in asp.
        2:now autorewrite with len.
        simpl in asp. autorewrite with len in asp.
        simpl in asp.
        autorewrite with len.
        now rewrite -{1}(Nat.add_0_r #|Γ0|) distr_lift_subst_rec /= Nat.add_0_r.
      * simpl in *. len in asp.
        simpl in asp.
        assert (len:=subslet_lengthE subsl).
        len in len. simpl in len.
        rewrite Nat.add_1_r in len.
        rewrite smash_context_app smash_context_acc /= in subsl.
        rewrite subst_context_lift_id in subsl.
        eapply subslet_app_invE in subsl as [subsl subsr].
        destruct args; simpl in * => //.
        noconf len.
        len in subsl; len in subsr. simpl in *.
        rewrite -H in subsl subsr. rewrite skipn_all_app_eq ?List.length_rev in subsl subsr => //.
        rewrite (firstn_app_left) ?firstn_0 ?app_nil_r ?List.length_rev in subsr => //.
        depelim subsl.
        constructor. now rewrite subst_empty in t1.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r.
        rewrite -(smash_context_subst []) /= in subsr.
        apply (X (subst_context [t] 0 Γ0) ltac:(now autorewrite with len)
          (subst [t] #|Γ0| T) _ subsr).
        rewrite extended_subst_app /= in asp.
        rewrite subst_context_lift_id in asp.
        erewrite subst_app_simpl' in asp.
        2:now autorewrite with len.
        simpl in asp.
        autorewrite with len.
        rewrite -{1}(Nat.add_0_r #|Γ0|) distr_lift_subst_rec /= Nat.add_0_r.
        move: asp. rewrite subst_app_simpl /=; autorewrite with len.
        rewrite distr_subst. autorewrite with len.
        rewrite (distr_subst_rec _ _ [t]).
        cbn [map]. rewrite -H. erewrite (subst_rel_eq _ _ 0) =>//.
        simpl; autorewrite with len.
        rewrite (Nat.add_1_r #|args|).
        erewrite <-(simpl_lift T #|args| _ 1 (#|Γ0| + 1 + #|args|)).
        all:try lia.
        rewrite (simpl_subst_k) //.
        now rewrite subst_extended_subst H.
  Qed.

  (** This shows that we can promote an argument spine for a given context to
      a spine for a context whose types are higher in the cumulativity relation.
  *)

  Lemma subslet_cumulE {pb Δ args Γ Γ'} :
    assumption_context Γ -> assumption_context Γ' ->
    wf_localE Σ (Δ ,,, Γ) ->
    wf_localE Σ (Δ ,,, Γ') ->
    ws_cumul_ctx_pbE_rel pb Σ Δ Γ Γ' ->
    subsletE Σ Δ args Γ -> subsletE Σ Δ args Γ'.
  Proof using wfΣ.
    intros ass ass' wf wf' a2.
    destruct a2.
    induction a in wf, wf', args, ass, ass' |- *.
    - inversion 1; constructor.
    - intros subsl; depelim subsl.
      2:{ exfalso; inv ass. }
      specialize (IHa s).
      forward IHa by now depelim ass.
      forward IHa by now depelim ass'.
      depelim wf.
      depelim wf'.
      2:{ exfalso; inv ass'. }
      specialize (IHa wf wf' subsl).
      constructor; auto.
      eapply type_ws_cumul_pbE; eauto. depelim p.
      eapply isType_substE. exact IHa. eauto with pcuic.
      depelim p.
      eapply (substitution_ws_cumul_pbE_typed (s:=s) (Γ' := Γ) (Γ'' := [])); eauto.
  Qed.

  Lemma spine_subst_cumulE {Δ args Γ Γ'} :
    assumption_context Γ -> assumption_context Γ' ->
    wf_localE Σ (Δ ,,, Γ) ->
    wf_localE Σ (Δ ,,, Γ') ->
    ws_cumul_ctx_pbE_rel Cumul Σ Δ Γ Γ' ->
    spine_substE Σ Δ args (List.rev args) Γ ->
    spine_substE Σ Δ args (List.rev args) Γ'.
  Proof using wfΣ.
    intros ass ass' wf wf' a2.
    intros [spine_dom_wf0 spine_codom_wf0 inst_ctx_subst0 inst_subslet0]; split; auto.
    - clear -a2 ass ass' inst_ctx_subst0.
      revert inst_ctx_subst0; generalize (List.rev args).
      intros l ctxs.
      induction ctxs in ass, Γ', ass', a2 |- *; depelim a2; try (simpl in H; noconf H); try constructor; auto.
      * depelim a. constructor.
      * depelim a. depelim a0. econstructor. eapply IHctxs. now depelim ass.
        now depelim ass'. red. split => //.
      * exfalso; depelim ass.
    - eapply subslet_cumulE. 6:eauto. all:eauto.
  Qed.

  Lemma pre_type_mkApps_arityE {Γ t u tty T} :
    Σ;;; Γ |-E t : tty -> isTypeE Σ Γ tty ->
    arity_spineE Σ Γ tty u T ->
    Σ;;; Γ |-E mkApps t u : T.
  Proof using wfΣ.
    intros Ht Hty Har.
    eapply type_mkAppsE; tea.
    eapply wf_arity_spine_typing_spineE.
    constructor; tas.
  Qed.

  Local Set SimplIsCbn.

  Lemma spine_subst_extended_substE {Γ inst s Δ} :
    spine_substE Σ Γ inst s Δ ->
    s = map (subst0 (List.rev inst)) (extended_subst Δ 0).
  Proof using Type.
    intros [_ _ sp _]. now apply context_subst_subst_extended_subst in sp.
  Qed.

  Lemma spine_subst_appE {Γ Δ Δ' inst inst' insts} :
    #|inst| = context_assumptions Δ ->
    wf_localE Σ (Γ ,,, Δ ,,, Δ') ->
    spine_substE Σ Γ inst (skipn #|Δ'| insts) Δ ->
    spine_substE Σ Γ inst' (firstn #|Δ'| insts) (subst_context (skipn #|Δ'| insts) 0 Δ') ->
    spine_substE Σ Γ (inst ++ inst') insts (Δ ,,, Δ').
  Proof using Type.
    intros len wf [wfdom wfcodom cs subst] [wfdom' wfcodom' cs' subst'].
    split; auto.
    now rewrite app_context_assoc.
    eapply context_subst_app_inv; split; auto.
    rewrite skipn_all_app_eq; try lia. auto.
    rewrite (firstn_app_left) ?Nat.add_0_r // firstn_0 // app_nil_r //.
    rewrite -(firstn_skipn #|Δ'| insts).
    eapply subslet_appE; auto.
  Qed.
  Hint Rewrite @context_assumptions_lift @context_assumptions_subst : len.

  Lemma ws_cumul_ctx_pb_rel'_context_assumptionsE {pb} {Γ} {Δ Δ'} :
    All2_fold
      (fun Γ' _ : context =>
        All_decls_alpha_pb pb
          (fun pb (x y : term) => Σ ;;; Γ,,, Γ' ⊢E x ≤[pb] y)) Δ Δ' ->
    context_assumptions Δ = context_assumptions Δ'.
  Proof using Type.
    induction 1; auto.
    depelim p; simpl; auto. lia.
  Qed.

  (* The binder types are written: base's are inferred from base's [ws_cumul_ctx_pb_rel]
     ([list context_decl]), while [ws_cumul_ctx_pbE_rel] would infer [context], δ-equal but
     printed differently. The same holds for the three lemmas marked below. *)
  Lemma ws_cumul_ctx_pb_rel_context_assumptionsE {pb} {Γ : list context_decl} {Δ Δ' : list context_decl} :
    ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ' ->
    context_assumptions Δ = context_assumptions Δ'.
  Proof using Type.
    intros []. now eapply ws_cumul_ctx_pb_rel'_context_assumptionsE.
  Qed.

  (* Lemma subslet_subs {cf} {Σ} {wfΣ : wf Σ} {Γ i Δ Δ'} :
  ws_cumul_ctx_pb_rel pb Σ Γ Δ Δ' ->
  ctx_inst Σ Γ i (Li *)

  Lemma ws_cumul_pb_expand_lets_kE {pb} {Γ Δ Γ'} {T T'} :
    wf_localE Σ (Γ ,,, Δ) ->
    Σ ;;; Γ ,,, Δ ,,, Γ' ⊢E T ≤[pb] T' ->
    Σ ;;; Γ ,,, smash_context [] Δ ,,, expand_lets_ctx Δ Γ' ⊢E
      expand_lets_k Δ #|Γ'| T ≤[pb] expand_lets_k Δ #|Γ'| T'.
  Proof using wfΣ.
    intros wf cum.
    rewrite -app_context_assoc in cum.
    eapply (weakening_ws_cumul_pbE (Γ'' := smash_context [] Δ)) in cum; tea.
    rewrite /expand_lets /expand_lets_k.
    rewrite lift_context_app in cum.
    rewrite app_context_assoc in cum.
    eapply substitution_ws_cumul_pbE_typed in cum; tea.
    len in cum; tea.
    destruct (All_local_env_app_inv wf).
    simpl.
    len.
    now eapply PCUICContextsEta.subslet_extended_substE.
    eapply wf_local_smash_endE in wf. eauto with fvs.
  Qed.

  Lemma ws_cumul_pb_expand_letsE {pb} {Γ} {Δ} {T T'} :
    wf_localE Σ (Γ ,,, Δ) ->
    Σ ;;; Γ ,,, Δ ⊢E T ≤[pb] T' ->
    Σ ;;; Γ ,,, smash_context [] Δ ⊢E expand_lets Δ T ≤[pb] expand_lets Δ T'.
  Proof using wfΣ.
    intros wf cum.
    eapply (weakening_ws_cumul_pbE (Γ'' := smash_context [] Δ)) in cum; tea.
    rewrite /expand_lets /expand_lets_k.
    eapply (substitution_ws_cumul_pbE_typed (Γ'' := [])) in cum; tea. len in cum; tea.
    destruct (All_local_env_app_inv wf).
    simpl.
    len.
    now eapply PCUICContextsEta.subslet_extended_substE.
    eapply wf_local_smash_endE in wf. eauto with fvs.
  Qed.

  Lemma ws_cumul_pb_terms_liftE {Γ Δ args args'} :
    is_closed_context (Γ,,, Δ) ->
    ws_cumul_pbE_terms Σ Γ args args' ->
    ws_cumul_pbE_terms Σ (Γ ,,, Δ) (map (lift0 #|Δ|) args) (map (lift0 #|Δ|) args').
  Proof using wfΣ.
    intros onctx conv.
    eapply All2_map.
    eapply (All2_impl conv).
    intros x y eqxy.
    eapply (weakening_ws_cumul_pbE (Γ' := [])) => //.
  Qed.

  Lemma ws_cumul_pb_le_leE {pb Γ T T'} :
    Σ ;;; Γ ⊢E T ≤[pb] T' -> Σ ;;; Γ ⊢E T ≤ T'.
  Proof using Type.
    destruct pb; eauto.
    eapply ws_cumul_pbE_eq_le.
  Qed.

  Lemma ws_cumul_ctx_pb_le_leE {pb Γ Γ'} :
    ws_cumul_ctx_pbE pb Σ Γ Γ' -> ws_cumul_ctx_pbE Cumul Σ Γ Γ'.
  Proof using Type.
    intros a; eapply All2_fold_impl; tea.
    cbn; intros.
    depelim X; constructor; auto.
    now eapply ws_cumul_pb_le_leE.
    now eapply ws_cumul_pb_le_leE.
  Qed.

  Lemma ws_cumul_ctx_pb_eq_leE {pb Γ Δ} :
    ws_cumul_ctx_pbE Conv Σ Γ Δ -> ws_cumul_ctx_pbE pb Σ Γ Δ.
  Proof using Type.
    destruct pb; eauto.
    apply ws_cumul_ctx_pb_le_leE.
  Qed.

  Lemma subslet_ws_cumul_ctx_pbE {pb} {Γ Γ' Δ Δ'} {s} :
    wf_localE Σ (Γ ,,, Δ) ->
    wf_localE Σ (Γ ,,, Δ') ->
    ws_cumul_ctx_pbE_rel pb Σ Γ Δ' Δ ->
    subsletE Σ (Γ ,,, Δ) s Γ' ->
    subsletE Σ (Γ ,,, Δ') s Γ'.
  Proof using wfΣ.
    intros wfl wfr cumul.
    induction 1; constructor; auto.
    * eapply context_cumulativityE; tea.
      eapply ws_cumul_ctx_pbE_rel_app in cumul.
      eapply ws_cumul_ctx_pb_le_leE in cumul.
      now apply ws_cumul_ctx_pbE_forget in cumul.
    * eapply context_cumulativityE; tea.
      eapply ws_cumul_ctx_pbE_rel_app in cumul.
      eapply ws_cumul_ctx_pb_le_leE in cumul.
      now apply ws_cumul_ctx_pbE_forget in cumul.
  Qed.

  Arguments on_free_vars_ctx _ _ : simpl never.

  Lemma ws_cumul_ctx_pb_rel_conv_extended_substE {pb} {Γ Δ Δ'} :
    wf_localE Σ (Γ ,,, Δ) ->
    wf_localE Σ (Γ ,,, Δ') ->
    ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ' ->
    ws_cumul_pbE_terms Σ (Γ ,,, smash_context [] Δ) (extended_subst Δ 0) (extended_subst Δ' 0) ×
    ws_cumul_ctx_pbE_rel pb Σ Γ (smash_context [] Δ) (smash_context [] Δ').
  Proof using wfΣ.
    intros wfl wfr [clΓ cum].
    assert (is_closed_context (Γ ,,, smash_context [] Δ)).
    { eapply wf_local_smash_endE in wfl. eauto with fvs. }
    induction cum in |- *; simpl; auto.
    - split; constructor => //. constructor.
    - depelim p; simpl;
      depelim wfl; depelim wfr;
      specialize (IHcum wfl wfr) as [conv cum'];
      try assert (is_closed_context (Γ,,, smash_context [] Γ0)) by
       (rewrite /= smash_context_acc /= on_free_vars_ctx_snoc in H; now move/andP: H) => //.
      all:auto.
      * split; try constructor; auto.
        + eapply ws_cumul_pbE_refl => //. cbn. len.
        + rewrite !(lift_extended_subst _ 1).
          move: H.
          rewrite /= ![smash_context [_] _]smash_context_acc /= /map_decl /= => ha.
          eapply (ws_cumul_pb_terms_liftE (Δ := [_])) => //.
        + move: H; simpl; rewrite /= !(smash_context_acc _ [_]) /=;
          constructor; auto.
          apply cum'. rewrite /map_decl /=.
          constructor; auto.
          eapply ws_cumul_pb_expand_letsE in eqt; tea.
          etransitivity;tea. rewrite /expand_lets /expand_lets_k. simpl.
          rewrite -(length_of cum).
          rewrite -(ws_cumul_ctx_pb_rel'_context_assumptionsE cum).
          move: (context_assumptions_smash_context [] Γ0); cbn => <-. simpl.
          change (Γ ,,, smash_context [] Γ0) with (Γ ,,, smash_context [] Γ0 ,,, []).
          eapply (substitution_ws_cumul_pbE_subst_conv (Δ := [])); tea.
          { now eapply subslet_untyped_subsletE, PCUICContextsEta.subslet_extended_substE. }
          { eapply subslet_untyped_subsletE, subslet_ws_cumul_ctx_pbE. 3:tea.
            now eapply wf_local_smash_endE.
            now eapply wf_local_smash_endE.
            now eapply PCUICContextsEta.subslet_extended_substE. }
          relativize (context_assumptions Γ').
          eapply is_closed_context_lift; tea; eauto with fvs. len.
          now rewrite -(ws_cumul_ctx_pb_rel'_context_assumptionsE cum).
          eapply ws_cumul_pbE_refl.
          rewrite -[context_assumptions Γ0](smash_context_length []).
          eapply is_closed_context_lift; tea; eauto with fvs.
          rewrite -[context_assumptions Γ0](smash_context_length []); cbn.
          rewrite context_assumptions_smash_context /=.
          rewrite -[context_assumptions Γ0](smash_context_length []); cbn.
          relativize #|Γ0|.
          eapply is_open_term_lift.
          destruct l0 as (_ & s & Hs & _). eapply subject_closedE in Hs.
          rewrite is_open_term_closedE in Hs. move: Hs.
          now rewrite !length_app -(All2_fold_length cum). reflexivity.
      * split; auto.
        constructor; auto.
        len.
        eapply ws_cumul_pb_expand_letsE in eqb; tea.
        etransitivity; tea.
        rewrite /expand_lets /expand_lets_k. simpl.
        rewrite -(length_of cum).
        rewrite -(ws_cumul_ctx_pb_rel'_context_assumptionsE cum).
        move: (context_assumptions_smash_context [] Γ0); cbn => <-. simpl.
        change (smash_context [] Γ0 ++ Γ) with (Γ ,,, smash_context [] Γ0 ,,, []).
        cbn. rewrite smash_context_acc /=.
        change (smash_context [] Γ0 ++ Γ) with (Γ ,,, smash_context [] Γ0 ,,, []).
        eapply (substitution_ws_cumul_pbE_subst_conv (Δ := [])); tea.
        { now eapply subslet_untyped_subsletE, PCUICContextsEta.subslet_extended_substE. }
        { eapply subslet_untyped_subsletE, subslet_ws_cumul_ctx_pbE. 3:tea.
          now eapply wf_local_smash_endE.
          now eapply wf_local_smash_endE.
          now eapply PCUICContextsEta.subslet_extended_substE. }
        relativize (context_assumptions Γ').
        eapply is_closed_context_lift; tea; eauto with fvs. len.
        now rewrite -(ws_cumul_ctx_pb_rel'_context_assumptionsE cum).
        eapply ws_cumul_pbE_refl.
        rewrite -[context_assumptions Γ0](smash_context_length []).
        eapply is_closed_context_lift; tea; eauto with fvs.
        rewrite -[context_assumptions Γ0](smash_context_length []); cbn.
        rewrite context_assumptions_smash_context /=.
        rewrite -[context_assumptions Γ0](smash_context_length []); cbn.
        relativize #|Γ0|.
        eapply is_open_term_lift.
        eapply unlift_TermTyp, subject_closedE in l0.
        rewrite is_open_term_closedE in l0. move: l0.
        now rewrite !length_app -(All2_fold_length cum). reflexivity.
  Qed.

  Lemma ws_cumul_ctx_pb_rel_smashE {pb} {Γ Δ Δ'} :
    wf_localE Σ (Γ ,,, Δ) ->
    wf_localE Σ (Γ ,,, Δ') ->
    ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ' ->
    ws_cumul_ctx_pbE_rel pb Σ Γ (smash_context [] Δ) (smash_context [] Δ').
  Proof using wfΣ.
    now intros; apply ws_cumul_ctx_pb_rel_conv_extended_substE.
  Qed.

  Lemma ws_cumul_pb_terms_ws_cumul_ctxE {pb} {Γ Δ Δ'} {ts ts'} :
    wf_localE Σ (Γ ,,, Δ) ->
    wf_localE Σ (Γ ,,, Δ') ->
    ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ' ->
    ws_cumul_pbE_terms Σ (Γ ,,, Δ') ts ts' ->
    ws_cumul_pbE_terms Σ (Γ ,,, Δ) ts ts'.
  Proof using wfΣ.
    intros wfl wfr cum conv.
    eapply (All2_impl conv).
    intros x y xy.
    eapply ws_cumul_pbE_ws_cumul_ctx_pb.
    now eapply ws_cumul_ctx_pbE_rel_app in cum.
    assumption.
  Qed.

  (* Binder types written as in [ws_cumul_ctx_pb_rel_context_assumptionsE]. *)
  Lemma ws_cumul_ctx_pb_rel_lengthE {pb} {Γ Δ Δ' : list context_decl} :
    ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ' ->
    #|Δ| = #|Δ'|.
  Proof using Type. intros []. apply (length_of a). Qed.

  Hint Resolve is_closed_context_smash_end : fvs.

  Lemma ws_cumul_pb_expand_lets_ws_cumul_ctxE {pb le'} {Γ} {Δ Δ'} {T T'} :
    wf_localE Σ (Γ ,,, Δ) ->
    wf_localE Σ (Γ ,,, Δ') ->
    Σ ;;; Γ ,,, Δ ⊢E T ≤[le'] T' ->
    ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ' ->
    Σ ;;; Γ ,,, smash_context [] Δ ⊢E expand_lets Δ T ≤[le'] expand_lets Δ' T'.
  Proof using wfΣ.
    intros wfl wfr cum cumΓ.
    rewrite /expand_lets /expand_lets_k.
    rewrite -(ws_cumul_ctx_pb_rel_lengthE cumΓ) /=.
    rewrite -(ws_cumul_ctx_pb_rel_context_assumptionsE cumΓ).
    change (Γ ,,, smash_context [] Δ) with (Γ ,,, smash_context [] Δ ,,, []).
    eapply (substitution_ws_cumul_pbE_subst_conv (Δ := [])); tea.
    3:{ eapply ws_cumul_ctx_pb_rel_conv_extended_substE; tea. }
    * eapply subslet_untyped_subsletE, PCUICContextsEta.subslet_extended_substE; tea.
    * eapply subslet_untyped_subsletE, subslet_ws_cumul_ctx_pbE; cycle 2.
      + eapply ws_cumul_ctx_pb_rel_smashE; tea.
      + eapply PCUICContextsEta.subslet_extended_substE; tea.
      + now eapply wf_local_smash_endE.
      + now eapply wf_local_smash_endE.
    * simpl.
      rewrite -(ws_cumul_ctx_pb_rel_context_assumptionsE cumΓ).
      rewrite -[context_assumptions _](smash_context_length [] Δ).
      eapply is_closed_context_lift; eauto with fvs.
    * rewrite -[context_assumptions _](smash_context_length [] Δ).
      eapply weakening_ws_cumul_pbE => //; eauto with fvs.
  Qed.

  (* Binder types written as in [ws_cumul_ctx_pb_rel_context_assumptionsE]. *)
  Lemma ctx_inst_cumulE {pb} {Γ : list context_decl} {i} {Δ Δ' : list context_decl} :
    ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ' ->
    ctx_instE Σ Γ i (List.rev Δ) ->
    wf_local_relE Σ Γ Δ ->
    wf_local_relE Σ Γ Δ' ->
    ctx_instE Σ Γ i (List.rev Δ').
  Proof using wfΣ.
    intros [clΓ a].
    induction a in i |- *; intros ci.
    - depelim ci. constructor.
    - simpl in ci. eapply ctx_inst_app_invE in ci as [dom codom].
      depelim p.
      * simpl in codom. depelim codom.
        simpl in codom. depelim codom. cbn in t1.
        destruct i as [|i t0] using rev_case.
        { rewrite skipn_nil in H => //. }
        assert (context_assumptions (List.rev Γ0) = #|i|).
        apply (f_equal (@length _)) in H. simpl in H.
        rewrite List.length_skipn length_app /= in H. lia.
        rewrite skipn_all_app_eq // in H. noconf H.
        intros HΔ; depelim HΔ.
        intros HΔ'; depelim HΔ'.
        destruct l0 as (_ & s & Hs & _). simpl.
        rewrite (ctx_inst_sub_substE dom) in t1.
        rewrite firstn_app_left // in dom.
        specialize (IHa _ dom HΔ HΔ').
        eapply (ctx_inst_appE IHa).
        simpl. constructor; [|constructor].
        rewrite (ctx_inst_sub_substE IHa).
        rewrite firstn_app_left // in t1.
        simpl.
        rewrite context_assumptions_rev in H0.
        assert (context_assumptions Γ' = #|i|) by now rewrite -(ws_cumul_ctx_pb_rel'_context_assumptionsE a).
        rewrite map_subst_expand_lets in t1; len=> //.
        rewrite map_subst_expand_lets; len=> //.
        unshelve epose proof (ctx_inst_spine_substE _ IHa); tea.
        now eapply typingE_wf_local in Hs.
        eapply spine_subst_smashE in X; tea.
        eapply type_ws_cumul_pbE; tea.
        + eapply typing_expand_letsE in Hs.
          eapply (substitutionE (s := List.rev i) (Δ := [])) in Hs; tea.
          simpl in Hs. eapply has_sort_isTypeE. now rewrite subst_context_nil /= in Hs.
          exact X.
        + unshelve epose proof (ctx_inst_spine_substE _ dom); tea.
          eapply All_local_env_app; tea. now eapply typingE_wf_local.
          pose proof (spine_codom_wfE _ _ _ _ _ X0).
          eapply spine_subst_smashE in X0; tea.
          eapply (substitution_ws_cumul_pbE_typed (Γ := Γ) (Γ'' := []) X0).
          simpl.
          eapply ws_cumul_pb_expand_lets_ws_cumul_ctxE; tea.
          now eapply typingE_wf_local in Hs. split; tea.
    * simpl in codom. depelim codom.
      simpl in codom. depelim codom.
      assert (context_assumptions (List.rev Γ0) = #|i|).
      pose proof (ctx_inst_length dom).
      apply (f_equal (@length _)) in H. simpl in H.
      rewrite List.length_skipn /= in H.
      apply firstn_length_le_inv in H0. lia.
      rewrite H0 in H, dom. rewrite firstn_all in dom.
      intros HΔ; depelim HΔ.
      intros HΔ'; depelim HΔ'.
      destruct l as (Hb & s & Hs & _). simpl in *.
      destruct l0 as (Hb' & s' & Hs' & _). simpl in *.
      specialize (IHa _ dom).
      forward IHa. apply All_local_env_app_inv; pcuic.
      forward IHa. apply All_local_env_app_inv; pcuic.
      rewrite -(app_nil_r i).
      eapply (ctx_inst_appE IHa).
      rewrite (ctx_inst_sub_substE IHa) /=.
      repeat constructor.
  Qed.

  Lemma ctx_inst_smash_accE {Γ i Δ} :
    ctx_instE Σ Γ i Δ <~>
    ctx_instE Σ Γ i (List.rev (smash_context [] (List.rev Δ))).
  Proof using Type.
    split.
    - induction 1.
      + constructor.
      + simpl.
        rewrite smash_context_app_ass. len.
        rewrite List.rev_app_distr /=.
        constructor. auto.
        rewrite subst_telescope_subst_context.
        rewrite -smash_context_subst /=; len.
        now rewrite subst_context_rev_subst_telescope.
      + simpl. rewrite smash_context_app_def.
        now rewrite subst_context_rev_subst_telescope.
    - induction Δ using ctx_length_ind in i |- *; simpl; auto.
      destruct d as [na [b|] ty] => /=.
      * rewrite smash_context_app_def /=.
        rewrite subst_context_rev_subst_telescope.
        intros ctxi. constructor.
        apply X => //. now rewrite subst_telescope_length //.
      * rewrite smash_context_app_ass List.rev_app_distr /=.
        intros ctxi; depelim ctxi.
        constructor => //.
        apply X. rewrite subst_telescope_length //.
        rewrite subst_telescope_subst_context in ctxi.
        rewrite -(smash_context_subst []) in ctxi.
        now rewrite subst_context_rev_subst_telescope in ctxi.
  Qed.

  Lemma ctx_inst_smashE {Γ i Δ} :
    ctx_instE Σ Γ i (List.rev Δ) <~>
    ctx_instE Σ Γ i (List.rev (smash_context [] Δ)).
  Proof using Type.
    split; intros.
    - apply (fst ctx_inst_smash_accE) in X. now rewrite List.rev_involutive in X.
    - apply (snd ctx_inst_smash_accE). now rewrite List.rev_involutive.
  Qed.

  (* Binder types written as in [ws_cumul_ctx_pb_rel_context_assumptionsE]. *)
  Lemma ws_cumul_ctx_pb_rel_transE {pb} {Γ Δ Δ' Δ'' : list context_decl} :
    ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ' ->
    ws_cumul_ctx_pbE_rel pb Σ Γ Δ' Δ'' ->
    ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ''.
  Proof using wfΣ.
    move/ws_cumul_ctx_pbE_rel_app => h /ws_cumul_ctx_pbE_rel_app h'.
    apply ws_cumul_ctx_pbE_rel_app.
    now etransitivity.
  Qed.

  Lemma OnOne2_ctx_instE {pb} {P} {Γ inst inst' Δ} :
    (forall Γ Δ' Δ s s', wf_localE Σ (Γ ,,, Δ' ,,, Δ) ->
    subsletE Σ Γ (List.rev s) Δ' ->
    subsletE Σ Γ (List.rev s') Δ' ->
    OnOne2 (P Σ Γ) s s' ->
    ws_cumul_ctx_pbE pb Σ (Γ ,,, subst_context (List.rev s) 0 Δ)
      (Γ ,,, subst_context (List.rev s') 0 Δ)) ->
    wf_localE Σ (Γ ,,, (List.rev Δ)) ->
    PCUICTyping.ctx_inst
      (fun (Γ : context) (t T : term) =>
      forall u : term, P Σ Γ t u -> Σ;;; Γ |-E u : T) Γ inst Δ ->
    ctx_instE Σ Γ inst Δ ->
    OnOne2 (P Σ Γ) inst inst' ->
    ctx_instE Σ Γ inst' Δ.
  Proof using wfΣ.
    intros HP wf c.
    induction c in inst', wf |- *; intros ctxi; depelim ctxi; intros o.
    - depelim o.
    - depelim o. constructor. apply t0. auto.
      rewrite -(List.rev_involutive Δ).
      rewrite subst_telescope_subst_context.
      simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf.
      eapply ctx_inst_cumulE.
      2:{ instantiate (1:=subst_context [i] 0 (List.rev Δ)).
          rewrite -subst_telescope_subst_context List.rev_involutive. exact ctxi. }
      eapply ws_cumul_ctx_pbE_rel_app.
      eapply (HP _ _ _ [i] [hd']); tea.
      repeat constructor. now rewrite subst_empty. repeat constructor.
      now rewrite subst_empty. constructor. auto.
      eapply All_local_env_app_inv. eapply substitution_wf_localE; tea.
      repeat (constructor; tea). rewrite subst_empty; tea.
      eapply All_local_env_app_inv. eapply substitution_wf_localE; tea.
      repeat (constructor; tea). rewrite subst_empty; tea. now eapply t0.
      constructor; auto. eapply IHc.
      rewrite -subst_context_subst_telescope.
      eapply substitution_wf_localE; tea.
      repeat (constructor; tea). rewrite subst_empty; tea.
      simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf.
      exact wf. tas. tas.
    - constructor. eapply IHc; eauto.
      simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf.
      rewrite -subst_context_subst_telescope.
      eapply substitution_wf_localE; tea.
      repeat (constructor; tea). eapply subslet_def_tipE.
      eapply All_local_env_app_inv in wf as [wf _]. depelim wf. now eapply unlift_TermTyp.
  Qed.

  Lemma All2_ctx_instE {pb} {P} {Γ inst inst' Δ} :
    (forall Γ Δ' Δ s s', wf_localE Σ (Γ ,,, Δ' ,,, Δ) ->
    subsletE Σ Γ (List.rev s) Δ' ->
    subsletE Σ Γ (List.rev s') Δ' ->
    All2 (P Σ Γ) s s' ->
    ws_cumul_ctx_pbE pb Σ (Γ ,,, subst_context (List.rev s) 0 Δ)
      (Γ ,,, subst_context (List.rev s') 0 Δ)) ->
    wf_localE Σ (Γ ,,, (List.rev Δ)) ->
    PCUICTyping.ctx_inst
      (fun (Γ : context) (t T : term) =>
      forall u : term, P Σ Γ t u -> Σ;;; Γ |-E u : T) Γ inst Δ ->
    ctx_instE Σ Γ inst Δ ->
    All2 (P Σ Γ) inst inst' ->
    ctx_instE Σ Γ inst' Δ.
  Proof using wfΣ.
    intros HP wf c.
    induction c in inst', wf |- *; intros ctxi; depelim ctxi; intros o.
    - depelim o. constructor.
    - depelim o. constructor. apply t0. auto.
      rewrite -(List.rev_involutive Δ).
      rewrite subst_telescope_subst_context.
      simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf.
      eapply ctx_inst_cumulE.
      2:{ instantiate (1:=subst_context [i] 0 (List.rev Δ)).
          rewrite -subst_telescope_subst_context List.rev_involutive. eapply IHc => //.
          rewrite -subst_context_subst_telescope.
          eapply substitution_wf_localE; tea.
          repeat (constructor; tea). rewrite subst_empty; tea. }
      eapply ws_cumul_ctx_pbE_rel_app.
      eapply (HP _ _  _ [i] [y]); tea.
      repeat constructor. now rewrite subst_empty.
      now apply subslet_ass_tipE.
      now repeat constructor.
      * eapply All_local_env_app_inv. eapply substitution_wf_localE; tea.
        now apply subslet_ass_tipE.
      * eapply All_local_env_app_inv. eapply substitution_wf_localE; tea.
        now apply subslet_ass_tipE.
    - constructor. eapply IHc; eauto.
      simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf.
      rewrite -subst_context_subst_telescope.
      eapply substitution_wf_localE; tea.
      repeat (constructor; tea). eapply subslet_def_tipE.
      eapply All_local_env_app_inv in wf as [wf _]. depelim wf. now eapply unlift_TermTyp.
  Qed.

  Lemma ctx_inst_open_termsE Γ args Δ :
    ctx_instE Σ Γ args Δ ->
    All (is_open_term Γ) args.
  Proof using wfΣ.
    induction 1; try constructor; eauto using subject_is_open_termE.
  Qed.

  Lemma subslet_open_termsE Γ s Δ :
    subsletE Σ Γ s Δ ->
    All (is_open_term Γ) s.
  Proof using wfΣ.
    induction 1; try constructor; eauto using subject_is_open_termE.
  Qed.

  Lemma ctx_inst_eq_contextE {Γ Δ : context} {args args'} :
    wf_localE Σ (Γ ,,, List.rev Δ) ->
    PCUICTyping.ctx_inst
          (fun (Γ : context) (u A : term) =>
          forall v : term, upto_names' u v -> Σ;;; Γ |-E v : A) Γ args Δ ->
    ctx_instE Σ Γ args Δ ->
    All2 upto_names' args args' ->
    ctx_instE Σ Γ args' Δ.
  Proof using wfΣ.
    intros wf ctxi ctxi' a.
    eapply All2_ctx_instE; tea.
    2:exact ctxi. 2:auto.
    cbn; clear -wfΣ; intros.
    eapply substitution_ws_cumul_ctx_pbE.
    now eapply subslet_untyped_subsletE.
    now eapply subslet_untyped_subsletE.
    eapply All2_rev.
    move/All_local_env_app_inv: X => [] /All_local_env_app_inv[] /wf_local_closed_contextE clΓ0 _ _.
    eapply subslet_open_termsE, All_rev_inv in X0.
    eapply subslet_open_termsE, All_rev_inv in X1.
    solve_all. eapply into_ws_cumul_pbE_spec; tea.
    apply eq_term_upto_univ_cumulSpecE. now apply upto_names_impl_eq_term.
    all:eauto with fvs.
  Qed.

End WfEnv.

Lemma spine_subst_vassE `{cf: checker_flags} Σ Γ s t σ Δ na A :
  wfE Σ.1 ->
  spine_substE Σ Γ s σ Δ ->
  lift_typing typingE Σ (Γ ,,, Δ) (j_vass na A) ->
  Σ ;;; Γ |-E t : subst0 σ A ->
  spine_substE Σ Γ (s ++ [t]) (t :: σ) (Δ ,, vass na A).
Proof.
  move=> wfΣ sss Atyp ttyp; move: (sss)=> [????].
  change (?x ,, ?y) with (x ,,, [ y ]).
  apply: spine_subst_appE=> //=.
  + apply: PCUICContextSubst.context_subst_length2; eassumption.
  + apply: localenv_cons_abs=> //.
  + rewrite /skipn /subst_context /fold_context_k /= /map_decl /=.
    constructor=> //=.
    * apply: localenv_cons_abs=> //.
      apply: isTypeRel_substE; eassumption.
    * apply: (PCUICContextSubst.context_subst_ass [] [] [] na _ t); constructor.
    * econstructor; first constructor.
      by rewrite PCUICLiftSubst.subst_empty.
Qed.

Lemma wf_local_nth_isTypeRelE {cf} {Σ} {Γ n d} :
  wf_localE Σ Γ ->
  nth_error Γ n = Some d ->
  isTypeRelE Σ (skipn (S n) Γ) d.(decl_type) d.(decl_name).(binder_relevance).
Proof.
  intros Hwf hnth.
  eapply All_local_env_nth_error in Hwf; tea.
  now apply lift_sorting_forget_body in Hwf.
Qed.

Lemma spine_subst_vass'E `{cf:checker_flags} Σ Γ s t σ Δ na A :
  wfE Σ.1 ->
  spine_substE Σ Γ s σ Δ ->
  wf_localE Σ (Γ ,,, Δ ,, vass na A) ->
  (spine_substE Σ Γ s σ Δ ->
    isTypeE Σ Γ (subst0 σ A) ->
    Σ ;;; Γ |-E t : subst0 σ A) ->
  spine_substE Σ Γ (s ++ [t]) (t :: σ) (Δ ,, vass na A).
Proof.
  move=> wfΣ sss Atyp /(_ sss) ttyp; apply: spine_subst_vassE=> //.
  2: apply: ttyp; apply: isType_substE; first (apply: inst_subsletE; eassumption).
  all: exact (wf_local_nth_isTypeRelE (n := 0) Atyp eq_refl).
Qed.

Lemma mk_ctx_subst_spec'E `{cf : checker_flags} {Σ Γ Δ args} (c : ctx_instE Σ Γ args (List.rev Δ)) :
  mk_ctx_subst Δ args = ctx_inst_subE c.
Proof.
  apply: context_subst_fun.
  - apply: mk_ctx_subst_spec; by rewrite (ctx_inst_length c) context_assumptions_rev.
  - move: (ctx_inst_sub_specE c)=> /make_context_subst_spec.
    rewrite {1}rev_involutive //.
Qed.

Section ClosedSpineSubst.
  Context `{cf: checker_flags}.

  Lemma closed_subsletE {Σ} {wfΣ : wfE Σ.1} {Γ s Δ} : subsletE Σ Γ s Δ -> forallb (closedn #|Γ|) s.
  Proof using cf.
    move=> z; depind z=> //=; rewrite IHz andb_true_r;
    apply: PCUICClosedTypEta.subject_closedE; eassumption.
  Qed.

  Lemma closed_spine_substE {Σ} {wfΣ : wfE Σ.1} {Γ inst s Δ} :
    spine_substE Σ Γ inst s Δ -> forallb (closedn #|Γ|) s.
  Proof using cf. move=> /inst_subsletE; apply: closed_subsletE.  Qed.

  Lemma closed_spine_subst_instE {Σ} {wfΣ : wfE Σ.1} {Γ inst s Δ} :
    spine_substE Σ Γ inst s Δ -> forallb (closedn #|Γ|) inst.
  Proof using cf.
    move=> /spine_subst_smashE /closed_spine_substE; by rewrite forallb_rev.
  Qed.
End ClosedSpineSubst.
