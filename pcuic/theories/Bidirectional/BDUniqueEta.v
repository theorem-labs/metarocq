(* Distributed under the terms of the MIT license.   *)

(** * Uniqueness of inferred types over the η relations (plan row T6): the E copy of [BDUnique]

  A copy of base [Bidirectional/BDUnique.v] over the landed bidirectional E judgments
  ([BDTypingEta]: [inferingE], [checkingE], ...): [wf] → [wfE], [wf_local] → [wf_localE],
  [typing] → [typingE], [isTypeRel] → [isTypeRelE], the bidirectional judgments → their E
  copies, [env_prop_bd] → [env_prop_bdE], the scoped conversion [Σ ;;; Γ ⊢ _ ≤ _] / [⊢ _ = _]
  ([ws_cumul_pb]) → [⊢E] ([ws_cumul_pbE]), [ws_cumul_pb_terms] → [ws_cumul_pbE_terms]. Nothing
  else changes in a statement: the reductions [Σ ;;; Γ ⊢ T ⇝ T'] ([closed_red]) and [red_terms]
  are base's, as the E judgments' [▹□], [▹Π] and [▹{}] use base [red]. Each name takes the
  suffix [E] (plan [t0-plan.md] §2, D1). Map, base → E: [bidirectional_unique] →
  [bidirectional_uniqueE]; [infering_unique], [infering_unique'], [infering_checking],
  [infering_sort_sort], [infering_sort_infering], [infering_prod_prod], [infering_prod_prod'],
  [infering_prod_infering], [infering_ind_ind], [infering_ind_ind'], [infering_ind_infering],
  [principal_type], [isTypeRel_unique] → the same name with [E].

  ** The statements are true over η (checked before the proofs)

  Uniqueness here is up to a COMMON REDUCT for [red], not up to conversion: the inferred type is
  computed syntactically from the term, and the only places where a type is read off another are
  [▹□], [▹Π] and [▹{}], which reduce with base [red]. The η rules enter the E judgments only
  through [checkingE] (a [JoinE] premise) and the parameter comparison of [inferE_Case]
  ([All2 (JoinE ..)]), and neither produces an inferred type: [inferE_Case]'s type is
  [mkApps ptm (skipn npar args ++ [c])], with [ptm] read from the predicate and [args] from the
  scrutinee's [▹{}]. So every case of base's induction goes through with base confluence of
  [red], and so do the syntactic conclusions ([u = u'] for [▹□], [na = na'] for [▹Π],
  [ind = ind'] and [u = u'] for [▹{}]). No statement is changed.

  ** Proof routes that differ from base (statements do not)

  - Reduction facts that base proves under [wf Σ] are used under [ClosedBodies Σ] (from [wfE Σ] by
    [wfE_ClosedBodies]): [invert_red_prod_cb], [invert_red_mkApps_tInd_cb], [red_red_ctx_inv'_cb],
    [closed_red_red_subst0_cb], and [PCUICPrincipalityEta.closed_red_confluence_cb] (from
    [red_confluence_cb]) and [PCUICPrincipalityEta.invert_red_sort_cb] (no premise), written
    qualified ([PCUICPrincipalityEta] is required, not imported: its [principal_typeE] is the twin
    of the other base [principal_type], see "Same names" below).
  - App: base substitutes the argument with the typed [closed_red_subst] and a typed [subslet];
    here [closed_red_untyped_substitution_cb] with the scoping of the argument (from
    [checking_typingE]).
  - Proj: base types the substitution [c :: rev args] with [projection_subslet] and closes the
    projection context with [wf_projection_context]; here [untyped_subslet_projection_contextE] and
    [is_closed_projection_contextE] ([BDFromPCUICEta], class-free), as [BDFromPCUICEta] does.

  ** The forecast block

  The lemmas take the forecast class of [BDToPCUICEta] (T1's [SRForecastCopy18], copy 18b) as a
  section [Context], because they use soundness ([infering_typingE], ...), validity and
  completeness ([typing_inferingE], ...); it is imported, never redefined. This file adds no
  class. [Print Assumptions] in [BDUniqueEtaInstances] shows the class as an argument.

  ** Same names

  Base has two [principal_type] ([PCUICPrincipality.principal_type] and
  [BDUnique.principal_type], different statements); the twin of the second is
  [BDUniqueEta.principal_typeE] (here), the twin of the first [PCUICPrincipalityEta.principal_typeE].
  This file requires [PCUICPrincipalityEta], so both are in its context and in that of every file
  that loads it: every reference to either is written qualified (cross-lane-commitments.md C6). *)

From Stdlib Require Import Bool List Arith Lia.
From MetaRocq.Utils Require Import utils monad_utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICGlobalEnv PCUICAst PCUICAstUtils PCUICTactics
  PCUICInduction PCUICLiftSubst PCUICTyping PCUICEquality PCUICArities PCUICInversion
  PCUICReduction PCUICSubstitution PCUICConversion PCUICCumulativity PCUICGeneration
  PCUICWfUniverses PCUICContextConversion PCUICContextSubst PCUICContexts PCUICSpine
  PCUICWfUniverses PCUICUnivSubst PCUICClosed PCUICInductives PCUICValidity
  PCUICInductiveInversion PCUICConfluence PCUICWellScopedCumulativity PCUICSR
  PCUICOnFreeVars PCUICClosedTyp.
From MetaRocq.PCUIC Require Import BDTyping BDToPCUIC BDFromPCUIC BDUnique.
From MetaRocq.PCUIC Require Import PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
  PCUICTypingEtaNotions PCUICClosedBodies PCUICClosedTypEta PCUICEtaI5
  PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICContextConversionEta
  PCUICWsCumulEtaCtx PCUICContextConversionTypEta PCUICAritiesEta PCUICSpineEta
  PCUICValidityEta PCUICSREta BDTypingEta BDToPCUICEta BDFromPCUICEta.
From MetaRocq.PCUIC Require PCUICPrincipalityEta.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From Equations.Prop Require Import DepElim.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Section BDUniqueEta.

(* FORECAST-ONLY: T1's class ([PCUICSREta], copy 18b); delete it when its row lands. *)
Context {F18 : SRForecastCopy18}.

Section BDUnique.

Context `{cf : checker_flags}.
Context (Σ : global_env_ext).
Context (wfΣ : wfE Σ).

Let Pinfer Γ t T :=
  wf_localE Σ Γ ->
  forall T', Σ ;;; Γ |-E t ▹ T' ->
  ∑ T'', Σ ;;; Γ ⊢ T ⇝ T'' × Σ ;;; Γ ⊢ T' ⇝ T''.

Let Psort Γ t u :=
  wf_localE Σ Γ ->
  forall u', Σ ;;; Γ |-E t ▹□ u' ->
  u = u'.

Let Pprod Γ t (na : aname) A B :=
  wf_localE Σ Γ ->
  forall na' A' B', Σ ;;; Γ |-E t ▹Π (na',A',B') ->
  ∑ A'' B'',
  [× na = na', Σ ;;; Γ ⊢ A ⇝ A'', Σ ;;; Γ ⊢ A' ⇝ A'',
      Σ ;;; Γ,, vass na A ⊢ B ⇝ B'' & Σ ;;; Γ,, vass na A' ⊢ B' ⇝ B''].

Let Pind Γ ind t u args :=
  wf_localE Σ Γ ->
  forall ind' u' args', Σ ;;; Γ |-E t ▹{ind'} (u',args') ->
  ∑ args'',
  [× ind = ind',
      u = u',
      red_terms Σ Γ args args'' &
      red_terms Σ Γ args' args''].

Let Pcheck (Γ : context) (t T : term) := True.

Let Pj (Γ : context) (j : judgment) := lift_sorting (Pcheck Γ) (Psort Γ) j.

Let PΓ (Γ : context) := True.

Let PΓ_rel (Γ Γ' : context) := True.

(** Base [bidirectional_unique] ([BDUnique.v:61]). *)
Theorem bidirectional_uniqueE : env_prop_bdE Σ Pcheck Pinfer Psort Pprod Pind Pj PΓ PΓ_rel.
Proof.

  apply bidir_ind_envE.

  all: intros ; red ; auto.
  { apply lift_sorting_impl with (1 := X) => ?? [] //. }
  1-9,11-13: intros ? T' ty_T' ; inversion_clear ty_T'.
  14-17: intros.

  - rewrite H in H0.
    inversion H0. subst. clear H0.
    eexists ; split.
    all: eapply closed_red_refl.
    2,4: eapply PCUICInversion.nth_error_closed_context.
    all: fvs.

  - eexists ; split.
    all: eapply closed_red_refl ; fvs.

  - apply unlift_TypUniv in X0, X3.
    apply X0 in X3 => //.
    apply H in X4.
    2:{ constructor ; auto. now eapply lift_sorting_forget_univ, lift_sorting_lift_typingE. }
    subst.
    eexists ; split.
    all: eapply closed_red_refl ; fvs.

  - apply X2 in X5 as [bty' []].
    2:{ constructor ; auto. now apply lift_sorting_lift_typingE. }
    exists (tProd na t bty') ; split.
    all: now eapply closed_red_prod_codom.

  - apply lift_sorting_lift_typingE in X, X4; tas.
    apply lift_typing_is_open_termE in X4 as [X4_1 X4_2]; tas; cbn in *.
    apply X2 in X5 as [A' []].
    2: now constructor.
    apply wf_local_closed_contextE in X3.
    exists (tLetIn na b B A').
    split.
    all: eapply closed_red_letin ; tea.
    all: now apply closed_red_refl.

  - unshelve epose proof (X0 _ _ _ _ X3) as (A''&B''&[]) ; tea.
    subst.
    exists (B''{0 := u}).
    split.
    all: eapply (closed_red_untyped_substitution_cb (Δ := [_]) (Γ' := [])) ; tea.
    all: try solve [repeat constructor].
    all: cbn; rewrite andb_true_r.
    all: eapply subject_is_open_termE, checking_typingE ; tea.
    all: eapply isTypeRelE_isTypeE.
    all: now eapply isType_tProdE, validityE, infering_prod_typingE.

  - pose proof (declared_constant_to_gen (wfΣ := wfΣ) isdecl).
    pose proof (declared_constant_to_gen (wfΣ := wfΣ) H).
    replace decl0 with decl by (eapply declared_constant_inj ; eassumption).
    eexists ; split.
    all: eapply closed_red_refl.
    1,3: fvs.
    all: rewrite on_free_vars_subst_instance.
    all: now eapply closed_on_free_vars, declared_constant_closed_typeE.

  - pose proof (declared_inductive_to_gen (wfΣ := wfΣ) isdecl).
    pose proof (declared_inductive_to_gen (wfΣ := wfΣ) H).
    replace idecl0 with idecl by (eapply declared_inductive_inj ; eassumption).
    eexists ; split.
    all: eapply closed_red_refl.
    1,3: fvs.
    all: rewrite on_free_vars_subst_instance.
    all: now eapply closed_on_free_vars, declared_inductive_closed_typeE.

  - pose proof (declared_constructor_to_gen (wfΣ := wfΣ) isdecl).
    pose proof (declared_constructor_to_gen (wfΣ := wfΣ) H).
    replace cdecl0 with cdecl by (eapply declared_constructor_inj ; eassumption).
    replace mdecl0 with mdecl by (eapply declared_constructor_inj ; eassumption).
    eexists ; split.
    all: eapply closed_red_refl.
    1,3: fvs.
    all: now eapply closed_on_free_vars, declared_constructor_closed_typeE.

  - pose proof (declared_projection_to_gen (wfΣ := wfΣ) H1).
    apply (declared_projection_to_gen (wfΣ := wfΣ)) in H.
    eapply declared_projection_inj in H as (?&?&?&?); tea.
    subst.
    move: (X2) => tyc'.
    eapply X0 in X2 as [args'' []] ; tea.
    eapply infering_ind_typingE in X ; tea.
    eapply infering_ind_typingE in tyc' ; tea.
    subst.
    exists (subst0 (c :: List.rev args'') (proj_type pdecl)@[u0]).
    split.
    + eapply (closed_red_red_subst0_cb (Δ := projection_context (proj_ind p) mdecl idecl u0)) ; tea.
      * eapply is_closed_context_weaken.
        1: fvs.
        now eapply is_closed_projection_contextE.
      * constructor.
        2: now apply All2_rev.
        apply closed_red_refl.
        1: fvs.
        now eapply subject_is_open_termE.
      * now eapply untyped_subslet_projection_contextE.
      * rewrite on_free_vars_subst_instance.
        move: (H1) => H.
        eapply declared_projection_closedE in H; eauto.
        rewrite (declared_minductive_ind_nparsE (proj1 (proj1 (proj1 H1)))) in H.
        cbn in H. len.
        rewrite closedn_on_free_vars //.
        eapply closed_upwards; tea. cbn. lia.
    + eapply (closed_red_red_subst0_cb (Δ := projection_context (proj_ind p) mdecl idecl u0)) ; tea.
      * eapply is_closed_context_weaken.
        1: fvs.
        now eapply is_closed_projection_contextE.
      * constructor.
        2: now apply All2_rev.
        apply closed_red_refl.
        1: fvs.
        now eapply subject_is_open_termE.
      * now eapply untyped_subslet_projection_contextE.
      * rewrite on_free_vars_subst_instance.
        move: (H1) => H.
        eapply declared_projection_closedE in H; eauto.
        rewrite (declared_minductive_ind_nparsE (proj1 (proj1 (proj1 H1)))) in H.
        cbn in H. len.
        rewrite closedn_on_free_vars //.
        eapply closed_upwards; tea. cbn. lia.

  - rewrite H2 in H0 ; injection H0 as ->.
    eapply nth_error_all in X as (?&[]); tea.
    eexists ; split.
    all: eapply closed_red_refl.
    1,3:fvs.
    all: now eapply subject_is_open_termE, infering_sort_typingE.

  - rewrite H2 in H0 ; injection H0 as ->.
    eapply nth_error_all in X as (?&[]); tea.
    eexists ; split.
    all: eapply closed_red_refl.
    1,3:fvs.
    all: now eapply subject_is_open_termE, infering_sort_typingE.

  - intros ? T' ty_T'.
    inversion ty_T' ; subst.
    unshelve eapply declared_inductive_to_gen in H14; cycle -2; eauto.
    unshelve eapply declared_inductive_to_gen in H; cycle -2; eauto.
    move: (H) => /declared_inductive_inj /(_ H14) [? ?].
    subst.
    assert (op' : is_open_term Γ (mkApps ptm0 (skipn (ci_npar ci) args0 ++ [c]))).
      by now eapply type_is_open_termE, infering_typingE.
    move: op'.
    rewrite on_free_vars_mkApps => /andP [optm' oargs'].
    eapply X0 in X9 as [args'' []] ; tea.
    subst.
    eexists (mkApps ptm ((skipn (ci_npar ci) args'') ++ [c])).
    split.
    + eapply into_closed_red.
      * eapply red_mkApps.
        1: reflexivity.
        eapply All2_app.
        2: now constructor.
        eapply All2_skipn, All2_impl ; tea.
        intros ? ? r.
        now apply r.
      * fvs.
      * eapply type_is_open_termE, infering_typingE ; tea.
        econstructor; eauto. apply declared_inductive_from_gen; eauto.
    + eapply into_closed_red.
      * eapply red_mkApps.
        1: reflexivity.
        eapply All2_app.
        2: now constructor.
        eapply All2_skipn, All2_impl ; tea.
        intros ? ? r.
        now apply r.
      * fvs.
      * now eapply type_is_open_termE, infering_typingE.

  - depelim X; depelim X0.
    * inversion X2 ; subst. rewrite H3 in H; noconf H. eexists. split; eapply closed_red_refl; fvs.
    * inversion X2 ; subst. rewrite H3 in H; noconf H. eexists. split; eapply closed_red_refl; fvs.
    * inversion X2 ; subst. rewrite H3 in H; noconf H. eexists. split; eapply closed_red_refl; fvs.
    * inversion X2 ; subst. rewrite H3 in H; noconf H. eexists. split; eapply closed_red_refl; fvs.
      all:simp prim_type; cbn. cbn in hty.
      all:eapply type_is_open_termE, checking_typingE; tea.
      all:eapply has_sort_isTypeE; eapply checking_typingE; tea.
      all:eapply has_sort_isTypeE; econstructor; tea.

  - inversion X3 ; subst.
    eapply X0 in X4 as [T'' []]; subst ; tea.
    eapply into_closed_red in X1 ; fvs.
    eapply into_closed_red in X5 ; fvs.
    eapply PCUICPrincipalityEta.closed_red_confluence_cb in X5 as [? [? ru']]; tea.
    eapply PCUICPrincipalityEta.invert_red_sort_cb in ru' ; subst.
    eapply PCUICPrincipalityEta.closed_red_confluence_cb in X1 as [? [ru' ru]].
    2: now etransitivity.
    eapply PCUICPrincipalityEta.invert_red_sort_cb in ru ; subst.
    eapply PCUICPrincipalityEta.invert_red_sort_cb in ru'.
    now congruence.

  - inversion X3 ; subst.
    eapply X0 in X4 as [T'' []]; subst ; tea.
    eapply into_closed_red in X1 ; fvs.
    eapply into_closed_red in X5 ; fvs.
    eapply PCUICPrincipalityEta.closed_red_confluence_cb in X5 as [? [? rA']]; tea.
    eapply invert_red_prod_cb in rA' as (?&B0&[]); subst.
    eapply PCUICPrincipalityEta.closed_red_confluence_cb in X1 as [? [rA' rA]].
    2: now etransitivity.
    eapply invert_red_prod_cb in rA as (?&?&[]); subst.
    eapply invert_red_prod_cb in rA' as (A''&B''&[]) ; subst.
    injection e as -> -> ->.
    exists A'', B'' ; split ; tea.
    1: reflexivity.
    1: now etransitivity.
    etransitivity ; tea.
    eapply red_red_ctx_inv'_cb ; tea.
    constructor.
    1: eapply closed_red_ctx_refl ; fvs.
    now constructor.

  - inversion X3 ; subst.
    eapply X0 in X4 as [T'' []]; subst ; tea.
    eapply into_closed_red in X1 ; fvs.
    eapply into_closed_red in X5 ; fvs.
    eapply PCUICPrincipalityEta.closed_red_confluence_cb in X5 as [? [? rind']]; tea.
    eapply invert_red_mkApps_tInd_cb in rind' as [? []]; subst.
    eapply PCUICPrincipalityEta.closed_red_confluence_cb in X1 as [? [rind' rind]].
    2: now etransitivity.
    eapply invert_red_mkApps_tInd_cb in rind as [? []]; subst.
    eapply invert_red_mkApps_tInd_cb in rind' as [args'' [e ]]; subst.
    eapply mkApps_notApp_inj in e as [e ->].
    2-3: easy.
    injection e as <- <-.
    exists args'' ; split ; auto.
    eapply All2_trans ; tea.
    eapply closed_red_trans.
Qed.

End BDUnique.

(** Base [infering_unique] ([BDUnique.v:311]). *)
Theorem infering_uniqueE `{checker_flags} {Σ} (wfΣ : wfE Σ) {Γ} (wfΓ : wf_localE Σ Γ) {t T T'} :
  Σ ;;; Γ |-E t ▹ T -> Σ ;;; Γ |-E t ▹ T' ->
  ∑ T'', Σ ;;; Γ ⊢ T ⇝ T'' × Σ ;;; Γ ⊢ T' ⇝ T''.
Proof.
  intros ty ty'.
  now eapply bidirectional_uniqueE in ty'.
Qed.

(** Base [infering_unique'] ([BDUnique.v:319]). *)
Theorem infering_unique'E `{checker_flags} {Σ} (wfΣ : wfE Σ) {Γ} (wfΓ : wf_localE Σ Γ) {t T T'} :
  Σ ;;; Γ |-E t ▹ T -> Σ ;;; Γ |-E t ▹ T' ->
  Σ ;;; Γ ⊢E T = T'.
Proof.
  intros ty ty'.
  eapply bidirectional_uniqueE in ty as [? []]; tea.
  etransitivity.
  2: symmetry.
  all: now eapply red_ws_cumul_pbE.
Qed.

(** Base [infering_checking] ([BDUnique.v:330]). *)
Theorem infering_checkingE `{checker_flags} {Σ} (wfΣ : wfE Σ) {Γ} (wfΓ : wf_localE Σ Γ) {t T T'} :
  is_open_term Γ T' -> Σ ;;; Γ |-E t ▹ T -> Σ ;;; Γ |-E t ◃ T' -> Σ ;;; Γ ⊢E T ≤ T'.
Proof.
  intros ? ty ty'.
  depelim ty'.
  eapply infering_unique'E in ty ; tea.
  etransitivity ; last first.
  - apply into_ws_cumul_pbE ; tea.
    1: fvs.
    now eapply type_is_open_termE, infering_typingE.
  - now eapply ws_cumul_pbE_eq_le.
Qed.

(** Base [infering_sort_sort] ([BDUnique.v:343]). *)
Theorem infering_sort_sortE `{checker_flags} {Σ} (wfΣ : wfE Σ) {Γ} (wfΓ : wf_localE Σ Γ) {t u u'} :
  Σ ;;; Γ |-E t ▹□ u -> Σ ;;; Γ |-E t ▹□ u' -> u = u'.
Proof.
  intros ty ty'.
  now eapply bidirectional_uniqueE in ty'.
Qed.

(** Base [infering_sort_infering] ([BDUnique.v:350]). *)
Theorem infering_sort_inferingE `{checker_flags} {Σ} (wfΣ : wfE Σ)
  {Γ} {wfΓ : wf_localE Σ Γ} {t u T} :
  Σ ;;; Γ |-E t ▹□ u -> Σ ;;; Γ |-E t ▹ T ->
  Σ ;;; Γ ⊢ T ⇝ tSort u.
Proof.
  intros ty ty'.
  depelim ty.
  eapply into_closed_red in r.
  2: fvs.
  2: now eapply type_is_open_termE, infering_typingE.
  eapply bidirectional_uniqueE in i as [T'' []]; tea.
  eapply PCUICPrincipalityEta.closed_red_confluence_cb in r as [? [? ru]]; tea.
  eapply PCUICPrincipalityEta.invert_red_sort_cb in ru ; subst.
  now etransitivity.
Qed.

(** Base [infering_prod_prod] ([BDUnique.v:366]). *)
Theorem infering_prod_prodE `{checker_flags} {Σ} (wfΣ : wfE Σ)
  {Γ} (wfΓ : wf_localE Σ Γ) {t na na' A A' B B'} :
  Σ ;;; Γ |-E t ▹Π (na,A,B) -> Σ ;;; Γ |-E t ▹Π (na',A',B') ->
  ∑ A'' B'',
  [× na = na', Σ ;;; Γ ⊢ A ⇝ A'', Σ ;;; Γ ⊢ A' ⇝ A'',
      Σ ;;; Γ,, vass na A ⊢ B ⇝ B'' & Σ ;;; Γ,, vass na A' ⊢ B' ⇝ B''].
Proof.
  intros ty ty'.
  now eapply bidirectional_uniqueE in ty'.
Qed.

(** Base [infering_prod_prod'] ([BDUnique.v:377]). *)
Theorem infering_prod_prod'E `{checker_flags} {Σ} (wfΣ : wfE Σ)
  {Γ} (wfΓ : wf_localE Σ Γ) {t na na' A A' B B'} :
  Σ ;;; Γ |-E t ▹Π (na,A,B) -> Σ ;;; Γ |-E t ▹Π (na',A',B') ->
  [× na = na', Σ ;;; Γ ⊢E A = A' & Σ ;;; Γ,, vass na A ⊢E B = B'].
Proof.
  intros ty ty'.
  eapply infering_prod_prodE in ty as (A''&B''&[]); tea.
  subst.
  assert (Σ ;;; Γ ⊢E A = A').
  {
    etransitivity.
    2: symmetry.
    all: now eapply red_ws_cumul_pbE.
  }
  split ; auto.
  etransitivity.
  1: now eapply red_ws_cumul_pbE.
  symmetry.
  eapply ws_cumul_pbE_ws_cumul_ctx.
  2: now eapply red_ws_cumul_pbE.
  constructor.
  1: eapply ws_cumul_ctx_pbE_refl ; fvs.
  unfold ws_cumul_declsE.
  constructor; [exact eq_refl|now symmetry].
Qed.

(** Base [infering_prod_infering] ([BDUnique.v:402]). *)
Theorem infering_prod_inferingE `{checker_flags} {Σ} (wfΣ : wfE Σ)
  {Γ} (wfΓ : wf_localE Σ Γ) {t na A B T} :
  Σ ;;; Γ |-E t ▹Π(na,A,B) ->
  Σ ;;; Γ |-E t ▹ T ->
  ∑ A' B', [× Σ ;;; Γ ⊢ T ⇝ tProd na A' B',
    Σ ;;; Γ ⊢ A ⇝ A' &
    Σ ;;; Γ,, vass na A ⊢ B ⇝ B'].
Proof.
  intros ty ty'.
  depelim ty.
  eapply into_closed_red in r.
  2: fvs.
  2: now eapply type_is_open_termE, infering_typingE.
  eapply bidirectional_uniqueE in i as [? []]; tea.
  eapply PCUICPrincipalityEta.closed_red_confluence_cb in r as [? [? rA']]; tea.
  eapply invert_red_prod_cb in rA' as (A'&B'&[]); subst.
  exists A', B' ; split ; tea.
  now etransitivity.
Qed.

(** Base [infering_ind_ind] ([BDUnique.v:422]). *)
Theorem infering_ind_indE `{checker_flags} {Σ} (wfΣ : wfE Σ)
  {Γ} (wfΓ : wf_localE Σ Γ) {t ind ind' u u' args args'} :
  Σ ;;; Γ |-E t ▹{ind} (u,args) -> Σ ;;; Γ |-E t ▹{ind'} (u',args') ->
  ∑ args'',
    [× ind = ind', u = u',
      red_terms Σ Γ args args'' &
      red_terms Σ Γ args' args''].
Proof.
  intros ty ty'.
  now eapply bidirectional_uniqueE in ty'.
Qed.

(** Base [infering_ind_ind'] ([BDUnique.v:434]). *)
Theorem infering_ind_ind'E `{checker_flags} {Σ} (wfΣ : wfE Σ)
  {Γ} (wfΓ : wf_localE Σ Γ) {t ind ind' u u' args args'} :
  Σ ;;; Γ |-E t ▹{ind} (u,args) -> Σ ;;; Γ |-E t ▹{ind'} (u',args') ->
    [× ind = ind', u = u' &
      ws_cumul_pbE_terms Σ Γ args args'].
Proof.
  intros ty ty'.
  eapply bidirectional_uniqueE in ty as [args'' []] ; tea.
  subst.
  split ; auto.
  etransitivity.
  2: symmetry.
  all: now eapply red_terms_ws_cumul_pbE_terms.
Qed.

(** Base [infering_ind_infering] ([BDUnique.v:449]). *)
Theorem infering_ind_inferingE `{checker_flags} {Σ} (wfΣ : wfE Σ)
  {Γ} (wfΓ : wf_localE Σ Γ) {t ind u args T} :
  Σ ;;; Γ |-E t ▹{ind} (u,args) ->
  Σ ;;; Γ |-E t ▹ T ->
  ∑ args',
    Σ ;;; Γ ⊢ T ⇝ mkApps (tInd ind u) args' ×
      red_terms Σ Γ args args'.
Proof.
  intros ty ty'.
  depelim ty.
  eapply into_closed_red in r.
  2: fvs.
  2: now eapply type_is_open_termE, infering_typingE.
  eapply bidirectional_uniqueE in i as [? []]; tea.
  eapply PCUICPrincipalityEta.closed_red_confluence_cb in r as [? [? rind]]; tea.
  eapply invert_red_mkApps_tInd_cb in rind as [args' []]; subst.
  exists args' ; split ; tea.
  now etransitivity.
Qed.

(** Base [principal_type] ([BDUnique.v:469]); base [PCUICPrincipality] has another lemma of this
    name (see the header). *)
Corollary principal_typeE `{checker_flags} {Σ} (wfΣ : wfE Σ) {Γ t T} :
  Σ ;;; Γ |-E t : T ->
  ∑ T',
    (forall T'', Σ ;;; Γ |-E t : T'' -> Σ ;;; Γ ⊢E T' ≤ T'') × Σ ;;; Γ |-E t : T'.
Proof.
  intros ty.
  assert (wf_localE Σ Γ) by (eapply typingE_wf_local; eauto).
  apply typing_inferingE in ty as (S & infS & _); auto.
  exists S.
  split.
  2: by apply infering_typingE.
  intros T' ty.
  eapply typing_inferingE in ty as (S' & infS' & cum'); auto.
  etransitivity ; eauto.
  now eapply ws_cumul_pbE_eq_le, infering_unique'E.
Qed.

(** Base [isTypeRel_unique] ([BDUnique.v:487]). *)
Corollary isTypeRel_uniqueE `{checker_flags} {Σ} (wfΣ : wfE Σ) {Γ T rel rel'} :
  isTypeRelE Σ Γ T rel -> isTypeRelE Σ Γ T rel' -> rel = rel'.
Proof.
  intros (_ & s1 & H1 & _ & <-) (_ & s2 & H2 & _ & <-). cbn in H1, H2.
  apply typingE_wf_local in H1 as wfΓ.
  apply typing_infering_sortE in H1 as (u1 & H1 & Hle), H2 as (u2 & H2 & Hle'); tas.
  apply leq_relevance_eq in Hle as <-, Hle' as <-.
  eapply infering_sort_sortE in H2 as ->; tea.
  reflexivity.
Qed.

End BDUniqueEta.
