(* Distributed under the terms of the MIT license. *)

(** * Consistency over [typingE] (row T9): the E copy of [PCUICConsistency]

  The E twin of base [pcuic_consistent] ([PCUICConsistency.v:40]): [typing] → [typingE],
  [wf_ext] → [wf_extE], [NormalizationIn] → [NormalizationInE] ([PCUICSNEta]). Nothing else
  changes; the name takes the suffix [E]. Base's [False_oib] and [False_mib] mention no
  relation and are used from base ([PCUICConsistency] is imported).

  Proof route: base's, with [pcuic_canonicityE] ([PCUICCanonicityEta]),
  [PCUICValidityEta.inversion_mkAppsE] (written qualified, as base writes
  [PCUICValidity.inversion_mkApps]: [PCUICProgressEta] declares a second [inversion_mkAppsE]),
  [inversion_ConstructE] ([PCUICInversionEta]), [Construct_Ind_ind_eqE] (copy 18b,
  [PCUICInductiveInversionEtaB], written qualified) and [typing_cofix_coindE] ([PCUICClassificationEta]). Base
  destructs [on_declared_constructor d] (:59-62) and clears every component it produces at :64
  ([clear -Hdecl d wfΣ]); the E proof does not take it.

  ** Premises

  - [NormalizationInE Σ] is base's [NormalizationIn Σ] premise over [welltypedE]: a PREMISE,
    as in base, not a forecast. Nothing proves it (strong normalization; [PCUICSNEta]'s header).
  - No forecast class. [PCUICCanonicityEta]'s [CanonForecastCopy20] (base [wh_normalization],
    copy 20) was a section class here until copy 20 (bfe54de2) and the class was
    deleted; T1's [SRForecastCopy18] was a second one until copy 18b landed (frac/eta 3e6b422d)
    and was deleted. This file adds no class.
    Instances: [PCUICConsistencyEtaInstances].

  ** BET-339 (integ-all8 [1a92b56c]; F0 forecast [wip/eta-meta-f0-land45-2026-10-30])

  Base integ-all8 gives [pcuic_consistent] the premise [no_closed_stuck_cofix_case_at Σ
  False_pcuic] (base [PCUICConsistency.v:52]): canonicity may now return a case blocked on a
  cofixpoint ([pcuic_canonicity]'s new disjunct), and that case is the one the proof cannot
  close. This file copies, only the relation renamed: the definition
  [no_closed_stuck_cofix_case_atE] (over [typingE]), the inversions it rests on
  ([typing_tApp_invE], [typing_tCase_scrutE], [typing_tProj_argE], [typing_tCoFix_cofiniteE],
  [typing_mkApps_argE], [typing_mkApps_headE], [typing_stuck_cofix_case_cofiniteE]), its proof in
  every environment without a coinductive block ([no_closed_stuck_cofix_case_at_no_cofiniteE]),
  and base's concrete instance ([no_closed_stuck_cofix_case_at_Σ_FalseE], at base's [Σ_False],
  used from base: it mentions no relation). [pcuic_consistentE] takes the premise. *)

From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICTyping PCUICEquality PCUICAst PCUICAstUtils
  PCUICReduction PCUICWcbvEval PCUICNormal PCUICSN PCUICViews PCUICClassification PCUICCanonicity
  PCUICConsistency.
From MetaRocq.PCUIC Require Import PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
  PCUICTypingEtaNotions PCUICWellScopedCumulativityEta PCUICSNEta PCUICInversionEta
  PCUICValidityEta PCUICSREta PCUICClassificationEta PCUICCanonicityEta.
From MetaRocq.PCUIC Require PCUICInductiveInversionEtaB.

From Equations Require Import Equations.

(** Base [no_closed_stuck_cofix_case_at] (integ-all8 [:52]), over [typingE]: no closed term of
    the empty type is a case blocked on a cofixpoint. Base's comment ([:40-51]) gives the
    reason it is a hypothesis: Rocq's kernel types such a match and unfolds the cofixpoint
    under it; it is not proved for environments with a coinductive type; it holds in every
    environment without one ([no_closed_stuck_cofix_case_at_no_cofiniteE] below). *)
Definition no_closed_stuck_cofix_case_atE {cf : checker_flags} (Σ : global_env_ext)
    (ind : inductive) :=
  forall t, stuck_cofix_case t -> Σ ;;; [] |-E t : tInd ind [] -> False.

(** Base [typing_tApp_inv] (integ-all8 [:59]). *)
Lemma typing_tApp_invE {cf : checker_flags} {Σ : global_env_ext} {Γ f a T} :
  Σ ;;; Γ |-E tApp f a : T -> (∑ U, Σ ;;; Γ |-E f : U) × (∑ U, Σ ;;; Γ |-E a : U).
Proof.
  intros h; depind h; try solve [eauto]; split; eexists; eassumption.
Qed.

(** Base [typing_tCase_scrut] (integ-all8 [:65]). *)
Lemma typing_tCase_scrutE {cf : checker_flags} {Σ : global_env_ext} {Γ ci p c brs T} :
  Σ ;;; Γ |-E tCase ci p c brs : T -> ∑ U, Σ ;;; Γ |-E c : U.
Proof.
  intros h; depind h; try solve [eauto]; eexists; eassumption.
Qed.

(** Base [typing_tProj_arg] (integ-all8 [:71]). *)
Lemma typing_tProj_argE {cf : checker_flags} {Σ : global_env_ext} {Γ pr c T} :
  Σ ;;; Γ |-E tProj pr c : T -> ∑ U, Σ ;;; Γ |-E c : U.
Proof.
  intros h; depind h; try solve [eauto]; eexists; eassumption.
Qed.

(** Base [typing_tCoFix_cofinite] (integ-all8 [:77]); [wf_cofixpoint] → [wf_cofixpointE]. *)
Lemma typing_tCoFix_cofiniteE {cf : checker_flags} {Σ : global_env_ext} {Γ mfix idx T} :
  Σ ;;; Γ |-E tCoFix mfix idx : T ->
  ∑ mind, check_recursivity_kind (lookup_env Σ) mind CoFinite.
Proof.
  intros h; depind h; try solve [eauto];
  match goal with H : wf_cofixpointE _ _ _ |- _ => destruct H as (mind & _ & _ & hk) end;
  now exists mind.
Qed.

(** Base [typing_mkApps_arg] (integ-all8 [:86]). *)
Lemma typing_mkApps_argE {cf : checker_flags} {Σ : global_env_ext} {Γ f args T n arg} :
  Σ ;;; Γ |-E mkApps f args : T -> nth_error args n = Some arg ->
  ∑ U, Σ ;;; Γ |-E arg : U.
Proof.
  revert T; induction args using rev_ind; intros T; [intros _ hn; now destruct n|].
  rewrite mkApps_app /=. intros h hn.
  destruct (typing_tApp_invE h) as [[U hf] [V hx]].
  destruct (lt_dec n #|args|) as [lt|ge].
  - rewrite nth_error_app_lt // in hn. eauto.
  - rewrite nth_error_app_ge in hn; [lia|].
    destruct (n - #|args|) as [|k]; cbn in hn; [|now destruct k].
    injection hn as <-. now exists V.
Qed.

(** Base [typing_mkApps_head] (integ-all8 [:100]). *)
Lemma typing_mkApps_headE {cf : checker_flags} {Σ : global_env_ext} {Γ f args T} :
  Σ ;;; Γ |-E mkApps f args : T -> ∑ U, Σ ;;; Γ |-E f : U.
Proof.
  revert T; induction args using rev_ind; intros T; [intros h; now exists T|].
  rewrite mkApps_app /=. intros h.
  destruct (typing_tApp_invE h) as [[U hf] _]. eauto.
Qed.

(** Base [typing_stuck_cofix_case_cofinite] (integ-all8 [:108]). *)
Lemma typing_stuck_cofix_case_cofiniteE {cf : checker_flags} {Σ : global_env_ext} {Γ t T} :
  stuck_cofix_case t -> Σ ;;; Γ |-E t : T ->
  ∑ mind, check_recursivity_kind (lookup_env Σ) mind CoFinite.
Proof.
  intros st; induction st in Γ, T |- *; intros h.
  - destruct (typing_tCase_scrutE h) as [U hc].
    destruct (typing_mkApps_headE hc) as [V hcf].
    exact (typing_tCoFix_cofiniteE hcf).
  - destruct (typing_tApp_invE h) as [[U hf] _]. eauto.
  - destruct (typing_tCase_scrutE h) as [U hc]. eauto.
  - destruct (typing_tProj_argE h) as [U hc]. eauto.
  - match goal with hn : nth_error args _ = Some arg |- _ =>
      destruct (typing_mkApps_argE h hn) as [U ha] end. eauto.
Qed.

(** Base [no_closed_stuck_cofix_case_at_no_cofinite] (integ-all8 [:124]): the hypothesis holds
    in every environment without a coinductive block. *)
Lemma no_closed_stuck_cofix_case_at_no_cofiniteE {cf : checker_flags} (Σ : global_env_ext) ind :
  (forall mind, check_recursivity_kind (lookup_env Σ) mind CoFinite = false) ->
  no_closed_stuck_cofix_case_atE Σ ind.
Proof.
  intros nocof t st h.
  destruct (typing_stuck_cofix_case_cofiniteE st h) as [mind hk].
  now rewrite nocof in hk.
Qed.

(** Base [no_closed_stuck_cofix_case_at_Σ_False] (integ-all8 [:141]), at base's [Σ_False]. *)
Lemma no_closed_stuck_cofix_case_at_Σ_FalseE {cf : checker_flags} :
  no_closed_stuck_cofix_case_atE Σ_False (mkInd False_kn 0).
Proof.
  apply no_closed_stuck_cofix_case_at_no_cofiniteE.
  intros mind. unfold check_recursivity_kind, lookup_env, Σ_False; cbn.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

(** Base [pcuic_consistent] (integ-all8 [:149]). *)
Theorem pcuic_consistentE {cf:checker_flags} {nor : normalizing_flags} Σ
  {normalization_in: NormalizationInE Σ} t False_pcuic :
  declared_inductive Σ False_pcuic False_mib False_oib ->
  wf_extE Σ -> axiom_free Σ ->
  no_closed_stuck_cofix_case_atE Σ False_pcuic ->
  Σ ;;; [] |-E t : tInd False_pcuic []  -> False.
Proof.
  intros Hdecl wfΣ axΣ nostuck typ_false.
  have wfΣ' : wfE Σ := wfΣ.1.
  destruct (pcuic_canonicityE Σ t False_pcuic [] []) as [t' [[typ_false' eqtt'] ctor]]; eauto.
  destruct ctor as [ctor|stuck].
  2:{ now eapply nostuck. }
  destruct Hdecl as [Hdecl Hidecl].
  destruct False_pcuic as [kn n]. destruct n; cbn in *; [| now rewrite nth_error_nil in Hidecl].
  rewrite /construct_cofix_discr /head in ctor.
  destruct decompose_app eqn:decomp.
  apply decompose_app_inv in decomp; subst.
  destruct t0; try discriminate ctor.
  - apply (PCUICValidityEta.inversion_mkAppsE (wfΣ := wfΣ')) in typ_false' as H.
    destruct H as (?&typ_ctor&_).
    apply inversion_ConstructE in typ_ctor as (?&?&?&?&?&?&?); auto.
    eapply PCUICInductiveInversionEtaB.Construct_Ind_ind_eqE with (args' := []) in typ_false'; tea.
    destruct typ_false' as (((((->&_)&_)&_)&_)&_).
    clear -Hdecl d wfΣ. destruct wfΣ.
    cbn in *.
    destruct d as ((?&?)&?).
    unshelve eapply declared_minductive_to_gen in Hdecl; eauto.
    unshelve eapply declared_minductive_to_gen in H; eauto.
    red in H, Hdecl. cbn in *. rewrite Hdecl in H; noconf H.
    cbn in H0. noconf H0.
    cbn in H1. rewrite nth_error_nil in H1.
    discriminate.
  - eapply @typing_cofix_coindE with (indargs := []) in typ_false'; eauto.
    unfold check_recursivity_kind in typ_false'. destruct wfΣ.
    unshelve eapply declared_minductive_to_gen in Hdecl; eauto.
    red in Hdecl. rewrite Hdecl in typ_false'.
    cbn in typ_false'. inversion typ_false'.
Qed.
