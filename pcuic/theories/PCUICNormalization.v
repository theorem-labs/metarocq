(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICTyping PCUICEquality PCUICAst PCUICAstUtils
  PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICGeneration PCUICArities
  PCUICWcbvEval PCUICSR PCUICInversion
  PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
  PCUICElimination PCUICSigmaCalculus PCUICContextConversion
  PCUICUnivSubst PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICCumulativity PCUICConfluence
  PCUICInduction PCUICLiftSubst PCUICContexts PCUICSpine
  PCUICConversion PCUICValidity PCUICInductives PCUICConversion
  PCUICInductiveInversion PCUICNormal PCUICSafeLemmata
  PCUICParallelReductionConfluence
  PCUICWcbvEval PCUICClosed PCUICClosedTyp
  PCUICReduction PCUICCSubst PCUICOnFreeVars PCUICWellScopedCumulativity
  PCUICWcbvEval PCUICClassification PCUICProgress PCUICSN.

From Equations Require Import Equations.

From MetaRocq.PCUIC Require Import PCUICSN.

Lemma wh_normalization {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationIn Σ} {t} : wf Σ -> axiom_free Σ ->
{A & Σ ;;; [] |- t : A}  -> { v & whnf RedFlags.default Σ [] v * red Σ [] t v}.
Proof.
intros Hwf Hax [A HA].
assert (welltyped Σ [] t) as Hwt. { econstructor; eauto. }
eapply PCUICSN.normalization_in in Hwt as HSN; eauto. clear Hwt.
induction HSN as [t H IH].
destruct (@red1_progress _ Σ Hwf Hax t A HA) as [[t' Ht'] | Hwnf].
- edestruct IH as [v Hv].
  { econstructor. eauto. }
  { eapply subject_reduction; eauto. }
  exists v. destruct Hv. split; eauto. eapply red_step; eauto.
- exists t. split; eauto.
Defined.

(** A blocked case has no value, so evaluation reports it instead. *)
Lemma SN_to_WN {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationIn Σ} {A t} : wf Σ -> axiom_free Σ ->
  Acc (cored Σ []) t -> Σ ;;; [] |- t : A ->
  { v & eval Σ t v} + reduces_to_wcbv_stuck Σ t.
Proof.
  intros Hwf Hax HSN HA.
  induction HSN as [t H IH].
  edestruct progress_env_prop as [_ [_ [[[t' Ht'] | Hval] | Hstuck]]]; eauto.
  - eapply wcbv_red1_red1 in Ht' as Hred. 2:{ change 0 with (#|@nil context_decl|). eapply subject_closed. eauto. }
    edestruct IH as [[v Hv] | [w [hred hstuck]]].
    { econstructor. eauto. }
    { eapply subject_reduction; eauto. }
    + left. exists v. eapply wcbv_red1_eval; eauto.
      now eapply subject_closed in HA.
    + right. exists w. split; auto. eapply red_step; eauto.
  - left. exists t. eapply value_final; eauto.
  - right. exists t. split; eauto.
Qed.

Lemma wcbv_normalization {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationIn Σ} {A t} : wf Σ -> axiom_free Σ ->
  Σ ;;; [] |- t : A -> { v & eval Σ t v} + reduces_to_wcbv_stuck Σ t.
Proof.
  intros Hwf Hax HA.
  assert (welltyped Σ [] t) as Hwt. { econstructor; eauto. }
  eapply PCUICSN.normalization_in in Hwt as HSN; eauto. clear Hwt.
  eapply SN_to_WN; eauto.
Qed.

From MetaRocq.PCUIC Require Import PCUICFirstorder.

Lemma firstorder_value_irred {cf:checker_flags} Σ t t' :
  firstorder_value Σ [] t ->
  PCUICReduction.red1 Σ [] t t' -> False.
Proof.
  intros H.
  revert t'. pattern t. revert t H.
  eapply firstorder_value_inds.
  intros i n ui u args pandi Hty Hargs IH Hprop t' Hred.
  eapply red1_mkApps_tConstruct_inv in Hred as (x & -> & Hone).
  solve_all.
  clear - IH Hone. induction IH as [ | ? ? []] in x, Hone |- *.
  - invs Hone.
  - invs Hone; eauto.
Qed.

Definition ws_empty f : ws_context f.
Proof.
  unshelve econstructor.
  exact nil.
  reflexivity.
Defined.

Lemma irred_equal Σ Γ t t' :
  Σ ;;; Γ ⊢ t ⇝ t' ->
  (forall v', PCUICReduction.red1 Σ Γ t v' -> False) ->
  t = t'.
Proof.
  intros Hred Hirred. destruct Hred.
  clear clrel_ctx clrel_src.
  induction clrel_rel.
  - edestruct Hirred; eauto.
  - reflexivity.
  - assert (x = y) as <- by eauto. eauto.
Qed.

(** Under (A') a well-typed term need not have a value, so the caller supplies one: the
    lemma turns head reduction to an irreducible term into the machine's evaluation. *)
Lemma ws_wcbv_standardization {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationIn Σ} {T} {t v : ws_term (fun _ => false)} : wf Σ -> axiom_free Σ ->
  Σ ;;; [] |- t : T ->
  (∑ v0, eval Σ t v0) ->
  closed_red Σ [] t v ->
  ¬ { t' & Σ ;;; [] |- v ⇝ t'} ->
  {v' & eval Σ t v' * (Σ ;;; [] ⊢ v' ⇝ v)}.
Proof.
  intros Hwf Hax Hty [v' Hv'] Hred Hirred.
  assert (Σ;;; [] |- t ⇝* v') as Hred' by now eapply wcbveval_red.
  eapply closed_red_confluence in Hred as Hred_. destruct Hred_ as (v'' & H1 & H2).
  2:{ econstructor; eauto. eapply subject_is_open_term. eauto. }
  destruct v as [v Hv].
  assert (v = v'') as <- by (eapply irred_equal; eauto).
  exists v'; split; eauto.
Qed.

Lemma ws_wcbv_standardization_fst {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationIn Σ} {i u args mind} {t v : ws_term (fun _ => false)} : wf Σ -> axiom_free Σ ->
  Σ ;;; [] |- t : mkApps (tInd i u) args ->
  (∑ v0, eval Σ t v0) ->
  lookup_env Σ (i.(inductive_mind)) = Some (InductiveDecl mind) ->
  @firstorder_ind Σ (firstorder_env Σ) i ->
  closed_red Σ [] t v ->
  ¬ { t' & Σ ;;; [] |- v ⇝ t'} ->
  eval Σ t v.
Proof.
  intros Hwf Hax Hty hev Hdecl Hfo Hred Hirred.
  destruct (ws_wcbv_standardization Hwf Hax Hty hev Hred Hirred) as [v' [H H']].
  assert (firstorder_value Σ [] v'). {
    eapply firstorder_value_spec; eauto.
    eapply subject_reduction_eval; eauto.
    eapply eval_to_value. eauto.
  }
  enough (v' = v) as -> by eauto.
  eapply irred_equal. eauto.
  intros. eapply firstorder_value_irred; eauto.
  Unshelve.
Qed.

Lemma wcbv_standardization {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationIn Σ} {T t v : term} : wf Σ -> axiom_free Σ ->
  Σ ;;; [] |- t : T ->
  (∑ v0, eval Σ t v0) ->
  Σ ;;; [] |- t ⇝ v ->
  ¬ { t' & Σ ;;; [] |- v ⇝ t'} ->
  {v' & eval Σ t v' * (Σ ;;; [] ⊢ v' ⇝ v)}.
Proof.
  intros Hwf Hax Hty hev Hred Hirred.
  unshelve eapply @ws_wcbv_standardization with (T := T) (t := (exist t _)) (v := (exist v _)).
  all: sq; eauto; cbn.
  1-2: shelve.
  econstructor; eauto.
  eapply subject_is_open_term. eauto.
  Unshelve.
  all: rewrite -closed_on_free_vars_none.
  - now eapply subject_closed in Hty.
  - eapply @subject_closed with (Γ := []); eauto.
    eapply subject_reduction; eauto.
Qed.

Lemma wcbv_standardization_fst {cf:checker_flags} {no:normalizing_flags} {Σ} {normalization:NormalizationIn Σ} {i u args mind} {t v : term} : wf Σ -> axiom_free Σ ->
  Σ ;;; [] |- t : mkApps (tInd i u) args ->
  (∑ v0, eval Σ t v0) ->
  lookup_env Σ (i.(inductive_mind)) = Some (InductiveDecl mind) ->
  @firstorder_ind Σ (firstorder_env Σ) i ->
  red Σ [] t v ->
  ¬ { t' & Σ ;;; [] |- v ⇝ t'} ->
  eval Σ t v.
Proof.
  intros Hwf Hax Hty hev Hdecl Hfo Hred Hirred.
  unshelve eapply @ws_wcbv_standardization_fst with (t := (exist t _)) (v := (exist v _)).
  all: sq; eauto; cbn.
  1-2: shelve.
  econstructor; eauto.
  eapply subject_is_open_term. eauto.
  Unshelve.
  all: rewrite -closed_on_free_vars_none.
  - now eapply subject_closed in Hty.
  - eapply @subject_closed with (Γ := []); eauto.
    eapply subject_reduction; eauto.
Qed.
