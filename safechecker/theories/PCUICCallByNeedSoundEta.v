(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICTyping PCUICWellScopedCumulativity
  PCUICClosedTyp PCUICTypingEta PCUICWellScopedCumulativityEta.
From MetaRocq.SafeChecker Require PCUICWfEnv PCUICCallByNeed PCUICCallByNeedSoundHookProof.
From MetaRocq.SafeChecker Require Import PCUICWfEnvEta PCUICCallByNeedEta.

(** * FORECAST-ONLY (fc/etak-forecast1): soundness of the call-by-need fast path over [welltypedE]

  integ-all7's [PCUICTypeChecker.convert] tries the call-by-need machine ([cbn_conv], BET-298)
  before [isconv_term]; a [true] answer is accepted with the proof
  [PCUICCallByNeedSoundHookProof.convert_cbn_sound], which needs base [welltyped] premises.
  [PCUICTypeCheckerEta.convert] keeps the same branch (over [PCUICCallByNeedEta.cbn_conv], the η
  environment's copy of the same machine), but it holds only [welltypedE] premises, which do not give
  [welltyped] (E typing accepts strictly more).  So the branch's proof is the named hypothesis
  [cbn_conv_soundE] below, a [Prop] class (erased by extraction), carried as an implicit premise of
  the E checker's sections next to [EtaFacts].

  Forecast-only: [frac/eta] has no call-by-need fast path (BET-298 is in integ-all7 only).
  Reconciled at the landing of [convert_cbn_soundE], the statement of [cbn_conv_soundE] proved: the
  E statement of [PCUICCallByNeedSoundHookProof.convert_cbn_sound] over [welltypedE]. *)

(** The fast path's [true] is an E conversion, at [welltypedE] premises, in the shape of
    [PCUICCallByNeedSoundHookProof.convert_cbn_sound] (the premises are the obligation's [ht], [hu]
    and [Hcbn]; the conclusion is [ws_cumul_pbE] in place of [ws_cumul_pb]). *)
Class CbnConvSoundE {cf : checker_flags} : Prop :=
  cbn_conv_soundE :
    forall (X_type : abstract_env_impl) (X : X_type.π2.π1) (le : conv_pb) (Γ : context) (t u : term),
      (forall Σ, abstract_env_ext_rel X Σ -> welltypedE Σ Γ t) ->
      (forall Σ, abstract_env_ext_rel X Σ -> welltypedE Σ Γ u) ->
      true = PCUICCallByNeedEta.cbn_conv X_type X le Γ t u ->
      forall Σ, abstract_env_ext_rel X Σ -> ∥ Σ ;;; Γ ⊢E t ≤[le] u ∥.

(** ** The base instance

  The statement of [cbn_conv_soundE] at base [welltyped], over a base environment and base
  [cbn_conv] (the same machine), proved from [PCUICCallByNeedSoundHookProof.convert_cbn_sound] and
  the inclusion [ws_cumul_pb_incl_E] (plan I0).  (1) This base instance shows that the hypothesis's
  shape is consistent and about something real: the machine's [true] is a conversion, hence an E conversion.
  (2) It does NOT discharge the instantiation at [welltypedE] over a [PCUICWfEnvEta] environment: the
  machine's soundness proof reads back through base typing (subject reduction, closedness of typed
  terms), so over [typingE] it needs subject reduction over [typingE] (plan row T1) and the other
  named E facts; [cbn_conv_soundE] remains a hypothesis until [convert_cbn_soundE] lands. *)
(* instance: SHAPE-ONLY — over BASE cbn_conv and base environment, not the E copy PCUICCallByNeedEta.cbn_conv; it shows the hypothesis shape is consistent, it is NOT an instance of cbn_conv_soundE itself. *)
Lemma convert_cbn_sound_base_instance {cf : checker_flags}
    (X_type : PCUICWfEnv.abstract_env_impl) (X : X_type.π2.π1) (le : conv_pb) (Γ : context) (t u : term) :
  (forall Σ, PCUICWfEnv.abstract_env_ext_rel X Σ -> welltyped Σ Γ t) ->
  (forall Σ, PCUICWfEnv.abstract_env_ext_rel X Σ -> welltyped Σ Γ u) ->
  true = PCUICCallByNeed.cbn_conv X_type X le Γ t u ->
  forall Σ, PCUICWfEnv.abstract_env_ext_rel X Σ -> ∥ Σ ;;; Γ ⊢E t ≤[le] u ∥.
Proof.
  intros ht hu Hcbn Σ wfΣ.
  destruct (PCUICWfEnv.abstract_env_ext_sq_wf X_type X Σ wfΣ) as [hwf].
  destruct (PCUICCallByNeedSoundHookProof.convert_cbn_sound X_type X le Γ t u ht hu Hcbn Σ wfΣ) as [h].
  constructor. exact (ws_cumul_pb_incl_E (wfΣ := wf_ClosedBodies Σ (wfΣ := hwf)) h).
Qed.
