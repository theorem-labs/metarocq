(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICTyping PCUICWellScopedCumulativity
  PCUICClosedTyp PCUICTypingEta PCUICWellScopedCumulativityEta.
From MetaRocq.SafeChecker Require PCUICWfEnv PCUICCallByNeed PCUICCallByNeedSoundHookProof
  PCUICCallByNeedEtaSoundHookProof.
From MetaRocq.SafeChecker Require Import PCUICWfEnvEta PCUICCallByNeedEta.

(** * Soundness of the call-by-need fast path over [welltypedE]

  Base [PCUICTypeChecker.convert] (integ-all8 1a92b56c) tries the call-by-need machine ([cbn_conv],
  BET-298) before [isconv_term]; a [true] answer is accepted with the proof
  [PCUICCallByNeedSoundHookProof.convert_cbn_sound], which needs base [welltyped] premises.
  [PCUICTypeCheckerEta.convert] keeps the same branch (over [PCUICCallByNeedEta.cbn_conv], the η
  environment's copy of the same machine), but it holds only [welltypedE] premises, which do not give
  [welltyped] (E typing accepts strictly more).  So the branch needs the statement [cbn_conv_soundE]
  below, a [Prop] class (erased by extraction): the E statement of
  [PCUICCallByNeedSoundHookProof.convert_cbn_sound] over [welltypedE] and [PCUICCallByNeedEta].

  [frac/eta] has no call-by-need fast path (it branched before the machine existed); the ship tree
  (integ-all8 with the η checker) does.  The statement is PROVED: [cbn_conv_soundE_proved] below
  (wip/etak-cbne-2026-10-30), from [PCUICCallByNeedEtaSoundHookProof.convert_cbn_sound], the machine's
  soundness proof re-stated over the copy [PCUICCallByNeedEta] and [wfE].  [PCUICTypeCheckerEta.convert]
  uses that instance directly, so no root of the E checker binds [CbnConvSoundE] (FRAC's ship rule,
  2026-10-30 04:34Z: no open premise at a root). *)

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

(** ** The proved instance

  [PCUICCallByNeedEtaSoundHookProof.convert_cbn_sound] is [cbn_conv_soundE]'s statement, for every
  η environment [X_type]: the η copies [PCUICCallByNeedEtaSound*] of base's machine-proof files,
  with [wf Σ] threaded as [wfE Σ] (from [abstract_env_ext_sq_wf]), base's reduction and
  [ws_cumul_pb] lemmas replaced by their [ClosedBodies]/E twins, and the hook's typed facts read
  over [typingE] (the list: the header of [PCUICCallByNeedEtaSoundHookProof]).  The proof uses no
  subject reduction, no validity and no inversion; its only premises are the obligation's [ht],
  [hu] and [Hcbn]. *)
(* instance: PROVED — the E statement itself, over PCUICCallByNeedEta.cbn_conv and a PCUICWfEnvEta environment; no premise beyond the statement's own. *)
#[global] Instance cbn_conv_soundE_proved {cf : checker_flags} : CbnConvSoundE.
Proof. red. exact (@PCUICCallByNeedEtaSoundHookProof.convert_cbn_sound cf). Qed.

(** ** The base instance

  The statement of [cbn_conv_soundE] at base [welltyped], over a base environment and base
  [cbn_conv] (the same machine), proved from [PCUICCallByNeedSoundHookProof.convert_cbn_sound] and
  the inclusion [ws_cumul_pb_incl_E] (plan I0).  It shows that the statement's shape is consistent
  with base's: the machine's [true] is a conversion, hence an E conversion.  It is not an instance
  of [CbnConvSoundE] itself (base environment, base [cbn_conv]); that is [cbn_conv_soundE_proved]
  above. *)
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
