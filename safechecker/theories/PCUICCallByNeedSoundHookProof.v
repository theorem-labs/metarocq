(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require CanonicalTries.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping
  PCUICOnFreeVars PCUICClosed PCUICClosedTyp.
From MetaRocq.SafeChecker Require Import PCUICWfEnv PCUICCallByNeed PCUICCallByNeedSound
  PCUICCallByNeedSoundGC PCUICCallByNeedSoundCtx PCUICCallByNeedSoundMemo
  PCUICCallByNeedSoundHook PCUICCallByNeedSoundEval PCUICCallByNeedSoundLevel
  PCUICCallByNeedSoundReadBack PCUICCallByNeedSoundConv PCUICCallByNeedSoundHookFrame.
From MetaRocq.PCUIC Require Import PCUICWellScopedCumulativity.

(** * The call-by-need fast path is sound at the hook

  [PCUICTypeChecker.convert] answers "convertible" when [cbn_conv X_type X le Γ t u] is
  [true]. This file proves that answer sound: [cbn_conv_sound] gives
  [∥ Σ ;;; Γ ⊢ t ≤[le] u ∥] from [wf Σ], [abstract_env_ext_rel X Σ] and the
  well-typedness of [t] and [u] in [Γ], and [convert_cbn_sound] restates it in exactly the
  shape of [convert]'s obligation.

  The proof follows [cbn_run]'s first call. [cbn_run_eq] exposes it: [cbn_conv_term] at fuel
  [cbn_depth] and level [#|Γ|] on the two root codes [cbn_run_c1], [cbn_run_c2], in the start state
  [cbn_run_s2], with no roots. [cbn_run_gok_frame] gives the start state's [cbn_gok] (at
  [Δ = []], level [#|Γ|]), the two codes in the ghost's table and their readings [t] and
  [u]; with the empty heap ([cbn_run_s2_heap]) this is [cbn_minv] at [L = Q = #|Γ|]
  ([cbn_minv_start]). [cbn_spec_term] at [cbn_depth] then turns the answer [true] into
  [cbn_lift_conv L L le t u]. With [Q - L = 0] the lift is the identity, [t] and [u] are scoped at
  [#|Γ|] ([subject_closed]), and [Δ = []] gives the conversion in [Γ] itself.

  The comparison theorem [forall d, cbn_spec_all d] is
  [PCUICCallByNeedSoundConv.cbn_spec_all_holds]. Its read-back premise [cbn_rb_sound] is
  [PCUICCallByNeedSoundReadBack.cbn_rb_sound_holds]. Every other premise of [cbn_spec_term]'s call
  is discharged here from the obligation's own context, so [convert_cbn_sound] has no hypothesis
  beyond the obligation's. *)

Section HookProof.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).

  (** [cbn_conv] unfolded to [cbn_run]. Do not [unfold cbn_conv, cbn_conv_answer in hc] and
    then [rewrite cbn_run_eq in hc]. The tactics succeed at once, but at [Qed] the kernel
    checks [hc : cbn_conv ... = true] against the rewrite's motive applied to
    [cbn_run ...], evaluates the machine at [cbn_depth] on the way, and runs out of memory
    (more than 8 GB). Rewriting with this [eq_refl] lemma first makes each rewrite's motive
    syntactically the hypothesis, and [Qed] is instant. *)
  Lemma cbn_conv_unfold (le : conv_pb) (Γ : context) (t u : term) :
    cbn_conv X_type X le Γ t u
    = match cbn_run X_type X Γ #|Γ| le t u with CbnYes => true | _ => false end.
  Proof. reflexivity. Qed.

  (** [cbn_lift_conv] at [L = Q = #|Γ|], read at [Δ = []], for two terms scoped in [Γ]. *)
  Lemma cbn_lift_conv_hook (Σ : global_env_ext) (Γ : context) (le : conv_pb) (t u : term) :
    is_closed_context Γ -> closedn #|Γ| t -> closedn #|Γ| u ->
    cbn_lift_conv Γ #|Γ| Σ #|Γ| #|Γ| le t u -> ∥ Σ ;;; Γ ⊢ t ≤[le] u ∥.
  Proof.
    intros hΓ hct hcu hq.
    assert (e : forall v : term, v = lift0 (#|Γ| - #|Γ|) v)
      by (intros v; rewrite Nat.sub_diag, lift0_id; reflexivity).
    exact (hq t u (e t) (e u) (closedn_on_free_vars hct) (closedn_on_free_vars hcu)
             [] ltac:(cbn; lia) hΓ).
  Qed.

  (** The fast path's [true] is a conversion. *)
  Lemma cbn_conv_sound (Σ : global_env_ext) (Γ : context) (le : conv_pb) (t u : term) :
    wf Σ -> abstract_env_ext_rel X Σ -> welltyped Σ Γ t -> welltyped Σ Γ u ->
    cbn_conv X_type X le Γ t u = true -> ∥ Σ ;;; Γ ⊢ t ≤[le] u ∥.
  Proof.
    intros wfΣ hΣ hwt hwu hc.
    pose proof hwt as [A htA]. pose proof hwu as [B huB].
    destruct (cbn_run_gok_frame X_type X Σ Γ t u wfΣ hwt hwu)
      as (_ & _ & hcio & hhyg & hok & hs1 & hc1 & hs2 & hc2).
    assert (hΓ : is_closed_context Γ)
      by exact (wf_local_closed_context (wfΣ := wfΣ) (typing_wf_local htA)).
    rewrite cbn_conv_unfold, cbn_run_eq in hc.
    destruct (cbn_conv_term X_type X Γ #|Γ| cbn_depth #|Γ| le cbn_env_empty (cbn_run_c1 X_type X t)
                cbn_env_empty (cbn_run_c2 X_type X t u) [] (cbn_run_s2 X_type X t u))
      as [[[b rs'] s']|w] eqn:Ec; [|discriminate hc].
    destruct b; [|discriminate hc].
    destruct (cbn_spec_all_holds X_type X Γ #|Γ| Σ wfΣ hΣ eq_refl hΓ hhyg hcio
                (cbn_rb_sound_holds X_type X Γ #|Γ| Σ wfΣ hΓ hhyg) cbn_depth)
      as (_ & _ & _ & hT & _).
    destruct (hT #|Γ| #|Γ| xH (cbn_run_ghost X_type X t u) le cbn_env_empty (cbn_run_c1 X_type X t)
                cbn_env_empty (cbn_run_c2 X_type X t u) t u [] (cbn_run_s2 X_type X t u) true rs' s'
                (cbn_r_minv_start X_type X Σ Γ #|Γ| t u eq_refl hok) (Forall_nil _) hs1 hc1 hs2 hc2
                Ec) as [_ hq].
    exact (cbn_lift_conv_hook Σ Γ le t u hΓ (subject_closed htA) (subject_closed huB) (hq eq_refl)).
  Qed.

  (** [cbn_conv_sound] in the shape of [PCUICTypeChecker.convert]'s obligation for the
    branch [@exist true Hcbn]: the premises are exactly that obligation's [ht], [hu] and
    [Hcbn], and [wf Σ] comes from [abstract_env_ext_sq_wf]. *)
  Lemma convert_cbn_sound (le : conv_pb) (Γ : context) (t u : term)
      (ht : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ t)
      (hu : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ u) :
    true = cbn_conv X_type X le Γ t u ->
    forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ ⊢ t ≤[le] u ∥.
  Proof.
    intros Hcbn Σ wfΣ.
    destruct (abstract_env_ext_sq_wf X_type X Σ wfΣ) as [cbn_hwf].
    exact (cbn_conv_sound Σ Γ le t u cbn_hwf wfΣ (ht Σ wfΣ) (hu Σ wfΣ) (eq_sym Hcbn)).
  Qed.

End HookProof.
