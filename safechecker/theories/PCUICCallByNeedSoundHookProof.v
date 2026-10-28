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

  The proof follows [cbn_run]'s first call. [cbn_run_eq] exposes it: [conv_term] at fuel
  [cbn_depth] and level [#|Γ|] on the two root codes [run_c1], [run_c2], in the start state
  [run_s2], with no roots. [cbn_run_gok_frame] gives the start state's [gok] (at
  [Δ = []], level [#|Γ|]), the two codes in the ghost's table and their readings [t] and
  [u]; with the empty heap ([run_s2_heap]) this is [minv] at [L = Q = #|Γ|]
  ([minv_start]). [spec_term] at [cbn_depth] then turns the answer [true] into
  [cq L L le t u]. With [Q - L = 0] the lift is the identity, [t] and [u] are scoped at
  [#|Γ|] ([subject_closed]), and [Δ = []] gives the conversion in [Γ] itself.

  The comparison theorem [forall d, spec_all d] is [PCUICCallByNeedSoundConv.spec_all_holds].
  Its read-back premise [rb_sound] is [PCUICCallByNeedSoundReadBack.rb_sound_holds]. Every
  other premise of [spec_term]'s call is discharged here from the obligation's own context,
  so [convert_cbn_sound] has no hypothesis beyond the obligation's. *)

Section HookProof.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).

  (** The start state of [cbn_run] is an instance of [minv] at [L = Q = #|Γ|]. *)
  Lemma run_s2_minv (Σ : global_env_ext) (Γ : context) (t u : term) :
    gok X_type X Γ #|Γ| Σ [] #|Γ| xH (run_ghost X_type X t u) (run_s2 X_type X t u) ->
    minv X_type X Γ #|Γ| Σ #|Γ| #|Γ| xH (run_ghost X_type X t u) (run_s2 X_type X t u).
  Proof.
    intros hok. apply minv_start; [reflexivity|exact hok|].
    intros a cl h. unfold heap_get in h. rewrite run_s2_heap, bh_get_holes in h.
    discriminate h.
  Qed.

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

  (** [cq] at [L = Q = #|Γ|], read at [Δ = []], for two terms scoped in [Γ]. *)
  Lemma cq_hook (Σ : global_env_ext) (Γ : context) (le : conv_pb) (t u : term) :
    is_closed_context Γ -> closedn #|Γ| t -> closedn #|Γ| u ->
    cq Γ #|Γ| Σ #|Γ| #|Γ| le t u -> ∥ Σ ;;; Γ ⊢ t ≤[le] u ∥.
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
    destruct (conv_term X_type X Γ #|Γ| cbn_depth #|Γ| le env_empty (run_c1 X_type X t)
                env_empty (run_c2 X_type X t u) [] (run_s2 X_type X t u))
      as [[[b rs'] s']|w] eqn:Ec; [|discriminate hc].
    destruct b; [|discriminate hc].
    destruct (spec_all_holds X_type X Γ #|Γ| Σ wfΣ hΣ eq_refl hΓ hhyg hcio
                (rb_sound_holds X_type X Γ #|Γ| Σ wfΣ hΓ hhyg) cbn_depth)
      as (_ & _ & _ & hT & _).
    destruct (hT #|Γ| #|Γ| xH (run_ghost X_type X t u) le env_empty (run_c1 X_type X t)
                env_empty (run_c2 X_type X t u) t u [] (run_s2 X_type X t u) true rs' s'
                (run_s2_minv Σ Γ t u hok) (Forall_nil _) hs1 hc1 hs2 hc2 Ec) as [_ hq].
    exact (cq_hook Σ Γ le t u hΓ (subject_closed htA) (subject_closed huB) (hq eq_refl)).
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
    destruct (abstract_env_ext_sq_wf X_type X Σ wfΣ) as [hwf].
    exact (cbn_conv_sound Σ Γ le t u hwf wfΣ (ht Σ wfΣ) (hu Σ wfΣ) (eq_sym Hcbn)).
  Qed.

End HookProof.
