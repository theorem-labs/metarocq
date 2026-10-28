(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require CanonicalTries.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping
  PCUICOnFreeVars PCUICReduction PCUICClosed PCUICClosedTyp.
From MetaRocq.SafeChecker Require Import PCUICWfEnv PCUICCallByNeed PCUICCallByNeedSound
  PCUICCallByNeedSoundGC PCUICCallByNeedSoundCtx PCUICCallByNeedSoundMemo
  PCUICCallByNeedSoundHook PCUICCallByNeedSoundEval PCUICCallByNeedSoundLevel.
From MetaRocq.PCUIC Require Import PCUICWellScopedCumulativity.

Import CanonicalTries.

Local Notation cbn_xpredT := (fun _ : nat => true) (only parsing).

(** * The frame of a call against the evaluator's invariant

  [cbn_machine_sound] ([PCUICCallByNeedSoundEval]) takes the state invariant [cbn_gok] as a
  precondition. This file proves that the state [cbn_run] hands to its first [cbn_conv_term]
  satisfies it, from exactly what the hook in [PCUICTypeChecker.convert] has: [wf Σ] and
  the well-typedness of [t] and [u] in [Γ] ([cbn_run_gok_frame]).

  - [cbn_gok] of the start state is [PCUICCallByNeedSoundLevel.cbn_run_s2_gok]. Its premises on the
    input terms come from here: [cbn_consts_okb] of [t] and [u] from [cbn_typing_consts_okb'], and
    their hygiene from [cbn_typing_hyg]. [PCUICCallByNeedSoundEval] never calls
    [cbn_typing_consts_okb']: this is the place the input terms enter the invariant.
  - The two root codes are in the ghost's table ([cbn_cok] of the evaluator) and their initial
    suspensions read, under the ghost, as the hook's own [t] and [u]
    ([cbn_run_c1_g_susp], [cbn_run_c1_gcok], [cbn_run_c2_g_susp], [cbn_run_c2_gcok]).
  - [cbn_machine_sound]'s premises on the let-bodies of [Γ], [cbn_consts_okb] and [cbn_ctx_hyg],
  come
    from [wf_local] ([cbn_wf_local_consts_okb], [cbn_wf_local_ctx_hyg]). *)

Section Frame.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).

  (** [cbn_machine_sound]'s premise on the context: every let-body of a well-formed context
    names its constants at the right instance length. *)
  Lemma cbn_wf_local_consts_okb (Σ : global_env_ext) (Γ : context) :
    wf Σ -> wf_local Σ Γ ->
    forall j decl b, nth_error Γ j = Some decl -> decl.(decl_body) = Some b ->
      cbn_consts_okb Σ b.
  Proof.
    intros wfΣ wfΓ j decl b hj hb.
    pose proof (All_local_env_nth_error wfΓ hj) as hd.
    destruct decl as [na [b'|] ty]; cbn in hb; [|discriminate hb].
    injection hb as <-. cbn in hd. destruct hd as [hbt _]. cbn in hbt.
    exact (cbn_typing_consts_okb' Σ _ b' ty wfΣ hbt).
  Qed.

  (** A typed term is hygienic: it is closed in its context ([subject_closed]). *)
  Lemma cbn_typing_hyg (Σ : global_env_ext) (Γ : context) (t T : term) :
    wf Σ -> Σ ;;; Γ |- t : T -> on_free_vars cbn_xpredT t.
  Proof.
    intros wfΣ ht. pose proof (subject_closed ht) as hc.
    eapply on_free_vars_impl; [|exact (closedn_on_free_vars (P := cbn_xpredT) hc)].
    intros; reflexivity.
  Qed.

  (** The hygiene premise of [cbn_gok] on the context: every let-body of a well-formed context is
    hygienic. *)
  Lemma cbn_wf_local_ctx_hyg (Σ : global_env_ext) (Γ : context) :
    wf Σ -> wf_local Σ Γ -> cbn_ctx_hyg Γ.
  Proof.
    intros wfΣ wfΓ j decl b hj hb.
    pose proof (All_local_env_nth_error wfΓ hj) as hd.
    destruct decl as [na [b'|] ty]; cbn in hb; [|discriminate hb].
    injection hb as <-. cbn in hd. destruct hd as [hbt _]. cbn in hbt.
    exact (cbn_typing_hyg Σ _ b' ty wfΣ hbt).
  Qed.

  (** The hook's instance of every section hypothesis of [cbn_machine_sound] and of
    [PCUICCallByNeedSoundLevel]'s [Master] section that depends on the context: [Δ = []],
    [nctx = lvl = #|Γ|], [const_instance_ok], [cbn_ctx_hyg] and [is_closed_context], from
    [wf Σ] and [wf_local Σ Γ]. *)
  Lemma cbn_eval_section_instance (Σ : global_env_ext) (Γ : context) :
    wf Σ -> wf_local Σ Γ ->
    #|([] : context)| = #|Γ| - #|Γ| /\ #|Γ| = #|Γ| /\ #|Γ| <= #|Γ|
    /\ (forall j decl b, nth_error Γ j = Some decl -> decl.(decl_body) = Some b ->
          cbn_consts_okb Σ b)
    /\ cbn_ctx_hyg Γ /\ is_closed_context Γ.
  Proof.
    intros wfΣ wfΓ. split; [cbn; lia|]. split; [reflexivity|]. split; [lia|].
    split; [exact (cbn_wf_local_consts_okb Σ Γ wfΣ wfΓ)|].
    split; [exact (cbn_wf_local_ctx_hyg Σ Γ wfΣ wfΓ)|].
    exact (wf_local_closed_context (wfΣ := wfΣ) wfΓ).
  Qed.

  (** ** The frame lemma

    Everything [cbn_machine_sound] asks of the start of a call, from the hook's hypotheses: the
    side conditions on [nctx], [lvl] and [Δ], the context premise, the state invariant (with
    its hygiene clauses: the root entries [t] and [u] are hygienic because they are typed),
    the hygiene of [Γ]'s let-bodies under which [cbn_gok]'s hygiene clauses apply, and the two
    root suspensions with their codes in the table and their readings. *)
  Lemma cbn_run_gok_frame (Σ : global_env_ext) (Γ : context) (t u : term) :
    wf Σ -> welltyped Σ Γ t -> welltyped Σ Γ u ->
    #|([] : context)| = #|Γ| - #|Γ|
    /\ #|Γ| <= #|Γ|
    /\ (forall j decl b, nth_error Γ j = Some decl -> decl.(decl_body) = Some b ->
          cbn_consts_okb Σ b)
    /\ cbn_ctx_hyg Γ
    /\ cbn_gok X_type X Γ #|Γ| Σ [] #|Γ| xH (cbn_run_ghost X_type X t u) (cbn_run_s2 X_type X t u)
    /\ cbn_g_susp #|Γ| #|Γ| (cbn_run_ghost X_type X t u) cbn_env_empty
      (cbn_run_c1 X_type X t).(cbn_c_term) t
    /\ PCUICCallByNeedSoundEval.cbn_cok (cbn_run_ghost X_type X t u) (cbn_run_c1 X_type X t)
    /\ cbn_g_susp #|Γ| #|Γ| (cbn_run_ghost X_type X t u) cbn_env_empty
      (cbn_run_c2 X_type X t u).(cbn_c_term) u
    /\ PCUICCallByNeedSoundEval.cbn_cok (cbn_run_ghost X_type X t u) (cbn_run_c2 X_type X t u).
  Proof.
    intros wfΣ [A htA] [B huB].
    split; [cbn; lia|]. split; [lia|].
    split; [exact (cbn_wf_local_consts_okb Σ Γ wfΣ (typing_wf_local htA))|].
    split; [exact (cbn_wf_local_ctx_hyg Σ Γ wfΣ (typing_wf_local htA))|].
    split.
    { apply cbn_run_s2_gok.
      - exact (cbn_typing_consts_okb' Σ Γ t A wfΣ htA).
      - exact (cbn_typing_consts_okb' Σ Γ u B wfΣ huB).
      - exact (cbn_typing_hyg Σ Γ t A wfΣ htA).
      - exact (cbn_typing_hyg Σ Γ u B wfΣ huB). }
    split; [apply cbn_run_c1_g_susp|]. split; [apply cbn_run_c1_gcok|].
    split; [apply cbn_run_c2_g_susp|apply cbn_run_c2_gcok].
  Qed.

End Frame.
