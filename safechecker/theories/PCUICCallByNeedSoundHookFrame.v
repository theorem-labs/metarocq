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

Local Notation xpredT := (fun _ : nat => true) (only parsing).

(** * The frame of a call against the evaluator's invariant

  [machine_sound] ([PCUICCallByNeedSoundEval]) takes the state invariant [gok] as a
  precondition. This file proves that the state [cbn_run] hands to its first [conv_term]
  satisfies it, from exactly what the hook in [PCUICTypeChecker.convert] has: [wf Σ] and
  the well-typedness of [t] and [u] in [Γ] ([cbn_run_gok_frame]).

  - [gok] of the start state is [PCUICCallByNeedSoundLevel.run_s2_gok]. Its premises on the
    input terms come from here: [consts_okb] of [t] and [u] from [typing_consts_okb'], and
    their hygiene from [typing_hyg]. [PCUICCallByNeedSoundEval] never calls
    [typing_consts_okb']: this is the place the input terms enter the invariant.
  - The two root codes are in the ghost's table ([cok] of the evaluator) and their initial
    suspensions read, under the ghost, as the hook's own [t] and [u]
    ([run_c1_g_susp], [run_c1_gcok], [run_c2_g_susp], [run_c2_gcok]).
  - [machine_sound]'s premises on the let-bodies of [Γ], [consts_okb] and [ctx_hyg], come
    from [wf_local] ([wf_local_consts_okb], [wf_local_ctx_hyg]). *)

Section Frame.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).

  (** [machine_sound]'s premise on the context: every let-body of a well-formed context
    names its constants at the right instance length. *)
  Lemma wf_local_consts_okb (Σ : global_env_ext) (Γ : context) :
    wf Σ -> wf_local Σ Γ ->
    forall j decl b, nth_error Γ j = Some decl -> decl.(decl_body) = Some b ->
      consts_okb Σ b.
  Proof.
    intros wfΣ wfΓ j decl b hj hb.
    pose proof (All_local_env_nth_error wfΓ hj) as hd.
    destruct decl as [na [b'|] ty]; cbn in hb; [|discriminate hb].
    injection hb as <-. cbn in hd. destruct hd as [hbt _]. cbn in hbt.
    exact (typing_consts_okb' Σ _ b' ty wfΣ hbt).
  Qed.

  (** A typed term is hygienic: it is closed in its context ([subject_closed]). *)
  Lemma typing_hyg (Σ : global_env_ext) (Γ : context) (t T : term) :
    wf Σ -> Σ ;;; Γ |- t : T -> on_free_vars xpredT t.
  Proof.
    intros wfΣ ht. pose proof (subject_closed ht) as hc.
    eapply on_free_vars_impl; [|exact (closedn_on_free_vars (P := xpredT) hc)].
    intros; reflexivity.
  Qed.

  (** The hygiene premise of [gok] on the context: every let-body of a well-formed context is
    hygienic. *)
  Lemma wf_local_ctx_hyg (Σ : global_env_ext) (Γ : context) :
    wf Σ -> wf_local Σ Γ -> ctx_hyg Γ.
  Proof.
    intros wfΣ wfΓ j decl b hj hb.
    pose proof (All_local_env_nth_error wfΓ hj) as hd.
    destruct decl as [na [b'|] ty]; cbn in hb; [|discriminate hb].
    injection hb as <-. cbn in hd. destruct hd as [hbt _]. cbn in hbt.
    exact (typing_hyg Σ _ b' ty wfΣ hbt).
  Qed.

  (** The hook's instance of every section hypothesis of [machine_sound] and of
    [PCUICCallByNeedSoundLevel]'s [Master] section that depends on the context: [Δ = []],
    [nctx = lvl = #|Γ|], [const_instance_ok], [ctx_hyg] and [is_closed_context], from
    [wf Σ] and [wf_local Σ Γ]. *)
  Lemma eval_section_instance (Σ : global_env_ext) (Γ : context) :
    wf Σ -> wf_local Σ Γ ->
    #|([] : context)| = #|Γ| - #|Γ| /\ #|Γ| = #|Γ| /\ #|Γ| <= #|Γ|
    /\ (forall j decl b, nth_error Γ j = Some decl -> decl.(decl_body) = Some b ->
          consts_okb Σ b)
    /\ ctx_hyg Γ /\ is_closed_context Γ.
  Proof.
    intros wfΣ wfΓ. split; [cbn; lia|]. split; [reflexivity|]. split; [lia|].
    split; [exact (wf_local_consts_okb Σ Γ wfΣ wfΓ)|].
    split; [exact (wf_local_ctx_hyg Σ Γ wfΣ wfΓ)|].
    exact (wf_local_closed_context (wfΣ := wfΣ) wfΓ).
  Qed.

  (** ** The frame lemma

    Everything [machine_sound] asks of the start of a call, from the hook's hypotheses: the
    side conditions on [nctx], [lvl] and [Δ], the context premise, the state invariant (with
    its hygiene clauses: the root entries [t] and [u] are hygienic because they are typed),
    the hygiene of [Γ]'s let-bodies under which [gok]'s hygiene clauses apply, and the two
    root suspensions with their codes in the table and their readings. *)
  Lemma cbn_run_gok_frame (Σ : global_env_ext) (Γ : context) (t u : term) :
    wf Σ -> welltyped Σ Γ t -> welltyped Σ Γ u ->
    #|([] : context)| = #|Γ| - #|Γ|
    /\ #|Γ| <= #|Γ|
    /\ (forall j decl b, nth_error Γ j = Some decl -> decl.(decl_body) = Some b ->
          consts_okb Σ b)
    /\ ctx_hyg Γ
    /\ gok X_type X Γ #|Γ| Σ [] #|Γ| xH (run_ghost X_type X t u) (run_s2 X_type X t u)
    /\ g_susp #|Γ| #|Γ| (run_ghost X_type X t u) env_empty (run_c1 X_type X t).(c_term) t
    /\ PCUICCallByNeedSoundEval.cok (run_ghost X_type X t u) (run_c1 X_type X t)
    /\ g_susp #|Γ| #|Γ| (run_ghost X_type X t u) env_empty (run_c2 X_type X t u).(c_term) u
    /\ PCUICCallByNeedSoundEval.cok (run_ghost X_type X t u) (run_c2 X_type X t u).
  Proof.
    intros wfΣ [A htA] [B huB].
    split; [cbn; lia|]. split; [lia|].
    split; [exact (wf_local_consts_okb Σ Γ wfΣ (typing_wf_local htA))|].
    split; [exact (wf_local_ctx_hyg Σ Γ wfΣ (typing_wf_local htA))|].
    split.
    { apply run_s2_gok.
      - exact (typing_consts_okb' Σ Γ t A wfΣ htA).
      - exact (typing_consts_okb' Σ Γ u B wfΣ huB).
      - exact (typing_hyg Σ Γ t A wfΣ htA).
      - exact (typing_hyg Σ Γ u B wfΣ huB). }
    split; [apply run_c1_g_susp|]. split; [apply run_c1_gcok|].
    split; [apply run_c2_g_susp|apply run_c2_gcok].
  Qed.

End Frame.
