(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require CanonicalTries.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping
  PCUICOnFreeVars.
From MetaRocq.SafeChecker Require Import PCUICWfEnv PCUICCallByNeed PCUICCallByNeedSound
  PCUICCallByNeedSoundGC PCUICCallByNeedSoundCtx PCUICCallByNeedSoundMemo
  PCUICCallByNeedSoundHook PCUICCallByNeedSoundEval PCUICCallByNeedSoundConv.

Import CanonicalTries.

(** * The frame of a call against the evaluator's invariant (BET-298, step 4, part 1)

  [machine_sound] ([PCUICCallByNeedSoundEval]) takes the state invariant [gok] as a
  precondition. This file proves that the state [cbn_run] hands to its first [conv_term]
  satisfies it, from exactly what the hook in [PCUICTypeChecker.convert] has: [wf Σ] and
  the well-typedness of [t] and [u] in [Γ].

  - The ghost is empty on addresses (the heap is empty) and its code table is the real one:
    the two root entries [cbn_run] adds with [new_entry].
  - [mok]: [memo_inv] and [memo_ok] of the two [new_entry] calls ([memo_inv_init],
    [memo_inv_new_entry], [run_s2_memo_ok]), and [consts_okb] of the two root entries, from
    [typing_consts_okb'] on [t] and [u]. [PCUICCallByNeedSoundEval] never calls
    [typing_consts_okb']: this is the place the input terms enter the invariant.
  - The two root codes are in the ghost's table ([cok] of the evaluator), by
    [new_entry_in_table] and [new_entry_code_inv] ([run_c1_in_table], [run_c1_code_inv]).
  - The two initial suspensions read, under the ghost, as the hook's own [t] and [u]; this is
    the ghost twin of [cbn_run_frame]'s [repr_susp] clauses.
  - [machine_sound]'s premise [const_instance_ok] on the let-bodies of [Γ], from [wf_local]. *)

Section Frame.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).

  (** The ghost of the start state: no address, the real code table. *)
  Definition run_ghost (t u : term) : ghost :=
    mkGhost (fun _ => None) (((run_s2 X_type X t u).(st_memo)).(m_codes)).

  Lemma run_s2_gam_empty (t u : term) :
    (run_s2 X_type X t u).(st_gam) = PTree.empty haddr.
  Proof. unfold run_s2, run_s1. rewrite !new_entry_gam. reflexivity. Qed.

  Lemma run_s2_memo_inv (t u : term) : memo_inv X_type X (run_s2 X_type X t u).
  Proof.
    unfold run_s2, run_s1. apply memo_inv_new_entry, memo_inv_new_entry, memo_inv_init.
  Qed.

  (** Every entry of the start table names its constants at the right instance length. *)
  Lemma run_s2_consts_okb (Σ : global_env_ext) (t u : term) :
    consts_okb Σ t -> consts_okb Σ u ->
    forall i e, PTree.get i (((run_s2 X_type X t u).(st_memo)).(m_codes)) = Some e ->
      consts_okb Σ (inst_code e.(ce_inst) e.(ce_term)).
  Proof.
    intros ht hu i e hi. rewrite run_s2_codes in hi.
    destruct (key_eqb i (key_succ String2pos.xH)) eqn:E1.
    - apply key_eqb_spec in E1; subst i. rewrite PTree.gss in hi.
      injection hi as <-. cbn [ce_inst ce_term]. rewrite consts_inst_code. exact hu.
    - rewrite PTree.gso in hi by (apply key_neq_of_eqb, E1).
      destruct (key_eqb i String2pos.xH) eqn:E2.
      + apply key_eqb_spec in E2; subst i. rewrite PTree.gss in hi.
        injection hi as <-. cbn [ce_inst ce_term]. rewrite consts_inst_code. exact ht.
      + rewrite PTree.gso in hi by (apply key_neq_of_eqb, E2).
        rewrite PTree.gempty in hi. discriminate hi.
  Qed.

  (** The state invariant of [machine_sound] holds of the state [cbn_run] starts in, at every
    level and under every extension [Δ]: the heap and the context map are empty. *)
  Lemma run_s2_gok (Γ : context) (nctx : nat) (Σ : global_env_ext) (Δ : context)
      (lvl : nat) (t u : term) :
    consts_okb Σ t -> consts_okb Σ u ->
    gok X_type X Γ nctx Σ Δ lvl xH (run_ghost t u) (run_s2 X_type X t u).
  Proof.
    intros ht hu. split.
    - apply run_s2_state_ok.
    - apply run_s2_nofwd.
    - intros a cl h. unfold heap_get in h. rewrite run_s2_heap, bh_get_holes in h.
      discriminate h.
    - intros a tm h. discriminate h.
    - intros j a h. rewrite run_s2_gam_empty, PTree.gempty in h. discriminate h.
    - split; [apply run_s2_memo_inv|]. split; [apply run_s2_memo_ok|]. split.
      + intros i e hi. exact hi.
      + exact (run_s2_consts_okb Σ t u ht hu).
  Qed.

  (** The two root codes are in the ghost's table. *)
  Lemma run_c1_gcok (t u : term) :
    PCUICCallByNeedSoundEval.cok (run_ghost t u) (run_c1 X_type X t).
  Proof.
    exists (mkEntry t [] (NSInput false) (wf_term_univs X_type X t)). split.
    - exact (run_c1_in_table X_type X t u).
    - exact (run_c1_code_inv X_type X t).
  Qed.

  Lemma run_c2_gcok (t u : term) :
    PCUICCallByNeedSoundEval.cok (run_ghost t u) (run_c2 X_type X t u).
  Proof.
    exists (mkEntry u [] (NSInput true) (wf_term_univs X_type X u)). split.
    - exact (run_c2_in_table X_type X t u).
    - exact (run_c2_code_inv X_type X t u).
  Qed.

  (** A suspension of a code in the empty environment, at the call's own level, reads as the
    code itself, under any ghost. *)
  Lemma g_susp_env_empty (nctx : nat) (G : ghost) (t : term) :
    g_susp nctx nctx G env_empty t t.
  Proof.
    pose proof (g_susp_intro nctx nctx G [] 0 0 t [] (g_slots_nil nctx nctx G) eq_refl) as h.
    rewrite subst_empty, Nat.sub_diag in h. cbn [Nat.add] in h. rewrite lift0_id in h.
    exact h.
  Qed.

  Lemma run_c1_g_susp (nctx : nat) (t u : term) :
    g_susp nctx nctx (run_ghost t u) env_empty (run_c1 X_type X t).(c_term) t.
  Proof. rewrite run_c1_term. apply g_susp_env_empty. Qed.

  Lemma run_c2_g_susp (nctx : nat) (t u : term) :
    g_susp nctx nctx (run_ghost t u) env_empty (run_c2 X_type X t u).(c_term) u.
  Proof. rewrite run_c2_term. apply g_susp_env_empty. Qed.

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

  (** ** The frame lemma

    Everything [machine_sound] asks of the start of a call, from the hook's hypotheses: the
    side conditions on [nctx], [lvl] and [Δ], the context premise, the state invariant, and
    the two root suspensions with their codes in the table and their readings. *)
  Lemma cbn_run_gok_frame (Σ : global_env_ext) (Γ : context) (t u : term) :
    wf Σ -> welltyped Σ Γ t -> welltyped Σ Γ u ->
    #|([] : context)| = #|Γ| - #|Γ|
    /\ #|Γ| <= #|Γ|
    /\ (forall j decl b, nth_error Γ j = Some decl -> decl.(decl_body) = Some b ->
          consts_okb Σ b)
    /\ gok X_type X Γ #|Γ| Σ [] #|Γ| xH (run_ghost t u) (run_s2 X_type X t u)
    /\ g_susp #|Γ| #|Γ| (run_ghost t u) env_empty (run_c1 X_type X t).(c_term) t
    /\ PCUICCallByNeedSoundEval.cok (run_ghost t u) (run_c1 X_type X t)
    /\ g_susp #|Γ| #|Γ| (run_ghost t u) env_empty (run_c2 X_type X t u).(c_term) u
    /\ PCUICCallByNeedSoundEval.cok (run_ghost t u) (run_c2 X_type X t u).
  Proof.
    intros wfΣ [A htA] [B huB].
    split; [cbn; lia|]. split; [lia|].
    split; [exact (wf_local_consts_okb Σ Γ wfΣ (typing_wf_local htA))|].
    split.
    { apply run_s2_gok.
      - exact (typing_consts_okb' Σ Γ t A wfΣ htA).
      - exact (typing_consts_okb' Σ Γ u B wfΣ huB). }
    split; [apply run_c1_g_susp|]. split; [apply run_c1_gcok|].
    split; [apply run_c2_g_susp|apply run_c2_gcok].
  Qed.

End Frame.
