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

(** * The evaluator seam of [PCUICCallByNeedSoundConv] is false at the fuel [cbn_run] uses

  [slot_seam] and [term_seam] read the comparison's inputs with the heap-following
  [repr_*] and promise, of every answer, that the caller's roots keep their [repr] reading
  ([root_pres]) and that the state keeps [cok], whose [gam_ok] asks every cell of the
  context map to stand, under [repr], for exactly the context entry it was made for.
  Forcing a cell writes its value back, and [repr] reads a forced cell as that value: a
  reduct of what it stood for, not the same term. So neither promise survives a single
  evaluation that forces a context cell.

  The run below is [cbn_run]'s own first [conv_term], at [cbn_depth], in
  [Γ = [x := (fun n : nat => n) O : nat]] with [t = x] and [u = fun n : nat => n]. The
  start state satisfies [cok] ([cok_run_s2]). [whnf] of [x] allocates the context cell of
  [x] at address 1, records it in [st_gam], forces it and writes back [VCon O []]; the
  comparison then answers [false] (constructor against lambda: no rule). [gam_ok] of the
  final state would need address 1 to stand under [repr] for the body
  [(fun n : nat => n) O]; it stands for [O]. [term_seam] promises [cok] of the final state,
  so it is false ([term_seam_false]). The same run through [conv_slot] on two inline slots
  refutes [slot_seam] ([slot_seam_false]). Nothing in the counterexample is ill-typed; and
  it is not a defect of the machine, which is sound here: it is a defect of the seam's
  heap-following invariant, the one [PCUICCallByNeedSoundEval]'s header explains why the
  evaluator replaced by the ghost reading. *)

Section SeamCounterexample.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Σ : global_env_ext).

  Definition sc_na : aname := {| binder_name := nAnon; binder_relevance := Relevant |}.
  Definition sc_nat : inductive :=
    {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |}.
  Definition sc_O : term := tConstruct sc_nat 0 [].
  Definition sc_body : term := tApp (tLambda sc_na (tInd sc_nat []) (tRel 0)) sc_O.
  Definition sc_Γ : context := [vdef sc_na sc_body (tInd sc_nat [])].
  Definition sc_t : term := tRel 0.
  Definition sc_u : term := tLambda sc_na (tInd sc_nat []) (tRel 0).

  (** [cok] holds of the state every call starts in. *)
  Lemma cok_run_s2 (Γ : context) (nctx lvl : nat) (t u : term) :
    PCUICCallByNeedSoundConv.cok X_type X Γ nctx lvl (run_s2 X_type X t u).
  Proof.
    split; [exists xH; apply run_s2_state_ok|].
    split; [apply run_s2_nofwd|].
    split; [intros l; apply run_s2_gam_ok|].
    split; [apply run_s2_memo_ok|apply run_s2_memo_inv].
  Qed.

  (** The run, by computation: the context cell of [x] is at address 1 and holds [O]. *)
  Lemma sc_term_run :
    match conv_term X_type X sc_Γ 1 false cbn_depth 1 Conv env_empty (run_c1 X_type X sc_t)
            env_empty (run_c2 X_type X sc_t sc_u) [] (run_s2 X_type X sc_t sc_u) with
    | COk (_, _, s) =>
        PTree.get (key_of_succ_nat 0) s.(st_gam) = Some (HAddr 1)
        /\ heap_get (HAddr 1) s = Some (CDone (VCon sc_O []))
    | CFail _ => False
    end.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma sc_slot_run :
    match conv_slot X_type X sc_Γ 1 false cbn_depth 1 Conv
            (SInl [] 0 0 (run_c1 X_type X sc_t)) (SInl [] 0 0 (run_c2 X_type X sc_t sc_u))
            [] (run_s2 X_type X sc_t sc_u) with
    | COk (_, _, s) =>
        PTree.get (key_of_succ_nat 0) s.(st_gam) = Some (HAddr 1)
        /\ heap_get (HAddr 1) s = Some (CDone (VCon sc_O []))
    | CFail _ => False
    end.
  Proof. vm_compute. split; reflexivity. Qed.

  (** No state whose context cell of [x] holds [O] satisfies [cok]. *)
  Lemma sc_not_cok (s : cbn_state) :
    PTree.get (key_of_succ_nat 0) s.(st_gam) = Some (HAddr 1) ->
    heap_get (HAddr 1) s = Some (CDone (VCon sc_O [])) ->
    ~ PCUICCallByNeedSoundConv.cok X_type X sc_Γ 1 1 s.
  Proof.
    intros hg hh (_ & _ & hgam & _ & _).
    destruct (hgam 1 0 (HAddr 1) hg) as (tm & hden & hr).
    cbn in hden. injection hden as <-.
    inversion hr as [lv a cl tm0 hget hcl]; subst.
    unfold heap_get in hh. rewrite hh in hget. injection hget as <-.
    inversion hcl; subst.
    match goal with h : repr_value _ _ _ (VCon _ _) _ |- _ => inversion h; subst end.
    match goal with h : repr_addrs _ _ _ [] _ |- _ => inversion h; subst end.
    match goal with h : mkApps sc_O [] = _ |- _ => cbv [mkApps sc_O] in h; discriminate h end.
  Qed.

  Lemma term_seam_false : ~ term_seam X_type X Σ sc_Γ 1 false cbn_depth.
  Proof.
    intros hseam.
    pose proof sc_term_run as hrun.
    destruct (conv_term X_type X sc_Γ 1 false cbn_depth 1 Conv env_empty
                (run_c1 X_type X sc_t) env_empty (run_c2 X_type X sc_t sc_u) []
                (run_s2 X_type X sc_t sc_u)) as [[[b rs] s']|w] eqn:E;
      [|contradiction hrun].
    destruct hrun as [hg hh].
    destruct (hseam 1 Conv sc_Γ env_empty (run_c1 X_type X sc_t) env_empty
                (run_c2 X_type X sc_t sc_u) [] (run_s2 X_type X sc_t sc_u) b rs s'
                (cok_run_s2 sc_Γ 1 1 sc_t sc_u) eq_refl eq_refl (le_n 1) E)
      as (_ & hcok & _).
    exact (sc_not_cok s' hg hh hcok).
  Qed.

  Lemma slot_seam_false : ~ slot_seam X_type X Σ sc_Γ 1 false cbn_depth.
  Proof.
    intros hseam.
    pose proof sc_slot_run as hrun.
    destruct (conv_slot X_type X sc_Γ 1 false cbn_depth 1 Conv
                (SInl [] 0 0 (run_c1 X_type X sc_t)) (SInl [] 0 0 (run_c2 X_type X sc_t sc_u))
                [] (run_s2 X_type X sc_t sc_u)) as [[[b rs] s']|w] eqn:E;
      [|contradiction hrun].
    destruct hrun as [hg hh].
    destruct (hseam 1 Conv sc_Γ (SInl [] 0 0 (run_c1 X_type X sc_t))
                (SInl [] 0 0 (run_c2 X_type X sc_t sc_u)) [] (run_s2 X_type X sc_t sc_u)
                b rs s' (cok_run_s2 sc_Γ 1 1 sc_t sc_u) eq_refl eq_refl (le_n 1) E)
      as (_ & hcok & _).
    exact (sc_not_cok s' hg hh hcok).
  Qed.

End SeamCounterexample.
