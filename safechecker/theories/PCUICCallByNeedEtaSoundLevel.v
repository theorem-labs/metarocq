(* Distributed under the terms of the MIT license. *)
(** ETA-COPY (wip/etak-cbne-2026-10-30) of integ-all8's [PCUICCallByNeedSoundLevel] (1a92b56c) over the η environment
    ([PCUICWfEnvEta], [PCUICCallByNeedEta]): see [PCUICCallByNeedEtaSoundHookProof] for what differs. *)
From Stdlib Require Import BinPos BinNat Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require CanonicalTries.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping
  PCUICOnFreeVars PCUICReduction PCUICSigmaCalculus PCUICRenameDef PCUICRenameConv
  PCUICOnFreeVarsConv PCUICWeakeningConv PCUICRedTypeIrrelevance BDStrengthening
  PCUICWellScopedCumulativity PCUICClosedBodies PCUICTypingEta PCUICClosedTypEta.
From MetaRocq.SafeChecker Require Import PCUICWfEnvEta PCUICCallByNeedEta PCUICCallByNeedEtaSound
  PCUICCallByNeedEtaSoundGC PCUICCallByNeedEtaSoundCtx PCUICCallByNeedEtaSoundMemo
  PCUICCallByNeedEtaSoundHook PCUICCallByNeedEtaSoundCong PCUICCallByNeedEtaSoundEval
  PCUICCallByNeedEtaSoundHeapWf.

Import CanonicalTries.

Local Notation cbn_xpredT := (fun _ : nat => true) (only parsing).
Local Notation cbn_xpred0 := (fun _ : nat => false) (only parsing).

(** * The comparison's levels against the evaluator's invariant

  The comparison crosses binders, so it reads its inputs at a level [L] that grows and
  shrinks, while [cbn_gok] cannot change its level downwards while a stale fresh-variable cell
  exists ([PCUICCallByNeedCounterexamples.cbn_ghost_shift_false], [cbn_ghost_map_false]).

  The design: [cbn_gok] is kept at a MASTER level [Q], the highest level the comparison has
  reached, with the junk context [cbn_jctx (Q - nctx)] for the variables between [nctx] and [Q];
  the comparison's logical level is [L <= Q]. The machine runs at [Q] ([cbn_machine_sound] is
  level-free in its code). A root the comparison holds at [L] reads at [Q] as [lift0 (Q - L)]
  of its logical reading, and a reduct of such a reading is again a lift
  ([cbn_red_unlift], by [red_rename_cb]): that is how a fact at [Q] becomes a fact at [L].

  - [cbn_gok_raise] lifts the master level, [Q] to [Q + n], with every ghost term lifted by [n]
    ([cbn_gshift]). It needs [cbn_hwf Q] of [PCUICCallByNeedEtaSoundHeapWf]: no cell names a fresh
    variable at a level [>= Q], and the head of every constructor and neutral constant value
    is closed. That is a whole-heap STRUCTURAL invariant, true at the master level (fresh
    variables are only allocated below it) but not one the ghost reading can see; the machine
    keeps it by [cbn_machine_hwf_holds], under [#|Γ| <= nctx]. It also needs
    [cbn_gk_hyg], the hygiene of every ghost term, for red weakening
    ([PCUICCallByNeedCounterexamples.cbn_red_weakening_needs_hygiene]).
  - [cbn_red_unlift] and [cbn_red_assum_irrel] do NOT depend on [cbn_gk_hyg]: the terms they move
  are
    root readings, which are reducts of the typed inputs of the hook, hence hygienic by
    themselves ([red_on_free_vars_cb]). *)

(** ** The junk context and the lifted ghost *)

Definition cbn_jdecl : context_decl :=
  vass {| binder_name := nAnon; binder_relevance := Relevant |} (tSort sProp).
Definition cbn_jctx (n : nat) : context := repeat cbn_jdecl n.

Lemma cbn_jctx_length n : #|cbn_jctx n| = n.
Proof. apply repeat_length. Qed.

Lemma cbn_jctx_add m n : cbn_jctx (m + n) = cbn_jctx n ,,, cbn_jctx m.
Proof. unfold cbn_jctx, app_context. rewrite repeat_app. reflexivity. Qed.

Lemma cbn_jctx_closed p n : on_free_vars_ctx p (cbn_jctx n).
Proof.
  revert p. induction n as [|n ih]; intros p; [reflexivity|].
  change (cbn_jctx (S n)) with (cbn_jctx n ,, cbn_jdecl). rewrite on_free_vars_ctx_snoc, ih.
  reflexivity.
Qed.

Lemma cbn_jctx_assum n : assumption_context (cbn_jctx n).
Proof. induction n as [|n ih]; cbn; constructor; exact ih. Qed.

Definition cbn_gshift (n : nat) (G : cbn_ghost) : cbn_ghost :=
  cbn_mkGhost (fun a => option_map (lift0 n) (G a)) (cbn_gc G).

(** ** Readings commute with the lift of the ghost *)

Section Shift.
  Context (nctx lvl n : nat) (hle : nctx <= lvl).

  Lemma cbn_lift_susp_read N nvals t ts :
    #|ts| = nvals ->
    lift0 n (subst ts 0 (lift N nvals t)) = subst (map (lift0 n) ts) 0 (lift (n + N) nvals t).
  Proof.
    intros hl. rewrite distr_lift_subst, Nat.add_0_r, hl.
    rewrite (simpl_lift t N nvals n nvals) by lia. reflexivity.
  Qed.

  Lemma cbn_g_slot_shift G :
    (forall x t, cbn_g_slot nctx lvl G x t ->
      cbn_g_slot nctx (lvl + n) (cbn_gshift n G) x (lift0 n t))
    /\ (forall l ts, cbn_g_slots nctx lvl G l ts ->
          cbn_g_slots nctx (lvl + n) (cbn_gshift n G) l (map (lift0 n) ts) /\ #|ts| = #|l|).
  Proof.
    apply (cbn_g_slot_mutind nctx lvl G
             (fun x t => cbn_g_slot nctx (lvl + n) (cbn_gshift n G) x (lift0 n t))
             (fun l ts => cbn_g_slots nctx (lvl + n) (cbn_gshift n G) l (map (lift0 n) ts)
                          /\ #|ts| = #|l|)).
    - intros a t ha. constructor. cbn. rewrite ha. reflexivity.
    - intros vals nvals goff c ts _ [ih hl] hn hc.
      rewrite (cbn_lift_susp_read _ nvals) by lia.
      replace (n + (lvl - nctx + goff)) with (lvl + n - nctx + goff) by lia.
      constructor; [exact ih|exact hn|exact hc].
    - split; [constructor|reflexivity].
    - intros x l t ts _ ih1 _ [ih2 hl]. split; [constructor; assumption|cbn; congruence].
  Qed.

  Lemma cbn_g_susp_shift G e t u :
    cbn_g_susp nctx lvl G e t u -> cbn_g_susp nctx (lvl + n) (cbn_gshift n G) e t (lift0 n u).
  Proof.
    intros h. inversion h as [vals nvals goff t0 ts hs hn]; subst.
    destruct (proj2 (cbn_g_slot_shift G) _ _ hs) as [hs' hl].
    rewrite (cbn_lift_susp_read _ #|vals|) by lia.
    replace (n + (lvl - nctx + goff)) with (lvl + n - nctx + goff) by lia.
    constructor; [exact hs'|reflexivity].
  Qed.

  Lemma cbn_g_addrs_shift G l ts :
    cbn_g_addrs G l ts -> cbn_g_addrs (cbn_gshift n G) l (map (lift0 n) ts).
  Proof.
    induction 1 as [|a t l ts ha hl ih]; constructor; [cbn; rewrite ha; reflexivity|exact ih].
  Qed.

  Lemma cbn_g_value_shift G v t :
    cbn_vwf lvl v -> cbn_g_value nctx lvl G v t ->
      cbn_g_value nctx (lvl + n) (cbn_gshift n G) v (lift0 n t).
  Proof.
    intros hw hv. destruct hv; cbn in hw; rewrite ?lift_mkApps.
    - rewrite (lift_closed n 0 h hw). constructor. exact (cbn_g_addrs_shift G _ _ H).
    - constructor; [exact (cbn_g_susp_shift G _ _ _ H)|exact H0].
    - constructor; [exact (cbn_g_susp_shift G _ _ _ H)|exact H0].
    - cbn [lift]. destruct (Nat.leb_spec 0 (lvl - S l)) as [_|]; [|lia].
      replace (n + (lvl - S l)) with (lvl + n - S l) by lia.
      constructor. exact (cbn_g_addrs_shift G _ _ H).
    - rewrite (lift_closed n 0 h hw). constructor. exact (cbn_g_addrs_shift G _ _ H).
    - econstructor; [exact (cbn_g_susp_shift G _ _ _ H)|exact H0|exact
      (cbn_g_addrs_shift G _ _ H1)].
    - econstructor; [exact H|exact (cbn_g_susp_shift G _ _ _ H0)|exact H1|exact
      (cbn_g_addrs_shift G _ _ H2)].
    - econstructor; [exact H|exact (cbn_g_susp_shift G _ _ _ H0)|exact H1|exact
      (cbn_g_addrs_shift G _ _ H2)].
  Qed.

  Lemma cbn_g_cell_shift G cl u :
    cbn_cwf lvl cl -> cbn_g_cell nctx lvl G cl u ->
      cbn_g_cell nctx (lvl + n) (cbn_gshift n G) cl (lift0 n u).
  Proof.
    intros hw hc. destruct hc; cbn in hw.
    - constructor; [exact (cbn_g_susp_shift G _ _ _ H)|exact H0].
    - constructor. exact (cbn_g_value_shift G _ _ hw H).
  Qed.

  Lemma cbn_ctx_den_shift Γ j t :
    nctx = #|Γ| -> cbn_ctx_den Γ nctx lvl j = Some t ->
      cbn_ctx_den Γ nctx (lvl + n) j = Some (lift0 n t).
  Proof.
    intros hn. unfold cbn_ctx_den. destruct (nth_error Γ j) as [decl|] eqn:E; [|discriminate].
    pose proof (nth_error_Some_length E) as hj.
    destruct (decl_body decl) as [b|]; intros h; injection h as <-; f_equal.
    - rewrite (simpl_lift b (lvl - nctx + S j) 0 n 0) by lia. f_equal. lia.
    - cbn [lift]. destruct (Nat.leb_spec 0 (lvl - S (nctx - S j))) as [_|]; [|lia].
      f_equal. lia.
  Qed.
End Shift.

(** ** Raising the master level *)

Section Raise.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat) (Σ : global_env_ext).
  Context (wfΣ : wfE Σ) (hnctx : nctx = #|Γ|) (hΓ : is_closed_context Γ) (hhyg : cbn_ctx_hyg Γ).

  Lemma cbn_master_ctx_xpredT Q : on_ctx_free_vars cbn_xpredT (Γ ,,, cbn_jctx Q).
  Proof.
    apply (on_free_vars_ctx_on_ctx_free_vars_xpredT (P := cbn_xpred0)).
    rewrite on_free_vars_ctx_app, hΓ. apply cbn_jctx_closed.
  Qed.

  (** A ghost reduction at [Q] lifts to [Q + n]: red weakening, which needs the hygiene of the
    ghost term (ETA-COPY: [weakening_red_0_cb] under [ClosedBodies Σ], from [wfE_ClosedBodies]). *)
  Lemma cbn_cred_raise Q n t u :
    on_free_vars cbn_xpredT t ->
    cbn_cred Γ Σ (cbn_jctx Q) t u -> cbn_cred Γ Σ (cbn_jctx (n + Q)) (lift0 n t) (lift0 n u).
  Proof.
    intros ht [hr]. constructor.
    rewrite cbn_jctx_add, app_context_assoc.
    eapply (weakening_red_0_cb (wfΣ := wfE_ClosedBodies Σ) (P := cbn_xpredT) (Γ' := cbn_jctx n)).
    - symmetry. apply cbn_jctx_length.
    - apply cbn_master_ctx_xpredT.
    - exact ht.
    - exact hr.
  Qed.

  Lemma cbn_gok_raise Q n lo G s :
    nctx <= Q -> cbn_hwf Q s ->
    cbn_gok X_type X Γ nctx Σ (cbn_jctx (Q - nctx)) Q lo G s ->
    cbn_gok X_type X Γ nctx Σ (cbn_jctx (Q + n - nctx)) (Q + n) lo (cbn_gshift n G) s.
  Proof.
    intros hQ hw hok.
    replace (Q + n - nctx) with (n + (Q - nctx)) by lia.
    split.
    - exact (cbn_gk_state _ _ _ _ _ _ _ _ _ _ hok).
    - exact (cbn_gk_nofwd _ _ _ _ _ _ _ _ _ _ hok).
    - intros a cl ha.
      destruct (cbn_gk_cells _ _ _ _ _ _ _ _ _ _ hok a cl ha) as (t & ht & hc).
      exists (lift0 n t). split; [cbn; rewrite ht; reflexivity|].
      destruct hc as [hb|(u & hu & hr)]; [left; exact hb|right].
      exists (lift0 n u). split.
      + exact (cbn_g_cell_shift nctx Q n hQ G cl u (hw a cl ha) hu).
      + exact (cbn_cred_raise (Q - nctx) n t u (cbn_gk_hyg _ _ _ _ _ _ _ _ _ _ hok hhyg a t ht) hr).
    - intros a t ht. cbn in ht. destruct (G a) as [t0|] eqn:E; [|discriminate ht].
      exact (cbn_gk_dom _ _ _ _ _ _ _ _ _ _ hok a t0 E).
    - intros j a hj. destruct (cbn_gk_gam _ _ _ _ _ _ _ _ _ _ hok j a hj) as (t & hden & hGa).
      exists (lift0 n t). split.
      + exact (cbn_ctx_den_shift nctx Q n hQ Γ j t hnctx hden).
      + cbn. rewrite hGa. reflexivity.
    - exact (cbn_gk_memo _ _ _ _ _ _ _ _ _ _ hok).
    - intros hc a t ht. cbn in ht. destruct (G a) as [t0|] eqn:E; [|discriminate ht].
      injection ht as <-. apply cbn_hyg_lift. exact (cbn_gk_hyg _ _ _ _ _ _ _ _ _ _ hok hc a t0 E).
  Qed.
End Raise.

(** ** From the master level to the logical level *)

(** A reduct of a lifted term is a lift, and the reduction happens below the lift. The
  source is a root reading, hygienic because it is a reduct of a typed input; nothing here
  uses [cbn_gk_hyg]. (ETA-COPY: [red_rename_cb] and [red_on_free_vars_cb] under
  [ClosedBodies Σ], from [wfE_ClosedBodies].) *)
Lemma cbn_red_unlift {cf : checker_flags} (Σ : global_env_ext) (wfΣ : wfE Σ) (Ξ J : context)
    (t u : term) :
  on_ctx_free_vars cbn_xpredT Ξ -> on_free_vars cbn_xpredT t ->
  red Σ (Ξ ,,, J) (lift0 #|J| t) u ->
  exists u', u = lift0 #|J| u' /\ ∥ red Σ Ξ t u' ∥.
Proof.
  intros hΞ ht hr.
  pose (P := strengthenP 0 #|J| cbn_xpredT).
  pose (f := unlift_renaming #|J| 0).
  assert (hctx : on_ctx_free_vars P (Ξ ,,, J)).
  { exact (on_ctx_free_vars_strengthenP Ξ J [] hΞ eq_refl). }
  assert (hsrc : on_free_vars P (lift0 #|J| t)).
  { unfold P. rewrite on_free_vars_lift. exact ht. }
  assert (hren : urenaming P (Ξ ,,, J) Ξ f).
  { exact (urenaming_strengthen cbn_xpredT Ξ J []). }
  pose proof (red_rename_cb P Σ (Ξ ,,, J) Ξ (lift0 #|J| t) u f (wfE_ClosedBodies Σ) hren hctx hsrc hr)
    as hr'.
  pose proof (red_on_free_vars_cb (wfΣ := wfE_ClosedBodies Σ) hctx hsrc hr) as hu.
  assert (hlu : rename f (lift0 #|J| t) = t).
  { rewrite lift_rename, rename_compose.
    rewrite (rename_ext _ ren_id (lift_unlift #|J| 0)). apply rename_ren_id. }
  exists (rename f u). split.
  - rewrite lift_rename, rename_compose.
    rewrite (rename_ext_cond P (lift_renaming #|J| 0 ∘ f) ren_id u);
      [now rewrite rename_ren_id| |exact hu].
    intros i hi. unfold P, strengthenP in hi. cbn in hi.
    destruct (Nat.ltb_spec i #|J|) as [hlt|hge]; [discriminate hi|].
    unfold f, lift_renaming, unlift_renaming, ren_id. cbn.
    destruct (Nat.ltb_spec i 0); [lia|].
    destruct (Nat.leb_spec 0 (i - #|J|)); [lia|lia].
  - constructor. rewrite hlu in hr'. exact hr'.
Qed.

(** The types of the variables of an assumption context are irrelevant to reduction. *)
Lemma cbn_red_assum_irrel (Σ : global_env) (Ξ Δ1 Δ2 : context) (t u : term) :
  #|Δ1| = #|Δ2| -> assumption_context Δ1 ->
  red Σ (Ξ ,,, Δ1) t u -> red Σ (Ξ ,,, Δ2) t u.
Proof.
  intros hl ha. apply context_pres_let_bodies_red.
  revert Δ2 hl ha. induction Δ1 as [|d1 Δ1 ih]; intros [|d2 Δ2] hl ha; cbn in hl;
    try discriminate.
  - apply pres_let_bodies_ctx_refl.
  - assert (hb : decl_body d1 = None) by (inversion ha; reflexivity).
    assert (ha' : assumption_context Δ1) by (inversion ha; assumption).
    constructor; [apply ih; [congruence|exact ha']|].
    unfold pres_let_bodies. rewrite hb. exact tt.
Qed.

(** ** The state a run starts in, against [cbn_gok] *)

Section RunStart.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).

  (** The ghost of the start state: no address, the real code table. *)
  Definition cbn_run_ghost (t u : term) : cbn_ghost :=
    cbn_mkGhost (fun _ => None) (((cbn_run_s2 X_type X t u).(cbn_st_memo)).(cbn_m_codes)).

  Lemma cbn_run_s2_gam_empty (t u : term) :
    (cbn_run_s2 X_type X t u).(cbn_st_gam) = PTree.empty cbn_haddr.
  Proof. unfold cbn_run_s2, cbn_run_s1. rewrite !cbn_new_entry_gam. reflexivity. Qed.

  Lemma cbn_run_s2_memo_inv (t u : term) : cbn_memo_inv X_type X (cbn_run_s2 X_type X t u).
  Proof.
    unfold cbn_run_s2, cbn_run_s1. apply cbn_memo_inv_new_entry, cbn_memo_inv_new_entry,
      cbn_memo_inv_init.
  Qed.

  (** Every entry of the start table names its constants at the right instance length. *)
  Lemma cbn_run_s2_consts_okb (Σ : global_env_ext) (t u : term) :
    cbn_consts_okb Σ t -> cbn_consts_okb Σ u ->
    forall i e, PTree.get i (((cbn_run_s2 X_type X t u).(cbn_st_memo)).(cbn_m_codes)) = Some e ->
      cbn_consts_okb Σ (cbn_inst_code e.(cbn_ce_inst) e.(cbn_ce_term)).
  Proof.
    intros ht hu i e hi. rewrite cbn_run_s2_codes in hi.
    destruct (cbn_key_eqb i (cbn_key_succ String2pos.xH)) eqn:E1.
    - apply cbn_key_eqb_spec in E1; subst i. rewrite PTree.gss in hi.
      injection hi as <-. cbn [cbn_ce_inst cbn_ce_term]. rewrite cbn_consts_inst_code. exact hu.
    - rewrite PTree.gso in hi by (apply cbn_key_neq_of_eqb, E1).
      destruct (cbn_key_eqb i String2pos.xH) eqn:E2.
      + apply cbn_key_eqb_spec in E2; subst i. rewrite PTree.gss in hi.
        injection hi as <-. cbn [cbn_ce_inst cbn_ce_term]. rewrite cbn_consts_inst_code. exact ht.
      + rewrite PTree.gso in hi by (apply cbn_key_neq_of_eqb, E2).
        rewrite PTree.gempty in hi. discriminate hi.
  Qed.

  (** Every entry of the start table is hygienic. *)
  Lemma cbn_run_s2_hyg (t u : term) :
    on_free_vars cbn_xpredT t -> on_free_vars cbn_xpredT u ->
    forall i e, PTree.get i (((cbn_run_s2 X_type X t u).(cbn_st_memo)).(cbn_m_codes)) = Some e ->
      on_free_vars cbn_xpredT (cbn_inst_code e.(cbn_ce_inst) e.(cbn_ce_term)).
  Proof.
    intros ht hu i e hi. rewrite cbn_run_s2_codes in hi.
    destruct (cbn_key_eqb i (cbn_key_succ String2pos.xH)) eqn:E1.
    - apply cbn_key_eqb_spec in E1; subst i. rewrite PTree.gss in hi.
      injection hi as <-. cbn [cbn_ce_inst cbn_ce_term]. rewrite cbn_hyg_inst_code. exact hu.
    - rewrite PTree.gso in hi by (apply cbn_key_neq_of_eqb, E1).
      destruct (cbn_key_eqb i String2pos.xH) eqn:E2.
      + apply cbn_key_eqb_spec in E2; subst i. rewrite PTree.gss in hi.
        injection hi as <-. cbn [cbn_ce_inst cbn_ce_term]. rewrite cbn_hyg_inst_code. exact ht.
      + rewrite PTree.gso in hi by (apply cbn_key_neq_of_eqb, E2).
        rewrite PTree.gempty in hi. discriminate hi.
  Qed.

  (** The state invariant of [cbn_machine_sound] holds of the state [cbn_run] starts in, at every
    level and under every extension [Δ]: the heap and the context map are empty. *)
  Lemma cbn_run_s2_gok (Γ : context) (nctx : nat) (Σ : global_env_ext) (Δ : context)
      (lvl : nat) (t u : term) :
    cbn_consts_okb Σ t -> cbn_consts_okb Σ u -> on_free_vars cbn_xpredT t ->
      on_free_vars cbn_xpredT u ->
    cbn_gok X_type X Γ nctx Σ Δ lvl xH (cbn_run_ghost t u) (cbn_run_s2 X_type X t u).
  Proof.
    intros ht hu hht hhu. split.
    - apply cbn_run_s2_state_ok.
    - apply cbn_run_s2_nofwd.
    - intros a cl h. unfold cbn_heap_get in h. rewrite cbn_run_s2_heap, cbn_bh_get_holes in h.
      discriminate h.
    - intros a tm h. discriminate h.
    - intros j a h. rewrite cbn_run_s2_gam_empty, PTree.gempty in h. discriminate h.
    - split; [apply cbn_run_s2_memo_inv|]. split; [apply cbn_run_s2_memo_ok|]. split.
      + intros i e hi. exact hi.
      + split; [exact (cbn_run_s2_consts_okb Σ t u ht hu)|].
        intros _. exact (cbn_run_s2_hyg t u hht hhu).
    - intros _ a tm h. discriminate h.
  Qed.

  (** The two root codes are in the ghost's table. *)
  Lemma cbn_run_c1_gcok (t u : term) :
    PCUICCallByNeedEtaSoundEval.cbn_cok (cbn_run_ghost t u) (cbn_run_c1 X_type X t).
  Proof.
    exists (cbn_mkEntry t [] (cbn_wf_term_univs X_type X t)). split.
    - exact (cbn_run_c1_in_table X_type X t u).
    - exact (cbn_run_c1_code_inv X_type X t).
  Qed.

  Lemma cbn_run_c2_gcok (t u : term) :
    PCUICCallByNeedEtaSoundEval.cbn_cok (cbn_run_ghost t u) (cbn_run_c2 X_type X t u).
  Proof.
    exists (cbn_mkEntry u [] (cbn_wf_term_univs X_type X u)). split.
    - exact (cbn_run_c2_in_table X_type X t u).
    - exact (cbn_run_c2_code_inv X_type X t u).
  Qed.

  (** A suspension of a code in the empty environment, at the call's own level, reads as the
    code itself, under any ghost. *)
  Lemma cbn_g_susp_env_empty (nctx : nat) (G : cbn_ghost) (t : term) :
    cbn_g_susp nctx nctx G cbn_env_empty t t.
  Proof.
    pose proof (cbn_g_susp_intro nctx nctx G [] 0 0 t [] (cbn_g_slots_nil nctx nctx G) eq_refl) as
      h.
    rewrite subst_empty, Nat.sub_diag in h. cbn [Nat.add] in h. rewrite lift0_id in h.
    exact h.
  Qed.

  Lemma cbn_run_c1_g_susp (nctx : nat) (t u : term) :
    cbn_g_susp nctx nctx (cbn_run_ghost t u) cbn_env_empty (cbn_run_c1 X_type X t).(cbn_c_term) t.
  Proof. rewrite cbn_run_c1_term. apply cbn_g_susp_env_empty. Qed.

  Lemma cbn_run_c2_g_susp (nctx : nat) (t u : term) :
    cbn_g_susp nctx nctx (cbn_run_ghost t u) cbn_env_empty (cbn_run_c2 X_type X t u).(cbn_c_term) u.
  Proof. rewrite cbn_run_c2_term. apply cbn_g_susp_env_empty. Qed.

End RunStart.

(** ** The comparison's invariant: [cbn_gok] at the master level

  [cbn_minv L Q lo G s]: the comparison is at logical level [L], the master level is [Q], and
  the state satisfies [cbn_gok] at [Q] with the junk context, and [cbn_hwf Q]. The roots the
  comparison holds are described by their readings at [Q] in each lemma, as [lift0 (Q - L)]
  of a logical reading. *)

Section Master.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat) (Σ : global_env_ext).
  Context (wfΣ : wfE Σ) (hΣ : abstract_env_ext_rel X Σ).
  Context (hnctx : nctx = #|Γ|) (hΓ : is_closed_context Γ).
  Context (hcio : forall j decl b, nth_error Γ j = Some decl -> decl.(decl_body) = Some b ->
                    PCUICCallByNeedEtaSoundHook.cbn_consts_okb Σ b).

  Record cbn_minv (L Q : nat) (lo : positive) (G : cbn_ghost) (s : cbn_state) : Prop := cbn_mkMinv {
    cbn_mi_L : nctx <= L;
    cbn_mi_Q : L <= Q;
    cbn_mi_gok : cbn_gok X_type X Γ nctx Σ (cbn_jctx (Q - nctx)) Q lo G s;
    cbn_mi_hwf : cbn_hwf Q s }.

  (** *** The machine at the master level

    [cbn_machine_sound] gives the reading of the result, and [cbn_machine_hwf_holds], at
    [#|Γ| <= nctx] from [hnctx], keeps [cbn_hwf Q]. *)

  Lemma cbn_whnf_master d L Q lo G e c stk sts tc rs s v rs' s' :
    cbn_minv L Q lo G s -> Forall (cbn_rwf Q) rs ->
    cbn_g_susp nctx Q G e c.(cbn_c_term) tc -> PCUICCallByNeedEtaSoundEval.cbn_cok G c ->
    cbn_g_slots nctx Q G stk sts ->
    cbn_whnf X_type X Γ nctx d e c stk rs s = CbnCOk (v, rs', s') ->
    exists lo' G' u, cbn_minv L Q lo' G' s' /\ Forall (cbn_rwf Q) rs' /\ cbn_vwf Q v
      /\ cbn_gren nctx Q G G' rs rs' /\ cbn_g_value nctx Q G' v u
      /\ cbn_cred Γ Σ (cbn_jctx (Q - nctx)) (mkApps tc sts) u.
  Proof.
    intros [hL hQ hok hw] hrs hs hc hstk he.
    assert (hlen : #|cbn_jctx (Q - nctx)| = Q - nctx) by apply cbn_jctx_length.
    destruct (cbn_machine_sound X_type X Γ nctx Σ (cbn_jctx (Q - nctx)) Q wfΣ hΣ hlen hnctx
                ltac:(lia) hcio d) as (_ & _ & hW & _ & _).
    destruct (hW lo G e c stk sts tc rs s v rs' s' hok hs hc hstk he)
      as (lo' & G' & u & hren & hok' & hv & hr).
    destruct (cbn_machine_hwf_holds X_type X Γ nctx ltac:(lia) d Q ltac:(lia))
      as (_ & _ & hWf & _ & _).
    destruct (hWf e c stk rs s v rs' s' he hw hrs) as (hw' & hrs' & hvw).
    exists lo', G', u. split; [constructor; assumption|]. split; [exact hrs'|].
    split; [exact hvw|]. split; [exact hren|]. split; [exact hv|exact hr].
  Qed.

  Lemma cbn_eval_slot_master d L Q lo G x stk sts tx rs s v rs' s' :
    cbn_minv L Q lo G s -> Forall (cbn_rwf Q) rs ->
    cbn_g_slot nctx Q G x tx -> cbn_g_slots nctx Q G stk sts ->
    cbn_eval_slot X_type X Γ nctx d x stk rs s = CbnCOk (v, rs', s') ->
    exists lo' G' u, cbn_minv L Q lo' G' s' /\ Forall (cbn_rwf Q) rs' /\ cbn_vwf Q v
      /\ cbn_gren nctx Q G G' rs rs' /\ cbn_g_value nctx Q G' v u
      /\ cbn_cred Γ Σ (cbn_jctx (Q - nctx)) (mkApps tx sts) u.
  Proof.
    intros [hL hQ hok hw] hrs hx hstk he.
    assert (hlen : #|cbn_jctx (Q - nctx)| = Q - nctx) by apply cbn_jctx_length.
    destruct (cbn_machine_sound X_type X Γ nctx Σ (cbn_jctx (Q - nctx)) Q wfΣ hΣ hlen hnctx
                ltac:(lia) hcio d) as (_ & hE & _ & _ & _).
    destruct (hE lo G x stk sts tx rs s v rs' s' hok hx hstk he)
      as (lo' & G' & u & hren & hok' & hv & hr).
    destruct (cbn_machine_hwf_holds X_type X Γ nctx ltac:(lia) d Q ltac:(lia))
      as (_ & hWf & _ & _ & _).
    destruct (hWf x stk rs s v rs' s' he hw hrs) as (hw' & hrs' & hvw).
    exists lo', G', u. split; [constructor; assumption|]. split; [exact hrs'|].
    split; [exact hvw|]. split; [exact hren|]. split; [exact hv|exact hr].
  Qed.

  (** *** From the master level to the logical level

    A master reduction from a lifted logical reading is a lifted logical reduction, in any
    assumption context of the logical length. *)
  Lemma cbn_cred_unlift L Q v u :
    nctx <= L -> L <= Q -> on_free_vars cbn_xpredT v ->
    cbn_cred Γ Σ (cbn_jctx (Q - nctx)) (lift0 (Q - L) v) u ->
    exists u', u = lift0 (Q - L) u'
      /\ forall Δ, #|Δ| = L - nctx -> ∥ red Σ (Γ ,,, Δ) v u' ∥.
  Proof using wfΣ hΓ.
    clear hnctx. intros hL hQ hv [hr].
    replace (Q - nctx) with ((Q - L) + (L - nctx)) in hr by lia.
    rewrite cbn_jctx_add, app_context_assoc in hr.
    pose proof (cbn_red_unlift Σ wfΣ (Γ ,,, cbn_jctx (L - nctx)) (cbn_jctx (Q - L)) v u
                  (cbn_master_ctx_xpredT Γ hΓ (L - nctx)) hv) as hU.
    rewrite cbn_jctx_length in hU.
    destruct (hU hr) as (u' & hu & [hr']).
    exists u'. split; [exact hu|].
    intros Δ hΔ. constructor.
    exact (cbn_red_assum_irrel Σ Γ (cbn_jctx (L - nctx)) Δ v u'
             ltac:(rewrite cbn_jctx_length; lia) (cbn_jctx_assum _) hr').
  Qed.

  (** The start of a run is an instance of [cbn_minv]: [L = Q = nctx], an empty heap. It is the
    satisfying instance of [cbn_minv] at a start state that [cbn_gok] describes. *)
  Lemma cbn_minv_start lo G s :
    cbn_gok X_type X Γ nctx Σ [] nctx lo G s ->
    (forall a cl, cbn_heap_get a s = Some cl -> False) ->
    cbn_minv nctx nctx lo G s.
  Proof.
    intros hok hempty. split; [lia|lia| |].
    - rewrite Nat.sub_diag. exact hok.
    - intros a cl ha. destruct (hempty a cl ha).
  Qed.

  (** A step that leaves heap, next address, context map and memo alone keeps [cbn_minv]. *)
  Lemma cbn_minv_same L Q lo G s s' :
    cbn_minv L Q lo G s -> s'.(cbn_st_heap) = s.(cbn_st_heap) ->
      s'.(cbn_st_next) = s.(cbn_st_next) ->
    s'.(cbn_st_gam) = s.(cbn_st_gam) -> s'.(cbn_st_memo) = s.(cbn_st_memo) -> cbn_minv L Q lo G s'.
  Proof.
    intros [hL hQ hok hw] e1 e2 e3 e4. split; [exact hL|exact hQ| |].
    - eapply cbn_gok_same; [exact hok|exact e1|exact e2|exact e3|].
      eapply cbn_mok_memo; [exact e4|exact (cbn_gk_memo _ _ _ _ _ _ _ _ _ _ hok)].
    - intros a cl ha. unfold cbn_heap_get in ha. rewrite e1 in ha. exact (hw a cl ha).
  Qed.

  (** The machine's initial state is an instance of [cbn_minv] with the empty ghost: the
    satisfying instance of [cbn_minv] at [cbn_init]. *)
  Lemma cbn_minv_init : cbn_minv nctx nctx xH
    (cbn_mkGhost (fun _ => None) (PTree.empty _)) cbn_init.
  Proof.
    split; [lia|lia| |].
    - exact (cbn_gok_init X_type X Γ nctx Σ (cbn_jctx (nctx - nctx)) nctx).
    - intros a cl h. unfold cbn_heap_get, cbn_init in h. cbn [cbn_st_heap] in h.
      rewrite cbn_bh_get_holes in h. discriminate.
  Qed.

  (** *** The interface of the read-back

    A read-back at the logical level [L] of a suspension whose master reading is the lifted
    logical term [v] is a reduct of [v], and leaves [cbn_minv] alone. Its instance:
    [cbn_rb_instance] below, a real call that returns. *)
  Definition cbn_rb_case (d : cbn_fuel) (L Q : nat) (lo : positive) (G : cbn_ghost) (e : cbn_env)
      (t v : term) (s : cbn_state) : Prop :=
    cbn_minv L Q lo G s -> on_free_vars cbn_xpredT t -> on_free_vars cbn_xpredT v ->
    cbn_g_susp nctx Q G e t (lift0 (Q - L) v) ->
    forall u s', cbn_rb_susp nctx d L e t s = CbnCOk (u, s') ->
      cbn_minv L Q lo G s' /\ forall Δ, #|Δ| = L - nctx -> ∥ red Σ (Γ ,,, Δ) v u ∥.

  Definition cbn_rb_sound : Prop := forall d L Q lo G e t v s, cbn_rb_case d L Q lo G e t v s.
End Master.

(** ** Satisfying instances of the named hypotheses

  The section hypotheses of [Shift], [Raise] and [Master]: [nctx <= lvl], [wfΣ], [hΣ],
  [hnctx], [hΓ], [hhyg], [hcio]. For the empty context and for a context of one assumption
  ([cbn_level_ctx_instance_nil], [cbn_level_ctx_instance_one]); for any well-formed context,
  [PCUICCallByNeedEtaSoundHookFrame.cbn_eval_section_instance]; [wfΣ] and [hΣ] for every abstract
  environment, [PCUICCallByNeedEtaSoundEval.cbn_eval_env_instance]. The interface [cbn_rb_sound]:
  [cbn_rb_instance] below. *)

Definition cbn_inst_na : aname := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition cbn_inst_Γ : context := [vass cbn_inst_na (tSort sProp)].

(** The satisfying instance of the context hypotheses at the empty context. *)
Lemma cbn_level_ctx_instance_nil (Σ : global_env_ext) :
  0 <= 0 /\ 0 = #|([] : context)| /\ is_closed_context [] /\ cbn_ctx_hyg []
  /\ (forall j decl b, nth_error ([] : context) j = Some decl -> decl.(decl_body) = Some b ->
        PCUICCallByNeedEtaSoundHook.cbn_consts_okb Σ b).
Proof.
  split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
  split; intros j decl b h; destruct j; discriminate h.
Qed.

Lemma cbn_inst_Γ_nobody j decl b :
  nth_error cbn_inst_Γ j = Some decl -> decl.(decl_body) = Some b -> False.
Proof.
  destruct j as [|j]; cbn; intros h hb; [injection h as <-; discriminate hb|].
  destruct j; discriminate h.
Qed.

(** The satisfying instance of the context hypotheses at a context of one assumption. *)
Lemma cbn_level_ctx_instance_one (Σ : global_env_ext) :
  1 <= 1 /\ 1 = #|cbn_inst_Γ| /\ is_closed_context cbn_inst_Γ /\ cbn_ctx_hyg cbn_inst_Γ
  /\ (forall j decl b, nth_error cbn_inst_Γ j = Some decl -> decl.(decl_body) = Some b ->
        PCUICCallByNeedEtaSoundHook.cbn_consts_okb Σ b).
Proof.
  split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
  split; intros j decl b h hb; destruct (cbn_inst_Γ_nobody j decl b h hb).
Qed.

Fixpoint cbn_fuel_n (n : nat) : cbn_fuel :=
  match n with O => CbnFO | S n => CbnFS (fun _ => cbn_fuel_n n) end.

Section Instances.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Σ : global_env_ext).

  #[local] Definition cbn_G0 : cbn_ghost := cbn_mkGhost (fun _ => None) (PTree.empty _).

  (** The satisfying instance of [cbn_rb_case] (the interface [cbn_rb_sound]) at a real call that
    returns: the read-back of a sort in the empty environment, at the start state. *)
  Lemma cbn_rb_instance :
    (exists s', cbn_rb_susp 0 (cbn_fuel_n 1) 0 cbn_env_empty (tSort sProp) cbn_init
      = CbnCOk (tSort sProp, s'))
    /\ cbn_minv X_type X [] 0 Σ 0 0 xH cbn_G0 cbn_init
    /\ on_free_vars cbn_xpredT (tSort sProp)
    /\ cbn_g_susp 0 0 cbn_G0 cbn_env_empty (tSort sProp) (lift0 (0 - 0) (tSort sProp))
    /\ cbn_rb_case X_type X [] 0 Σ (cbn_fuel_n 1) 0 0 xH cbn_G0 cbn_env_empty (tSort sProp)
      (tSort sProp) cbn_init.
  Proof.
    split.
    { destruct (cbn_rb_susp 0 (cbn_fuel_n 1) 0 cbn_env_empty (tSort sProp) cbn_init) as
      [[u s']|w] eqn:E;
        pose proof E as Ec; vm_compute in Ec; try discriminate Ec.
      injection Ec as hu _. subst u. exists s'. reflexivity. }
    split; [exact (cbn_minv_init X_type X [] 0 Σ eq_refl)|]. split; [reflexivity|].
    split; [exact (cbn_g_susp_env_empty 0 cbn_G0 (tSort sProp))|].
    intros hm _ _ _ u s' E. pose proof E as Ec. vm_compute in Ec.
    injection Ec as hu hs. subst u s'. split.
    - eapply cbn_minv_same; [exact hm|reflexivity|reflexivity|reflexivity|reflexivity].
    - intros Δ _. constructor. apply refl_red.
  Qed.

End Instances.
