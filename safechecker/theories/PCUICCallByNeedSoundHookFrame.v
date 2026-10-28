(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require CanonicalTries.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping
  PCUICOnFreeVars PCUICReduction PCUICConfluence.
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

(** * The ghost reading cannot change level: the shift is false (BET-298, step 3b)

  The comparison crosses binders: its lambda, product and match rows compare at [S lvl] or
  [lvl + n]. Restating it on the ghost reading of [PCUICCallByNeedSoundEval] would need [gok]
  at [lvl] to give [gok] at [S lvl] for the same state, with every ghost term lifted by one:
  [gok lvl G s -> gok (S lvl) (gshift 1 G) s]. That is false ([ghost_shift_false]).

  The cause is a cell left in the heap by an earlier binder. The lambda row allocates
  [CDone (VNeu (NVar lvl) [])] for its fresh variable, and the cell stays after the
  comparison comes back out of the binder (no collection runs unless [stress] is set or
  [st_room] is spent). At level [lvl] the cell reads [tRel (lvl - S lvl)], which is [tRel 0]
  by the truncation of [nat] subtraction; at [S lvl] it reads [tRel (S lvl - S lvl)], which is
  [tRel 0] again; but the lifted ghost is [tRel 1], and [tRel 1] does not reduce to [tRel 0].
  The machine reaches this state: in [Γ = []], comparing [c (fun y => y) (fun y => y)] with
  [c (fun y => (fun w => w) y) (fun y => (fun w => w) y)] for a constructor [c], the first
  pair of arguments takes the lambda row at level 0 and leaves its fresh variable in the
  heap; the second pair takes the lambda row at level 0 again and needs [gok] at level 1.

  No map on ghost terms repairs the shift ([ghost_map_false]). At level 1 a cell
  [VNeu (NVar 0)] (the genuine variable at level 0) and a stale cell [VNeu (NVar 1)] both read
  [tRel 0], so both may carry the ghost [tRel 0]. At level 2 the first reads [tRel 1] and the
  second [tRel 0], so the image of [tRel 0] under the map would have to reduce to both, which
  confluence forbids. The lemma asks the image to be a term of the level-2 context (as every
  level shift gives); for an image outside the context, [red_confluence] does not apply, and
  the same conclusion is left as this argument. [red_confluence] brings
  [functional_extensionality_dep] into the assumptions of [ghost_map_false]; those of
  [ghost_shift_false] are the Rocq primitives and [guard_checking] only.

  So the level of [gok] cannot move down while a stale cell exists, and a whole-heap scoping
  clause ([heap_wf lvl] of [PCUICCallByNeedSoundConv]) is false at the comparison's level for
  the same reason. [env_reads] does not help: it is a hypothesis of [case_cong_sound] and
  [case_branches_sound], and [env_reads_intro], the only way to obtain it, needs that false
  [heap_wf lvl] and is called nowhere. *)

Section GhostShiftCounterexample.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).

  (** Every ghost term lifted by [n]; every ghost term mapped by [φ]. *)
  Definition gshift (n : nat) (G : ghost) : ghost :=
    mkGhost (fun a => option_map (lift0 n) (G a)) (gc G).

  Definition gmap (φ : term -> term) (G : ghost) : ghost :=
    mkGhost (fun a => option_map φ (G a)) (gc G).

  (** A variable without a body reduces only to itself. *)
  Lemma red_rel_nobody (Σ : global_env_ext) (Ξ : context) (i : nat) (v : term) :
    (forall b, option_map decl_body (nth_error Ξ i) <> Some (Some b)) ->
    red Σ Ξ (tRel i) v -> v = tRel i.
  Proof.
    intros hnb hr. remember (tRel i) as x eqn:hx. revert hx.
    induction hr as [x y h|x|x y z h1 ih1 h2 ih2]; intros hx; subst x.
    - inversion h; subst; exfalso.
      + eapply hnb. eassumption.
      + match goal with H : mkApps _ ?args = tRel _ |- _ =>
          destruct args as [|a args _] using rev_ind;
            [discriminate H|rewrite mkApps_app in H; discriminate H]
        end.
    - reflexivity.
    - specialize (ih1 eq_refl). subst y. exact (ih2 eq_refl).
  Qed.

  Definition gs_na : aname := {| binder_name := nAnon; binder_relevance := Relevant |}.
  Definition gs_d : context_decl := vass gs_na (tSort sProp).
  Definition gs_var (l : nat) : cbn_cell := CDone (VNeu (NVar l) []).

  (** The cell of the fresh variable at level [l] reads, at level [lvl], as [tRel (lvl - S l)]. *)
  Lemma g_cell_var (nctx lvl : nat) (G : ghost) (l : nat) :
    g_cell nctx lvl G (gs_var l) (tRel (lvl - S l)).
  Proof.
    unfold gs_var. constructor.
    exact (g_VNeuVar nctx lvl G l [] [] (Forall2_nil _)).
  Qed.

  Lemma g_cell_var_inv (nctx lvl : nat) (G : ghost) (l : nat) (u : term) :
    g_cell nctx lvl G (gs_var l) u -> u = tRel (lvl - S l).
  Proof.
    unfold gs_var. intros h. inversion h; subst.
    match goal with hv : g_value _ _ _ _ _ |- _ => inversion hv; subst end.
    match goal with ha : g_addrs _ [] _ |- _ => inversion ha; subst end.
    reflexivity.
  Qed.

  (** The state of the counterexample: the start state with the fresh variable of level 0. *)
  Definition gs_s1 : cbn_state := snd (alloc_now (gs_var 0) cbn_init).
  Definition gs_a1 : haddr := fst (alloc_now (gs_var 0) cbn_init).

  Lemma gs_s1_get : heap_get gs_a1 gs_s1 = Some (gs_var 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma ghost_shift_false (Σ : global_env_ext) (Δ' : context) :
    #|Δ'| = 1 ->
    ~ (forall lo G s, gok X_type X [] 0 Σ [] 0 lo G s ->
                      gok X_type X [] 0 Σ Δ' 1 lo (gshift 1 G) s).
  Proof.
    intros hl hshift.
    destruct (alloc_now_sound X_type X [] 0 Σ [] 0 eq_refl eq_refl (le_n 0) xH _ (gs_var 0)
                (tRel (0 - S 0))
                cbn_init
                (gok_init X_type X [] 0 Σ [] 0) (g_cell_var 0 0 _ 0))
      as (G1 & _ & hok1 & ha1).
    pose proof (hshift _ _ _ hok1) as hok2.
    destruct (gk_cells _ _ _ _ _ _ _ _ _ _ hok2 gs_a1 (gs_var 0) gs_s1_get)
      as (t & ht & [hb|(u & hu & [hr])]); [discriminate hb|].
    cbn [gshift gm] in ht. unfold gs_a1 in ht. rewrite ha1 in ht. cbn in ht.
    injection ht as <-.
    apply g_cell_var_inv in hu. subst u.
    apply red_rel_nobody in hr.
    - discriminate hr.
    - intros b. rewrite app_context_nil_l.
      destruct (nth_error Δ' 1) eqn:E; [|discriminate].
      apply nth_error_Some_length in E. lia.
  Qed.

  (** The state of the second counterexample, at level 1: the genuine variable of level 0 and
    a stale variable of level 1, the cell a binder of an earlier excursion to level 2 left. *)
  Definition gs_s2 : cbn_state := snd (alloc_now (gs_var 1) gs_s1).
  Definition gs_a2 : haddr := fst (alloc_now (gs_var 1) gs_s1).

  Lemma gs_s2_get1 : heap_get gs_a1 gs_s2 = Some (gs_var 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma gs_s2_get2 : heap_get gs_a2 gs_s2 = Some (gs_var 1).
  Proof. vm_compute. reflexivity. Qed.

  (** At level 1 both cells may carry the ghost [tRel 0]; no map [φ] of the ghost terms whose
    image of [tRel 0] is a term of the level-2 context gives [gok] at level 2. *)
  Lemma ghost_map_false (Σ : global_env_ext) (wfΣ : wf Σ) :
    exists lo G, gok X_type X [] 0 Σ [gs_d] 1 lo G gs_s2
      /\ forall φ, on_free_vars (shiftnP 2 ssrbool.xpred0) (φ (tRel 0)) ->
           ~ gok X_type X [] 0 Σ [gs_d; gs_d] 2 lo (gmap φ G) gs_s2.
  Proof.
    destruct (alloc_now_sound X_type X [] 0 Σ [gs_d] 1 eq_refl eq_refl (le_S _ _ (le_n 0)) xH
                _ (gs_var 0) (tRel (1 - S 0)) cbn_init
                (gok_init X_type X [] 0 Σ [gs_d] 1) (g_cell_var 0 1 _ 0))
      as (G1 & _ & hok1 & ha1).
    destruct (alloc_now_sound X_type X [] 0 Σ [gs_d] 1 eq_refl eq_refl (le_S _ _ (le_n 0)) xH
                G1 (gs_var 1) (tRel (1 - S 1)) gs_s1 hok1 (g_cell_var 0 1 G1 1))
      as (G2 & hx & hok2 & ha2).
    exists xH, G2. split; [exact hok2|].
    intros φ hop hok.
    destruct (gk_cells _ _ _ _ _ _ _ _ _ _ hok gs_a1 (gs_var 0) gs_s2_get1)
      as (t1 & ht1 & [hb|(u1 & hu1 & [hr1])]); [discriminate hb|].
    destruct (gk_cells _ _ _ _ _ _ _ _ _ _ hok gs_a2 (gs_var 1) gs_s2_get2)
      as (t2 & ht2 & [hb|(u2 & hu2 & [hr2])]); [discriminate hb|].
    cbn [gmap gm] in ht1, ht2. unfold gs_a1 in ht1. unfold gs_a2 in ht2.
    rewrite (gx_map _ _ hx _ _ ha1) in ht1. rewrite ha2 in ht2. cbn in ht1, ht2.
    injection ht1 as <-. injection ht2 as <-.
    apply g_cell_var_inv in hu1. apply g_cell_var_inv in hu2. subst u1 u2.
    rewrite app_context_nil_l in hr1, hr2.
    assert (hcl : on_free_vars_ctx ssrbool.xpred0 [gs_d; gs_d]) by reflexivity.
    destruct (@red_confluence _ Σ wfΣ (exist [gs_d; gs_d] hcl) (exist (φ (tRel 0)) hop) _ _
                hr1 hr2)
      as (v & hv1 & hv2).
    apply red_rel_nobody in hv1; [|intros b; cbn; discriminate].
    apply red_rel_nobody in hv2; [|intros b; cbn; discriminate].
    rewrite hv1 in hv2. cbn in hv2. discriminate hv2.
  Qed.
End GhostShiftCounterexample.
