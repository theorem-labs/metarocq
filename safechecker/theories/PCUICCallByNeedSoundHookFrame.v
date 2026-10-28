(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require CanonicalTries.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping
  PCUICOnFreeVars PCUICReduction PCUICConfluence PCUICClosed PCUICClosedTyp.
From MetaRocq.SafeChecker Require Import PCUICWfEnv PCUICCallByNeed PCUICCallByNeedSound
  PCUICCallByNeedSoundGC PCUICCallByNeedSoundCtx PCUICCallByNeedSoundMemo
  PCUICCallByNeedSoundHook PCUICCallByNeedSoundEval PCUICCallByNeedSoundLevel.
From MetaRocq.PCUIC Require Import PCUICWellScopedCumulativity.

Import CanonicalTries.

Local Notation xpredT := (fun _ : nat => true) (only parsing).

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

(** * The old evaluator seam of the comparison was false at the fuel [cbn_run] uses

  The comparison was first proved against two seam hypotheses, [slot_seam] and [term_seam],
  since deleted from [PCUICCallByNeedSoundConv] and kept below as [old_slot_seam] and
  [old_term_seam]. They read the comparison's inputs with the heap-following [repr_*] and
  promised, of every answer, that the caller's roots keep their [repr] reading ([root_pres])
  and that the state keeps [old_cok], whose [gam_ok] asks every cell of the context map to
  stand, under [repr], for exactly the context entry it was made for.
  Forcing a cell writes its value back, and [repr] reads a forced cell as that value: a
  reduct of what it stood for, not the same term. So neither promise survives a single
  evaluation that forces a context cell.

  The run below is [cbn_run]'s own first [conv_term], at [cbn_depth], in
  [Γ = [x := (fun n : nat => n) O : nat]] with [t = x] and [u = fun n : nat => n]. The
  start state satisfies [old_cok] ([cok_run_s2]). [whnf] of [x] allocates the context cell of
  [x] at address 1, records it in [st_gam], forces it and writes back [VCon O []]; the
  comparison then answers [false] (constructor against lambda: no rule). [gam_ok] of the
  final state would need address 1 to stand under [repr] for the body
  [(fun n : nat => n) O]; it stands for [O]. [old_term_seam] promises [old_cok] of the final
  state, so it is false ([term_seam_false]). The same run through [conv_slot] on two inline
  slots refutes [old_slot_seam] ([slot_seam_false]). Nothing in the counterexample is
  ill-typed; and it is not a defect of the machine, which is sound here: it is a defect of the
  seam's heap-following invariant. The comparison is now proved on ghost readings instead
  ([spec_all_holds] in [PCUICCallByNeedSoundConv]), as the evaluator already was. *)

Section SeamCounterexample.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Σ : global_env_ext).

  (** The REFUTED definitions: the old [cok], [term_seam] and [slot_seam] of
    [PCUICCallByNeedSoundConv], deleted there and copied here under [old_] names solely so
    that the counterexamples below stay checkable. No result of the development depends on
    them. *)
  Definition old_cok (Γ : context) (nctx lvl : nat) (s : cbn_state) : Prop :=
    (exists lo : positive, state_ok lo s)
    /\ heap_nofwd s.(st_heap)
    /\ (forall l : nat, gam_ok Γ nctx l s)
    /\ memo_ok X_type X s
    /\ memo_inv X_type X s.

  Definition old_slot_seam (Γ : context) (nctx : nat) (stress : bool) (d : cbn_fuel) : Prop :=
    forall (lvl : nat) (pb : conv_pb) (Ξ : context) (x1 x2 : cbn_slot)
      (rs : list root) (s : cbn_state) (b : bool) (rs' : list root) (s' : cbn_state),
      old_cok Γ nctx lvl s -> #|Ξ| = lvl -> is_closed_context Ξ -> nctx <= lvl ->
      conv_slot X_type X Γ nctx stress d lvl pb x1 x2 rs s = COk (b, rs', s') ->
      Forall2 (root_pres nctx (s.(st_heap)) (s'.(st_heap))) rs rs'
      /\ old_cok Γ nctx lvl s'
      /\ (b = true ->
          forall t1 t2 : term,
            repr_slot nctx (s.(st_heap)) lvl x1 t1 ->
            repr_slot nctx (s.(st_heap)) lvl x2 t2 ->
            is_open_term Ξ t1 -> is_open_term Ξ t2 ->
            ∥ Σ ;;; Ξ ⊢ t1 ≤[pb] t2 ∥).

  Definition old_term_seam (Γ : context) (nctx : nat) (stress : bool) (d : cbn_fuel) : Prop :=
    forall (lvl : nat) (pb : conv_pb) (Ξ : context) (e1 : cbn_env) (c1 : code)
      (e2 : cbn_env) (c2 : code) (rs : list root) (s : cbn_state) (b : bool)
      (rs' : list root) (s' : cbn_state),
      old_cok Γ nctx lvl s -> #|Ξ| = lvl -> is_closed_context Ξ -> nctx <= lvl ->
      conv_term X_type X Γ nctx stress d lvl pb e1 c1 e2 c2 rs s = COk (b, rs', s') ->
      Forall2 (root_pres nctx (s.(st_heap)) (s'.(st_heap))) rs rs'
      /\ old_cok Γ nctx lvl s'
      /\ (b = true ->
          forall u1 u2 : term,
            repr_susp nctx (s.(st_heap)) lvl e1 (c1.(c_term)) u1 ->
            repr_susp nctx (s.(st_heap)) lvl e2 (c2.(c_term)) u2 ->
            is_open_term Ξ u1 -> is_open_term Ξ u2 ->
            ∥ Σ ;;; Ξ ⊢ u1 ≤[pb] u2 ∥).

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
    old_cok Γ nctx lvl (run_s2 X_type X t u).
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
    ~ old_cok sc_Γ 1 1 s.
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

  Lemma term_seam_false : ~ old_term_seam sc_Γ 1 false cbn_depth.
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

  Lemma slot_seam_false : ~ old_slot_seam sc_Γ 1 false cbn_depth.
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

  So the level of [gok] cannot move down while a stale cell exists. The old comparison's
  whole-heap scoping clause [heap_wf lvl] (since deleted from [PCUICCallByNeedSoundConv])
  held on the empty start heap ([run_s2_heap]); the claim that it then FAILS is an ARGUMENT,
  not a Coq result: once a fresh-variable cell [CDone (VNeu (NVar lvl) [])] outlives its
  binder and the comparison is back at level [lvl], [value_wf] would need [lvl < lvl]. That
  such a state is reachable is the run described above, not formalized. The old
  [case_cong_sound] and [case_branches_sound] rested on [env_reads], whose only introduction
  needed [heap_wf lvl] and was called nowhere; all of these are deleted, and the comparison's
  replacement keeps scoping per master level in [minv] ([PCUICCallByNeedSoundLevel]). *)

Section GhostShiftCounterexample.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).

  (** Every ghost term mapped by [φ]; [gshift] ([PCUICCallByNeedSoundLevel]) lifts them. *)

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
      (* Every case but [red_rel] has an application spine on the left (with primitive
         operations, more than one such constructor exists), so one tactic covers them all. *)
      all: first
        [ eapply hnb; eassumption
        | match goal with H : mkApps _ ?args = tRel _ |- _ =>
            destruct args as [|a args _] using rev_ind;
              [discriminate H|rewrite mkApps_app in H; discriminate H]
          end ].
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
                (gok_init X_type X [] 0 Σ [] 0) (g_cell_var 0 0 _ 0) (fun _ => eq_refl))
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
                (gok_init X_type X [] 0 Σ [gs_d] 1) (g_cell_var 0 1 _ 0) (fun _ => eq_refl))
      as (G1 & _ & hok1 & ha1).
    destruct (alloc_now_sound X_type X [] 0 Σ [gs_d] 1 eq_refl eq_refl (le_S _ _ (le_n 0)) xH
                G1 (gs_var 1) (tRel (1 - S 1)) gs_s1 hok1 (g_cell_var 0 1 G1 1)
                (fun _ => eq_refl))
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
