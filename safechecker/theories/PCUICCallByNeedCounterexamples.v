(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require CanonicalTries.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping
  PCUICOnFreeVars PCUICReduction PCUICConfluence.
From MetaRocq.SafeChecker Require Import PCUICWfEnv PCUICCallByNeed PCUICCallByNeedSound
  PCUICCallByNeedSoundGC PCUICCallByNeedSoundCtx PCUICCallByNeedSoundMemo
  PCUICCallByNeedSoundEval PCUICCallByNeedSoundLevel PCUICCallByNeedSoundConv.
From MetaRocq.PCUIC Require Import PCUICWellScopedCumulativity.

Import CanonicalTries.

Local Notation cbn_xpredT := (fun _ : nat => true) (only parsing).

(** * Counterexamples to natural invariants of the call-by-need machine

  The soundness proof of the call-by-need fast path ([PCUICCallByNeedSoundHookProof]) reads
  every machine structure through a ghost map ([cbn_g_value] and its companions of
  [PCUICCallByNeedSoundEval]), and keeps the ghost at a master level
  ([PCUICCallByNeedSoundLevel]). Two simpler designs look natural and are false for this
  machine. This file proves that they are false, so that the reasons for the ghost-reading
  design can be checked. No result of the development depends on this file, and nothing on
  the path of [PCUICTypeChecker.convert] imports it.

  - Reading the heap directly. [repr_*] below reads a structure by following its addresses
    through the heap, and [cbn_old_cok] asks that every cell of the context map stand, under
    [repr], for the context entry it was made for. Forcing a cell writes its value back, and
    [repr] reads a forced cell as that value: a reduct of what it stood for, not the same
    term. So a comparison that promises [cbn_old_cok] of its final state is false
    ([cbn_term_seam_false], [cbn_slot_seam_false]).
  - Moving the ghost to a deeper level. A ghost invariant at level [lvl] does not give the
    same invariant at [S lvl] with the ghost terms lifted ([cbn_ghost_shift_false]), and no map
    on ghost terms repairs this ([cbn_ghost_map_false]).
  - Ghost terms without a hygiene condition. Red weakening, which every change of level
    needs, fails for a term with free variables inside a branch context
    ([cbn_red_weakening_needs_hygiene]); this is why [cbn_gok] carries [cbn_gk_hyg]. *)

(** ** Reading a structure by following the heap

  [cbn_repr_value H lvl v t] reads "in heap [H], with [lvl] levels in scope, the value [v]
  stands for the term [t]". It is the relational form of the machine's read-back functions
  [cbn_rb_slot], [cbn_rb_susp] and [cbn_rb_value]. [nctx] is the length of the context the call started
  in. A cell that is being forced ([CbnCBusy]) or that the collector has moved ([CbnCFwd]) stands
  for no term. *)

Section Repr.
  Context (nctx : nat).

  Inductive cbn_repr_addr (H : cbn_bheap cbn_cell) : nat -> cbn_haddr -> term -> Prop :=
  | cbn_repr_addr_intro lvl a cl t :
      cbn_bh_get a H = Some cl -> cbn_repr_cell H lvl cl t -> cbn_repr_addr H lvl a t

  with cbn_repr_addrs (H : cbn_bheap cbn_cell) : nat -> list cbn_haddr -> list term -> Prop :=
  | cbn_repr_addrs_nil lvl : cbn_repr_addrs H lvl [] []
  | cbn_repr_addrs_cons lvl a l t ts :
      cbn_repr_addr H lvl a t -> cbn_repr_addrs H lvl l ts -> cbn_repr_addrs H lvl (a :: l) (t :: ts)

  with cbn_repr_cell (H : cbn_bheap cbn_cell) : nat -> cbn_cell -> term -> Prop :=
  | cbn_repr_cell_susp lvl vals nvals goff c t :
      cbn_repr_susp H lvl (cbn_mkEnv vals nvals goff) c.(cbn_c_term) t ->
      cbn_repr_cell H lvl (CbnCSusp vals nvals goff c) t
  | cbn_repr_cell_done lvl v t :
      cbn_repr_value H lvl v t -> cbn_repr_cell H lvl (CbnCDone v) t

  with cbn_repr_slot (H : cbn_bheap cbn_cell) : nat -> cbn_slot -> term -> Prop :=
  | cbn_repr_slot_addr lvl a t :
      cbn_repr_addr H lvl a t -> cbn_repr_slot H lvl (CbnSAddr a) t
  | cbn_repr_slot_inl lvl vals nvals goff c t :
      cbn_repr_susp H lvl (cbn_mkEnv vals nvals goff) c.(cbn_c_term) t ->
      cbn_repr_slot H lvl (CbnSInl vals nvals goff c) t

  with cbn_repr_slots (H : cbn_bheap cbn_cell) : nat -> list cbn_slot -> list term -> Prop :=
  | cbn_repr_slots_nil lvl : cbn_repr_slots H lvl [] []
  | cbn_repr_slots_cons lvl x l t ts :
      cbn_repr_slot H lvl x t -> cbn_repr_slots H lvl l ts -> cbn_repr_slots H lvl (x :: l) (t :: ts)

  (** [cbn_repr_susp H lvl e t u]: the suspension of the code [t] in the environment [e] stands
    for [u]. This is [cbn_rb_susp]'s equation, with the slots read back one by one. *)
  with cbn_repr_susp (H : cbn_bheap cbn_cell) : nat -> cbn_env -> term -> term -> Prop :=
  | cbn_repr_susp_intro lvl vals nvals goff t ts :
      cbn_repr_slots H lvl vals ts ->
      cbn_repr_susp H lvl (cbn_mkEnv vals nvals goff) t
        (subst ts 0 (lift (lvl - nctx + goff) nvals t))

  with cbn_repr_value (H : cbn_bheap cbn_cell) : nat -> cbn_value -> term -> Prop :=
  | cbn_repr_VCon lvl h sp ts :
      cbn_repr_addrs H lvl sp ts -> cbn_repr_value H lvl (CbnVCon h sp) (mkApps h ts)
  | cbn_repr_VLam lvl e c t :
      cbn_repr_susp H lvl e c.(cbn_c_term) t -> cbn_repr_value H lvl (CbnVLam e c) t
  | cbn_repr_VOpen lvl e c t :
      cbn_repr_susp H lvl e c.(cbn_c_term) t -> cbn_repr_value H lvl (CbnVOpen e c) t
  | cbn_repr_VFix lvl e c i sp mfix j h ts :
      c.(cbn_c_term) = tFix mfix j ->
      cbn_repr_susp H lvl e (tFix mfix i) h ->
      cbn_repr_addrs H lvl sp ts ->
      cbn_repr_value H lvl (CbnVFix e c i sp) (mkApps h ts)
  | cbn_repr_VStuckFix lvl e c i sp mfix j h ts :
      c.(cbn_c_term) = tFix mfix j ->
      cbn_repr_susp H lvl e (tFix mfix i) h ->
      cbn_repr_addrs H lvl sp ts ->
      cbn_repr_value H lvl (CbnVStuckFix e c i sp) (mkApps h ts)
  | cbn_repr_VNeuVar lvl l sp ts :
      cbn_repr_addrs H lvl sp ts ->
      cbn_repr_value H lvl (CbnVNeu (CbnNVar l) sp) (mkApps (tRel (lvl - S l)) ts)
  | cbn_repr_VNeuConst lvl h sp ts :
      cbn_repr_addrs H lvl sp ts ->
      cbn_repr_value H lvl (CbnVNeu (CbnNConst h) sp) (mkApps h ts)
  | cbn_repr_VStuck lvl e c sp h ts :
      cbn_repr_susp H lvl e c.(cbn_c_term) h ->
      cbn_repr_addrs H lvl sp ts ->
      cbn_repr_value H lvl (CbnVStuck e c sp) (mkApps h ts).
End Repr.

(** The context-map invariant read through [repr]: every cell [cbn_st_gam] holds for the context
  entry [j] stands, at [lvl] levels in scope, for the term that entry denotes. *)
Definition cbn_old_gam_ok (Γ : context) (nctx lvl : nat) (s : cbn_state) : Prop :=
  forall (j : nat) (a : cbn_haddr),
    PTree.get (cbn_key_of_succ_nat j) (s.(cbn_st_gam)) = Some a ->
    exists t : term, cbn_ctx_den Γ nctx lvl j = Some t /\ cbn_repr_addr nctx (s.(cbn_st_heap)) lvl a t.

(** A renamed root stands in the new heap for what the root stood for in the old heap, one
  clause per shape of root. *)
Definition cbn_old_root_pres (nctx : nat) (Hold Hnew : cbn_bheap cbn_cell) (r r' : cbn_root) : Prop :=
  match r, r' with
  | CbnRA a, CbnRA a' => forall lvl t, cbn_repr_addr nctx Hold lvl a t -> cbn_repr_addr nctx Hnew lvl a' t
  | CbnRSl x, CbnRSl x' => forall lvl t, cbn_repr_slot nctx Hold lvl x t -> cbn_repr_slot nctx Hnew lvl x' t
  | CbnRE e, CbnRE e' =>
    forall lvl tm u, cbn_repr_susp nctx Hold lvl e tm u -> cbn_repr_susp nctx Hnew lvl e' tm u
  | CbnRV v, CbnRV v' => forall lvl t, cbn_repr_value nctx Hold lvl v t -> cbn_repr_value nctx Hnew lvl v' t
  | CbnRSk l, CbnRSk l' =>
    forall lvl ts, cbn_repr_slots nctx Hold lvl l ts -> cbn_repr_slots nctx Hnew lvl l' ts
  | CbnRSp l, CbnRSp l' =>
    forall lvl ts, cbn_repr_addrs nctx Hold lvl l ts -> cbn_repr_addrs nctx Hnew lvl l' ts
  | CbnRC cl, CbnRC cl' => forall lvl t, cbn_repr_cell nctx Hold lvl cl t -> cbn_repr_cell nctx Hnew lvl cl' t
  | _, _ => False
  end.

(** ** A comparison seam on heap readings is false at the fuel [cbn_run] uses

  [cbn_old_slot_seam] and [cbn_old_term_seam] read the comparison's inputs with [repr_*] and promise,
  of every answer, that the caller's roots keep their [repr] reading ([cbn_old_root_pres]) and
  that the state keeps [cbn_old_cok].

  The run below is [cbn_run]'s own first [cbn_conv_term], at [cbn_depth], in
  [cbn_w_Γ = [x := (fun n : nat => n) O : nat]] with [cbn_w_t = x] and [cbn_w_u = fun n : nat => n]
  ([PCUICCallByNeedSoundConv]). The start state satisfies [cbn_old_cok] ([cbn_old_cok_run_s2]).
  [cbn_whnf] of [x] allocates the context cell of [x] at address 1, records it in [cbn_st_gam],
  forces it and writes back [CbnVCon O []]; the comparison then answers [false] (constructor
  against lambda: no rule). [cbn_old_gam_ok] of the final state would need address 1 to stand
  under [repr] for the body [(fun n : nat => n) O]; it stands for [O]. [cbn_old_term_seam]
  promises [cbn_old_cok] of the final state, so it is false ([cbn_term_seam_false]). The same run
  through [cbn_conv_slot] on two inline slots refutes [cbn_old_slot_seam] ([cbn_slot_seam_false]).
  Nothing in the counterexample is ill-typed, and the machine is sound here: the defect is
  in the heap-following invariant. The ghost reading does not have it: every ghost of the
  invariant [cbn_minv] still reads the forced cell as the let-body ([cbn_sc_ghost_reads_body]); the
  same run satisfies the comparison's postcondition ([PCUICCallByNeedSoundConv.cbn_witness_seam_run]). *)

Section SeamCounterexample.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Σ : global_env_ext).

  Definition cbn_old_cok (Γ : context) (nctx lvl : nat) (s : cbn_state) : Prop :=
    (exists lo : positive, cbn_state_ok lo s)
    /\ cbn_heap_nofwd s.(cbn_st_heap)
    /\ (forall l : nat, cbn_old_gam_ok Γ nctx l s)
    /\ cbn_memo_ok X_type X s
    /\ cbn_memo_inv X_type X s.

  Definition cbn_old_slot_seam (Γ : context) (nctx : nat) (d : cbn_fuel) : Prop :=
    forall (lvl : nat) (pb : conv_pb) (Ξ : context) (x1 x2 : cbn_slot)
      (rs : list cbn_root) (s : cbn_state) (b : bool) (rs' : list cbn_root) (s' : cbn_state),
      cbn_old_cok Γ nctx lvl s -> #|Ξ| = lvl -> is_closed_context Ξ -> nctx <= lvl ->
      cbn_conv_slot X_type X Γ nctx d lvl pb x1 x2 rs s = CbnCOk (b, rs', s') ->
      Forall2 (cbn_old_root_pres nctx (s.(cbn_st_heap)) (s'.(cbn_st_heap))) rs rs'
      /\ cbn_old_cok Γ nctx lvl s'
      /\ (b = true ->
          forall t1 t2 : term,
            cbn_repr_slot nctx (s.(cbn_st_heap)) lvl x1 t1 ->
            cbn_repr_slot nctx (s.(cbn_st_heap)) lvl x2 t2 ->
            is_open_term Ξ t1 -> is_open_term Ξ t2 ->
            ∥ Σ ;;; Ξ ⊢ t1 ≤[pb] t2 ∥).

  Definition cbn_old_term_seam (Γ : context) (nctx : nat) (d : cbn_fuel) : Prop :=
    forall (lvl : nat) (pb : conv_pb) (Ξ : context) (e1 : cbn_env) (c1 : cbn_code)
      (e2 : cbn_env) (c2 : cbn_code) (rs : list cbn_root) (s : cbn_state) (b : bool)
      (rs' : list cbn_root) (s' : cbn_state),
      cbn_old_cok Γ nctx lvl s -> #|Ξ| = lvl -> is_closed_context Ξ -> nctx <= lvl ->
      cbn_conv_term X_type X Γ nctx d lvl pb e1 c1 e2 c2 rs s = CbnCOk (b, rs', s') ->
      Forall2 (cbn_old_root_pres nctx (s.(cbn_st_heap)) (s'.(cbn_st_heap))) rs rs'
      /\ cbn_old_cok Γ nctx lvl s'
      /\ (b = true ->
          forall u1 u2 : term,
            cbn_repr_susp nctx (s.(cbn_st_heap)) lvl e1 (c1.(cbn_c_term)) u1 ->
            cbn_repr_susp nctx (s.(cbn_st_heap)) lvl e2 (c2.(cbn_c_term)) u2 ->
            is_open_term Ξ u1 -> is_open_term Ξ u2 ->
            ∥ Σ ;;; Ξ ⊢ u1 ≤[pb] u2 ∥).

  (** [cbn_old_cok] holds of the state every call starts in: the context map is empty there. *)
  Lemma cbn_old_cok_run_s2 (Γ : context) (nctx lvl : nat) (t u : term) :
    cbn_old_cok Γ nctx lvl (cbn_run_s2 X_type X t u).
  Proof.
    split; [exists xH; apply cbn_run_s2_state_ok|].
    split; [apply cbn_run_s2_nofwd|].
    split.
    { intros l j a h. rewrite cbn_run_s2_gam_empty, PTree.gempty in h. discriminate h. }
    split; [apply cbn_run_s2_memo_ok|apply cbn_run_s2_memo_inv].
  Qed.

  (** The run, by computation: it answers [false], and the context cell of [x] is at
    address 1 and holds [O]. *)
  Lemma cbn_sc_term_run :
    match cbn_conv_term X_type X cbn_w_Γ 1 cbn_depth 1 Conv cbn_env_empty (cbn_run_c1 X_type X cbn_w_t)
            cbn_env_empty (cbn_run_c2 X_type X cbn_w_t cbn_w_u) [] (cbn_run_s2 X_type X cbn_w_t cbn_w_u) with
    | CbnCOk (b, rs, s) =>
        b = false /\ rs = []
        /\ PTree.get (cbn_key_of_succ_nat 0) s.(cbn_st_gam) = Some (CbnHAddr 1)
        /\ cbn_heap_get (CbnHAddr 1) s = Some (CbnCDone (CbnVCon cbn_w_O []))
    | CbnCFail _ => False
    end.
  Proof. vm_compute. repeat split. Qed.

  Lemma cbn_sc_slot_run :
    match cbn_conv_slot X_type X cbn_w_Γ 1 cbn_depth 1 Conv
            (CbnSInl [] 0 0 (cbn_run_c1 X_type X cbn_w_t)) (CbnSInl [] 0 0 (cbn_run_c2 X_type X cbn_w_t cbn_w_u))
            [] (cbn_run_s2 X_type X cbn_w_t cbn_w_u) with
    | CbnCOk (_, _, s) =>
        PTree.get (cbn_key_of_succ_nat 0) s.(cbn_st_gam) = Some (CbnHAddr 1)
        /\ cbn_heap_get (CbnHAddr 1) s = Some (CbnCDone (CbnVCon cbn_w_O []))
    | CbnCFail _ => False
    end.
  Proof. vm_compute. split; reflexivity. Qed.

  (** In a state whose context map records the cell of [x] at address 1, every ghost of
    [cbn_minv] reads that cell as the let-body of [x], whatever the cell holds. *)
  Lemma cbn_sc_ghost_reads_body (s : cbn_state) :
    PTree.get (cbn_key_of_succ_nat 0) s.(cbn_st_gam) = Some (CbnHAddr 1) ->
    forall Q lo G, cbn_minv X_type X cbn_w_Γ 1 Σ 1 Q lo G s -> G (CbnHAddr 1) = Some cbn_w_body.
  Proof.
    intros hgam Q lo G [_ _ hok _].
    destruct (@cbn_gk_gam _ X_type X cbn_w_Γ 1 Σ _ _ _ _ _ hok 0 (CbnHAddr 1) hgam) as (tm & hden & hG).
    change (cbn_ctx_den cbn_w_Γ 1 Q 0) with (Some (lift0 (Q - 1 + 1) cbn_w_body)) in hden.
    assert (hl : forall n k, lift n k cbn_w_body = cbn_w_body) by reflexivity.
    rewrite hl in hden. injection hden as <-. exact hG.
  Qed.

  (** No state whose context cell of [x] holds [O] satisfies [cbn_old_cok]. *)
  Lemma cbn_sc_not_old_cok (s : cbn_state) :
    PTree.get (cbn_key_of_succ_nat 0) s.(cbn_st_gam) = Some (CbnHAddr 1) ->
    cbn_heap_get (CbnHAddr 1) s = Some (CbnCDone (CbnVCon cbn_w_O [])) ->
    ~ cbn_old_cok cbn_w_Γ 1 1 s.
  Proof.
    intros hg hh (_ & _ & hgam & _ & _).
    destruct (hgam 1 0 (CbnHAddr 1) hg) as (tm & hden & hr).
    cbn in hden. injection hden as <-.
    inversion hr as [lv a cl tm0 hget hcl]; subst.
    unfold cbn_heap_get in hh. rewrite hh in hget. injection hget as <-.
    inversion hcl; subst.
    match goal with h : cbn_repr_value _ _ _ (CbnVCon _ _) _ |- _ => inversion h; subst end.
    match goal with h : cbn_repr_addrs _ _ _ [] _ |- _ => inversion h; subst end.
    match goal with h : mkApps cbn_w_O [] = _ |- _ => cbv [mkApps cbn_w_O] in h; discriminate h end.
  Qed.

  Lemma cbn_term_seam_false : ~ cbn_old_term_seam cbn_w_Γ 1 cbn_depth.
  Proof.
    intros hseam.
    pose proof cbn_sc_term_run as hrun.
    destruct (cbn_conv_term X_type X cbn_w_Γ 1 cbn_depth 1 Conv cbn_env_empty
                (cbn_run_c1 X_type X cbn_w_t) cbn_env_empty (cbn_run_c2 X_type X cbn_w_t cbn_w_u) []
                (cbn_run_s2 X_type X cbn_w_t cbn_w_u)) as [[[b rs] s']|w] eqn:E;
      [|contradiction hrun].
    destruct hrun as (_ & _ & hg & hh).
    destruct (hseam 1 Conv cbn_w_Γ cbn_env_empty (cbn_run_c1 X_type X cbn_w_t) cbn_env_empty
                (cbn_run_c2 X_type X cbn_w_t cbn_w_u) [] (cbn_run_s2 X_type X cbn_w_t cbn_w_u) b rs s'
                (cbn_old_cok_run_s2 cbn_w_Γ 1 1 cbn_w_t cbn_w_u) eq_refl eq_refl (le_n 1) E)
      as (_ & hcok & _).
    exact (cbn_sc_not_old_cok s' hg hh hcok).
  Qed.

  Lemma cbn_slot_seam_false : ~ cbn_old_slot_seam cbn_w_Γ 1 cbn_depth.
  Proof.
    intros hseam.
    pose proof cbn_sc_slot_run as hrun.
    destruct (cbn_conv_slot X_type X cbn_w_Γ 1 cbn_depth 1 Conv
                (CbnSInl [] 0 0 (cbn_run_c1 X_type X cbn_w_t)) (CbnSInl [] 0 0 (cbn_run_c2 X_type X cbn_w_t cbn_w_u))
                [] (cbn_run_s2 X_type X cbn_w_t cbn_w_u)) as [[[b rs] s']|w] eqn:E;
      [|contradiction hrun].
    destruct hrun as [hg hh].
    destruct (hseam 1 Conv cbn_w_Γ (CbnSInl [] 0 0 (cbn_run_c1 X_type X cbn_w_t))
                (CbnSInl [] 0 0 (cbn_run_c2 X_type X cbn_w_t cbn_w_u)) [] (cbn_run_s2 X_type X cbn_w_t cbn_w_u)
                b rs s' (cbn_old_cok_run_s2 cbn_w_Γ 1 1 cbn_w_t cbn_w_u) eq_refl eq_refl (le_n 1) E)
      as (_ & hcok & _).
    exact (cbn_sc_not_old_cok s' hg hh hcok).
  Qed.

End SeamCounterexample.

(** ** The ghost reading cannot change level

  The comparison crosses binders: its lambda, product and match rows compare at [S lvl] or
  [lvl + n]. Stating it on the ghost reading of [PCUICCallByNeedSoundEval] at the current
  level would need [cbn_gok] at [lvl] to give [cbn_gok] at [S lvl] for the same state, with every
  ghost term lifted by one: [cbn_gok lvl G s -> cbn_gok (S lvl) (cbn_gshift 1 G) s]. That is false
  ([cbn_ghost_shift_false]).

  The cause is a cell left in the heap by an earlier binder. The lambda row allocates
  [CbnCDone (CbnVNeu (CbnNVar lvl) [])] for its fresh variable, and the cell stays after the
  comparison comes back out of the binder (no collection runs unless [cbn_st_room] is spent). At
  level [lvl] the cell reads [tRel (lvl - S lvl)], which is [tRel 0] by the truncation of [nat]
  subtraction; at [S lvl] it reads [tRel (S lvl - S lvl)], which is [tRel 0] again; but the
  lifted ghost is [tRel 1], and [tRel 1] does not reduce to [tRel 0].
  The machine reaches this state: in [Γ = []], comparing [c (fun y => y) (fun y => y)] with
  [c (fun y => (fun w => w) y) (fun y => (fun w => w) y)] for a constructor [c], the first
  pair of arguments takes the lambda row at level 0 and leaves its fresh variable in the
  heap; the second pair takes the lambda row at level 0 again and needs [cbn_gok] at level 1.

  No map on ghost terms repairs the shift ([cbn_ghost_map_false]). At level 1 a cell
  [CbnVNeu (CbnNVar 0)] (the genuine variable at level 0) and a stale cell [CbnVNeu (CbnNVar 1)] both read
  [tRel 0], so both may carry the ghost [tRel 0]. At level 2 the first reads [tRel 1] and the
  second [tRel 0], so the image of [tRel 0] under the map would have to reduce to both, which
  confluence forbids. The lemma asks the image to be a term of the level-2 context (as every
  level shift gives); for an image outside the context, [red_confluence] does not apply, and
  the same conclusion is left as this argument. [red_confluence] brings
  [functional_extensionality_dep] into the assumptions of [cbn_ghost_map_false].

  So the level of [cbn_gok] cannot move down while a stale cell exists. For the same reason a
  whole-heap scoping clause at the current level would fail once a fresh-variable cell
  [CbnCDone (CbnVNeu (CbnNVar lvl) [])] outlives its binder and the comparison is back at level
  [lvl]: that cell would need [lvl < lvl]. This last claim is an argument, not a Rocq
  result. The comparison therefore keeps its ghost at a master level, and its scoping per
  master level in [cbn_minv] ([PCUICCallByNeedSoundLevel]). *)

Section GhostShiftCounterexample.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).

  (** Every ghost term mapped by [φ]; [cbn_gshift] ([PCUICCallByNeedSoundLevel]) lifts them. *)

  #[local] Definition cbn_gmap (φ : term -> term) (G : cbn_ghost) : cbn_ghost :=
    cbn_mkGhost (fun a => option_map φ (G a)) (cbn_gc G).

  (** A variable without a body reduces only to itself. *)
  Lemma cbn_red_rel_nobody (Σ : global_env_ext) (Ξ : context) (i : nat) (v : term) :
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
            let l := fresh "l" in
            remember args as l eqn:Hl; clear Hl;
            destruct l as [|a l _] using rev_ind;
              [discriminate H|rewrite mkApps_app in H; discriminate H]
          end ].
    - reflexivity.
    - specialize (ih1 eq_refl). subst y. exact (ih2 eq_refl).
  Qed.

  Definition cbn_gs_na : aname := {| binder_name := nAnon; binder_relevance := Relevant |}.
  #[local] Definition cbn_gs_d : context_decl := vass cbn_gs_na (tSort sProp).
  Definition cbn_gs_var (l : nat) : cbn_cell := CbnCDone (CbnVNeu (CbnNVar l) []).

  (** The cell of the fresh variable at level [l] reads, at level [lvl], as [tRel (lvl - S l)]. *)
  Lemma cbn_g_cell_var (nctx lvl : nat) (G : cbn_ghost) (l : nat) :
    cbn_g_cell nctx lvl G (cbn_gs_var l) (tRel (lvl - S l)).
  Proof.
    unfold cbn_gs_var. constructor.
    exact (cbn_g_VNeuVar nctx lvl G l [] [] (Forall2_nil _)).
  Qed.

  Lemma cbn_g_cell_var_inv (nctx lvl : nat) (G : cbn_ghost) (l : nat) (u : term) :
    cbn_g_cell nctx lvl G (cbn_gs_var l) u -> u = tRel (lvl - S l).
  Proof.
    unfold cbn_gs_var. intros h. inversion h; subst.
    match goal with hv : cbn_g_value _ _ _ _ _ |- _ => inversion hv; subst end.
    match goal with ha : cbn_g_addrs _ [] _ |- _ => inversion ha; subst end.
    reflexivity.
  Qed.

  (** The state of the counterexample: the start state with the fresh variable of level 0. *)
  Definition cbn_gs_s1 : cbn_state := snd (cbn_alloc_now (cbn_gs_var 0) cbn_init).
  Definition cbn_gs_a1 : cbn_haddr := fst (cbn_alloc_now (cbn_gs_var 0) cbn_init).

  Lemma cbn_gs_s1_get : cbn_heap_get cbn_gs_a1 cbn_gs_s1 = Some (cbn_gs_var 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma cbn_ghost_shift_false (Σ : global_env_ext) (Δ' : context) :
    #|Δ'| = 1 ->
    ~ (forall lo G s, cbn_gok X_type X [] 0 Σ [] 0 lo G s ->
                      cbn_gok X_type X [] 0 Σ Δ' 1 lo (cbn_gshift 1 G) s).
  Proof.
    intros hl hshift.
    destruct (cbn_alloc_now_sound X_type X [] 0 Σ [] 0 eq_refl eq_refl (le_n 0) xH _ (cbn_gs_var 0)
                (tRel (0 - S 0))
                cbn_init
                (cbn_gok_init X_type X [] 0 Σ [] 0) (cbn_g_cell_var 0 0 _ 0) (fun _ => eq_refl))
      as (G1 & _ & hok1 & ha1).
    pose proof (hshift _ _ _ hok1) as hok2.
    destruct (cbn_gk_cells _ _ _ _ _ _ _ _ _ _ hok2 cbn_gs_a1 (cbn_gs_var 0) cbn_gs_s1_get)
      as (t & ht & [hb|(u & hu & [hr])]); [discriminate hb|].
    cbn [cbn_gshift cbn_gm] in ht. unfold cbn_gs_a1 in ht. rewrite ha1 in ht. cbn in ht.
    injection ht as <-.
    apply cbn_g_cell_var_inv in hu. subst u.
    apply cbn_red_rel_nobody in hr.
    - discriminate hr.
    - intros b. rewrite app_context_nil_l.
      destruct (nth_error Δ' 1) eqn:E; [|discriminate].
      apply nth_error_Some_length in E. lia.
  Qed.

  (** The state of the second counterexample, at level 1: the genuine variable of level 0 and
    a stale variable of level 1, the cell a binder of an earlier excursion to level 2 left. *)
  Definition cbn_gs_s2 : cbn_state := snd (cbn_alloc_now (cbn_gs_var 1) cbn_gs_s1).
  Definition cbn_gs_a2 : cbn_haddr := fst (cbn_alloc_now (cbn_gs_var 1) cbn_gs_s1).

  Lemma cbn_gs_s2_get1 : cbn_heap_get cbn_gs_a1 cbn_gs_s2 = Some (cbn_gs_var 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma cbn_gs_s2_get2 : cbn_heap_get cbn_gs_a2 cbn_gs_s2 = Some (cbn_gs_var 1).
  Proof. vm_compute. reflexivity. Qed.

  (** At level 1 both cells may carry the ghost [tRel 0]; no map [φ] of the ghost terms whose
    image of [tRel 0] is a term of the level-2 context gives [cbn_gok] at level 2. *)
  Lemma cbn_ghost_map_false (Σ : global_env_ext) (wfΣ : wf Σ) :
    exists lo G, cbn_gok X_type X [] 0 Σ [cbn_gs_d] 1 lo G cbn_gs_s2
      /\ forall φ, on_free_vars (shiftnP 2 ssrbool.xpred0) (φ (tRel 0)) ->
           ~ cbn_gok X_type X [] 0 Σ [cbn_gs_d; cbn_gs_d] 2 lo (cbn_gmap φ G) cbn_gs_s2.
  Proof.
    destruct (cbn_alloc_now_sound X_type X [] 0 Σ [cbn_gs_d] 1 eq_refl eq_refl (le_S _ _ (le_n 0)) xH
                _ (cbn_gs_var 0) (tRel (1 - S 0)) cbn_init
                (cbn_gok_init X_type X [] 0 Σ [cbn_gs_d] 1) (cbn_g_cell_var 0 1 _ 0) (fun _ => eq_refl))
      as (G1 & _ & hok1 & ha1).
    destruct (cbn_alloc_now_sound X_type X [] 0 Σ [cbn_gs_d] 1 eq_refl eq_refl (le_S _ _ (le_n 0)) xH
                G1 (cbn_gs_var 1) (tRel (1 - S 1)) cbn_gs_s1 hok1 (cbn_g_cell_var 0 1 G1 1)
                (fun _ => eq_refl))
      as (G2 & hx & hok2 & ha2).
    exists xH, G2. split; [exact hok2|].
    intros φ hop hok.
    destruct (cbn_gk_cells _ _ _ _ _ _ _ _ _ _ hok cbn_gs_a1 (cbn_gs_var 0) cbn_gs_s2_get1)
      as (t1 & ht1 & [hb|(u1 & hu1 & [hr1])]); [discriminate hb|].
    destruct (cbn_gk_cells _ _ _ _ _ _ _ _ _ _ hok cbn_gs_a2 (cbn_gs_var 1) cbn_gs_s2_get2)
      as (t2 & ht2 & [hb|(u2 & hu2 & [hr2])]); [discriminate hb|].
    cbn [cbn_gmap cbn_gm] in ht1, ht2. unfold cbn_gs_a1 in ht1. unfold cbn_gs_a2 in ht2.
    rewrite (cbn_gx_map _ _ hx _ _ ha1) in ht1. rewrite ha2 in ht2. cbn in ht1, ht2.
    injection ht1 as <-. injection ht2 as <-.
    apply cbn_g_cell_var_inv in hu1. apply cbn_g_cell_var_inv in hu2. subst u1 u2.
    rewrite app_context_nil_l in hr1, hr2.
    assert (hcl : on_free_vars_ctx ssrbool.xpred0 [cbn_gs_d; cbn_gs_d]) by reflexivity.
    destruct (@red_confluence _ Σ wfΣ (exist [cbn_gs_d; cbn_gs_d] hcl) (exist (φ (tRel 0)) hop) _ _
                hr1 hr2)
      as (v & hv1 & hv2).
    apply cbn_red_rel_nobody in hv1; [|intros b; cbn; discriminate].
    apply cbn_red_rel_nobody in hv2; [|intros b; cbn; discriminate].
    rewrite hv1 in hv2. cbn in hv2. discriminate hv2.
  Qed.
End GhostShiftCounterexample.

(** ** Why [cbn_gok] carries a hygiene clause: red weakening is false without it

  The comparison changes the level of [cbn_gok] by lifting every ghost term, which needs red
  weakening of every ghost term. [cbn_rw_w] below is a match whose branch context is one
  let-binding of an outer variable. [lift] leaves branch contexts alone, so [lift0 1 cbn_rw_w] is
  [cbn_rw_w] itself, while [iota_red] expands the let-body: [cbn_rw_w] reduces to [tRel 0] in a
  context of one assumption, and in a context of two its lift still reduces to [tRel 0],
  never to [lift0 1 (tRel 0)] ([cbn_red_weakening_needs_hygiene]). Without [cbn_gk_hyg], a cell
  [CbnCDone (CbnVNeu (CbnNVar 0) [])] at level 1, which reads [tRel 0], could carry the ghost
  [cbn_rw_w]; after lifting to level 2 the cell reads [tRel 1] and the lifted ghost does not
  reduce to it. [cbn_rw_w] fails the hygiene test ([cbn_rw_w_unhygienic]), which is what [cbn_gk_hyg]
  excludes. *)

Definition cbn_rw_na : aname := {| binder_name := nAnon; binder_relevance := Relevant |}.
#[local] Definition cbn_rw_d : context_decl := vass cbn_rw_na (tSort sProp).
Definition cbn_rw_ind : inductive :=
  {| inductive_mind := (MPfile ["RW"], "rw"); inductive_ind := 0 |}.
Definition cbn_rw_ci : case_info := {| ci_ind := cbn_rw_ind; ci_npar := 0; ci_relevance := Relevant |}.
#[local] Definition cbn_rw_p : predicate term :=
  {| pparams := []; puinst := []; pcontext := []; preturn := tSort sProp |}.
(** A branch whose context is one let-binding of [tRel 0]: a variable outside the match. *)
Definition cbn_rw_br (b : term) : branch term :=
  {| bcontext := [vdef cbn_rw_na (tRel 0) (tSort sProp)]; bbody := b |}.
Definition cbn_rw_case (b : term) : term := tCase cbn_rw_ci cbn_rw_p (tConstruct cbn_rw_ind 0 []) [cbn_rw_br b].
#[local] Definition cbn_rw_w : term := cbn_rw_case (tRel 0).

Lemma cbn_rw_w_unhygienic : on_free_vars cbn_xpredT cbn_rw_w = false.
Proof. reflexivity. Qed.

(** [lift] leaves the branch context alone, and the branch body [tRel 0] is bound by it. *)
Lemma cbn_rw_w_lift : lift0 1 cbn_rw_w = cbn_rw_w.
Proof. reflexivity. Qed.

Lemma cbn_mkApps_eq_nonapp f args t :
  match t with tApp _ _ => False | _ => True end -> mkApps f args = t -> args = [] /\ f = t.
Proof.
  intros hn h. destruct args as [|a args _] using rev_ind; [split; [reflexivity|exact h]|].
  rewrite mkApps_app in h. subst t. destruct hn.
Qed.

Local Ltac cbn_rw_clean :=
  repeat match goal with
  | H : mkApps _ ?args = _ |- _ =>
      apply cbn_mkApps_eq_nonapp in H;
        [let ha := fresh "ha" in destruct H as [ha H]; subst; try discriminate H|exact I]
  end.

Local Ltac cbn_rw_nobody :=
  match goal with
  | H : option_map decl_body (nth_error _ _) = Some (Some _) |- _ => cbn in H; discriminate H
  end.

(** The terms [cbn_rw_w] reaches in a context of two assumptions. *)
Definition cbn_rw_reach (x : term) : Prop :=
  x = cbn_rw_case (tRel 0) \/ x = cbn_rw_case (tRel 1) \/ x = tRel 0.

Lemma cbn_rw_step_case (Σ : global_env) (b y : term) :
  (b = tRel 0 \/ b = tRel 1) -> red1 Σ [cbn_rw_d; cbn_rw_d] (cbn_rw_case b) y -> cbn_rw_reach y.
Proof.
  intros hb h. unfold cbn_rw_case in h.
  inversion h; subst; cbn_rw_clean.
  - (* iota: the let-body of the branch context, [tRel 0] *)
    match goal with Hn : nth_error _ ?c = Some _ |- _ =>
      destruct c as [|c]; [cbn in Hn; injection Hn as <-|destruct c; discriminate Hn] end.
    right; right. destruct hb as [-> | ->]; reflexivity.
  - (* parameters: there are none *)
    match goal with X : OnOne2 _ _ _ |- _ => cbn in X; inversion X end.
  - (* return clause: [tSort sProp] is normal *)
    match goal with X : red1 _ _ _ _ |- _ => cbn [preturn cbn_rw_p] in X; inversion X; subst end;
      cbn_rw_clean.
  - (* discriminant: a constructor is normal *)
    match goal with X : red1 _ _ (tConstruct _ _ _) _ |- _ => inversion X; subst end; cbn_rw_clean.
  - (* branch body: [tRel 0] unfolds the let to [tRel 1], which is normal *)
    match goal with X : OnOne2 _ _ _ |- _ => inversion X; subst end.
    + match goal with X0 : prod _ _ |- _ => destruct X0 as [hr hc] end.
      match goal with |- cbn_rw_reach (tCase _ _ _ [?br']) => destruct br' as [bc bb] end.
      cbn in hr, hc. subst bc.
      destruct hb as [-> | ->]; inversion hr; subst; cbn_rw_clean; [|cbn_rw_nobody].
      match goal with H : option_map decl_body (nth_error _ _) = Some (Some _) |- _ =>
        cbn in H; injection H as <- end.
      right; left. reflexivity.
    + match goal with X0 : OnOne2 _ [] _ |- _ => inversion X0 end.
Qed.

Lemma cbn_rw_step (Σ : global_env) (x y : term) :
  cbn_rw_reach x -> red1 Σ [cbn_rw_d; cbn_rw_d] x y -> cbn_rw_reach y.
Proof.
  intros hx h. destruct hx as [ -> | [ -> | -> ] ].
  - exact (cbn_rw_step_case Σ (tRel 0) y (or_introl eq_refl) h).
  - exact (cbn_rw_step_case Σ (tRel 1) y (or_intror eq_refl) h).
  - inversion h; subst; cbn_rw_clean. cbn_rw_nobody.
Qed.

Lemma cbn_rw_reach_red (Σ : global_env) (x y : term) :
  cbn_rw_reach x -> red Σ [cbn_rw_d; cbn_rw_d] x y -> cbn_rw_reach y.
Proof.
  intros hx hr. induction hr as [x y h|x|x y z h1 ih1 h2 ih2].
  - exact (cbn_rw_step Σ x y hx h).
  - exact hx.
  - exact (ih2 (ih1 hx)).
Qed.

(** Red weakening fails for [cbn_rw_w]: it reduces to [tRel 0] in a context of one assumption,
  but its lift (itself) does not reduce to the lift of [tRel 0] in a context of two. *)
Lemma cbn_red_weakening_needs_hygiene (Σ : global_env) :
  ∥ red Σ [cbn_rw_d] cbn_rw_w (tRel 0) ∥
  /\ ~ ∥ red Σ ([cbn_rw_d] ,,, [cbn_rw_d]) (lift0 1 cbn_rw_w) (lift0 1 (tRel 0)) ∥.
Proof.
  split.
  - constructor. apply red1_red.
    exact (red_iota Σ [cbn_rw_d] cbn_rw_ci 0 [] [] cbn_rw_p [cbn_rw_br (tRel 0)] (cbn_rw_br (tRel 0))
             eq_refl eq_refl).
  - rewrite cbn_rw_w_lift. intros [hr].
    destruct (cbn_rw_reach_red Σ _ _ (or_introl eq_refl) hr) as [h|[h|h]]; discriminate h.
Qed.

