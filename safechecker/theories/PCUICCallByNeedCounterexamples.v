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

(** * Counterexamples to natural invariants of the call-by-need machine

  The soundness proof of the call-by-need fast path ([PCUICCallByNeedSoundHookProof]) reads
  every machine structure through a ghost map ([g_value] and its companions of
  [PCUICCallByNeedSoundEval]), and keeps the ghost at a master level
  ([PCUICCallByNeedSoundLevel]). Two simpler designs look natural and are false for this
  machine. This file proves that they are false, so that the reasons for the ghost-reading
  design can be checked. No result of the development depends on this file, and nothing on
  the path of [PCUICTypeChecker.convert] imports it.

  - Reading the heap directly. [repr_*] below reads a structure by following its addresses
    through the heap, and [old_cok] asks that every cell of the context map stand, under
    [repr], for the context entry it was made for. Forcing a cell writes its value back, and
    [repr] reads a forced cell as that value: a reduct of what it stood for, not the same
    term. So a comparison that promises [old_cok] of its final state is false
    ([term_seam_false], [slot_seam_false]).
  - Moving the ghost to a deeper level. A ghost invariant at level [lvl] does not give the
    same invariant at [S lvl] with the ghost terms lifted ([ghost_shift_false]), and no map
    on ghost terms repairs this ([ghost_map_false]).
  - Ghost terms without a hygiene condition. Red weakening, which every change of level
    needs, fails for a term with free variables inside a branch context
    ([red_weakening_needs_hygiene]); this is why [gok] carries [gk_hyg]. *)

(** ** Reading a structure by following the heap

  [repr_value H lvl v t] reads "in heap [H], with [lvl] levels in scope, the value [v]
  stands for the term [t]". It is the relational form of the machine's read-back functions
  [rb_slot], [rb_susp] and [rb_value]. [nctx] is the length of the context the call started
  in. A cell that is being forced ([CBusy]) or that the collector has moved ([CFwd]) stands
  for no term. *)

Section Repr.
  Context (nctx : nat).

  Inductive repr_addr (H : bheap cbn_cell) : nat -> haddr -> term -> Prop :=
  | repr_addr_intro lvl a cl t :
      bh_get a H = Some cl -> repr_cell H lvl cl t -> repr_addr H lvl a t

  with repr_addrs (H : bheap cbn_cell) : nat -> list haddr -> list term -> Prop :=
  | repr_addrs_nil lvl : repr_addrs H lvl [] []
  | repr_addrs_cons lvl a l t ts :
      repr_addr H lvl a t -> repr_addrs H lvl l ts -> repr_addrs H lvl (a :: l) (t :: ts)

  with repr_cell (H : bheap cbn_cell) : nat -> cbn_cell -> term -> Prop :=
  | repr_cell_susp lvl vals nvals goff c t :
      repr_susp H lvl (mkEnv vals nvals goff) c.(c_term) t ->
      repr_cell H lvl (CSusp vals nvals goff c) t
  | repr_cell_done lvl v t :
      repr_value H lvl v t -> repr_cell H lvl (CDone v) t

  with repr_slot (H : bheap cbn_cell) : nat -> cbn_slot -> term -> Prop :=
  | repr_slot_addr lvl a t :
      repr_addr H lvl a t -> repr_slot H lvl (SAddr a) t
  | repr_slot_inl lvl vals nvals goff c t :
      repr_susp H lvl (mkEnv vals nvals goff) c.(c_term) t ->
      repr_slot H lvl (SInl vals nvals goff c) t

  with repr_slots (H : bheap cbn_cell) : nat -> list cbn_slot -> list term -> Prop :=
  | repr_slots_nil lvl : repr_slots H lvl [] []
  | repr_slots_cons lvl x l t ts :
      repr_slot H lvl x t -> repr_slots H lvl l ts -> repr_slots H lvl (x :: l) (t :: ts)

  (** [repr_susp H lvl e t u]: the suspension of the code [t] in the environment [e] stands
    for [u]. This is [rb_susp]'s equation, with the slots read back one by one. *)
  with repr_susp (H : bheap cbn_cell) : nat -> cbn_env -> term -> term -> Prop :=
  | repr_susp_intro lvl vals nvals goff t ts :
      repr_slots H lvl vals ts ->
      repr_susp H lvl (mkEnv vals nvals goff) t
        (subst ts 0 (lift (lvl - nctx + goff) nvals t))

  with repr_value (H : bheap cbn_cell) : nat -> cbn_value -> term -> Prop :=
  | repr_VCon lvl h sp ts :
      repr_addrs H lvl sp ts -> repr_value H lvl (VCon h sp) (mkApps h ts)
  | repr_VLam lvl e c t :
      repr_susp H lvl e c.(c_term) t -> repr_value H lvl (VLam e c) t
  | repr_VOpen lvl e c t :
      repr_susp H lvl e c.(c_term) t -> repr_value H lvl (VOpen e c) t
  | repr_VFix lvl e c i sp mfix j h ts :
      c.(c_term) = tFix mfix j ->
      repr_susp H lvl e (tFix mfix i) h ->
      repr_addrs H lvl sp ts ->
      repr_value H lvl (VFix e c i sp) (mkApps h ts)
  | repr_VStuckFix lvl e c i sp mfix j h ts :
      c.(c_term) = tFix mfix j ->
      repr_susp H lvl e (tFix mfix i) h ->
      repr_addrs H lvl sp ts ->
      repr_value H lvl (VStuckFix e c i sp) (mkApps h ts)
  | repr_VNeuVar lvl l sp ts :
      repr_addrs H lvl sp ts ->
      repr_value H lvl (VNeu (NVar l) sp) (mkApps (tRel (lvl - S l)) ts)
  | repr_VNeuConst lvl h sp ts :
      repr_addrs H lvl sp ts ->
      repr_value H lvl (VNeu (NConst h) sp) (mkApps h ts)
  | repr_VStuck lvl e c sp h ts :
      repr_susp H lvl e c.(c_term) h ->
      repr_addrs H lvl sp ts ->
      repr_value H lvl (VStuck e c sp) (mkApps h ts).
End Repr.

(** The context-map invariant read through [repr]: every cell [st_gam] holds for the context
  entry [j] stands, at [lvl] levels in scope, for the term that entry denotes. *)
Definition old_gam_ok (Γ : context) (nctx lvl : nat) (s : cbn_state) : Prop :=
  forall (j : nat) (a : haddr),
    PTree.get (key_of_succ_nat j) (s.(st_gam)) = Some a ->
    exists t : term, ctx_den Γ nctx lvl j = Some t /\ repr_addr nctx (s.(st_heap)) lvl a t.

(** A renamed root stands in the new heap for what the root stood for in the old heap, one
  clause per shape of root. *)
Definition old_root_pres (nctx : nat) (Hold Hnew : bheap cbn_cell) (r r' : root) : Prop :=
  match r, r' with
  | RA a, RA a' => forall lvl t, repr_addr nctx Hold lvl a t -> repr_addr nctx Hnew lvl a' t
  | RSl x, RSl x' => forall lvl t, repr_slot nctx Hold lvl x t -> repr_slot nctx Hnew lvl x' t
  | RE e, RE e' =>
    forall lvl tm u, repr_susp nctx Hold lvl e tm u -> repr_susp nctx Hnew lvl e' tm u
  | RV v, RV v' => forall lvl t, repr_value nctx Hold lvl v t -> repr_value nctx Hnew lvl v' t
  | RSk l, RSk l' =>
    forall lvl ts, repr_slots nctx Hold lvl l ts -> repr_slots nctx Hnew lvl l' ts
  | RSp l, RSp l' =>
    forall lvl ts, repr_addrs nctx Hold lvl l ts -> repr_addrs nctx Hnew lvl l' ts
  | RC cl, RC cl' => forall lvl t, repr_cell nctx Hold lvl cl t -> repr_cell nctx Hnew lvl cl' t
  | _, _ => False
  end.

(** ** A comparison seam on heap readings is false at the fuel [cbn_run] uses

  [old_slot_seam] and [old_term_seam] read the comparison's inputs with [repr_*] and promise,
  of every answer, that the caller's roots keep their [repr] reading ([old_root_pres]) and
  that the state keeps [old_cok].

  The run below is [cbn_run]'s own first [conv_term], at [cbn_depth], in
  [w_Γ = [x := (fun n : nat => n) O : nat]] with [w_t = x] and [w_u = fun n : nat => n]
  ([PCUICCallByNeedSoundConv]). The start state satisfies [old_cok] ([old_cok_run_s2]).
  [whnf] of [x] allocates the context cell of [x] at address 1, records it in [st_gam],
  forces it and writes back [VCon O []]; the comparison then answers [false] (constructor
  against lambda: no rule). [old_gam_ok] of the final state would need address 1 to stand
  under [repr] for the body [(fun n : nat => n) O]; it stands for [O]. [old_term_seam]
  promises [old_cok] of the final state, so it is false ([term_seam_false]). The same run
  through [conv_slot] on two inline slots refutes [old_slot_seam] ([slot_seam_false]).
  Nothing in the counterexample is ill-typed, and the machine is sound here: the defect is
  in the heap-following invariant. The ghost reading does not have it: every ghost of the
  invariant [minv] still reads the forced cell as the let-body ([sc_ghost_reads_body]); the
  same run satisfies the comparison's postcondition ([PCUICCallByNeedSoundConv.witness_seam_run]). *)

Section SeamCounterexample.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Σ : global_env_ext).

  Definition old_cok (Γ : context) (nctx lvl : nat) (s : cbn_state) : Prop :=
    (exists lo : positive, state_ok lo s)
    /\ heap_nofwd s.(st_heap)
    /\ (forall l : nat, old_gam_ok Γ nctx l s)
    /\ memo_ok X_type X s
    /\ memo_inv X_type X s.

  Definition old_slot_seam (Γ : context) (nctx : nat) (stress : bool) (d : cbn_fuel) : Prop :=
    forall (lvl : nat) (pb : conv_pb) (Ξ : context) (x1 x2 : cbn_slot)
      (rs : list root) (s : cbn_state) (b : bool) (rs' : list root) (s' : cbn_state),
      old_cok Γ nctx lvl s -> #|Ξ| = lvl -> is_closed_context Ξ -> nctx <= lvl ->
      conv_slot X_type X Γ nctx stress d lvl pb x1 x2 rs s = COk (b, rs', s') ->
      Forall2 (old_root_pres nctx (s.(st_heap)) (s'.(st_heap))) rs rs'
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
      Forall2 (old_root_pres nctx (s.(st_heap)) (s'.(st_heap))) rs rs'
      /\ old_cok Γ nctx lvl s'
      /\ (b = true ->
          forall u1 u2 : term,
            repr_susp nctx (s.(st_heap)) lvl e1 (c1.(c_term)) u1 ->
            repr_susp nctx (s.(st_heap)) lvl e2 (c2.(c_term)) u2 ->
            is_open_term Ξ u1 -> is_open_term Ξ u2 ->
            ∥ Σ ;;; Ξ ⊢ u1 ≤[pb] u2 ∥).

  (** [old_cok] holds of the state every call starts in: the context map is empty there. *)
  Lemma old_cok_run_s2 (Γ : context) (nctx lvl : nat) (t u : term) :
    old_cok Γ nctx lvl (run_s2 X_type X t u).
  Proof.
    split; [exists xH; apply run_s2_state_ok|].
    split; [apply run_s2_nofwd|].
    split.
    { intros l j a h. rewrite run_s2_gam_empty, PTree.gempty in h. discriminate h. }
    split; [apply run_s2_memo_ok|apply run_s2_memo_inv].
  Qed.

  (** The run, by computation: it answers [false], and the context cell of [x] is at
    address 1 and holds [O]. *)
  Lemma sc_term_run :
    match conv_term X_type X w_Γ 1 false cbn_depth 1 Conv env_empty (run_c1 X_type X w_t)
            env_empty (run_c2 X_type X w_t w_u) [] (run_s2 X_type X w_t w_u) with
    | COk (b, rs, s) =>
        b = false /\ rs = []
        /\ PTree.get (key_of_succ_nat 0) s.(st_gam) = Some (HAddr 1)
        /\ heap_get (HAddr 1) s = Some (CDone (VCon w_O []))
    | CFail _ => False
    end.
  Proof. vm_compute. repeat split. Qed.

  Lemma sc_slot_run :
    match conv_slot X_type X w_Γ 1 false cbn_depth 1 Conv
            (SInl [] 0 0 (run_c1 X_type X w_t)) (SInl [] 0 0 (run_c2 X_type X w_t w_u))
            [] (run_s2 X_type X w_t w_u) with
    | COk (_, _, s) =>
        PTree.get (key_of_succ_nat 0) s.(st_gam) = Some (HAddr 1)
        /\ heap_get (HAddr 1) s = Some (CDone (VCon w_O []))
    | CFail _ => False
    end.
  Proof. vm_compute. split; reflexivity. Qed.

  (** In a state whose context map records the cell of [x] at address 1, every ghost of
    [minv] reads that cell as the let-body of [x], whatever the cell holds. *)
  Lemma sc_ghost_reads_body (s : cbn_state) :
    PTree.get (key_of_succ_nat 0) s.(st_gam) = Some (HAddr 1) ->
    forall Q lo G, minv X_type X w_Γ 1 Σ 1 Q lo G s -> G (HAddr 1) = Some w_body.
  Proof.
    intros hgam Q lo G [_ _ hok _].
    destruct (@gk_gam _ X_type X w_Γ 1 Σ _ _ _ _ _ hok 0 (HAddr 1) hgam) as (tm & hden & hG).
    change (ctx_den w_Γ 1 Q 0) with (Some (lift0 (Q - 1 + 1) w_body)) in hden.
    assert (hl : forall n k, lift n k w_body = w_body) by reflexivity.
    rewrite hl in hden. injection hden as <-. exact hG.
  Qed.

  (** No state whose context cell of [x] holds [O] satisfies [old_cok]. *)
  Lemma sc_not_old_cok (s : cbn_state) :
    PTree.get (key_of_succ_nat 0) s.(st_gam) = Some (HAddr 1) ->
    heap_get (HAddr 1) s = Some (CDone (VCon w_O [])) ->
    ~ old_cok w_Γ 1 1 s.
  Proof.
    intros hg hh (_ & _ & hgam & _ & _).
    destruct (hgam 1 0 (HAddr 1) hg) as (tm & hden & hr).
    cbn in hden. injection hden as <-.
    inversion hr as [lv a cl tm0 hget hcl]; subst.
    unfold heap_get in hh. rewrite hh in hget. injection hget as <-.
    inversion hcl; subst.
    match goal with h : repr_value _ _ _ (VCon _ _) _ |- _ => inversion h; subst end.
    match goal with h : repr_addrs _ _ _ [] _ |- _ => inversion h; subst end.
    match goal with h : mkApps w_O [] = _ |- _ => cbv [mkApps w_O] in h; discriminate h end.
  Qed.

  Lemma term_seam_false : ~ old_term_seam w_Γ 1 false cbn_depth.
  Proof.
    intros hseam.
    pose proof sc_term_run as hrun.
    destruct (conv_term X_type X w_Γ 1 false cbn_depth 1 Conv env_empty
                (run_c1 X_type X w_t) env_empty (run_c2 X_type X w_t w_u) []
                (run_s2 X_type X w_t w_u)) as [[[b rs] s']|w] eqn:E;
      [|contradiction hrun].
    destruct hrun as (_ & _ & hg & hh).
    destruct (hseam 1 Conv w_Γ env_empty (run_c1 X_type X w_t) env_empty
                (run_c2 X_type X w_t w_u) [] (run_s2 X_type X w_t w_u) b rs s'
                (old_cok_run_s2 w_Γ 1 1 w_t w_u) eq_refl eq_refl (le_n 1) E)
      as (_ & hcok & _).
    exact (sc_not_old_cok s' hg hh hcok).
  Qed.

  Lemma slot_seam_false : ~ old_slot_seam w_Γ 1 false cbn_depth.
  Proof.
    intros hseam.
    pose proof sc_slot_run as hrun.
    destruct (conv_slot X_type X w_Γ 1 false cbn_depth 1 Conv
                (SInl [] 0 0 (run_c1 X_type X w_t)) (SInl [] 0 0 (run_c2 X_type X w_t w_u))
                [] (run_s2 X_type X w_t w_u)) as [[[b rs] s']|w] eqn:E;
      [|contradiction hrun].
    destruct hrun as [hg hh].
    destruct (hseam 1 Conv w_Γ (SInl [] 0 0 (run_c1 X_type X w_t))
                (SInl [] 0 0 (run_c2 X_type X w_t w_u)) [] (run_s2 X_type X w_t w_u)
                b rs s' (old_cok_run_s2 w_Γ 1 1 w_t w_u) eq_refl eq_refl (le_n 1) E)
      as (_ & hcok & _).
    exact (sc_not_old_cok s' hg hh hcok).
  Qed.

End SeamCounterexample.

(** ** The ghost reading cannot change level

  The comparison crosses binders: its lambda, product and match rows compare at [S lvl] or
  [lvl + n]. Stating it on the ghost reading of [PCUICCallByNeedSoundEval] at the current
  level would need [gok] at [lvl] to give [gok] at [S lvl] for the same state, with every
  ghost term lifted by one: [gok lvl G s -> gok (S lvl) (gshift 1 G) s]. That is false
  ([ghost_shift_false]).

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
  [functional_extensionality_dep] into the assumptions of [ghost_map_false].

  So the level of [gok] cannot move down while a stale cell exists. For the same reason a
  whole-heap scoping clause at the current level would fail once a fresh-variable cell
  [CDone (VNeu (NVar lvl) [])] outlives its binder and the comparison is back at level
  [lvl]: that cell would need [lvl < lvl]. This last claim is an argument, not a Rocq
  result. The comparison therefore keeps its ghost at a master level, and its scoping per
  master level in [minv] ([PCUICCallByNeedSoundLevel]). *)

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
            let l := fresh "l" in
            remember args as l eqn:Hl; clear Hl;
            destruct l as [|a l _] using rev_ind;
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

(** ** Why [gok] carries a hygiene clause: red weakening is false without it

  The comparison changes the level of [gok] by lifting every ghost term, which needs red
  weakening of every ghost term. [rw_w] below is a match whose branch context is one
  let-binding of an outer variable. [lift] leaves branch contexts alone, so [lift0 1 rw_w] is
  [rw_w] itself, while [iota_red] expands the let-body: [rw_w] reduces to [tRel 0] in a
  context of one assumption, and in a context of two its lift still reduces to [tRel 0],
  never to [lift0 1 (tRel 0)] ([red_weakening_needs_hygiene]). Without [gk_hyg], a cell
  [CDone (VNeu (NVar 0) [])] at level 1, which reads [tRel 0], could carry the ghost
  [rw_w]; after lifting to level 2 the cell reads [tRel 1] and the lifted ghost does not
  reduce to it. [rw_w] fails the hygiene test ([rw_w_unhygienic]), which is what [gk_hyg]
  excludes. *)

Definition rw_na : aname := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition rw_d : context_decl := vass rw_na (tSort sProp).
Definition rw_ind : inductive :=
  {| inductive_mind := (MPfile ["RW"], "rw"); inductive_ind := 0 |}.
Definition rw_ci : case_info := {| ci_ind := rw_ind; ci_npar := 0; ci_relevance := Relevant |}.
Definition rw_p : predicate term :=
  {| pparams := []; puinst := []; pcontext := []; preturn := tSort sProp |}.
(** A branch whose context is one let-binding of [tRel 0]: a variable outside the match. *)
Definition rw_br (b : term) : branch term :=
  {| bcontext := [vdef rw_na (tRel 0) (tSort sProp)]; bbody := b |}.
Definition rw_case (b : term) : term := tCase rw_ci rw_p (tConstruct rw_ind 0 []) [rw_br b].
Definition rw_w : term := rw_case (tRel 0).

Lemma rw_w_unhygienic : on_free_vars xpredT rw_w = false.
Proof. reflexivity. Qed.

(** [lift] leaves the branch context alone, and the branch body [tRel 0] is bound by it. *)
Lemma rw_w_lift : lift0 1 rw_w = rw_w.
Proof. reflexivity. Qed.

Lemma mkApps_eq_nonapp f args t :
  match t with tApp _ _ => False | _ => True end -> mkApps f args = t -> args = [] /\ f = t.
Proof.
  intros hn h. destruct args as [|a args _] using rev_ind; [split; [reflexivity|exact h]|].
  rewrite mkApps_app in h. subst t. destruct hn.
Qed.

Local Ltac rw_clean :=
  repeat match goal with
  | H : mkApps _ ?args = _ |- _ =>
      apply mkApps_eq_nonapp in H;
        [let ha := fresh "ha" in destruct H as [ha H]; subst; try discriminate H|exact I]
  end.

Local Ltac rw_nobody :=
  match goal with
  | H : option_map decl_body (nth_error _ _) = Some (Some _) |- _ => cbn in H; discriminate H
  end.

(** The terms [rw_w] reaches in a context of two assumptions. *)
Definition rw_reach (x : term) : Prop :=
  x = rw_case (tRel 0) \/ x = rw_case (tRel 1) \/ x = tRel 0.

Lemma rw_step_case (Σ : global_env) (b y : term) :
  (b = tRel 0 \/ b = tRel 1) -> red1 Σ [rw_d; rw_d] (rw_case b) y -> rw_reach y.
Proof.
  intros hb h. unfold rw_case in h.
  inversion h; subst; rw_clean.
  - (* iota: the let-body of the branch context, [tRel 0] *)
    match goal with Hn : nth_error _ ?c = Some _ |- _ =>
      destruct c as [|c]; [cbn in Hn; injection Hn as <-|destruct c; discriminate Hn] end.
    right; right. destruct hb as [-> | ->]; reflexivity.
  - (* parameters: there are none *)
    match goal with X : OnOne2 _ _ _ |- _ => cbn in X; inversion X end.
  - (* return clause: [tSort sProp] is normal *)
    match goal with X : red1 _ _ _ _ |- _ => cbn [preturn rw_p] in X; inversion X; subst end;
      rw_clean.
  - (* discriminant: a constructor is normal *)
    match goal with X : red1 _ _ (tConstruct _ _ _) _ |- _ => inversion X; subst end; rw_clean.
  - (* branch body: [tRel 0] unfolds the let to [tRel 1], which is normal *)
    match goal with X : OnOne2 _ _ _ |- _ => inversion X; subst end.
    + match goal with X0 : prod _ _ |- _ => destruct X0 as [hr hc] end.
      match goal with |- rw_reach (tCase _ _ _ [?br']) => destruct br' as [bc bb] end.
      cbn in hr, hc. subst bc.
      destruct hb as [-> | ->]; inversion hr; subst; rw_clean; [|rw_nobody].
      match goal with H : option_map decl_body (nth_error _ _) = Some (Some _) |- _ =>
        cbn in H; injection H as <- end.
      right; left. reflexivity.
    + match goal with X0 : OnOne2 _ [] _ |- _ => inversion X0 end.
Qed.

Lemma rw_step (Σ : global_env) (x y : term) :
  rw_reach x -> red1 Σ [rw_d; rw_d] x y -> rw_reach y.
Proof.
  intros hx h. destruct hx as [ -> | [ -> | -> ] ].
  - exact (rw_step_case Σ (tRel 0) y (or_introl eq_refl) h).
  - exact (rw_step_case Σ (tRel 1) y (or_intror eq_refl) h).
  - inversion h; subst; rw_clean. rw_nobody.
Qed.

Lemma rw_reach_red (Σ : global_env) (x y : term) :
  rw_reach x -> red Σ [rw_d; rw_d] x y -> rw_reach y.
Proof.
  intros hx hr. induction hr as [x y h|x|x y z h1 ih1 h2 ih2].
  - exact (rw_step Σ x y hx h).
  - exact hx.
  - exact (ih2 (ih1 hx)).
Qed.

(** Red weakening fails for [rw_w]: it reduces to [tRel 0] in a context of one assumption,
  but its lift (itself) does not reduce to the lift of [tRel 0] in a context of two. *)
Lemma red_weakening_needs_hygiene (Σ : global_env) :
  ∥ red Σ [rw_d] rw_w (tRel 0) ∥
  /\ ~ ∥ red Σ ([rw_d] ,,, [rw_d]) (lift0 1 rw_w) (lift0 1 (tRel 0)) ∥.
Proof.
  split.
  - constructor. apply red1_red.
    exact (red_iota Σ [rw_d] rw_ci 0 [] [] rw_p [rw_br (tRel 0)] (rw_br (tRel 0))
             eq_refl eq_refl).
  - rewrite rw_w_lift. intros [hr].
    destruct (rw_reach_red Σ _ _ (or_introl eq_refl) hr) as [h|[h|h]]; discriminate h.
Qed.

