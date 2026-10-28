(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require CanonicalTries.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping
  PCUICOnFreeVars PCUICReduction PCUICSigmaCalculus PCUICRenameDef PCUICRenameConv
  PCUICOnFreeVarsConv PCUICWeakeningConv PCUICRedTypeIrrelevance BDStrengthening.
From MetaRocq.SafeChecker Require Import PCUICWfEnv PCUICCallByNeed PCUICCallByNeedSound
  PCUICCallByNeedSoundCtx PCUICCallByNeedSoundEval.

Import CanonicalTries.

Local Notation xpredT := (fun _ : nat => true) (only parsing).
Local Notation xpred0 := (fun _ : nat => false) (only parsing).

(** * The comparison's levels against the evaluator's invariant (BET-298, step 3b)

  The comparison crosses binders, so it reads its inputs at a level [L] that grows and
  shrinks, while [gok] cannot change its level downwards while a stale fresh-variable cell
  exists ([PCUICCallByNeedSoundHookFrame.ghost_shift_false], [ghost_map_false]).

  The design: [gok] is kept at a MASTER level [Q], the highest level the comparison has
  reached, with the junk context [jctx (Q - nctx)] for the variables between [nctx] and [Q];
  the comparison's logical level is [L <= Q]. The machine runs at [Q] ([machine_sound] is
  level-free in its code). A root the comparison holds at [L] reads at [Q] as [lift0 (Q - L)]
  of its logical reading, and a reduct of such a reading is again a lift
  ([red_unlift], by [red_rename]): that is how a fact at [Q] becomes a fact at [L].

  - [gok_raise] lifts the master level, [Q] to [Q + n], with every ghost term lifted by [n]
    ([gshift]). It needs [hwf Q]: no cell names a fresh variable at a level [>= Q], and the
    head of every constructor and neutral constant value is closed. That is a whole-heap
    STRUCTURAL invariant, true at the master level (fresh variables are only allocated
    below it) but not one the ghost reading can see, so its preservation by the machine is a
    separate theorem ([machine_hwf] states it; it is proved elsewhere). It also needs
    [gk_hyg], the hygiene of every ghost term, for red weakening
    ([PCUICCallByNeedSoundEval.red_weakening_needs_hygiene]).
  - [red_unlift] and [red_assum_irrel] do NOT depend on [gk_hyg]: the terms they move are
    root readings, which are reducts of the typed inputs of the hook, hence hygienic by
    themselves ([red_on_free_vars]). *)

(** ** The junk context and the lifted ghost *)

Definition jdecl : context_decl :=
  vass {| binder_name := nAnon; binder_relevance := Relevant |} (tSort sProp).
Definition jctx (n : nat) : context := repeat jdecl n.

Lemma jctx_length n : #|jctx n| = n.
Proof. apply repeat_length. Qed.

Lemma jctx_add m n : jctx (m + n) = jctx n ,,, jctx m.
Proof. unfold jctx, app_context. rewrite repeat_app. reflexivity. Qed.

Lemma jctx_closed p n : on_free_vars_ctx p (jctx n).
Proof.
  revert p. induction n as [|n ih]; intros p; [reflexivity|].
  change (jctx (S n)) with (jctx n ,, jdecl). rewrite on_free_vars_ctx_snoc, ih. reflexivity.
Qed.

Lemma jctx_assum n : assumption_context (jctx n).
Proof. induction n as [|n ih]; cbn; constructor; exact ih. Qed.

Definition gshift (n : nat) (G : ghost) : ghost :=
  mkGhost (fun a => option_map (lift0 n) (G a)) (gc G).

(** ** The structural invariant at the master level *)

Definition vwf (lvl : nat) (v : cbn_value) : Prop :=
  match v with
  | VNeu (NVar l) _ => l < lvl
  | VNeu (NConst h) _ | VCon h _ => closedn 0 h
  | _ => True
  end.

Definition cwf (lvl : nat) (cl : cbn_cell) : Prop :=
  match cl with CDone v => vwf lvl v | _ => True end.

Definition hwf (lvl : nat) (s : cbn_state) : Prop :=
  forall a cl, heap_get a s = Some cl -> cwf lvl cl.

Definition rwf (lvl : nat) (r : root) : Prop :=
  match r with RV v => vwf lvl v | RC cl => cwf lvl cl | _ => True end.

Lemma vwf_mono lvl lvl' v : lvl <= lvl' -> vwf lvl v -> vwf lvl' v.
Proof. intros hle. destruct v as [| | | |[l|h] sp| |]; cbn; try tauto; lia. Qed.

Lemma cwf_mono lvl lvl' cl : lvl <= lvl' -> cwf lvl cl -> cwf lvl' cl.
Proof. intros hle. destruct cl; cbn; try tauto. apply vwf_mono, hle. Qed.

Lemma hwf_mono lvl lvl' s : lvl <= lvl' -> hwf lvl s -> hwf lvl' s.
Proof. intros hle h a cl ha. exact (cwf_mono _ _ _ hle (h a cl ha)). Qed.

(** ** Readings commute with the lift of the ghost *)

Section Shift.
  Context (nctx lvl n : nat) (hle : nctx <= lvl).

  Lemma lift_susp_read N nvals t ts :
    #|ts| = nvals ->
    lift0 n (subst ts 0 (lift N nvals t)) = subst (map (lift0 n) ts) 0 (lift (n + N) nvals t).
  Proof.
    intros hl. rewrite distr_lift_subst, Nat.add_0_r, hl.
    rewrite (simpl_lift t N nvals n nvals) by lia. reflexivity.
  Qed.

  Lemma g_slot_shift G :
    (forall x t, g_slot nctx lvl G x t -> g_slot nctx (lvl + n) (gshift n G) x (lift0 n t))
    /\ (forall l ts, g_slots nctx lvl G l ts ->
          g_slots nctx (lvl + n) (gshift n G) l (map (lift0 n) ts) /\ #|ts| = #|l|).
  Proof.
    apply (g_slot_mutind nctx lvl G
             (fun x t => g_slot nctx (lvl + n) (gshift n G) x (lift0 n t))
             (fun l ts => g_slots nctx (lvl + n) (gshift n G) l (map (lift0 n) ts)
                          /\ #|ts| = #|l|)).
    - intros a t ha. constructor. cbn. rewrite ha. reflexivity.
    - intros vals nvals goff c ts _ [ih hl] hn hc.
      rewrite (lift_susp_read _ nvals) by lia.
      replace (n + (lvl - nctx + goff)) with (lvl + n - nctx + goff) by lia.
      constructor; [exact ih|exact hn|exact hc].
    - split; [constructor|reflexivity].
    - intros x l t ts _ ih1 _ [ih2 hl]. split; [constructor; assumption|cbn; congruence].
  Qed.

  Lemma g_susp_shift G e t u :
    g_susp nctx lvl G e t u -> g_susp nctx (lvl + n) (gshift n G) e t (lift0 n u).
  Proof.
    intros h. inversion h as [vals nvals goff t0 ts hs hn]; subst.
    destruct (proj2 (g_slot_shift G) _ _ hs) as [hs' hl].
    rewrite (lift_susp_read _ #|vals|) by lia.
    replace (n + (lvl - nctx + goff)) with (lvl + n - nctx + goff) by lia.
    constructor; [exact hs'|reflexivity].
  Qed.

  Lemma g_addrs_shift G l ts :
    g_addrs G l ts -> g_addrs (gshift n G) l (map (lift0 n) ts).
  Proof.
    induction 1 as [|a t l ts ha hl ih]; constructor; [cbn; rewrite ha; reflexivity|exact ih].
  Qed.

  Lemma g_value_shift G v t :
    vwf lvl v -> g_value nctx lvl G v t -> g_value nctx (lvl + n) (gshift n G) v (lift0 n t).
  Proof.
    intros hw hv. destruct hv; cbn in hw; rewrite ?lift_mkApps.
    - rewrite (lift_closed n 0 h hw). constructor. exact (g_addrs_shift G _ _ H).
    - constructor; [exact (g_susp_shift G _ _ _ H)|exact H0].
    - constructor; [exact (g_susp_shift G _ _ _ H)|exact H0].
    - cbn [lift]. destruct (Nat.leb_spec 0 (lvl - S l)) as [_|]; [|lia].
      replace (n + (lvl - S l)) with (lvl + n - S l) by lia.
      constructor. exact (g_addrs_shift G _ _ H).
    - rewrite (lift_closed n 0 h hw). constructor. exact (g_addrs_shift G _ _ H).
    - econstructor; [exact (g_susp_shift G _ _ _ H)|exact H0|exact (g_addrs_shift G _ _ H1)].
    - econstructor; [exact H|exact (g_susp_shift G _ _ _ H0)|exact H1|exact (g_addrs_shift G _ _ H2)].
    - econstructor; [exact H|exact (g_susp_shift G _ _ _ H0)|exact H1|exact (g_addrs_shift G _ _ H2)].
  Qed.

  Lemma g_cell_shift G cl u :
    cwf lvl cl -> g_cell nctx lvl G cl u -> g_cell nctx (lvl + n) (gshift n G) cl (lift0 n u).
  Proof.
    intros hw hc. destruct hc; cbn in hw.
    - constructor; [exact (g_susp_shift G _ _ _ H)|exact H0].
    - constructor. exact (g_value_shift G _ _ hw H).
  Qed.

  Lemma ctx_den_shift Γ j t :
    nctx = #|Γ| -> ctx_den Γ nctx lvl j = Some t -> ctx_den Γ nctx (lvl + n) j = Some (lift0 n t).
  Proof.
    intros hn. unfold ctx_den. destruct (nth_error Γ j) as [decl|] eqn:E; [|discriminate].
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
  Context (wfΣ : wf Σ) (hnctx : nctx = #|Γ|) (hΓ : is_closed_context Γ) (hhyg : ctx_hyg Γ).

  Lemma master_ctx_xpredT Q : on_ctx_free_vars xpredT (Γ ,,, jctx Q).
  Proof.
    apply (on_free_vars_ctx_on_ctx_free_vars_xpredT (P := xpred0)).
    rewrite on_free_vars_ctx_app, hΓ. apply jctx_closed.
  Qed.

  (** A ghost reduction at [Q] lifts to [Q + n]: red weakening, which needs the hygiene of the
    ghost term. *)
  Lemma cred_raise Q n t u :
    on_free_vars xpredT t ->
    cred Γ Σ (jctx Q) t u -> cred Γ Σ (jctx (n + Q)) (lift0 n t) (lift0 n u).
  Proof.
    intros ht [hr]. constructor.
    rewrite jctx_add, app_context_assoc.
    eapply (weakening_red_0 (wfΣ := wfΣ) (P := xpredT) (Γ' := jctx n)).
    - symmetry. apply jctx_length.
    - apply master_ctx_xpredT.
    - exact ht.
    - exact hr.
  Qed.

  Lemma gok_raise Q n lo G s :
    nctx <= Q -> hwf Q s ->
    gok X_type X Γ nctx Σ (jctx (Q - nctx)) Q lo G s ->
    gok X_type X Γ nctx Σ (jctx (Q + n - nctx)) (Q + n) lo (gshift n G) s.
  Proof.
    intros hQ hw hok.
    replace (Q + n - nctx) with (n + (Q - nctx)) by lia.
    split.
    - exact (gk_state _ _ _ _ _ _ _ _ _ _ hok).
    - exact (gk_nofwd _ _ _ _ _ _ _ _ _ _ hok).
    - intros a cl ha.
      destruct (gk_cells _ _ _ _ _ _ _ _ _ _ hok a cl ha) as (t & ht & hc).
      exists (lift0 n t). split; [cbn; rewrite ht; reflexivity|].
      destruct hc as [hb|(u & hu & hr)]; [left; exact hb|right].
      exists (lift0 n u). split.
      + exact (g_cell_shift nctx Q n hQ G cl u (hw a cl ha) hu).
      + exact (cred_raise (Q - nctx) n t u (gk_hyg _ _ _ _ _ _ _ _ _ _ hok hhyg a t ht) hr).
    - intros a t ht. cbn in ht. destruct (G a) as [t0|] eqn:E; [|discriminate ht].
      exact (gk_dom _ _ _ _ _ _ _ _ _ _ hok a t0 E).
    - intros j a hj. destruct (gk_gam _ _ _ _ _ _ _ _ _ _ hok j a hj) as (t & hden & hGa).
      exists (lift0 n t). split.
      + exact (ctx_den_shift nctx Q n hQ Γ j t hnctx hden).
      + cbn. rewrite hGa. reflexivity.
    - exact (gk_memo _ _ _ _ _ _ _ _ _ _ hok).
    - intros hc a t ht. cbn in ht. destruct (G a) as [t0|] eqn:E; [|discriminate ht].
      injection ht as <-. apply hyg_lift. exact (gk_hyg _ _ _ _ _ _ _ _ _ _ hok hc a t0 E).
  Qed.
End Raise.

(** ** From the master level to the logical level *)

(** A reduct of a lifted term is a lift, and the reduction happens below the lift. The
  source is a root reading, hygienic because it is a reduct of a typed input; nothing here
  uses [gk_hyg]. *)
Lemma red_unlift {cf : checker_flags} (Σ : global_env_ext) (wfΣ : wf Σ) (Ξ J : context)
    (t u : term) :
  on_ctx_free_vars xpredT Ξ -> on_free_vars xpredT t ->
  red Σ (Ξ ,,, J) (lift0 #|J| t) u ->
  exists u', u = lift0 #|J| u' /\ ∥ red Σ Ξ t u' ∥.
Proof.
  intros hΞ ht hr.
  pose (P := strengthenP 0 #|J| xpredT).
  pose (f := unlift_renaming #|J| 0).
  assert (hctx : on_ctx_free_vars P (Ξ ,,, J)).
  { exact (on_ctx_free_vars_strengthenP Ξ J [] hΞ eq_refl). }
  assert (hsrc : on_free_vars P (lift0 #|J| t)).
  { unfold P. rewrite on_free_vars_lift. exact ht. }
  assert (hren : urenaming P (Ξ ,,, J) Ξ f).
  { exact (urenaming_strengthen xpredT Ξ J []). }
  pose proof (red_rename P Σ (Ξ ,,, J) Ξ (lift0 #|J| t) u f wfΣ hren hctx hsrc hr) as hr'.
  pose proof (red_on_free_vars (wfΣ := wfΣ) hctx hsrc hr) as hu.
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
Lemma red_assum_irrel (Σ : global_env) (Ξ Δ1 Δ2 : context) (t u : term) :
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

(** ** The comparison's invariant: [gok] at the master level

  [minv L Q lo G s]: the comparison is at logical level [L], the master level is [Q], and
  the state satisfies [gok] at [Q] with the junk context, and [hwf Q]. The roots the
  comparison holds are described by their readings at [Q] in each lemma, as [lift0 (Q - L)]
  of a logical reading. *)

Section Master.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat) (stress : bool) (Σ : global_env_ext).
  Context (wfΣ : wf Σ) (hΣ : abstract_env_ext_rel X Σ).
  Context (hnctx : nctx = #|Γ|) (hΓ : is_closed_context Γ) (hhyg : ctx_hyg Γ).
  Context (hcio : forall j decl b, nth_error Γ j = Some decl -> decl.(decl_body) = Some b ->
                    PCUICCallByNeedSoundHook.consts_okb Σ b).

  Record minv (L Q : nat) (lo : positive) (G : ghost) (s : cbn_state) : Prop := mkMinv {
    mi_L : nctx <= L;
    mi_Q : L <= Q;
    mi_gok : gok X_type X Γ nctx Σ (jctx (Q - nctx)) Q lo G s;
    mi_hwf : hwf Q s }.

  (** *** The interface of the structural invariant (slice B)

    The machine keeps [hwf Q] of the heap, of the roots and of the value it returns, and so
    does an allocation of a cell that has it. Stated here, proved in its own slice; every
    lemma of the comparison that needs it takes it as a hypothesis. *)
  Definition machine_hwf : Prop := forall d Q, nctx <= Q ->
    (forall a rs s v rs' s', hwf Q s -> Forall (rwf Q) rs ->
       force X_type X Γ nctx stress d a rs s = COk (v, rs', s') ->
       hwf Q s' /\ Forall (rwf Q) rs' /\ vwf Q v)
    /\ (forall x stk rs s v rs' s', hwf Q s -> Forall (rwf Q) rs ->
       eval_slot X_type X Γ nctx stress d x stk rs s = COk (v, rs', s') ->
       hwf Q s' /\ Forall (rwf Q) rs' /\ vwf Q v)
    /\ (forall e c stk rs s v rs' s', hwf Q s -> Forall (rwf Q) rs ->
       whnf X_type X Γ nctx stress d e c stk rs s = COk (v, rs', s') ->
       hwf Q s' /\ Forall (rwf Q) rs' /\ vwf Q v)
    /\ (forall e c mfix idx stk rs s v rs' s', hwf Q s -> Forall (rwf Q) rs ->
       whnf_fix X_type X Γ nctx stress d e c mfix idx stk rs s = COk (v, rs', s') ->
       hwf Q s' /\ Forall (rwf Q) rs' /\ vwf Q v)
    /\ (forall v stk rs s w rs' s', hwf Q s -> Forall (rwf Q) rs -> vwf Q v ->
       apply X_type X Γ nctx stress d v stk rs s = COk (w, rs', s') ->
       hwf Q s' /\ Forall (rwf Q) rs' /\ vwf Q w).

  Definition alloc_hwf : Prop := forall Q cl rs s a rs' s', nctx <= Q ->
    hwf Q s -> cwf Q cl -> Forall (rwf Q) rs ->
    alloc stress cl rs s = COk (a, rs', s') -> hwf Q s' /\ Forall (rwf Q) rs'.

  (** *** The machine at the master level *)

  Lemma whnf_master (hB : machine_hwf) d L Q lo G e c stk sts tc rs s v rs' s' :
    minv L Q lo G s -> Forall (rwf Q) rs ->
    g_susp nctx Q G e c.(c_term) tc -> PCUICCallByNeedSoundEval.cok G c ->
    g_slots nctx Q G stk sts ->
    whnf X_type X Γ nctx stress d e c stk rs s = COk (v, rs', s') ->
    exists lo' G' u, minv L Q lo' G' s' /\ Forall (rwf Q) rs' /\ vwf Q v
      /\ gren nctx Q G G' rs rs' /\ g_value nctx Q G' v u
      /\ cred Γ Σ (jctx (Q - nctx)) (mkApps tc sts) u.
  Proof.
    intros [hL hQ hok hw] hrs hs hc hstk he.
    assert (hlen : #|jctx (Q - nctx)| = Q - nctx) by apply jctx_length.
    destruct (machine_sound X_type X Γ nctx stress Σ (jctx (Q - nctx)) Q wfΣ hΣ hlen hnctx
                ltac:(lia) hcio d) as (_ & _ & hW & _ & _).
    destruct (hW lo G e c stk sts tc rs s v rs' s' hok hs hc hstk he)
      as (lo' & G' & u & hren & hok' & hv & hr).
    destruct (hB d Q ltac:(lia)) as (_ & _ & hBw & _ & _).
    destruct (hBw e c stk rs s v rs' s' hw hrs he) as (hw' & hrs' & hvw).
    exists lo', G', u. split; [constructor; assumption|]. split; [exact hrs'|].
    split; [exact hvw|]. split; [exact hren|]. split; [exact hv|exact hr].
  Qed.

  Lemma eval_slot_master (hB : machine_hwf) d L Q lo G x stk sts tx rs s v rs' s' :
    minv L Q lo G s -> Forall (rwf Q) rs ->
    g_slot nctx Q G x tx -> g_slots nctx Q G stk sts ->
    eval_slot X_type X Γ nctx stress d x stk rs s = COk (v, rs', s') ->
    exists lo' G' u, minv L Q lo' G' s' /\ Forall (rwf Q) rs' /\ vwf Q v
      /\ gren nctx Q G G' rs rs' /\ g_value nctx Q G' v u
      /\ cred Γ Σ (jctx (Q - nctx)) (mkApps tx sts) u.
  Proof.
    intros [hL hQ hok hw] hrs hx hstk he.
    assert (hlen : #|jctx (Q - nctx)| = Q - nctx) by apply jctx_length.
    destruct (machine_sound X_type X Γ nctx stress Σ (jctx (Q - nctx)) Q wfΣ hΣ hlen hnctx
                ltac:(lia) hcio d) as (_ & hE & _ & _ & _).
    destruct (hE lo G x stk sts tx rs s v rs' s' hok hx hstk he)
      as (lo' & G' & u & hren & hok' & hv & hr).
    destruct (hB d Q ltac:(lia)) as (_ & hBe & _ & _ & _).
    destruct (hBe x stk rs s v rs' s' hw hrs he) as (hw' & hrs' & hvw).
    exists lo', G', u. split; [constructor; assumption|]. split; [exact hrs'|].
    split; [exact hvw|]. split; [exact hren|]. split; [exact hv|exact hr].
  Qed.

  (** *** From the master level to the logical level

    A master reduction from a lifted logical reading is a lifted logical reduction, in any
    assumption context of the logical length. *)
  Lemma cred_unlift L Q v u :
    nctx <= L -> L <= Q -> on_free_vars xpredT v ->
    cred Γ Σ (jctx (Q - nctx)) (lift0 (Q - L) v) u ->
    exists u', u = lift0 (Q - L) u'
      /\ forall Δ, #|Δ| = L - nctx -> ∥ red Σ (Γ ,,, Δ) v u' ∥.
  Proof.
    intros hL hQ hv [hr].
    replace (Q - nctx) with ((Q - L) + (L - nctx)) in hr by lia.
    rewrite jctx_add, app_context_assoc in hr.
    pose proof (red_unlift Σ wfΣ (Γ ,,, jctx (L - nctx)) (jctx (Q - L)) v u
                  (master_ctx_xpredT Γ hΓ (L - nctx)) hv) as hU.
    rewrite jctx_length in hU.
    destruct (hU hr) as (u' & hu & [hr']).
    exists u'. split; [exact hu|].
    intros Δ hΔ. constructor.
    exact (red_assum_irrel Σ Γ (jctx (L - nctx)) Δ v u'
             ltac:(rewrite jctx_length; lia) (jctx_assum _) hr').
  Qed.

  (** The start of a run is an instance of [minv]: [L = Q = nctx], an empty heap. *)
  Lemma minv_start lo G s :
    gok X_type X Γ nctx Σ [] nctx lo G s ->
    (forall a cl, heap_get a s = Some cl -> False) ->
    minv nctx nctx lo G s.
  Proof.
    intros hok hempty. split; [lia|lia| |].
    - rewrite Nat.sub_diag. exact hok.
    - intros a cl ha. destruct (hempty a cl ha).
  Qed.
End Master.
