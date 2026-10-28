(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require CanonicalTries.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICTyping
  PCUICOnFreeVars PCUICReduction PCUICSigmaCalculus PCUICRenameDef PCUICRenameConv
  PCUICOnFreeVarsConv PCUICInstConv PCUICSubstitution BDStrengthening.
From MetaRocq.SafeChecker Require Import PCUICWfEnv PCUICCallByNeed PCUICCallByNeedSound
  PCUICCallByNeedSoundGC PCUICCallByNeedSoundCtx PCUICCallByNeedSoundMemo
  PCUICCallByNeedSoundHook PCUICCallByNeedSoundCong PCUICCallByNeedSoundEval
  PCUICCallByNeedSoundHeapWf PCUICCallByNeedSoundLevel.

Local Notation xpredT := (fun _ : nat => true) (only parsing).

(** * The read-back against the ghost reading

  [rb_sound_holds] proves [PCUICCallByNeedSoundLevel.rb_sound]: a read-back at the logical
  level [L] of a suspension whose master reading at [Q] is [lift0 (Q - L) v] returns a
  reduct of [v], and leaves [minv] alone.

  The read-back is pure apart from [tick], which lowers only [st_steps]; [minv] reads the
  heap, the next address, the context map and the memo ([minv_same]), never [st_steps].

  The one obstacle: a slot of an environment that the code does not use may read, at [Q],
  as a term that names a fresh variable at a level [>= L] (it is not a lift). Its read-back
  at [L] is then junk ([tRel (L - S l)] saturates to [tRel 0]), but the junk lands in a
  position the code does not use. The proof:
  - [rename_susp]: the logical reading [v] is the master reading renamed by
    [unlift_renaming (Q - L) 0], which is again a reading of the same code through the
    renamed slots, at the logical level;
  - [on_free_vars_inst_inv] (the converse of [on_free_vars_inst]): every slot the code uses
    reads as a lift ([live_vars]);
  - the slots the code does not use are replaced by their own read-backs
    ([subst_ext_live], [build_ws]), and [red_red] moves the used ones. *)

(** ** Terms *)

Lemma on_free_vars_up_inv (P Q : nat -> bool) n s :
  (forall i, on_free_vars P (s i) -> Q i) ->
  forall i, on_free_vars (shiftnP n P) (up n s i) -> shiftnP n Q i.
Proof.
  intros H i. unfold up. destruct (Nat.leb_spec n i) as [Hi|Hi].
  - rewrite on_free_vars_rename. intros h. unfold shiftnP.
    destruct (Nat.ltb_spec i n) as [|_]; [lia|]. cbn. apply H.
    assert (heq : forall j, (shiftnP n P ∘ Nat.add n) j = P j).
    { intros j. cbv beta. unfold shiftnP.
      destruct (Nat.ltb_spec (n + j) n); [lia|]. cbn. f_equal. lia. }
    rewrite <- (on_free_vars_ext _ _ _ heq). exact h.
  - intros _. unfold shiftnP. destruct (Nat.ltb_spec i n); [reflexivity|lia].
Qed.

Definition ofv_inv (t : term) : Prop := forall (P Q : nat -> bool) s,
  (forall i, on_free_vars P (s i) -> Q i) -> on_free_vars P (inst s t) -> on_free_vars Q t.

Lemma forallb_inst_inv (P Q : nat -> bool) s l :
  All ofv_inv l -> (forall i, on_free_vars P (s i) -> Q i) ->
  forallb (on_free_vars P) (map (inst s) l) -> forallb (on_free_vars Q) l.
Proof.
  induction 1 as [|t l ht hl ih]; cbn; intros Hs h; [reflexivity|].
  apply andb_prop in h as [h1 h2]. rewrite (ht _ _ _ Hs h1), (ih Hs h2). reflexivity.
Qed.

Lemma fix_inst_inv (P Q : nat -> bool) s k (m : mfixpoint term) :
  All (fun d => ofv_inv d.(dtype) × ofv_inv d.(dbody)) m ->
  (forall i, on_free_vars P (s i) -> Q i) ->
  forallb (fun d => on_free_vars P (dtype d) && on_free_vars (shiftnP k P) (dbody d))
    (map (map_def (inst s) (inst (up k s))) m) ->
  forallb (fun d => on_free_vars Q (dtype d) && on_free_vars (shiftnP k Q) (dbody d)) m.
Proof.
  induction 1 as [|d m [hd hb] hm ih]; cbn; intros Hs h; [reflexivity|].
  apply andb_prop in h as [hdb h]. apply andb_prop in hdb as [h1 h2].
  rewrite (hd _ _ _ Hs h1), (hb _ (shiftnP k Q) _ (on_free_vars_up_inv _ _ k _ Hs) h2),
    (ih Hs h). reflexivity.
Qed.

(** The converse of [on_free_vars_inst]: a variable of [t] that [t.[s]] keeps maps to a
  term [P] accepts. *)
Lemma on_free_vars_inst_inv (P Q : nat -> bool) s t :
  (forall i, on_free_vars P (s i) -> Q i) ->
  on_free_vars P (inst s t) -> on_free_vars Q t.
Proof.
  intros Hs Ht.
  induction t in P, Q, s, Hs, Ht |- * using term_forall_list_ind; cbn in *; try easy.
  all: try unfold test_def in *.
  all: try solve [solve_all; eauto using on_free_vars_up_inv].
  - (* tCase *)
    destruct X as (Xpar & _ & Xret). rewrite length_map in Ht.
    apply andb_prop in Ht as [h1 Ht]. apply andb_prop in Ht as [h2 Ht].
    apply andb_prop in Ht as [h3 Ht]. apply andb_prop in Ht as [h4 h5].
    rewrite (forallb_inst_inv _ _ _ _ Xpar Hs h1),
      (Xret _ _ _ (on_free_vars_up_inv _ _ _ _ Hs) h2), h3, (IHt _ _ _ Hs h4).
    cbn [andb]. rewrite forallb_map in h5. clear -X0 h5 Hs.
    induction X0 as [|br l [_ hb] X0 ih]; cbn in *; [reflexivity|].
    apply andb_prop in h5 as [hb5 h5]. apply andb_prop in hb5 as [hc hbb].
    rewrite hc, (hb _ _ _ (on_free_vars_up_inv _ _ _ _ Hs) hbb), (ih h5). reflexivity.
  - (* tFix *) rewrite length_map in Ht. exact (fix_inst_inv _ _ _ _ _ X Hs Ht).
  - (* tCoFix *) rewrite length_map in Ht. exact (fix_inst_inv _ _ _ _ _ X Hs Ht).
Qed.

Lemma unlift_lift0 n x : rename (unlift_renaming n 0) (lift0 n x) = x.
Proof.
  rewrite lift_rename, rename_compose, (rename_ext _ ren_id (lift_unlift n 0)).
  apply rename_ren_id.
Qed.

Lemma lift0_inj n a b : lift0 n a = lift0 n b -> a = b.
Proof.
  intros h. transitivity (rename (unlift_renaming n 0) (lift0 n a)).
  - symmetry. apply unlift_lift0.
  - rewrite h. apply unlift_lift0.
Qed.

(** A term without the variables below [n] is the lift of its unlift. *)
Lemma lift_clean n x :
  on_free_vars (strengthenP 0 n xpredT) x -> lift0 n (rename (unlift_renaming n 0) x) = x.
Proof.
  intros hx. rewrite lift_rename, rename_compose.
  rewrite (rename_ext_cond (strengthenP 0 n xpredT)
             (lift_renaming n 0 ∘ unlift_renaming n 0) ren_id x);
    [now rewrite rename_ren_id| |exact hx].
  intros i hi. unfold strengthenP in hi. cbn in hi.
  destruct (Nat.ltb_spec i n) as [hlt|hge]; [discriminate hi|].
  cbv beta. unfold lift_renaming, unlift_renaming, ren_id. cbn.
  destruct (Nat.leb_spec 0 (i - n)); lia.
Qed.

Lemma hyg_rename g x : on_free_vars xpredT x -> on_free_vars xpredT (rename g x).
Proof.
  intros h. rewrite on_free_vars_rename. eapply on_free_vars_impl; [|exact h].
  intros; reflexivity.
Qed.

(** The unlift of a reading through an environment is the reading through the unlifted
  slots, at the lower level. *)
Lemma rename_susp m K' n ts t :
  #|ts| = n ->
  rename (unlift_renaming m 0) (subst ts 0 (lift (m + K') n t))
  = subst (map (rename (unlift_renaming m 0)) ts) 0 (lift K' n t).
Proof.
  intros hl. rewrite rename_subst0, hl. f_equal.
  rewrite !lift_rename, rename_compose. apply rename_ext. intros i.
  cbv beta. unfold shiftn, lift_renaming, unlift_renaming.
  destruct (Nat.leb_spec n i) as [h1|h1].
  - destruct (Nat.ltb_spec (m + K' + i) n); [lia|].
    destruct (Nat.ltb_spec (m + K' + i - n) 0); [lia|]. lia.
  - destruct (Nat.ltb_spec i n); [reflexivity|lia].
Qed.

(** Every slot a code uses through a reading without low variables is itself without low
  variables. *)
Lemma live_vars m n K K' ts t :
  #|ts| = n ->
  on_free_vars (strengthenP 0 m xpredT) (subst ts 0 (lift K n t)) ->
  on_free_vars (fun i => (n <=? i)
                  || on_free_vars (strengthenP 0 m xpredT) (subst_consn ts ids i))
    (lift K' n t).
Proof.
  intros hl h. rewrite subst0_inst in h.
  apply (on_free_vars_inst_inv _
           (fun i => on_free_vars (strengthenP 0 m xpredT) (subst_consn ts ids i)) _ _
           (fun i hi => hi)) in h.
  rewrite lift_rename, on_free_vars_rename in h. rewrite lift_rename, on_free_vars_rename.
  eapply on_free_vars_impl; [|exact h]. intros j hj. cbv beta in *. unfold lift_renaming in *.
  destruct (Nat.leb_spec n j).
  - apply orb_true_intro; left. apply Nat.leb_le. lia.
  - apply orb_true_intro; right. exact hj.
Qed.

Lemma subst_ext_live (ws ws' : list term) T (live : nat -> bool) :
  #|ws| = #|ws'| ->
  (forall i x x', live i -> nth_error ws i = Some x -> nth_error ws' i = Some x' -> x = x') ->
  on_free_vars (fun i => (#|ws| <=? i) || live i) T ->
  subst ws 0 T = subst ws' 0 T.
Proof.
  intros hl hx hT. rewrite !subst0_inst. eapply inst_ext_cond; [|exact hT].
  intros i hi. destruct (Nat.ltb_spec i #|ws|) as [hlt|hge].
  - apply orb_prop in hi as [hi|hi]; [apply Nat.leb_le in hi; lia|].
    destruct (subst_consn_lt_spec hlt) as [x [hx1 hx2]].
    assert (hlt' : i < #|ws'|) by lia.
    destruct (subst_consn_lt_spec hlt') as [x' [hx1' hx2']].
    rewrite hx2, hx2'. exact (hx i x x' hi hx1 hx1').
  - rewrite !subst_consn_ge by lia. rewrite hl. reflexivity.
Qed.

Lemma lift_mkApps_inv n ts : forall w h, lift0 n w = mkApps h ts ->
  exists w0 ws, w = mkApps w0 ws /\ lift0 n w0 = h /\ map (lift0 n) ws = ts.
Proof.
  induction ts as [|x ts ih] using rev_ind; intros w h e.
  - exists w, []. cbn in *. auto.
  - rewrite mkApps_app in e. cbn in e.
    assert (hw : exists w1 w2, w = tApp w1 w2)
      by (destruct w; cbn in e; try discriminate e; eauto).
    destruct hw as (w1 & w2 & ->). cbn in e. injection e as e1 e2.
    destruct (ih _ _ e1) as (w0 & ws & -> & e3 & e4).
    exists w0, (ws ++ [w2]). rewrite mkApps_app, map_app, e4. cbn. rewrite e2. auto.
Qed.

Lemma untyped_subslet_jctx Ξ (l : list term) : untyped_subslet Ξ l (jctx #|l|).
Proof. induction l as [|t l ih]; cbn; constructor. exact ih. Qed.

(** ** The read-back *)

Section ReadBack.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat) (Σ : global_env_ext).
  Context (wfΣ : wf Σ) (hΓ : is_closed_context Γ) (hhyg : ctx_hyg Γ).
  Context (L Q : nat) (lo : positive) (G : ghost) (s0 : cbn_state).
  Context (hm : minv X_type X Γ nctx Σ L Q lo G s0).

  Local Notation ren := (rename (unlift_renaming (Q - L) 0)).
  Local Notation clean := (on_free_vars (strengthenP 0 (Q - L) xpredT)).

  #[local] Lemma hL : nctx <= L. Proof. destruct hm as [h _ _ _]. exact h. Qed.
  #[local] Lemma hQ : L <= Q. Proof. destruct hm as [_ h _ _]. exact h. Qed.
  #[local] Lemma hok0 : gok X_type X Γ nctx Σ (jctx (Q - nctx)) Q lo G s0.
  Proof. destruct hm as [_ _ h _]. exact h. Qed.
  #[local] Lemma hw0 : hwf Q s0. Proof. destruct hm as [_ _ _ h]. exact h. Qed.

  (** The state a read-back leaves: [s0] up to [st_steps] (and [st_room]). *)
  #[local] Definition same (s : cbn_state) : Prop :=
    s.(st_heap) = s0.(st_heap) /\ s.(st_next) = s0.(st_next)
    /\ s.(st_gam) = s0.(st_gam) /\ s.(st_memo) = s0.(st_memo).

  Lemma same_tick s s1 : same s -> tick s = Some s1 -> same s1.
  Proof.
    intros (e1 & e2 & e3 & e4) ht. destruct (tick_shape s s1 ht) as (f1 & f2 & _ & f3 & f4).
    split; [congruence|]. split; [congruence|]. split; congruence.
  Qed.

  Lemma same_heap s a : same s -> heap_get a s = heap_get a s0.
  Proof. intros (e1 & _). unfold heap_get. rewrite e1. reflexivity. Qed.

  #[local] Definition rL (w u : term) : Prop := ∥ red Σ (Γ ,,, jctx (L - nctx)) w u ∥.

  (** A reading at [Q] and a read-back at [L]: when the reading is a lift of a hygienic
    logical term, the read-back is a reduct of it. *)
  #[local] Definition lrel (t u : term) : Prop :=
    forall w, t = lift0 (Q - L) w -> on_free_vars xpredT w -> rL w u.

  Lemma rL_refl w : rL w w.
  Proof. constructor. apply refl_red. Qed.

  Lemma ctxL_xpredT k : on_ctx_free_vars xpredT ((Γ ,,, jctx (L - nctx)) ,,, jctx k).
  Proof. rewrite <- app_context_assoc, <- jctx_add. apply master_ctx_xpredT. exact hΓ. Qed.

  Lemma ctxL_xpredT0 : on_ctx_free_vars xpredT (Γ ,,, jctx (L - nctx)).
  Proof. apply master_ctx_xpredT. exact hΓ. Qed.

  (** *** Hygiene of the readings *)

  Lemma G_hyg : hygG G.
  Proof. intros a t h. exact (gk_hyg _ _ _ _ _ _ _ _ _ _ hok0 hhyg a t h). Qed.

  Lemma code_hyg : codes_hyg G.
  Proof. exact (gok_codes_hyg _ _ _ _ _ _ _ _ _ _ hok0 hhyg). Qed.

  Lemma slots_hyg l ts : g_slots nctx Q G l ts -> forallb (on_free_vars xpredT) ts.
  Proof. exact (proj2 (g_slot_hyg nctx Q G G_hyg code_hyg) l ts). Qed.

  Lemma closed_hyg h : closedn 0 h -> on_free_vars xpredT h.
  Proof.
    intros hc. eapply on_free_vars_impl; [|exact (closedn_on_free_vars (P := xpredT) hc)].
    intros; reflexivity.
  Qed.

  (** *** Heads and spines *)

  Lemma lrel_closed h : closedn 0 h -> lrel h h.
  Proof.
    intros hc w e _. rewrite <- (lift_closed (Q - L) 0 h hc) in e.
    rewrite (lift0_inj _ _ _ (eq_sym e)). apply rL_refl.
  Qed.

  Lemma Forall2_lrel_red ws us :
    forallb (on_free_vars xpredT) ws -> Forall2 lrel (map (lift0 (Q - L)) ws) us ->
    ∥ All2 (red Σ (Γ ,,, jctx (L - nctx))) ws us ∥.
  Proof.
    revert us. induction ws as [|w ws ih]; intros us hws h; cbn in h.
    - inversion h; subst. constructor. constructor.
    - inversion h as [|a b la lb hab hl]; subst.
      cbn in hws. apply andb_prop in hws as [hw hws].
      destruct (hab w eq_refl hw) as [hr]. destruct (ih _ hws hl) as [hall].
      constructor. constructor; assumption.
  Qed.

  Lemma lrel_app h hu ts us :
    lrel h hu -> Forall2 lrel ts us -> lrel (mkApps h ts) (mkApps hu us).
  Proof.
    intros hh hts w e hw.
    destruct (lift_mkApps_inv _ ts w h (eq_sym e)) as (w0 & ws & -> & e0 & e1).
    rewrite on_free_vars_mkApps in hw. apply andb_prop in hw as [hw0 hws].
    destruct (hh w0 (eq_sym e0) hw0) as [hr].
    subst ts. destruct (Forall2_lrel_red ws us hws hts) as [hall].
    constructor. apply red_mkApps; assumption.
  Qed.

  (** *** The four functions, by the fuel *)

  Definition Pcell (d : cbn_fuel) : Prop := forall a s u s', same s ->
    rb_cell nctx d L a s = COk (u, s') ->
    same s' /\ on_free_vars xpredT u /\ forall t, G a = Some t -> lrel t u.

  Definition Pslot (d : cbn_fuel) : Prop := forall x s u s' tx, same s ->
    g_slot nctx Q G x tx -> rb_slot nctx d L x s = COk (u, s') ->
    same s' /\ on_free_vars xpredT u /\ lrel tx u.

  Definition Psusp (d : cbn_fuel) : Prop := forall e t s u s' tx, same s ->
    on_free_vars xpredT t -> g_susp nctx Q G e t tx -> rb_susp nctx d L e t s = COk (u, s') ->
    same s' /\ on_free_vars xpredT u /\ lrel tx u.

  Definition Pvalue (d : cbn_fuel) : Prop := forall v s u s' tv, same s ->
    vwf Q v -> g_value nctx Q G v tv -> rb_value nctx d L v s = COk (u, s') ->
    same s' /\ on_free_vars xpredT u /\ lrel tv u.

  Lemma spine_ok d : Pcell d -> forall sp ts s us s', same s -> g_addrs G sp ts ->
    map_st (rb_cell nctx d L) sp s = COk (us, s') ->
    same s' /\ forallb (on_free_vars xpredT) us /\ Forall2 lrel ts us.
  Proof.
    intros IH sp. induction sp as [|a sp ih]; intros ts s us s' hs ha E; cbn in E.
    - injection E as <- <-. inversion ha; subst. split; [exact hs|]. split; constructor.
    - inversion ha as [|a' t sp' ts' hat hsp]; subst.
      destruct (rb_cell nctx d L a s) as [[y s1]|w] eqn:E1; [|discriminate E].
      destruct (map_st (rb_cell nctx d L) sp s1) as [[ys s2]|w] eqn:E2; [|discriminate E].
      injection E as <- <-.
      destruct (IH _ _ _ _ hs E1) as (hs1 & hy & hry).
      destruct (ih _ _ _ _ hs1 hsp E2) as (hs2 & hys & hrys).
      split; [exact hs2|]. split; [cbn; rewrite hy, hys; reflexivity|].
      constructor; [exact (hry t hat)|exact hrys].
  Qed.

  Lemma slots_ok d : Pslot d -> forall l ts s us s', same s -> g_slots nctx Q G l ts ->
    map_st (rb_slot nctx d L) l s = COk (us, s') ->
    same s' /\ forallb (on_free_vars xpredT) us /\ Forall2 lrel ts us.
  Proof.
    intros IH l. induction l as [|x l ih]; intros ts s us s' hs hl E; cbn in E.
    - injection E as <- <-. inversion hl; subst. split; [exact hs|]. split; constructor.
    - inversion hl as [|x' t l' ts' hx hl']; subst.
      destruct (rb_slot nctx d L x s) as [[y s1]|w] eqn:E1; [|discriminate E].
      destruct (map_st (rb_slot nctx d L) l s1) as [[ys s2]|w] eqn:E2; [|discriminate E].
      injection E as <- <-.
      destruct (IH _ _ _ _ _ hs hx E1) as (hs1 & hy & hry).
      destruct (ih _ _ _ _ hs1 hl' E2) as (hs2 & hys & hrys).
      split; [exact hs2|]. split; [cbn; rewrite hy, hys; reflexivity|].
      constructor; [exact hry|exact hrys].
  Qed.

  (** The used slots move by their read-backs, the unused ones are replaced by them. *)
  Lemma build_ws (ts us : list term) :
    forallb (on_free_vars xpredT) ts -> forallb (on_free_vars xpredT) us ->
    Forall2 lrel ts us ->
    exists ws', ∥ All2 (red Σ (Γ ,,, jctx (L - nctx))) ws' us ∥
      /\ forallb (on_free_vars xpredT) ws' /\ #|ws'| = #|ts|
      /\ forall i t x, nth_error ts i = Some t -> clean t -> nth_error ws' i = Some x ->
           x = ren t.
  Proof.
    intros hts hus h. induction h as [|t u ts us htu htl ih]; cbn in hts, hus.
    - exists []. split; [constructor; constructor|]. split; [reflexivity|].
      split; [reflexivity|]. intros i t x _ _ hx. destruct i; discriminate hx.
    - apply andb_prop in hts as [ht hts]. apply andb_prop in hus as [hu hus].
      destruct (ih hts hus) as (ws & [hall] & hws & hl & hnth).
      destruct (clean t) eqn:ec.
      + assert (hr : rL (ren t) u).
        { apply htu; [symmetry; apply lift_clean; exact ec|apply hyg_rename; exact ht]. }
        destruct hr as [hr]. exists (ren t :: ws).
        split; [constructor; constructor; assumption|].
        split; [cbn; rewrite (hyg_rename _ _ ht), hws; reflexivity|].
        split; [cbn; congruence|].
        intros [|i] t' x hti hc hx; cbn in hti, hx.
        * injection hti as <-. injection hx as <-. reflexivity.
        * exact (hnth i t' x hti hc hx).
      + exists (u :: ws). split; [constructor; constructor; [apply refl_red|assumption]|].
        split; [cbn; rewrite hu, hws; reflexivity|]. split; [cbn; congruence|].
        intros [|i] t' x hti hc hx; cbn in hti, hx.
        * injection hti as <-. rewrite ec in hc. discriminate hc.
        * exact (hnth i t' x hti hc hx).
  Qed.

  Lemma susp_step k : Pslot (k tt) -> Psusp (FS k).
  Proof.
    intros IH e t s u s' tx hs ht hsu E. cbn [rb_susp] in E.
    destruct (tick s) as [s1|] eqn:Et; [|discriminate E].
    destruct (map_st (rb_slot nctx (k tt) L) e.(ev_vals) s1) as [[us s2]|w] eqn:Em;
      [|discriminate E].
    injection E as <- <-.
    apply g_susp_inv in hsu as (ts & hts & hn & ->).
    destruct (slots_ok _ IH _ _ _ _ _ (same_tick _ _ hs Et) hts Em) as (hs2 & hus & hF).
    pose proof (slots_hyg _ _ hts) as htsh.
    pose proof (g_slots_length _ _ _ _ _ hts) as hlt.
    pose proof (Forall2_length hF) as hlu.
    split; [exact hs2|]. split.
    { apply hyg_subst; [exact hus|apply hyg_lift; exact ht]. }
    set (n := ev_nvals e) in *. set (K' := L - nctx + ev_goff e).
    assert (hK : Q - nctx + ev_goff e = (Q - L) + K')
      by (pose proof hL; pose proof hQ; unfold K'; lia).
    rewrite hK. intros w hwe hw.
    assert (hlen : #|ts| = n) by (rewrite hlt, hn; reflexivity).
    assert (hwr : w = subst (map ren ts) 0 (lift K' n t)).
    { rewrite <- (unlift_lift0 (Q - L) w), <- hwe. apply rename_susp. exact hlen. }
    assert (hocc := live_vars (Q - L) n ((Q - L) + K') K' ts t hlen
                      ltac:(rewrite hwe, on_free_vars_lift; exact hw)).
    destruct (build_ws ts us htsh hus hF) as (ws' & [hall] & hws' & hl' & hnth).
    assert (hext : subst (map ren ts) 0 (lift K' n t) = subst ws' 0 (lift K' n t)).
    { apply (subst_ext_live _ _ _
               (fun i => clean (subst_consn ts ids i))).
      - rewrite length_map, hl'. reflexivity.
      - intros i x x' hli hx hx'. rewrite nth_error_map in hx.
        destruct (nth_error ts i) as [ti|] eqn:Eti; cbn in hx; [|discriminate hx].
        injection hx as <-. unfold subst_consn in hli. rewrite Eti in hli.
        symmetry. exact (hnth i ti x' Eti hli hx').
      - rewrite length_map, hlen. exact hocc. }
    rewrite hwr, hext. constructor.
    assert (hons : All (on_free_vars (addnP (#|@nil context_decl| + #|jctx n|) xpredT)) ws').
    { apply forallb_All in hws'. eapply All_impl; [exact hws'|].
      intros x hx. eapply on_free_vars_impl; [|exact hx]. intros; reflexivity. }
    assert (hsub : untyped_subslet (Γ ,,, jctx (L - nctx)) ws' (jctx n)).
    { rewrite <- hlen, <- hl'. apply untyped_subslet_jctx. }
    exact (red_red (Σ := Σ) (wfΣ := wfΣ) (P := xpredT) (Γ := Γ ,,, jctx (L - nctx))
             (Δ := jctx n) (Γ' := []) (ctxL_xpredT n) (hyg_lift _ _ _ ht) hall hons hsub).
  Qed.

  Lemma cell_step k : Pvalue (k tt) -> Psusp (k tt) -> Pcell (FS k).
  Proof.
    intros IHv IHs a s u s' hs E. cbn [rb_cell] in E.
    rewrite (same_heap _ a hs) in E.
    destruct (heap_get a s0) as [cl|] eqn:Eh; [|discriminate E].
    destruct (gk_cells _ _ _ _ _ _ _ _ _ _ hok0 a cl Eh) as (t0 & hGa & hc).
    destruct cl as [vs n o c|v| |a']; try discriminate E.
    - destruct hc as [hc|(y & hy & hr)]; [discriminate hc|].
      apply g_cell_susp_inv in hy as hy'. pose proof (g_cell_susp_cok _ _ _ _ _ _ _ _ hy) as hcok.
      destruct (IHs _ _ _ _ _ _ hs (code_hyg c hcok) hy' E) as (hs' & hu & hl).
      split; [exact hs'|]. split; [exact hu|].
      intros t ht. rewrite hGa in ht. injection ht as <-.
      intros w -> hw.
      destruct (cred_unlift Γ nctx Σ wfΣ hΓ L Q w y hL hQ hw hr) as (y' & -> & hd).
      destruct (hd _ (jctx_length _)) as [hr1].
      pose proof (PCUICRenameConv.red_on_free_vars ctxL_xpredT0 hw hr1) as hy1.
      destruct (hl y' eq_refl hy1) as [hr2]. constructor. exact (red_trans _ _ _ _ _ hr1 hr2).
    - destruct hc as [hc|(y & hy & hr)]; [discriminate hc|].
      apply g_cell_done_inv in hy.
      pose proof (hw0 a (CDone v) Eh) as hvw. cbn in hvw.
      destruct (IHv _ _ _ _ _ hs hvw hy E) as (hs' & hu & hl).
      split; [exact hs'|]. split; [exact hu|].
      intros t ht. rewrite hGa in ht. injection ht as <-.
      intros w -> hw.
      destruct (cred_unlift Γ nctx Σ wfΣ hΓ L Q w y hL hQ hw hr) as (y' & -> & hd).
      destruct (hd _ (jctx_length _)) as [hr1].
      pose proof (PCUICRenameConv.red_on_free_vars ctxL_xpredT0 hw hr1) as hy1.
      destruct (hl y' eq_refl hy1) as [hr2]. constructor. exact (red_trans _ _ _ _ _ hr1 hr2).
  Qed.

  Lemma slot_step k : Pcell (k tt) -> Psusp (k tt) -> Pslot (FS k).
  Proof.
    intros IHc IHs x s u s' tx hs hx E. cbn [rb_slot] in E.
    destruct x as [a|vs n o c].
    - apply g_slot_addr_inv in hx.
      destruct (IHc _ _ _ _ hs E) as (hs' & hu & hl).
      split; [exact hs'|]. split; [exact hu|]. exact (hl tx hx).
    - pose proof (g_slot_inl_cok _ _ _ _ _ _ _ _ hx) as hcok.
      apply g_slot_inl_inv in hx.
      exact (IHs _ _ _ _ _ _ hs (code_hyg c hcok) hx E).
  Qed.

  Lemma value_step k : Pcell (k tt) -> Psusp (k tt) -> Pvalue (FS k).
  Proof.
    intros IHc IHs v s u s' tv hs hvw hv E. cbn [rb_value] in E.
    destruct v as [h sp|e c|e c i sp|e c i sp|[l|h] sp|e c|e c sp].
    - (* VCon *)
      destruct (map_st (rb_cell nctx (k tt) L) sp s) as [[us s1]|w] eqn:Em; [|discriminate E].
      injection E as <- <-. cbn in hvw.
      apply g_value_VCon_inv in hv as (ts & -> & hts).
      destruct (spine_ok _ IHc _ _ _ _ _ hs hts Em) as (hs1 & hus & hF).
      split; [exact hs1|]. split; [apply hyg_mkApps; [exact (closed_hyg h hvw)|exact hus]|].
      exact (lrel_app _ _ _ _ (lrel_closed h hvw) hF).
    - (* VLam *)
      pose proof (g_value_VLam_cok _ _ _ _ _ _ hv) as hcok.
      apply g_value_VLam_inv in hv.
      exact (IHs _ _ _ _ _ _ hs (code_hyg c hcok) hv E).
    - (* VFix *)
      apply g_value_VFix_inv in hv as (mfix & idx & hh & ts & hct & hsu & hcok & hts & ->).
      rewrite hct in E.
      destruct (rb_susp nctx (k tt) L e (tFix mfix i) s) as [[hu s1]|w] eqn:E1;
        [|discriminate E].
      destruct (map_st (rb_cell nctx (k tt) L) sp s1) as [[us s2]|w] eqn:Em; [|discriminate E].
      injection E as <- <-.
      assert (hf : on_free_vars xpredT (tFix mfix i)).
      { eapply hyg_tFix_idx. rewrite <- hct. exact (code_hyg c hcok). }
      destruct (IHs _ _ _ _ _ _ hs hf hsu E1) as (hs1 & hhu & hlh).
      destruct (spine_ok _ IHc _ _ _ _ _ hs1 hts Em) as (hs2 & hus & hF).
      split; [exact hs2|]. split; [apply hyg_mkApps; assumption|].
      exact (lrel_app _ _ _ _ hlh hF).
    - (* VStuckFix *)
      apply g_value_VStuckFix_inv in hv as (mfix & idx & hh & ts & hct & hsu & hcok & hts & ->).
      rewrite hct in E.
      destruct (rb_susp nctx (k tt) L e (tFix mfix i) s) as [[hu s1]|w] eqn:E1;
        [|discriminate E].
      destruct (map_st (rb_cell nctx (k tt) L) sp s1) as [[us s2]|w] eqn:Em; [|discriminate E].
      injection E as <- <-.
      assert (hf : on_free_vars xpredT (tFix mfix i)).
      { eapply hyg_tFix_idx. rewrite <- hct. exact (code_hyg c hcok). }
      destruct (IHs _ _ _ _ _ _ hs hf hsu E1) as (hs1 & hhu & hlh).
      destruct (spine_ok _ IHc _ _ _ _ _ hs1 hts Em) as (hs2 & hus & hF).
      split; [exact hs2|]. split; [apply hyg_mkApps; assumption|].
      exact (lrel_app _ _ _ _ hlh hF).
    - (* VNeu (NVar l) *)
      destruct (map_st (rb_cell nctx (k tt) L) sp s) as [[us s1]|w] eqn:Em; [|discriminate E].
      injection E as <- <-. cbn in hvw.
      apply g_value_VNeu_inv in hv as [(l' & ts & el & -> & hts)|(h & ts & el & _)];
        [|discriminate el].
      injection el as <-.
      destruct (spine_ok _ IHc _ _ _ _ _ hs hts Em) as (hs1 & hus & hF).
      split; [exact hs1|]. split; [apply hyg_mkApps; [reflexivity|exact hus]|].
      apply lrel_app; [|exact hF].
      intros w0 e0 _.
      assert (hw : exists j, w0 = tRel j)
        by (destruct w0; cbn in e0; try discriminate e0; eauto).
      destruct hw as (j & ->). cbn in e0. injection e0 as e0.
      pose proof hQ. replace (L - S l) with j by lia. apply rL_refl.
    - (* VNeu (NConst h) *)
      destruct (map_st (rb_cell nctx (k tt) L) sp s) as [[us s1]|w] eqn:Em; [|discriminate E].
      injection E as <- <-. cbn in hvw.
      apply g_value_VNeu_inv in hv as [(l' & ts & el & _)|(h' & ts & el & -> & hts)];
        [discriminate el|].
      injection el as <-.
      destruct (spine_ok _ IHc _ _ _ _ _ hs hts Em) as (hs1 & hus & hF).
      split; [exact hs1|]. split; [apply hyg_mkApps; [exact (closed_hyg h hvw)|exact hus]|].
      exact (lrel_app _ _ _ _ (lrel_closed h hvw) hF).
    - (* VOpen *)
      assert (hcok : PCUICCallByNeedSoundEval.cok G c) by (inversion hv; subst; assumption).
      apply g_value_VOpen_inv in hv.
      exact (IHs _ _ _ _ _ _ hs (code_hyg c hcok) hv E).
    - (* VStuck *)
      pose proof (g_value_VStuck_cok _ _ _ _ _ _ _ hv) as hcok.
      apply g_value_VStuck_inv in hv as (hh & ts & hsu & hts & ->).
      destruct (rb_susp nctx (k tt) L e c.(c_term) s) as [[hu s1]|w] eqn:E1;
        [|discriminate E].
      destruct (map_st (rb_cell nctx (k tt) L) sp s1) as [[us s2]|w] eqn:Em; [|discriminate E].
      injection E as <- <-.
      destruct (IHs _ _ _ _ _ _ hs (code_hyg c hcok) hsu E1) as (hs1 & hhu & hlh).
      destruct (spine_ok _ IHc _ _ _ _ _ hs1 hts Em) as (hs2 & hus & hF).
      split; [exact hs2|]. split; [apply hyg_mkApps; assumption|].
      exact (lrel_app _ _ _ _ hlh hF).
  Qed.

  Lemma rb_main d : Pcell d /\ Pslot d /\ Psusp d /\ Pvalue d.
  Proof.
    induction d as [|k ih].
    - split; [|split; [|split]].
      + intros a s u s' _ E. cbn in E. discriminate E.
      + intros x s u s' tx _ _ E. cbn in E. discriminate E.
      + intros e t s u s' tx _ _ _ E. cbn in E. discriminate E.
      + intros v s u s' tv _ _ _ E. cbn in E. discriminate E.
    - destruct (ih tt) as (IHc & IHs & IHu & IHv).
      split; [exact (cell_step k IHv IHu)|].
      split; [exact (slot_step k IHc IHu)|].
      split; [exact (susp_step k IHs)|exact (value_step k IHc IHu)].
  Qed.
End ReadBack.

(** ** The interface of the read-back holds

  Its premises [wf Σ], [is_closed_context Γ] and [ctx_hyg Γ] are section hypotheses of
  [PCUICCallByNeedSoundLevel]; their instances are
  [PCUICCallByNeedSoundLevel.level_ctx_instance_nil], [level_ctx_instance_one] and
  [PCUICCallByNeedSoundEval.eval_env_instance]. *)
Theorem rb_sound_holds {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1)
    (Γ : context) (nctx : nat) (Σ : global_env_ext) :
  wf Σ -> is_closed_context Γ -> ctx_hyg Γ -> rb_sound X_type X Γ nctx Σ.
Proof.
  intros wfΣ hΓ hhyg d L Q lo G e t v s hm ht hv hs u s' E.
  assert (hs0 : same s s) by (repeat split).
  destruct (proj1 (proj2 (proj2 (rb_main X_type X Γ nctx Σ wfΣ hΓ hhyg L Q lo G s hm d)))
              e t s u s' _ hs0 ht hs E) as ((e1 & e2 & e3 & e4) & _ & hl).
  split.
  - eapply minv_same; [exact hm|exact e1|exact e2|exact e3|exact e4].
  - intros Δ hΔ. destruct (hl v eq_refl hv) as [hr]. constructor.
    exact (red_assum_irrel Σ Γ (jctx (L - nctx)) Δ v u
             ltac:(rewrite jctx_length; lia) (jctx_assum _) hr).
Qed.

(** The satisfying instance of [rb_sound_holds]'s premises at the empty context: every
  hypothesis discharged, for any [Σ] with [wf Σ]. *)
Corollary rb_sound_nil {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1)
    (Σ : global_env_ext) : wf Σ -> rb_sound X_type X [] 0 Σ.
Proof.
  intros wfΣ. destruct (level_ctx_instance_nil Σ) as (_ & _ & hΓ & hhyg & _).
  exact (rb_sound_holds X_type X [] 0 Σ wfΣ hΓ hhyg).
Qed.
