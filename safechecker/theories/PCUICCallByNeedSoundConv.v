(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require String2pos CanonicalTries.
From MetaRocq.Common Require Import config Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICTyping PCUICEquality PCUICCumulativity PCUICOnFreeVars
  PCUICClosed PCUICSubstitution PCUICContexts PCUICWfUniverses
  PCUICWellScopedCumulativity PCUICConversion.
From MetaRocq.SafeChecker Require Import PCUICEqualityDec PCUICWfEnv PCUICCallByNeed
  PCUICCallByNeedSound PCUICCallByNeedSoundGC PCUICCallByNeedSoundCtx
  PCUICCallByNeedSoundMemo PCUICCallByNeedSoundCong.

Import CanonicalTries.

Set Default Goal Selector "1".

Local Notation key := String2pos.positive.

(** * BET-298 step 3: the comparison's non-evaluating rules

  The comparison of [PCUICCallByNeed] is the mutual block [conv_slot], [conv_eval],
  [conv_term], [conv_same_code], [same_code_cells], [case_cong], [case_params],
  [case_branches], [conv_rows], [conv_value], [conv_cells]. Each function answers
  [COk (true, _, _)] for "convertible", [COk (false, _, _)] for "this rule does not apply,
  try the next one" and [CFail w] for "give up". Only the [true] answer is a claim, so every
  lemma here has the shape "if the function answers [true] then the two readings are
  convertible at the comparison's [conv_pb]"; nothing is said of [false], which is only a
  loss of speed.

  This file holds the rules that answer *without forcing a value*, so none of them depends
  on the evaluator theorem:

  - **Same code** ([conv_same_code], [same_code_cells]). Two suspensions of the same code
    under two environments are convertible when the environment slots the code can see are
    pairwise convertible. The machine skips a slot whose two sides are the same address, and
    a slot whose index does not occur in the code ([noccur_between i 1 t]). The PCUIC content
    is [PCUICCallByNeedSoundCong.ws_cumul_pb_subst_lift], whose shape
    [subst ts 0 (lift (lvl - nctx + goff) nvals t)] is the read-back's own; the skipped
    positions are handled by [subst_noccur_irrel], which says that a substitution does not
    look at an index the term does not use.
  - **The identifier fast path.** [same_id c1 c2 = true] with both codes satisfying
    [code_inv] for entries of one table gives [c_term c1 = c_term c2]
    ([PCUICCallByNeed.same_id_sound_table]), so the same-code rule is sound with no term
    comparison at all, and in particular with no universe check:
    [conv_same_code_sound_same_id] below carries no [wf_universes] hypothesis.
  - **Stuck match** ([case_cong], [case_params], [case_branches]). Two stuck [tCase]s with
    convertible scrutinees, pairwise convertible parameters, convertible return clauses and
    pairwise convertible branch bodies, through [ws_cumul_pb_tCase] and [case_ctx_ok_spec].

  **The seam with the evaluator.** Everything the comparison reaches through [conv_eval]
  needs the evaluator theorem, which another task owns. It enters here in exactly two
  places, [conv_slot] (called by [same_code_cells]) and [conv_term] (called by
  [case_params], [case_cong] and [case_branches]), and both are taken as the explicit
  hypotheses [slot_seam] and [term_seam] below. They are the only hypotheses of this file
  that are not discharged in it.

  Readings are [PCUICCallByNeedSound]'s relational read-back, not the machine's partial
  [rb_*] functions, so the lemmas compose with the collector ([PCUICCallByNeedSoundGC]) and
  the call frame ([PCUICCallByNeedSoundCtx]). Conversion is squashed ([∥ _ ∥]) because
  [ws_cumul_pb] lives in [Type] and the read-back in [Prop]; that is also the shape of the
  hook's obligation ([PCUICTypeChecker.v:467]: [∥ Σ ;;; Γ ⊢ t ≤[le] u ∥]). *)

(** ** Shape well-formedness of the machine's structures

  What the level shift needs: a [VNeu (NVar l)] names a level already in scope, the head of
  a [VCon] or a [VNeu (NConst h)] is closed (it is a [tConstruct], [tInd] or [tConst]), and
  every environment records its own length. *)

Inductive slot_wf : cbn_slot -> Prop :=
| slot_wf_addr a : slot_wf (SAddr a)
| slot_wf_inl vals nvals goff c :
    nvals = #|vals| -> slots_wf vals -> slot_wf (SInl vals nvals goff c)
with slots_wf : list cbn_slot -> Prop :=
| slots_wf_nil : slots_wf []
| slots_wf_cons x l : slot_wf x -> slots_wf l -> slots_wf (x :: l).

Definition env_wf (e : cbn_env) : Prop :=
  e.(ev_nvals) = #|e.(ev_vals)| /\ slots_wf e.(ev_vals).

Definition value_wf (lvl : nat) (v : cbn_value) : Prop :=
  match v with
  | VNeu (NVar l) _ => l < lvl
  | VNeu (NConst h) _ => closedn 0 h
  | VCon h _ => closedn 0 h
  | VLam e _ | VOpen e _ => env_wf e
  | VStuck e _ _ => env_wf e
  | VFix e _ _ _ | VStuckFix e _ _ _ => env_wf e
  end.

Definition cell_wf (lvl : nat) (cl : cbn_cell) : Prop :=
  match cl with
  | CSusp vals nvals goff c => nvals = #|vals| /\ slots_wf vals
  | CDone v => value_wf lvl v
  | CBusy | CFwd _ => True
  end.

Definition heap_wf (lvl : nat) (H : bheap cbn_cell) : Prop :=
  forall a cl, bh_get a H = Some cl -> cell_wf lvl cl.

Lemma heap_wf_mono (lvl lvl' : nat) (H : bheap cbn_cell) :
  lvl <= lvl' -> heap_wf lvl H -> heap_wf lvl' H.
Proof.
  intros hle hwf a cl e. specialize (hwf a cl e).
  destruct cl as [vals nvals goff c|v| |a']; try exact hwf.
  destruct v as [h sp|e' c|e' c i sp|e' c i sp|[l|h] sp|e' c|e' c sp]; try exact hwf.
  cbn in *. lia.
Qed.

Lemma repr_slots_length (nctx lvl : nat) (H : bheap cbn_cell) (l : list cbn_slot)
    (ts : list term) :
  repr_slots nctx H lvl l ts -> #|ts| = #|l|.
Proof. induction 1; cbn; congruence. Qed.

(** When the comparison pushes [n] fresh variables it reads the same machine structures at
  level [lvl + n], and each reading is then the old one lifted by [n]. *)
Lemma repr_shift (nctx n lvl : nat) (H : bheap cbn_cell) :
  nctx <= lvl -> heap_wf lvl H ->
  (forall a t, repr_addr nctx H lvl a t -> repr_addr nctx H (lvl + n) a (lift0 n t))
  /\ (forall l ts, repr_addrs nctx H lvl l ts ->
        repr_addrs nctx H (lvl + n) l (map (lift0 n) ts))
  /\ (forall cl t, repr_cell nctx H lvl cl t -> cell_wf lvl cl ->
        repr_cell nctx H (lvl + n) cl (lift0 n t))
  /\ (forall x t, repr_slot nctx H lvl x t -> slot_wf x ->
        repr_slot nctx H (lvl + n) x (lift0 n t))
  /\ (forall l ts, repr_slots nctx H lvl l ts -> slots_wf l ->
        repr_slots nctx H (lvl + n) l (map (lift0 n) ts))
  /\ (forall e t u, repr_susp nctx H lvl e t u -> env_wf e ->
        repr_susp nctx H (lvl + n) e t (lift0 n u))
  /\ (forall v t, repr_value nctx H lvl v t -> value_wf lvl v ->
        repr_value nctx H (lvl + n) v (lift0 n t)).
Proof.
  intros hle hwf.
  (* [repr_mutind] quantifies the level in its motives; every constructor keeps it, so the
     motives pin it to [lvl] by an equation. *)
  enough (G :
    (forall l0 a t, repr_addr nctx H l0 a t -> l0 = lvl ->
       repr_addr nctx H (lvl + n) a (lift0 n t))
    /\ (forall l0 l ts, repr_addrs nctx H l0 l ts -> l0 = lvl ->
       repr_addrs nctx H (lvl + n) l (map (lift0 n) ts))
    /\ (forall l0 cl t, repr_cell nctx H l0 cl t -> l0 = lvl -> cell_wf lvl cl ->
       repr_cell nctx H (lvl + n) cl (lift0 n t))
    /\ (forall l0 x t, repr_slot nctx H l0 x t -> l0 = lvl -> slot_wf x ->
       repr_slot nctx H (lvl + n) x (lift0 n t))
    /\ (forall l0 l ts, repr_slots nctx H l0 l ts -> l0 = lvl -> slots_wf l ->
       repr_slots nctx H (lvl + n) l (map (lift0 n) ts))
    /\ (forall l0 e t u, repr_susp nctx H l0 e t u -> l0 = lvl -> env_wf e ->
       repr_susp nctx H (lvl + n) e t (lift0 n u))
    /\ (forall l0 v t, repr_value nctx H l0 v t -> l0 = lvl -> value_wf lvl v ->
       repr_value nctx H (lvl + n) v (lift0 n t))).
  { destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    split; [intros a t h; exact (G1 _ _ _ h eq_refl)|].
    split; [intros l ts h; exact (G2 _ _ _ h eq_refl)|].
    split; [intros cl t h w; exact (G3 _ _ _ h eq_refl w)|].
    split; [intros x t h w; exact (G4 _ _ _ h eq_refl w)|].
    split; [intros l ts h w; exact (G5 _ _ _ h eq_refl w)|].
    split; [intros e t u h w; exact (G6 _ _ _ _ h eq_refl w)|].
    intros v t h w; exact (G7 _ _ _ h eq_refl w). }
  apply (repr_mutind nctx H
    (fun l0 a t => l0 = lvl -> repr_addr nctx H (lvl + n) a (lift0 n t))
    (fun l0 l ts => l0 = lvl -> repr_addrs nctx H (lvl + n) l (map (lift0 n) ts))
    (fun l0 cl t => l0 = lvl -> cell_wf lvl cl -> repr_cell nctx H (lvl + n) cl (lift0 n t))
    (fun l0 x t => l0 = lvl -> slot_wf x -> repr_slot nctx H (lvl + n) x (lift0 n t))
    (fun l0 l ts => l0 = lvl -> slots_wf l ->
       repr_slots nctx H (lvl + n) l (map (lift0 n) ts))
    (fun l0 e t u => l0 = lvl -> env_wf e -> repr_susp nctx H (lvl + n) e t (lift0 n u))
    (fun l0 v t => l0 = lvl -> value_wf lvl v ->
       repr_value nctx H (lvl + n) v (lift0 n t))).
  - (* repr_addr_intro: the cell's [cell_wf] comes from [heap_wf] *)
    intros l0 a cl t hget _ IH heq; subst l0.
    eapply repr_addr_intro; [exact hget|].
    exact (IH eq_refl (hwf _ _ hget)).
  - (* repr_addrs_nil *)
    intros l0 _. cbn. constructor.
  - (* repr_addrs_cons *)
    intros l0 a l t ts _ IHa _ IHl heq; subst l0. cbn.
    constructor; [exact (IHa eq_refl)|exact (IHl eq_refl)].
  - (* repr_cell_susp *)
    intros l0 vals nvals goff c t _ IH heq hw; subst l0.
    apply repr_cell_susp. exact (IH eq_refl hw).
  - (* repr_cell_done *)
    intros l0 v t _ IH heq hw; subst l0.
    apply repr_cell_done. exact (IH eq_refl hw).
  - (* repr_slot_addr *)
    intros l0 a t _ IH heq _; subst l0.
    apply repr_slot_addr. exact (IH eq_refl).
  - (* repr_slot_inl *)
    intros l0 vals nvals goff c t _ IH heq hw; subst l0.
    apply repr_slot_inl. apply (IH eq_refl).
    inversion hw as [|vals' nvals' goff' c' hn hs]; subst.
    split; [reflexivity|exact hs].
  - (* repr_slots_nil *)
    intros l0 _ _. cbn. constructor.
  - (* repr_slots_cons *)
    intros l0 x l t ts _ IHx _ IHl heq hw; subst l0.
    inversion hw as [|x' l' hx hl]; subst. cbn.
    constructor; [exact (IHx eq_refl hx)|exact (IHl eq_refl hl)].
  - (* repr_susp_intro: lift through the substitution, then merge the two lifts *)
    intros l0 vals nvals goff t ts hs IH heq [hn hws]; subst l0.
    cbn [ev_vals ev_nvals] in hn, hws.
    pose proof (repr_slots_length _ _ _ _ _ hs) as hlen.
    rewrite distr_lift_subst, Nat.add_0_r, hlen, <- hn.
    rewrite simpl_lift by lia.
    replace (n + (lvl - nctx + goff)) with (lvl + n - nctx + goff) by lia.
    apply repr_susp_intro. exact (IH eq_refl hws).
  - (* repr_VCon: the head is closed *)
    intros l0 h sp ts _ IH heq hc; subst l0.
    rewrite lift_mkApps, (lift_closed n 0 h hc).
    apply repr_VCon. exact (IH eq_refl).
  - (* repr_VLam *)
    intros l0 e c t _ IH heq hw; subst l0.
    apply repr_VLam. exact (IH eq_refl hw).
  - (* repr_VOpen *)
    intros l0 e c t _ IH heq hw; subst l0.
    apply repr_VOpen. exact (IH eq_refl hw).
  - (* repr_VFix *)
    intros l0 e c i sp mfix j h ts hc _ IHh _ IHs heq hw; subst l0.
    rewrite lift_mkApps.
    eapply repr_VFix; [exact hc|exact (IHh eq_refl hw)|exact (IHs eq_refl)].
  - (* repr_VStuckFix *)
    intros l0 e c i sp mfix j h ts hc _ IHh _ IHs heq hw; subst l0.
    rewrite lift_mkApps.
    eapply repr_VStuckFix; [exact hc|exact (IHh eq_refl hw)|exact (IHs eq_refl)].
  - (* repr_VNeuVar: the level is in scope *)
    intros l0 l sp ts _ IH heq hl; subst l0.
    cbn [value_wf] in hl.
    rewrite lift_mkApps.
    replace (lift0 n (tRel (lvl - S l))) with (tRel (lvl + n - S l))
      by (rewrite lift_rel_ge by lia; f_equal; lia).
    apply repr_VNeuVar. exact (IH eq_refl).
  - (* repr_VNeuConst: the head is closed *)
    intros l0 h sp ts _ IH heq hc; subst l0.
    rewrite lift_mkApps, (lift_closed n 0 h hc).
    apply repr_VNeuConst. exact (IH eq_refl).
  - (* repr_VStuck *)
    intros l0 e c sp h ts _ IHh _ IHs heq hw; subst l0.
    rewrite lift_mkApps.
    apply repr_VStuck; [exact (IHh eq_refl hw)|exact (IHs eq_refl)].
Qed.

Lemma repr_slots_shift (nctx n lvl : nat) (H : bheap cbn_cell) (l : list cbn_slot)
    (ts : list term) :
  nctx <= lvl -> heap_wf lvl H -> slots_wf l -> repr_slots nctx H lvl l ts ->
  repr_slots nctx H (lvl + n) l (map (lift0 n) ts).
Proof.
  intros hle hwf hl hr.
  destruct (repr_shift nctx n lvl H hle hwf) as (_ & _ & _ & _ & G & _ & _).
  exact (G l ts hr hl).
Qed.

Lemma repr_susp_shift (nctx n lvl : nat) (H : bheap cbn_cell) (e : cbn_env) (t u : term) :
  nctx <= lvl -> heap_wf lvl H -> env_wf e -> repr_susp nctx H lvl e t u ->
  repr_susp nctx H (lvl + n) e t (lift0 n u).
Proof.
  intros hle hwf he hr.
  destruct (repr_shift nctx n lvl H hle hwf) as (_ & _ & _ & _ & _ & G & _).
  exact (G e t u hr he).
Qed.

(** ** Roots: reflexivity and composition of [root_pres]

  [PCUICCallByNeedSoundGC.root_pres] says that a renamed root stands for what the root
  stood for. A step that does not move anything keeps every root, and two steps compose. *)

Lemma root_pres_refl (nctx : nat) (H : bheap cbn_cell) (r : root) :
  root_pres nctx H H r r.
Proof. destruct r; cbn; intros; assumption. Qed.

Lemma root_pres_trans (nctx : nat) (H1 H2 H3 : bheap cbn_cell) (r1 r2 r3 : root) :
  root_pres nctx H1 H2 r1 r2 -> root_pres nctx H2 H3 r2 r3 ->
  root_pres nctx H1 H3 r1 r3.
Proof.
  destruct r1, r2, r3; cbn; intros h1 h2; try contradiction; intros; auto.
Qed.

Lemma Forall2_cons_inv {A B : Type} (R : A -> B -> Prop) (x : A) (l : list A)
    (m : list B) :
  Forall2 R (x :: l) m ->
  exists (y : B) (m' : list B), m = y :: m' /\ R x y /\ Forall2 R l m'.
Proof.
  intros h. inversion h; subst. eexists. eexists.
  split; [reflexivity|]. split; assumption.
Qed.

Lemma roots_pres_refl (nctx : nat) (H : bheap cbn_cell) (rs : list root) :
  Forall2 (root_pres nctx H H) rs rs.
Proof. induction rs; constructor; [apply root_pres_refl|assumption]. Qed.

Lemma roots_pres_trans (nctx : nat) (H1 H2 H3 : bheap cbn_cell) (rs1 rs2 rs3 : list root) :
  Forall2 (root_pres nctx H1 H2) rs1 rs2 -> Forall2 (root_pres nctx H2 H3) rs2 rs3 ->
  Forall2 (root_pres nctx H1 H3) rs1 rs3.
Proof.
  intros h1. revert rs3. induction h1 as [|r1 r2 l1 l2 hr _ ih]; intros rs3 h2;
    inversion h2; subst; constructor.
  - eapply root_pres_trans; eassumption.
  - apply ih. assumption.
Qed.

(** ** Soundness of the machine's syntactic tests

  [cmp_term], [cmp_sort], [cmp_level_conv] and [wf_term_univs] ([PCUICCallByNeed]) and
  [cbn_ceq_term] ([PCUICCallByNeedSoundMemo]) read the abstract environment [X]; here they
  are shown sound for every [Σ] that [X] stands for ([abstract_env_ext_rel X Σ]). The proofs
  replay [PCUICSafeConversion.cmpb_term_correct] and its local lemmas without importing that
  file, whose section assumes [normalization_in] — a hypothesis the fast path must not
  depend on. [wf_term_univs_correct] uses the pointwise congruence [cs_on_universes_ext],
  not functional extensionality. *)

Lemma cs_forallb_ext {A} (f g : A -> bool) (l : list A) :
  (forall x, f x = g x) -> forallb f l = forallb g l.
Proof.
  intros h. induction l as [|x l IH]; cbn; [reflexivity|]. now rewrite h, IH.
Qed.

(** [on_universes] depends only on the values of its universe test. *)
Lemma cs_on_universes_ext (f g : Universe.t -> bool) (fc : nat -> term -> bool) :
  (forall u, f u = g u) -> forall t, on_universes f fc t = on_universes g fc t.
Proof.
  intros hfg t.
  induction t using term_forall_list_ind; cbn.
  - reflexivity.
  - reflexivity.
  - eapply All_forallb_eq_forallb; tea. now intros.
  - destruct s; cbn; auto.
  - congruence.
  - congruence.
  - congruence.
  - congruence.
  - now apply cs_forallb_ext.
  - now apply cs_forallb_ext.
  - now apply cs_forallb_ext.
  - destruct X as [hpar [_ hret]].
    rewrite (cs_forallb_ext f g _ hfg).
    rewrite (All_forallb_eq_forallb _ (on_universes f fc) (on_universes g fc) _ hpar);
      [|now intros].
    rewrite (All_forallb_eq_forallb _ (test_branch (fc #|puinst p|) (on_universes f fc))
      (test_branch (fc #|puinst p|) (on_universes g fc)) _ X0);
      [|intros b [_ hb]; unfold test_branch; now rewrite hb].
    congruence.
  - assumption.
  - eapply All_forallb_eq_forallb; tea. intros d [h1 h2]. now rewrite h1, h2.
  - eapply All_forallb_eq_forallb; tea. intros d [h1 h2]. now rewrite h1, h2.
  - eapply test_primu_primProp; tea.
    + intros x. apply hfg.
    + now intros.
Qed.

Lemma cs_reflectT_true {P : Type} {b : bool} : reflectT P b -> b = true -> P.
Proof.
  intros r e. destruct r as [p|np]; [exact p|discriminate e].
Qed.

Section CmpSound.
  Context {cf : checker_flags}.
  Context (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Σ : global_env_ext) (hΣ : abstract_env_ext_rel X Σ).

  Lemma wf_term_univs_correct (t : term) : wf_term_univs X_type X t = wf_universes Σ t.
  Proof.
    unfold wf_term_univs, wf_universes.
    apply cs_on_universes_ext. intros u.
    symmetry. exact (abstract_env_ext_wf_universeb_correct X hΣ u).
  Qed.

  Lemma cs_iff_reflect (P : Prop) (b : bool) :
    P <-> b -> reflect P b.
  Proof.
    intro H. apply iff_reflect. exact H.
  Qed.

  Lemma cs_wf_universe_iff u :
    wf_universeb Σ u <-> wf_universe Σ u.
  Proof.
    symmetry; apply reflect_iff. eapply wf_universe_reflect.
  Qed.

  Lemma cs_wf_sort_iff s :
    wf_sortb Σ s <-> wf_sort Σ s.
  Proof.
    symmetry; apply reflect_iff. eapply wf_sort_reflect.
  Qed.

  Lemma cs_wf_instance_iff u :
    wf_instanceb Σ u <-> wf_instance Σ u.
  Proof.
    symmetry; apply reflect_iff. eapply wf_instanceP.
  Qed.

  Lemma cs_compare_global_instance_correct pb ref n l l' :
    wf_instance Σ l ->
    wf_instance Σ l' ->
    cmp_global_instance Σ (compare_universe Σ) pb ref n l l' <->
    compare_global_instance (abstract_env_lookup X) (abstract_env_compare_universe X)
      pb ref n l l'.
  Proof.
    intros hl hl'. apply reflect_iff.
    apply (reflect_cmp_global_instance Σ (abstract_env_lookup X) (wf_universeb Σ)).
    - intros u u' hu hu'. apply cs_iff_reflect.
      apply (abstract_env_compare_universe_correct X hΣ); now apply cs_wf_universe_iff.
    - intros u u' hu hu'. apply cs_iff_reflect.
      apply (abstract_env_compare_universe_correct X hΣ); now apply cs_wf_universe_iff.
    - intros kn. exact (abstract_env_lookup_correct' X kn hΣ).
    - rewrite wf_universeb_instance_forall. now apply cs_wf_instance_iff.
    - rewrite wf_universeb_instance_forall. now apply cs_wf_instance_iff.
  Qed.

  Lemma cs_cmpb_term_reflect pb napp t u :
    wf_universes Σ t ->
    wf_universes Σ u ->
    reflectT (compare_term_napp Σ Σ pb napp t u)
      (eqb_term_upto_univ_napp (abstract_env_compare_universe X) (abstract_env_compare_sort X)
        (compare_global_instance (abstract_env_lookup X) (abstract_env_compare_universe X))
        pb napp t u).
  Proof.
    intros ht hu. unfold compare_term_napp.
    apply (reflect_eq_term_upto_univ Σ (wf_universeb Σ) closedu).
    - intros u1 u2 h1 h2. apply cs_iff_reflect.
      apply (abstract_env_compare_universe_correct X hΣ); now apply cs_wf_universe_iff.
    - intros u1 u2 h1 h2. apply cs_iff_reflect.
      apply (abstract_env_compare_universe_correct X hΣ); now apply cs_wf_universe_iff.
    - intros s1 s2 h1 h2. apply cs_iff_reflect.
      apply (abstract_env_compare_sort_correct X hΣ); now apply cs_wf_sort_iff.
    - intros s1 s2 h1 h2. apply cs_iff_reflect.
      apply (abstract_env_compare_sort_correct X hΣ); now apply cs_wf_sort_iff.
    - intros gr n ui ui' h1 h2. apply cs_iff_reflect.
      rewrite wf_universeb_instance_forall in h1.
      rewrite wf_universeb_instance_forall in h2.
      apply cs_compare_global_instance_correct; now apply cs_wf_instance_iff.
    - intros gr n ui ui' h1 h2. apply cs_iff_reflect.
      rewrite wf_universeb_instance_forall in h1.
      rewrite wf_universeb_instance_forall in h2.
      apply cs_compare_global_instance_correct; now apply cs_wf_instance_iff.
    - exact ht.
    - exact hu.
  Qed.

  Lemma cmp_term_wf (pb : conv_pb) (napp : nat) (t u : term) :
    cmp_term X_type X pb napp t u = true -> wf_universes Σ t /\ wf_universes Σ u.
  Proof.
    unfold cmp_term. intros h.
    apply andb_true_iff in h as [h _].
    apply andb_true_iff in h as [ht hu].
    split; rewrite <- wf_term_univs_correct; assumption.
  Qed.

  Lemma cmp_term_sound (pb : conv_pb) (napp : nat) (t u : term) :
    cmp_term X_type X pb napp t u = true -> compare_term_napp Σ Σ pb napp t u.
  Proof.
    intros h. destruct (cmp_term_wf pb napp t u h) as [ht hu].
    unfold cmp_term in h. apply andb_true_iff in h as [_ h].
    exact (cs_reflectT_true (cs_cmpb_term_reflect pb napp t u ht hu) h).
  Qed.

  Lemma cbn_ceq_term_sound (t u : term) :
    wf_universes Σ t -> wf_universes Σ u ->
    cbn_ceq_term X_type X t u = true -> compare_term Σ Σ Conv t u.
  Proof.
    intros ht hu h.
    exact (cs_reflectT_true (cs_cmpb_term_reflect Conv 0 t u ht hu) h).
  Qed.

  Lemma cmp_sort_sound (pb : conv_pb) (s1 s2 : sort) :
    cmp_sort X_type X pb s1 s2 = true -> compare_sort Σ pb s1 s2.
  Proof.
    unfold cmp_sort. intros h.
    apply andb_true_iff in h as [h12 h].
    apply andb_true_iff in h12 as [h1 h2].
    rewrite <- (abstract_env_ext_wf_sortb_correct X hΣ) in h1.
    rewrite <- (abstract_env_ext_wf_sortb_correct X hΣ) in h2.
    assert (w1 : wf_sort Σ s1) by (apply cs_wf_sort_iff; exact h1).
    assert (w2 : wf_sort Σ s2) by (apply cs_wf_sort_iff; exact h2).
    exact (proj2 (abstract_env_compare_sort_correct X hΣ pb s1 s2 w1 w2) h).
  Qed.

  Lemma cmp_level_conv_sound (l1 l2 : Level.t) :
    cmp_level_conv X_type X l1 l2 = true ->
    compare_universe Σ Conv (Universe.make' l1) (Universe.make' l2).
  Proof.
    unfold cmp_level_conv; cbv zeta. intros h.
    apply andb_true_iff in h as [h12 h].
    apply andb_true_iff in h12 as [h1 h2].
    rewrite <- (abstract_env_ext_wf_universeb_correct X hΣ) in h1.
    rewrite <- (abstract_env_ext_wf_universeb_correct X hΣ) in h2.
    assert (w1 : wf_universe Σ (Universe.make' l1)) by (apply cs_wf_universe_iff; exact h1).
    assert (w2 : wf_universe Σ (Universe.make' l2)) by (apply cs_wf_universe_iff; exact h2).
    exact (proj2 (abstract_env_compare_universe_correct X hΣ Conv _ _ w1 w2) h).
  Qed.

  Lemma cmp_level_conv_instance (u1 u2 : Instance.t) :
    forallb2 (cmp_level_conv X_type X) u1 u2 = true ->
    cmp_universe_instance (compare_universe Σ Conv) u1 u2.
  Proof.
    unfold cmp_universe_instance.
    revert u2. induction u1 as [|l1 u1 IH]; intros u2; destruct u2 as [|l2 u2]; cbn;
      try (intros e; discriminate e).
    - intros _. constructor.
    - intros h. apply andb_true_iff in h as [h hs]. constructor.
      + exact (cmp_level_conv_sound l1 l2 h).
      + exact (IH u2 hs).
  Qed.
End CmpSound.

(** ** A substitution does not look at an index the term does not use

  The same-code rule skips a position whose index does not occur in the code
  ([noccur_between i 1 t]), so what it establishes of the two environments is weaker than
  "pairwise convertible". [subst_noccur_irrel] says that this is enough: two substitutions
  that agree at every index the term uses give the same term. [subst_agree_lift] is the
  instance the read-back shape [subst ts 0 (lift N #|ts| t)] meets, where the cut of the
  lift sits above every substituted index, so the occurrence test is made on [t] itself
  ([noccur_between_lift]). *)

Lemma noccA_forallb_map {A B : Type} (P : A -> Type) (p : A -> bool) (q : B -> bool)
  (f : A -> B) (l : list A) :
  All P l -> (forall x, P x -> p x = true -> q (f x) = true) ->
  forallb p l = true -> forallb q (map f l) = true.
Proof.
  intros HA Hf. induction HA as [|x l Px HA IH]; cbn; intros H; [reflexivity|].
  apply Bool.andb_true_iff in H as [H1 H2]. apply Bool.andb_true_iff. split.
  - exact (Hf x Px H1).
  - exact (IH H2).
Qed.

Lemma noccA_map_ext {A B : Type} (P : A -> Type) (f g : A -> B) (l : list A) :
  All P l -> (forall x, In x l -> P x -> f x = g x) -> map f l = map g l.
Proof.
  intros HA. induction HA as [|x l Px HA IH]; cbn; intros H; [reflexivity|].
  f_equal.
  - apply H; [left; reflexivity | exact Px].
  - apply IH. intros y Hy Py. apply H; [right; exact Hy | exact Py].
Qed.

Lemma noccA_forallb_false {A : Type} (p : A -> bool) (l : list A) (x : A) :
  In x l -> p x = false -> forallb p l = false.
Proof.
  intros Hin Hx. induction l as [|y l IH]; cbn in Hin |- *; [contradiction|].
  destruct Hin as [Hy|Hin].
  - subst y. rewrite Hx. reflexivity.
  - rewrite (IH Hin). apply Bool.andb_false_r.
Qed.

(* [noccA_false H] closes a goal [c = false] where [c] is a conjunction ([andb]) one of
   whose conjuncts is, up to conversion, the left side of [H : _ = false]. *)
Ltac noccA_false H :=
  first [ exact H
        | apply Bool.andb_false_iff;
          first [ left; noccA_false H | right; noccA_false H ] ].

(* [noccA_sub Hj] moves the agreement hypothesis [Hj] of a term to one of its direct
   subterms: if the subterm uses an index then so does the term. *)
Ltac noccA_sub Hj :=
  let j := fresh "j" in
  let Hj1 := fresh "Hj1" in
  let Hj2 := fresh "Hj2" in
  intros j Hj1 Hj2; apply Hj; [exact Hj1 | cbn [noccur_between]; noccA_false Hj2].

Lemma noccur_between_lift (n k i : nat) (t : term) :
  i < k -> noccur_between i 1 t = true -> noccur_between i 1 (lift n k t) = true.
Proof.
  revert n k i. elim t using term_forall_list_ind.
  - (* tRel *)
    intros r N K I HIK H. cbn [lift noccur_between] in H |- *.
    destruct (K <=? r) eqn:E; [|exact H].
    apply Nat.leb_le in E.
    apply Bool.orb_true_iff; right; apply Nat.leb_le; lia.
  - (* tVar *) intros; reflexivity.
  - (* tEvar *)
    intros ev l Hl N K I HIK H. cbn [lift noccur_between] in H |- *.
    refine (noccA_forallb_map _ _ _ _ _ Hl _ H). intros x Px Hx. apply Px; assumption.
  - (* tSort *) intros; reflexivity.
  - (* tProd *)
    intros na A IHA B IHB N K I HIK H. cbn [lift noccur_between] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply IHA | apply IHB]; first [assumption | lia].
  - (* tLambda *)
    intros na A IHA B IHB N K I HIK H. cbn [lift noccur_between] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply IHA | apply IHB]; first [assumption | lia].
  - (* tLetIn *)
    intros na b IHb ty IHty B IHB N K I HIK H. cbn [lift noccur_between] in H |- *.
    apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply Bool.andb_true_iff; split|].
    + apply IHb; first [assumption | lia].
    + apply IHty; first [assumption | lia].
    + apply IHB; first [assumption | lia].
  - (* tApp *)
    intros u v IHu IHv N K I HIK H. cbn [lift noccur_between] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply IHu | apply IHv]; first [assumption | lia].
  - (* tConst *) intros; reflexivity.
  - (* tInd *) intros; reflexivity.
  - (* tConstruct *) intros; reflexivity.
  - (* tCase *)
    intros ci p Hp c IHc brs Hbrs N K I HIK H. cbn [lift noccur_between] in H |- *.
    destruct Hp as [Hpar [Hctx Hret]].
    unfold test_predicate_k, map_predicate_k in H |- *. simpl in H |- *.
    apply Bool.andb_true_iff in H as [H Hbr].
    apply Bool.andb_true_iff in H as [H Hc].
    apply Bool.andb_true_iff in H as [H Hr].
    apply Bool.andb_true_iff in H as [Hpa Hcx].
    apply Bool.andb_true_iff; split.
    2:{ refine (noccA_forallb_map _ _ _ _ _ Hbrs _ Hbr).
        intros br [Pctx Pbody] Hb. unfold test_branch_k, map_branch_k in Hb |- *.
        simpl in Hb |- *. cbv [id].
        rewrite length_map.
        apply Bool.andb_true_iff in Hb as [Hb1 Hb2].
        apply Bool.andb_true_iff; split; [exact Hb1 | apply Pbody; [lia | exact Hb2]]. }
    apply Bool.andb_true_iff; split.
    2:{ apply IHc; assumption. }
    apply Bool.andb_true_iff; split.
    2:{ apply Hret; [lia | exact Hr]. }
    apply Bool.andb_true_iff; split.
    2:{ rewrite length_map. exact Hcx. }
    refine (noccA_forallb_map _ _ _ _ _ Hpar _ Hpa). intros x Px Hx. apply Px; assumption.
  - (* tProj *)
    intros pr c IHc N K I HIK H. cbn [lift noccur_between] in H |- *.
    apply IHc; assumption.
  - (* tFix *)
    intros mfix idx Hm N K I HIK H. cbn [lift noccur_between] in H |- *.
    rewrite length_map.
    refine (noccA_forallb_map _ _ _ _ _ Hm _ H).
    intros d [Pty Pbody] Hd. unfold test_def, map_def in Hd |- *. simpl in Hd |- *.
    apply Bool.andb_true_iff in Hd as [Hd1 Hd2].
    apply Bool.andb_true_iff; split; [apply Pty | apply Pbody]; first [assumption | lia].
  - (* tCoFix *)
    intros mfix idx Hm N K I HIK H. cbn [lift noccur_between] in H |- *.
    rewrite length_map.
    refine (noccA_forallb_map _ _ _ _ _ Hm _ H).
    intros d [Pty Pbody] Hd. unfold test_def, map_def in Hd |- *. simpl in Hd |- *.
    apply Bool.andb_true_iff in Hd as [Hd1 Hd2].
    apply Bool.andb_true_iff; split; [apply Pty | apply Pbody]; first [assumption | lia].
  - (* tPrim *)
    intros prim Hprim N K I HIK H. cbn [lift noccur_between] in H |- *.
    destruct prim as [tg [? | ? | ? | a]]; cbn in Hprim, H |- *; try reflexivity.
    destruct Hprim as [Hty [Hdef Hval]].
    apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply Bool.andb_true_iff; split|].
    + refine (noccA_forallb_map _ _ _ _ _ Hval _ H1). intros y Py Hy. apply Py; assumption.
    + apply Hdef; assumption.
    + apply Hty; assumption.
Qed.

Lemma subst_noccur_irrel (l1 l2 : list term) :
  #|l1| = #|l2| ->
  forall (b : term) (k : nat),
    (forall j, j < #|l1| -> noccur_between (k + j) 1 b = false ->
               nth_error l1 j = nth_error l2 j) ->
    subst l1 k b = subst l2 k b.
Proof.
  intros Hlen b. elim b using term_forall_list_ind.
  - (* tRel *)
    intros r k Hj. cbn [subst].
    destruct (k <=? r) eqn:E; [|reflexivity].
    apply Nat.leb_le in E.
    destruct (Nat.lt_ge_cases (r - k) #|l1|) as [Hlt|Hge].
    + assert (Heq : nth_error l1 (r - k) = nth_error l2 (r - k)).
      { apply Hj; [exact Hlt|]. cbn [noccur_between].
        apply Bool.orb_false_iff; split; [apply Nat.ltb_ge | apply Nat.leb_gt]; lia. }
      rewrite Heq. rewrite Hlen. reflexivity.
    + assert (E1 : nth_error l1 (r - k) = None) by (apply nth_error_None; lia).
      assert (E2 : nth_error l2 (r - k) = None) by (apply nth_error_None; lia).
      rewrite E1. rewrite E2. rewrite Hlen. reflexivity.
  - (* tVar *) intros; reflexivity.
  - (* tEvar *)
    intros ev l Hl k Hj. cbn [subst].
    f_equal. apply (noccA_map_ext _ _ _ _ Hl). intros x Hin Px. apply Px.
    intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
    exact (noccA_forallb_false _ _ _ Hin Hj2).
  - (* tSort *) intros; reflexivity.
  - (* tProd *)
    intros na A IHA B IHB k Hj. cbn [subst].
    f_equal; [apply IHA | apply IHB]; noccA_sub Hj.
  - (* tLambda *)
    intros na A IHA B IHB k Hj. cbn [subst].
    f_equal; [apply IHA | apply IHB]; noccA_sub Hj.
  - (* tLetIn *)
    intros na t IHt ty IHty B IHB k Hj. cbn [subst].
    f_equal; [apply IHt | apply IHty | apply IHB]; noccA_sub Hj.
  - (* tApp *)
    intros u v IHu IHv k Hj. cbn [subst].
    f_equal; [apply IHu | apply IHv]; noccA_sub Hj.
  - (* tConst *) intros; reflexivity.
  - (* tInd *) intros; reflexivity.
  - (* tConstruct *) intros; reflexivity.
  - (* tCase *)
    intros ci p Hp c IHc brs Hbrs k Hj. cbn [subst].
    destruct Hp as [Hpar [Hctx Hret]].
    f_equal; [unfold map_predicate_k; f_equal | apply IHc; noccA_sub Hj | ].
    + (* pparams *)
      apply (noccA_map_ext _ _ _ _ Hpar). intros x Hin Px. apply Px.
      intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
      unfold test_predicate_k.
      pose proof (noccA_forallb_false _ _ _ Hin Hj2) as Hf. noccA_false Hf.
    + (* preturn *)
      apply Hret. intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
      unfold test_predicate_k.
      rewrite <- Nat.add_assoc in Hj2. noccA_false Hj2.
    + (* branches *)
      apply (noccA_map_ext _ _ _ _ Hbrs). intros br Hin [Pctx Pbody].
      unfold map_branch_k. f_equal. apply Pbody.
      intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
      rewrite <- Nat.add_assoc in Hj2.
      assert (Hb : test_branch_k p (fun k0 => noccur_between k0 1) (k + j) br = false)
        by (unfold test_branch_k; noccA_false Hj2).
      pose proof (noccA_forallb_false _ _ _ Hin Hb) as Hf. noccA_false Hf.
  - (* tProj *)
    intros pr c IHc k Hj. cbn [subst].
    f_equal; apply IHc; noccA_sub Hj.
  - (* tFix *)
    intros mfix idx Hm k Hj. cbn [subst].
    f_equal. apply (noccA_map_ext _ _ _ _ Hm). intros d Hin [Pty Pbody].
    unfold map_def. f_equal.
    + apply Pty. intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
      assert (Hd : test_def (noccur_between (k + j) 1)
                     (noccur_between (#|mfix| + (k + j)) 1) d = false)
        by (unfold test_def; noccA_false Hj2).
      exact (noccA_forallb_false _ _ _ Hin Hd).
    + apply Pbody. intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
      rewrite <- Nat.add_assoc in Hj2.
      assert (Hd : test_def (noccur_between (k + j) 1)
                     (noccur_between (#|mfix| + (k + j)) 1) d = false)
        by (unfold test_def; noccA_false Hj2).
      exact (noccA_forallb_false _ _ _ Hin Hd).
  - (* tCoFix *)
    intros mfix idx Hm k Hj. cbn [subst].
    f_equal. apply (noccA_map_ext _ _ _ _ Hm). intros d Hin [Pty Pbody].
    unfold map_def. f_equal.
    + apply Pty. intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
      assert (Hd : test_def (noccur_between (k + j) 1)
                     (noccur_between (#|mfix| + (k + j)) 1) d = false)
        by (unfold test_def; noccA_false Hj2).
      exact (noccA_forallb_false _ _ _ Hin Hd).
    + apply Pbody. intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
      rewrite <- Nat.add_assoc in Hj2.
      assert (Hd : test_def (noccur_between (k + j) 1)
                     (noccur_between (#|mfix| + (k + j)) 1) d = false)
        by (unfold test_def; noccA_false Hj2).
      exact (noccA_forallb_false _ _ _ Hin Hd).
  - (* tPrim *)
    intros prim Hprim k Hj. cbn [subst].
    destruct prim as [tg [? | ? | ? | a]]; cbn in Hprim |- *; try reflexivity.
    destruct Hprim as [Hty [Hdef Hval]].
    assert (E1 : subst l1 k (array_type a) = subst l2 k (array_type a)).
    { apply Hty. intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn. noccA_false Hj2. }
    assert (E2 : subst l1 k (array_default a) = subst l2 k (array_default a)).
    { apply Hdef. intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn. noccA_false Hj2. }
    assert (E3 : map (subst l1 k) (array_value a) = map (subst l2 k) (array_value a)).
    { apply (noccA_map_ext _ _ _ _ Hval). intros y Hin Py. apply Py.
      intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn.
      pose proof (noccA_forallb_false _ _ _ Hin Hj2) as Hf. noccA_false Hf. }
    unfold mapu_array_model.
    rewrite E1. rewrite E2. rewrite E3. reflexivity.
Qed.

Lemma subst_agree_lift (l1 l2 : list term) (N m : nat) (t : term) :
  #|l1| = #|l2| -> m = #|l1| ->
  (forall j, j < #|l1| -> noccur_between j 1 t = false ->
             nth_error l1 j = nth_error l2 j) ->
  subst l1 0 (lift N m t) = subst l2 0 (lift N m t).
Proof.
  intros Hlen Hm Hag.
  apply subst_noccur_irrel; [exact Hlen|].
  intros j Hj Hnoc. apply Hag; [exact Hj|].
  destruct (noccur_between j 1 t) eqn:E; [|reflexivity].
  exfalso.
  assert (Hl : noccur_between (0 + j) 1 (lift N m t) = true)
    by (apply noccur_between_lift; [lia | exact E]).
  rewrite Hl in Hnoc. discriminate.
Qed.

(** ** The fuel a sub-call runs at

  Every function of the comparison matches its fuel [FS k] and calls its neighbours at
  [k tt]. [fuel_sub d' d] says that [d'] is reachable from [d] that way, so a rule proved
  at [d] may use the evaluator's seam at every fuel its own sub-calls can reach. *)
Inductive fuel_sub : cbn_fuel -> cbn_fuel -> Prop :=
| fuel_sub_refl d : fuel_sub d d
| fuel_sub_step d k : fuel_sub d (k tt) -> fuel_sub d (FS k).

(** ** The list of readings the same-code rule compares

  [same_code_cells] walks the two environments side by side. At a position it either sees
  the same address, or an index the code does not use, or it calls the comparison. What it
  establishes is therefore, position by position, "the index does not occur in the code, or
  the two readings are convertible". *)

Section Conv.
  Context {cf : checker_flags}.
  Context (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Σ : global_env_ext) (wfΣ : wf Σ) (hΣ : abstract_env_ext_rel X Σ).
  Context (Γ : context) (nctx : nat).
  Context (stress : bool).

  Local Notation conv_ok Ξ pb t u := (∥ Σ ;;; Ξ ⊢ t ≤[pb] u ∥).

  Inductive cells_agree (Ξ : context) (t : term) : nat -> list term -> list term -> Prop :=
  | cells_agree_nil i : cells_agree Ξ t i [] []
  | cells_agree_cons i u1 u2 l1 l2 :
      (noccur_between i 1 t = true \/ ∥ Σ ;;; Ξ ⊢ u1 = u2 ∥) ->
      cells_agree Ξ t (S i) l1 l2 ->
      cells_agree Ξ t i (u1 :: l1) (u2 :: l2).

  (** The list the same-code rule may substitute instead of the second one: at a position
    the machine skipped because the code does not use it, the first list's entry. *)
  Fixpoint patch (t : term) (i : nat) (l1 l2 : list term) : list term :=
    match l1, l2 with
    | u1 :: l1, u2 :: l2 =>
        (if noccur_between i 1 t then u1 else u2) :: patch t (S i) l1 l2
    | _, _ => l2
    end.

  Lemma patch_length (t : term) (i : nat) (l1 l2 : list term) :
    #|l1| = #|l2| -> #|patch t i l1 l2| = #|l1|.
  Proof.
    revert i l2. induction l1 as [|u1 l1 ih]; intros i [|u2 l2] hl; cbn in hl |- *;
      try discriminate hl; [reflexivity|].
    f_equal. apply ih. lia.
  Qed.

  Lemma patch_nth (t : term) (i : nat) (l1 l2 : list term) (j : nat) :
    #|l1| = #|l2| -> noccur_between (i + j) 1 t = false ->
    nth_error (patch t i l1 l2) j = nth_error l2 j.
  Proof.
    revert i l2 j. induction l1 as [|u1 l1 ih]; intros i [|u2 l2] j hl hn;
      cbn in hl |- *; try discriminate hl; [reflexivity|].
    destruct j as [|j]; cbn.
    - rewrite Nat.add_0_r in hn. rewrite hn. reflexivity.
    - apply ih; [lia|]. rewrite <- hn. f_equal. lia.
  Qed.

  Lemma sq_terms_all2 (Ξ : context) (l1 l2 : list term) :
    Forall2 (fun u v => ∥ Σ ;;; Ξ ⊢ u = v ∥) l1 l2 ->
    ∥ All2 (ws_cumul_pb Conv Σ Ξ) l1 l2 ∥.
  Proof.
    induction 1 as [|u v l1 l2 h _ ih].
    - constructor. constructor.
    - destruct h as [h], ih as [ih]. constructor. constructor; assumption.
  Qed.

  Lemma cells_agree_patch (Ξ : context) (t : term) (i : nat) (l1 l2 : list term) :
    is_closed_context Ξ ->
    forallb (is_open_term Ξ) l1 ->
    cells_agree Ξ t i l1 l2 ->
    Forall2 (fun u v => ∥ Σ ;;; Ξ ⊢ u = v ∥) l1 (patch t i l1 l2).
  Proof.
    intros clΞ hop hag. induction hag as [i|i u1 u2 l1 l2 hd _ ih]; cbn.
    - constructor.
    - cbn in hop. apply andb_true_iff in hop as [hu hl].
      constructor.
      + destruct (noccur_between i 1 t) eqn:En.
        * constructor. exact (@ws_cumul_pb_refl_open cf Σ Conv Ξ u1 clΞ hu).
        * destruct hd as [hd|hd]; [exfalso; congruence|exact hd].
      + exact (ih hl).
  Qed.

  (** ** What every function of the comparison assumes of the state

    The state invariants of the earlier files, bundled: the heap was built the way
    [bh_ok] describes and holds no forwarding pointer, the context map names only cells
    that stand for what the context entry denotes, the code table is good, the five memo
    tables mean what they say, and no cell names a variable at a level not yet in scope.
    Raising the level only weakens the last clause. *)
  Definition cok (lvl : nat) (s : cbn_state) : Prop :=
    (exists lo : positive, state_ok lo s)
    /\ heap_nofwd s.(st_heap)
    /\ (forall l : nat, gam_ok Γ nctx l s)
    /\ memo_ok X_type X s
    /\ memo_inv X_type X s
    /\ heap_wf lvl s.(st_heap).

  Lemma cok_mono (lvl lvl' : nat) (s : cbn_state) : lvl <= lvl' -> cok lvl s -> cok lvl' s.
  Proof.
    intros hle (h1 & h2 & h3 & h4 & h5 & h6).
    split; [exact h1|]. split; [exact h2|]. split; [exact h3|].
    split; [exact h4|]. split; [exact h5|].
    exact (heap_wf_mono lvl lvl' _ hle h6).
  Qed.

  Lemma cok_memo_inv (lvl : nat) (s : cbn_state) : cok lvl s -> memo_inv X_type X s.
  Proof. intros (_ & _ & _ & _ & h & _). exact h. Qed.

  Lemma cok_ceq_ok (lvl : nat) (s : cbn_state) : cok lvl s -> ceq_ok X_type X (s.(st_memo)).
  Proof. intros h. exact (proj1 (proj2 (proj2 (proj2 (cok_memo_inv lvl s h))))). Qed.

  (** A step that leaves the heap, the next address, the context map and the code table
    alone keeps the whole invariant; [code_eq] is such a step. *)
  Lemma cok_same (lvl : nat) (s s' : cbn_state) :
    cok lvl s -> memo_inv X_type X s' ->
    s'.(st_heap) = s.(st_heap) -> s'.(st_next) = s.(st_next) ->
    s'.(st_gam) = s.(st_gam) ->
    ((s'.(st_memo)).(m_codes)) = ((s.(st_memo)).(m_codes)) ->
    cok lvl s'.
  Proof.
    intros (h1 & h2 & h3 & h4 & _ & h6) hm he hn hg hc.
    split; [|split; [|split; [|split; [|split]]]].
    - destruct h1 as [lo [hb hcl hga]]. exists lo. split.
      + rewrite he, hn. exact hb.
      + rewrite he, hn. exact hcl.
      + rewrite hg, hn. exact hga.
    - rewrite he. exact h2.
    - intros l j a hk. rewrite hg in hk. destruct (h3 l j a hk) as [t [hd hr]].
      exists t. split; [exact hd|]. rewrite he. exact hr.
    - exact (memo_ok_codes X_type X s s' hc h4).
    - exact hm.
    - rewrite he. exact h6.
  Qed.

  (** ** The seam with the evaluator

    [conv_slot] and [conv_term] are the two doors of the comparison that can force a value
    ([conv_eval], [whnf]), so their soundness is the evaluator's theorem, not this file's.
    Each is assumed here in exactly the form the comparison uses it, and nothing else in
    this file is assumed. A function that answers at all hands the caller's roots back
    renamed, keeps the state invariant, and — when it answers [true] — relates the two
    readings. *)
  Definition slot_seam (d : cbn_fuel) : Prop :=
    forall (lvl : nat) (pb : conv_pb) (Ξ : context) (x1 x2 : cbn_slot)
      (rs : list root) (s : cbn_state) (b : bool) (rs' : list root) (s' : cbn_state),
      cok lvl s -> #|Ξ| = lvl -> is_closed_context Ξ -> nctx <= lvl ->
      conv_slot X_type X Γ nctx stress d lvl pb x1 x2 rs s = COk (b, rs', s') ->
      Forall2 (root_pres nctx (s.(st_heap)) (s'.(st_heap))) rs rs'
      /\ cok lvl s'
      /\ (b = true ->
          forall t1 t2 : term,
            repr_slot nctx (s.(st_heap)) lvl x1 t1 ->
            repr_slot nctx (s.(st_heap)) lvl x2 t2 ->
            is_open_term Ξ t1 -> is_open_term Ξ t2 ->
            ∥ Σ ;;; Ξ ⊢ t1 ≤[pb] t2 ∥).

  Definition term_seam (d : cbn_fuel) : Prop :=
    forall (lvl : nat) (pb : conv_pb) (Ξ : context) (e1 : cbn_env) (c1 : code)
      (e2 : cbn_env) (c2 : code) (rs : list root) (s : cbn_state) (b : bool)
      (rs' : list root) (s' : cbn_state),
      cok lvl s -> #|Ξ| = lvl -> is_closed_context Ξ -> nctx <= lvl ->
      conv_term X_type X Γ nctx stress d lvl pb e1 c1 e2 c2 rs s = COk (b, rs', s') ->
      Forall2 (root_pres nctx (s.(st_heap)) (s'.(st_heap))) rs rs'
      /\ cok lvl s'
      /\ (b = true ->
          forall u1 u2 : term,
            repr_susp nctx (s.(st_heap)) lvl e1 (c1.(c_term)) u1 ->
            repr_susp nctx (s.(st_heap)) lvl e2 (c2.(c_term)) u2 ->
            is_open_term Ξ u1 -> is_open_term Ξ u2 ->
            ∥ Σ ;;; Ξ ⊢ u1 ≤[pb] u2 ∥).

  (** The sub-calls run at the fuel [k tt] of the caller's [FS k], so a rule is proved
    from the seam at every fuel the caller can reach. *)
  Definition slot_seam_below (d : cbn_fuel) : Prop :=
    forall d' : cbn_fuel, fuel_sub d' d -> slot_seam d'.

  Definition term_seam_below (d : cbn_fuel) : Prop :=
    forall d' : cbn_fuel, fuel_sub d' d -> term_seam d'.

  Lemma slot_seam_below_step (k : unit -> cbn_fuel) :
    slot_seam_below (FS k) -> slot_seam_below (k tt).
  Proof. intros h d' hs. exact (h d' (fuel_sub_step d' k hs)). Qed.

  Lemma term_seam_below_step (k : unit -> cbn_fuel) :
    term_seam_below (FS k) -> term_seam_below (k tt).
  Proof. intros h d' hs. exact (h d' (fuel_sub_step d' k hs)). Qed.

  Lemma slot_seam_below_here (k : unit -> cbn_fuel) :
    slot_seam_below (FS k) -> slot_seam (k tt).
  Proof. intros h. exact (h (k tt) (fuel_sub_step _ k (fuel_sub_refl _))). Qed.

  Lemma term_seam_below_here (k : unit -> cbn_fuel) :
    term_seam_below (FS k) -> term_seam (k tt).
  Proof. intros h. exact (h (k tt) (fuel_sub_step _ k (fuel_sub_refl _))). Qed.

  (** ** Reading a renamed root *)

  Lemma root_pres_RSk_inv (H H' : bheap cbn_cell) (l : list cbn_slot) (r : root) :
    root_pres nctx H H' (RSk l) r ->
    exists l' : list cbn_slot,
      r = RSk l'
      /\ (forall lvl ts, repr_slots nctx H lvl l ts -> repr_slots nctx H' lvl l' ts).
  Proof.
    destruct r as [a|x|e|v|lk|lp|cl]; cbn; intros h; try contradiction.
    exists lk. split; [reflexivity|exact h].
  Qed.

  Lemma root_pres_RE_inv (H H' : bheap cbn_cell) (e : cbn_env) (r : root) :
    root_pres nctx H H' (RE e) r ->
    exists e' : cbn_env,
      r = RE e'
      /\ (forall lvl tm u, repr_susp nctx H lvl e tm u -> repr_susp nctx H' lvl e' tm u).
  Proof.
    destruct r as [a|x|e0|v|lk|lp|cl]; cbn; intros h; try contradiction.
    exists e0. split; [reflexivity|exact h].
  Qed.

  Lemma haddr_eqb_eq (a b : haddr) : haddr_eqb a b = true -> a = b.
  Proof.
    destruct a as [p], b as [q]. unfold haddr_eqb. cbn. intros h.
    apply Pos.eqb_eq in h. rewrite h. reflexivity.
  Qed.

  Lemma repr_slots_nil_inv (H : bheap cbn_cell) (lvl : nat) (ts : list term) :
    repr_slots nctx H lvl [] ts -> ts = [].
  Proof. intros h. inversion h; subst. reflexivity. Qed.

  Lemma repr_slots_cons_inv (H : bheap cbn_cell) (lvl : nat) (x : cbn_slot)
      (l : list cbn_slot) (ts : list term) :
    repr_slots nctx H lvl (x :: l) ts ->
    exists (u : term) (ts' : list term),
      ts = u :: ts' /\ repr_slot nctx H lvl x u /\ repr_slots nctx H lvl l ts'.
  Proof.
    intros h. inversion h; subst. eexists. eexists.
    split; [reflexivity|]. split; eassumption.
  Qed.

  (** The body of [same_code_cells] at a successor fuel, written with the names of the
    comparison's functions: [cbn] would replace them by the raw mutual fixpoint. *)
  Lemma same_code_cells_eq (k : unit -> cbn_fuel) (lvl : nat) (t : term) (i : nat)
      (l1 l2 : list cbn_slot) (rs : list root) (s : cbn_state) :
    same_code_cells X_type X Γ nctx stress (FS k) lvl t i l1 l2 rs s
    = match l1, l2 with
      | [], [] => COk (true, rs, s)
      | x1 :: l1, x2 :: l2 =>
        if slot_same x1 x2 || noccur_between i 1 t
        then same_code_cells X_type X Γ nctx stress (k tt) lvl t (S i) l1 l2 rs s
        else
          match conv_slot X_type X Γ nctx stress (k tt) lvl Conv x1 x2
                  (RSk l1 :: RSk l2 :: rs) s with
          | COk (true, rs, s) =>
            match rs with
            | RSk l1 :: RSk l2 :: rs =>
              same_code_cells X_type X Γ nctx stress (k tt) lvl t (S i) l1 l2 rs s
            | _ => CFail WRoots
            end
          | COk (false, rs, s) => COk (false, skipn 2 rs, s)
          | CFail w => CFail w
          end
      | _, _ => COk (false, rs, s)
      end.
  Proof. reflexivity. Qed.

  Lemma conv_same_code_eq (k : unit -> cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : code)
      (e2 : cbn_env) (c2 : code) (rs : list root) (s : cbn_state) :
    conv_same_code X_type X Γ nctx stress (FS k) lvl e1 c1 e2 c2 rs s
    = (if (e1.(ev_goff) == e2.(ev_goff)) && (e1.(ev_nvals) == e2.(ev_nvals)) then
         let (b, s) := code_eq X_type X c1 c2 s in
         if b then same_code_cells X_type X Γ nctx stress (k tt) lvl (c1.(c_term)) 0
                     (e1.(ev_vals)) (e2.(ev_vals)) rs s
         else COk (false, rs, s)
       else COk (false, rs, s)).
  Proof. reflexivity. Qed.

  (** ** The same-code rule, cell by cell

    [same_code_cells] walks the two environments side by side: it skips a position whose
    two slots are the same address (so the two readings are the same term), and a position
    the code does not use ([noccur_between i 1 t]); everything else goes to [conv_slot].
    What it establishes is exactly [cells_agree]. *)
  Lemma same_code_cells_sound :
    forall (d : cbn_fuel) (lvl : nat) (Ξ : context) (t : term) (i : nat)
      (l1 l2 : list cbn_slot) (ts1 ts2 : list term) (rs : list root) (s : cbn_state)
      (rs' : list root) (s' : cbn_state),
      slot_seam_below d ->
      cok lvl s -> #|Ξ| = lvl -> is_closed_context Ξ -> nctx <= lvl ->
      repr_slots nctx (s.(st_heap)) lvl l1 ts1 ->
      repr_slots nctx (s.(st_heap)) lvl l2 ts2 ->
      forallb (is_open_term Ξ) ts1 = true ->
      forallb (is_open_term Ξ) ts2 = true ->
      same_code_cells X_type X Γ nctx stress d lvl t i l1 l2 rs s = COk (true, rs', s') ->
      Forall2 (root_pres nctx (s.(st_heap)) (s'.(st_heap))) rs rs'
      /\ cok lvl s'
      /\ cells_agree Ξ t i ts1 ts2.
  Proof.
    intros d. induction d as [|k ih]; intros lvl Ξ t i l1 l2 ts1 ts2 rs s rs' s'
      hseam hok hlen clΞ hnc hr1 hr2 ho1 ho2 he.
    { cbn in he. discriminate he. }
    rewrite same_code_cells_eq in he.
    destruct l1 as [|x1 l1]; destruct l2 as [|x2 l2].
    - (* both exhausted *)
      cbn in he. inversion he; subst.
      rewrite (repr_slots_nil_inv _ _ _ hr1), (repr_slots_nil_inv _ _ _ hr2).
      split; [apply roots_pres_refl|]. split; [exact hok|]. constructor.
    - discriminate he.
    - discriminate he.
    - destruct (repr_slots_cons_inv _ _ _ _ _ hr1) as [u1 [ts1' [-> [hx1 hl1]]]].
      destruct (repr_slots_cons_inv _ _ _ _ _ hr2) as [u2 [ts2' [-> [hx2 hl2]]]].
      cbn in ho1, ho2.
      apply andb_true_iff in ho1 as [hou1 ho1].
      apply andb_true_iff in ho2 as [hou2 ho2].
      destruct (slot_same x1 x2 || noccur_between i 1 t) eqn:Eskip.
      + (* the machine skipped this position *)
        destruct (ih tt lvl Ξ t (S i) l1 l2 ts1' ts2' rs s rs' s'
                    (slot_seam_below_step k hseam) hok hlen clΞ hnc hl1 hl2 ho1 ho2 he)
          as (hp & hok' & hag).
        split; [exact hp|]. split; [exact hok'|].
        constructor; [|exact hag].
        apply orb_true_iff in Eskip as [Esame|Enocc]; [|left; exact Enocc].
        right.
        (* the same address: the two slots stand for one term *)
        destruct x1 as [a1|? ? ? ?], x2 as [a2|? ? ? ?]; cbn in Esame;
          try discriminate Esame.
        apply haddr_eqb_eq in Esame. subst a2.
        assert (hu : u1 = u2).
        { exact (proj1 (proj2 (proj2 (proj2 (repr_det nctx (s.(st_heap))))))
                   lvl (SAddr a1) u1 hx1 u2 hx2). }
        subst u2. constructor.
        exact (@ws_cumul_pb_refl_open cf Σ Conv Ξ u1 clΞ hou1).
      + (* the machine compared this position *)
        destruct (conv_slot X_type X Γ nctx stress (k tt) lvl Conv x1 x2
                    (RSk l1 :: RSk l2 :: rs) s) as [[[b2 rs2] s2]|w] eqn:Ecs;
          [|discriminate he].
        destruct (slot_seam_below_here k hseam lvl Conv Ξ x1 x2
                    (RSk l1 :: RSk l2 :: rs) s b2 rs2 s2 hok hlen clΞ hnc Ecs)
          as (hp1 & hok2 & hconv).
        destruct b2; [|discriminate he].
        destruct (Forall2_cons_inv _ _ _ _ hp1) as [r1' [q1 [-> [hpr1 hp1']]]].
        destruct (root_pres_RSk_inv (s.(st_heap)) (s2.(st_heap)) l1 r1' hpr1)
          as [l1b [-> hk1]].
        destruct (Forall2_cons_inv _ _ _ _ hp1') as [r2' [q2 [-> [hpr2 hp2']]]].
        destruct (root_pres_RSk_inv (s.(st_heap)) (s2.(st_heap)) l2 r2' hpr2)
          as [l2b [-> hk2]].

        destruct (ih tt lvl Ξ t (S i) l1b l2b ts1' ts2' q2 s2 rs' s'
                    (slot_seam_below_step k hseam) hok2 hlen clΞ hnc
                    (hk1 lvl ts1' hl1) (hk2 lvl ts2' hl2) ho1 ho2 he)
          as (hp & hok' & hag).
        split.
        * exact (roots_pres_trans nctx (s.(st_heap)) (s2.(st_heap)) (s'.(st_heap))
                   rs q2 rs' hp2' hp).
        * split; [exact hok'|].
          constructor; [|exact hag].
          right. exact (hconv eq_refl u1 u2 hx1 hx2 hou1 hou2).
  Qed.

  (** ** From the cells to the two readings

    [cells_agree] is enough for the substitution congruence: replace, at each position the
    machine skipped for non-occurrence, the second list's entry by the first's ([patch]).
    The patched list is pairwise convertible with the first ([cells_agree_patch]), which is
    [PCUICCallByNeedSoundCong.ws_cumul_pb_subst_lift]'s hypothesis, and substituting it is
    the same as substituting the second ([subst_agree_lift]). *)
  Lemma cells_agree_subst (Ξ : context) (t : term) (ts1 ts2 : list term)
      (N m : nat) (pb : conv_pb) :
    is_closed_context Ξ ->
    #|ts1| = #|ts2| -> m = #|ts1| -> N <= #|Ξ| ->
    on_free_vars (shiftnP (m + (#|Ξ| - N)) (fun _ : nat => false)) t ->
    forallb (is_open_term Ξ) ts1 = true ->
    cells_agree Ξ t 0 ts1 ts2 ->
    ∥ Σ ;;; Ξ ⊢ subst ts1 0 (lift N m t) ≤[pb] subst ts2 0 (lift N m t) ∥.
  Proof.
    intros clΞ hlen hm hN hof hop hag.
    assert (hpl : #|patch t 0 ts1 ts2| = #|ts1|) by exact (patch_length t 0 ts1 ts2 hlen).
    assert (heq : subst (patch t 0 ts1 ts2) 0 (lift N m t) = subst ts2 0 (lift N m t)).
    { apply subst_agree_lift; [lia|lia|].
      intros j hj hn. rewrite hpl in hj.
      exact (patch_nth t 0 ts1 ts2 j hlen hn). }
    destruct (sq_terms_all2 Ξ ts1 (patch t 0 ts1 ts2)
                (cells_agree_patch Ξ t 0 ts1 ts2 clΞ hop hag)) as [hall].
    constructor. rewrite <- heq.
    exact (@ws_cumul_pb_subst_lift cf Σ wfΣ pb Ξ ts1 (patch t 0 ts1 ts2) N m t
             clΞ hall (eq_sym hm) hN hof).
  Qed.

  (** ** The same-code rule

    [conv_same_code] answers [true] only when the two environments agree on the global
    offset and the number of slots, [code_eq] accepts the two codes, and every slot the
    code can see is convertible. [code_eq] accepts in two ways
    ([PCUICCallByNeedSoundMemo.code_eq_sound]): the two codes have the *same term*, which
    is where the identifier fast path lands, or the cached syntactic comparison
    [eqb_term_upto_univ] at [Conv] says yes, which needs the universes of both terms to be
    well formed. The second hypothesis below asks for that exactly when the identifiers
    differ, so [conv_same_code_sound_same_id] can drop it. *)
  Lemma conv_same_code_sound :
    forall (d : cbn_fuel) (lvl : nat) (Ξ : context) (pb : conv_pb)
      (e1 : cbn_env) (c1 : code) (e2 : cbn_env) (c2 : code)
      (ce1 ce2 : code_entry) (ts1 ts2 : list term)
      (rs : list root) (s : cbn_state) (rs' : list root) (s' : cbn_state),
      slot_seam_below d ->
      cok lvl s -> #|Ξ| = lvl -> is_closed_context Ξ -> nctx <= lvl ->
      PTree.get c1.(c_entry) ((s.(st_memo)).(m_codes)) = Some ce1 -> code_inv ce1 c1 ->
      PTree.get c2.(c_entry) ((s.(st_memo)).(m_codes)) = Some ce2 -> code_inv ce2 c2 ->
      (same_id c1 c2 = false ->
       wf_universes Σ (c1.(c_term)) /\ wf_universes Σ (c2.(c_term))) ->
      repr_slots nctx (s.(st_heap)) lvl (e1.(ev_vals)) ts1 ->
      repr_slots nctx (s.(st_heap)) lvl (e2.(ev_vals)) ts2 ->
      e1.(ev_nvals) = #|e1.(ev_vals)| -> e2.(ev_nvals) = #|e2.(ev_vals)| ->
      forallb (is_open_term Ξ) ts1 = true ->
      forallb (is_open_term Ξ) ts2 = true ->
      (lvl - nctx + e1.(ev_goff)) <= #|Ξ| ->
      on_free_vars
        (shiftnP (e1.(ev_nvals) + (#|Ξ| - (lvl - nctx + e1.(ev_goff))))
           (fun _ : nat => false))
        (c1.(c_term)) ->
      is_open_term Ξ
        (subst ts2 0 (lift (lvl - nctx + e2.(ev_goff)) (e2.(ev_nvals)) (c2.(c_term)))) ->
      conv_same_code X_type X Γ nctx stress d lvl e1 c1 e2 c2 rs s = COk (true, rs', s') ->
      Forall2 (root_pres nctx (s.(st_heap)) (s'.(st_heap))) rs rs'
      /\ cok lvl s'
      /\ ∥ Σ ;;; Ξ ⊢
             subst ts1 0 (lift (lvl - nctx + e1.(ev_goff)) (e1.(ev_nvals)) (c1.(c_term)))
             ≤[pb]
             subst ts2 0 (lift (lvl - nctx + e2.(ev_goff)) (e2.(ev_nvals)) (c2.(c_term)))
           ∥.
  Proof.
    intros d lvl Ξ pb e1 c1 e2 c2 ce1 ce2 ts1 ts2 rs s rs' s'
      hseam hok hlen clΞ hnc hg1 hi1 hg2 hi2 hwf hr1 hr2 hnv hnv2 ho1 ho2 hN hof hopen2 he.
    destruct d as [|k]; [cbn in he; discriminate he|].
    rewrite conv_same_code_eq in he.
    destruct ((e1.(ev_goff) == e2.(ev_goff)) && (e1.(ev_nvals) == e2.(ev_nvals)))
      eqn:Eeq; [|discriminate he].
    apply andb_true_iff in Eeq as [Eg En].
    assert (hgoff : e1.(ev_goff) = e2.(ev_goff)) by (apply eqb_eq; exact Eg).
    assert (hnval : e1.(ev_nvals) = e2.(ev_nvals)) by (apply eqb_eq; exact En).
    (* the code test: it changes only the caches *)
    assert (hmi : memo_inv X_type X s) by exact (cok_memo_inv lvl s hok).
    destruct (memo_inv_code_eq X_type X c1 c2 ce1 ce2 s hmi hg1 hi1 hg2 hi2)
      as (hmi' & hcodes & hheap & hnext & _ & _ & hgam).
    assert (hok2 : cok lvl (snd (code_eq X_type X c1 c2 s)))
      by exact (cok_same lvl s _ hok hmi' hheap hnext hgam hcodes).
    destruct (code_eq X_type X c1 c2 s) as [b2 s2] eqn:Ece.
    cbn [fst snd] in hok2, hcodes, hheap, hnext, hgam.
    destruct b2; [|discriminate he].
    (* the slots *)
    assert (hlent : #|ts1| = #|ts2|).
    { rewrite (repr_slots_length nctx lvl (s.(st_heap)) _ _ hr1),
        (repr_slots_length nctx lvl (s.(st_heap)) _ _ hr2).
      rewrite <- hnv, <- hnv2. exact hnval. }
    rewrite <- hheap in hr1, hr2.
    destruct (same_code_cells_sound (k tt) lvl Ξ (c1.(c_term)) 0
                (e1.(ev_vals)) (e2.(ev_vals)) ts1 ts2 rs s2 rs' s'
                (slot_seam_below_step k hseam) hok2 hlen clΞ hnc hr1 hr2 ho1 ho2 he)
      as (hp & hok' & hag).
    rewrite hheap in hp, hr1, hr2.
    split; [exact hp|]. split; [exact hok'|].
    (* the two readings *)
    rewrite <- hgoff, <- hnval.
    assert (hsubst : ∥ Σ ;;; Ξ ⊢
              subst ts1 0 (lift (lvl - nctx + e1.(ev_goff)) (e1.(ev_nvals)) (c1.(c_term)))
              ≤[pb]
              subst ts2 0 (lift (lvl - nctx + e1.(ev_goff)) (e1.(ev_nvals)) (c1.(c_term)))
            ∥).
    { apply (cells_agree_subst Ξ (c1.(c_term)) ts1 ts2); try assumption.
      rewrite hnv. symmetry. exact (repr_slots_length nctx lvl (s.(st_heap)) _ _ hr1). }
    (* either the two codes have one term, or they are equal up to universes *)
    assert (Ece' : fst (code_eq X_type X c1 c2 s) = true) by (rewrite Ece; reflexivity).
    destruct (code_eq_sound X_type X c1 c2 ce1 ce2 s (cok_ceq_ok lvl s hok)
                hg1 hi1 hg2 hi2 Ece') as [hterm|hceq].
    - rewrite <- hterm. exact hsubst.
    - destruct (same_id c1 c2) eqn:Esid.
      + rewrite <- (same_id_sound_table ((s.(st_memo)).(m_codes)) ce1 ce2 c1 c2
                      Esid hg1 hi1 hg2 hi2).
        exact hsubst.
      + destruct (hwf eq_refl) as [hw1 hw2].
        destruct hsubst as [hsubst]. constructor.
        refine (@ws_cumul_pb_conv_trans_r cf Σ wfΣ pb Ξ _ _ _ hsubst _).
        apply (@ws_cumul_pb_compare_term cf Σ Conv Ξ); [exact clΞ| | |].
        * exact (@ws_cumul_pb_is_open_term_right cf pb Σ wfΣ Ξ _ _ hsubst).
        * rewrite hnval, hgoff. exact hopen2.
        * apply subst_eq_term.
          apply (eq_term_upto_univ_lift Σ (compare_universe Σ) (compare_sort Σ) Conv
                   (lvl - nctx + e1.(ev_goff)) 0 (e1.(ev_nvals))).
          exact (cbn_ceq_term_sound X_type X Σ hΣ (c1.(c_term)) (c2.(c_term))
                   hw1 hw2 hceq).
  Qed.

  (** The identifier fast path: two codes with the same identifier, each the code of an
    entry of one table, have one and the same term ([same_id_sound_table]), so the rule is
    sound with no term comparison at all — and so with no universe check. *)
  Lemma same_id_terms (codes : PTree.t code_entry) (ce1 ce2 : code_entry)
      (c1 c2 : code) :
    same_id c1 c2 = true ->
    PTree.get c1.(c_entry) codes = Some ce1 -> code_inv ce1 c1 ->
    PTree.get c2.(c_entry) codes = Some ce2 -> code_inv ce2 c2 ->
    c1.(c_term) = c2.(c_term).
  Proof.
    intros h g1 i1 g2 i2. exact (same_id_sound_table codes ce1 ce2 c1 c2 h g1 i1 g2 i2).
  Qed.

  Lemma conv_same_code_sound_same_id :
    forall (d : cbn_fuel) (lvl : nat) (Ξ : context) (pb : conv_pb)
      (e1 : cbn_env) (c1 : code) (e2 : cbn_env) (c2 : code)
      (ce1 ce2 : code_entry) (ts1 ts2 : list term)
      (rs : list root) (s : cbn_state) (rs' : list root) (s' : cbn_state),
      slot_seam_below d ->
      cok lvl s -> #|Ξ| = lvl -> is_closed_context Ξ -> nctx <= lvl ->
      same_id c1 c2 = true ->
      PTree.get c1.(c_entry) ((s.(st_memo)).(m_codes)) = Some ce1 -> code_inv ce1 c1 ->
      PTree.get c2.(c_entry) ((s.(st_memo)).(m_codes)) = Some ce2 -> code_inv ce2 c2 ->
      repr_slots nctx (s.(st_heap)) lvl (e1.(ev_vals)) ts1 ->
      repr_slots nctx (s.(st_heap)) lvl (e2.(ev_vals)) ts2 ->
      e1.(ev_nvals) = #|e1.(ev_vals)| -> e2.(ev_nvals) = #|e2.(ev_vals)| ->
      forallb (is_open_term Ξ) ts1 = true ->
      forallb (is_open_term Ξ) ts2 = true ->
      (lvl - nctx + e1.(ev_goff)) <= #|Ξ| ->
      on_free_vars
        (shiftnP (e1.(ev_nvals) + (#|Ξ| - (lvl - nctx + e1.(ev_goff))))
           (fun _ : nat => false))
        (c1.(c_term)) ->
      is_open_term Ξ
        (subst ts2 0 (lift (lvl - nctx + e2.(ev_goff)) (e2.(ev_nvals)) (c2.(c_term)))) ->
      conv_same_code X_type X Γ nctx stress d lvl e1 c1 e2 c2 rs s = COk (true, rs', s') ->
      Forall2 (root_pres nctx (s.(st_heap)) (s'.(st_heap))) rs rs'
      /\ cok lvl s'
      /\ ∥ Σ ;;; Ξ ⊢
             subst ts1 0 (lift (lvl - nctx + e1.(ev_goff)) (e1.(ev_nvals)) (c1.(c_term)))
             ≤[pb]
             subst ts2 0 (lift (lvl - nctx + e2.(ev_goff)) (e2.(ev_nvals)) (c2.(c_term)))
           ∥.
  Proof.
    intros d lvl Ξ pb e1 c1 e2 c2 ce1 ce2 ts1 ts2 rs s rs' s'
      hseam hok hlen clΞ hnc hsid hg1 hi1 hg2 hi2 hr1 hr2 hnv hnv2 ho1 ho2 hN hof hopen2 he.
    apply (conv_same_code_sound d lvl Ξ pb e1 c1 e2 c2 ce1 ce2 ts1 ts2 rs s rs' s');
      try assumption.
    intros hf. rewrite hsid in hf. discriminate hf.
  Qed.
End Conv.
