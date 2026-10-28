(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require String2pos CanonicalTries.
From MetaRocq.Common Require Import config Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICTyping PCUICEquality PCUICCumulativity PCUICOnFreeVars
  PCUICClosed PCUICSubstitution PCUICContexts PCUICWfUniverses
  PCUICWellScopedCumulativity PCUICConversion PCUICSigmaCalculus.
From MetaRocq.SafeChecker Require Import PCUICEqualityDec PCUICWfEnv PCUICCallByNeed
  PCUICCallByNeedSound PCUICCallByNeedSoundGC PCUICCallByNeedSoundCtx
  PCUICCallByNeedSoundMemo PCUICCallByNeedSoundCong PCUICCallByNeedSoundHook
  PCUICCallByNeedSoundEval PCUICCallByNeedSoundLevel PCUICCallByNeedSoundHeapWf.
From MetaRocq.PCUIC Require PCUICConfluence PCUICOnFreeVarsConv PCUICRenameConv.

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

(** ** Pushing fresh variables in front of a substitution

  When the comparison pushes [n] fresh variables and reads a child at the higher level,
  the child's substitution is the fresh variables' readings [idsn n] in front of the old
  slot readings lifted by [n]. [subst_push_fresh] says that this reading is the parent's
  one with the substitution started [n] binders further in; [k] counts the binders already
  crossed inside the term. *)

Lemma pushA_map2_ext {A B C : Type} (P : A -> Type) (f1 f2 : A -> B) (g1 g2 : B -> C)
  (l : list A) :
  All P l -> (forall x, P x -> g1 (f1 x) = g2 (f2 x)) ->
  map g1 (map f1 l) = map g2 (map f2 l).
Proof.
  intros HA Hf. induction HA as [|x l Px HA IH]; cbn; [reflexivity|].
  f_equal; [exact (Hf x Px) | exact IH].
Qed.

Lemma subst_push_fresh (n m N : nat) (ts : list term) :
  #|ts| = m ->
  forall (t : term) (k : nat),
    subst (idsn n ++ map (lift0 n) ts) k (lift (N + n) (k + (n + m)) t)
    = subst ts (k + n) (lift N (k + (n + m)) t).
Proof.
  intros Hlen t.
  assert (HL : #|idsn n ++ map (lift0 n) ts| = n + m).
  { rewrite length_app. rewrite idsn_length. rewrite length_map. lia. }
  elim t using term_forall_list_ind.
  - (* tRel *)
    intros r k. cbn [lift].
    destruct (k + (n + m) <=? r) eqn:E1.
    + (* above the lift's cut: both sides fall past the end of their substitution *)
      apply Nat.leb_le in E1. cbn [subst].
      assert (E2 : (k <=? N + n + r) = true) by (apply Nat.leb_le; lia).
      assert (E3 : (k + n <=? N + r) = true) by (apply Nat.leb_le; lia).
      assert (E4 : nth_error (idsn n ++ map (lift0 n) ts) (N + n + r - k) = None)
        by (apply nth_error_None; lia).
      assert (E5 : nth_error ts (N + r - (k + n)) = None)
        by (apply nth_error_None; lia).
      rewrite E2. rewrite E3. rewrite E4. rewrite E5. rewrite HL. rewrite Hlen.
      cbv beta iota. f_equal. lia.
    + apply Nat.leb_gt in E1. cbn [subst].
      destruct (k <=? r) eqn:E2.
      * apply Nat.leb_le in E2.
        destruct (Nat.lt_ge_cases r (k + n)) as [Hlt|Hge].
        -- (* a fresh variable *)
           assert (E3 : (k + n <=? r) = false) by (apply Nat.leb_gt; lia).
           rewrite E3.
           assert (H1 : r - k < #|idsn n|) by (rewrite idsn_length; lia).
           rewrite (nth_error_app_lt _ _ _ H1).
           assert (H2 : r - k < n) by lia.
           rewrite (idsn_lt H2).
           cbn [lift Nat.leb]. f_equal. lia.
        -- (* an old slot *)
           assert (E3 : (k + n <=? r) = true) by (apply Nat.leb_le; lia).
           rewrite E3.
           assert (H1 : #|idsn n| <= r - k) by (rewrite idsn_length; lia).
           rewrite (nth_error_app_ge _ _ _ H1).
           rewrite idsn_length. rewrite nth_error_map.
           replace (r - k - n) with (r - (k + n)) by lia.
           destruct (nth_error ts (r - (k + n))) as [x|] eqn:E4.
           ++ cbn [option_map].
              exact (simpl_lift x n 0 k 0 (Nat.le_0_l _) (Nat.le_refl 0)).
           ++ apply nth_error_None in E4. lia.
      * (* below the substitution's start *)
        apply Nat.leb_gt in E2.
        assert (E3 : (k + n <=? r) = false) by (apply Nat.leb_gt; lia).
        rewrite E3. reflexivity.
  - (* tVar *) intros; reflexivity.
  - (* tEvar *)
    intros ev l Hl k. cbn [lift subst]. f_equal.
    apply (pushA_map2_ext _ _ _ _ _ _ Hl). intros x Px. exact (Px k).
  - (* tSort *) intros; reflexivity.
  - (* tProd *)
    intros na A IHA B IHB k. cbn [lift subst].
    f_equal; [exact (IHA k) | exact (IHB (S k))].
  - (* tLambda *)
    intros na A IHA B IHB k. cbn [lift subst].
    f_equal; [exact (IHA k) | exact (IHB (S k))].
  - (* tLetIn *)
    intros na b IHb ty IHty B IHB k. cbn [lift subst].
    f_equal; [exact (IHb k) | exact (IHty k) | exact (IHB (S k))].
  - (* tApp *)
    intros u v IHu IHv k. cbn [lift subst].
    f_equal; [exact (IHu k) | exact (IHv k)].
  - (* tConst *) intros; reflexivity.
  - (* tInd *) intros; reflexivity.
  - (* tConstruct *) intros; reflexivity.
  - (* tCase *)
    intros ci p Hp c IHc brs Hbrs k. cbn [lift subst].
    destruct Hp as [Hpar [Hctx Hret]].
    f_equal.
    + unfold map_predicate_k. cbn [pparams puinst pcontext preturn]. f_equal.
      * apply (pushA_map2_ext _ _ _ _ _ _ Hpar). intros x Px. exact (Px k).
      * pose proof (Hret (#|pcontext p| + k)) as E.
        rewrite <- (Nat.add_assoc #|pcontext p| k (n + m)) in E.
        rewrite <- (Nat.add_assoc #|pcontext p| k n) in E.
        exact E.
    + exact (IHc k).
    + apply (pushA_map2_ext _ _ _ _ _ _ Hbrs). intros br [Pctx Pbody].
      unfold map_branch_k. cbn [bcontext bbody]. f_equal.
      pose proof (Pbody (#|bcontext br| + k)) as E.
      rewrite <- (Nat.add_assoc #|bcontext br| k (n + m)) in E.
      rewrite <- (Nat.add_assoc #|bcontext br| k n) in E.
      exact E.
  - (* tProj *)
    intros pr c IHc k. cbn [lift subst]. f_equal. exact (IHc k).
  - (* tFix *)
    intros mfix idx Hm k. cbn [lift subst]. f_equal.
    rewrite !length_map.
    apply (pushA_map2_ext _ _ _ _ _ _ Hm). intros d [Pty Pbody].
    unfold map_def. cbn [dname dtype dbody rarg]. f_equal.
    + exact (Pty k).
    + pose proof (Pbody (#|mfix| + k)) as E.
      rewrite <- (Nat.add_assoc #|mfix| k (n + m)) in E.
      rewrite <- (Nat.add_assoc #|mfix| k n) in E.
      exact E.
  - (* tCoFix *)
    intros mfix idx Hm k. cbn [lift subst]. f_equal.
    rewrite !length_map.
    apply (pushA_map2_ext _ _ _ _ _ _ Hm). intros d [Pty Pbody].
    unfold map_def. cbn [dname dtype dbody rarg]. f_equal.
    + exact (Pty k).
    + pose proof (Pbody (#|mfix| + k)) as E.
      rewrite <- (Nat.add_assoc #|mfix| k (n + m)) in E.
      rewrite <- (Nat.add_assoc #|mfix| k n) in E.
      exact E.
  - (* tPrim *)
    intros prim Hprim k. cbn [lift subst].
    destruct prim as [tg [? | ? | ? | a]]; cbn in Hprim |- *; try reflexivity.
    destruct Hprim as [Hty [Hdef Hval]].
    assert (E3 : map (subst (idsn n ++ map (lift0 n) ts) k)
                   (map (lift (N + n) (k + (n + m))) (array_value a))
                 = map (subst ts (k + n)) (map (lift N (k + (n + m))) (array_value a))).
    { apply (pushA_map2_ext _ _ _ _ _ _ Hval). intros y Py. exact (Py k). }
    unfold mapu_array_model. cbn [array_level array_type array_default array_value].
    rewrite (Hty k). rewrite (Hdef k). rewrite E3. reflexivity.
Qed.

Lemma subst_push_fresh0 (n m N : nat) (ts : list term) (t : term) :
  #|ts| = m ->
  subst (idsn n ++ map (lift0 n) ts) 0 (lift (N + n) (n + m) t)
  = subst ts n (lift N (n + m) t).
Proof.
  intros Hlen. exact (subst_push_fresh n m N ts Hlen t 0).
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

(** ** Allocation and renaming facts for the stuck-match rule

  [push_fresh] allocates one cell per fresh variable and pushes its address on both
  environments; an allocation may collect first. What the rule needs: renaming keeps an
  environment's shape, an allocation keeps the caller's roots, and [push_fresh] pushes the
  SAME addresses on both environments, each reading back as the variable it stands for.

  The "same addresses" part rests on the collector being a function on addresses: once
  [gc_copy] has copied an address, the old heap holds [CFwd a'] there for the rest of the
  walk ([pfd_gc_copy_fwd_le]), so a second visit of the address returns the same [a']
  ([pfd_gc_copy_on_fwd]). The induction on [n] carries the addresses already pushed as a
  common prefix of both environments ([pfd_push_fresh_prefix]). *)

Section ConvPartD.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat) (stress : bool).

  (** *** List helpers *)

  Lemma pfd_forall2_impl {A B : Type} {R Q : A -> B -> Prop} {l : list A} {l' : list B} :
    Forall2 R l l' -> (forall a b, R a b -> Q a b) -> Forall2 Q l l'.
  Proof. intros h himp. induction h; constructor; auto. Qed.

  Lemma pfd_forall2_head {A B : Type} {R : A -> B -> Prop} {a : A} {b : B} {l : list A}
      {l' : list B} :
    Forall2 R (a :: l) (b :: l') -> R a b.
  Proof. intros h. inversion h; assumption. Qed.

  Lemma pfd_forall2_tail {A B : Type} {R : A -> B -> Prop} {a : A} {b : B} {l : list A}
      {l' : list B} :
    Forall2 R (a :: l) (b :: l') -> Forall2 R l l'.
  Proof. intros h. inversion h; assumption. Qed.

  (** *** 1. Renaming keeps an environment's shape *)

  Lemma rn_slots_length {G : Type} (f : haddr -> G -> cbn_res (haddr * G))
      (l : list cbn_slot) (g : G) (l' : list cbn_slot) (g' : G) :
    rn_slots f l g = COk (l', g') -> #|l'| = #|l|.
  Proof. exact (PCUICCallByNeed.rn_slots_length f l g l' g'). Qed.

  Lemma rn_env_shape {G : Type} (f : haddr -> G -> cbn_res (haddr * G))
      (e : cbn_env) (g : G) (e' : cbn_env) (g' : G) :
    rn_env f e g = COk (e', g') ->
    e'.(ev_nvals) = e.(ev_nvals) /\ e'.(ev_goff) = e.(ev_goff)
    /\ #|e'.(ev_vals)| = #|e.(ev_vals)|.
  Proof.
    intros h. destruct (PCUICCallByNeed.rn_env_shape f e g e' g' h) as [hn ho].
    exact (conj hn (conj ho (rn_env_length f e g e' g' h))).
  Qed.

  Lemma pfd_rn_root_RE {G : Type} (f : haddr -> G -> cbn_res (haddr * G)) (e : cbn_env)
      (g : G) :
    rn_root f (RE e) g =
    match rn_env f e g with
    | COk (e', g') => COk (RE e', g')
    | CFail w => CFail w
    end.
  Proof. reflexivity. Qed.

  Lemma pfd_rn_env_mk {G : Type} (f : haddr -> G -> cbn_res (haddr * G))
      (vs : list cbn_slot) (n o : nat) (g : G) :
    rn_env f (mkEnv vs n o) g =
    match rn_slots f vs g with
    | COk (vs', g') => COk (mkEnv vs' n o, g')
    | CFail w => CFail w
    end.
  Proof. reflexivity. Qed.

  Lemma pfd_rn_slots_cons {G : Type} (f : haddr -> G -> cbn_res (haddr * G))
      (y : cbn_slot) (l : list cbn_slot) (g : G) :
    rn_slots f (y :: l) g =
    match rn_slot f y g with
    | COk (y', g1) =>
      match rn_slots f l g1 with
      | COk (l', g2) => COk (y' :: l', g2)
      | CFail w => CFail w
      end
    | CFail w => CFail w
    end.
  Proof. reflexivity. Qed.

  Lemma pfd_rn_slot_SAddr {G : Type} (f : haddr -> G -> cbn_res (haddr * G)) (a : haddr)
      (g : G) :
    rn_slot f (SAddr a) g =
    match f a g with
    | COk (a', g') => COk (SAddr a', g')
    | CFail w => CFail w
    end.
  Proof. reflexivity. Qed.

  Lemma collect_env_shape (e : cbn_env) (rs : list root) (s : cbn_state)
      (rs' : list root) (s' : cbn_state) :
    collect (RE e :: rs) s = COk (rs', s') ->
    exists (e' : cbn_env) (rs2 : list root),
      rs' = RE e' :: rs2 /\ e'.(ev_nvals) = e.(ev_nvals) /\ e'.(ev_goff) = e.(ev_goff)
      /\ #|e'.(ev_vals)| = #|e.(ev_vals)|.
  Proof.
    intros he. destruct (collect_inv _ _ _ _ he) as (gm & g1 & g2 & hr & _).
    set (F := fuel_of_pos (st_next s) (fun _ : unit => FO)) in hr.
    rewrite rn_roots_cons, pfd_rn_root_RE in hr.
    destruct (rn_env (gc_copy F) e g1) as [[e' ga]|w] eqn:E1; [|discriminate].
    cbv beta iota in hr.
    destruct (rn_roots (gc_copy F) rs ga) as [[rs2 gb]|w] eqn:E2; [|discriminate].
    cbv beta iota in hr. injection hr as hrs hg. subst rs'.
    exists e', rs2. split; [reflexivity|]. exact (rn_env_shape _ _ _ _ _ E1).
  Qed.

  (** *** 2. An allocation keeps the caller's roots *)

  Lemma root_pres_heap_le (H H' : bheap cbn_cell) (r : root) :
    heap_le H H' -> root_pres nctx H H' r r.
  Proof.
    intros hle. destruct (repr_mono nctx H H' hle) as (ha & has & hc & hsl & hss & hsu & hv).
    unfold root_pres. destruct r; cbn; intros; eauto.
  Qed.

  Lemma pfd_root_pres_trans (H1 H2 H3 : bheap cbn_cell) (r1 r2 r3 : root) :
    root_pres nctx H1 H2 r1 r2 -> root_pres nctx H2 H3 r2 r3 -> root_pres nctx H1 H3 r1 r3.
  Proof.
    unfold root_pres. destruct r1, r2, r3; cbn; intros h1 h2;
      first [contradiction | intros; apply h2; apply h1; assumption].
  Qed.

  Lemma pfd_root_pres_mono (H1 H2 H3 : bheap cbn_cell) (r r' : root) :
    root_pres nctx H1 H2 r r' -> heap_le H2 H3 -> root_pres nctx H1 H3 r r'.
  Proof.
    intros h hle. exact (pfd_root_pres_trans _ _ _ _ _ _ h (root_pres_heap_le _ _ r' hle)).
  Qed.

  Lemma pfd_roots_refl (H H' : bheap cbn_cell) (hle : heap_le H H') (rs : list root) :
    Forall2 (root_pres nctx H H') rs rs.
  Proof.
    induction rs as [|r rs ih]; constructor; [exact (root_pres_heap_le H H' r hle)|exact ih].
  Qed.

  Lemma pfd_roots_trans (H1 H2 H3 : bheap cbn_cell) :
    forall (l1 l2 l3 : list root),
      Forall2 (root_pres nctx H1 H2) l1 l2 -> Forall2 (root_pres nctx H2 H3) l2 l3 ->
      Forall2 (root_pres nctx H1 H3) l1 l3.
  Proof.
    intros l1 l2 l3 h12. revert l3.
    induction h12 as [|a b l1 l2 hab h12 ih]; intros l3 h23.
    - destruct l3 as [|c l3]; [constructor|inversion h23].
    - destruct l3 as [|c l3]; [inversion h23|].
      constructor.
      + exact (pfd_root_pres_trans _ _ _ _ _ _ hab (pfd_forall2_head h23)).
      + exact (ih _ (pfd_forall2_tail h23)).
  Qed.

  Lemma pfd_roots_mono (H1 H2 H3 : bheap cbn_cell) (l l' : list root) :
    Forall2 (root_pres nctx H1 H2) l l' -> heap_le H2 H3 ->
    Forall2 (root_pres nctx H1 H3) l l'.
  Proof. intros h hle. exact (pfd_roots_trans _ _ _ _ _ _ h (pfd_roots_refl _ _ hle l')). Qed.

  Lemma alloc_roots (lo : positive) (cl : cbn_cell) (rs : list root) (s : cbn_state)
      (a : haddr) (rs' : list root) (s' : cbn_state) :
    state_ok lo s -> heap_nofwd (s.(st_heap)) ->
    (forall (G : Type) (f : haddr -> G -> cbn_res (haddr * G)) (g : G),
        rn_cell f cl g = COk (cl, g)) ->
    alloc stress cl rs s = COk (a, rs', s') ->
    Forall2 (root_pres nctx (s.(st_heap)) (s'.(st_heap))) rs rs'.
  Proof.
    intros hs hnf hrn e. unfold alloc in e.
    destruct (gc_due stress s) eqn:Egc.
    - destruct (collect (RC cl :: rs) s) as [[rs2 s2]|w] eqn:Ec; [|discriminate].
      destruct (collect_cons_cell cl rs rs2 s s2 hrn Ec) as [rs3 ->].
      destruct (collect_sound nctx _ _ _ _ hnf Ec) as (hok2 & _ & _ & _ & hfa & _).
      pose proof (pfd_forall2_tail hfa) as hfa'.
      cbv beta iota in e.
      destruct (alloc_now cl s2) as [a2 s3] eqn:Ea.
      cbv beta iota in e. injection e as e1 e2 e3. subst a rs' s'.
      pose proof (alloc_now_heap_le _ cl s2 (so_heap _ _ hok2)) as hle.
      rewrite Ea in hle. cbn [snd] in hle.
      exact (pfd_roots_mono _ _ _ _ _ hfa' hle).
    - cbv beta iota in e.
      destruct (alloc_now cl s) as [a2 s3] eqn:Ea.
      cbv beta iota in e. injection e as e1 e2 e3. subst a rs' s'.
      pose proof (alloc_now_heap_le _ cl s (so_heap _ _ hs)) as hle.
      rewrite Ea in hle. cbn [snd] in hle.
      exact (pfd_roots_refl _ _ hle rs).
  Qed.

  (** *** 3. What [push_fresh] builds *)

  (** **** A renaming threads its state monotonically when its address map does *)
  Section RnPres.
    Context {G : Type} (f : haddr -> G -> cbn_res (haddr * G)) (R : G -> G -> Prop)
      (Rrefl : forall g, R g g)
      (Rtrans : forall g1 g2 g3, R g1 g2 -> R g2 g3 -> R g1 g3)
      (hf : forall a g a' g', f a g = COk (a', g') -> R g g').

    Lemma pfd_rn_addrs : forall (l : list haddr) (g : G) (l' : list haddr) (g' : G),
      rn_addrs f l g = COk (l', g') -> R g g'.
    Proof.
      induction l as [|a l ih]; intros g l' g' he; simpl in he.
      - injection he as hl hg. subst g'. apply Rrefl.
      - destruct (f a g) as [[b g1]|w] eqn:e1; [|discriminate].
        cbv beta iota in he.
        destruct (rn_addrs f l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
        cbv beta iota in he. injection he as hl hg. subst g'.
        exact (Rtrans _ _ _ (hf _ _ _ _ e1) (ih _ _ _ e2)).
    Qed.

    Lemma pfd_rn_slot : forall (x : cbn_slot) (g : G) (x' : cbn_slot) (g' : G),
      rn_slot f x g = COk (x', g') -> R g g'.
    Proof.
      intros x. induction x as [a|vs n o c ihvs] using slot_ind'; intros g x' g' he.
      - rewrite pfd_rn_slot_SAddr in he.
        destruct (f a g) as [[b g1]|w] eqn:e1; [|discriminate].
        cbv beta iota in he. injection he as hx hg. subst g'. exact (hf _ _ _ _ e1).
      - rewrite rn_slot_SInl in he.
        destruct (rn_slots f vs g) as [[vs' g1]|w] eqn:e1; [|discriminate].
        cbv beta iota in he. injection he as hx hg. subst x' g'.
        revert g vs' g1 e1.
        induction ihvs as [|y vs hy hvs ihl]; intros g vs' g1 e1; simpl in e1.
        + injection e1 as hv hg. subst g1. apply Rrefl.
        + destruct (rn_slot f y g) as [[y' ga]|wa] eqn:ea; [|discriminate].
          cbv beta iota in e1.
          destruct (rn_slots f vs ga) as [[vs2 gb]|wb] eqn:eb; [|discriminate].
          cbv beta iota in e1. injection e1 as hv hg. subst g1.
          exact (Rtrans _ _ _ (hy _ _ _ ea) (ihl _ _ _ eb)).
    Qed.

    Lemma pfd_rn_slots : forall (l : list cbn_slot) (g : G) (l' : list cbn_slot) (g' : G),
      rn_slots f l g = COk (l', g') -> R g g'.
    Proof.
      induction l as [|y l ih]; intros g l' g' he.
      - simpl in he. injection he as hl hg. subst g'. apply Rrefl.
      - rewrite pfd_rn_slots_cons in he.
        destruct (rn_slot f y g) as [[y' g1]|w] eqn:e1; [|discriminate].
        cbv beta iota in he.
        destruct (rn_slots f l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
        cbv beta iota in he. injection he as hl hg. subst g'.
        exact (Rtrans _ _ _ (pfd_rn_slot _ _ _ _ e1) (ih _ _ _ e2)).
    Qed.

    Lemma pfd_rn_env (e : cbn_env) (g : G) (e' : cbn_env) (g' : G) :
      rn_env f e g = COk (e', g') -> R g g'.
    Proof.
      intros he. destruct e as [vals n o]. rewrite pfd_rn_env_mk in he.
      destruct (rn_slots f vals g) as [[vs g1]|w] eqn:e1; [|discriminate].
      cbv beta iota in he. injection he as hv hg. subst g'.
      exact (pfd_rn_slots _ _ _ _ e1).
    Qed.

    Lemma pfd_rn_value (v : cbn_value) (g : G) (v' : cbn_value) (g' : G) :
      rn_value f v g = COk (v', g') -> R g g'.
    Proof.
      intros he.
      destruct v as [hd sp|e c|e c i sp|e c i sp|hd sp|e c|e c sp]; unfold rn_value in he.
      - destruct (rn_addrs f sp g) as [[sp' g1]|w] eqn:e1; [|discriminate].
        cbv beta iota in he. injection he as hv hg. subst g'.
        exact (pfd_rn_addrs _ _ _ _ e1).
      - destruct (rn_env f e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        cbv beta iota in he. injection he as hv hg. subst g'.
        exact (pfd_rn_env _ _ _ _ e1).
      - destruct (rn_env f e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        cbv beta iota in he.
        destruct (rn_addrs f sp g1) as [[sp' g2]|w] eqn:e2; [|discriminate].
        cbv beta iota in he. injection he as hv hg. subst g'.
        exact (Rtrans _ _ _ (pfd_rn_env _ _ _ _ e1) (pfd_rn_addrs _ _ _ _ e2)).
      - destruct (rn_env f e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        cbv beta iota in he.
        destruct (rn_addrs f sp g1) as [[sp' g2]|w] eqn:e2; [|discriminate].
        cbv beta iota in he. injection he as hv hg. subst g'.
        exact (Rtrans _ _ _ (pfd_rn_env _ _ _ _ e1) (pfd_rn_addrs _ _ _ _ e2)).
      - destruct (rn_addrs f sp g) as [[sp' g1]|w] eqn:e1; [|discriminate].
        cbv beta iota in he. injection he as hv hg. subst g'.
        exact (pfd_rn_addrs _ _ _ _ e1).
      - destruct (rn_env f e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        cbv beta iota in he. injection he as hv hg. subst g'.
        exact (pfd_rn_env _ _ _ _ e1).
      - destruct (rn_env f e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        cbv beta iota in he.
        destruct (rn_addrs f sp g1) as [[sp' g2]|w] eqn:e2; [|discriminate].
        cbv beta iota in he. injection he as hv hg. subst g'.
        exact (Rtrans _ _ _ (pfd_rn_env _ _ _ _ e1) (pfd_rn_addrs _ _ _ _ e2)).
    Qed.

    Lemma pfd_rn_cell (cl : cbn_cell) (g : G) (cl' : cbn_cell) (g' : G) :
      rn_cell f cl g = COk (cl', g') -> R g g'.
    Proof.
      intros he. destruct cl as [vals n o c|v| |b]; unfold rn_cell in he.
      - destruct (rn_slots f vals g) as [[vs g1]|w] eqn:e1; [|discriminate].
        cbv beta iota in he. injection he as hc hg. subst g'.
        exact (pfd_rn_slots _ _ _ _ e1).
      - destruct (rn_value f v g) as [[v1 g1]|w] eqn:e1; [|discriminate].
        cbv beta iota in he. injection he as hc hg. subst g'.
        exact (pfd_rn_value _ _ _ _ e1).
      - injection he as hc hg. subst g'. apply Rrefl.
      - destruct (f b g) as [[b1 g1]|w] eqn:e1; [|discriminate].
        cbv beta iota in he. injection he as hc hg. subst g'.
        exact (hf _ _ _ _ e1).
    Qed.
  End RnPres.

  (** **** A forwarding pointer of the old heap stays for the rest of the walk *)
  Definition pfd_fwd_le (g g' : gc_state) : Prop :=
    forall b c, bh_get b g.(g_old) = Some (CFwd c) -> bh_get b g'.(g_old) = Some (CFwd c).

  Lemma pfd_fwd_le_refl (g : gc_state) : pfd_fwd_le g g.
  Proof. intros b c h. exact h. Qed.

  Lemma pfd_fwd_le_trans (g1 g2 g3 : gc_state) :
    pfd_fwd_le g1 g2 -> pfd_fwd_le g2 g3 -> pfd_fwd_le g1 g3.
  Proof. intros h1 h2 b c h. exact (h2 _ _ (h1 _ _ h)). Qed.

  Lemma pfd_fwd_le_write (g g1 : gc_state) (a : haddr) (cl : cbn_cell) (c0 : haddr)
      (old hp : bheap cbn_cell) (nx : positive) :
    bh_get a g.(g_old) = Some cl -> cell_fwd cl = None -> pfd_fwd_le g g1 ->
    bh_upd a (CFwd c0) g1.(g_old) = Some old -> pfd_fwd_le g (mkGc old hp nx).
  Proof.
    intros ha hcl hle e2 b c hb. cbn [g_old].
    assert (hne : b <> a).
    { intros ->. rewrite ha in hb. injection hb as ->. discriminate hcl. }
    rewrite (bh_get_upd_other _ _ _ _ _ e2 hne). exact (hle _ _ hb).
  Qed.

  Lemma pfd_gc_copy_fwd_le : forall (F : cbn_fuel) (a : haddr) (g : gc_state) (a' : haddr)
      (g' : gc_state),
    gc_copy F a g = COk (a', g') -> pfd_fwd_le g g'.
  Proof.
    intros F. induction F as [|k ih]; intros a g a' g' he.
    - rewrite gc_copy_FO in he.
      destruct (bh_get a g.(g_old)) as [cl|] eqn:ea; [|discriminate].
      destruct cl as [vals n o c|v| |b]; try discriminate.
      inversion he; subst. apply pfd_fwd_le_refl.
    - rewrite gc_copy_FS in he.
      destruct (bh_get a g.(g_old)) as [cl|] eqn:ea; [|discriminate].
      destruct cl as [vals n o c|v| |b].
      + destruct (rn_cell (gc_copy (k tt)) (CSusp vals n o c) g) as [[cl1 g1]|w] eqn:e1;
          [|discriminate].
        destruct (bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old)) as [old|] eqn:e2;
          [|discriminate].
        inversion he; subst.
        exact (pfd_fwd_le_write _ _ _ _ _ _ _ _ ea eq_refl
                 (pfd_rn_cell (gc_copy (k tt)) pfd_fwd_le pfd_fwd_le_refl pfd_fwd_le_trans
                    (ih tt) _ _ _ _ e1) e2).
      + destruct (rn_cell (gc_copy (k tt)) (CDone v) g) as [[cl1 g1]|w] eqn:e1;
          [|discriminate].
        destruct (bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old)) as [old|] eqn:e2;
          [|discriminate].
        inversion he; subst.
        exact (pfd_fwd_le_write _ _ _ _ _ _ _ _ ea eq_refl
                 (pfd_rn_cell (gc_copy (k tt)) pfd_fwd_le pfd_fwd_le_refl pfd_fwd_le_trans
                    (ih tt) _ _ _ _ e1) e2).
      + destruct (rn_cell (gc_copy (k tt)) CBusy g) as [[cl1 g1]|w] eqn:e1;
          [|discriminate].
        destruct (bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old)) as [old|] eqn:e2;
          [|discriminate].
        inversion he; subst.
        exact (pfd_fwd_le_write _ _ _ _ _ _ _ _ ea eq_refl
                 (pfd_rn_cell (gc_copy (k tt)) pfd_fwd_le pfd_fwd_le_refl pfd_fwd_le_trans
                    (ih tt) _ _ _ _ e1) e2).
      + inversion he; subst. apply pfd_fwd_le_refl.
  Qed.

  Lemma pfd_gc_copy_on_fwd (F : cbn_fuel) (a : haddr) (g : gc_state) (c : haddr) :
    bh_get a g.(g_old) = Some (CFwd c) -> gc_copy F a g = COk (c, g).
  Proof.
    intros h. destruct F as [|k]; [rewrite gc_copy_FO|rewrite gc_copy_FS]; rewrite h;
      reflexivity.
  Qed.

  (** **** Addresses read through a renaming *)
  Definition pfd_ra (H H' : bheap cbn_cell) (p p' : haddr) : Prop :=
    root_pres nctx H H' (RA p) (RA p').

  Lemma pfd_ra_refl (H H' : bheap cbn_cell) (hle : heap_le H H') (P : list haddr) :
    Forall2 (pfd_ra H H') P P.
  Proof.
    induction P as [|p P ih]; constructor; [exact (root_pres_heap_le H H' (RA p) hle)|exact ih].
  Qed.

  Lemma pfd_ra_trans (H1 H2 H3 : bheap cbn_cell) :
    forall (l1 l2 l3 : list haddr),
      Forall2 (pfd_ra H1 H2) l1 l2 -> Forall2 (pfd_ra H2 H3) l2 l3 ->
      Forall2 (pfd_ra H1 H3) l1 l3.
  Proof.
    intros l1 l2 l3 h12. revert l3.
    induction h12 as [|a b l1 l2 hab h12 ih]; intros l3 h23.
    - destruct l3 as [|c l3]; [constructor|inversion h23].
    - destruct l3 as [|c l3]; [inversion h23|].
      constructor.
      + exact (pfd_root_pres_trans H1 H2 H3 (RA a) (RA b) (RA c) hab (pfd_forall2_head h23)).
      + exact (ih _ (pfd_forall2_tail h23)).
  Qed.

  Lemma pfd_ra_mono (H1 H2 H3 : bheap cbn_cell) (P P' : list haddr) :
    Forall2 (pfd_ra H1 H2) P P' -> heap_le H2 H3 -> Forall2 (pfd_ra H1 H3) P P'.
  Proof. intros h hle. exact (pfd_ra_trans _ _ _ _ _ _ h (pfd_ra_refl _ _ hle P')). Qed.

  Lemma pfd_slots_mono (H H' : bheap cbn_cell) (hle : heap_le H H') (lvl : nat)
      (l : list cbn_slot) (ts : list term) :
    repr_slots nctx H lvl l ts -> repr_slots nctx H' lvl l ts.
  Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (repr_mono nctx H H' hle))))) lvl l ts). Qed.

  (** **** A prefix of addresses, renamed once, then renamed again to the same addresses *)
  Lemma pfd_prefix_first (Hold : bheap cbn_cell) (onext : positive) (F : cbn_fuel) :
    forall (P : list haddr) (B : list cbn_slot) (g : gc_state) (l : list cbn_slot)
      (g' : gc_state),
      gc_inv nctx Hold onext g ->
      rn_slots (gc_copy F) (map SAddr P ++ B) g = COk (l, g') ->
      exists (P' : list haddr) (B' : list cbn_slot),
        l = map SAddr P' ++ B'
        /\ Forall2 (fun p p' => bh_get p g'.(g_old) = Some (CFwd p')
                                /\ pfd_ra Hold g'.(g_heap) p p') P P'
        /\ exists gm : gc_state, gstep nctx Hold onext g gm
                                /\ rn_slots (gc_copy F) B gm = COk (B', g').
  Proof.
    pose proof (gc_copy_ok nctx Hold onext F) as hcp.
    induction P as [|p P ih]; intros B g l g' hinv he.
    - exists [], l. split; [reflexivity|]. split; [constructor|].
      exists g. split; [exact (gstep_refl _ _ _ _ hinv)|exact he].
    - change (map SAddr (p :: P) ++ B) with (SAddr p :: (map SAddr P ++ B)) in he.
      rewrite pfd_rn_slots_cons, pfd_rn_slot_SAddr in he.
      destruct (gc_copy F p g) as [[p' g1]|w] eqn:e1; [|discriminate].
      cbv beta iota in he.
      destruct (rn_slots (gc_copy F) (map SAddr P ++ B) g1) as [[l2 g2]|w] eqn:e2;
        [|discriminate].
      cbv beta iota in he. injection he as hl hg. subst l g'.
      destruct (hcp _ _ _ _ hinv e1) as (hs1 & _ & _ & hr1).
      pose proof (step_inv _ _ _ _ _ hs1) as hinv1.
      destruct (ih B g1 l2 g2 hinv1 e2) as (P1 & B' & -> & hP & gm & hsm & em).
      destruct (rn_slots_ok nctx Hold onext (gc_copy F) hcp _ _ _ _ hinv1 e2) as (hs2 & _).
      pose proof (pfd_rn_slots (gc_copy F) pfd_fwd_le pfd_fwd_le_refl pfd_fwd_le_trans
                    (pfd_gc_copy_fwd_le F) _ _ _ _ e2) as hf2.
      exists (p' :: P1), B'. split; [reflexivity|]. split.
      + constructor; [|exact hP]. split.
        * exact (hf2 _ _ (gc_copy_old_fwd _ _ _ _ _ e1)).
        * intros lvl t ht.
          exact (repr_addr_mono nctx _ _ (step_heap _ _ _ _ _ hs2) _ _ _ (hr1 lvl t ht)).
      + exists gm. split; [exact (gstep_trans _ _ _ _ _ _ hs1 hsm)|exact em].
  Qed.

  Lemma pfd_prefix_again (F : cbn_fuel) :
    forall (P P' : list haddr) (B : list cbn_slot) (g : gc_state) (l : list cbn_slot)
      (g' : gc_state),
      Forall2 (fun p p' => bh_get p g.(g_old) = Some (CFwd p')) P P' ->
      rn_slots (gc_copy F) (map SAddr P ++ B) g = COk (l, g') ->
      exists B' : list cbn_slot,
        l = map SAddr P' ++ B' /\ rn_slots (gc_copy F) B g = COk (B', g').
  Proof.
    intros P P' B g l g' hP. revert l.
    induction hP as [|p p' P P' hp hP ih]; intros l he.
    - exists l. split; [reflexivity|exact he].
    - change (map SAddr (p :: P) ++ B) with (SAddr p :: (map SAddr P ++ B)) in he.
      rewrite pfd_rn_slots_cons, pfd_rn_slot_SAddr, (pfd_gc_copy_on_fwd F p g p' hp) in he.
      cbv beta iota in he.
      remember (rn_slots (gc_copy F) (map SAddr P ++ B) g) as res eqn:e2 in he.
      destruct res as [[l2 g2]|w]; [|discriminate].
      symmetry in e2.
      cbv beta iota in he. injection he as hl hg. subst l g2.
      destruct (ih _ e2) as (B' & -> & hB). exists B'. split; [reflexivity|exact hB].
  Qed.

  (** **** A collection over the two environments of [push_fresh]: their common prefix is
    renamed to one common prefix *)
  Lemma pfd_collect_two_envs (cl : cbn_cell) (P : list haddr) (B1 B2 : list cbn_slot)
      (n1 n2 o1 o2 : nat) (rs : list root) (s : cbn_state) (rs' : list root)
      (s' : cbn_state) :
    heap_nofwd s.(st_heap) ->
    (forall (G : Type) (f : haddr -> G -> cbn_res (haddr * G)) (g : G),
        rn_cell f cl g = COk (cl, g)) ->
    collect (RC cl :: RE (mkEnv (map SAddr P ++ B1) n1 o1)
               :: RE (mkEnv (map SAddr P ++ B2) n2 o2) :: rs) s = COk (rs', s') ->
    exists (P' : list haddr) (B1' B2' : list cbn_slot) (rs2 : list root),
      rs' = RC cl :: RE (mkEnv (map SAddr P' ++ B1') n1 o1)
              :: RE (mkEnv (map SAddr P' ++ B2') n2 o2) :: rs2
      /\ #|B1'| = #|B1| /\ #|B2'| = #|B2|
      /\ Forall2 (pfd_ra s.(st_heap) s'.(st_heap)) P P'
      /\ root_pres nctx s.(st_heap) s'.(st_heap) (RSk B1) (RSk B1')
      /\ root_pres nctx s.(st_heap) s'.(st_heap) (RSk B2) (RSk B2').
  Proof.
    intros hnf hrn he. rewrite collect_eq in he.
    set (F := fuel_of_pos (st_next s) (fun _ : unit => FO)) in he.
    destruct (rn_ptree (gc_copy F) (st_gam s)
                (mkGc (st_heap s) (bh_holes (st_next s)) (st_next s))) as [[gm g1]|w1] eqn:e1;
      [|discriminate].
    cbv beta iota in he.
    destruct (rn_roots (gc_copy F)
                (RC cl :: RE (mkEnv (map SAddr P ++ B1) n1 o1)
                   :: RE (mkEnv (map SAddr P ++ B2) n2 o2) :: rs) g1) as [[rs3 g2]|w2] eqn:e2;
      [|discriminate].
    cbv beta iota in he. injection he as hrs hs. subst rs' s'.
    assert (hinv0 : gc_inv nctx (st_heap s) (st_next s)
                      (mkGc (st_heap s) (bh_holes (st_next s)) (st_next s))).
    { constructor; cbn.
      - intros a cl0 hc _. exact hc.
      - intros a a' hc. destruct (hnf _ _ hc).
      - apply bh_ok_holes.
      - intros b cl0 hc. rewrite bh_get_holes in hc. discriminate.
      - intros b b' hc. rewrite bh_get_holes in hc. discriminate. }
    pose proof (gc_copy_ok nctx (st_heap s) (st_next s) F) as hcp.
    destruct (rn_ptree_ok nctx (st_heap s) (st_next s) (gc_copy F) hcp _ _ _ _ hinv0 e1)
      as (hs1 & _).
    pose proof (step_inv _ _ _ _ _ hs1) as hinv1.
    rewrite rn_roots_cons, rn_root_RC, hrn in e2. cbv beta iota in e2.
    rewrite rn_roots_cons, pfd_rn_root_RE, pfd_rn_env_mk in e2.
    destruct (rn_slots (gc_copy F) (map SAddr P ++ B1) g1) as [[vs1 ga]|w] eqn:ea;
      [|discriminate].
    cbv beta iota in e2.
    rewrite rn_roots_cons, pfd_rn_root_RE, pfd_rn_env_mk in e2.
    destruct (rn_slots (gc_copy F) (map SAddr P ++ B2) ga) as [[vs2 gb]|w] eqn:eb;
      [|discriminate].
    cbv beta iota in e2.
    destruct (rn_roots (gc_copy F) rs gb) as [[rs4 gc]|w] eqn:ec; [|discriminate].
    cbv beta iota in e2. injection e2 as hrs3 hg2. subst rs3 g2.
    destruct (pfd_prefix_first (st_heap s) (st_next s) F P B1 g1 vs1 ga hinv1 ea)
      as (P' & B1' & -> & hP & gm1 & hsm & em).
    destruct (rn_slots_ok nctx (st_heap s) (st_next s) (gc_copy F) hcp _ _ _ _
                (step_inv _ _ _ _ _ hsm) em) as (hsa & _ & hrB1).
    pose proof (step_inv _ _ _ _ _ hsa) as hinva.
    assert (hPf : Forall2 (fun p p' => bh_get p ga.(g_old) = Some (CFwd p')) P P').
    { refine (pfd_forall2_impl hP _). intros p p' h. exact (proj1 h). }
    destruct (pfd_prefix_again F P P' B2 ga vs2 gb hPf eb) as (B2' & -> & eB2).
    destruct (rn_slots_ok nctx (st_heap s) (st_next s) (gc_copy F) hcp _ _ _ _ hinva eB2)
      as (hsb & _ & hrB2).
    destruct (rn_roots_ok nctx (st_heap s) (st_next s) (gc_copy F) hcp _ _ _ _
                (step_inv _ _ _ _ _ hsb) ec) as (hsc & _ & _).
    pose proof (step_heap _ _ _ _ _ hsc) as hle_b.
    pose proof (heap_le_trans _ _ _ (step_heap _ _ _ _ _ hsb) hle_b) as hle_a.
    exists P', B1', B2', rs4. cbn [st_heap].
    split; [reflexivity|].
    split; [exact (rn_slots_length _ _ _ _ _ em)|].
    split; [exact (rn_slots_length _ _ _ _ _ eB2)|].
    split.
    { refine (pfd_forall2_impl hP _). intros p p' h.
      exact (pfd_root_pres_trans (st_heap s) (g_heap ga) (g_heap gc) (RA p) (RA p') (RA p')
               (proj2 h) (root_pres_heap_le (g_heap ga) (g_heap gc) (RA p') hle_a)). }
    split.
    { intros l ts h. exact (pfd_slots_mono _ _ hle_a _ _ _ (hrB1 l ts h)). }
    { intros l ts h. exact (pfd_slots_mono _ _ hle_b _ _ _ (hrB2 l ts h)). }
  Qed.

  (** **** One step of [push_fresh]: the allocation of one fresh variable *)
  Lemma pfd_alloc_step (lo : positive) (lvl : nat) (P : list haddr) (B1 B2 : list cbn_slot)
      (n1 n2 o1 o2 : nat) (rs : list root) (s : cbn_state)
      (x : haddr) (rsA : list root) (s1 : cbn_state) :
    state_ok lo s -> (forall l, gam_ok Γ nctx l s) -> memo_ok X_type X s ->
    heap_nofwd s.(st_heap) ->
    alloc stress (CDone (VNeu (NVar lvl) []))
      (RE (mkEnv (map SAddr P ++ B1) n1 o1) :: RE (mkEnv (map SAddr P ++ B2) n2 o2) :: rs) s
      = COk (x, rsA, s1) ->
    exists (lo1 : positive) (P1 : list haddr) (B1a B2a : list cbn_slot) (rsa : list root),
      rsA = RE (mkEnv (map SAddr P1 ++ B1a) n1 o1)
              :: RE (mkEnv (map SAddr P1 ++ B2a) n2 o2) :: rsa
      /\ #|B1a| = #|B1| /\ #|B2a| = #|B2|
      /\ Forall2 (pfd_ra s.(st_heap) s1.(st_heap)) P P1
      /\ root_pres nctx s.(st_heap) s1.(st_heap) (RSk B1) (RSk B1a)
      /\ root_pres nctx s.(st_heap) s1.(st_heap) (RSk B2) (RSk B2a)
      /\ Forall2 (root_pres nctx s.(st_heap) s1.(st_heap)) rs rsa
      /\ state_ok lo1 s1 /\ (forall l, gam_ok Γ nctx l s1) /\ memo_ok X_type X s1
      /\ heap_nofwd s1.(st_heap)
      /\ (forall l, repr_addr nctx s1.(st_heap) l x (tRel (l - S lvl))).
  Proof.
    intros hs hg hm hnf e.
    assert (hrn : forall (G : Type) (f : haddr -> G -> cbn_res (haddr * G)) (g : G),
               rn_cell f (CDone (VNeu (NVar lvl) [])) g = COk (CDone (VNeu (NVar lvl) []), g)).
    { intros G f g. exact (rn_cell_ctx_var f lvl g). }
    assert (hfacts : forall l, exists lo' : positive,
               state_ok lo' s1 /\ gam_ok Γ nctx l s1 /\ memo_ok X_type X s1
               /\ heap_nofwd s1.(st_heap)
               /\ repr_addr nctx s1.(st_heap) l x (tRel (l - S lvl))).
    { intros l.
      destruct (alloc_addr_free X_type X Γ nctx stress lo l (CDone (VNeu (NVar lvl) []))
                  (tRel (l - S lvl)) _ s x rsA s1 hs (hg l) hm hnf eq_refl
                  (fun H => repr_cell_ctx_var nctx H l lvl) hrn e)
        as (lo' & h1 & h2 & h3 & h4 & h5 & _).
      exists lo'. exact (conj h1 (conj h2 (conj h3 (conj h4 h5)))). }
    destruct (hfacts 0) as (lo1 & hs1 & _ & hm1 & hnf1 & _).
    assert (hg1 : forall l, gam_ok Γ nctx l s1).
    { intros l. destruct (hfacts l) as (lo' & _ & h & _). exact h. }
    assert (hx : forall l, repr_addr nctx s1.(st_heap) l x (tRel (l - S lvl))).
    { intros l. destruct (hfacts l) as (lo' & _ & _ & _ & _ & h). exact h. }
    unfold alloc in e. destruct (gc_due stress s) eqn:Egc.
    - destruct (collect (RC (CDone (VNeu (NVar lvl) []))
                  :: RE (mkEnv (map SAddr P ++ B1) n1 o1)
                  :: RE (mkEnv (map SAddr P ++ B2) n2 o2) :: rs) s)
        as [[rs2 s2]|w] eqn:Ec; [|discriminate].
      destruct (pfd_collect_two_envs _ P B1 B2 n1 n2 o1 o2 rs s rs2 s2 hnf hrn Ec)
        as (P1 & B1a & B2a & rs3 & -> & hl1 & hl2 & hP & hB1 & hB2).
      destruct (collect_sound nctx _ _ _ _ hnf Ec) as (hok2 & _ & _ & _ & hfa & _).
      pose proof (pfd_forall2_tail (pfd_forall2_tail (pfd_forall2_tail hfa))) as hrs.
      cbv beta iota in e.
      destruct (alloc_now (CDone (VNeu (NVar lvl) [])) s2) as [a2 s3] eqn:Ea.
      cbv beta iota in e. injection e as ex erA es1. subst x rsA s1.
      pose proof (alloc_now_heap_le (st_next s) (CDone (VNeu (NVar lvl) [])) s2
                    (so_heap _ _ hok2)) as hle.
      rewrite Ea in hle. cbn [snd] in hle.
      exists lo1, P1, B1a, B2a, rs3.
      split; [reflexivity|]. split; [exact hl1|]. split; [exact hl2|].
      split; [exact (pfd_ra_mono _ _ _ _ _ hP hle)|].
      split; [exact (pfd_root_pres_mono _ _ _ _ _ hB1 hle)|].
      split; [exact (pfd_root_pres_mono _ _ _ _ _ hB2 hle)|].
      split; [exact (pfd_roots_mono _ _ _ _ _ hrs hle)|].
      split; [exact hs1|]. split; [exact hg1|]. split; [exact hm1|]. split; [exact hnf1|].
      exact hx.
    - cbv beta iota in e.
      destruct (alloc_now (CDone (VNeu (NVar lvl) [])) s) as [a2 s3] eqn:Ea.
      cbv beta iota in e. injection e as ex erA es1. subst x rsA s1.
      pose proof (alloc_now_heap_le lo (CDone (VNeu (NVar lvl) [])) s (so_heap _ _ hs)) as hle.
      rewrite Ea in hle. cbn [snd] in hle.
      exists lo1, P, B1, B2, rs.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact (pfd_ra_refl _ _ hle P)|].
      split; [exact (root_pres_heap_le _ _ _ hle)|].
      split; [exact (root_pres_heap_le _ _ _ hle)|].
      split; [exact (pfd_roots_refl _ _ hle rs)|].
      split; [exact hs1|]. split; [exact hg1|]. split; [exact hm1|]. split; [exact hnf1|].
      exact hx.
  Qed.

  Lemma pfd_env_step (x' : haddr) (as' P' : list haddr) (B : list cbn_slot) (m n o : nat) :
    mkEnv (List.rev (map SAddr as') ++ map SAddr (x' :: P') ++ B) (m + S n) o
    = mkEnv (List.rev (map SAddr (x' :: as')) ++ map SAddr P' ++ B) (S m + n) o.
  Proof.
    rewrite Nat.add_succ_r. cbn [map List.rev]. rewrite <- List.app_assoc. reflexivity.
  Qed.

  Lemma pfd_push_fresh_O (lvl : nat) (e1 e2 : cbn_env) (rs : list root) (s : cbn_state) :
    push_fresh stress 0 lvl e1 e2 rs s = COk ((lvl, e1, e2), rs, s).
  Proof. reflexivity. Qed.

  Lemma pfd_push_fresh_S (m lvl : nat) (e1 e2 : cbn_env) (rs : list root) (s : cbn_state) :
    push_fresh stress (S m) lvl e1 e2 rs s =
    match alloc stress (CDone (VNeu (NVar lvl) [])) (RE e1 :: RE e2 :: rs) s with
    | COk (x, rs1, s1) =>
      match rs1 with
      | RE e1' :: RE e2' :: rs2 =>
        push_fresh stress m (S lvl) (env_push (SAddr x) e1') (env_push (SAddr x) e2') rs2 s1
      | _ => CFail WRoots
      end
    | CFail w => CFail w
    end.
  Proof. reflexivity. Qed.

  (** **** [push_fresh] over two environments that share a prefix of addresses *)
  Lemma pfd_push_fresh_prefix (n : nat) :
    forall (lo : positive) (lvl : nat) (P : list haddr) (B1 B2 : list cbn_slot)
      (n1 n2 o1 o2 : nat) (rs : list root) (s : cbn_state)
      (r : nat * cbn_env * cbn_env) (rs' : list root) (s' : cbn_state),
      state_ok lo s -> (forall l, gam_ok Γ nctx l s) -> memo_ok X_type X s ->
      heap_nofwd s.(st_heap) ->
      push_fresh stress n lvl (mkEnv (map SAddr P ++ B1) n1 o1)
        (mkEnv (map SAddr P ++ B2) n2 o2) rs s = COk (r, rs', s') ->
      exists (lo' : positive) (P' : list haddr) (B1' B2' : list cbn_slot) (as_ : list haddr),
        #|as_| = n /\ #|B1'| = #|B1| /\ #|B2'| = #|B2|
        /\ r = (lvl + n, mkEnv (List.rev (map SAddr as_) ++ map SAddr P' ++ B1') (n + n1) o1,
                         mkEnv (List.rev (map SAddr as_) ++ map SAddr P' ++ B2') (n + n2) o2)
        /\ Forall2 (root_pres nctx s.(st_heap) s'.(st_heap)) rs rs'
        /\ Forall2 (pfd_ra s.(st_heap) s'.(st_heap)) P P'
        /\ root_pres nctx s.(st_heap) s'.(st_heap) (RSk B1) (RSk B1')
        /\ root_pres nctx s.(st_heap) s'.(st_heap) (RSk B2) (RSk B2')
        /\ state_ok lo' s' /\ (forall l, gam_ok Γ nctx l s') /\ memo_ok X_type X s'
        /\ heap_nofwd s'.(st_heap)
        /\ (forall (j : nat) (a : haddr), nth_error as_ j = Some a ->
              forall l, repr_addr nctx s'.(st_heap) l a (tRel (l - S (lvl + j)))).
  Proof.
    induction n as [|m ih];
      intros lo lvl P B1 B2 n1 n2 o1 o2 rs s r rs' s' hs hg hm hnf e.
    - rewrite pfd_push_fresh_O in e. injection e as er ers es. subst r rs' s'.
      exists lo, P, B1, B2, [].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [rewrite Nat.add_0_r; reflexivity|].
      split; [exact (pfd_roots_refl _ _ (heap_le_refl _) rs)|].
      split; [exact (pfd_ra_refl _ _ (heap_le_refl _) P)|].
      split; [exact (root_pres_heap_le _ _ _ (heap_le_refl _))|].
      split; [exact (root_pres_heap_le _ _ _ (heap_le_refl _))|].
      split; [exact hs|]. split; [exact hg|]. split; [exact hm|]. split; [exact hnf|].
      intros j a hj. destruct j; discriminate.
    - rewrite pfd_push_fresh_S in e.
      destruct (alloc stress (CDone (VNeu (NVar lvl) []))
                  (RE (mkEnv (map SAddr P ++ B1) n1 o1)
                     :: RE (mkEnv (map SAddr P ++ B2) n2 o2) :: rs) s)
        as [[[x rsA] s1]|w] eqn:ea; [|discriminate].
      destruct (pfd_alloc_step lo lvl P B1 B2 n1 n2 o1 o2 rs s x rsA s1 hs hg hm hnf ea)
        as (lo1 & P1 & B1a & B2a & rsa & -> & hl1 & hl2 & hP1 & hB1 & hB2 & hrs1
            & hs1 & hg1 & hm1 & hnf1 & hx).
      cbv beta iota in e.
      change (push_fresh stress m (S lvl) (mkEnv (map SAddr (x :: P1) ++ B1a) (S n1) o1)
                (mkEnv (map SAddr (x :: P1) ++ B2a) (S n2) o2) rsa s1 = COk (r, rs', s')) in e.
      destruct (ih lo1 (S lvl) (x :: P1) B1a B2a (S n1) (S n2) o1 o2 rsa s1 r rs' s'
                  hs1 hg1 hm1 hnf1 e)
        as (lo' & P2 & B1' & B2' & as' & hlen & hl1' & hl2' & -> & hrs2 & hP2 & hB1' & hB2'
            & hs' & hg' & hm' & hnf' & hrd).
      destruct P2 as [|x' P']; [inversion hP2|].
      exists lo', P', B1', B2', (x' :: as').
      split; [cbn; rewrite hlen; reflexivity|].
      split; [exact (eq_trans hl1' hl1)|].
      split; [exact (eq_trans hl2' hl2)|].
      split.
      { rewrite (pfd_env_step x' as' P' B1' m n1 o1), (pfd_env_step x' as' P' B2' m n2 o2).
        rewrite Nat.add_succ_r. reflexivity. }
      split; [exact (pfd_roots_trans _ _ _ _ _ _ hrs1 hrs2)|].
      split; [exact (pfd_ra_trans _ _ _ _ _ _ hP1 (pfd_forall2_tail hP2))|].
      split; [exact (pfd_root_pres_trans _ _ _ _ _ _ hB1 hB1')|].
      split; [exact (pfd_root_pres_trans _ _ _ _ _ _ hB2 hB2')|].
      split; [exact hs'|]. split; [exact hg'|]. split; [exact hm'|]. split; [exact hnf'|].
      intros j a hj l. destruct j as [|j].
      + cbn in hj. injection hj as <-. rewrite Nat.add_0_r.
        exact (pfd_forall2_head hP2 l _ (hx l)).
      + cbn in hj. rewrite Nat.add_succ_r. exact (hrd j a hj l).
  Qed.

  (** **** What [push_fresh] builds, for any roots the caller hands in *)
  Lemma push_fresh_spec_gen (lo : positive) (n lvl : nat) (e1 e2 : cbn_env) (rs : list root)
      (s : cbn_state) (r : nat * cbn_env * cbn_env) (rs' : list root) (s' : cbn_state) :
    state_ok lo s -> (forall l, gam_ok Γ nctx l s) -> memo_ok X_type X s ->
    heap_nofwd s.(st_heap) ->
    push_fresh stress n lvl e1 e2 rs s = COk (r, rs', s') ->
    exists (lo' : positive) (e1' e2' : cbn_env) (as_ : list haddr) (f1 f2 : cbn_env),
      #|as_| = n
      /\ r = (lvl + n, f1, f2)
      /\ Forall2 (root_pres nctx s.(st_heap) s'.(st_heap)) rs rs'
      /\ root_pres nctx s.(st_heap) s'.(st_heap) (RE e1) (RE e1')
      /\ root_pres nctx s.(st_heap) s'.(st_heap) (RE e2) (RE e2')
      /\ e1'.(ev_nvals) = e1.(ev_nvals) /\ e1'.(ev_goff) = e1.(ev_goff)
      /\ #|e1'.(ev_vals)| = #|e1.(ev_vals)|
      /\ e2'.(ev_nvals) = e2.(ev_nvals) /\ e2'.(ev_goff) = e2.(ev_goff)
      /\ #|e2'.(ev_vals)| = #|e2.(ev_vals)|
      /\ f1 = mkEnv (List.rev (map SAddr as_) ++ e1'.(ev_vals)) (n + e1'.(ev_nvals))
                e1'.(ev_goff)
      /\ f2 = mkEnv (List.rev (map SAddr as_) ++ e2'.(ev_vals)) (n + e2'.(ev_nvals))
                e2'.(ev_goff)
      /\ state_ok lo' s' /\ (forall l, gam_ok Γ nctx l s') /\ memo_ok X_type X s'
      /\ heap_nofwd s'.(st_heap)
      /\ (forall (j : nat) (a : haddr), nth_error as_ j = Some a ->
            forall l, repr_addr nctx s'.(st_heap) l a (tRel (l - S (lvl + j)))).
  Proof.
    intros hs hg hm hnf e.
    destruct e1 as [V1 n1 o1], e2 as [V2 n2 o2].
    change (push_fresh stress n lvl (mkEnv (map SAddr [] ++ V1) n1 o1)
              (mkEnv (map SAddr [] ++ V2) n2 o2) rs s = COk (r, rs', s')) in e.
    destruct (pfd_push_fresh_prefix n lo lvl [] V1 V2 n1 n2 o1 o2 rs s r rs' s'
                hs hg hm hnf e)
      as (lo' & P' & B1' & B2' & as_ & hlen & hl1 & hl2 & -> & hrs & hP & hB1 & hB2
          & hs' & hg' & hm' & hnf' & hrd).
    destruct P' as [|p P']; [|inversion hP].
    exists lo', (mkEnv B1' n1 o1), (mkEnv B2' n2 o2), as_,
      (mkEnv (List.rev (map SAddr as_) ++ B1') (n + n1) o1),
      (mkEnv (List.rev (map SAddr as_) ++ B2') (n + n2) o2).
    cbn [ev_vals ev_nvals ev_goff].
    split; [exact hlen|].
    split; [reflexivity|].
    split; [exact hrs|].
    split; [intros l tm u h;
            exact (repr_susp_transport nctx _ _ _ _ _ _ _ h (st_heap s') B1' hB1)|].
    split; [intros l tm u h;
            exact (repr_susp_transport nctx _ _ _ _ _ _ _ h (st_heap s') B2' hB2)|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact hl1|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact hl2|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [exact hs'|]. split; [exact hg'|]. split; [exact hm'|]. split; [exact hnf'|].
    exact hrd.
  Qed.

  (** **** What [push_fresh] builds, at the call of the stuck-match rule: the roots are the
    two environments followed by the caller's roots *)
  Lemma push_fresh_spec (lo : positive) (n lvl : nat) (e1 e2 : cbn_env) (rs : list root)
      (s : cbn_state) (r : nat * cbn_env * cbn_env) (rs' : list root) (s' : cbn_state) :
    state_ok lo s -> (forall l, gam_ok Γ nctx l s) -> memo_ok X_type X s ->
    heap_nofwd s.(st_heap) ->
    push_fresh stress n lvl e1 e2 (RE e1 :: RE e2 :: rs) s = COk (r, rs', s') ->
    exists (lo' : positive) (e1' e2' : cbn_env) (as_ : list haddr) (f1 f2 : cbn_env)
      (e1r e2r : cbn_env) (rs2 : list root),
      #|as_| = n
      /\ r = (lvl + n, f1, f2)
      /\ rs' = RE e1r :: RE e2r :: rs2
      /\ root_pres nctx s.(st_heap) s'.(st_heap) (RE e1) (RE e1r)
      /\ root_pres nctx s.(st_heap) s'.(st_heap) (RE e2) (RE e2r)
      /\ Forall2 (root_pres nctx s.(st_heap) s'.(st_heap)) rs rs2
      /\ root_pres nctx s.(st_heap) s'.(st_heap) (RE e1) (RE e1')
      /\ root_pres nctx s.(st_heap) s'.(st_heap) (RE e2) (RE e2')
      /\ e1'.(ev_nvals) = e1.(ev_nvals) /\ e1'.(ev_goff) = e1.(ev_goff)
      /\ #|e1'.(ev_vals)| = #|e1.(ev_vals)|
      /\ e2'.(ev_nvals) = e2.(ev_nvals) /\ e2'.(ev_goff) = e2.(ev_goff)
      /\ #|e2'.(ev_vals)| = #|e2.(ev_vals)|
      /\ f1 = mkEnv (List.rev (map SAddr as_) ++ e1'.(ev_vals)) (n + e1'.(ev_nvals))
                e1'.(ev_goff)
      /\ f2 = mkEnv (List.rev (map SAddr as_) ++ e2'.(ev_vals)) (n + e2'.(ev_nvals))
                e2'.(ev_goff)
      /\ state_ok lo' s' /\ (forall l, gam_ok Γ nctx l s') /\ memo_ok X_type X s'
      /\ heap_nofwd s'.(st_heap)
      /\ (forall (j : nat) (a : haddr), nth_error as_ j = Some a ->
            forall l, repr_addr nctx s'.(st_heap) l a (tRel (l - S (lvl + j)))).
  Proof.
    intros hs hg hm hnf e.
    destruct (push_fresh_spec_gen lo n lvl e1 e2 _ s r rs' s' hs hg hm hnf e)
      as (lo' & e1' & e2' & as_ & f1 & f2 & hlen & hr & hrs & hp1 & hp2 & rest).
    destruct rs' as [|q1 rs3]; [inversion hrs|].
    destruct rs3 as [|q2 rs2]; [pose proof (pfd_forall2_tail hrs) as ht; inversion ht|].
    pose proof (pfd_forall2_head hrs) as hq1.
    pose proof (pfd_forall2_head (pfd_forall2_tail hrs)) as hq2.
    pose proof (pfd_forall2_tail (pfd_forall2_tail hrs)) as hrs2.
    destruct q1 as [a1|x1|e1r|v1|l1|l1|c1]; try (exfalso; exact hq1).
    destruct q2 as [a2|x2|e2r|v2|l2|l2|c2]; try (exfalso; exact hq2).
    exists lo', e1', e2', as_, f1, f2, e1r, e2r, rs2.
    split; [exact hlen|]. split; [exact hr|]. split; [reflexivity|].
    split; [exact hq1|]. split; [exact hq2|]. split; [exact hrs2|].
    split; [exact hp1|]. split; [exact hp2|]. exact rest.
  Qed.

End ConvPartD.

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
    that stand for what the context entry denotes, the code table is good and the five memo
    tables mean what they say.

    It does NOT say that no cell of the heap names a variable at a level not yet in scope:
    that is false as soon as a binder has been crossed — the cells [push_fresh] and the
    binder rows allocate for the fresh variables stay in the heap after the comparison has
    come back out of the binder. Scoping is a property of each environment instead
    ([env_reads] below). [lvl] is kept as an argument so that every statement says at
    which level the invariant is used. *)
  Definition cok (lvl : nat) (s : cbn_state) : Prop :=
    (exists lo : positive, state_ok lo s)
    /\ heap_nofwd s.(st_heap)
    /\ (forall l : nat, gam_ok Γ nctx l s)
    /\ memo_ok X_type X s
    /\ memo_inv X_type X s.

  Lemma cok_mono (lvl lvl' : nat) (s : cbn_state) : lvl <= lvl' -> cok lvl s -> cok lvl' s.
  Proof. intros _ h. exact h. Qed.

  Lemma cok_memo_inv (lvl : nat) (s : cbn_state) : cok lvl s -> memo_inv X_type X s.
  Proof. intros (_ & _ & _ & _ & h). exact h. Qed.

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
    intros (h1 & h2 & h3 & h4 & _) hm he hn hg hc.
    split; [|split; [|split; [|split]]].
    - destruct h1 as [lo [hb hcl hga]]. exists lo. split.
      + rewrite he, hn. exact hb.
      + rewrite he, hn. exact hcl.
      + rewrite hg, hn. exact hga.
    - rewrite he. exact h2.
    - intros l j a hk. rewrite hg in hk. destruct (h3 l j a hk) as [t [hd hr]].
      exists t. split; [exact hd|]. rewrite he. exact hr.
    - exact (memo_ok_codes X_type X s s' hc h4).
    - exact hm.
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

  (** ** The stuck-match rule: the parameters

    [case_params] compares the two parameter lists one by one, each as a child code of its
    own [tCase] under its own environment. Readings are given as [repr_susp] facts, one per
    parameter, because that is the shape the roots of a collection carry: [root_pres] of an
    [RE] root preserves [repr_susp], not the slot list. *)
  Lemma Forall2_susp_transport (H H' : bheap cbn_cell) (lvl : nat) (e e' : cbn_env)
      (l us : list term) :
    (forall lvl tm u, repr_susp nctx H lvl e tm u -> repr_susp nctx H' lvl e' tm u) ->
    Forall2 (fun t u => repr_susp nctx H lvl e t u) l us ->
    Forall2 (fun t u => repr_susp nctx H' lvl e' t u) l us.
  Proof. intros hk. induction 1; constructor; auto. Qed.

  Lemma case_params_eq (k : unit -> cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : code)
      (e2 : cbn_env) (c2 : code) (i : N) (l1 l2 : list term) (rs : list root)
      (s : cbn_state) :
    case_params X_type X Γ nctx stress (FS k) lvl e1 c1 e2 c2 i l1 l2 rs s
    = match l1, l2 with
      | [], [] => COk (true, rs, s)
      | t1 :: l1, t2 :: l2 =>
        match conv_term X_type X Γ nctx stress (k tt) lvl Conv
                e1 (child c1 (case_param_step i) t1)
                e2 (child c2 (case_param_step i) t2) (RE e1 :: RE e2 :: rs) s with
        | COk (true, rs, s) =>
          match rs with
          | RE e1 :: RE e2 :: rs =>
            case_params X_type X Γ nctx stress (k tt) lvl e1 c1 e2 c2 (N.succ i)
              l1 l2 rs s
          | _ => CFail WRoots
          end
        | COk (false, rs, s) => COk (false, skipn 2 rs, s)
        | CFail w => CFail w
        end
      | _, _ => COk (false, rs, s)
      end.
  Proof. reflexivity. Qed.

  Lemma case_params_sound :
    forall (d : cbn_fuel) (lvl : nat) (Ξ : context) (e1 : cbn_env) (c1 : code)
      (e2 : cbn_env) (c2 : code) (i : N) (l1 l2 us1 us2 : list term)
      (rs : list root) (s : cbn_state) (rs' : list root) (s' : cbn_state),
      term_seam_below d ->
      cok lvl s -> #|Ξ| = lvl -> is_closed_context Ξ -> nctx <= lvl ->
      Forall2 (fun t u => repr_susp nctx (s.(st_heap)) lvl e1 t u) l1 us1 ->
      Forall2 (fun t u => repr_susp nctx (s.(st_heap)) lvl e2 t u) l2 us2 ->
      forallb (is_open_term Ξ) us1 = true ->
      forallb (is_open_term Ξ) us2 = true ->
      case_params X_type X Γ nctx stress d lvl e1 c1 e2 c2 i l1 l2 rs s
        = COk (true, rs', s') ->
      Forall2 (root_pres nctx (s.(st_heap)) (s'.(st_heap))) rs rs'
      /\ cok lvl s'
      /\ Forall2 (fun a b => ∥ Σ ;;; Ξ ⊢ a = b ∥) us1 us2.
  Proof.
    intros d. induction d as [|k ih];
      intros lvl Ξ e1 c1 e2 c2 i l1 l2 us1 us2 rs s rs' s'
        hseam hok hlen clΞ hnc hu1 hu2 ho1 ho2 he.
    { cbn in he. discriminate he. }
    rewrite case_params_eq in he.
    destruct l1 as [|t1 l1]; destruct l2 as [|t2 l2].
    - cbn in he. inversion he; subst.
      inversion hu1; subst. inversion hu2; subst.
      split; [apply roots_pres_refl|]. split; [exact hok|]. constructor.
    - discriminate he.
    - discriminate he.
    - destruct (Forall2_cons_inv _ _ _ _ hu1) as [v1 [us1' [-> [hv1 hl1]]]].
      destruct (Forall2_cons_inv _ _ _ _ hu2) as [v2 [us2' [-> [hv2 hl2]]]].
      cbn in ho1, ho2.
      apply andb_true_iff in ho1 as [hov1 ho1].
      apply andb_true_iff in ho2 as [hov2 ho2].
      destruct (conv_term X_type X Γ nctx stress (k tt) lvl Conv
                  e1 (child c1 (case_param_step i) t1)
                  e2 (child c2 (case_param_step i) t2) (RE e1 :: RE e2 :: rs) s)
        as [[[b2 rs2] s2]|w] eqn:Ect; [|discriminate he].
      destruct (term_seam_below_here k hseam lvl Conv Ξ
                  e1 (child c1 (case_param_step i) t1)
                  e2 (child c2 (case_param_step i) t2) (RE e1 :: RE e2 :: rs) s
                  b2 rs2 s2 hok hlen clΞ hnc Ect) as (hp1 & hok2 & hconv).
      destruct b2; [|discriminate he].
      destruct (Forall2_cons_inv _ _ _ _ hp1) as [r1' [q1 [-> [hpr1 hp1']]]].
      destruct (root_pres_RE_inv (s.(st_heap)) (s2.(st_heap)) e1 r1' hpr1)
        as [f1 [-> hk1]].
      destruct (Forall2_cons_inv _ _ _ _ hp1') as [r2' [q2 [-> [hpr2 hp2']]]].
      destruct (root_pres_RE_inv (s.(st_heap)) (s2.(st_heap)) e2 r2' hpr2)
        as [f2 [-> hk2]].
      destruct (ih tt lvl Ξ f1 c1 f2 c2 (N.succ i) l1 l2 us1' us2' q2 s2 rs' s'
                  (term_seam_below_step k hseam) hok2 hlen clΞ hnc
                  (Forall2_susp_transport (s.(st_heap)) (s2.(st_heap)) lvl e1 f1
                     l1 us1' hk1 hl1)
                  (Forall2_susp_transport (s.(st_heap)) (s2.(st_heap)) lvl e2 f2
                     l2 us2' hk2 hl2)
                  ho1 ho2 he)
        as (hp & hok' & hag).
      split.
      + exact (roots_pres_trans nctx (s.(st_heap)) (s2.(st_heap)) (s'.(st_heap))
                 rs q2 rs' hp2' hp).
      + split; [exact hok'|].
        constructor; [|exact hag].
        exact (hconv eq_refl v1 v2 hv1 hv2 hov1 hov2).
  Qed.

  (** ** The stuck-match rule: the branches and the whole rule

    [case_cong] compares two stuck [tCase]s part by part: the parameters ([case_params]), the
    return clauses under [#|pcontext|] fresh variables, the scrutinees, and the branch bodies
    ([case_branches]), each under [#|bcontext|] fresh variables. Going under the binders reads
    the two environments at a higher level, so what the rule needs of each environment is that
    its readings at every higher level are its readings at [lvl] lifted ([env_reads]). That is
    a statement about what the environment stands for, so a renamed root carries it, and the
    renamings done by the sub-calls and by [push_fresh] keep it at every level at once. *)

  (* ssrbool's names for the constant predicates, which the [PCUICOnFreeVars] statements use;
     this file does not import ssrbool. *)
  Local Notation xpred0 := (fun _ : nat => false) (only parsing).
  Local Notation xpredT := (fun _ : nat => true) (only parsing).

  (** *** List helpers *)

  Lemma cc_forallb_Forall {A : Type} (f : A -> bool) (l : list A) :
    forallb f l = true -> Forall (fun x => f x = true) l.
  Proof.
    induction l as [|x l ih]; cbn; intros h; [constructor|].
    apply andb_true_iff in h as [h1 h2]. constructor; [exact h1|exact (ih h2)].
  Qed.

  Lemma cc_Forall_impl {A : Type} (P Q : A -> Prop) (l : list A) :
    Forall P l -> (forall x, P x -> Q x) -> Forall Q l.
  Proof. intros h himp. induction h; constructor; auto. Qed.

  Lemma cc_Forall_cons_inv {A : Type} (P : A -> Prop) (x : A) (l : list A) :
    Forall P (x :: l) -> P x /\ Forall P l.
  Proof. intros h. inversion h; subst. split; assumption. Qed.

  Lemma sq_forall2_all2 {A B : Type} (R : A -> B -> Type) (l1 : list A) (l2 : list B) :
    Forall2 (fun x y => ∥ R x y ∥) l1 l2 -> ∥ All2 R l1 l2 ∥.
  Proof.
    intros h. induction h as [|x y m1 m2 hr _ ih].
    - constructor. constructor.
    - destruct hr as [r]. destruct ih as [ih]. constructor. constructor; assumption.
  Qed.

  (** *** Slot lists *)

  Lemma repr_slots_app (H : bheap cbn_cell) (lvl : nat) (l1 l2 : list cbn_slot)
      (ts1 ts2 : list term) :
    repr_slots nctx H lvl l1 ts1 -> repr_slots nctx H lvl l2 ts2 ->
    repr_slots nctx H lvl (l1 ++ l2) (ts1 ++ ts2).
  Proof.
    intros h1. induction h1 as [lv|lv x l t ts hx _ ih]; intros h2; cbn; [exact h2|].
    constructor; [exact hx|exact (ih h2)].
  Qed.

  (** The fresh addresses [push_fresh] pushes, the first one deepest, read back as the
    de Bruijn indices they stand for. *)
  Lemma repr_slots_fresh (H : bheap cbn_cell) (lvl : nat) (as_ : list haddr) :
    (forall j a, nth_error as_ j = Some a ->
       forall l, repr_addr nctx H l a (tRel (l - S (lvl + j)))) ->
    repr_slots nctx H (lvl + #|as_|) (List.rev (map SAddr as_)) (idsn #|as_|).
  Proof.
    revert lvl. induction as_ as [|a as' ih]; intros lvl hfr.
    - cbn. constructor.
    - cbn [List.rev map length idsn].
      apply repr_slots_app.
      + replace (lvl + S #|as'|) with (S lvl + #|as'|) by lia.
        apply ih. intros j b hj l.
        replace (l - S (S lvl + j)) with (l - S (lvl + S j)) by lia.
        exact (hfr (S j) b hj l).
      + constructor; [|constructor].
        apply repr_slot_addr.
        replace (tRel #|as'|) with (tRel (lvl + S #|as'| - S (lvl + 0))) by (f_equal; lia).
        exact (hfr 0 a eq_refl _).
  Qed.

  Lemma crs_susp_inv (H : bheap cbn_cell) (lvl : nat) (vals : list cbn_slot)
      (nvals goff : nat) (t u : term) :
    repr_susp nctx H lvl (mkEnv vals nvals goff) t u ->
    exists ts, repr_slots nctx H lvl vals ts
               /\ u = subst ts 0 (lift (lvl - nctx + goff) nvals t).
  Proof. intros h. inversion h; subst. eexists. split; [eassumption|reflexivity]. Qed.

  (** *** A term under [n] binders, to read a body at the cut [n] *)

  Fixpoint lam_n (n : nat) (t : term) : term :=
    match n with
    | O => t
    | S n =>
      tLambda {| binder_name := nAnon; binder_relevance := Relevant |} (tSort Sort.type0)
        (lam_n n t)
    end.

  Lemma lam_n_lift (N n k : nat) (t : term) :
    lift N k (lam_n n t) = lam_n n (lift N (n + k) t).
  Proof.
    revert k. induction n as [|n ih]; intros k; [reflexivity|].
    cbn [lam_n lift]. rewrite ih. rewrite Nat.add_succ_r. reflexivity.
  Qed.

  Lemma lam_n_subst (s : list term) (n k : nat) (t : term) :
    subst s k (lam_n n t) = lam_n n (subst s (n + k) t).
  Proof.
    revert k. induction n as [|n ih]; intros k; [reflexivity|].
    cbn [lam_n subst]. rewrite ih. rewrite Nat.add_succ_r. reflexivity.
  Qed.

  Lemma lam_n_inj (n : nat) (a b : term) : lam_n n a = lam_n n b -> a = b.
  Proof.
    induction n as [|n ih]; cbn [lam_n]; intros h; [exact h|].
    injection h as h. exact (ih h).
  Qed.

  (** *** Environments whose readings shift

    [env_reads H lvl e ts N]: the environment [e], held at level [lvl], names no variable at a
    level [>= lvl], so its readings at every higher level [lvl + j] are its readings at [lvl]
    lifted by [j]. [ts] are the readings of its slots at [lvl] and [N] the lift of its
    suspensions at [lvl] ([lvl - nctx + ev_goff e], [env_reads_intro]). It says only what the
    environment stands for, so a renamed [RE] root carries it ([env_reads_tr],
    [env_reads_root]). *)
  Definition env_reads (H : bheap cbn_cell) (lvl : nat) (e : cbn_env) (ts : list term)
      (N : nat) : Prop :=
    forall (j : nat) (t : term),
      repr_susp nctx H (lvl + j) e t (subst (map (lift0 j) ts) 0 (lift (N + j) #|ts| t)).

  Lemma env_reads_intro (H : bheap cbn_cell) (lvl : nat) (e : cbn_env) (ts : list term) :
    nctx <= lvl -> heap_wf lvl H -> env_wf e -> repr_slots nctx H lvl e.(ev_vals) ts ->
    env_reads H lvl e ts (lvl - nctx + e.(ev_goff)).
  Proof.
    intros hle hwf [hn hws] hs j t.
    destruct e as [vals nvals goff]. cbn [ev_vals ev_nvals ev_goff] in hn, hws, hs |- *.
    pose proof (repr_slots_length _ _ _ _ _ hs) as hlen.
    replace (lvl - nctx + goff + j) with (lvl + j - nctx + goff) by lia.
    rewrite hlen, <- hn.
    apply repr_susp_intro.
    exact (repr_slots_shift nctx j lvl H vals ts hle hwf hws hs).
  Qed.

  Lemma env_reads_tr (H H' : bheap cbn_cell) (lvl : nat) (e e' : cbn_env) (ts : list term)
      (N : nat) :
    (forall lvl tm u, repr_susp nctx H lvl e tm u -> repr_susp nctx H' lvl e' tm u) ->
    env_reads H lvl e ts N -> env_reads H' lvl e' ts N.
  Proof. intros hk hr j t. exact (hk _ _ _ (hr j t)). Qed.

  Lemma env_reads_root (H H' : bheap cbn_cell) (lvl : nat) (e e' : cbn_env) (ts : list term)
      (N : nat) :
    root_pres nctx H H' (RE e) (RE e') -> env_reads H lvl e ts N -> env_reads H' lvl e' ts N.
  Proof.
    intros hp. destruct (root_pres_RE_inv H H' e (RE e') hp) as [e0 [he0 hk]].
    injection he0 as he0. subst e0. exact (env_reads_tr H H' lvl e e' ts N hk).
  Qed.

  Lemma env_reads_here (H : bheap cbn_cell) (lvl : nat) (e : cbn_env) (ts : list term)
      (N : nat) (t : term) :
    env_reads H lvl e ts N -> repr_susp nctx H lvl e t (subst ts 0 (lift N #|ts| t)).
  Proof.
    intros h. pose proof (h 0 t) as h0.
    rewrite !Nat.add_0_r in h0. rewrite map_lift0 in h0. exact h0.
  Qed.

  Lemma env_reads_det (H : bheap cbn_cell) (lvl : nat) (e : cbn_env) (ts : list term)
      (N : nat) (t u : term) :
    env_reads H lvl e ts N -> repr_susp nctx H lvl e t u -> u = subst ts 0 (lift N #|ts| t).
  Proof.
    intros hr hu. destruct (repr_det nctx H) as (_ & _ & _ & _ & _ & hd & _).
    exact (hd _ _ _ _ hu _ (env_reads_here H lvl e ts N t hr)).
  Qed.

  Lemma env_reads_map (H : bheap cbn_cell) (lvl : nat) (e : cbn_env) (ts : list term)
      (N : nat) (l : list term) :
    env_reads H lvl e ts N ->
    Forall2 (fun t u => repr_susp nctx H lvl e t u) l
      (map (fun t => subst ts 0 (lift N #|ts| t)) l).
  Proof.
    intros h. induction l as [|t l ih]; cbn; constructor;
      [exact (env_reads_here H lvl e ts N t h)|exact ih].
  Qed.

  (** The reading of a body under the environment [push_fresh] builds: the fresh slots read
    as [idsn n] and the others as the lifted readings, which is the body's component of the
    parent's reading ([subst_push_fresh0]). [n'] is [n] written as the caller has it. *)
  Lemma env_reads_push (H : bheap cbn_cell) (lvl n n' : nat) (e : cbn_env) (ts : list term)
      (N : nat) (as_ : list haddr) (t : term) :
    #|as_| = n -> n' = n ->
    env_reads H lvl e ts N ->
    (forall j a, nth_error as_ j = Some a ->
       forall l, repr_addr nctx H l a (tRel (l - S (lvl + j)))) ->
    repr_susp nctx H (lvl + n)
      (mkEnv (List.rev (map SAddr as_) ++ e.(ev_vals)) (n + e.(ev_nvals)) e.(ev_goff)) t
      (subst ts n' (lift N (n' + #|ts|) t)).
  Proof.
    intros hn hn' hr hfr. subst n'.
    destruct e as [vals nvals goff]. cbn [ev_vals ev_nvals ev_goff].
    destruct (crs_susp_inv _ _ _ _ _ _ _ (hr n (lam_n n t))) as [ts2 [hs2 he2]].
    rewrite !lam_n_lift, !lam_n_subst in he2.
    apply lam_n_inj in he2. rewrite !Nat.add_0_r in he2.
    pose proof (repr_slots_fresh H lvl as_ hfr) as hf. rewrite hn in hf.
    pose proof (repr_susp_intro nctx H (lvl + n) _ (n + nvals) goff t _
                  (repr_slots_app _ _ _ _ _ _ hf hs2)) as hp.
    assert (E : subst (idsn n ++ ts2) 0 (lift (lvl + n - nctx + goff) (n + nvals) t)
                = subst ts n (lift N (n + #|ts|) t)).
    { rewrite subst_app_simpl, idsn_length, Nat.add_0_l, <- he2.
      rewrite <- (subst_push_fresh0 n #|ts| N ts t eq_refl).
      rewrite subst_app_simpl, idsn_length, Nat.add_0_l. reflexivity. }
    rewrite <- E. exact hp.
  Qed.

  (** *** [push_fresh] keeps the state invariant *)

  Lemma collect_memo (rs : list root) (s : cbn_state) (rs' : list root) (s' : cbn_state) :
    collect rs s = COk (rs', s') -> s'.(st_memo) = s.(st_memo).
  Proof.
    rewrite collect_eq.
    destruct (rn_ptree (gc_copy (fuel_of_pos s.(st_next) (fun _ => FO))) s.(st_gam)
                (mkGc s.(st_heap) (bh_holes s.(st_next)) s.(st_next))) as [[gm g1]|w];
      [|intros h; discriminate h].
    destruct (rn_roots (gc_copy (fuel_of_pos s.(st_next) (fun _ => FO))) rs g1)
      as [[rs2 g2]|w]; [|intros h; discriminate h].
    intros h. inversion h; subst. reflexivity.
  Qed.

  Lemma alloc_memo (cl : cbn_cell) (rs : list root) (s : cbn_state) (a : haddr)
      (rs' : list root) (s' : cbn_state) :
    alloc stress cl rs s = COk (a, rs', s') -> s'.(st_memo) = s.(st_memo).
  Proof.
    unfold alloc. destruct (gc_due stress s).
    - destruct (collect (RC cl :: rs) s) as [[rs1 s1]|w] eqn:Ec; [|intros h; discriminate h].
      destruct rs1 as [|q rs1]; [intros h; discriminate h|].
      destruct q; try (intros h; discriminate h).
      intros h. unfold alloc_now in h. cbv beta iota zeta in h.
      inversion h; subst. exact (collect_memo _ _ _ _ Ec).
    - intros h. unfold alloc_now in h. cbv beta iota zeta in h.
      inversion h; subst. reflexivity.
  Qed.

  Lemma push_fresh_memo (n : nat) :
    forall (lvl : nat) (e1 e2 : cbn_env) (rs : list root) (s : cbn_state)
      (r : nat * cbn_env * cbn_env) (rs' : list root) (s' : cbn_state),
      push_fresh stress n lvl e1 e2 rs s = COk (r, rs', s') -> s'.(st_memo) = s.(st_memo).
  Proof.
    induction n as [|n ih]; intros lvl e1 e2 rs s r rs' s' h.
    - rewrite pfd_push_fresh_O in h. inversion h; subst. reflexivity.
    - rewrite pfd_push_fresh_S in h.
      destruct (alloc stress (CDone (VNeu (NVar lvl) [])) (RE e1 :: RE e2 :: rs) s)
        as [[[x rs1] s1]|w] eqn:Ea; [|discriminate h].
      destruct rs1 as [|q1 rs1]; [discriminate h|]. destruct q1; try discriminate h.
      destruct rs1 as [|q2 rs1]; [discriminate h|]. destruct q2; try discriminate h.
      cbv beta iota in h.
      rewrite (ih _ _ _ _ _ _ _ _ h). exact (alloc_memo _ _ _ _ _ _ Ea).
  Qed.

  Lemma push_fresh_cok (n lvl lvl' : nat) (e1 e2 : cbn_env) (rs : list root) (s : cbn_state)
      (r : nat * cbn_env * cbn_env) (rs' : list root) (s' : cbn_state) :
    cok lvl s -> push_fresh stress n lvl e1 e2 (RE e1 :: RE e2 :: rs) s = COk (r, rs', s') ->
    cok lvl' s'.
  Proof.
    intros ([lo hso] & hnf & hg & hm & hmi) e.
    destruct (push_fresh_spec X_type X Γ nctx stress lo n lvl e1 e2 rs s r rs' s' hso hg hm hnf e)
      as (lo' & e1' & e2' & as_ & f1 & f2 & e1r & e2r & rs2 & _ & _ & _ & _ & _ & _ & _ & _
          & _ & _ & _ & _ & _ & _ & _ & _ & hso' & hg' & hm' & hnf' & _).
    split; [exists lo'; exact hso'|]. split; [exact hnf'|]. split; [exact hg'|].
    split; [exact hm'|].
    exact (memo_inv_memo X_type X s s' (push_fresh_memo n lvl e1 e2 _ s r rs' s' e) hmi).
  Qed.

  (** *** The read-back of a [tCase] is a [tCase] *)

  Definition rd_pred (ts : list term) (N : nat) (p : predicate term) : predicate term :=
    {| pparams := map (fun t => subst ts 0 (lift N #|ts| t)) p.(pparams);
       puinst := p.(puinst);
       pcontext := p.(pcontext);
       preturn := subst ts #|p.(pcontext)| (lift N (#|p.(pcontext)| + #|ts|) p.(preturn)) |}.

  Definition rd_br (ts : list term) (N : nat) (br : branch term) : branch term :=
    {| bcontext := br.(bcontext);
       bbody := subst ts #|br.(bcontext)| (lift N (#|br.(bcontext)| + #|ts|) br.(bbody)) |}.

  Lemma rsusp_case (ts : list term) (N : nat) (ci : case_info) (p : predicate term)
      (c : term) (brs : list (branch term)) :
    subst ts 0 (lift N #|ts| (tCase ci p c brs))
    = tCase ci (rd_pred ts N p) (subst ts 0 (lift N #|ts| c)) (map (rd_br ts N) brs).
  Proof.
    cbn [lift subst]. f_equal.
    - unfold rd_pred, map_predicate_k. cbn [pparams puinst pcontext preturn]. cbv [id].
      rewrite map_map. rewrite Nat.add_0_r. reflexivity.
    - rewrite map_map. apply map_ext. intros br. unfold rd_br, map_branch_k.
      cbn [bcontext bbody]. cbv [id]. rewrite Nat.add_0_r. reflexivity.
  Qed.

  Lemma open_case_inv (Ξ : context) (ci : case_info) (p : predicate term) (c : term)
      (brs : list (branch term)) :
    is_open_term Ξ (tCase ci p c brs) ->
    forallb (is_open_term Ξ) p.(pparams)
    /\ on_free_vars (shiftnP #|p.(pcontext)| (shiftnP #|Ξ| xpred0)) p.(preturn)
    /\ on_free_vars_ctx (closedP #|p.(pparams)| xpredT) p.(pcontext)
    /\ is_open_term Ξ c
    /\ Forall (fun br => on_free_vars_ctx (closedP #|p.(pparams)| xpredT) br.(bcontext)
                 /\ on_free_vars (shiftnP #|br.(bcontext)| (shiftnP #|Ξ| xpred0)) br.(bbody))
         brs.
  Proof.
    intros h. cbn [on_free_vars is_true] in h.
    apply andb_true_iff in h as [h1 h]. apply andb_true_iff in h as [h2 h].
    apply andb_true_iff in h as [h3 h]. apply andb_true_iff in h as [h4 h5].
    rewrite test_context_k_closed_on_free_vars_ctx in h3.
    split; [exact h1|]. split; [exact h2|]. split; [exact h3|]. split; [exact h4|].
    refine (cc_Forall_impl _ _ _ (cc_forallb_Forall _ _ h5) _).
    intros br hb. cbv beta in hb. apply andb_true_iff in hb as [hb1 hb2].
    rewrite test_context_k_closed_on_free_vars_ctx in hb1. split; [exact hb1|exact hb2].
  Qed.

  Lemma open_in_ctx (Δ : context) (n lvl : nat) (t : term) :
    #|Δ| = lvl + n -> on_free_vars (shiftnP n (shiftnP lvl xpred0)) t -> is_open_term Δ t.
  Proof.
    intros hl h. rewrite hl, Nat.add_comm.
    rewrite (on_free_vars_ext _ _ t (shiftnP_add n lvl xpred0)) in h. exact h.
  Qed.

  (** *** The machine's bodies, with the comparison's names *)

  Lemma case_branches_eq (k : unit -> cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : code)
      (e2 : cbn_env) (c2 : code) (i : N) (l1 l2 : list (branch term)) (rs : list root)
      (s : cbn_state) :
    case_branches X_type X Γ nctx stress (FS k) lvl e1 c1 e2 c2 i l1 l2 rs s
    = match l1, l2 with
      | [], [] => COk (true, rs, s)
      | b1 :: l1, b2 :: l2 =>
        if case_ctx_ok b1.(bcontext) b2.(bcontext) then
          match push_fresh stress #|b1.(bcontext)| lvl e1 e2 (RE e1 :: RE e2 :: rs) s with
          | COk (r, rs, s) =>
            let '(lvlb, eb1, eb2) := r in
            match conv_term X_type X Γ nctx stress (k tt) lvlb Conv
                    eb1 (child c1 (case_branch_step i) b1.(bbody))
                    eb2 (child c2 (case_branch_step i) b2.(bbody)) rs s with
            | COk (true, rs, s) =>
              match rs with
              | RE e1 :: RE e2 :: rs =>
                case_branches X_type X Γ nctx stress (k tt) lvl e1 c1 e2 c2 (N.succ i)
                  l1 l2 rs s
              | _ => CFail WRoots
              end
            | COk (false, rs, s) => COk (false, skipn 2 rs, s)
            | CFail w => CFail w
            end
          | CFail w => CFail w
          end
        else COk (false, rs, s)
      | _, _ => COk (false, rs, s)
      end.
  Proof. reflexivity. Qed.

  Lemma case_cong_eq (k : unit -> cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : code)
      (e2 : cbn_env) (c2 : code) (rs : list root) (s : cbn_state) :
    case_cong X_type X Γ nctx stress (FS k) lvl e1 c1 e2 c2 rs s
    = match c1.(c_term), c2.(c_term) with
      | tCase ci1 p1 sc1 brs1, tCase ci2 p2 sc2 brs2 =>
        if case_info_eqb ci1 ci2 && (#|brs1| == #|brs2|)
           && (#|p1.(pparams)| == #|p2.(pparams)|)
           && forallb2 (cmp_level_conv X_type X) p1.(puinst) p2.(puinst)
           && case_ctx_ok p1.(pcontext) p2.(pcontext)
        then
          match case_params X_type X Γ nctx stress (k tt) lvl e1 c1 e2 c2 0%N
                  p1.(pparams) p2.(pparams) (RE e1 :: RE e2 :: rs) s with
          | COk (true, rs, s) =>
            match rs with
            | RE e1 :: RE e2 :: rs =>
              match push_fresh stress #|p1.(pcontext)| lvl e1 e2 (RE e1 :: RE e2 :: rs) s with
              | COk (r, rs, s) =>
                let '(lvlr, er1, er2) := r in
                match conv_term X_type X Γ nctx stress (k tt) lvlr Conv
                        er1 (child c1 1 p1.(preturn)) er2 (child c2 1 p2.(preturn)) rs s with
                | COk (true, rs, s) =>
                  match rs with
                  | RE e1 :: RE e2 :: rs =>
                    match conv_term X_type X Γ nctx stress (k tt) lvl Conv
                            e1 (child c1 0 sc1) e2 (child c2 0 sc2) (RE e1 :: RE e2 :: rs) s with
                    | COk (true, rs, s) =>
                      match rs with
                      | RE e1 :: RE e2 :: rs =>
                        case_branches X_type X Γ nctx stress (k tt) lvl e1 c1 e2 c2 0%N
                          brs1 brs2 rs s
                      | _ => CFail WRoots
                      end
                    | COk (false, rs, s) => COk (false, skipn 2 rs, s)
                    | CFail w => CFail w
                    end
                  | _ => CFail WRoots
                  end
                | COk (false, rs, s) => COk (false, skipn 2 rs, s)
                | CFail w => CFail w
                end
              | CFail w => CFail w
              end
            | _ => CFail WRoots
            end
          | COk (false, rs, s) => COk (false, skipn 2 rs, s)
          | CFail w => CFail w
          end
        else COk (false, rs, s)
      | _, _ => COk (false, rs, s)
      end.
  Proof. reflexivity. Qed.

  (* [cc_split_conv he b r s E] cases on the first call of [conv_term] in [he]. *)
  Ltac cc_split_conv he b r s E :=
    revert he;
    match goal with
    | |- context [conv_term ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 ?a13 ?a14] =>
      destruct (conv_term a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14)
        as [[[b r] s]|?] eqn:E
    end;
    intros he.

  (** *** The branches

    [case_branches] walks the two branch lists side by side. For each pair it checks the two
    contexts with [case_ctx_ok], pushes [#|bcontext|] fresh variables and compares the two
    bodies. The readings of the branches are [rd_br], the branches of the reading of the
    [tCase]; [Ctx br] is the context the body of [br] is compared in, which the caller chooses
    ([Ξ ,,, inst_case_branch_context p br] for [ws_cumul_pb_tCase]). *)
  Lemma case_branches_sound :
    forall (d : cbn_fuel) (lvl : nat) (Ctx : branch term -> context)
      (e1 : cbn_env) (c1 : code) (e2 : cbn_env) (c2 : code) (i : N)
      (l1 l2 : list (branch term)) (ts1 ts2 : list term) (N1 N2 : nat)
      (rs : list root) (s : cbn_state) (rs' : list root) (s' : cbn_state),
      term_seam_below d ->
      cok lvl s -> nctx <= lvl ->
      env_reads (s.(st_heap)) lvl e1 ts1 N1 ->
      env_reads (s.(st_heap)) lvl e2 ts2 N2 ->
      Forall (fun br => #|Ctx br| = lvl + #|br.(bcontext)| /\ is_closed_context (Ctx br)
                /\ on_free_vars (shiftnP #|br.(bcontext)| (shiftnP lvl xpred0)) br.(bbody))
        (map (rd_br ts1 N1) l1) ->
      Forall (fun br => on_free_vars (shiftnP #|br.(bcontext)| (shiftnP lvl xpred0)) br.(bbody))
        (map (rd_br ts2 N2) l2) ->
      case_branches X_type X Γ nctx stress d lvl e1 c1 e2 c2 i l1 l2 rs s
        = COk (true, rs', s') ->
      Forall2 (root_pres nctx (s.(st_heap)) (s'.(st_heap))) rs rs'
      /\ cok lvl s'
      /\ Forall2 (fun br1 br2 => ∥ eq_context_upto_names br1.(bcontext) br2.(bcontext)
                                   × Σ ;;; Ctx br1 ⊢ br1.(bbody) = br2.(bbody) ∥)
           (map (rd_br ts1 N1) l1) (map (rd_br ts2 N2) l2).
  Proof.
    intros d. induction d as [|k ih];
      intros lvl Ctx e1 c1 e2 c2 i l1 l2 ts1 ts2 N1 N2 rs s rs' s'
        hseam hok hnc hr1 hr2 hf1 hf2 he.
    { cbn in he. discriminate he. }
    rewrite case_branches_eq in he.
    destruct l1 as [|b1 l1]; destruct l2 as [|b2 l2].
    - cbn in he. inversion he; subst.
      split; [apply roots_pres_refl|]. split; [exact hok|]. constructor.
    - discriminate he.
    - discriminate he.
    - cbn [map] in hf1, hf2 |- *.
      destruct (cc_Forall_cons_inv _ _ _ hf1) as [[hlenb [hclb hob1]] hf1'].
      destruct (cc_Forall_cons_inv _ _ _ hf2) as [hob2 hf2'].
      cbv beta iota in he.
      destruct (case_ctx_ok (bcontext b1) (bcontext b2)) eqn:Ectx; [|discriminate he].
      cbv beta iota in he.
      destruct (case_ctx_ok_spec _ _ Ectx) as [hctx _ _].
      pose proof (All2_length hctx) as hn12.
      destruct (push_fresh stress #|bcontext b1| lvl e1 e2 (RE e1 :: RE e2 :: rs) s)
        as [[[r rsB] sB]|w] eqn:EB; [|discriminate he].
      pose proof (push_fresh_cok #|bcontext b1| lvl (lvl + #|bcontext b1|) e1 e2 rs s r rsB sB
                    hok EB) as hokB.
      destruct hok as ([lo hso] & hnf & hg & hm & _).
      destruct (push_fresh_spec X_type X Γ nctx stress lo #|bcontext b1| lvl e1 e2 rs s r rsB sB
                  hso hg hm hnf EB)
        as (lo' & e1' & e2' & as_ & F1 & F2 & e1r & e2r & rsB2 & hlas & -> & -> & hq1 & hq2
            & hrsB & hp1' & hp2' & _ & _ & _ & _ & _ & _ & -> & -> & _ & _ & _ & _ & hfr).
      cbv beta iota in he.
      pose proof (env_reads_push _ _ _ #|bcontext b1| _ _ _ _ (bbody b1) hlas eq_refl
                    (env_reads_root _ _ _ _ _ _ _ hp1' hr1) hfr) as hw1.
      pose proof (env_reads_push _ _ _ #|bcontext b2| _ _ _ _ (bbody b2) hlas (eq_sym hn12)
                    (env_reads_root _ _ _ _ _ _ _ hp2' hr2) hfr) as hw2.
      cc_split_conv he bC rsC sC EC; [|discriminate he].
      destruct bC; [|discriminate he].
      cbv beta iota in he.
      destruct (term_seam_below_here k hseam (lvl + #|bcontext b1|) Conv (Ctx (rd_br ts1 N1 b1))
                  _ _ _ _ _ sB true rsC sC hokB hlenb hclb ltac:(lia) EC)
        as (hpC & hokC & hconvB).
      assert (ho1 : is_open_term (Ctx (rd_br ts1 N1 b1)) (bbody (rd_br ts1 N1 b1)))
        by exact (open_in_ctx _ _ _ _ hlenb hob1).
      assert (ho2 : is_open_term (Ctx (rd_br ts1 N1 b1)) (bbody (rd_br ts2 N2 b2))).
      { apply (open_in_ctx _ #|bcontext b2| lvl); [|exact hob2].
        rewrite hlenb, <- hn12. reflexivity. }
      pose proof (hconvB eq_refl (bbody (rd_br ts1 N1 b1)) (bbody (rd_br ts2 N2 b2))
                    hw1 hw2 ho1 ho2) as hcb.
      destruct (Forall2_cons_inv _ _ _ _ hpC) as [qc1 [rsC1 [-> [hqc1 hpC1]]]].
      destruct (root_pres_RE_inv _ _ e1r qc1 hqc1) as [g1 [-> hkg1]].
      destruct (Forall2_cons_inv _ _ _ _ hpC1) as [qc2 [rsC2 [-> [hqc2 hpC2]]]].
      destruct (root_pres_RE_inv _ _ e2r qc2 hqc2) as [g2 [-> hkg2]].
      cbv beta iota in he.
      destruct (ih tt lvl Ctx g1 c1 g2 c2 (N.succ i) l1 l2 ts1 ts2 N1 N2 rsC2 sC rs' s'
                  (term_seam_below_step k hseam) hokC hnc
                  (env_reads_tr _ _ _ _ _ _ _ hkg1 (env_reads_root _ _ _ _ _ _ _ hq1 hr1))
                  (env_reads_tr _ _ _ _ _ _ _ hkg2 (env_reads_root _ _ _ _ _ _ _ hq2 hr2))
                  hf1' hf2' he)
        as (hpE & hokE & hbrs).
      split.
      + exact (roots_pres_trans nctx _ _ _ rs rsB2 rs' hrsB
                 (roots_pres_trans nctx _ _ _ rsB2 rsC2 rs' hpC2 hpE)).
      + split; [exact hokE|]. constructor; [|exact hbrs].
        destruct hcb as [hcb]. constructor. exact (hctx, hcb).
  Qed.

  (** *** The whole rule

    Two stuck matches with the same [case_info], pairwise convertible parameters, universe
    instances related by [cmp_level_conv], contexts equal up to names, convertible return
    clauses and scrutinees and pairwise convertible branches are convertible
    ([ws_cumul_pb_tCase]). The readings of the two [tCase]s are [tCase]s ([rsusp_case]), and
    each sub-call compares exactly one of their components. *)
  Lemma case_cong_sound :
    forall (d : cbn_fuel) (lvl : nat) (Ξ : context) (pb : conv_pb)
      (e1 : cbn_env) (c1 : code) (e2 : cbn_env) (c2 : code)
      (ts1 ts2 : list term) (N1 N2 : nat) (rs : list root) (s : cbn_state)
      (rs' : list root) (s' : cbn_state) (u1 u2 : term),
      term_seam_below d ->
      cok lvl s -> #|Ξ| = lvl -> is_closed_context Ξ -> nctx <= lvl ->
      env_reads (s.(st_heap)) lvl e1 ts1 N1 ->
      env_reads (s.(st_heap)) lvl e2 ts2 N2 ->
      repr_susp nctx (s.(st_heap)) lvl e1 (c1.(c_term)) u1 ->
      repr_susp nctx (s.(st_heap)) lvl e2 (c2.(c_term)) u2 ->
      is_open_term Ξ u1 -> is_open_term Ξ u2 ->
      case_cong X_type X Γ nctx stress d lvl e1 c1 e2 c2 rs s = COk (true, rs', s') ->
      Forall2 (root_pres nctx (s.(st_heap)) (s'.(st_heap))) rs rs'
      /\ cok lvl s'
      /\ ∥ Σ ;;; Ξ ⊢ u1 ≤[pb] u2 ∥.
  Proof.
    intros d lvl Ξ pb e1 c1 e2 c2 ts1 ts2 N1 N2 rs s rs' s' u1 u2
      hseam hok hlen clΞ hnc hr1 hr2 hu1 hu2 ho1 ho2 he.
    destruct d as [|k]; [cbn in he; discriminate he|].
    rewrite case_cong_eq in he.
    destruct (c_term c1) as [| | | | | | | | | | |ci1 p1 sc1 brs1| | | |] eqn:Ec1;
      try discriminate he.
    destruct (c_term c2) as [| | | | | | | | | | |ci2 p2 sc2 brs2| | | |] eqn:Ec2;
      try discriminate he.
    cbv beta iota in he.
    destruct (case_info_eqb ci1 ci2 && (#|brs1| == #|brs2|)
              && (#|pparams p1| == #|pparams p2|)
              && forallb2 (cmp_level_conv X_type X) (puinst p1) (puinst p2)
              && case_ctx_ok (pcontext p1) (pcontext p2)) eqn:Etest; [|discriminate he].
    apply andb_true_iff in Etest as [Etest Ectx].
    apply andb_true_iff in Etest as [Etest Einst].
    apply andb_true_iff in Etest as [Etest _].
    apply andb_true_iff in Etest as [Eci _].
    apply case_info_eqb_eq in Eci. subst ci2.
    cbv beta iota in he.
    destruct (case_ctx_ok_spec _ _ Ectx) as [hctx _ _].
    pose proof (All2_length hctx) as hnctx.
    (* the two readings are [tCase]s *)
    pose proof (env_reads_det _ _ _ _ _ _ _ hr1 hu1) as Eu1.
    rewrite rsusp_case in Eu1. subst u1.
    pose proof (env_reads_det _ _ _ _ _ _ _ hr2 hu2) as Eu2.
    rewrite rsusp_case in Eu2. subst u2.
    destruct (open_case_inv _ _ _ _ _ ho1) as (hop1 & hor1 & hoc1 & hos1 & hob1).
    destruct (open_case_inv _ _ _ _ _ ho2) as (hop2 & hor2 & hoc2 & hos2 & hob2).
    (* the parameters *)
    destruct (case_params X_type X Γ nctx stress (k tt) lvl e1 c1 e2 c2 0%N
                (pparams p1) (pparams p2) (RE e1 :: RE e2 :: rs) s)
      as [[[bA rsA] sA]|w] eqn:EA; [|discriminate he].
    destruct bA; [|discriminate he].
    destruct (case_params_sound (k tt) lvl Ξ e1 c1 e2 c2 0%N (pparams p1) (pparams p2) _ _
                (RE e1 :: RE e2 :: rs) s rsA sA (term_seam_below_step k hseam) hok hlen clΞ hnc
                (env_reads_map _ _ _ _ _ _ hr1) (env_reads_map _ _ _ _ _ _ hr2) hop1 hop2 EA)
      as (hpA & hokA & hparams).
    destruct (Forall2_cons_inv _ _ _ _ hpA) as [qa1 [rsA1 [-> [hqa1 hpA1]]]].
    destruct (root_pres_RE_inv _ _ e1 qa1 hqa1) as [f1 [-> hkf1]].
    destruct (Forall2_cons_inv _ _ _ _ hpA1) as [qa2 [rsA2 [-> [hqa2 hpA2]]]].
    destruct (root_pres_RE_inv _ _ e2 qa2 hqa2) as [f2 [-> hkf2]].
    cbv beta iota in he.
    pose proof (env_reads_tr _ _ _ _ _ _ _ hkf1 hr1) as hrA1.
    pose proof (env_reads_tr _ _ _ _ _ _ _ hkf2 hr2) as hrA2.
    (* the return clauses, under [#|pcontext p1|] fresh variables *)
    destruct (push_fresh stress #|pcontext p1| lvl f1 f2 (RE f1 :: RE f2 :: rsA2) sA)
      as [[[r rsB] sB]|w] eqn:EB; [|discriminate he].
    pose proof (push_fresh_cok #|pcontext p1| lvl (lvl + #|pcontext p1|) f1 f2 rsA2 sA r rsB sB
                  hokA EB) as hokB.
    destruct hokA as ([loA hsoA] & hnfA & hgA & hmA & _).
    destruct (push_fresh_spec X_type X Γ nctx stress loA #|pcontext p1| lvl f1 f2 rsA2 sA r rsB sB
                hsoA hgA hmA hnfA EB)
      as (lo' & f1' & f2' & as_ & F1 & F2 & f1r & f2r & rsB2 & hlas & -> & -> & hq1 & hq2
          & hrsB & hp1' & hp2' & _ & _ & _ & _ & _ & _ & -> & -> & _ & _ & _ & _ & hfr).
    cbv beta iota in he.
    pose proof (env_reads_push _ _ _ #|pcontext p1| _ _ _ _ (preturn p1) hlas eq_refl
                  (env_reads_root _ _ _ _ _ _ _ hp1' hrA1) hfr) as hw1.
    pose proof (env_reads_push _ _ _ #|pcontext p2| _ _ _ _ (preturn p2) hlas (eq_sym hnctx)
                  (env_reads_root _ _ _ _ _ _ _ hp2' hrA2) hfr) as hw2.
    cc_split_conv he bC rsC sC EC; [|discriminate he].
    destruct bC; [|discriminate he].
    cbv beta iota in he.
    assert (hlenR : #|Ξ ,,, inst_case_predicate_context (rd_pred ts1 N1 p1)|
                    = lvl + #|pcontext p1|).
    { rewrite app_context_length, inst_case_predicate_context_length, hlen, Nat.add_comm.
      reflexivity. }
    assert (clR : is_closed_context (Ξ ,,, inst_case_predicate_context (rd_pred ts1 N1 p1)))
      by exact (PCUICOnFreeVarsConv.on_free_vars_ctx_inst_case_context xpred0 Ξ _ _ _
                  hop1 hoc1 clΞ).
    destruct (term_seam_below_here k hseam (lvl + #|pcontext p1|) Conv
                (Ξ ,,, inst_case_predicate_context (rd_pred ts1 N1 p1)) _ _ _ _ _ sB true rsC sC
                hokB hlenR clR ltac:(lia) EC)
      as (hpC & hokC & hconvR).
    assert (hoR1 : is_open_term (Ξ ,,, inst_case_predicate_context (rd_pred ts1 N1 p1))
                     (preturn (rd_pred ts1 N1 p1))).
    { apply (open_in_ctx _ #|pcontext p1| lvl); [exact hlenR|].
      rewrite <- hlen. exact hor1. }
    assert (hoR2 : is_open_term (Ξ ,,, inst_case_predicate_context (rd_pred ts1 N1 p1))
                     (preturn (rd_pred ts2 N2 p2))).
    { apply (open_in_ctx _ #|pcontext p2| lvl).
      - rewrite <- hnctx. exact hlenR.
      - rewrite <- hlen. exact hor2. }
    pose proof (hconvR eq_refl (preturn (rd_pred ts1 N1 p1)) (preturn (rd_pred ts2 N2 p2))
                  hw1 hw2 hoR1 hoR2) as hret.
    destruct (Forall2_cons_inv _ _ _ _ hpC) as [qc1 [rsC1 [-> [hqc1 hpC1]]]].
    destruct (root_pres_RE_inv _ _ f1r qc1 hqc1) as [g1 [-> hkg1]].
    destruct (Forall2_cons_inv _ _ _ _ hpC1) as [qc2 [rsC2 [-> [hqc2 hpC2]]]].
    destruct (root_pres_RE_inv _ _ f2r qc2 hqc2) as [g2 [-> hkg2]].
    cbv beta iota in he.
    pose proof (env_reads_tr _ _ _ _ _ _ _ hkg1 (env_reads_root _ _ _ _ _ _ _ hq1 hrA1))
      as hrC1.
    pose proof (env_reads_tr _ _ _ _ _ _ _ hkg2 (env_reads_root _ _ _ _ _ _ _ hq2 hrA2))
      as hrC2.
    (* the scrutinees *)
    cc_split_conv he bD rsD sD ED; [|discriminate he].
    destruct bD; [|discriminate he].
    cbv beta iota in he.
    destruct (term_seam_below_here k hseam lvl Conv Ξ _ _ _ _ _ sC true rsD sD
                hokC hlen clΞ hnc ED)
      as (hpD & hokD & hconvS).
    pose proof (hconvS eq_refl _ _ (env_reads_here _ _ _ _ _ sc1 hrC1)
                  (env_reads_here _ _ _ _ _ sc2 hrC2) hos1 hos2) as hsc.
    destruct (Forall2_cons_inv _ _ _ _ hpD) as [qd1 [rsD1 [-> [hqd1 hpD1]]]].
    destruct (root_pres_RE_inv _ _ g1 qd1 hqd1) as [h1 [-> hkh1]].
    destruct (Forall2_cons_inv _ _ _ _ hpD1) as [qd2 [rsD2 [-> [hqd2 hpD2]]]].
    destruct (root_pres_RE_inv _ _ g2 qd2 hqd2) as [h2 [-> hkh2]].
    cbv beta iota in he.
    (* the branches *)
    assert (hF1 : Forall (fun br =>
                    #|Ξ ,,, inst_case_branch_context (rd_pred ts1 N1 p1) br| = lvl + #|bcontext br|
                    /\ is_closed_context (Ξ ,,, inst_case_branch_context (rd_pred ts1 N1 p1) br)
                    /\ on_free_vars (shiftnP #|bcontext br| (shiftnP lvl xpred0)) (bbody br))
                  (map (rd_br ts1 N1) brs1)).
    { refine (cc_Forall_impl _ _ _ hob1 _). intros br [hc hb]. split; [|split].
      - rewrite app_context_length, inst_case_branch_context_length, hlen. apply Nat.add_comm.
      - exact (PCUICOnFreeVarsConv.on_free_vars_ctx_inst_case_context xpred0 Ξ _ _ _
                 hop1 hc clΞ).
      - rewrite <- hlen. exact hb. }
    assert (hF2 : Forall (fun br =>
                    on_free_vars (shiftnP #|bcontext br| (shiftnP lvl xpred0)) (bbody br))
                  (map (rd_br ts2 N2) brs2)).
    { refine (cc_Forall_impl _ _ _ hob2 _). intros br [_ hb]. rewrite <- hlen. exact hb. }
    destruct (case_branches_sound (k tt) lvl
                (fun br => Ξ ,,, inst_case_branch_context (rd_pred ts1 N1 p1) br)
                h1 c1 h2 c2 0%N brs1 brs2 ts1 ts2 N1 N2 rsD2 sD rs' s'
                (term_seam_below_step k hseam) hokD hnc
                (env_reads_tr _ _ _ _ _ _ _ hkh1 hrC1) (env_reads_tr _ _ _ _ _ _ _ hkh2 hrC2)
                hF1 hF2 he)
      as (hpE & hokE & hbrs).
    split.
    - exact (roots_pres_trans nctx _ _ _ rs rsA2 rs' hpA2
               (roots_pres_trans nctx _ _ _ rsA2 rsB2 rs' hrsB
                  (roots_pres_trans nctx _ _ _ rsB2 rsC2 rs' hpC2
                     (roots_pres_trans nctx _ _ _ rsC2 rsD2 rs' hpD2 hpE)))).
    - split; [exact hokE|].
      destruct (sq_terms_all2 Ξ _ _ hparams) as [hpars].
      destruct (sq_forall2_all2 _ _ _ hbrs) as [hbrsA].
      destruct hret as [hret]. destruct hsc as [hsc].
      constructor.
      exact (@ws_cumul_pb_tCase cf Σ wfΣ pb Ξ ci1 (rd_pred ts1 N1 p1) (rd_pred ts2 N2 p2)
               _ _ _ _ ho1 ho2 hpars (cmp_level_conv_instance X_type X Σ hΣ _ _ Einst)
               hctx hret hsc hbrsA).
  Qed.
End Conv.

(** * Syntactic facts the ghost-reading comparison needs

  [cg_occ_inv]: a slot the code really uses is a subterm of the reading, so the reading's
  free-variable property passes to it (hygiene rules out an occurrence that is only in a
  [tCase] context). [cg_subst_scope_inv]: the free variables of a term above a substituted
  block. [cg_subst_fresh_lift]: fresh variables pushed at the top of an environment read
  back the lifted body. [cg_code_inv_wf_universes]: a code of a universe-checked entry is
  universe-checked. *)

Local Notation xpred0 := (fun _ : nat => false) (only parsing).
Local Notation xpredT := (fun _ : nat => true) (only parsing).

(** ** List helpers *)

Lemma cg_forallb_In {A} (p : A -> bool) (l : list A) (x : A) :
  forallb p l = true -> In x l -> p x = true.
Proof. intros H Hin. rewrite forallb_forall in H. exact (H x Hin). Qed.

Lemma cg_forallb_nth_some {A} (p : A -> bool) (l : list A) n x :
  forallb p l = true -> nth_error l n = Some x -> p x = true.
Proof. intros h hn. apply nth_error_In in hn. exact (cg_forallb_In p l x h hn). Qed.

Lemma cg_All_forallb_false {A} (Q : A -> Type) (p : A -> bool) (G : Prop) (l : list A) :
  All Q l -> forallb p l = false -> (forall x, In x l -> Q x -> p x = false -> G) -> G.
Proof.
  intros HA. induction HA as [|x l Qx HA IH]; cbn; intros H K; [discriminate H|].
  apply Bool.andb_false_iff in H as [H|H].
  - exact (K x (or_introl eq_refl) Qx H).
  - apply IH; [exact H|]. intros y Hy Qy Hpy. exact (K y (or_intror Hy) Qy Hpy).
Qed.

Lemma cg_forallb_All_impl {A} (Q : A -> Type) (p q : A -> bool) (l : list A) :
  All Q l -> (forall x, Q x -> p x = true -> q x = true) ->
  forallb p l = true -> forallb q l = true.
Proof.
  intros HA Hf. induction HA as [|x l Qx HA IH]; cbn; intros H; [reflexivity|].
  apply Bool.andb_true_iff in H as [H1 H2].
  apply Bool.andb_true_iff; split; [exact (Hf x Qx H1) | exact (IH H2)].
Qed.

Lemma cg_forallb_map_inv {A B} (Q : A -> Type) (p : A -> bool) (q : B -> bool) (f : A -> B)
  (l : list A) :
  All Q l -> (forall x, Q x -> q (f x) = true -> p x = true) ->
  forallb q (map f l) = true -> forallb p l = true.
Proof.
  intros HA Hf. induction HA as [|x l Qx HA IH]; cbn; intros H; [reflexivity|].
  apply Bool.andb_true_iff in H as [H1 H2].
  apply Bool.andb_true_iff; split; [exact (Hf x Qx H1) | exact (IH H2)].
Qed.

Lemma cg_test_context_k_impl_on (Q : term -> Type) (f g : nat -> term -> bool) (m : nat)
  (ctx : context) :
  onctx Q ctx -> (forall i t, Q t -> f i t = true -> g i t = true) ->
  test_context_k f m ctx = true -> test_context_k g m ctx = true.
Proof.
  intros HA Hfg. induction HA as [|d ctx [Hb Ht] HA IH]; cbn [test_context_k]; intros H;
    [reflexivity|].
  apply Bool.andb_true_iff in H as [H1 H2]. apply Bool.andb_true_iff; split; [exact (IH H1)|].
  destruct d as [na [b|] ty]; unfold test_decl in H2 |- *;
    cbn [option_default decl_body decl_type andb] in Hb, Ht, H2 |- *.
  - apply Bool.andb_true_iff in H2 as [H2 H3].
    apply Bool.andb_true_iff; split; [exact (Hfg _ _ Hb H2) | exact (Hfg _ _ Ht H3)].
  - exact (Hfg _ _ Ht H2).
Qed.

(** ** 1. A term closed at [k] does not use an index from [k] on *)

Lemma cg_closedn_noccur : forall (t : term) (k n : nat), closedn k t -> noccur_between k n t.
Proof.
  intros t. elim t using term_forall_list_ind.
  - (* tRel *)
    intros r k n H. cbn [closedn noccur_between] in H |- *.
    apply Bool.orb_true_iff; left; exact H.
  - (* tVar *) intros; reflexivity.
  - (* tEvar *)
    intros ev l Hl k n H. cbn [closedn noccur_between] in H |- *.
    refine (cg_forallb_All_impl _ _ _ _ Hl _ H). intros x Px Hx. apply Px; exact Hx.
  - (* tSort *) intros; reflexivity.
  - (* tProd *)
    intros na A IHA B IHB k n H. cbn [closedn noccur_between] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply IHA | apply IHB]; assumption.
  - (* tLambda *)
    intros na A IHA B IHB k n H. cbn [closedn noccur_between] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply IHA | apply IHB]; assumption.
  - (* tLetIn *)
    intros na b IHb ty IHty B IHB k n H. cbn [closedn noccur_between] in H |- *.
    apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply Bool.andb_true_iff; split|].
    + apply IHb; assumption.
    + apply IHty; assumption.
    + apply IHB; assumption.
  - (* tApp *)
    intros u v IHu IHv k n H. cbn [closedn noccur_between] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply IHu | apply IHv]; assumption.
  - (* tConst *) intros; reflexivity.
  - (* tInd *) intros; reflexivity.
  - (* tConstruct *) intros; reflexivity.
  - (* tCase *)
    intros ci p [Hpar [Hctx Hret]] c IHc brs Hbrs k n H.
    cbn [closedn noccur_between] in H |- *.
    unfold test_predicate_k in H |- *.
    apply Bool.andb_true_iff in H as [H Hbr].
    apply Bool.andb_true_iff in H as [H Hc].
    apply Bool.andb_true_iff in H as [H Hr].
    apply Bool.andb_true_iff in H as [H Hcx].
    apply Bool.andb_true_iff in H as [Hu Hpa].
    apply Bool.andb_true_iff; split.
    2:{ refine (cg_forallb_All_impl _ _ _ _ Hbrs _ Hbr).
        intros br [Pctx Pbody] Hb. unfold test_branch_k in Hb |- *.
        apply Bool.andb_true_iff in Hb as [Hb1 Hb2].
        apply Bool.andb_true_iff; split.
        - refine (cg_test_context_k_impl_on _ _ _ _ _ Pctx _ Hb1).
          intros i t' Qt Ht. apply Qt; exact Ht.
        - apply Pbody; exact Hb2. }
    apply Bool.andb_true_iff; split.
    2:{ apply IHc; exact Hc. }
    apply Bool.andb_true_iff; split.
    2:{ apply Hret; exact Hr. }
    apply Bool.andb_true_iff; split.
    2:{ refine (cg_test_context_k_impl_on _ _ _ _ _ Hctx _ Hcx).
        intros i t' Qt Ht. apply Qt; exact Ht. }
    apply Bool.andb_true_iff; split; [reflexivity|].
    refine (cg_forallb_All_impl _ _ _ _ Hpar _ Hpa). intros x Px Hx. apply Px; exact Hx.
  - (* tProj *)
    intros pr c IHc k n H. cbn [closedn noccur_between] in H |- *. apply IHc; exact H.
  - (* tFix *)
    intros mfix idx Hm k n H. cbn [closedn noccur_between] in H |- *.
    refine (cg_forallb_All_impl _ _ _ _ Hm _ H).
    intros d [Pty Pbody] Hd. unfold test_def in Hd |- *.
    apply Bool.andb_true_iff in Hd as [Hd1 Hd2].
    apply Bool.andb_true_iff; split; [apply Pty | apply Pbody]; assumption.
  - (* tCoFix *)
    intros mfix idx Hm k n H. cbn [closedn noccur_between] in H |- *.
    refine (cg_forallb_All_impl _ _ _ _ Hm _ H).
    intros d [Pty Pbody] Hd. unfold test_def in Hd |- *.
    apply Bool.andb_true_iff in Hd as [Hd1 Hd2].
    apply Bool.andb_true_iff; split; [apply Pty | apply Pbody]; assumption.
  - (* tPrim *)
    intros prim Hprim k n H. cbn [closedn noccur_between] in H |- *.
    destruct prim as [tg [? | ? | ? | a]]; cbn in Hprim, H |- *; try reflexivity.
    destruct Hprim as [Hty [Hdef Hval]].
    apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply Bool.andb_true_iff; split|].
    + refine (cg_forallb_All_impl _ _ _ _ Hval _ H1). intros y Py Hy. apply Py; exact Hy.
    + apply Hdef; exact H2.
    + apply Hty; exact H3.
Qed.

(** ** Free-variable helpers *)

Lemma cg_hyg_shift n t : on_free_vars (shiftnP n xpredT) t = on_free_vars xpredT t.
Proof. apply on_free_vars_ext. apply shiftnP_xpredT. Qed.

Lemma cg_ofv_shiftn (P : nat -> bool) n k t :
  on_free_vars (shiftnP n (shiftnP k P)) t = on_free_vars (shiftnP (n + k) P) t.
Proof. apply on_free_vars_ext. apply shiftnP_add. Qed.

Lemma cg_ofv_lift0 (P : nat -> bool) k u :
  on_free_vars (shiftnP k P) (lift0 k u) = on_free_vars P u.
Proof.
  rewrite lift_rename. rewrite PCUICOnFreeVarsConv.on_free_vars_rename.
  apply on_free_vars_ext. intros i. cbv [shiftnP lift_renaming].
  replace (0 <=? i) with true by (symmetry; apply Nat.leb_le; lia).
  replace (k + i <? k) with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (k + i - k) with i by lia. reflexivity.
Qed.

(** Hygiene closes every [tCase] context, so no index occurs in one. *)
Lemma cg_ctx_hyg_noccur (n m : nat) (ctx : context) :
  test_context_k (fun k => on_free_vars (closedP k xpredT)) m ctx = true ->
  test_context_k (fun k' => noccur_between k' n) m ctx = true.
Proof.
  induction ctx as [|d ctx IH]; cbn [test_context_k]; intros H; [reflexivity|].
  apply Bool.andb_true_iff in H as [H1 H2]. apply Bool.andb_true_iff; split; [exact (IH H1)|].
  destruct d as [na [b|] ty]; unfold test_decl in H2 |- *;
    cbn [option_default decl_body decl_type andb] in H2 |- *.
  - apply Bool.andb_true_iff in H2 as [H2 H3].
    apply Bool.andb_true_iff; split; apply cg_closedn_noccur; rewrite closedP_on_free_vars;
      assumption.
  - apply cg_closedn_noccur; rewrite closedP_on_free_vars; assumption.
Qed.

(** ** 2. An index the term really uses *)

Lemma cg_occ_inv (P : nat -> bool) (ts : list term) (N j : nat) (u : term) :
  nth_error ts j = Some u ->
  forall (t : term) (k : nat),
    on_free_vars xpredT t ->
    noccur_between (k + j) 1 t = false ->
    on_free_vars (shiftnP k P) (subst ts k (lift N (k + #|ts|) t)) ->
    on_free_vars P u.
Proof.
  intros Hj t. elim t using term_forall_list_ind.
  - (* tRel *)
    intros r k _ Hn Hf. cbn [noccur_between] in Hn.
    apply Bool.orb_false_iff in Hn as [H1 H2].
    apply Nat.ltb_ge in H1. apply Nat.leb_gt in H2.
    assert (Hr : r = k + j) by lia. subst r.
    assert (Hlt : j < #|ts|) by (apply nth_error_Some; rewrite Hj; discriminate).
    rewrite (lift_rel_lt N (k + j) (k + #|ts|)) in Hf by lia.
    rewrite (subst_rel_eq ts k j u (k + j) Hj eq_refl) in Hf.
    rewrite cg_ofv_lift0 in Hf. exact Hf.
  - (* tVar *) intros i k _ Hn _. cbn in Hn. discriminate Hn.
  - (* tEvar *)
    intros ev l Hl k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    apply (cg_All_forallb_false _ _ _ _ Hl Hn). intros x Hin IH Hx.
    apply (IH k); [exact (cg_forallb_In _ _ _ Hh Hin) | exact Hx |].
    apply (cg_forallb_In _ _ _ Hf). apply in_map. apply in_map. exact Hin.
  - (* tSort *) intros s k _ Hn _. cbn in Hn. discriminate Hn.
  - (* tProd *)
    intros na A IHA B IHB k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    apply Bool.andb_true_iff in Hh as [HhA HhB]. rewrite cg_hyg_shift in HhB.
    apply Bool.andb_true_iff in Hf as [HfA HfB]. rewrite cg_ofv_shiftn in HfB.
    apply Bool.andb_false_iff in Hn as [Hn|Hn].
    + exact (IHA k HhA Hn HfA).
    + exact (IHB (S k) HhB Hn HfB).
  - (* tLambda *)
    intros na A IHA B IHB k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    apply Bool.andb_true_iff in Hh as [HhA HhB]. rewrite cg_hyg_shift in HhB.
    apply Bool.andb_true_iff in Hf as [HfA HfB]. rewrite cg_ofv_shiftn in HfB.
    apply Bool.andb_false_iff in Hn as [Hn|Hn].
    + exact (IHA k HhA Hn HfA).
    + exact (IHB (S k) HhB Hn HfB).
  - (* tLetIn *)
    intros na b IHb ty IHty B IHB k Hh Hn Hf.
    cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    apply Bool.andb_true_iff in Hh as [Hhb Hh]. apply Bool.andb_true_iff in Hh as [Hhty HhB].
    rewrite cg_hyg_shift in HhB.
    apply Bool.andb_true_iff in Hf as [Hfb Hf]. apply Bool.andb_true_iff in Hf as [Hfty HfB].
    rewrite cg_ofv_shiftn in HfB.
    apply Bool.andb_false_iff in Hn as [Hn|Hn]; [apply Bool.andb_false_iff in Hn as [Hn|Hn]|].
    + exact (IHb k Hhb Hn Hfb).
    + exact (IHty k Hhty Hn Hfty).
    + exact (IHB (S k) HhB Hn HfB).
  - (* tApp *)
    intros a b IHa IHb k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    apply Bool.andb_true_iff in Hh as [Hha Hhb].
    apply Bool.andb_true_iff in Hf as [Hfa Hfb].
    apply Bool.andb_false_iff in Hn as [Hn|Hn].
    + exact (IHa k Hha Hn Hfa).
    + exact (IHb k Hhb Hn Hfb).
  - (* tConst *) intros s ui k _ Hn _. cbn in Hn. discriminate Hn.
  - (* tInd *) intros i ui k _ Hn _. cbn in Hn. discriminate Hn.
  - (* tConstruct *) intros i n ui k _ Hn _. cbn in Hn. discriminate Hn.
  - (* tCase *)
    intros ci p [Hpar [Hctx Hret]] c IHc brs Hbrs k Hh Hn Hf.
    cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    unfold map_predicate_k in Hf. cbn [pparams pcontext preturn puinst] in Hf.
    apply Bool.andb_true_iff in Hh as [Hhpa Hh]. apply Bool.andb_true_iff in Hh as [Hhr Hh].
    apply Bool.andb_true_iff in Hh as [Hhcx Hh]. apply Bool.andb_true_iff in Hh as [Hhc Hhbr].
    apply Bool.andb_true_iff in Hf as [Hfpa Hf]. apply Bool.andb_true_iff in Hf as [Hfr Hf].
    apply Bool.andb_true_iff in Hf as [_ Hf]. apply Bool.andb_true_iff in Hf as [Hfc Hfbr].
    unfold test_predicate_k in Hn.
    apply Bool.andb_false_iff in Hn as [Hn|Hn].
    1: apply Bool.andb_false_iff in Hn as [Hn|Hn].
    1: apply Bool.andb_false_iff in Hn as [Hn|Hn].
    1: apply Bool.andb_false_iff in Hn as [Hn|Hn].
    1: apply Bool.andb_false_iff in Hn as [Hn|Hn].
    + (* puinst *) discriminate Hn.
    + (* pparams *)
      apply (cg_All_forallb_false _ _ _ _ Hpar Hn). intros x Hin IH Hx.
      apply (IH k); [exact (cg_forallb_In _ _ _ Hhpa Hin) | exact Hx |].
      apply (cg_forallb_In _ _ _ Hfpa). apply in_map. apply in_map. exact Hin.
    + (* pcontext *)
      rewrite (cg_ctx_hyg_noccur 1 _ _ Hhcx) in Hn. discriminate Hn.
    + (* preturn *)
      apply (Hret (#|pcontext p| + k)).
      * rewrite cg_hyg_shift in Hhr. exact Hhr.
      * rewrite <- Nat.add_assoc. exact Hn.
      * rewrite cg_ofv_shiftn in Hfr. rewrite <- Nat.add_assoc. exact Hfr.
    + (* scrutinee *) exact (IHc k Hhc Hn Hfc).
    + (* branches *)
      apply (cg_All_forallb_false _ _ _ _ Hbrs Hn). intros br Hin [Pctx Pbody] Hx.
      unfold test_branch_k in Hx.
      pose proof (cg_forallb_In _ _ _ Hhbr Hin) as Hhb. cbn beta in Hhb.
      apply Bool.andb_true_iff in Hhb as [Hhbcx Hhbb].
      apply Bool.andb_false_iff in Hx as [Hx|Hx].
      * rewrite (cg_ctx_hyg_noccur 1 _ _ Hhbcx) in Hx. discriminate Hx.
      * pose proof (cg_forallb_In _ _ _ Hfbr (in_map _ _ _ (in_map _ _ _ Hin))) as Hfb.
        cbn [map_branch_k bcontext bbody id] in Hfb.
        apply Bool.andb_true_iff in Hfb as [_ Hfb].
        apply (Pbody (#|bcontext br| + k)).
        -- rewrite cg_hyg_shift in Hhbb. exact Hhbb.
        -- rewrite <- Nat.add_assoc. exact Hx.
        -- rewrite cg_ofv_shiftn in Hfb. rewrite <- Nat.add_assoc. exact Hfb.
  - (* tProj *)
    intros pr c IHc k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    exact (IHc k Hh Hn Hf).
  - (* tFix *)
    intros mfix idx Hm k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    rewrite !length_map in Hf.
    apply (cg_All_forallb_false _ _ _ _ Hm Hn). intros d Hin [Pty Pbody] Hx.
    unfold test_def in Hx.
    pose proof (cg_forallb_In _ _ _ Hh Hin) as Hhd. unfold test_def in Hhd.
    apply Bool.andb_true_iff in Hhd as [Hhty Hhbody].
    pose proof (cg_forallb_In _ _ _ Hf (in_map _ _ _ (in_map _ _ _ Hin))) as Hfd.
    unfold test_def in Hfd. cbn [map_def dtype dbody] in Hfd.
    apply Bool.andb_true_iff in Hfd as [Hfty Hfbody].
    apply Bool.andb_false_iff in Hx as [Hx|Hx].
    + exact (Pty k Hhty Hx Hfty).
    + apply (Pbody (#|mfix| + k)).
      * rewrite cg_hyg_shift in Hhbody. exact Hhbody.
      * rewrite <- Nat.add_assoc. exact Hx.
      * rewrite cg_ofv_shiftn in Hfbody. rewrite <- Nat.add_assoc. exact Hfbody.
  - (* tCoFix *)
    intros mfix idx Hm k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    rewrite !length_map in Hf.
    apply (cg_All_forallb_false _ _ _ _ Hm Hn). intros d Hin [Pty Pbody] Hx.
    unfold test_def in Hx.
    pose proof (cg_forallb_In _ _ _ Hh Hin) as Hhd. unfold test_def in Hhd.
    apply Bool.andb_true_iff in Hhd as [Hhty Hhbody].
    pose proof (cg_forallb_In _ _ _ Hf (in_map _ _ _ (in_map _ _ _ Hin))) as Hfd.
    unfold test_def in Hfd. cbn [map_def dtype dbody] in Hfd.
    apply Bool.andb_true_iff in Hfd as [Hfty Hfbody].
    apply Bool.andb_false_iff in Hx as [Hx|Hx].
    + exact (Pty k Hhty Hx Hfty).
    + apply (Pbody (#|mfix| + k)).
      * rewrite cg_hyg_shift in Hhbody. exact Hhbody.
      * rewrite <- Nat.add_assoc. exact Hx.
      * rewrite cg_ofv_shiftn in Hfbody. rewrite <- Nat.add_assoc. exact Hfbody.
  - (* tPrim *)
    intros prim Hprim k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    destruct prim as [tg [? | ? | ? | a]]; cbn -[shiftnP] in Hprim, Hh, Hn, Hf;
      try discriminate Hn.
    destruct Hprim as [Hty [Hdef Hval]].
    apply Bool.andb_true_iff in Hh as [Hh Hhty]. apply Bool.andb_true_iff in Hh as [Hhval Hhdef].
    apply Bool.andb_true_iff in Hf as [Hf Hfty]. apply Bool.andb_true_iff in Hf as [Hfval Hfdef].
    apply Bool.andb_false_iff in Hn as [Hn|Hn]; [apply Bool.andb_false_iff in Hn as [Hn|Hn]|].
    + apply (cg_All_forallb_false _ _ _ _ Hval Hn). intros x Hin IH Hx.
      apply (IH k); [exact (cg_forallb_In _ _ _ Hhval Hin) | exact Hx |].
      apply (cg_forallb_In _ _ _ Hfval). apply in_map. apply in_map. exact Hin.
    + exact (Hdef k Hhdef Hn Hfdef).
    + exact (Hty k Hhty Hn Hfty).
Qed.

(** ** 3. The free variables above a substituted block *)

Lemma cg_subst_scope_inv (P : nat -> bool) (ws : list term) :
  forall (b : term) (k : nat),
    on_free_vars (shiftnP k P) (subst ws k b) -> on_free_vars (shiftnP (k + #|ws|) P) b.
Proof.
  intros b. elim b using term_forall_list_ind.
  - (* tRel *)
    intros r k H. cbn [subst] in H. cbn [on_free_vars]. unfold shiftnP.
    revert H. destruct (k <=? r) eqn:E; intros H.
    + apply Nat.leb_le in E. revert H. destruct (nth_error ws (r - k)) as [x|] eqn:E2; intros H.
      * apply Bool.orb_true_iff; left. apply Nat.ltb_lt.
        assert (r - k < #|ws|) by (apply nth_error_Some; rewrite E2; discriminate). lia.
      * apply nth_error_None in E2. cbn [on_free_vars] in H. unfold shiftnP in H.
        apply Bool.orb_true_iff in H as [H|H]; [apply Nat.ltb_lt in H; lia|].
        apply Bool.orb_true_iff; right.
        replace (r - (k + #|ws|)) with (r - #|ws| - k) by lia. exact H.
    + apply Nat.leb_gt in E. apply Bool.orb_true_iff; left. apply Nat.ltb_lt. lia.
  - (* tVar *) intros; reflexivity.
  - (* tEvar *)
    intros ev l Hl k H. cbn [subst on_free_vars] in H |- *.
    refine (cg_forallb_map_inv _ _ _ _ _ Hl _ H). intros x Px Hx. exact (Px k Hx).
  - (* tSort *) intros; reflexivity.
  - (* tProd *)
    intros na A IHA B IHB k H. cbn [subst on_free_vars] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H2]. rewrite cg_ofv_shiftn in H2 |- *.
    apply Bool.andb_true_iff; split; [exact (IHA k H1) | exact (IHB (S k) H2)].
  - (* tLambda *)
    intros na A IHA B IHB k H. cbn [subst on_free_vars] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H2]. rewrite cg_ofv_shiftn in H2 |- *.
    apply Bool.andb_true_iff; split; [exact (IHA k H1) | exact (IHB (S k) H2)].
  - (* tLetIn *)
    intros na b0 IHb ty IHty B IHB k H. cbn [subst on_free_vars] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H]. apply Bool.andb_true_iff in H as [H2 H3].
    rewrite cg_ofv_shiftn in H3 |- *.
    apply Bool.andb_true_iff; split; [exact (IHb k H1)|].
    apply Bool.andb_true_iff; split; [exact (IHty k H2) | exact (IHB (S k) H3)].
  - (* tApp *)
    intros a b0 IHa IHb k H. cbn [subst on_free_vars] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [exact (IHa k H1) | exact (IHb k H2)].
  - (* tConst *) intros; reflexivity.
  - (* tInd *) intros; reflexivity.
  - (* tConstruct *) intros; reflexivity.
  - (* tCase *)
    intros ci p [Hpar [Hctx Hret]] c IHc brs Hbrs k H.
    cbn [subst on_free_vars] in H |- *.
    unfold map_predicate_k in H. cbn [pparams pcontext preturn puinst] in H.
    rewrite length_map in H.
    apply Bool.andb_true_iff in H as [Hpa H]. apply Bool.andb_true_iff in H as [Hr H].
    apply Bool.andb_true_iff in H as [Hcx H]. apply Bool.andb_true_iff in H as [Hc Hbr].
    apply Bool.andb_true_iff; split.
    { refine (cg_forallb_map_inv _ _ _ _ _ Hpar _ Hpa). intros x Px Hx. exact (Px k Hx). }
    apply Bool.andb_true_iff; split.
    { rewrite cg_ofv_shiftn in Hr |- *. rewrite Nat.add_assoc. exact (Hret _ Hr). }
    apply Bool.andb_true_iff; split; [exact Hcx|].
    apply Bool.andb_true_iff; split; [exact (IHc k Hc)|].
    refine (cg_forallb_map_inv _ _ _ _ _ Hbrs _ Hbr). intros br [Pctx Pbody] Hx.
    cbn [map_branch_k bcontext bbody id] in Hx.
    apply Bool.andb_true_iff in Hx as [Hx1 Hx2]. apply Bool.andb_true_iff; split; [exact Hx1|].
    rewrite cg_ofv_shiftn in Hx2 |- *. rewrite Nat.add_assoc. exact (Pbody _ Hx2).
  - (* tProj *)
    intros pr c IHc k H. cbn [subst on_free_vars] in H |- *. exact (IHc k H).
  - (* tFix *)
    intros mfix idx Hm k H. cbn [subst on_free_vars] in H |- *. rewrite !length_map in H.
    refine (cg_forallb_map_inv _ _ _ _ _ Hm _ H). intros d [Pty Pbody] Hx.
    unfold test_def in Hx |- *. cbn [map_def dtype dbody] in Hx.
    apply Bool.andb_true_iff in Hx as [Hx1 Hx2].
    apply Bool.andb_true_iff; split; [exact (Pty k Hx1)|].
    rewrite cg_ofv_shiftn in Hx2 |- *. rewrite Nat.add_assoc. exact (Pbody _ Hx2).
  - (* tCoFix *)
    intros mfix idx Hm k H. cbn [subst on_free_vars] in H |- *. rewrite !length_map in H.
    refine (cg_forallb_map_inv _ _ _ _ _ Hm _ H). intros d [Pty Pbody] Hx.
    unfold test_def in Hx |- *. cbn [map_def dtype dbody] in Hx.
    apply Bool.andb_true_iff in Hx as [Hx1 Hx2].
    apply Bool.andb_true_iff; split; [exact (Pty k Hx1)|].
    rewrite cg_ofv_shiftn in Hx2 |- *. rewrite Nat.add_assoc. exact (Pbody _ Hx2).
  - (* tPrim *)
    intros prim Hprim k H. cbn [subst on_free_vars] in H |- *.
    destruct prim as [tg [? | ? | ? | a]]; cbn -[shiftnP] in Hprim, H |- *; try reflexivity.
    destruct Hprim as [Hty [Hdef Hval]].
    apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply Bool.andb_true_iff; split|].
    + refine (cg_forallb_map_inv _ _ _ _ _ Hval _ H1). intros y Py Hy. exact (Py k Hy).
    + exact (Hdef k H2).
    + exact (Hty k H3).
Qed.

(** ** 4. Substituting the identity readings back *)

Lemma cg_subst_idsn_lift (k : nat) (t : term) : subst (idsn k) 0 (lift k k t) = t.
Proof.
  revert t. induction k as [|k IH]; intros t.
  - cbn [idsn]. rewrite subst_empty. apply lift0_id.
  - cbn [idsn]. rewrite subst_app_simpl. rewrite idsn_length. cbn [Nat.add].
    rewrite (subst_reli_lift_id k k t (le_n k)). exact (IH t).
Qed.

(** ** 5. Substituting lifted identity readings *)

Lemma cg_subst_fresh_lift (m k : nat) (t : term) :
  subst (map (lift0 m) (idsn k)) 0 (lift (m + k) k t) = lift0 m t.
Proof.
  pose proof (distr_lift_subst (lift k k t) (idsn k) m 0) as E.
  rewrite cg_subst_idsn_lift in E. rewrite idsn_length, Nat.add_0_r in E.
  rewrite (simpl_lift t k k m k) in E by lia.
  symmetry; exact E.
Qed.

(** ** 6. Universe well-formedness of a code's term *)

Lemma cg_code_inv_wf_universes {cf : checker_flags} (Σ : global_env_ext) (e : code_entry) (c : code) :
  code_inv e c -> wf_universes Σ (inst_code e.(ce_inst) e.(ce_term)) ->
  wf_universes Σ c.(c_term).
Proof.
  unfold code_inv; cbv zeta. intros [ks [_ ht]] hr. revert ht.
  generalize (c_term c) as t.
  induction ks as [|k ks IH]; cbn [fold_right]; intros t ht.
  - injection ht as <-. exact hr.
  - destruct (fold_right _ _ ks) as [t0|] eqn:E; [|discriminate ht].
    pose proof (IH t0 eq_refl) as h0. clear IH E.
    unfold wf_universes in h0 |- *.
    destruct t0; cbn [on_universes] in h0; cbn in ht; try discriminate ht;
      repeat match goal with
             | H : is_true (_ && _) |- _ => apply andb_true_iff in H as [? ?]
             | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
             end.
    + (* tProd *)
      destruct k as [|[q|q|]]; cbn in ht; try discriminate ht; injection ht as <-; assumption.
    + (* tLambda *)
      destruct k as [|[q|q|]]; cbn in ht; try discriminate ht; injection ht as <-; assumption.
    + (* tLetIn *)
      destruct k as [|[q|[q|q|]|]]; cbn in ht; try discriminate ht; injection ht as <-;
        assumption.
    + (* tApp *)
      destruct k as [|[q|q|]]; cbn in ht; try discriminate ht; injection ht as <-; assumption.
    + (* tCase *)
      destruct k as [|[q|q|]]; cbn in ht.
      * injection ht as <-. assumption.
      * destruct (nth_error brs _) as [br|] eqn:Eb; cbn in ht; [|discriminate ht].
        injection ht as <-.
        match goal with H : forallb _ brs = true |- _ =>
          pose proof (cg_forallb_nth_some _ _ _ _ H Eb) as hb end.
        unfold test_branch in hb. apply andb_true_iff in hb as [_ hb]. exact hb.
      * match goal with H : forallb _ (pparams _) = true |- _ =>
          exact (cg_forallb_nth_some _ _ _ _ H ht) end.
      * injection ht as <-. assumption.
    + (* tProj *)
      destruct k as [|q]; cbn in ht; [injection ht as <-; assumption|discriminate ht].
    + (* tFix *)
      destruct (nth_error mfix _) as [d|] eqn:Ed; cbn in ht; [|discriminate ht].
      injection ht as <-.
      pose proof (cg_forallb_nth_some _ _ _ _ h0 Ed) as hd.
      cbn beta in hd. apply andb_true_iff in hd. exact (proj2 hd).
    + (* tCoFix *)
      destruct (nth_error mfix _) as [d|] eqn:Ed; cbn in ht; [|discriminate ht].
      injection ht as <-.
      pose proof (cg_forallb_nth_some _ _ _ _ h0 Ed) as hd.
      cbn beta in hd. apply andb_true_iff in hd. exact (proj2 hd).
Qed.

(** * A machine call returns the caller's roots renamed, never reshaped (BET-298)

  The shape of a root is the root with every heap address replaced by one constant address
  ([mp_root kc]). A renaming ([rn_*]), a collection, an allocation and every function of the
  machine give back roots of the shape of the roots they were given: each function pops
  exactly the frames it pushes, and threads the rest through calls that keep their shape. *)

Definition kc : haddr -> haddr := fun _ => HAddr xH.

(** Two root lists of one shape, less their first root. *)
Lemma sk_tl r r' rs rs' :
  mp_roots kc (r' :: rs') = mp_roots kc (r :: rs) -> mp_roots kc rs' = mp_roots kc rs.
Proof. intros h. exact (f_equal (@tl root) h). Qed.

(** Strip the frames a call pushed and popped, then chain the equations of the calls. *)
Local Ltac sk_fin :=
  repeat match goal with
         | h : mp_roots kc (_ :: _) = mp_roots kc (_ :: _) |- _ => apply sk_tl in h
         end;
  repeat match goal with
         | h : mp_roots kc ?a = mp_roots kc ?b |- mp_roots kc ?a = _ => rewrite h; clear h
         end;
  reflexivity.

(** ** A renaming keeps the shape of what it renames *)

Section SkRename.
  Context {G : Type} (f : haddr -> G -> cbn_res (haddr * G)).

  Lemma sk_rn_addrs : forall l g l' g', rn_addrs f l g = COk (l', g') -> map kc l' = map kc l.
  Proof.
    induction l as [|a l ih]; intros g l' g' he; simpl in he.
    - injection he as <- <-. reflexivity.
    - destruct (f a g) as [[b g1]|w] eqn:e1; [|discriminate].
      destruct (rn_addrs f l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
      injection he as <- <-. cbn [map]. rewrite (ih _ _ _ e2). reflexivity.
  Qed.

  Lemma sk_rn_slot : forall x g x' g', rn_slot f x g = COk (x', g') -> mp_slot kc x' = mp_slot kc x.
  Proof.
    intros x. induction x as [a|vs n o c ihvs] using slot_ind'; intros g x' g' he.
    - simpl in he. destruct (f a g) as [[b g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. reflexivity.
    - rewrite rn_slot_SInl in he.
      destruct (rn_slots f vs g) as [[vs' g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. cbn [mp_slot]. f_equal.
      revert g vs' g1 e1.
      induction ihvs as [|y vs hy hvs ihl]; intros g vs' g1 e1; simpl in e1.
      + injection e1 as <- <-. reflexivity.
      + destruct (rn_slot f y g) as [[y' ga]|wa] eqn:ea; [|discriminate].
        destruct (rn_slots f vs ga) as [[vs2 gb]|wb] eqn:eb; [|discriminate].
        injection e1 as <- <-. cbn [map]. rewrite (hy _ _ _ ea), (ihl _ _ _ eb). reflexivity.
  Qed.

  Lemma sk_rn_slots : forall l g l' g',
    rn_slots f l g = COk (l', g') -> mp_slots kc l' = mp_slots kc l.
  Proof.
    unfold mp_slots. induction l as [|y l ih]; intros g l' g' he; simpl in he.
    - injection he as <- <-. reflexivity.
    - destruct (rn_slot f y g) as [[y' g1]|w] eqn:e1; [|discriminate].
      destruct (rn_slots f l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
      injection he as <- <-. cbn [map].
      rewrite (sk_rn_slot _ _ _ _ e1), (ih _ _ _ e2). reflexivity.
  Qed.

  Lemma sk_rn_env e g e' g' : rn_env f e g = COk (e', g') -> mp_env kc e' = mp_env kc e.
  Proof.
    intros he. unfold rn_env in he.
    destruct (rn_slots f (ev_vals e) g) as [[vs g1]|w] eqn:e1; [|discriminate].
    injection he as <- <-. unfold mp_env. cbn [ev_vals ev_nvals ev_goff].
    rewrite (sk_rn_slots _ _ _ _ e1). reflexivity.
  Qed.

  Lemma sk_rn_value v g v' g' : rn_value f v g = COk (v', g') -> mp_value kc v' = mp_value kc v.
  Proof.
    intros he. unfold rn_value in he.
    destruct v as [h sp|e c|e c i sp|e c i sp|h sp|e c|e c sp].
    - destruct (rn_addrs f sp g) as [[sp1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. cbn [mp_value]. rewrite (sk_rn_addrs _ _ _ _ e1). reflexivity.
    - destruct (rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      injection he as <- <-. cbn [mp_value]. rewrite (sk_rn_env _ _ _ _ E1). reflexivity.
    - destruct (rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      destruct (rn_addrs f sp g1) as [[sp1 g2]|w] eqn:E2; [|discriminate].
      injection he as <- <-. cbn [mp_value].
      rewrite (sk_rn_env _ _ _ _ E1), (sk_rn_addrs _ _ _ _ E2). reflexivity.
    - destruct (rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      destruct (rn_addrs f sp g1) as [[sp1 g2]|w] eqn:E2; [|discriminate].
      injection he as <- <-. cbn [mp_value].
      rewrite (sk_rn_env _ _ _ _ E1), (sk_rn_addrs _ _ _ _ E2). reflexivity.
    - destruct (rn_addrs f sp g) as [[sp1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. cbn [mp_value]. rewrite (sk_rn_addrs _ _ _ _ e1). reflexivity.
    - destruct (rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      injection he as <- <-. cbn [mp_value]. rewrite (sk_rn_env _ _ _ _ E1). reflexivity.
    - destruct (rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      destruct (rn_addrs f sp g1) as [[sp1 g2]|w] eqn:E2; [|discriminate].
      injection he as <- <-. cbn [mp_value].
      rewrite (sk_rn_env _ _ _ _ E1), (sk_rn_addrs _ _ _ _ E2). reflexivity.
  Qed.

  Lemma sk_rn_cell cl g cl' g' : rn_cell f cl g = COk (cl', g') -> mp_cell kc cl' = mp_cell kc cl.
  Proof.
    intros he. unfold rn_cell in he. destruct cl as [vs n o c|v| |b].
    - destruct (rn_slots f vs g) as [[vs1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. cbn [mp_cell]. rewrite (sk_rn_slots _ _ _ _ e1). reflexivity.
    - destruct (rn_value f v g) as [[v1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. cbn [mp_cell]. rewrite (sk_rn_value _ _ _ _ e1). reflexivity.
    - injection he as <- <-. reflexivity.
    - destruct (f b g) as [[b1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. reflexivity.
  Qed.
End SkRename.

Lemma rn_root_skel {G : Type} (f : haddr -> G -> cbn_res (haddr * G)) (r : root) (g : G) r' g' :
  rn_root f r g = COk (r', g') -> mp_root kc r' = mp_root kc r.
Proof.
  intros he. unfold rn_root in he. destruct r as [a|x|e|v|l|l|cl].
  - destruct (f a g) as [[b g1]|w] eqn:e1; [|discriminate].
    injection he as <- <-. reflexivity.
  - destruct (rn_slot f x g) as [[x1 g1]|w] eqn:e1; [|discriminate].
    injection he as <- <-. cbn [mp_root]. rewrite (sk_rn_slot f _ _ _ _ e1). reflexivity.
  - destruct (rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
    injection he as <- <-. cbn [mp_root]. rewrite (sk_rn_env f _ _ _ _ E1). reflexivity.
  - destruct (rn_value f v g) as [[v1 g1]|w] eqn:e1; [|discriminate].
    injection he as <- <-. cbn [mp_root]. rewrite (sk_rn_value f _ _ _ _ e1). reflexivity.
  - destruct (rn_slots f l g) as [[l1 g1]|w] eqn:e1; [|discriminate].
    injection he as <- <-. cbn [mp_root]. rewrite (sk_rn_slots f _ _ _ _ e1). reflexivity.
  - destruct (rn_addrs f l g) as [[l1 g1]|w] eqn:e1; [|discriminate].
    injection he as <- <-. cbn [mp_root]. rewrite (sk_rn_addrs f _ _ _ _ e1). reflexivity.
  - destruct (rn_cell f cl g) as [[cl1 g1]|w] eqn:e1; [|discriminate].
    injection he as <- <-. cbn [mp_root]. rewrite (sk_rn_cell f _ _ _ _ e1). reflexivity.
Qed.

Lemma rn_roots_skel {G : Type} (f : haddr -> G -> cbn_res (haddr * G)) (rs : list root) (g : G)
    rs' g' :
  rn_roots f rs g = COk (rs', g') -> mp_roots kc rs' = mp_roots kc rs.
Proof.
  revert g rs' g'. induction rs as [|r rs ih]; intros g rs' g' he; simpl in he.
  - injection he as <- <-. reflexivity.
  - destruct (rn_root f r g) as [[r1 g1]|w] eqn:e1; [|discriminate].
    destruct (rn_roots f rs g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
    injection he as <- <-. unfold mp_roots in *. cbn [map].
    rewrite (rn_root_skel f _ _ _ _ e1), (ih _ _ _ e2). reflexivity.
Qed.

(** ** A collection, and an allocation *)

Lemma collect_skel (rs : list root) (s : cbn_state) rs' s' :
  collect rs s = COk (rs', s') -> mp_roots kc rs' = mp_roots kc rs.
Proof.
  intros he. rewrite collect_eq in he.
  destruct (rn_ptree (gc_copy (fuel_of_pos s.(st_next) (fun _ => FO))) s.(st_gam)
              (mkGc s.(st_heap) (bh_holes s.(st_next)) s.(st_next))) as [[gm g1]|w] eqn:e1;
    [|discriminate he].
  destruct (rn_roots (gc_copy (fuel_of_pos s.(st_next) (fun _ => FO))) rs g1)
    as [[rs2 g2]|w] eqn:e2; [|discriminate he].
  injection he as <- <-. exact (rn_roots_skel _ _ _ _ _ e2).
Qed.

Lemma alloc_skel (stress : bool) cl rs s a rs' s' :
  alloc stress cl rs s = COk (a, rs', s') -> mp_roots kc rs' = mp_roots kc rs.
Proof.
  intros he. destruct (gc_due stress s) eqn:eg.
  - rewrite (alloc_gc stress cl rs s eg) in he.
    destruct (collect (RC cl :: rs) s) as [[rs2 s2]|w] eqn:ec; [|discriminate he].
    pose proof (collect_skel _ _ _ _ ec) as h1.
    destruct rs2 as [|[| | | | | |cl2] rs2]; try discriminate he.
    injection he as <- <- <-. exact (sk_tl _ _ _ _ h1).
  - rewrite (alloc_no_gc stress cl rs s eg) in he. injection he as <- <- <-. reflexivity.
Qed.

(** ** The machine *)

(** The first call whose answer [he] matches on: its answer is [COk (x, y, z)], named by [e]. *)
Local Ltac dcall he e x y z :=
  lazymatch type of he with
  | context [match ?t with COk _ => _ | CFail _ => _ end] =>
      destruct t as [[[x y] z]|?] eqn:e; [|discriminate he]
  end.

(** The decisions of a match or projection on a constructor: each test that fails fails. *)
Local Ltac dtests he :=
  repeat (match type of he with
          | context [if ?b then _ else _] => destruct b
          | context [match ?o with Some _ => _ | None => _ end] => destruct o
          | context [match ?m with O => _ | S _ => _ end] => destruct m
          end; try discriminate he).

Lemma push_fresh_skel (stress : bool) : forall n lvl e1 e2 rs s r rs' s',
  push_fresh stress n lvl e1 e2 rs s = COk (r, rs', s') -> mp_roots kc rs' = mp_roots kc rs.
Proof.
  induction n as [|n ih]; intros lvl e1 e2 rs s r rs' s' he; cbn [push_fresh] in he.
  - injection he as <- <- <-. reflexivity.
  - dcall he ea x1 rs1 s1.
    destruct rs1 as [|[| |f1| | | |] [|[| |f2| | | |] rs1]]; try discriminate he.
    pose proof (alloc_skel _ _ _ _ _ _ _ ea) as h1.
    pose proof (ih _ _ _ _ _ _ _ _ he) as h2. sk_fin.
Qed.

Section SkMachine.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat) (stress : bool).

  Lemma gam_skel j rs s a rs' s' :
    gam X_type X Γ nctx stress j rs s = COk (a, rs', s') -> mp_roots kc rs' = mp_roots kc rs.
  Proof.
    intros he. unfold gam in he. cbv zeta in he.
    destruct (PTree.get (key_of_succ_nat j) s.(st_gam)) as [a0|].
    { injection he as <- <- <-. reflexivity. }
    destruct (nth_error Γ j) as [decl|]; [|discriminate he].
    destruct (decl_body decl) as [b|].
    - destruct (new_entry X_type X b [] (NSCtx j) s) as [c s1].
      cbv beta iota in he. dcall he ea a1 rs1 s2.
      injection he as <- <- <-. exact (alloc_skel _ _ _ _ _ _ _ ea).
    - cbv beta iota in he. dcall he ea a1 rs1 s2.
      injection he as <- <- <-. exact (alloc_skel _ _ _ _ _ _ _ ea).
  Qed.

  Lemma env_var_skel n e rs s x rs' s' :
    env_var X_type X Γ nctx stress n e rs s = COk (x, rs', s') ->
    mp_roots kc rs' = mp_roots kc rs.
  Proof.
    intros he. unfold env_var in he.
    destruct (nth_error e.(ev_vals) n) as [y|].
    - injection he as <- <- <-. reflexivity.
    - dcall he eg a1 rs1 s1. injection he as <- <- <-. exact (gam_skel _ _ _ _ _ _ eg).
  Qed.

  Lemma arg_slot_skel e c rs s x rs' s' :
    arg_slot X_type X Γ nctx stress e c rs s = COk (x, rs', s') ->
    mp_roots kc rs' = mp_roots kc rs.
  Proof.
    intros he. unfold arg_slot in he.
    destruct (c_term c); try (injection he as <- <- <-; reflexivity).
    exact (env_var_skel _ _ _ _ _ _ _ he).
  Qed.

  Lemma materialize_skel x rs s a rs' s' :
    materialize X_type X stress x rs s = COk (a, rs', s') -> mp_roots kc rs' = mp_roots kc rs.
  Proof.
    intros he. unfold materialize in he.
    destruct x as [a0|vs n o c]; [injection he as <- <- <-; reflexivity|].
    destruct (c_term c) eqn:ec; try exact (alloc_skel _ _ _ _ _ _ _ he).
    - lazymatch type of he with
      | context [delta X_type X ?kn ?ui s] =>
        destruct (delta X_type X kn ui s) as [[[c'|] s1]|w] eqn:ed
      end; exact (alloc_skel _ _ _ _ _ _ _ he).
    - lazymatch type of he with
      | context [nth_error ?m ?i] => destruct (nth_error m i)
      end; exact (alloc_skel _ _ _ _ _ _ _ he).
  Qed.

  Lemma bind_skel x body rs s y rs' s' :
    bind X_type X stress x body rs s = COk (y, rs', s') -> mp_roots kc rs' = mp_roots kc rs.
  Proof.
    intros he. unfold bind in he. destruct x as [a0|vals n o c].
    - injection he as <- <- <-. reflexivity.
    - destruct (once_body body s) as [b s1]. destruct b.
      + injection he as <- <- <-. reflexivity.
      + dcall he em a1 rs1 s2. injection he as <- <- <-.
        exact (materialize_skel _ _ _ _ _ _ em).
  Qed.

  Lemma mat_all_skel : forall d l rs s al rs' s',
    mat_all X_type X stress d l rs s = COk (al, rs', s') -> mp_roots kc rs' = mp_roots kc rs.
  Proof.
    intros d. induction d as [|k ih]; intros l rs s al rs' s' he;
      destruct l as [|x l]; cbn [mat_all] in he.
    1,3: injection he as <- <- <-; reflexivity.
    - discriminate he.
    - dcall he em a1 rs1 s1.
      destruct rs1 as [|[| | | |l1| |] rs1]; try discriminate he.
      pose proof (materialize_skel _ _ _ _ _ _ em) as h1.
      dcall he em2 al1 rs2 s2.
      destruct rs2 as [|[a0| | | | | |] rs2]; try discriminate he.
      injection he as <- <- <-.
      pose proof (ih tt _ _ _ _ _ _ em2) as h2. sk_fin.
  Qed.

  Lemma push_fix_cells_skel : forall n e c i acc rs s e' rs' s',
    push_fix_cells stress e c i n acc rs s = COk (e', rs', s') ->
    mp_roots kc rs' = mp_roots kc rs.
  Proof.
    induction n as [|n ih]; intros e c i acc rs s e' rs' s' he;
      cbn [push_fix_cells] in he.
    - injection he as <- <- <-. reflexivity.
    - dcall he ea a1 rs1 s1.
      destruct rs1 as [|[| |e1| | | |] [|[| |acc1| | | |] rs1]]; try discriminate he.
      pose proof (alloc_skel _ _ _ _ _ _ _ ea) as h1.
      pose proof (ih _ _ _ _ _ _ _ _ _ he) as h2. sk_fin.
  Qed.

  (** The five functions of the machine at one fuel. *)
  Definition sk_m (d : cbn_fuel) : Prop :=
    (forall a rs s v rs' s', force X_type X Γ nctx stress d a rs s = COk (v, rs', s') ->
       mp_roots kc rs' = mp_roots kc rs)
    /\ (forall x stk rs s v rs' s', eval_slot X_type X Γ nctx stress d x stk rs s = COk (v, rs', s') ->
       mp_roots kc rs' = mp_roots kc rs)
    /\ (forall e c stk rs s v rs' s', whnf X_type X Γ nctx stress d e c stk rs s = COk (v, rs', s') ->
       mp_roots kc rs' = mp_roots kc rs)
    /\ (forall e c mfix idx stk rs s v rs' s',
         whnf_fix X_type X Γ nctx stress d e c mfix idx stk rs s = COk (v, rs', s') ->
       mp_roots kc rs' = mp_roots kc rs)
    /\ (forall v stk rs s w rs' s', apply X_type X Γ nctx stress d v stk rs s = COk (w, rs', s') ->
       mp_roots kc rs' = mp_roots kc rs).

  Lemma sk_machine : forall d, sk_m d.
  Proof.
    intros d. induction d as [|k ih].
    - (* FO: every call fails, except [apply] with an empty stack *)
      split; [|split; [|split; [|split]]].
      + intros a rs s v rs' s' he. cbn [force] in he. discriminate he.
      + intros x stk rs s v rs' s' he. cbn [eval_slot] in he. discriminate he.
      + intros e c stk rs s v rs' s' he. cbn [whnf] in he. discriminate he.
      + intros e c mfix idx stk rs s v rs' s' he. cbn [whnf_fix] in he. discriminate he.
      + intros v stk rs s w rs' s' he. cbn [apply] in he.
        destruct stk; [injection he as <- <- <-; reflexivity|discriminate he].
    - destruct (ih tt) as (IHf & IHs & IHw & IHx & IHa).
      split; [|split; [|split; [|split]]].
      + (* force *)
        intros a0 rs0 s0 v0 rs' s' he.
        cbv beta iota zeta delta [force] in he.
        destruct (heap_get a0 s0) as [cl|] eqn:ehc; [|discriminate he].
        destruct cl as [vs n o c|vd| |b]; try discriminate he.
        * (* a suspension: evaluate it, then write the value back *)
          destruct (heap_upd a0 CBusy s0) as [sb|] eqn:ebusy; [|discriminate he].
          dcall he ew vw rsw sw.
          destruct rsw as [|[ar| | | | | |] rsw]; try discriminate he.
          destruct (heap_upd ar (CDone vw) sw) as [sd|] eqn:edone; [|discriminate he].
          injection he as <- <- <-.
          pose proof (IHw _ _ _ _ _ _ _ _ ew) as h1. sk_fin.
        * (* a value: the heap has it *)
          injection he as <- <- <-. reflexivity.
      + (* eval_slot *)
        intros x stk rs0 s0 v0 rs' s' he.
        cbv beta iota zeta delta [eval_slot] in he.
        destruct x as [a|vs n o c].
        * dcall he ef vf rsf sf.
          destruct rsf as [|[| | | |lk| |] rsf]; try discriminate he.
          pose proof (IHf _ _ _ _ _ _ ef) as h1.
          pose proof (IHa _ _ _ _ _ _ _ he) as h2. sk_fin.
        * exact (IHw _ _ _ _ _ _ _ _ he).
      + (* whnf *)
        intros e c stk rs0 s0 v0 rs' s' he.
        cbv beta iota zeta delta [whnf] in he.
        destruct (tick s0) as [st|] eqn:etick; [|discriminate he].
        destruct (c_term c) as [n|vr|ev earg|srt|na A B|na A b|na b T body|f arg|kn ui
                               |ind ui|ind n ui|ci p scrut brs|pr arg|mfix idx|cmfix cidx|prm]
          eqn:ec; try solve [discriminate he].
        * (* tRel *)
          dcall he ev xr rsr sr.
          destruct rsr as [|[| | | |lk| |] rsr]; try discriminate he.
          pose proof (env_var_skel _ _ _ _ _ _ _ ev) as h1.
          pose proof (IHs _ _ _ _ _ _ _ he) as h2. sk_fin.
        * (* tSort *)
          destruct stk; [|discriminate he]. injection he as <- <- <-. reflexivity.
        * (* tProd *)
          destruct stk; [|discriminate he]. injection he as <- <- <-. reflexivity.
        * (* tLambda *)
          destruct stk as [|xh stk'].
          -- injection he as <- <- <-. reflexivity.
          -- dcall he eb xb rsb sb.
             destruct rsb as [|[| |e1| | | |] [|[| | | |k1| |] rsb]]; try discriminate he.
             pose proof (bind_skel _ _ _ _ _ _ _ eb) as h1.
             pose proof (IHw _ _ _ _ _ _ _ _ he) as h2. sk_fin.
        * (* tLetIn *)
          dcall he ea xa rsa sa.
          destruct rsa as [|[| |e1| | | |] [|[| | | |k1| |] rsa]]; try discriminate he.
          pose proof (arg_slot_skel _ _ _ _ _ _ _ ea) as h1.
          dcall he eb xb rsb sb.
          destruct rsb as [|[| |e2| | | |] [|[| | | |k2| |] rsb]]; try discriminate he.
          pose proof (bind_skel _ _ _ _ _ _ _ eb) as h2.
          pose proof (IHw _ _ _ _ _ _ _ _ he) as h3. sk_fin.
        * (* tApp *)
          dcall he ea xa rsa sa.
          destruct rsa as [|[| |e1| | | |] [|[| | | |k1| |] rsa]]; try discriminate he.
          pose proof (arg_slot_skel _ _ _ _ _ _ _ ea) as h1.
          pose proof (IHw _ _ _ _ _ _ _ _ he) as h2. sk_fin.
        * (* tConst *)
          destruct (delta X_type X kn ui st) as [[r s1]|w] eqn:ed; [|discriminate he].
          destruct r as [c'|].
          -- exact (IHw _ _ _ _ _ _ _ _ he).
          -- dcall he em sp rs1 s2.
             pose proof (mat_all_skel _ _ _ _ _ _ _ em) as h1.
             injection he as <- <- <-. exact h1.
        * (* tInd *)
          dcall he em sp rs1 s1.
          pose proof (mat_all_skel _ _ _ _ _ _ _ em) as h1.
          injection he as <- <- <-. exact h1.
        * (* tConstruct *)
          dcall he em sp rs1 s1.
          pose proof (mat_all_skel _ _ _ _ _ _ _ em) as h1.
          injection he as <- <- <-. exact h1.
        * (* tCase *)
          dcall he ewc vc rsc sc.
          destruct rsc as [|[| |e1| | | |] [|[| | | |k1| |] rsc]]; try discriminate he.
          pose proof (IHw _ _ _ _ _ _ _ _ ewc) as h1.
          destruct vc as [hd sp| | | |nn sp| |]; try discriminate he.
          1: { destruct hd; try discriminate he. dtests he.
               pose proof (IHw _ _ _ _ _ _ _ _ he) as h2. sk_fin. }
          all: dcall he em sp1 rsm sm;
               destruct rsm as [|[| |e5| | | |] rsm]; try discriminate he;
               pose proof (mat_all_skel _ _ _ _ _ _ _ em) as h2;
               injection he as <- <- <-; sk_fin.
        * (* tProj *)
          dcall he ewc vc rsc sc.
          destruct rsc as [|[| |e1| | | |] [|[| | | |k1| |] rsc]]; try discriminate he.
          pose proof (IHw _ _ _ _ _ _ _ _ ewc) as h1.
          destruct vc as [hd sp| | | |nn sp| |]; try discriminate he.
          1: { destruct hd; try discriminate he. dtests he.
               pose proof (IHs _ _ _ _ _ _ _ he) as h2. sk_fin. }
          all: dcall he em sp1 rsm sm;
               destruct rsm as [|[| |e5| | | |] rsm]; try discriminate he;
               pose proof (mat_all_skel _ _ _ _ _ _ _ em) as h2;
               injection he as <- <- <-; sk_fin.
        * (* tFix *)
          exact (IHx _ _ _ _ _ _ _ _ _ _ he).
        * (* tPrim *)
          destruct stk; [|discriminate he]. injection he as <- <- <-. reflexivity.
      + (* whnf_fix *)
        intros e c mfix idx stk rs0 s0 v0 rs' s' he.
        cbv beta iota zeta delta [whnf_fix] in he.
        destruct (nth_error mfix idx) as [def|]; [|discriminate he].
        destruct (nth_error stk (rarg def)) as [x|].
        * dcall he ea a1 rs1 s1.
          destruct rs1 as [|[| |e1| | | |] [|[| | | |k1| |] rs1]]; try discriminate he.
          pose proof (materialize_skel _ _ _ _ _ _ ea) as h1.
          dcall he ef vf rsf sf.
          destruct rsf as [|[| |e2| | | |] [|[| | | |k2| |] rsf]]; try discriminate he.
          pose proof (IHf _ _ _ _ _ _ ef) as h2.
          destruct vf as [hd sp| | | |nn sp| |]; try discriminate he.
          1: { (* the guard holds: the forced constructor goes to a fresh cell *)
               destruct hd; try discriminate he.
               dcall he ea2 a2 rs2 s2.
               destruct rs2 as [|[| |e3| | | |] [|[| | | |k3| |] rs2]]; try discriminate he.
               pose proof (alloc_skel _ _ _ _ _ _ _ ea2) as h3.
               dcall he ep e4 rs3 s3.
               destruct rs3 as [|[| | | |k4| |] rs3]; try discriminate he.
               pose proof (push_fix_cells_skel _ _ _ _ _ _ _ _ _ _ ep) as h4.
               pose proof (IHw _ _ _ _ _ _ _ _ he) as h5. sk_fin. }
          all: dcall he em sp1 rsm sm;
               destruct rsm as [|[| |e5| | | |] rsm]; try discriminate he;
               pose proof (mat_all_skel _ _ _ _ _ _ _ em) as h3;
               injection he as <- <- <-; sk_fin.
        * dcall he em sp rs1 s1.
          destruct rs1 as [|[| |e1| | | |] rs1]; try discriminate he.
          pose proof (mat_all_skel _ _ _ _ _ _ _ em) as h1.
          injection he as <- <- <-. sk_fin.
      + (* apply *)
        intros v stk rs0 s0 w rs' s' he.
        cbv beta iota zeta delta [apply] in he.
        destruct stk as [|y stk']; [injection he as <- <- <-; reflexivity|].
        destruct v as [hd sp|e c|e c idx sp|e c idx sp|nn sp|e c|e c sp]; try discriminate he.
        2: { (* a lambda: beta *)
             destruct (c_term c); try discriminate he.
             dcall he eb xb rsb sb.
             destruct rsb as [|[| |e1| | | |] [|[| | | |k1| |] rsb]]; try discriminate he.
             pose proof (bind_skel _ _ _ _ _ _ _ eb) as h1.
             pose proof (IHw _ _ _ _ _ _ _ _ he) as h2. sk_fin. }
        2: { (* a fixpoint: its spine goes back on the stack *)
             destruct (c_term c); try discriminate he.
             exact (IHx _ _ _ _ _ _ _ _ _ _ he). }
        all: (* the spine grows *)
             dcall he em sp1 rsm sm;
             destruct rsm as [|[| | |v1| | |] rsm]; try discriminate he;
             pose proof (mat_all_skel _ _ _ _ _ _ _ em) as h1;
             destruct (add_spine v1 sp1) as [v2|] eqn:eadd; [|discriminate he];
             injection he as <- <- <-; sk_fin.
  Qed.
End SkMachine.

Lemma machine_skel {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1)
    (Γ : context) (nctx : nat) (stress : bool) : forall d,
  (forall a rs s v rs' s', force X_type X Γ nctx stress d a rs s = COk (v, rs', s') ->
     mp_roots kc rs' = mp_roots kc rs)
  /\ (forall x stk rs s v rs' s', eval_slot X_type X Γ nctx stress d x stk rs s = COk (v, rs', s') ->
     mp_roots kc rs' = mp_roots kc rs)
  /\ (forall e c stk rs s v rs' s', whnf X_type X Γ nctx stress d e c stk rs s = COk (v, rs', s') ->
     mp_roots kc rs' = mp_roots kc rs)
  /\ (forall e c mfix idx stk rs s v rs' s',
       whnf_fix X_type X Γ nctx stress d e c mfix idx stk rs s = COk (v, rs', s') ->
     mp_roots kc rs' = mp_roots kc rs)
  /\ (forall v stk rs s w rs' s', apply X_type X Γ nctx stress d v stk rs s = COk (w, rs', s') ->
     mp_roots kc rs' = mp_roots kc rs).
Proof. exact (sk_machine X_type X Γ nctx stress). Qed.


(** * The comparison on ghost readings (BET-298, step 3b)

  The seams above ([slot_seam], [term_seam]) read the comparison's inputs with the
  heap-following [repr_*] and are false ([PCUICCallByNeedSoundHookFrame.term_seam_false]).
  This part states the comparison against the ghost reading of [machine_sound]
  ([PCUICCallByNeedSoundEval]) at the master level of [PCUICCallByNeedSoundLevel]: the state
  satisfies [minv L Q], where [L <= Q] is the comparison's logical level and [Q] the level of
  the ghost.

  Every function [f] of the comparison gets a statement [spec_f d], made of two parts.
  - The state part ([post]): from [minv L Q lo G s] and readings of the inputs under [G] at
    [Q], an answer [COk (b, rs', s')] comes with a master level [Q' >= Q] and a ghost [G'] such
    that [minv L Q' lo' G' s'] holds and every root of the caller keeps its reading, lifted by
    [Q' - Q] ([grq]). The master level rises when the comparison crosses binders: a fresh
    variable at level [L] must be below [Q] ([hwf]), and [gok_raise] lifts the ghost.
  - The conversion part ([cq]): if [b = true], whenever each of the two readings is the lift
    by [Q - L] of a term scoped at [L], those two terms are convertible at the comparison's
    [conv_pb] in [Γ ,,, Δ] for every [Δ] of length [L - nctx]. Nothing is said of [false].
  The lifts are a premise of the conversion part, not of the call: the state part needs
  nothing of the readings beyond their existence. That matters for [same_code_cells], which
  compares environment slots whose readings are lifts only where the code uses them. *)

Section ConvGhost.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat) (stress : bool) (Σ : global_env_ext).
  Context (wfΣ : wf Σ) (hΣ : abstract_env_ext_rel X Σ).
  Context (hnctx : nctx = #|Γ|) (hΓ : is_closed_context Γ) (hhyg : ctx_hyg Γ).
  Context (hcio : forall j decl b, nth_error Γ j = Some decl -> decl.(decl_body) = Some b ->
                    PCUICCallByNeedSoundHook.consts_okb Σ b).

  Local Notation xpred0 := (fun _ : nat => false) (only parsing).
  Local Notation xpredT := (fun _ : nat => true) (only parsing).
  Local Notation gcok := PCUICCallByNeedSoundEval.cok.
  Local Notation MI := (minv X_type X Γ nctx Σ).

  (** ** Lifts *)

  Lemma lift0_lift0 (a b : nat) (t : term) : lift0 a (lift0 b t) = lift0 (a + b) t.
  Proof. apply simpl_lift; lia. Qed.

  Lemma map_lift0_lift0 (a b : nat) (ts : list term) :
    map (lift0 a) (map (lift0 b) ts) = map (lift0 (a + b)) ts.
  Proof. rewrite map_map. apply map_ext. intros t. apply lift0_lift0. Qed.

  Lemma map_lift0_0 (ts : list term) : map (lift0 0) ts = ts.
  Proof. induction ts as [|t ts ih]; cbn; [reflexivity|]. rewrite lift0_id, ih. reflexivity. Qed.

  Lemma rn_comp (f g : nat -> nat) (t : term) :
    rename f (rename g t) = rename (fun i => f (g i)) t.
  Proof. exact (rename_compose f g t). Qed.

  Lemma rn_id (t : term) : rename ren_id t = t.
  Proof. exact (rename_ren_id t). Qed.

  (** [unl m] undoes a lift by [m]. *)
  Definition unl (m : nat) (t : term) : term := rename (fun i => i - m) t.

  Lemma unl_lift0 (m : nat) (u : term) : unl m (lift0 m u) = u.
  Proof.
    unfold unl. rewrite lift_rename, rn_comp.
    transitivity (rename ren_id u); [|apply rn_id].
    apply rename_ext. intros i. unfold lift_renaming, ren_id. cbn. lia.
  Qed.

  Lemma lift0_inj (m : nat) (a b : term) : lift0 m a = lift0 m b -> a = b.
  Proof. intros h. rewrite <- (unl_lift0 m a), <- (unl_lift0 m b), h. reflexivity. Qed.

  (** [scl L u]: [u] is scoped at level [L], so open in [Γ ,,, Δ] when [#|Δ| = L - nctx].
    [inq m Q]: the free variables of the lift by [m] of a term scoped at [Q - m]. *)
  Definition scl (L : nat) (u : term) : bool := on_free_vars (shiftnP L xpred0) u.

  Definition inq (m Q : nat) (i : nat) : bool := (m <=? i) && (i <? Q).

  Lemma inq_lift0 (m L : nat) (u : term) : scl L u -> on_free_vars (inq m (L + m)) (lift0 m u).
  Proof.
    unfold scl. intros h. rewrite lift_rename, PCUICOnFreeVarsConv.on_free_vars_rename.
    eapply on_free_vars_impl; [|exact h].
    intros i hi. unfold shiftnP in hi. cbv beta. unfold inq, lift_renaming. cbn.
    destruct (Nat.ltb_spec i L) as [hl|hl]; cbn in hi; [|discriminate hi].
    apply andb_true_iff. split; [apply Nat.leb_le; lia|apply Nat.ltb_lt; lia].
  Qed.

  Lemma inq_unl (m Q : nat) (t : term) :
    on_free_vars (inq m Q) t -> t = lift0 m (unl m t) /\ scl (Q - m) (unl m t).
  Proof.
    intros h. split.
    - unfold unl. rewrite lift_rename, rn_comp.
      transitivity (rename ren_id t); [symmetry; apply rn_id|].
      apply (PCUICOnFreeVarsConv.rename_ext_cond (inq m Q)); [|exact h].
      intros i hi. unfold inq in hi. apply andb_true_iff in hi as [h1 _].
      apply Nat.leb_le in h1. unfold lift_renaming, ren_id. cbn. lia.
    - unfold unl, scl. rewrite PCUICOnFreeVarsConv.on_free_vars_rename.
      eapply on_free_vars_impl; [|exact h].
      intros i hi. unfold inq in hi. apply andb_true_iff in hi as [h1 h2].
      apply Nat.leb_le in h1. apply Nat.ltb_lt in h2. unfold shiftnP. cbv beta.
      destruct (Nat.ltb_spec (i - m) (Q - m)); [reflexivity|lia].
  Qed.

  (** ** What a [true] claims *)

  Definition cv (L : nat) (pb : conv_pb) (u1 u2 : term) : Prop :=
    forall Δ : context, #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) ->
      ∥ Σ ;;; Γ ,,, Δ ⊢ u1 ≤[pb] u2 ∥.

  Definition cq (L Q : nat) (pb : conv_pb) (t1 t2 : term) : Prop :=
    forall u1 u2 : term, t1 = lift0 (Q - L) u1 -> t2 = lift0 (Q - L) u2 ->
      scl L u1 -> scl L u2 -> cv L pb u1 u2.

  Definition cvs (L : nat) (us1 us2 : list term) : Prop :=
    forall Δ : context, #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) ->
      ∥ ws_cumul_pb_terms Σ (Γ ,,, Δ) us1 us2 ∥.

  Definition cqs (L Q : nat) (ts1 ts2 : list term) : Prop :=
    forall us1 us2 : list term,
      ts1 = map (lift0 (Q - L)) us1 -> ts2 = map (lift0 (Q - L)) us2 ->
      forallb (scl L) us1 -> forallb (scl L) us2 -> cvs L us1 us2.

  Lemma scl_open (L : nat) (Δ : context) (u : term) :
    nctx <= L -> #|Δ| = L - nctx -> scl L u -> is_open_term (Γ ,,, Δ) u.
  Proof.
    intros hL hΔ h. rewrite app_context_length, hΔ, <- hnctx.
    replace (L - nctx + nctx) with L by lia. exact h.
  Qed.

  Lemma cq_refl (L Q : nat) (pb : conv_pb) (t : term) : nctx <= L -> cq L Q pb t t.
  Proof.
    intros hL u1 u2 e1 e2 h1 h2 Δ hΔ hcl. rewrite e1 in e2. apply lift0_inj in e2. subst u2.
    constructor. apply ws_cumul_pb_refl; [exact hcl|exact (scl_open L Δ u1 hL hΔ h1)].
  Qed.

  Lemma cq_lift (L Q Q' : nat) (pb : conv_pb) (t1 t2 : term) :
    L <= Q -> Q <= Q' ->
    cq L Q' pb (lift0 (Q' - Q) t1) (lift0 (Q' - Q) t2) -> cq L Q pb t1 t2.
  Proof.
    intros hLQ hQ h u1 u2 e1 e2 h1 h2. apply h; [| |exact h1|exact h2].
    - rewrite e1, lift0_lift0. f_equal. lia.
    - rewrite e2, lift0_lift0. f_equal. lia.
  Qed.

  Lemma cqs_lift (L Q Q' : nat) (ts1 ts2 : list term) :
    L <= Q -> Q <= Q' ->
    cqs L Q' (map (lift0 (Q' - Q)) ts1) (map (lift0 (Q' - Q)) ts2) -> cqs L Q ts1 ts2.
  Proof.
    intros hLQ hQ h us1 us2 e1 e2 h1 h2. apply h; [| |exact h1|exact h2].
    - rewrite e1, map_lift0_lift0. f_equal. f_equal. lia.
    - rewrite e2, map_lift0_lift0. f_equal. f_equal. lia.
  Qed.

  (** ** The caller's roots across a call that may raise the master level *)

  Definition gpq (Q Q' : nat) (G G' : ghost) (r r' : root) : Prop :=
    match r, r' with
    | RA a, RA a' => forall t, G a = Some t -> G' a' = Some (lift0 (Q' - Q) t)
    | RSl x, RSl x' =>
      forall t, g_slot nctx Q G x t -> g_slot nctx Q' G' x' (lift0 (Q' - Q) t)
    | RE e, RE e' =>
      e'.(ev_nvals) = e.(ev_nvals) /\ e'.(ev_goff) = e.(ev_goff)
      /\ forall ts, g_slots nctx Q G e.(ev_vals) ts ->
           g_slots nctx Q' G' e'.(ev_vals) (map (lift0 (Q' - Q)) ts)
    | RV v, RV v' =>
      forall t, g_value nctx Q G v t -> g_value nctx Q' G' v' (lift0 (Q' - Q) t)
    | RSk l, RSk l' =>
      forall ts, g_slots nctx Q G l ts -> g_slots nctx Q' G' l' (map (lift0 (Q' - Q)) ts)
    | RSp l, RSp l' => forall ts, g_addrs G l ts -> g_addrs G' l' (map (lift0 (Q' - Q)) ts)
    | RC cl, RC cl' =>
      forall t, g_cell nctx Q G cl t -> g_cell nctx Q' G' cl' (lift0 (Q' - Q) t)
    | _, _ => False
    end.

  (** Every root keeps its reading, lifted by [Q' - Q], and its shape ([machine_skel]): only
    its addresses change. *)
  Definition grq (Q Q' : nat) (G G' : ghost) (rs rs' : list root) : Prop :=
    gcx G G' /\ Forall2 (gpq Q Q' G G') rs rs' /\ mp_roots kc rs' = mp_roots kc rs.

  Lemma gpq_of_gpres Q G G' r r' : gpres nctx Q G G' r r' -> gpq Q Q G G' r r'.
  Proof.
    intros h. destruct r, r'; cbn in h |- *; try contradiction; rewrite Nat.sub_diag.
    all: first
      [ intros t ht; rewrite lift0_id; exact (h _ ht)
      | intros ts ht; rewrite map_lift0_0; exact (h _ ht)
      | destruct h as (a1 & b1 & c1); split; [exact a1|]; split; [exact b1|];
        intros ts ht; rewrite map_lift0_0; exact (c1 _ ht) ].
  Qed.

  Lemma grq_of_gren Q G G' rs rs' :
    gren nctx Q G G' rs rs' -> mp_roots kc rs' = mp_roots kc rs -> grq Q Q G G' rs rs'.
  Proof.
    intros [hc hf] hk. split; [exact hc|]. split; [|exact hk]. clear hk.
    induction hf; constructor; [apply gpq_of_gpres; assumption|assumption].
  Qed.

  Lemma grq_refl Q G rs : grq Q Q G G rs rs.
  Proof. apply grq_of_gren; [apply gren_refl|reflexivity]. Qed.

  Lemma gpq_trans Q Q1 Q2 G G1 G2 r r1 r2 :
    Q <= Q1 -> Q1 <= Q2 ->
    gpq Q Q1 G G1 r r1 -> gpq Q1 Q2 G1 G2 r1 r2 -> gpq Q Q2 G G2 r r2.
  Proof.
    intros hq1 hq2 h1 h2.
    assert (e : Q2 - Q = (Q2 - Q1) + (Q1 - Q)) by lia.
    destruct r, r1; cbn in h1; try contradiction; destruct r2; cbn in h2 |- *;
      try contradiction; rewrite e.
    all: first
      [ intros t ht; rewrite <- lift0_lift0; exact (h2 _ (h1 _ ht))
      | intros ts ht; rewrite <- map_lift0_lift0; exact (h2 _ (h1 _ ht))
      | destruct h1 as (a1 & b1 & c1), h2 as (a2 & b2 & c2);
        split; [congruence|]; split; [congruence|];
        intros ts ht; rewrite <- map_lift0_lift0; exact (c2 _ (c1 _ ht)) ].
  Qed.

  Lemma grq_trans Q Q1 Q2 G G1 G2 rs rs1 rs2 :
    Q <= Q1 -> Q1 <= Q2 ->
    grq Q Q1 G G1 rs rs1 -> grq Q1 Q2 G1 G2 rs1 rs2 -> grq Q Q2 G G2 rs rs2.
  Proof.
    intros hq1 hq2 [hc1 [hf1 hk1]] [hc2 [hf2 hk2]].
    split; [intros i e hi; exact (hc2 _ _ (hc1 _ _ hi))|].
    split; [|congruence].
    clear hk1 hk2.
    revert rs2 hf2. induction hf1 as [|r r1 l l1 hp hf ih]; intros rs2 hf2;
      inversion hf2; subst; constructor.
    - eapply gpq_trans; eassumption.
    - apply ih. assumption.
  Qed.

  Lemma grq_cons_inv_skel Q Q' G G' r rs rs1 :
    grq Q Q' G G' (r :: rs) rs1 ->
    exists r' rs', rs1 = r' :: rs' /\ gpq Q Q' G G' r r' /\ grq Q Q' G G' rs rs'
      /\ mp_root kc r' = mp_root kc r.
  Proof.
    intros [hc [hf hk]]. destruct rs1 as [|r' rs']; [inversion hf|].
    exists r', rs'. split; [reflexivity|]. cbn in hk. injection hk as hk1 hk2.
    inversion hf; subst. split; [assumption|]. split; [|exact hk1].
    split; [exact hc|split; assumption].
  Qed.

  Lemma grq_cons_inv Q Q' G G' r rs rs1 :
    grq Q Q' G G' (r :: rs) rs1 ->
    exists r' rs', rs1 = r' :: rs' /\ gpq Q Q' G G' r r' /\ grq Q Q' G G' rs rs'.
  Proof.
    intros h. destruct (grq_cons_inv_skel _ _ _ _ _ _ _ h) as (r' & rs' & e & h1 & h2 & _).
    exists r', rs'. split; [exact e|split; assumption].
  Qed.

  Lemma gpq_RSk_inv Q Q' G G' l r :
    gpq Q Q' G G' (RSk l) r ->
    exists l', r = RSk l'
      /\ forall ts, g_slots nctx Q G l ts -> g_slots nctx Q' G' l' (map (lift0 (Q' - Q)) ts).
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  Lemma gpq_RSp_inv Q Q' G G' l r :
    gpq Q Q' G G' (RSp l) r ->
    exists l', r = RSp l' /\ forall ts, g_addrs G l ts -> g_addrs G' l' (map (lift0 (Q' - Q)) ts).
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  Lemma gpq_RSl_inv Q Q' G G' x r :
    gpq Q Q' G G' (RSl x) r ->
    exists x', r = RSl x'
      /\ forall t, g_slot nctx Q G x t -> g_slot nctx Q' G' x' (lift0 (Q' - Q) t).
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  Lemma gpq_RV_inv Q Q' G G' v r :
    gpq Q Q' G G' (RV v) r ->
    exists v', r = RV v'
      /\ forall t, g_value nctx Q G v t -> g_value nctx Q' G' v' (lift0 (Q' - Q) t).
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  Lemma gpq_RE_inv Q Q' G G' e r :
    gpq Q Q' G G' (RE e) r ->
    exists e', r = RE e' /\ e'.(ev_nvals) = e.(ev_nvals) /\ e'.(ev_goff) = e.(ev_goff)
      /\ forall ts, g_slots nctx Q G e.(ev_vals) ts ->
           g_slots nctx Q' G' e'.(ev_vals) (map (lift0 (Q' - Q)) ts).
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  (** ** Raising the master level *)

  Lemma rwf_mono Q Q' r : Q <= Q' -> rwf Q r -> rwf Q' r.
  Proof.
    intros h. destruct r; cbn; intros hw; try exact I;
      [exact (vwf_mono _ _ _ h hw)|exact (cwf_mono _ _ _ h hw)].
  Qed.

  Lemma rwfs_mono Q Q' rs : Q <= Q' -> Forall (rwf Q) rs -> Forall (rwf Q') rs.
  Proof.
    intros h hr. induction hr as [|r rs hr0 _ ih]; constructor; [|exact ih].
    exact (rwf_mono _ _ _ h hr0).
  Qed.

  Lemma gpq_raise Q n G r : nctx <= Q -> rwf Q r -> gpq Q (Q + n) G (gshift n G) r r.
  Proof.
    intros hQ hw. unfold gpq. replace (Q + n - Q) with n by lia.
    destruct r; cbn in hw.
    - intros t ht. cbn. rewrite ht. reflexivity.
    - intros t ht. exact (proj1 (g_slot_shift nctx Q n hQ G) _ _ ht).
    - split; [reflexivity|]. split; [reflexivity|].
      intros ts ht. exact (proj1 (proj2 (g_slot_shift nctx Q n hQ G) _ _ ht)).
    - intros t ht. exact (g_value_shift nctx Q n hQ G _ _ hw ht).
    - intros ts ht. exact (proj1 (proj2 (g_slot_shift nctx Q n hQ G) _ _ ht)).
    - intros ts ht. apply g_addrs_shift. exact ht.
    - intros t ht. eapply g_cell_shift; eassumption.
  Qed.

  Lemma grq_raise Q n G rs : nctx <= Q -> Forall (rwf Q) rs -> grq Q (Q + n) G (gshift n G) rs rs.
  Proof.
    intros hQ hw. split; [intros i e hi; exact hi|]. split; [|reflexivity].
    induction hw; constructor; [apply gpq_raise; assumption|assumption].
  Qed.

  Lemma minv_raise L Q n lo G s : MI L Q lo G s -> MI L (Q + n) lo (gshift n G) s.
  Proof.
    intros [hL hQ hok hw].
    constructor; [exact hL|lia| |exact (hwf_mono Q (Q + n) s ltac:(lia) hw)].
    exact (gok_raise X_type X Γ nctx Σ wfΣ hnctx hΓ hhyg Q n lo G s ltac:(lia) hw hok).
  Qed.

  (** ** The state part of every statement *)

  Definition post (L Q : nat) (G : ghost) (rs : list root) (s' : cbn_state) (rs' : list root)
    : Prop :=
    exists Q' lo' G', Q <= Q' /\ MI L Q' lo' G' s' /\ Forall (rwf Q') rs'
      /\ grq Q Q' G G' rs rs'.

  Lemma post_refl L Q lo G rs s : MI L Q lo G s -> Forall (rwf Q) rs -> post L Q G rs s rs.
  Proof.
    intros hm hr. exists Q, lo, G. split; [lia|]. split; [exact hm|].
    split; [exact hr|apply grq_refl].
  Qed.

  Lemma post_compose L Q Q1 G G1 rs rs1 s' rs' :
    Q <= Q1 -> grq Q Q1 G G1 rs rs1 -> post L Q1 G1 rs1 s' rs' -> post L Q G rs s' rs'.
  Proof.
    intros hq hg (Q2 & lo2 & G2 & hq2 & hm & hr & hg2). exists Q2, lo2, G2.
    split; [lia|]. split; [exact hm|]. split; [exact hr|]. eapply grq_trans; eassumption.
  Qed.

  (** A sub-call answered [false]: the caller drops the two roots it pushed. *)
  Lemma post_drop2 L Q G r1 r2 rs s' rs' :
    post L Q G (r1 :: r2 :: rs) s' rs' -> post L Q G rs s' (skipn 2 rs').
  Proof.
    intros (Q1 & lo1 & G1 & hq & hm & hr & hg).
    destruct (grq_cons_inv _ _ _ _ _ _ _ hg) as (q1 & rsA & -> & _ & hgA).
    destruct (grq_cons_inv _ _ _ _ _ _ _ hgA) as (q2 & rsB & -> & _ & hgB).
    exists Q1, lo1, G1. split; [exact hq|]. split; [exact hm|]. cbn [skipn].
    split; [exact (Forall_inv_tail (Forall_inv_tail hr))|exact hgB].
  Qed.

  (** ** The same-code rule, cell by cell

    [cagree L Q a i ts1 ts2]: at each position of the two slot lists, either the code [a]
    does not use the slot, or the two readings are convertible in the sense of [cq]. *)
  Inductive cagree (L Q : nat) (a : term) : nat -> list term -> list term -> Prop :=
  | cagree_nil i : cagree L Q a i [] []
  | cagree_cons i u1 u2 l1 l2 :
      (noccur_between i 1 a = true \/ cq L Q Conv u1 u2) ->
      cagree L Q a (S i) l1 l2 -> cagree L Q a i (u1 :: l1) (u2 :: l2).

  Lemma cagree_lift L Q Q' a i l1 l2 :
    L <= Q -> Q <= Q' ->
    cagree L Q' a i (map (lift0 (Q' - Q)) l1) (map (lift0 (Q' - Q)) l2) -> cagree L Q a i l1 l2.
  Proof.
    intros hL hQ. revert i l2. induction l1 as [|u1 l1 ih]; intros i [|u2 l2] h; cbn in h;
      inversion h as [i0|i0 v1 v2 m1 m2 hd hl]; subst.
    - constructor.
    - constructor; [|exact (ih _ _ hl)].
      destruct hd as [hd|hd]; [left; exact hd|right; exact (cq_lift _ _ _ _ _ _ hL hQ hd)].
  Qed.

  Definition spec_slot (d : cbn_fuel) : Prop :=
    forall L Q lo G pb x1 x2 t1 t2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs ->
      g_slot nctx Q G x1 t1 -> g_slot nctx Q G x2 t2 ->
      conv_slot X_type X Γ nctx stress d L pb x1 x2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cq L Q pb t1 t2).

  Definition spec_scc (d : cbn_fuel) : Prop :=
    forall L Q lo G a i l1 l2 ts1 ts2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs ->
      g_slots nctx Q G l1 ts1 -> g_slots nctx Q G l2 ts2 ->
      same_code_cells X_type X Γ nctx stress d L a i l1 l2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cagree L Q a i ts1 ts2).

  (** [same_code_cells] skips a position whose two slots are one address (one reading) or
    whose slot the code does not use, and compares every other position with [conv_slot].
    Restates [same_code_cells_sound] on ghost readings. *)
  Lemma same_code_cells_sound_g (k : unit -> cbn_fuel) :
    spec_slot (k tt) -> spec_scc (k tt) -> spec_scc (FS k).
  Proof.
    intros hS hC L Q lo G a i l1 l2 ts1 ts2 rs s b rs' s' hm hr hl1 hl2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite same_code_cells_eq in he.
    destruct l1 as [|x1 l1]; destruct l2 as [|x2 l2].
    - injection he as <- <- <-. inversion hl1; subst. inversion hl2; subst.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros _. constructor.
    - injection he as <- <- <-.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - injection he as <- <- <-.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - inversion hl1 as [|y1 m1 u1 us1 hx1 hm1]; subst.
      inversion hl2 as [|y2 m2 u2 us2 hx2 hm2]; subst.
      destruct (slot_same x1 x2 || noccur_between i 1 a) eqn:Esk.
      + destruct (hC L Q lo G a (S i) l1 l2 us1 us2 rs s b rs' s' hm hr hm1 hm2 he)
          as [hp hc].
        split; [exact hp|]. intros hb. constructor; [|exact (hc hb)].
        apply orb_true_iff in Esk as [Esame|Enocc]; [right|left; exact Enocc].
        destruct x1 as [a1|]; destruct x2 as [a2|]; cbn in Esame; try discriminate Esame.
        apply haddr_eqb_eq in Esame. subst a2.
        apply g_slot_addr_inv in hx1. apply g_slot_addr_inv in hx2.
        rewrite hx1 in hx2. injection hx2 as <-. exact (cq_refl _ _ _ _ hL).
      + destruct (conv_slot X_type X Γ nctx stress (k tt) L Conv x1 x2
                    (RSk l1 :: RSk l2 :: rs) s) as [[[b2 rs2] s2]|w] eqn:Ecs;
          [|discriminate he].
        assert (hr' : Forall (rwf Q) (RSk l1 :: RSk l2 :: rs))
          by (constructor; [exact I|constructor; [exact I|exact hr]]).
        destruct (hS L Q lo G Conv x1 x2 u1 u2 _ s b2 rs2 s2 hm hr' hx1 hx2 Ecs)
          as [hp1 hc1].
        destruct b2.
        * destruct hp1 as (Q1 & lo1 & G1 & hq1 & hm1' & hr1 & hg1).
          destruct (grq_cons_inv _ _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hqa & hgA).
          destruct (gpq_RSk_inv _ _ _ _ _ _ hqa) as (l1' & -> & hk1).
          destruct (grq_cons_inv _ _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hqb & hgB).
          destruct (gpq_RSk_inv _ _ _ _ _ _ hqb) as (l2' & -> & hk2).
          cbv beta iota in he.
          destruct (hC L Q1 lo1 G1 a (S i) l1' l2' _ _ rsB s2 b rs' s' hm1'
                      (Forall_inv_tail (Forall_inv_tail hr1)) (hk1 _ hm1) (hk2 _ hm2) he)
            as [hp hc].
          split; [exact (post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
          intros hb. constructor; [right; exact (hc1 eq_refl)|].
          exact (cagree_lift _ _ _ _ _ _ _ hLQ hq1 (hc hb)).
        * cbv beta iota in he. injection he as <- <- <-.
          split; [exact (post_drop2 _ _ _ _ _ _ _ _ hp1)|]. intros hb; discriminate hb.
  Qed.

  (** ** The statements of the other functions *)

  Definition spec_eval (d : cbn_fuel) : Prop :=
    forall L Q lo G pb x1 x2 t1 t2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs ->
      g_slot nctx Q G x1 t1 -> g_slot nctx Q G x2 t2 ->
      conv_eval X_type X Γ nctx stress d L pb x1 x2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cq L Q pb t1 t2).

  Definition spec_cells (d : cbn_fuel) : Prop :=
    forall L Q lo G l1 l2 ts1 ts2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs ->
      g_addrs G l1 ts1 -> g_addrs G l2 ts2 ->
      conv_cells X_type X Γ nctx stress d L l1 l2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cqs L Q ts1 ts2).

  Definition spec_term (d : cbn_fuel) : Prop :=
    forall L Q lo G pb e1 c1 e2 c2 t1 t2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs ->
      g_susp nctx Q G e1 c1.(c_term) t1 -> gcok G c1 ->
      g_susp nctx Q G e2 c2.(c_term) t2 -> gcok G c2 ->
      conv_term X_type X Γ nctx stress d L pb e1 c1 e2 c2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cq L Q pb t1 t2).

  (** Two codes [code_eq] accepts: one term, or equal up to universes at [Conv]. *)
  Definition samec (a1 a2 : term) : Prop := a1 = a2 \/ ∥ compare_term Σ Σ Conv a1 a2 ∥.

  (** [conv_same_code] answers [true] with the facts the same-code rule rests on; the
    conversion of the two readings follows from them ([same_code_cq] below). *)
  Definition spec_same (d : cbn_fuel) : Prop :=
    forall L Q lo G e1 c1 e2 c2 ts1 ts2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs -> gcok G c1 -> gcok G c2 ->
      g_slots nctx Q G e1.(ev_vals) ts1 -> g_slots nctx Q G e2.(ev_vals) ts2 ->
      conv_same_code X_type X Γ nctx stress d L e1 c1 e2 c2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\
      (b = true -> e1.(ev_goff) = e2.(ev_goff) /\ e1.(ev_nvals) = e2.(ev_nvals)
                   /\ samec c1.(c_term) c2.(c_term) /\ cagree L Q c1.(c_term) 0 ts1 ts2).

  Definition spec_case (d : cbn_fuel) : Prop :=
    forall L Q lo G pb e1 c1 e2 c2 t1 t2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs ->
      g_susp nctx Q G e1 c1.(c_term) t1 -> gcok G c1 ->
      g_susp nctx Q G e2 c2.(c_term) t2 -> gcok G c2 ->
      case_cong X_type X Γ nctx stress d L e1 c1 e2 c2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cq L Q pb t1 t2).

  (** The parameter codes [case_params] walks: child [case_param_step i] onwards. *)
  Inductive pcodes (G : ghost) (c : code) : N -> list term -> Prop :=
  | pcodes_nil i : pcodes G c i []
  | pcodes_cons i t l :
      gcok G (child c (case_param_step i) t) -> pcodes G c (N.succ i) l ->
      pcodes G c i (t :: l).

  Definition spec_params (d : cbn_fuel) : Prop :=
    forall L Q lo G e1 c1 e2 c2 i l1 l2 us1 us2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs ->
      pcodes G c1 i l1 -> pcodes G c2 i l2 ->
      Forall2 (g_susp nctx Q G e1) l1 us1 -> Forall2 (g_susp nctx Q G e2) l2 us2 ->
      case_params X_type X Γ nctx stress d L e1 c1 e2 c2 i l1 l2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cqs L Q us1 us2).

  (** A branch body read at [Q] through slots [ts], under its own [#|bcontext|] binders, and
    what a [true] claims of two of them: the lifts by [Q - L] at the cut [#|bcontext|] of two
    terms scoped at [L + #|bcontext|] are convertible. *)
  Definition rbody (ts : list term) (N : nat) (br : branch term) : term :=
    subst ts #|br.(bcontext)| (lift N (#|br.(bcontext)| + #|ts|) br.(bbody)).

  Definition cqb (L Q k : nat) (pb : conv_pb) (B1 B2 : term) : Prop :=
    forall U1 U2 : term, B1 = lift (Q - L) k U1 -> B2 = lift (Q - L) k U2 ->
      scl (L + k) U1 -> scl (L + k) U2 -> cv (L + k) pb U1 U2.

  Inductive bcodes (G : ghost) (c : code) : N -> list (branch term) -> Prop :=
  | bcodes_nil i : bcodes G c i []
  | bcodes_cons i br l :
      gcok G (child c (case_branch_step i) br.(bbody)) -> bcodes G c (N.succ i) l ->
      bcodes G c i (br :: l).

  Definition spec_branches (d : cbn_fuel) : Prop :=
    forall L Q lo G e1 c1 e2 c2 i l1 l2 ts1 ts2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs ->
      bcodes G c1 i l1 -> bcodes G c2 i l2 ->
      g_slots nctx Q G e1.(ev_vals) ts1 -> e1.(ev_nvals) = #|e1.(ev_vals)| ->
      g_slots nctx Q G e2.(ev_vals) ts2 -> e2.(ev_nvals) = #|e2.(ev_vals)| ->
      case_branches X_type X Γ nctx stress d L e1 c1 e2 c2 i l1 l2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\
      (b = true -> Forall2 (fun br1 br2 =>
          case_ctx_ok br1.(bcontext) br2.(bcontext) = true
          /\ cqb L Q #|br1.(bcontext)| Conv (rbody ts1 (Q - nctx + e1.(ev_goff)) br1)
                 (rbody ts2 (Q - nctx + e2.(ev_goff)) br2)) l1 l2).

  Definition spec_rows_on (d : cbn_fuel) (R : cbn_value -> cbn_value -> Prop) : Prop :=
    forall L Q lo G pb v1 v2 w1 w2 rs s b rs' s',
      R v1 v2 -> MI L Q lo G s -> Forall (rwf Q) rs -> vwf Q v1 -> vwf Q v2 ->
      g_value nctx Q G v1 w1 -> g_value nctx Q G v2 w2 ->
      conv_rows X_type X Γ nctx stress d L pb v1 v2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cq L Q pb w1 w2).

  Definition spec_rows (d : cbn_fuel) : Prop := spec_rows_on d (fun _ _ => True).

  Definition spec_value (d : cbn_fuel) : Prop :=
    forall L Q lo G pb v1 v2 w1 w2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs -> vwf Q v1 -> vwf Q v2 ->
      g_value nctx Q G v1 w1 -> g_value nctx Q G v2 w2 ->
      conv_value X_type X Γ nctx stress d L pb v1 v2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cq L Q pb w1 w2).

  (** All eleven functions at one fuel: the induction hypothesis of the comparison. *)
  Definition spec_all (d : cbn_fuel) : Prop :=
    spec_slot d /\ spec_eval d /\ spec_cells d /\ spec_term d /\ spec_same d /\ spec_scc d
    /\ spec_case d /\ spec_params d /\ spec_branches d /\ spec_rows d /\ spec_value d.

  (** The base case of the induction: at [FO] every function of the comparison answers
    [CFail WDepth]. This is not evidence that the statements say anything; see the witness
    lemmas for that. *)
  Lemma spec_all_FO : spec_all FO.
  Proof.
    repeat split; repeat intro;
      match goal with h : _ = COk _ |- _ => cbn in h; discriminate h end.
  Qed.

  (** ** Helpers for the step lemmas *)

  Lemma post_level L L' Q G rs s' rs' :
    nctx <= L -> L <= L' -> post L' Q G rs s' rs' -> post L Q G rs s' rs'.
  Proof.
    intros h1 h2 (Q' & lo' & G' & hq & [hL hLQ hok hw] & hr & hg).
    exists Q', lo', G'. split; [exact hq|]. split; [constructor; [exact h1|lia|exact hok|exact hw]|].
    split; assumption.
  Qed.

  Lemma gren_cons_inv Q G G' r rs rs1 :
    gren nctx Q G G' (r :: rs) rs1 ->
    exists r' rs', rs1 = r' :: rs' /\ gpres nctx Q G G' r r' /\ gren nctx Q G G' rs rs'.
  Proof.
    intros [hc hf]. destruct rs1 as [|r' rs']; [inversion hf|].
    exists r', rs'. split; [reflexivity|].
    inversion hf; subst. split; [assumption|split; assumption].
  Qed.

  Lemma gpres_RE_inv Q G G' e r :
    gpres nctx Q G G' (RE e) r -> exists e', r = RE e' /\ genv nctx Q G G' e e'.
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  Lemma gpres_RV_inv Q G G' v r :
    gpres nctx Q G G' (RV v) r ->
    exists v', r = RV v' /\ forall t, g_value nctx Q G v t -> g_value nctx Q G' v' t.
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  Lemma gpres_RSl_inv Q G G' x r :
    gpres nctx Q G G' (RSl x) r ->
    exists x', r = RSl x' /\ forall t, g_slot nctx Q G x t -> g_slot nctx Q G' x' t.
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  Lemma ctx_closed_jctx n : is_closed_context (Γ ,,, jctx n).
  Proof. rewrite on_free_vars_ctx_app, hΓ. apply jctx_closed. Qed.

  Lemma red_scl L Δ v u :
    nctx <= L -> #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) -> scl L v ->
    PCUICReduction.red Σ (Γ ,,, Δ) v u -> scl L u.
  Proof.
    intros hL hΔ hcl hv hr. unfold scl in *.
    assert (e : #|Γ ,,, Δ| = L) by (rewrite app_context_length, hΔ, <- hnctx; lia).
    assert (hc : on_ctx_free_vars (shiftnP L xpred0) (Γ ,,, Δ)).
    { rewrite <- e, on_free_vars_ctx_on_ctx_free_vars. exact hcl. }
    exact (PCUICRenameConv.red_on_free_vars (wfΣ := wfΣ) hc hv hr).
  Qed.

  Lemma scl_hyg L u : scl L u -> on_free_vars xpredT u.
  Proof. intros h. eapply on_free_vars_impl; [|exact h]. intros; reflexivity. Qed.

  (** The readings of the inputs reduce, at the master level, to the readings of their values:
    a [true] about the values is a [true] about the inputs. *)
  Lemma cq_red L Q pb t1 t2 w1 w2 :
    nctx <= L -> L <= Q ->
    cred Γ Σ (jctx (Q - nctx)) t1 w1 -> cred Γ Σ (jctx (Q - nctx)) t2 w2 ->
    cq L Q pb w1 w2 -> cq L Q pb t1 t2.
  Proof.
    intros hL hQ hr1 hr2 h u1 u2 e1 e2 s1 s2 Δ hΔ hcl. subst t1 t2.
    destruct (cred_unlift Γ nctx Σ wfΣ hnctx hΓ L Q u1 w1 hL hQ (scl_hyg L u1 s1) hr1)
      as (w1' & -> & hd1).
    destruct (cred_unlift Γ nctx Σ wfΣ hnctx hΓ L Q u2 w2 hL hQ (scl_hyg L u2 s2) hr2)
      as (w2' & -> & hd2).
    assert (hj : #|jctx (L - nctx)| = L - nctx) by apply jctx_length.
    destruct (hd1 _ hj) as [rj1]. destruct (hd2 _ hj) as [rj2].
    pose proof (red_scl L _ u1 w1' hL hj (ctx_closed_jctx _) s1 rj1) as sw1.
    pose proof (red_scl L _ u2 w2' hL hj (ctx_closed_jctx _) s2 rj2) as sw2.
    destruct (h w1' w2' eq_refl eq_refl sw1 sw2 Δ hΔ hcl) as [hc].
    destruct (hd1 Δ hΔ) as [r1]. destruct (hd2 Δ hΔ) as [r2].
    constructor.
    eapply (ws_cumul_pb_closed_red (wfΣ := wfΣ)); [| |exact hc].
    - exact (into_closed_red r1 hcl (scl_open L Δ u1 hL hΔ s1)).
    - exact (into_closed_red r2 hcl (scl_open L Δ u2 hL hΔ s2)).
  Qed.

  Lemma cqs_nil L Q : cqs L Q [] [].
  Proof.
    intros us1 us2 e1 e2 _ _ Δ _ _.
    destruct us1; [|discriminate e1]. destruct us2; [|discriminate e2].
    constructor. constructor.
  Qed.

  Lemma cqs_cons L Q t1 t2 ts1 ts2 :
    cq L Q Conv t1 t2 -> cqs L Q ts1 ts2 -> cqs L Q (t1 :: ts1) (t2 :: ts2).
  Proof.
    intros h hs us1 us2 e1 e2 s1 s2 Δ hΔ hcl.
    destruct us1 as [|u1 us1]; [discriminate e1|]. destruct us2 as [|u2 us2]; [discriminate e2|].
    cbn in e1, e2. injection e1 as e1 e1'. injection e2 as e2 e2'.
    cbn in s1, s2. apply andb_true_iff in s1 as [s1 s1']. apply andb_true_iff in s2 as [s2 s2'].
    destruct (h u1 u2 e1 e2 s1 s2 Δ hΔ hcl) as [hc].
    destruct (hs us1 us2 e1' e2' s1' s2' Δ hΔ hcl) as [hcs].
    constructor. constructor; assumption.
  Qed.

  Lemma mkApps_lift0_inv m h ts u :
    mkApps h ts = lift0 m u ->
    exists h' us, u = mkApps h' us /\ h = lift0 m h' /\ ts = map (lift0 m) us.
  Proof.
    revert u. induction ts as [|t ts ih] using rev_ind; intros u e.
    - exists u, []. cbn in e |- *. split; [reflexivity|]. split; [exact e|reflexivity].
    - rewrite mkApps_app in e. cbn in e.
      destruct u as [| | | | | | |u1 u2| | | | | | | |]; cbn in e; try discriminate e.
      injection e as e1 e2.
      destruct (ih _ e1) as (h' & us & -> & -> & ->).
      exists h', (us ++ [u2]). split; [rewrite mkApps_app; reflexivity|]. split; [reflexivity|].
      rewrite map_app. cbn. rewrite e2. reflexivity.
  Qed.

  Lemma lift0_closed_inv m h h' : closedn 0 h -> h = lift0 m h' -> h' = h.
  Proof.
    intros hc e. apply (lift0_inj m).
    transitivity h; [symmetry; exact e|symmetry; exact (lift_closed _ _ _ hc)].
  Qed.

  (** ** [conv_cells] *)

  Lemma conv_cells_eq k L l1 l2 rs s :
    conv_cells X_type X Γ nctx stress (FS k) L l1 l2 rs s =
    match l1, l2 with
    | [], [] => COk (true, rs, s)
    | a1 :: l1, a2 :: l2 =>
      match conv_slot X_type X Γ nctx stress (k tt) L Conv (SAddr a1) (SAddr a2)
              (RSp l1 :: RSp l2 :: rs) s with
      | COk (true, rs, s) =>
        match rs with
        | RSp l1 :: RSp l2 :: rs => conv_cells X_type X Γ nctx stress (k tt) L l1 l2 rs s
        | _ => CFail WRoots
        end
      | COk (false, rs, s) => COk (false, skipn 2 rs, s)
      | CFail w => CFail w
      end
    | _, _ => COk (false, rs, s)
    end.
  Proof. reflexivity. Qed.

  Lemma conv_cells_sound_g (k : unit -> cbn_fuel) :
    spec_slot (k tt) -> spec_cells (k tt) -> spec_cells (FS k).
  Proof.
    intros hS hC L Q lo G l1 l2 ts1 ts2 rs s b rs' s' hm hr hl1 hl2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite conv_cells_eq in he.
    destruct l1 as [|a1 l1]; destruct l2 as [|a2 l2].
    - injection he as <- <- <-. inversion hl1; subst. inversion hl2; subst.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros _. apply cqs_nil.
    - injection he as <- <- <-.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - injection he as <- <- <-.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - inversion hl1 as [|y1 u1 m1 us1 hx1 hm1]; subst.
      inversion hl2 as [|y2 u2 m2 us2 hx2 hm2]; subst.
      destruct (conv_slot X_type X Γ nctx stress (k tt) L Conv (SAddr a1) (SAddr a2)
                  (RSp l1 :: RSp l2 :: rs) s) as [[[b2 rs2] s2]|w] eqn:Ecs;
        [|discriminate he].
      assert (hr' : Forall (rwf Q) (RSp l1 :: RSp l2 :: rs))
        by (constructor; [exact I|constructor; [exact I|exact hr]]).
      destruct (hS L Q lo G Conv (SAddr a1) (SAddr a2) u1 u2 _ s b2 rs2 s2 hm hr'
                  ltac:(constructor; exact hx1) ltac:(constructor; exact hx2) Ecs) as [hp1 hc1].
      destruct b2.
      + destruct hp1 as (Q1 & lo1 & G1 & hq1 & hm1' & hr1 & hg1).
        destruct (grq_cons_inv _ _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hqa & hgA).
        destruct (gpq_RSp_inv _ _ _ _ _ _ hqa) as (l1' & -> & hk1).
        destruct (grq_cons_inv _ _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hqb & hgB).
        destruct (gpq_RSp_inv _ _ _ _ _ _ hqb) as (l2' & -> & hk2).
        cbv beta iota in he.
        destruct (hC L Q1 lo1 G1 l1' l2' _ _ rsB s2 b rs' s' hm1'
                    (Forall_inv_tail (Forall_inv_tail hr1)) (hk1 _ hm1) (hk2 _ hm2) he)
          as [hp hc].
        split; [exact (post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
        intros hb. apply cqs_cons; [exact (hc1 eq_refl)|].
        exact (cqs_lift _ _ _ _ _ hLQ hq1 (hc hb)).
      + cbv beta iota in he. injection he as <- <- <-.
        split; [exact (post_drop2 _ _ _ _ _ _ _ _ hp1)|]. intros hb; discriminate hb.
  Qed.

  (** ** [conv_eval] and [conv_term]: the machine, then the values *)

  Lemma conv_eval_eq k L le x1 x2 rs s :
    conv_eval X_type X Γ nctx stress (FS k) L le x1 x2 rs s =
    match eval_slot X_type X Γ nctx stress (k tt) x1 [] (RSl x2 :: rs) s with
    | COk (v1, rs, s) =>
      match rs with
      | RSl x2 :: rs =>
        match eval_slot X_type X Γ nctx stress (k tt) x2 [] (RV v1 :: rs) s with
        | COk (v2, rs, s) =>
          match rs with
          | RV v1 :: rs => conv_value X_type X Γ nctx stress (k tt) L le v1 v2 rs s
          | _ => CFail WRoots
          end
        | CFail w => CFail w
        end
      | _ => CFail WRoots
      end
    | CFail w => CFail w
    end.
  Proof. reflexivity. Qed.

  Lemma conv_term_eq k L le e1 c1 e2 c2 rs s :
    conv_term X_type X Γ nctx stress (FS k) L le e1 c1 e2 c2 rs s =
    match whnf X_type X Γ nctx stress (k tt) e1 c1 [] (RE e2 :: rs) s with
    | COk (v1, rs, s) =>
      match rs with
      | RE e2 :: rs =>
        match whnf X_type X Γ nctx stress (k tt) e2 c2 [] (RV v1 :: rs) s with
        | COk (v2, rs, s) =>
          match rs with
          | RV v1 :: rs => conv_value X_type X Γ nctx stress (k tt) L le v1 v2 rs s
          | _ => CFail WRoots
          end
        | CFail w => CFail w
        end
      | _ => CFail WRoots
      end
    | CFail w => CFail w
    end.
  Proof. reflexivity. Qed.

  Lemma conv_eval_sound_g (k : unit -> cbn_fuel) : spec_value (k tt) -> spec_eval (FS k).
  Proof.
    intros hV L Q lo G pb x1 x2 t1 t2 rs s b rs' s' hm hr hx1 hx2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite conv_eval_eq in he.
    destruct (eval_slot X_type X Γ nctx stress (k tt) x1 [] (RSl x2 :: rs) s)
      as [[[v1 rs1] s1]|w] eqn:E1; [|discriminate he].
    destruct (eval_slot_master_hwf X_type X Γ nctx stress Σ wfΣ hΣ hnctx hcio (k tt) L Q lo G
                x1 [] [] t1 _ s v1 rs1 s1 hm (Forall_cons (RSl x2) I hr) hx1 ltac:(constructor) E1)
      as (lo1 & G1 & w1 & hm1 & hr1 & hv1 & hg1 & hw1 & hd1).
    destruct (gren_cons_inv _ _ _ _ _ _ hg1) as (q1 & rs1' & -> & hq1 & hg1').
    destruct (gpres_RSl_inv _ _ _ _ _ hq1) as (x2' & -> & hk1).
    cbv beta iota in he.
    destruct (eval_slot X_type X Γ nctx stress (k tt) x2' [] (RV v1 :: rs1') s1)
      as [[[v2 rs2] s2]|w] eqn:E2; [|discriminate he].
    destruct (eval_slot_master_hwf X_type X Γ nctx stress Σ wfΣ hΣ hnctx hcio (k tt) L Q lo1 G1
                x2' [] [] t2 _ s1 v2 rs2 s2 hm1 (Forall_cons (RV v1) hv1 (Forall_inv_tail hr1))
                (hk1 _ hx2) ltac:(constructor) E2)
      as (lo2 & G2 & w2 & hm2 & hr2 & hv2 & hg2 & hw2 & hd2).
    destruct (gren_cons_inv _ _ _ _ _ _ hg2) as (q2 & rs2' & -> & hq2 & hg2').
    destruct (gpres_RV_inv _ _ _ _ _ hq2) as (v1' & -> & hk2).
    cbv beta iota in he.
    destruct (hV L Q lo2 G2 pb v1' v2 w1 w2 rs2' s2 b rs' s' hm2 (Forall_inv_tail hr2)
                (Forall_inv hr2) hv2 (hk2 _ hw1) hw2 he) as [hp hc].
    pose proof (proj1 (proj2 (machine_skel X_type X Γ nctx stress (k tt))) _ _ _ _ _ _ _ E1)
      as hK1.
    pose proof (proj1 (proj2 (machine_skel X_type X Γ nctx stress (k tt))) _ _ _ _ _ _ _ E2)
      as hK2.
    split.
    - apply (post_compose L Q Q G G2 rs rs2' s' rs' (le_n Q)); [|exact hp].
      apply (grq_trans Q Q Q G G1 G2 rs rs1' rs2' (le_n Q) (le_n Q));
        (apply grq_of_gren; [assumption|eapply sk_tl; eassumption]).
    - intros hb. exact (cq_red L Q pb t1 t2 w1 w2 hL hLQ hd1 hd2 (hc hb)).
  Qed.

  Lemma conv_term_sound_g (k : unit -> cbn_fuel) : spec_value (k tt) -> spec_term (FS k).
  Proof.
    intros hV L Q lo G pb e1 c1 e2 c2 t1 t2 rs s b rs' s' hm hr hs1 hc1 hs2 hc2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite conv_term_eq in he.
    destruct (whnf X_type X Γ nctx stress (k tt) e1 c1 [] (RE e2 :: rs) s)
      as [[[v1 rs1] s1]|w] eqn:E1; [|discriminate he].
    destruct (whnf_master_hwf X_type X Γ nctx stress Σ wfΣ hΣ hnctx hcio (k tt) L Q lo G
                e1 c1 [] [] t1 _ s v1 rs1 s1 hm (Forall_cons (RE e2) I hr) hs1 hc1 ltac:(constructor) E1)
      as (lo1 & G1 & w1 & hm1 & hr1 & hv1 & hg1 & hw1 & hd1).
    destruct (gren_cons_inv _ _ _ _ _ _ hg1) as (q1 & rs1' & -> & hq1 & hg1').
    destruct (gpres_RE_inv _ _ _ _ _ hq1) as (e2' & -> & hk1).
    cbv beta iota in he.
    destruct (whnf X_type X Γ nctx stress (k tt) e2' c2 [] (RV v1 :: rs1') s1)
      as [[[v2 rs2] s2]|w] eqn:E2; [|discriminate he].
    destruct (whnf_master_hwf X_type X Γ nctx stress Σ wfΣ hΣ hnctx hcio (k tt) L Q lo1 G1
                e2' c2 [] [] t2 _ s1 v2 rs2 s2 hm1 (Forall_cons (RV v1) hv1 (Forall_inv_tail hr1))
                (genv_susp _ _ _ _ _ _ _ _ hk1 hs2) (cok_gcx _ _ (proj1 hg1) _ hc2)
                ltac:(constructor) E2)
      as (lo2 & G2 & w2 & hm2 & hr2 & hv2 & hg2 & hw2 & hd2).
    destruct (gren_cons_inv _ _ _ _ _ _ hg2) as (q2 & rs2' & -> & hq2 & hg2').
    destruct (gpres_RV_inv _ _ _ _ _ hq2) as (v1' & -> & hk2).
    cbv beta iota in he.
    destruct (hV L Q lo2 G2 pb v1' v2 w1 w2 rs2' s2 b rs' s' hm2 (Forall_inv_tail hr2)
                (Forall_inv hr2) hv2 (hk2 _ hw1) hw2 he) as [hp hc].
    pose proof (proj1 (proj2 (proj2 (machine_skel X_type X Γ nctx stress (k tt))))
                  _ _ _ _ _ _ _ _ E1) as hK1.
    pose proof (proj1 (proj2 (proj2 (machine_skel X_type X Γ nctx stress (k tt))))
                  _ _ _ _ _ _ _ _ E2) as hK2.
    split.
    - apply (post_compose L Q Q G G2 rs rs2' s' rs' (le_n Q)); [|exact hp].
      apply (grq_trans Q Q Q G G1 G2 rs rs1' rs2' (le_n Q) (le_n Q));
        (apply grq_of_gren; [assumption|eapply sk_tl; eassumption]).
    - intros hb. exact (cq_red L Q pb t1 t2 w1 w2 hL hLQ hd1 hd2 (hc hb)).
  Qed.

  (** ** The rows that compare heads and spines *)

  Lemma conv_rows_con_eq k L le h1 sp1 h2 sp2 rs s :
    conv_rows X_type X Γ nctx stress (FS k) L le (VCon h1 sp1) (VCon h2 sp2) rs s =
    if (#|sp1| == #|sp2|) && cmp_term X_type X le #|sp1| h1 h2
    then conv_cells X_type X Γ nctx stress (k tt) L sp1 sp2 rs s else COk (false, rs, s).
  Proof. reflexivity. Qed.

  Lemma conv_rows_var_eq k L le l1 sp1 l2 sp2 rs s :
    conv_rows X_type X Γ nctx stress (FS k) L le (VNeu (NVar l1) sp1) (VNeu (NVar l2) sp2) rs s =
    if l1 == l2 then conv_cells X_type X Γ nctx stress (k tt) L sp1 sp2 rs s
    else COk (false, rs, s).
  Proof. reflexivity. Qed.

  Lemma conv_rows_const_eq k L le h1 sp1 h2 sp2 rs s :
    conv_rows X_type X Γ nctx stress (FS k) L le (VNeu (NConst h1) sp1) (VNeu (NConst h2) sp2)
      rs s =
    if cmp_term X_type X Conv #|sp1| h1 h2
    then conv_cells X_type X Γ nctx stress (k tt) L sp1 sp2 rs s else COk (false, rs, s).
  Proof. reflexivity. Qed.

  Lemma conv_rows_sort_eq k L le e1 c1 e2 c2 s1 s2 rs s :
    c1.(c_term) = tSort s1 -> c2.(c_term) = tSort s2 ->
    conv_rows X_type X Γ nctx stress (FS k) L le (VOpen e1 c1) (VOpen e2 c2) rs s
    = COk (cmp_sort X_type X le s1 s2, rs, s).
  Proof.
    destruct c1 as [i1 p1 t1], c2 as [i2 p2 t2]. cbn. intros -> ->. reflexivity.
  Qed.

  (** Shared tail of the spine rows: equal heads (up to the head test) and convertible
    spines give convertible applications. *)
  Lemma cv_spine L pb h1 h2 us1 us2 :
    nctx <= L -> (forall Δ, #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) ->
                    ∥ Σ ;;; Γ ,,, Δ ⊢ h1 ≤[pb] h2 ∥) ->
    cvs L us1 us2 -> cv L pb (mkApps h1 us1) (mkApps h2 us2).
  Proof.
    intros hL hh hs Δ hΔ hcl. destruct (hh Δ hΔ hcl) as [h]. destruct (hs Δ hΔ hcl) as [hs'].
    constructor. exact (ws_cumul_pb_mkApps (wfΣ := wfΣ) h hs').
  Qed.

  Lemma conv_rows_con_g (k : unit -> cbn_fuel) :
    spec_cells (k tt) ->
    spec_rows_on (FS k) (fun v1 v2 => exists h1 sp1 h2 sp2, v1 = VCon h1 sp1 /\ v2 = VCon h2 sp2).
  Proof.
    intros hC L Q lo G pb v1 v2 w1 w2 rs s b rs' s' (h1 & sp1 & h2 & sp2 & -> & ->)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite conv_rows_con_eq in he.
    apply g_value_VCon_inv in hw1 as (ts1 & -> & ha1).
    apply g_value_VCon_inv in hw2 as (ts2 & -> & ha2).
    cbn in hv1, hv2.
    destruct ((#|sp1| == #|sp2|) && cmp_term X_type X pb #|sp1| h1 h2) eqn:Et;
      [|injection he as <- <- <-;
        split; [exact (post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    apply andb_true_iff in Et as [_ Ecmp].
    destruct (hC L Q lo G sp1 sp2 ts1 ts2 rs s b rs' s' hm hr ha1 ha2 he) as [hp hc].
    split; [exact hp|]. intros hb u1 u2 e1 e2 s1 s2.
    apply mkApps_lift0_inv in e1 as (h1' & us1 & -> & eh1 & ->).
    apply mkApps_lift0_inv in e2 as (h2' & us2 & -> & eh2 & ->).
    pose proof (lift0_closed_inv _ _ _ hv1 eh1) as ->.
    pose proof (lift0_closed_inv _ _ _ hv2 eh2) as ->.
    unfold scl in s1, s2. rewrite on_free_vars_mkApps in s1, s2.
    apply andb_true_iff in s1 as [sh1 sus1]. apply andb_true_iff in s2 as [sh2 sus2].
    intros Δ hΔ hcl.
    destruct (hc hb us1 us2 eq_refl eq_refl sus1 sus2 Δ hΔ hcl) as [hcs].
    constructor.
    apply (ws_cumul_pb_mkApps_napp (wfΣ := wfΣ));
      [exact hcl|exact (scl_open L Δ h1 hL hΔ sh1)|exact (scl_open L Δ h2 hL hΔ sh2)| |exact hcs].
    pose proof (cmp_term_sound X_type X Σ hΣ pb _ h1 h2 Ecmp) as hcmp.
    rewrite <- (g_addrs_length _ _ _ ha1), length_map in hcmp. exact hcmp.
  Qed.

  Lemma conv_rows_const_g (k : unit -> cbn_fuel) :
    spec_cells (k tt) ->
    spec_rows_on (FS k) (fun v1 v2 => exists h1 sp1 h2 sp2,
                           v1 = VNeu (NConst h1) sp1 /\ v2 = VNeu (NConst h2) sp2).
  Proof.
    intros hC L Q lo G pb v1 v2 w1 w2 rs s b rs' s' (h1 & sp1 & h2 & sp2 & -> & ->)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite conv_rows_const_eq in he.
    apply g_value_VNeu_inv in hw1 as [(l & ts & e & _)|(h1' & ts1 & e & -> & ha1)];
      [discriminate e|injection e as <-].
    apply g_value_VNeu_inv in hw2 as [(l & ts & e & _)|(h2' & ts2 & e & -> & ha2)];
      [discriminate e|injection e as <-].
    cbn in hv1, hv2.
    destruct (cmp_term X_type X Conv #|sp1| h1 h2) eqn:Ecmp;
      [|injection he as <- <- <-;
        split; [exact (post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    destruct (hC L Q lo G sp1 sp2 ts1 ts2 rs s b rs' s' hm hr ha1 ha2 he) as [hp hc].
    split; [exact hp|]. intros hb u1 u2 e1 e2 s1 s2.
    apply mkApps_lift0_inv in e1 as (h1' & us1 & -> & eh1 & ->).
    apply mkApps_lift0_inv in e2 as (h2' & us2 & -> & eh2 & ->).
    pose proof (lift0_closed_inv _ _ _ hv1 eh1) as ->.
    pose proof (lift0_closed_inv _ _ _ hv2 eh2) as ->.
    unfold scl in s1, s2. rewrite on_free_vars_mkApps in s1, s2.
    apply andb_true_iff in s1 as [sh1 sus1]. apply andb_true_iff in s2 as [sh2 sus2].
    intros Δ hΔ hcl.
    destruct (hc hb us1 us2 eq_refl eq_refl sus1 sus2 Δ hΔ hcl) as [hcs].
    constructor. apply (ws_cumul_eq_pb (wfΣ := wfΣ)).
    apply (ws_cumul_pb_mkApps_napp (wfΣ := wfΣ));
      [exact hcl|exact (scl_open L Δ h1 hL hΔ sh1)|exact (scl_open L Δ h2 hL hΔ sh2)| |exact hcs].
    pose proof (cmp_term_sound X_type X Σ hΣ Conv _ h1 h2 Ecmp) as hcmp.
    rewrite <- (g_addrs_length _ _ _ ha1), length_map in hcmp. exact hcmp.
  Qed.

  Lemma conv_rows_var_g (k : unit -> cbn_fuel) :
    spec_cells (k tt) ->
    spec_rows_on (FS k) (fun v1 v2 => exists l1 sp1 l2 sp2,
                           v1 = VNeu (NVar l1) sp1 /\ v2 = VNeu (NVar l2) sp2).
  Proof.
    intros hC L Q lo G pb v1 v2 w1 w2 rs s b rs' s' (l1 & sp1 & l2 & sp2 & -> & ->)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite conv_rows_var_eq in he.
    apply g_value_VNeu_inv in hw1 as [(l1' & ts1 & e & -> & ha1)|(h & ts & e & _)];
      [injection e as <-|discriminate e].
    apply g_value_VNeu_inv in hw2 as [(l2' & ts2 & e & -> & ha2)|(h & ts & e & _)];
      [injection e as <-|discriminate e].
    destruct (l1 == l2) eqn:El;
      [|injection he as <- <- <-;
        split; [exact (post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    apply eqb_eq in El. subst l2.
    destruct (hC L Q lo G sp1 sp2 ts1 ts2 rs s b rs' s' hm hr ha1 ha2 he) as [hp hc].
    split; [exact hp|]. intros hb u1 u2 e1 e2 s1 s2.
    apply mkApps_lift0_inv in e1 as (h1' & us1 & -> & eh1 & ->).
    apply mkApps_lift0_inv in e2 as (h2' & us2 & -> & eh2 & ->).
    rewrite eh1 in eh2. apply lift0_inj in eh2. subst h2'.
    unfold scl in s1, s2. rewrite on_free_vars_mkApps in s1, s2.
    apply andb_true_iff in s1 as [sh1 sus1]. apply andb_true_iff in s2 as [_ sus2].
    apply cv_spine; [exact hL| |exact (hc hb us1 us2 eq_refl eq_refl sus1 sus2)].
    intros Δ hΔ hcl. constructor. apply ws_cumul_pb_refl; [exact hcl|exact (scl_open L Δ h1' hL hΔ sh1)].
  Qed.

  Lemma conv_rows_sort_g (k : unit -> cbn_fuel) :
    spec_rows_on (FS k) (fun v1 v2 => exists e1 c1 e2 c2 s1 s2,
                           v1 = VOpen e1 c1 /\ v2 = VOpen e2 c2
                           /\ c1.(c_term) = tSort s1 /\ c2.(c_term) = tSort s2).
  Proof.
    intros L Q lo G pb v1 v2 w1 w2 rs s b rs' s' (e1 & c1 & e2 & c2 & s1 & s2 & -> & -> & h1 & h2)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite (conv_rows_sort_eq k L pb e1 c1 e2 c2 s1 s2 rs s h1 h2) in he.
    injection he as <- <- <-.
    split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros hcs u1 u2 e1' e2' _ _ Δ hΔ hcl.
    apply g_value_VOpen_inv in hw1. apply g_value_VOpen_inv in hw2.
    rewrite h1 in hw1. rewrite h2 in hw2.
    destruct (g_susp_inv _ _ _ _ _ _ hw1) as (ts1 & _ & _ & ->).
    destruct (g_susp_inv _ _ _ _ _ _ hw2) as (ts2 & _ & _ & ->).
    cbn in e1', e2'.
    destruct u1; cbn in e1'; try discriminate e1'. injection e1' as <-.
    destruct u2; cbn in e2'; try discriminate e2'. injection e2' as <-.
    constructor. apply ws_cumul_pb_compare_term; [exact hcl|reflexivity|reflexivity|].
    constructor. exact (cmp_sort_sound X_type X Σ hΣ pb s1 s2 hcs).
  Qed.

  (** ** Fresh variables at the master level *)

  (** A fresh-variable cell for level [lvl < Q] reads [tRel (Q - S lvl)]; allocating it keeps
    [minv] ([alloc_sound], [alloc_hwf_holds]). *)
  Lemma alloc_fresh_g L Q lo G lvl rs s x rs' s' :
    MI L Q lo G s -> Forall (rwf Q) rs -> lvl < Q ->
    alloc stress (CDone (VNeu (NVar lvl) [])) rs s = COk (x, rs', s') ->
    exists lo' G', MI L Q lo' G' s' /\ Forall (rwf Q) rs' /\ gren nctx Q G G' rs rs'
      /\ G' x = Some (tRel (Q - S lvl)).
  Proof.
    intros [hL hLQ hok hw] hr hlt he.
    assert (hj : #|jctx (Q - nctx)| = Q - nctx) by apply jctx_length.
    assert (hc : g_cell nctx Q G (CDone (VNeu (NVar lvl) [])) (tRel (Q - S lvl))).
    { apply g_cell_done. apply (g_VNeuVar _ _ _ lvl [] []). constructor. }
    destruct (alloc_sound X_type X Γ nctx stress Σ (jctx (Q - nctx)) Q hj hnctx ltac:(lia) lo G
                _ _ rs s x rs' s' hok hc (fun _ => eq_refl) he)
      as (lo' & G' & hg & hok' & hx).
    destruct (alloc_hwf_holds nctx stress Q (CDone (VNeu (NVar lvl) [])) rs s x rs' s'
                ltac:(lia) hw hlt hr he) as [hw' hr'].
    exists lo', G'. split; [constructor; assumption|]. split; [exact hr'|]. split; assumption.
  Qed.

  Lemma fresh_reads_S Q lvl n ts :
    lvl + S n <= Q ->
    map (lift0 (Q - (S lvl + n))) (idsn n) ++ tRel (Q - S lvl) :: ts
    = map (lift0 (Q - (lvl + S n))) (idsn (S n)) ++ ts.
  Proof.
    intros h. replace (Q - (lvl + S n)) with (Q - (S lvl + n)) by lia.
    cbn [idsn]. rewrite map_app, <- app_assoc. cbn [map app]. f_equal. f_equal.
    cbn. f_equal. lia.
  Qed.

  (** [push_fresh n lvl] pushes [n] fresh variables, levels [lvl] to [lvl + n - 1], on both
    environments; at the master level they read as the lift of [idsn n]. *)
  Lemma push_fresh_g (n : nat) :
    forall L Q lo G lvl e1 e2 ts1 ts2 rs s r rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs -> lvl + n <= Q ->
      g_slots nctx Q G e1.(ev_vals) ts1 -> e1.(ev_nvals) = #|e1.(ev_vals)| ->
      g_slots nctx Q G e2.(ev_vals) ts2 -> e2.(ev_nvals) = #|e2.(ev_vals)| ->
      push_fresh stress n lvl e1 e2 rs s = COk (r, rs', s') ->
      exists lo' G' f1 f2,
        r = (lvl + n, f1, f2) /\ MI L Q lo' G' s' /\ Forall (rwf Q) rs'
        /\ gren nctx Q G G' rs rs'
        /\ f1.(ev_nvals) = #|f1.(ev_vals)| /\ f1.(ev_goff) = e1.(ev_goff)
        /\ f2.(ev_nvals) = #|f2.(ev_vals)| /\ f2.(ev_goff) = e2.(ev_goff)
        /\ g_slots nctx Q G' f1.(ev_vals) (map (lift0 (Q - (lvl + n))) (idsn n) ++ ts1)
        /\ g_slots nctx Q G' f2.(ev_vals) (map (lift0 (Q - (lvl + n))) (idsn n) ++ ts2).
  Proof.
    induction n as [|n ih];
      intros L Q lo G lvl e1 e2 ts1 ts2 rs s r rs' s' hm hr hq hs1 hn1 hs2 hn2 he.
    - rewrite pfd_push_fresh_O in he. injection he as <- <- <-.
      exists lo, G, e1, e2. rewrite Nat.add_0_r. split; [reflexivity|].
      split; [exact hm|]. split; [exact hr|]. split; [apply gren_refl|].
      cbn [idsn map app]. repeat split; assumption.
    - rewrite pfd_push_fresh_S in he.
      destruct (alloc stress (CDone (VNeu (NVar lvl) [])) (RE e1 :: RE e2 :: rs) s)
        as [[[x rs1] s1]|w] eqn:Ea; [|discriminate he].
      destruct (alloc_fresh_g L Q lo G lvl _ s x rs1 s1 hm
                  (Forall_cons (RE e1) I (Forall_cons (RE e2) I hr)) ltac:(lia) Ea)
        as (lo1 & G1 & hm1 & hr1 & hg1 & hx).
      destruct (gren_cons_inv _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hq1 & hgA).
      destruct (gpres_RE_inv _ _ _ _ _ hq1) as (e1' & -> & (hn1' & hg1' & hk1)).
      destruct (gren_cons_inv _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hq2 & hgB).
      destruct (gpres_RE_inv _ _ _ _ _ hq2) as (e2' & -> & (hn2' & hg2' & hk2)).
      cbv beta iota in he.
      pose proof (hk1 _ hs1) as hs1'. pose proof (hk2 _ hs2) as hs2'.
      pose proof (g_slots_length _ _ _ _ _ hs1) as hl1.
      pose proof (g_slots_length _ _ _ _ _ hs1') as hl1'.
      pose proof (g_slots_length _ _ _ _ _ hs2) as hl2.
      pose proof (g_slots_length _ _ _ _ _ hs2') as hl2'.
      destruct (ih L Q lo1 G1 (S lvl) (env_push (SAddr x) e1') (env_push (SAddr x) e2')
                  (tRel (Q - S lvl) :: ts1) (tRel (Q - S lvl) :: ts2) rsB s1 r rs' s' hm1
                  (Forall_inv_tail (Forall_inv_tail hr1)) ltac:(lia)
                  ltac:(constructor; [constructor; exact hx|exact hs1'])
                  ltac:(cbn; lia)
                  ltac:(constructor; [constructor; exact hx|exact hs2'])
                  ltac:(cbn; lia) he)
        as (lo' & G' & f1 & f2 & -> & hm' & hr' & hg' & hf1 & hgo1 & hf2 & hgo2 & hr1' & hr2').
      exists lo', G', f1, f2.
      split; [do 2 f_equal; lia|]. split; [exact hm'|]. split; [exact hr'|].
      split; [exact (gren_trans _ _ _ _ _ _ _ _ hgB hg')|].
      split; [exact hf1|]. split; [rewrite hgo1; exact hg1'|].
      split; [exact hf2|]. split; [rewrite hgo2; exact hg2'|].
      rewrite <- !(fresh_reads_S Q lvl n) by lia. split; assumption.
  Qed.

  (** ** Environments across a call *)

  Lemma gsusp_q Q Q' G G' e e' t u :
    nctx <= Q -> Q <= Q' -> gpq Q Q' G G' (RE e) (RE e') ->
    g_susp nctx Q G e t u -> g_susp nctx Q' G' e' t (lift0 (Q' - Q) u).
  Proof.
    intros hQ hQ' (hn & hg & hk) hs.
    destruct (g_susp_inv _ _ _ _ _ _ hs) as (ts & hts & hnv & ->).
    pose proof (hk _ hts) as hts'.
    pose proof (g_slots_length _ _ _ _ _ hts) as hl.
    pose proof (g_slots_length _ _ _ _ _ hts') as hl'. rewrite length_map in hl'.
    rewrite (lift_susp_read nctx Q (Q' - Q) hQ (Q - nctx + ev_goff e) (ev_nvals e) t ts
               ltac:(lia)).
    replace (Q' - Q + (Q - nctx + ev_goff e)) with (Q' - nctx + ev_goff e') by lia.
    rewrite <- hn. apply g_susp_of_slots; [exact hts'|lia].
  Qed.

  Lemma gsusps_q Q Q' G G' e e' l us :
    nctx <= Q -> Q <= Q' -> gpq Q Q' G G' (RE e) (RE e') ->
    Forall2 (g_susp nctx Q G e) l us -> Forall2 (g_susp nctx Q' G' e') l (map (lift0 (Q' - Q)) us).
  Proof.
    intros hQ hQ' hp h. induction h; constructor; [|exact IHh].
    exact (gsusp_q _ _ _ _ _ _ _ _ hQ hQ' hp H).
  Qed.

  Lemma pcodes_gcx G G' c i l : gcx G G' -> pcodes G c i l -> pcodes G' c i l.
  Proof.
    intros hc h. induction h; constructor; [exact (cok_gcx _ _ hc _ H)|exact IHh].
  Qed.

  Lemma bcodes_gcx G G' c i l : gcx G G' -> bcodes G c i l -> bcodes G' c i l.
  Proof.
    intros hc h. induction h; constructor; [exact (cok_gcx _ _ hc _ H)|exact IHh].
  Qed.

  (** ** [case_params] *)

  Lemma case_params_sound_g (k : unit -> cbn_fuel) :
    spec_term (k tt) -> spec_params (k tt) -> spec_params (FS k).
  Proof.
    intros hT hP L Q lo G e1 c1 e2 c2 i l1 l2 us1 us2 rs s b rs' s' hm hr hp1 hp2 hu1 hu2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite case_params_eq in he.
    destruct l1 as [|t1 l1]; destruct l2 as [|t2 l2].
    - injection he as <- <- <-. inversion hu1; subst. inversion hu2; subst.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros _. apply cqs_nil.
    - injection he as <- <- <-.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - injection he as <- <- <-.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - inversion hu1 as [|y1 v1 m1 vs1 hv1 hvs1]; subst.
      inversion hu2 as [|y2 v2 m2 vs2 hv2 hvs2]; subst.
      inversion hp1 as [|i1 z1 n1 hc1 hp1']; subst.
      inversion hp2 as [|i2 z2 n2 hc2 hp2']; subst.
      destruct (conv_term X_type X Γ nctx stress (k tt) L Conv
                  e1 (child c1 (case_param_step i) t1) e2 (child c2 (case_param_step i) t2)
                  (RE e1 :: RE e2 :: rs) s) as [[[b2 rs2] s2]|w] eqn:Ect; [|discriminate he].
      destruct (hT L Q lo G Conv e1 (child c1 (case_param_step i) t1)
                  e2 (child c2 (case_param_step i) t2) v1 v2 _ s b2 rs2 s2 hm
                  (Forall_cons (RE e1) I (Forall_cons (RE e2) I hr)) hv1 hc1 hv2 hc2 Ect)
        as [hpA hcA].
      destruct b2.
      + destruct hpA as (QA & loA & GA & hqA & hmA & hrA & hgA).
        destruct (grq_cons_inv _ _ _ _ _ _ _ hgA) as (q1 & rsA & -> & hqa & hgA1).
        destruct (gpq_RE_inv _ _ _ _ _ _ hqa) as (f1 & -> & hfa).
        destruct (grq_cons_inv _ _ _ _ _ _ _ hgA1) as (q2 & rsB & -> & hqb & hgB).
        destruct (gpq_RE_inv _ _ _ _ _ _ hqb) as (f2 & -> & hfb).
        cbv beta iota in he.
        destruct (hP L QA loA GA f1 c1 f2 c2 (N.succ i) l1 l2 _ _ rsB s2 b rs' s' hmA
                    (Forall_inv_tail (Forall_inv_tail hrA))
                    (pcodes_gcx _ _ _ _ _ (proj1 hgA) hp1') (pcodes_gcx _ _ _ _ _ (proj1 hgA) hp2')
                    (gsusps_q Q QA G GA e1 f1 l1 vs1 ltac:(lia) hqA hqa hvs1)
                    (gsusps_q Q QA G GA e2 f2 l2 vs2 ltac:(lia) hqA hqb hvs2) he) as [hp hc].
        split; [exact (post_compose _ _ _ _ _ _ _ _ _ hqA hgB hp)|].
        intros hb. apply cqs_cons; [exact (hcA eq_refl)|].
        exact (cqs_lift _ _ _ _ _ hLQ hqA (hc hb)).
      + cbv beta iota in he. injection he as <- <- <-.
        split; [exact (post_drop2 _ _ _ _ _ _ _ _ hpA)|]. intros hb; discriminate hb.
  Qed.

  (** ** The same-code rule on ghost readings *)

  Lemma shiftnP0 (P : nat -> bool) : shiftnP 0 P =1 P.
  Proof. intros i. unfold shiftnP. cbn. rewrite Nat.sub_0_r. reflexivity. Qed.

  (** The slots of an environment unlifted where the code uses them, a closed filler
    elsewhere: the logical slots the same-code rule substitutes. *)
  Fixpoint pickw (m : nat) (a : term) (i : nat) (ts : list term) : list term :=
    match ts with
    | [] => []
    | t :: ts => (if noccur_between i 1 a then tSort sProp else unl m t) :: pickw m a (S i) ts
    end.

  Lemma pickw_length m a i ts : #|pickw m a i ts| = #|ts|.
  Proof.
    revert i. induction ts as [|t ts ih]; intros i; cbn; [reflexivity|]. rewrite ih. reflexivity.
  Qed.

  Lemma pickw_lift m a i ts :
    (forall j u, nth_error ts j = Some u -> noccur_between (i + j) 1 a = false ->
       u = lift0 m (unl m u)) ->
    forall j, j < #|ts| -> noccur_between (i + j) 1 a = false ->
      nth_error (map (lift0 m) (pickw m a i ts)) j = nth_error ts j.
  Proof.
    revert i. induction ts as [|t ts ih]; intros i h j hj hn; cbn in hj |- *; [lia|].
    destruct j as [|j]; cbn.
    - rewrite Nat.add_0_r in hn. rewrite hn. f_equal. symmetry. apply (h 0 t eq_refl).
      rewrite Nat.add_0_r. exact hn.
    - apply ih; [|lia|replace (S i + j) with (i + S j) by lia; exact hn].
      intros j' u hu hn'. apply (h (S j') u hu). replace (i + S j') with (S i + j') by lia.
      exact hn'.
  Qed.

  Lemma pick_all2 L Q a i ts1 ts2 Δ :
    nctx <= L -> L <= Q -> #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) ->
    cagree L Q a i ts1 ts2 ->
    (forall j u, nth_error ts1 j = Some u -> noccur_between (i + j) 1 a = false ->
       on_free_vars (inq (Q - L) Q) u) ->
    (forall j u, nth_error ts2 j = Some u -> noccur_between (i + j) 1 a = false ->
       on_free_vars (inq (Q - L) Q) u) ->
    ∥ ws_cumul_pb_terms Σ (Γ ,,, Δ) (pickw (Q - L) a i ts1) (pickw (Q - L) a i ts2) ∥.
  Proof.
    intros hL hQ hΔ hcl h. induction h as [i|i u1 u2 l1 l2 hd hag ih]; intros h1 h2.
    - constructor. constructor.
    - assert (h1' : forall j u, nth_error l1 j = Some u -> noccur_between (S i + j) 1 a = false ->
                      on_free_vars (inq (Q - L) Q) u).
      { intros j u hu hn. apply (h1 (S j) u hu). replace (i + S j) with (S i + j) by lia.
        exact hn. }
      assert (h2' : forall j u, nth_error l2 j = Some u -> noccur_between (S i + j) 1 a = false ->
                      on_free_vars (inq (Q - L) Q) u).
      { intros j u hu hn. apply (h2 (S j) u hu). replace (i + S j) with (S i + j) by lia.
        exact hn. }
      destruct (ih h1' h2') as [hall].
      cbn [pickw]. destruct (noccur_between i 1 a) eqn:En.
      + constructor. constructor; [|exact hall].
        apply ws_cumul_pb_refl; [exact hcl|reflexivity].
      + destruct hd as [hd|hd]; [discriminate hd|].
        pose proof (h1 0 u1 eq_refl ltac:(rewrite Nat.add_0_r; exact En)) as o1.
        pose proof (h2 0 u2 eq_refl ltac:(rewrite Nat.add_0_r; exact En)) as o2.
        destruct (inq_unl _ _ _ o1) as [e1 s1]. destruct (inq_unl _ _ _ o2) as [e2 s2].
        replace (Q - (Q - L)) with L in s1, s2 by lia.
        destruct (hd _ _ e1 e2 s1 s2 Δ hΔ hcl) as [hc].
        constructor. constructor; [exact hc|exact hall].
  Qed.

  Lemma same_code_cv L Q pb n goff ts1 ts2 a Δ :
    nctx <= L -> L <= Q -> #|ts1| = n -> #|ts2| = n ->
    #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) ->
    cagree L Q a 0 ts1 ts2 ->
    (forall j u, nth_error ts1 j = Some u -> noccur_between (0 + j) 1 a = false ->
       on_free_vars (inq (Q - L) Q) u) ->
    (forall j u, nth_error ts2 j = Some u -> noccur_between (0 + j) 1 a = false ->
       on_free_vars (inq (Q - L) Q) u) ->
    scl L (subst (pickw (Q - L) a 0 ts1) 0 (lift (L - nctx + goff) n a)) ->
    ∥ Σ ;;; Γ ,,, Δ ⊢ subst (pickw (Q - L) a 0 ts1) 0 (lift (L - nctx + goff) n a) ≤[pb]
                     subst (pickw (Q - L) a 0 ts2) 0 (lift (L - nctx + goff) n a) ∥.
  Proof.
    intros hL hQ hl1 hl2 hΔ hcl hag h1 h2 hs.
    destruct (pick_all2 L Q a 0 ts1 ts2 Δ hL hQ hΔ hcl hag h1 h2) as [hall].
    constructor. apply (ws_cumul_pb_subst_open (wfΣ := wfΣ)); [exact hcl|exact hall|].
    pose proof (cg_subst_scope_inv (shiftnP L xpred0) (pickw (Q - L) a 0 ts1)
                  (lift (L - nctx + goff) n a) 0) as hsc.
    rewrite pickw_length, hl1 in hsc.
    assert (h0 : on_free_vars (shiftnP 0 (shiftnP L xpred0))
                   (subst (pickw (Q - L) a 0 ts1) 0 (lift (L - nctx + goff) n a))).
    { rewrite (on_free_vars_ext _ _ _ (shiftnP0 _)). exact hs. }
    specialize (hsc h0). rewrite (on_free_vars_ext _ _ _ (shiftnP_add _ _ _)) in hsc.
    rewrite !app_context_length, fresh_context_length, pickw_length, hl1, hΔ, <- hnctx.
    assert (E : n + (L - nctx + nctx) = 0 + n + L) by lia. rewrite E. exact hsc.
  Qed.

  (** Two readings of codes [code_eq] accepts, through environments with the same counts whose
    used slots agree in the sense of [cq], are convertible at any [conv_pb]. The used slots of a
    lifted reading are lifts ([cg_occ_inv]); the unused ones do not matter
    ([subst_agree_lift]). *)
  Lemma same_code_cq L Q pb n goff ts1 ts2 a1 a2 :
    nctx <= L -> L <= Q -> #|ts1| = n -> #|ts2| = n ->
    on_free_vars xpredT a1 -> on_free_vars xpredT a2 ->
    samec a1 a2 -> cagree L Q a1 0 ts1 ts2 ->
    cq L Q pb (subst ts1 0 (lift (Q - nctx + goff) n a1))
              (subst ts2 0 (lift (Q - nctx + goff) n a2)).
  Proof.
    intros hL hQ hl1 hl2 hy1 hy2 hsame hag u1 u2 e1 e2 s1 s2 Δ hΔ hcl.
    assert (hQm : L + (Q - L) = Q) by lia.
    assert (hN : Q - nctx + goff = (Q - L) + (L - nctx + goff)) by lia.
    assert (hinv : forall ts a, on_free_vars xpredT a -> #|ts| = n ->
              on_free_vars (inq (Q - L) Q) (subst ts 0 (lift (Q - nctx + goff) n a)) ->
              forall j u, nth_error ts j = Some u -> noccur_between (0 + j) 1 a = false ->
                on_free_vars (inq (Q - L) Q) u).
    { intros ts a hy hl hT j u hu hn.
      apply (cg_occ_inv (inq (Q - L) Q) ts (Q - nctx + goff) j u hu a 0 hy hn).
      rewrite (on_free_vars_ext _ _ _ (shiftnP0 _)). cbn [Nat.add]. rewrite hl. exact hT. }
    assert (hU : forall ts a U, on_free_vars xpredT a -> #|ts| = n ->
              subst ts 0 (lift (Q - nctx + goff) n a) = lift0 (Q - L) U ->
              on_free_vars (inq (Q - L) Q) (subst ts 0 (lift (Q - nctx + goff) n a)) ->
              U = subst (pickw (Q - L) a 0 ts) 0 (lift (L - nctx + goff) n a)).
    { intros ts a U hy hl eU hT. apply (lift0_inj (Q - L)). rewrite <- eU.
      rewrite (lift_susp_read nctx L (Q - L) hL (L - nctx + goff) n a (pickw (Q - L) a 0 ts)
                 ltac:(rewrite pickw_length; exact hl)).
      rewrite <- hN.
      apply subst_agree_lift; [rewrite length_map, pickw_length; reflexivity|symmetry; exact hl|].
      intros j hj hn. symmetry. apply pickw_lift; [|exact hj|exact hn].
      intros j' u hu hn'. exact (proj1 (inq_unl _ _ u (hinv ts a hy hl hT j' u hu hn'))). }
    pose proof (inq_lift0 (Q - L) L u1 s1) as hT1. rewrite hQm, <- e1 in hT1.
    pose proof (inq_lift0 (Q - L) L u2 s2) as hT2. rewrite hQm, <- e2 in hT2.
    pose proof (hU ts1 a1 u1 hy1 hl1 e1 hT1) as hU1.
    destruct hsame as [<-|[hc12]].
    - pose proof (hU ts2 a1 u2 hy1 hl2 e2 hT2) as hU2.
      rewrite hU1 in s1 |- *. rewrite hU2.
      exact (same_code_cv L Q pb n goff ts1 ts2 a1 Δ hL hQ hl1 hl2 hΔ hcl hag
               (hinv ts1 a1 hy1 hl1 hT1) (hinv ts2 a1 hy1 hl2 hT2) s1).
    - set (T2' := subst ts2 0 (lift (Q - nctx + goff) n a1)).
      assert (h12 : compare_term Σ Σ Conv T2' (subst ts2 0 (lift (Q - nctx + goff) n a2))).
      { apply subst_eq_term.
        exact (eq_term_upto_univ_lift Σ (compare_universe Σ) (compare_sort Σ) Conv
                 (Q - nctx + goff) 0 n _ _ hc12). }
      assert (h21 : compare_term Σ Σ Conv (subst ts2 0 (lift (Q - nctx + goff) n a2)) T2')
        by (symmetry; exact h12).
      pose proof (PCUICConfluence.eq_term_upto_univ_napp_on_free_vars h21 hT2) as hT2'.
      destruct (inq_unl (Q - L) Q T2' hT2') as [eT2' sT2'].
      replace (Q - (Q - L)) with L in sT2' by lia.
      pose proof (hU ts2 a1 (unl (Q - L) T2') hy1 hl2 eT2' hT2') as hU2'.
      assert (hc2 : compare_term Σ Σ Conv (unl (Q - L) T2') u2).
      { rewrite <- (unl_lift0 (Q - L) u2), <- e2.
        exact (PCUICRenameConv.eq_term_upto_univ_rename Σ _ _ Conv 0 _ _ _ h12). }
      rewrite hU1 in s1 |- *.
      destruct (same_code_cv L Q pb n goff ts1 ts2 a1 Δ hL hQ hl1 hl2 hΔ hcl hag
                  (hinv ts1 a1 hy1 hl1 hT1) (hinv ts2 a1 hy1 hl2 hT2') s1) as [h1].
      constructor. refine (@ws_cumul_pb_conv_trans_r cf Σ wfΣ pb (Γ ,,, Δ) _ _ _ h1 _).
      rewrite <- hU2'.
      apply ws_cumul_pb_compare_term; [exact hcl|exact (scl_open L Δ _ hL hΔ sT2')|
                                       exact (scl_open L Δ u2 hL hΔ s2)|exact hc2].
  Qed.

  (** [code_eq_sound], with the universe checks [code_eq] ran on the way to a syntactic
    comparison. *)
  Lemma code_eq_sound_wf (c1 c2 : code) (e1 e2 : code_entry) (s : cbn_state) :
    ceq_ok X_type X (s.(st_memo)) ->
    PTree.get c1.(c_entry) ((s.(st_memo)).(m_codes)) = Some e1 -> code_inv e1 c1 ->
    PTree.get c2.(c_entry) ((s.(st_memo)).(m_codes)) = Some e2 -> code_inv e2 c2 ->
    fst (code_eq X_type X c1 c2 s) = true ->
    c1.(c_term) = c2.(c_term)
    \/ (cbn_ceq_term X_type X c1.(c_term) c2.(c_term) = true
        /\ entry_wf c1.(c_entry) s = true /\ entry_wf c2.(c_entry) s = true).
  Proof.
    intros hq g1 hi1 g2 hi2 hE.
    destruct (code_eq_sound X_type X c1 c2 e1 e2 s hq g1 hi1 g2 hi2 hE) as [h|h];
      [left; exact h|].
    destruct (same_id c1 c2) eqn:Esid.
    { left. exact (same_id_sound_table _ e1 e2 c1 c2 Esid g1 hi1 g2 hi2). }
    right. split; [exact h|].
    unfold code_eq in hE. rewrite Esid in hE.
    destruct (entry_wf c1.(c_entry) s && entry_wf c2.(c_entry) s) eqn:Ew;
      [apply andb_true_iff in Ew; exact Ew|cbn in hE; discriminate hE].
  Qed.

  Lemma conv_same_code_sound_g (k : unit -> cbn_fuel) : spec_scc (k tt) -> spec_same (FS k).
  Proof.
    intros hC L Q lo G e1 c1 e2 c2 ts1 ts2 rs s b rs' s' hm hr hc1 hc2 hs1 hs2 he.
    pose proof hm as [hL hLQ hok hw].
    rewrite conv_same_code_eq in he.
    destruct ((e1.(ev_goff) == e2.(ev_goff)) && (e1.(ev_nvals) == e2.(ev_nvals))) eqn:Eeq;
      [|injection he as <- <- <-;
        split; [exact (post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    apply andb_true_iff in Eeq as [Eg En]. apply eqb_eq in Eg. apply eqb_eq in En.
    destruct hc1 as [ce1 [hg1 hi1]]. destruct hc2 as [ce2 [hg2 hi2]].
    destruct (gk_memo _ _ _ _ _ _ _ _ _ _ hok) as (hmi & hmo & hK & hcons & hhy).
    pose proof (hK _ _ hg1) as hg1'. pose proof (hK _ _ hg2) as hg2'.
    destruct (memo_inv_code_eq X_type X c1 c2 ce1 ce2 s hmi hg1' hi1 hg2' hi2)
      as (hmi' & hcodes & hheap & hnext & _ & _ & hgam).
    assert (hm0 : MI L Q lo G (snd (code_eq X_type X c1 c2 s))).
    { constructor; [exact hL|exact hLQ| |exact (hwf_heap Q s _ hheap hw)].
      apply (gok_same X_type X Γ nctx Σ _ Q lo G s); [exact hok|exact hheap|exact hnext|exact hgam|].
      split; [exact hmi'|]. split; [exact (memo_ok_codes X_type X s _ hcodes hmo)|].
      rewrite hcodes. split; [exact hK|]. split; [exact hcons|exact hhy]. }
    assert (hE : forall b0, fst (code_eq X_type X c1 c2 s) = b0 -> b0 = true ->
                   samec c1.(c_term) c2.(c_term)).
    { intros b0 Eb0 ->.
      destruct (code_eq_sound_wf c1 c2 ce1 ce2 s (proj1 (proj2 (proj2 (proj2 hmi))))
                  hg1' hi1 hg2' hi2 Eb0) as [h|(hceq & hw1 & hw2)]; [left; exact h|right].
      rewrite (memo_entry_wf X_type X s _ ce1 hmo hg1') in hw1.
      rewrite (memo_entry_wf X_type X s _ ce2 hmo hg2') in hw2.
      rewrite (wf_term_univs_correct X_type X Σ hΣ) in hw1, hw2.
      constructor.
      exact (cbn_ceq_term_sound X_type X Σ hΣ _ _ (cg_code_inv_wf_universes Σ ce1 c1 hi1 hw1)
               (cg_code_inv_wf_universes Σ ce2 c2 hi2 hw2) hceq). }
    destruct (code_eq X_type X c1 c2 s) as [b0 s0] eqn:Ece. cbn [fst snd] in hm0, hE.
    destruct b0;
      [|injection he as <- <- <-;
        split; [exact (post_refl _ _ _ _ _ _ hm0 hr)|intros hb; discriminate hb]].
    destruct (hC L Q lo G c1.(c_term) 0 _ _ ts1 ts2 rs s0 b rs' s' hm0 hr hs1 hs2 he) as [hp hc].
    split; [exact hp|]. intros hb. split; [exact Eg|]. split; [exact En|].
    split; [exact (hE true eq_refl eq_refl)|exact (hc hb)].
  Qed.

  (** Restates [conv_same_code_sound] on ghost readings: a [true] makes the two readings of
    the codes convertible at any [conv_pb]. *)
  Lemma conv_same_code_sound_ghost (d : cbn_fuel) : spec_same d ->
    forall L Q lo G pb e1 c1 e2 c2 t1 t2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs ->
      g_susp nctx Q G e1 c1.(c_term) t1 -> gcok G c1 ->
      g_susp nctx Q G e2 c2.(c_term) t2 -> gcok G c2 ->
      conv_same_code X_type X Γ nctx stress d L e1 c1 e2 c2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cq L Q pb t1 t2).
  Proof.
    intros hS L Q lo G pb e1 c1 e2 c2 t1 t2 rs s b rs' s' hm hr hs1 hc1 hs2 hc2 he.
    pose proof hm as [hL hLQ hok _].
    destruct (g_susp_inv _ _ _ _ _ _ hs1) as (ts1 & hts1 & hn1 & ->).
    destruct (g_susp_inv _ _ _ _ _ _ hs2) as (ts2 & hts2 & hn2 & ->).
    destruct (hS L Q lo G e1 c1 e2 c2 ts1 ts2 rs s b rs' s' hm hr hc1 hc2 hts1 hts2 he)
      as [hp hc].
    split; [exact hp|]. intros hb. destruct (hc hb) as (hgo & hnv & hsame & hag).
    pose proof (gok_codes_hyg X_type X Γ nctx Σ _ Q lo G s hok hhyg) as hch.
    pose proof (g_slots_length _ _ _ _ _ hts1) as hl1.
    pose proof (g_slots_length _ _ _ _ _ hts2) as hl2.
    rewrite <- hgo, <- hnv.
    apply (same_code_cq L Q pb (ev_nvals e1) (ev_goff e1) ts1 ts2 _ _ hL hLQ);
      [lia|lia|exact (hch _ hc1)|exact (hch _ hc2)|exact hsame|exact hag].
  Qed.

  (** The identifier fast path: [same_id] gives one term, so no universe check enters. *)
  Lemma conv_same_code_sound_same_id_ghost (d : cbn_fuel) : spec_same d ->
    forall L Q lo G pb e1 c1 e2 c2 t1 t2 rs s b rs' s',
      same_id c1 c2 = true ->
      MI L Q lo G s -> Forall (rwf Q) rs ->
      g_susp nctx Q G e1 c1.(c_term) t1 -> gcok G c1 ->
      g_susp nctx Q G e2 c2.(c_term) t2 -> gcok G c2 ->
      conv_same_code X_type X Γ nctx stress d L e1 c1 e2 c2 rs s = COk (b, rs', s') ->
      c1.(c_term) = c2.(c_term) /\ post L Q G rs s' rs' /\ (b = true -> cq L Q pb t1 t2).
  Proof.
    intros hS L Q lo G pb e1 c1 e2 c2 t1 t2 rs s b rs' s' hsid hm hr hs1 hc1 hs2 hc2 he.
    split.
    - destruct hc1 as [ce1 [hg1 hi1]]. destruct hc2 as [ce2 [hg2 hi2]].
      exact (same_id_sound_table _ ce1 ce2 c1 c2 hsid hg1 hi1 hg2 hi2).
    - exact (conv_same_code_sound_ghost d hS L Q lo G pb e1 c1 e2 c2 t1 t2 rs s b rs' s'
               hm hr hs1 hc1 hs2 hc2 he).
  Qed.

  (** The same-code rule read for a fixpoint value: fixpoint [i] of the two [tFix] codes. *)
  Lemma cagree_fix L Q m idx idx' i l1 l2 :
    cagree L Q (tFix m idx) i l1 l2 -> cagree L Q (tFix m idx') i l1 l2.
  Proof. induction 1; constructor; [exact H|exact IHcagree]. Qed.

  Lemma samec_fix m1 m2 idx1 idx2 i :
    samec (tFix m1 idx1) (tFix m2 idx2) -> samec (tFix m1 i) (tFix m2 i).
  Proof.
    intros [e|[h]]; [injection e as -> _; left; reflexivity|right; constructor].
    inversion h; subst. constructor. assumption.
  Qed.

  (** ** [conv_slot] *)

  Lemma conv_slot_eq k L le x1 x2 rs s :
    conv_slot X_type X Γ nctx stress (FS k) L le x1 x2 rs s =
    match x1, x2 with
    | SAddr a1, SAddr a2 =>
      if haddr_eqb a1 a2 then COk (true, rs, s)
      else conv_eval X_type X Γ nctx stress (k tt) L le x1 x2 rs s
    | SInl vs1 n1 o1 c1, SInl vs2 n2 o2 c2 =>
      match conv_same_code X_type X Γ nctx stress (k tt) L (mkEnv vs1 n1 o1) c1
              (mkEnv vs2 n2 o2) c2 (RSl x1 :: RSl x2 :: rs) s with
      | COk (b, rs, s) =>
        match rs with
        | RSl x1 :: RSl x2 :: rs =>
          if b then COk (true, rs, s)
          else conv_eval X_type X Γ nctx stress (k tt) L le x1 x2 rs s
        | _ => CFail WRoots
        end
      | CFail w => CFail w
      end
    | _, _ => conv_eval X_type X Γ nctx stress (k tt) L le x1 x2 rs s
    end.
  Proof. reflexivity. Qed.

  Lemma conv_slot_sound_g (k : unit -> cbn_fuel) :
    spec_eval (k tt) -> spec_same (k tt) -> spec_slot (FS k).
  Proof.
    intros hE hS L Q lo G pb x1 x2 t1 t2 rs s b rs' s' hm hr hx1 hx2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite conv_slot_eq in he.
    destruct x1 as [a1|vs1 n1 o1 c1]; destruct x2 as [a2|vs2 n2 o2 c2];
      cbv beta iota in he;
      try exact (hE L Q lo G pb _ _ t1 t2 rs s b rs' s' hm hr hx1 hx2 he).
    - destruct (haddr_eqb a1 a2) eqn:Ea;
        [|exact (hE L Q lo G pb _ _ t1 t2 rs s b rs' s' hm hr hx1 hx2 he)].
      injection he as <- <- <-. split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros _.
      apply haddr_eqb_eq in Ea. subst a2.
      apply g_slot_addr_inv in hx1. apply g_slot_addr_inv in hx2.
      rewrite hx1 in hx2. injection hx2 as <-. exact (cq_refl _ _ _ _ hL).
    - assert (hs1 : g_susp nctx Q G (mkEnv vs1 n1 o1) c1.(c_term) t1)
        by (eapply g_slot_inl_inv; exact hx1).
      assert (hc1 : gcok G c1) by (eapply g_slot_inl_cok; exact hx1).
      assert (hs2 : g_susp nctx Q G (mkEnv vs2 n2 o2) c2.(c_term) t2)
        by (eapply g_slot_inl_inv; exact hx2).
      assert (hc2 : gcok G c2) by (eapply g_slot_inl_cok; exact hx2).
      destruct (conv_same_code X_type X Γ nctx stress (k tt) L (mkEnv vs1 n1 o1) c1
                  (mkEnv vs2 n2 o2) c2 (RSl (SInl vs1 n1 o1 c1) :: RSl (SInl vs2 n2 o2 c2) :: rs) s)
        as [[[b0 rs0] s0]|w] eqn:Ecs; [|discriminate he].
      destruct (conv_same_code_sound_ghost (k tt) hS L Q lo G pb _ c1 _ c2 t1 t2 _ s b0 rs0 s0
                  hm (Forall_cons (RSl _) I (Forall_cons (RSl _) I hr)) hs1 hc1 hs2 hc2 Ecs)
        as [hp0 hc0].
      destruct hp0 as (Q1 & lo1 & G1 & hq1 & hm1 & hr1 & hg1).
      destruct (grq_cons_inv _ _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hqa & hgA).
      destruct (gpq_RSl_inv _ _ _ _ _ _ hqa) as (y1 & -> & hk1).
      destruct (grq_cons_inv _ _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hqb & hgB).
      destruct (gpq_RSl_inv _ _ _ _ _ _ hqb) as (y2 & -> & hk2).
      cbv beta iota in he.
      destruct b0.
      + injection he as <- <- <-.
        split; [|intros _; exact (hc0 eq_refl)].
        exists Q1, lo1, G1. split; [exact hq1|]. split; [exact hm1|].
        split; [exact (Forall_inv_tail (Forall_inv_tail hr1))|exact hgB].
      + destruct (hE L Q1 lo1 G1 pb y1 y2 _ _ rsB s0 b rs' s' hm1
                    (Forall_inv_tail (Forall_inv_tail hr1)) (hk1 _ hx1) (hk2 _ hx2) he)
          as [hp hc].
        split; [exact (post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
        intros hb. exact (cq_lift _ _ _ _ _ _ hLQ hq1 (hc hb)).
  Qed.

  (** ** Crossing a binder: the lambda and product rows *)

  Lemma minv_level L L' Q lo G s : MI L Q lo G s -> nctx <= L' -> L' <= Q -> MI L' Q lo G s.
  Proof. intros [hL hQ hok hw] h1 h2. constructor; assumption. Qed.

  (** The body of a code read through slots lifted by [d] is the lift by [d] at the cut [k]. *)
  Lemma lift_bodyk d ts N n k t :
    #|ts| = n ->
    subst (map (lift0 d) ts) k (lift (d + N) (k + n) t) = lift d k (subst ts k (lift N (k + n) t)).
  Proof.
    intros hl. pose proof (distr_lift_subst_rec (lift N (k + n) t) ts d k 0) as h.
    rewrite !Nat.add_0_r in h. rewrite h. f_equal. rewrite hl.
    symmetry. apply simpl_lift; lia.
  Qed.

  Lemma subst_rel_lift1 j U : subst [tRel j] 0 (lift (S j) 1 U) = lift0 j U.
  Proof.
    pose proof (cg_subst_fresh_lift j 1 U) as h.
    replace (map (lift0 j) (idsn 1)) with [tRel j] in h
      by (cbn; rewrite Nat.add_0_r; reflexivity).
    rewrite Nat.add_1_r in h. exact h.
  Qed.

  (** After the domains: one fresh variable at level [L], pushed on both environments, then
    the bodies at [S L]. *)
  Definition binder_tail (d : cbn_fuel) (L : nat) (pb : conv_pb) (e1 e2 : cbn_env)
      (cb1 cb2 : code) (rs : list root) (s : cbn_state) :=
    match alloc stress (CDone (VNeu (NVar L) [])) (RE e1 :: RE e2 :: rs) s with
    | COk (x, rs, s) =>
      match rs with
      | RE e1 :: RE e2 :: rs =>
        conv_term X_type X Γ nctx stress d (S L) pb (env_push (SAddr x) e1) cb1
          (env_push (SAddr x) e2) cb2 rs s
      | _ => CFail WRoots
      end
    | CFail w => CFail w
    end.

  Lemma binder_tail_g (k : unit -> cbn_fuel) (hT : spec_term (k tt))
      L Q lo G pb e1 e2 cb1 cb2 ts1 ts2 rs s b rs' s' :
    MI L Q lo G s -> Forall (rwf Q) rs ->
    g_slots nctx Q G e1.(ev_vals) ts1 -> e1.(ev_nvals) = #|e1.(ev_vals)| ->
    g_slots nctx Q G e2.(ev_vals) ts2 -> e2.(ev_nvals) = #|e2.(ev_vals)| ->
    gcok G cb1 -> gcok G cb2 ->
    binder_tail (k tt) L pb e1 e2 cb1 cb2 rs s = COk (b, rs', s') ->
    post L Q G rs s' rs' /\
    (b = true -> cqb L Q 1 pb
       (subst ts1 1 (lift (Q - nctx + e1.(ev_goff)) (S e1.(ev_nvals)) cb1.(c_term)))
       (subst ts2 1 (lift (Q - nctx + e2.(ev_goff)) (S e2.(ev_nvals)) cb2.(c_term)))).
  Proof.
    intros hm hr hs1 hn1 hs2 hn2 hc1 hc2 he.
    pose proof hm as [hL hLQ _ _].
    pose proof (minv_raise L Q 1 lo G s hm) as hmR.
    pose proof (rwfs_mono Q (Q + 1) rs ltac:(lia) hr) as hrR.
    pose proof (grq_raise Q 1 G rs ltac:(lia) hr) as hgR.
    pose proof (proj2 (g_slot_shift nctx Q 1 ltac:(lia) G) _ _ hs1) as [hs1R _].
    pose proof (proj2 (g_slot_shift nctx Q 1 ltac:(lia) G) _ _ hs2) as [hs2R _].
    unfold binder_tail in he.
    destruct (alloc stress (CDone (VNeu (NVar L) [])) (RE e1 :: RE e2 :: rs) s)
      as [[[x rs1] s1]|w] eqn:Ea; [|discriminate he].
    destruct (alloc_fresh_g L (Q + 1) lo (gshift 1 G) L _ s x rs1 s1 hmR
                (Forall_cons (RE e1) I (Forall_cons (RE e2) I hrR)) ltac:(lia) Ea)
      as (lo1 & G1 & hm1 & hr1 & hg1 & hx).
    destruct (gren_cons_inv _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hq1 & hgA).
    destruct (gpres_RE_inv _ _ _ _ _ hq1) as (f1 & -> & (hn1' & hg1' & hk1)).
    destruct (gren_cons_inv _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hq2 & hgB).
    destruct (gpres_RE_inv _ _ _ _ _ hq2) as (f2 & -> & (hn2' & hg2' & hk2)).
    cbv beta iota in he.
    pose proof (hk1 _ hs1R) as hf1. pose proof (hk2 _ hs2R) as hf2.
    pose proof (g_slots_length _ _ _ _ _ hs1) as hl1.
    pose proof (g_slots_length _ _ _ _ _ hf1) as hl1'. rewrite length_map in hl1'.
    pose proof (g_slots_length _ _ _ _ _ hs2) as hl2.
    pose proof (g_slots_length _ _ _ _ _ hf2) as hl2'. rewrite length_map in hl2'.
    set (j := Q + 1 - S L).
    assert (hb1 : g_susp nctx (Q + 1) G1 (env_push (SAddr x) f1) cb1.(c_term)
                    (subst (tRel j :: map (lift0 1) ts1) 0
                       (lift (Q + 1 - nctx + ev_goff e1) (S (ev_nvals e1)) cb1.(c_term)))).
    { rewrite <- hg1', <- hn1'. apply (g_susp_of_slots _ _ _ (env_push (SAddr x) f1)).
      - cbn. constructor; [constructor; exact hx|exact hf1].
      - cbn. lia. }
    assert (hb2 : g_susp nctx (Q + 1) G1 (env_push (SAddr x) f2) cb2.(c_term)
                    (subst (tRel j :: map (lift0 1) ts2) 0
                       (lift (Q + 1 - nctx + ev_goff e2) (S (ev_nvals e2)) cb2.(c_term)))).
    { rewrite <- hg2', <- hn2'. apply (g_susp_of_slots _ _ _ (env_push (SAddr x) f2)).
      - cbn. constructor; [constructor; exact hx|exact hf2].
      - cbn. lia. }
    destruct (hT (S L) (Q + 1) lo1 G1 pb _ cb1 _ cb2 _ _ rsB s1 b rs' s'
                (minv_level L (S L) (Q + 1) lo1 G1 s1 hm1 ltac:(lia) ltac:(lia))
                (Forall_inv_tail (Forall_inv_tail hr1)) hb1 (cok_gcx _ _ (proj1 hg1) _ hc1)
                hb2 (cok_gcx _ _ (proj1 hg1) _ hc2) he) as [hp hc].
    split.
    - apply (post_compose L Q (Q + 1) G (gshift 1 G) rs rs s' rs' ltac:(lia) hgR).
      apply (post_compose L (Q + 1) (Q + 1) (gshift 1 G) G1 rs rsB s' rs' (le_n _)
               (grq_of_gren _ _ _ _ _ hgB
                  (sk_tl _ _ _ _ (sk_tl _ _ _ _ (alloc_skel _ _ _ _ _ _ _ Ea))))).
      exact (post_level L (S L) (Q + 1) G1 rsB s' rs' hL ltac:(lia) hp).
    - intros hbt U1 U2 eU1 eU2 sU1 sU2.
      rewrite Nat.add_1_r in sU1, sU2 |- *.
      apply (hc hbt U1 U2); [| |exact sU1|exact sU2].
      + rewrite subst_cons_app.
        replace (Q + 1 - nctx + ev_goff e1) with (1 + (Q - nctx + ev_goff e1)) by lia.
        replace (S (ev_nvals e1)) with (1 + #|ts1|) by lia.
        rewrite lift_bodyk by reflexivity.
        replace (1 + #|ts1|) with (S (ev_nvals e1)) by lia. rewrite eU1.
        rewrite simpl_lift by lia. subst j.
        replace (1 + (Q - L)) with (S (Q + 1 - S L)) by lia. apply subst_rel_lift1.
      + rewrite subst_cons_app.
        replace (Q + 1 - nctx + ev_goff e2) with (1 + (Q - nctx + ev_goff e2)) by lia.
        replace (S (ev_nvals e2)) with (1 + #|ts2|) by lia.
        rewrite lift_bodyk by reflexivity.
        replace (1 + #|ts2|) with (S (ev_nvals e2)) by lia. rewrite eU2.
        rewrite simpl_lift by lia. subst j.
        replace (1 + (Q - L)) with (S (Q + 1 - S L)) by lia. apply subst_rel_lift1.
  Qed.

  Lemma cqb_lift (L Q Q' k : nat) (pb : conv_pb) (B1 B2 : term) :
    L <= Q -> Q <= Q' ->
    cqb L Q' k pb (lift (Q' - Q) k B1) (lift (Q' - Q) k B2) -> cqb L Q k pb B1 B2.
  Proof.
    intros hLQ hQ h U1 U2 e1 e2 s1 s2. apply h; [| |exact s1|exact s2].
    - rewrite e1, simpl_lift by lia. f_equal. lia.
    - rewrite e2, simpl_lift by lia. f_equal. lia.
  Qed.

  (** Domains at [Conv], then one fresh variable and the bodies at [pbb]. *)
  Lemma binder_step (k : unit -> cbn_fuel) (hT : spec_term (k tt))
      L Q lo G pbb e1 e2 c1 c2 A1 A2 b1 b2 ts1 ts2 rs s b rs' s' :
    MI L Q lo G s -> Forall (rwf Q) rs ->
    g_slots nctx Q G e1.(ev_vals) ts1 -> e1.(ev_nvals) = #|e1.(ev_vals)| ->
    g_slots nctx Q G e2.(ev_vals) ts2 -> e2.(ev_nvals) = #|e2.(ev_vals)| ->
    gcok G (child c1 0 A1) -> gcok G (child c2 0 A2) ->
    gcok G (child c1 1 b1) -> gcok G (child c2 1 b2) ->
    match conv_term X_type X Γ nctx stress (k tt) L Conv e1 (child c1 0 A1) e2 (child c2 0 A2)
            (RE e1 :: RE e2 :: rs) s with
    | COk (true, rs, s) =>
      match rs with
      | RE e1 :: RE e2 :: rs => binder_tail (k tt) L pbb e1 e2 (child c1 1 b1) (child c2 1 b2) rs s
      | _ => CFail WRoots
      end
    | COk (false, rs, s) => COk (false, skipn 2 rs, s)
    | CFail w => CFail w
    end = COk (b, rs', s') ->
    post L Q G rs s' rs' /\
    (b = true ->
     cq L Q Conv (subst ts1 0 (lift (Q - nctx + e1.(ev_goff)) e1.(ev_nvals) A1))
                 (subst ts2 0 (lift (Q - nctx + e2.(ev_goff)) e2.(ev_nvals) A2))
     /\ cqb L Q 1 pbb (subst ts1 1 (lift (Q - nctx + e1.(ev_goff)) (S e1.(ev_nvals)) b1))
                      (subst ts2 1 (lift (Q - nctx + e2.(ev_goff)) (S e2.(ev_nvals)) b2))).
  Proof.
    intros hm hr hs1 hn1 hs2 hn2 hcA1 hcA2 hcB1 hcB2 he.
    pose proof hm as [hL hLQ _ _].
    destruct (conv_term X_type X Γ nctx stress (k tt) L Conv e1 (child c1 0 A1) e2 (child c2 0 A2)
                (RE e1 :: RE e2 :: rs) s) as [[[bA rsA] sA]|w] eqn:EA; [|discriminate he].
    destruct (hT L Q lo G Conv e1 (child c1 0 A1) e2 (child c2 0 A2) _ _ _ s bA rsA sA hm
                (Forall_cons (RE e1) I (Forall_cons (RE e2) I hr))
                (g_susp_of_slots _ _ _ e1 A1 ts1 hs1 hn1) hcA1
                (g_susp_of_slots _ _ _ e2 A2 ts2 hs2 hn2) hcA2 EA) as [hpA hcA].
    destruct bA.
    - destruct hpA as (QA & loA & GA & hqA & hmA & hrA & hgA).
      destruct (grq_cons_inv _ _ _ _ _ _ _ hgA) as (q1 & rsA1 & -> & hqa & hgA1).
      destruct (gpq_RE_inv _ _ _ _ _ _ hqa) as (f1 & -> & hnf1 & hgf1 & hkf1).
      destruct (grq_cons_inv _ _ _ _ _ _ _ hgA1) as (q2 & rsB & -> & hqb & hgB).
      destruct (gpq_RE_inv _ _ _ _ _ _ hqb) as (f2 & -> & hnf2 & hgf2 & hkf2).
      cbv beta iota in he.
      pose proof (hkf1 _ hs1) as hf1. pose proof (hkf2 _ hs2) as hf2.
      pose proof (g_slots_length _ _ _ _ _ hs1) as hl1.
      pose proof (g_slots_length _ _ _ _ _ hf1) as hl1'. rewrite length_map in hl1'.
      pose proof (g_slots_length _ _ _ _ _ hs2) as hl2.
      pose proof (g_slots_length _ _ _ _ _ hf2) as hl2'. rewrite length_map in hl2'.
      destruct (binder_tail_g k hT L QA loA GA pbb f1 f2 (child c1 1 b1) (child c2 1 b2)
                  _ _ rsB sA b rs' s' hmA (Forall_inv_tail (Forall_inv_tail hrA)) hf1
                  ltac:(lia) hf2 ltac:(lia)
                  (cok_gcx _ _ (proj1 hgA) _ hcB1) (cok_gcx _ _ (proj1 hgA) _ hcB2) he)
        as [hpB hcB].
      split; [exact (post_compose _ _ _ _ _ _ _ _ _ hqA hgB hpB)|].
      intros hb. split; [exact (hcA eq_refl)|].
      apply (cqb_lift L Q QA 1 pbb _ _ hLQ hqA).
      rewrite hnf1, hgf1, hnf2, hgf2 in hcB.
      replace (QA - nctx + ev_goff e1) with ((QA - Q) + (Q - nctx + ev_goff e1)) in hcB by lia.
      replace (QA - nctx + ev_goff e2) with ((QA - Q) + (Q - nctx + ev_goff e2)) in hcB by lia.
      replace (S (ev_nvals e1)) with (1 + #|ts1|) in hcB |- * by lia.
      replace (S (ev_nvals e2)) with (1 + #|ts2|) in hcB |- * by lia.
      rewrite !lift_bodyk in hcB by reflexivity. exact (hcB hb).
    - cbv beta iota in he. injection he as <- <- <-.
      split; [exact (post_drop2 _ _ _ _ _ _ _ _ hpA)|]. intros hb; discriminate hb.
  Qed.

  Lemma conv_rows_lam_eq k L le e1 c1 e2 c2 na1 A1 b1 na2 A2 b2 rs s :
    c1.(c_term) = tLambda na1 A1 b1 -> c2.(c_term) = tLambda na2 A2 b2 ->
    conv_rows X_type X Γ nctx stress (FS k) L le (VLam e1 c1) (VLam e2 c2) rs s =
    if eqb_binder_annot na1 na2 then
      match conv_term X_type X Γ nctx stress (k tt) L Conv e1 (child c1 0 A1) e2 (child c2 0 A2)
              (RE e1 :: RE e2 :: rs) s with
      | COk (true, rs, s) =>
        match rs with
        | RE e1 :: RE e2 :: rs =>
          binder_tail (k tt) L Conv e1 e2 (child c1 1 b1) (child c2 1 b2) rs s
        | _ => CFail WRoots
        end
      | COk (false, rs, s) => COk (false, skipn 2 rs, s)
      | CFail w => CFail w
      end
    else COk (false, rs, s).
  Proof. destruct c1 as [i1 p1 t1], c2 as [i2 p2 t2]. cbn. intros -> ->. reflexivity. Qed.

  Lemma conv_rows_prod_eq k L le e1 c1 e2 c2 na1 A1 b1 na2 A2 b2 rs s :
    c1.(c_term) = tProd na1 A1 b1 -> c2.(c_term) = tProd na2 A2 b2 ->
    conv_rows X_type X Γ nctx stress (FS k) L le (VOpen e1 c1) (VOpen e2 c2) rs s =
    if eqb_binder_annot na1 na2 then
      match conv_term X_type X Γ nctx stress (k tt) L Conv e1 (child c1 0 A1) e2 (child c2 0 A2)
              (RE e1 :: RE e2 :: rs) s with
      | COk (true, rs, s) =>
        match rs with
        | RE e1 :: RE e2 :: rs =>
          binder_tail (k tt) L le e1 e2 (child c1 1 b1) (child c2 1 b2) rs s
        | _ => CFail WRoots
        end
      | COk (false, rs, s) => COk (false, skipn 2 rs, s)
      | CFail w => CFail w
      end
    else COk (false, rs, s).
  Proof. destruct c1 as [i1 p1 t1], c2 as [i2 p2 t2]. cbn. intros -> ->. reflexivity. Qed.

  (** The logical context of a body: one more assumption. *)
  Lemma snoc_closed L Δ na A :
    nctx <= L -> #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) -> scl L A ->
    is_closed_context (Γ ,,, (Δ ,, vass na A)).
  Proof.
    intros hL hΔ hcl hA.
    change (Γ ,,, (Δ ,, vass na A)) with ((Γ ,,, Δ) ,, vass na A).
    rewrite on_free_vars_ctx_snoc, hcl. cbn. rewrite ?andb_true_r.
    exact (scl_open L Δ A hL hΔ hA).
  Qed.

  Lemma scl_binder L B : on_free_vars (shiftnP 1 (shiftnP L xpred0)) B -> scl (L + 1) B.
  Proof.
    intros h. unfold scl. rewrite (on_free_vars_ext _ _ _ (shiftnP_add _ _ _)) in h.
    rewrite Nat.add_comm. exact h.
  Qed.

  Lemma conv_rows_lam_g (k : unit -> cbn_fuel) :
    spec_term (k tt) ->
    spec_rows_on (FS k) (fun v1 v2 => exists e1 c1 e2 c2 na1 A1 b1 na2 A2 b2,
                           v1 = VLam e1 c1 /\ v2 = VLam e2 c2
                           /\ c1.(c_term) = tLambda na1 A1 b1 /\ c2.(c_term) = tLambda na2 A2 b2).
  Proof.
    intros hT L Q lo G pb v1 v2 w1 w2 rs s b rs' s'
      (e1 & c1 & e2 & c2 & na1 & A1 & b1 & na2 & A2 & b2 & -> & -> & h1 & h2)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite (conv_rows_lam_eq k L pb e1 c1 e2 c2 na1 A1 b1 na2 A2 b2 rs s h1 h2) in he.
    assert (hc1 : gcok G c1) by (eapply g_value_VLam_cok; exact hw1).
    assert (hc2 : gcok G c2) by (eapply g_value_VLam_cok; exact hw2).
    apply g_value_VLam_inv in hw1. apply g_value_VLam_inv in hw2.
    rewrite h1 in hw1. rewrite h2 in hw2.
    destruct (g_susp_inv _ _ _ _ _ _ hw1) as (ts1 & hts1 & hn1 & ->).
    destruct (g_susp_inv _ _ _ _ _ _ hw2) as (ts2 & hts2 & hn2 & ->).
    destruct (eqb_binder_annot na1 na2) eqn:Ena;
      [|injection he as <- <- <-;
        split; [exact (post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    destruct (binder_step k hT L Q lo G Conv e1 e2 c1 c2 A1 A2 b1 b2 ts1 ts2 rs s b rs' s'
                hm hr hts1 hn1 hts2 hn2
                (cok_child G c1 0 A1 hc1 ltac:(rewrite h1; constructor))
                (cok_child G c2 0 A2 hc2 ltac:(rewrite h2; constructor))
                (cok_child G c1 1 b1 hc1 ltac:(rewrite h1; constructor))
                (cok_child G c2 1 b2 hc2 ltac:(rewrite h2; constructor)) he) as [hp hc].
    split; [exact hp|]. intros hb. destruct (hc hb) as [hdom hbody].
    intros u1 u2 e1u e2u s1 s2 Δ hΔ hcl.
    cbn [lift subst] in e1u, e2u.
    destruct u1 as [| | | | |na1' A1u B1u| | | | | | | | | |]; cbn in e1u; try discriminate e1u.
    injection e1u as <- eA1 eB1.
    destruct u2 as [| | | | |na2' A2u B2u| | | | | | | | | |]; cbn in e2u; try discriminate e2u.
    injection e2u as <- eA2 eB2.
    unfold scl in s1, s2. cbn [on_free_vars] in s1, s2.
    apply andb_true_iff in s1 as [sA1 sB1]. apply andb_true_iff in s2 as [sA2 sB2].
    destruct (hdom A1u A2u eA1 eA2 sA1 sA2 Δ hΔ hcl) as [hd].
    assert (hΔ' : #|Δ ,, vass na1 A1u| = L + 1 - nctx) by (cbn; lia).
    destruct (hbody B1u B2u eB1 eB2 (scl_binder L B1u sB1) (scl_binder L B2u sB2)
                (Δ ,, vass na1 A1u) hΔ' (snoc_closed L Δ na1 A1u hL hΔ hcl sA1)) as [hbd].
    constructor.
    exact (ws_cumul_pb_Lambda (wfΣ := wfΣ) (eqb_binder_annot_spec _ _ Ena) hd hbd).
  Qed.

  Lemma conv_rows_prod_g (k : unit -> cbn_fuel) :
    spec_term (k tt) ->
    spec_rows_on (FS k) (fun v1 v2 => exists e1 c1 e2 c2 na1 A1 b1 na2 A2 b2,
                           v1 = VOpen e1 c1 /\ v2 = VOpen e2 c2
                           /\ c1.(c_term) = tProd na1 A1 b1 /\ c2.(c_term) = tProd na2 A2 b2).
  Proof.
    intros hT L Q lo G pb v1 v2 w1 w2 rs s b rs' s'
      (e1 & c1 & e2 & c2 & na1 & A1 & b1 & na2 & A2 & b2 & -> & -> & h1 & h2)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite (conv_rows_prod_eq k L pb e1 c1 e2 c2 na1 A1 b1 na2 A2 b2 rs s h1 h2) in he.
    assert (hc1 : gcok G c1) by (inversion hw1; assumption).
    assert (hc2 : gcok G c2) by (inversion hw2; assumption).
    apply g_value_VOpen_inv in hw1. apply g_value_VOpen_inv in hw2.
    rewrite h1 in hw1. rewrite h2 in hw2.
    destruct (g_susp_inv _ _ _ _ _ _ hw1) as (ts1 & hts1 & hn1 & ->).
    destruct (g_susp_inv _ _ _ _ _ _ hw2) as (ts2 & hts2 & hn2 & ->).
    destruct (eqb_binder_annot na1 na2) eqn:Ena;
      [|injection he as <- <- <-;
        split; [exact (post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    destruct (binder_step k hT L Q lo G pb e1 e2 c1 c2 A1 A2 b1 b2 ts1 ts2 rs s b rs' s'
                hm hr hts1 hn1 hts2 hn2
                (cok_child G c1 0 A1 hc1 ltac:(rewrite h1; constructor))
                (cok_child G c2 0 A2 hc2 ltac:(rewrite h2; constructor))
                (cok_child G c1 1 b1 hc1 ltac:(rewrite h1; constructor))
                (cok_child G c2 1 b2 hc2 ltac:(rewrite h2; constructor)) he) as [hp hc].
    split; [exact hp|]. intros hb. destruct (hc hb) as [hdom hbody].
    intros u1 u2 e1u e2u s1 s2 Δ hΔ hcl.
    cbn [lift subst] in e1u, e2u.
    destruct u1 as [| | | |na1' A1u B1u| | | | | | | | | | |]; cbn in e1u; try discriminate e1u.
    injection e1u as <- eA1 eB1.
    destruct u2 as [| | | |na2' A2u B2u| | | | | | | | | | |]; cbn in e2u; try discriminate e2u.
    injection e2u as <- eA2 eB2.
    unfold scl in s1, s2. cbn [on_free_vars] in s1, s2.
    apply andb_true_iff in s1 as [sA1 sB1]. apply andb_true_iff in s2 as [sA2 sB2].
    destruct (hdom A1u A2u eA1 eA2 sA1 sA2 Δ hΔ hcl) as [hd].
    assert (hΔ' : #|Δ ,, vass na1 A1u| = L + 1 - nctx) by (cbn; lia).
    destruct (hbody B1u B2u eB1 eB2 (scl_binder L B1u sB1) (scl_binder L B2u sB2)
                (Δ ,, vass na1 A1u) hΔ' (snoc_closed L Δ na1 A1u hL hΔ hcl sA1)) as [hbd].
    constructor.
    exact (ws_cumul_pb_Prod (wfΣ := wfΣ) pb (eqb_binder_annot_spec _ _ Ena) hd hbd).
  Qed.

  (** ** [conv_value]: same code first, then the rows *)

  Lemma minv_tick L Q lo G s s' : tick s = Some s' -> MI L Q lo G s -> MI L Q lo G s'.
  Proof.
    intros ht [hL hQ hok hw]. destruct (tick_shape s s' ht) as (h1 & h2 & _ & h4 & h5).
    constructor; [exact hL|exact hQ| |exact (hwf_heap Q s s' h1 hw)].
    apply (gok_same X_type X Γ nctx Σ _ Q lo G s); [exact hok|exact h1|exact h2|exact h4|].
    eapply mok_memo; [exact h5|exact (gk_memo _ _ _ _ _ _ _ _ _ _ hok)].
  Qed.

  Lemma mkApps_inj_len f f' l l' : #|l| = #|l'| -> mkApps f l = mkApps f' l' -> f = f' /\ l = l'.
  Proof.
    revert l'. induction l as [|a l ih] using rev_ind; intros l' hl e.
    - destruct l'; [|discriminate hl]. split; [exact e|reflexivity].
    - destruct l' as [|a' l' _] using rev_ind; [rewrite length_app in hl; cbn in hl; lia|].
      rewrite !mkApps_app in e. cbn in e. injection e as e1 e2.
      rewrite !length_app in hl. cbn in hl.
      destruct (ih l' ltac:(lia) e1) as [-> ->]. subst a'. split; reflexivity.
  Qed.

  (** Every value reads as a head applied to the readings of its spine. *)
  Lemma g_value_spine Q G v t :
    g_value nctx Q G v t -> exists H T, t = mkApps H T /\ g_addrs G (spine_of v) T.
  Proof.
    intros h. destruct h;
      first [ eexists _, _; split; [reflexivity|eassumption]
            | exists t, []; split; [reflexivity|constructor] ].
  Qed.

  (** A value renamed without reshaping keeps the readings of its spine. *)
  Lemma spine_reads Q Q' G G' v v' H T :
    (forall t, g_value nctx Q G v t -> g_value nctx Q' G' v' (lift0 (Q' - Q) t)) ->
    mp_value kc v' = mp_value kc v ->
    g_value nctx Q G v (mkApps H T) -> g_addrs G (spine_of v) T ->
    g_addrs G' (spine_of v') (map (lift0 (Q' - Q)) T).
  Proof.
    intros hk hs hw hT.
    destruct (g_value_spine _ _ _ _ (hk _ hw)) as (H' & T' & e & hT').
    rewrite lift_mkApps in e.
    pose proof (f_equal (@length _) (f_equal spine_of hs)) as hl.
    rewrite !mp_spine_of, !length_map in hl.
    assert (hl' : #|map (lift0 (Q' - Q)) T| = #|T'|).
    { rewrite length_map, (g_addrs_length _ _ _ hT), (g_addrs_length _ _ _ hT'). lia. }
    destruct (mkApps_inj_len _ _ _ _ hl' e) as [_ <-]. exact hT'.
  Qed.

  Lemma cq_mkApps L Q pb H1 H2 T1 T2 :
    nctx <= L -> cq L Q pb H1 H2 -> cqs L Q T1 T2 -> cq L Q pb (mkApps H1 T1) (mkApps H2 T2).
  Proof.
    intros hL hh hs u1 u2 e1 e2 s1 s2.
    apply mkApps_lift0_inv in e1 as (h1' & us1 & -> & eh1 & ->).
    apply mkApps_lift0_inv in e2 as (h2' & us2 & -> & eh2 & ->).
    unfold scl in s1, s2. rewrite on_free_vars_mkApps in s1, s2.
    apply andb_true_iff in s1 as [sh1 sus1]. apply andb_true_iff in s2 as [sh2 sus2].
    apply cv_spine; [exact hL| |exact (hs us1 us2 eq_refl eq_refl sus1 sus2)].
    exact (hh h1' h2' eh1 eh2 sh1 sh2).
  Qed.

  Definition cv_same (d : cbn_fuel) (L : nat) (le : conv_pb) (v1 v2 : cbn_value)
      (e1 : cbn_env) (c1 : code) (e2 : cbn_env) (c2 : code) (spines : bool)
      (rs : list root) (s : cbn_state) :=
    match conv_same_code X_type X Γ nctx stress d L e1 c1 e2 c2 (RV v1 :: RV v2 :: rs) s with
    | COk (b, rs, s) =>
      match rs with
      | RV v1 :: RV v2 :: rs =>
        if b then
          if spines then conv_cells X_type X Γ nctx stress d L (spine_of v1) (spine_of v2) rs s
          else COk (true, rs, s)
        else conv_rows X_type X Γ nctx stress d L le v1 v2 rs s
      | _ => CFail WRoots
      end
    | CFail w => CFail w
    end.

  Lemma conv_value_eq k L le v1 v2 rs s :
    conv_value X_type X Γ nctx stress (FS k) L le v1 v2 rs s =
    match tick s with
    | None => CFail WSteps
    | Some s =>
      match v1, v2 with
      | VLam e1 c1, VLam e2 c2 | VOpen e1 c1, VOpen e2 c2 =>
        cv_same (k tt) L le v1 v2 e1 c1 e2 c2 false rs s
      | VStuck e1 c1 sp1, VStuck e2 c2 sp2 =>
        if #|sp1| == #|sp2| then cv_same (k tt) L le v1 v2 e1 c1 e2 c2 true rs s
        else conv_rows X_type X Γ nctx stress (k tt) L le v1 v2 rs s
      | VFix e1 c1 i1 sp1, VFix e2 c2 i2 sp2
      | VStuckFix e1 c1 i1 sp1, VStuckFix e2 c2 i2 sp2 =>
        if (i1 == i2) && (#|sp1| == #|sp2|) then cv_same (k tt) L le v1 v2 e1 c1 e2 c2 true rs s
        else conv_rows X_type X Γ nctx stress (k tt) L le v1 v2 rs s
      | _, _ => conv_rows X_type X Γ nctx stress (k tt) L le v1 v2 rs s
      end
    end.
  Proof. cbn. destruct (tick s); [|reflexivity]. destruct v1, v2; reflexivity. Qed.

  (** Closures and open values: the same code makes the two readings convertible. *)
  Lemma cv_same_flat (k : unit -> cbn_fuel) :
    spec_same (k tt) -> spec_rows (k tt) ->
    forall L Q lo G pb v1 v2 w1 w2 e1 c1 e2 c2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs -> vwf Q v1 -> vwf Q v2 ->
      g_value nctx Q G v1 w1 -> g_value nctx Q G v2 w2 ->
      g_susp nctx Q G e1 c1.(c_term) w1 -> gcok G c1 ->
      g_susp nctx Q G e2 c2.(c_term) w2 -> gcok G c2 ->
      cv_same (k tt) L pb v1 v2 e1 c1 e2 c2 false rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cq L Q pb w1 w2).
  Proof.
    intros hS hR L Q lo G pb v1 v2 w1 w2 e1 c1 e2 c2 rs s b rs' s' hm hr hv1 hv2 hw1 hw2
      hs1 hc1 hs2 hc2 he.
    pose proof hm as [hL hLQ _ _].
    unfold cv_same in he.
    destruct (conv_same_code X_type X Γ nctx stress (k tt) L e1 c1 e2 c2 (RV v1 :: RV v2 :: rs) s)
      as [[[b0 rs0] s0]|w] eqn:E; [|discriminate he].
    destruct (conv_same_code_sound_ghost (k tt) hS L Q lo G pb e1 c1 e2 c2 w1 w2 _ s b0 rs0 s0
                hm (Forall_cons (RV v1) hv1 (Forall_cons (RV v2) hv2 hr)) hs1 hc1 hs2 hc2 E)
      as [hp0 hc0].
    destruct hp0 as (Q1 & lo1 & G1 & hq1 & hm1 & hr1 & hg1).
    destruct (grq_cons_inv _ _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hqa & hgA).
    destruct (gpq_RV_inv _ _ _ _ _ _ hqa) as (v1' & -> & hk1).
    destruct (grq_cons_inv _ _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hqb & hgB).
    destruct (gpq_RV_inv _ _ _ _ _ _ hqb) as (v2' & -> & hk2).
    cbv beta iota in he.
    destruct b0.
    - injection he as <- <- <-. split; [|intros _; exact (hc0 eq_refl)].
      exists Q1, lo1, G1. split; [exact hq1|]. split; [exact hm1|].
      split; [exact (Forall_inv_tail (Forall_inv_tail hr1))|exact hgB].
    - destruct (hR L Q1 lo1 G1 pb v1' v2' _ _ rsB s0 b rs' s' I hm1
                  (Forall_inv_tail (Forall_inv_tail hr1)) (Forall_inv hr1)
                  (Forall_inv (Forall_inv_tail hr1)) (hk1 _ hw1) (hk2 _ hw2) he) as [hp hc].
      split; [exact (post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
      intros hb. exact (cq_lift _ _ _ _ _ _ hLQ hq1 (hc hb)).
  Qed.

  (** Stuck terms and fixpoints: the same code makes the heads convertible, then the spines are
    compared; the renamed values keep their shape, so their spines read as before. *)
  Lemma cv_same_spine (k : unit -> cbn_fuel) :
    spec_same (k tt) -> spec_cells (k tt) -> spec_rows (k tt) ->
    forall L Q lo G pb v1 v2 H1 H2 T1 T2 e1 c1 e2 c2 ts1 ts2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs -> vwf Q v1 -> vwf Q v2 ->
      g_value nctx Q G v1 (mkApps H1 T1) -> g_value nctx Q G v2 (mkApps H2 T2) ->
      g_addrs G (spine_of v1) T1 -> g_addrs G (spine_of v2) T2 ->
      gcok G c1 -> gcok G c2 ->
      g_slots nctx Q G e1.(ev_vals) ts1 -> g_slots nctx Q G e2.(ev_vals) ts2 ->
      (e1.(ev_goff) = e2.(ev_goff) -> e1.(ev_nvals) = e2.(ev_nvals) ->
       samec c1.(c_term) c2.(c_term) -> cagree L Q c1.(c_term) 0 ts1 ts2 -> cq L Q pb H1 H2) ->
      cv_same (k tt) L pb v1 v2 e1 c1 e2 c2 true rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cq L Q pb (mkApps H1 T1) (mkApps H2 T2)).
  Proof.
    intros hS hC hR L Q lo G pb v1 v2 H1 H2 T1 T2 e1 c1 e2 c2 ts1 ts2 rs s b rs' s'
      hm hr hv1 hv2 hw1 hw2 hT1 hT2 hc1 hc2 hts1 hts2 hhead he.
    pose proof hm as [hL hLQ _ _].
    unfold cv_same in he.
    destruct (conv_same_code X_type X Γ nctx stress (k tt) L e1 c1 e2 c2 (RV v1 :: RV v2 :: rs) s)
      as [[[b0 rs0] s0]|w] eqn:E; [|discriminate he].
    destruct (hS L Q lo G e1 c1 e2 c2 ts1 ts2 _ s b0 rs0 s0 hm
                (Forall_cons (RV v1) hv1 (Forall_cons (RV v2) hv2 hr)) hc1 hc2 hts1 hts2 E)
      as [hp0 hc0].
    destruct hp0 as (Q1 & lo1 & G1 & hq1 & hm1 & hr1 & hg1).
    destruct (grq_cons_inv_skel _ _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hqa & hgA & hsk1).
    destruct (gpq_RV_inv _ _ _ _ _ _ hqa) as (v1' & -> & hk1).
    destruct (grq_cons_inv_skel _ _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hqb & hgB & hsk2).
    destruct (gpq_RV_inv _ _ _ _ _ _ hqb) as (v2' & -> & hk2).
    cbn in hsk1, hsk2. injection hsk1 as hsk1. injection hsk2 as hsk2.
    cbv beta iota in he.
    destruct b0.
    - destruct (hc0 eq_refl) as (hgo & hnv & hsame & hag).
      destruct (hC L Q1 lo1 G1 (spine_of v1') (spine_of v2') _ _ rsB s0 b rs' s' hm1
                  (Forall_inv_tail (Forall_inv_tail hr1))
                  (spine_reads Q Q1 G G1 v1 v1' H1 T1 hk1 hsk1 hw1 hT1)
                  (spine_reads Q Q1 G G1 v2 v2' H2 T2 hk2 hsk2 hw2 hT2) he) as [hp hc].
      split; [exact (post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
      intros hb. apply (cq_mkApps L Q pb H1 H2 T1 T2 hL (hhead hgo hnv hsame hag)).
      exact (cqs_lift _ _ _ _ _ hLQ hq1 (hc hb)).
    - destruct (hR L Q1 lo1 G1 pb v1' v2' _ _ rsB s0 b rs' s' I hm1
                  (Forall_inv_tail (Forall_inv_tail hr1)) (Forall_inv hr1)
                  (Forall_inv (Forall_inv_tail hr1)) (hk1 _ hw1) (hk2 _ hw2) he) as [hp hc].
      split; [exact (post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
      intros hb. exact (cq_lift _ _ _ _ _ _ hLQ hq1 (hc hb)).
  Qed.

  Lemma conv_value_sound_g (k : unit -> cbn_fuel) :
    spec_same (k tt) -> spec_cells (k tt) -> spec_rows (k tt) -> spec_value (FS k).
  Proof.
    intros hS hC hR L Q lo G pb v1 v2 w1 w2 rs s b rs' s' hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ hok _].
    rewrite conv_value_eq in he.
    destruct (tick s) as [s0|] eqn:Et; [|discriminate he].
    pose proof (minv_tick _ _ _ _ _ _ Et hm) as hm0.
    pose proof (gok_codes_hyg X_type X Γ nctx Σ _ Q lo G s hok hhyg) as hch.
    assert (hrows : conv_rows X_type X Γ nctx stress (k tt) L pb v1 v2 rs s0 = COk (b, rs', s') ->
              post L Q G rs s' rs' /\ (b = true -> cq L Q pb w1 w2))
      by (intros h; exact (hR L Q lo G pb v1 v2 w1 w2 rs s0 b rs' s' I hm0 hr hv1 hv2 hw1 hw2 h)).
    destruct v1 as [h1 sp1|e1 c1|e1 c1 i1 sp1|e1 c1 i1 sp1|n1 sp1|e1 c1|e1 c1 sp1];
    destruct v2 as [h2 sp2|e2 c2|e2 c2 i2 sp2|e2 c2 i2 sp2|n2 sp2|e2 c2|e2 c2 sp2];
      cbv beta iota in he; try exact (hrows he).
    - (* closures *)
      exact (cv_same_flat k hS hR L Q lo G pb _ _ w1 w2 e1 c1 e2 c2 rs s0 b rs' s' hm0 hr hv1 hv2
               hw1 hw2 (g_value_VLam_inv _ _ _ _ _ _ hw1) (g_value_VLam_cok _ _ _ _ _ _ hw1)
               (g_value_VLam_inv _ _ _ _ _ _ hw2) (g_value_VLam_cok _ _ _ _ _ _ hw2) he).
    - (* fixpoints *)
      destruct ((i1 == i2) && (#|sp1| == #|sp2|)) eqn:Ei; [|exact (hrows he)].
      apply andb_true_iff in Ei as [Ei _]. apply eqb_eq in Ei. subst i2.
      pose proof hw1 as hw1'. pose proof hw2 as hw2'.
      apply g_value_VFix_inv in hw1' as (m1 & idx1 & H1 & T1 & hct1 & hh1 & hc1 & hT1 & ->).
      apply g_value_VFix_inv in hw2' as (m2 & idx2 & H2 & T2 & hct2 & hh2 & hc2 & hT2 & ->).
      destruct (g_susp_inv _ _ _ _ _ _ hh1) as (ts1 & hts1 & hn1 & ->).
      destruct (g_susp_inv _ _ _ _ _ _ hh2) as (ts2 & hts2 & hn2 & ->).
      apply (cv_same_spine k hS hC hR L Q lo G pb _ _ _ _ T1 T2 e1 c1 e2 c2 ts1 ts2 rs s0 b rs' s'
               hm0 hr hv1 hv2 hw1 hw2 hT1 hT2 hc1 hc2 hts1 hts2); [|exact he].
      intros hgo hnv hsame hag. rewrite hct1, hct2 in hsame. rewrite hct1 in hag.
      pose proof (g_slots_length _ _ _ _ _ hts1) as hl1.
      pose proof (g_slots_length _ _ _ _ _ hts2) as hl2.
      rewrite <- hgo, <- hnv.
      apply (same_code_cq L Q pb (ev_nvals e1) (ev_goff e1) ts1 ts2 _ _ hL hLQ);
        [lia|lia| | |exact (samec_fix _ _ _ _ _ hsame)|exact (cagree_fix _ _ _ _ _ _ _ _ hag)].
      + apply (hyg_tFix_idx _ idx1). rewrite <- hct1. exact (hch _ hc1).
      + apply (hyg_tFix_idx _ idx2). rewrite <- hct2. exact (hch _ hc2).
    - (* stuck fixpoints *)
      destruct ((i1 == i2) && (#|sp1| == #|sp2|)) eqn:Ei; [|exact (hrows he)].
      apply andb_true_iff in Ei as [Ei _]. apply eqb_eq in Ei. subst i2.
      pose proof hw1 as hw1'. pose proof hw2 as hw2'.
      apply g_value_VStuckFix_inv in hw1' as (m1 & idx1 & H1 & T1 & hct1 & hh1 & hc1 & hT1 & ->).
      apply g_value_VStuckFix_inv in hw2' as (m2 & idx2 & H2 & T2 & hct2 & hh2 & hc2 & hT2 & ->).
      destruct (g_susp_inv _ _ _ _ _ _ hh1) as (ts1 & hts1 & hn1 & ->).
      destruct (g_susp_inv _ _ _ _ _ _ hh2) as (ts2 & hts2 & hn2 & ->).
      apply (cv_same_spine k hS hC hR L Q lo G pb _ _ _ _ T1 T2 e1 c1 e2 c2 ts1 ts2 rs s0 b rs' s'
               hm0 hr hv1 hv2 hw1 hw2 hT1 hT2 hc1 hc2 hts1 hts2); [|exact he].
      intros hgo hnv hsame hag. rewrite hct1, hct2 in hsame. rewrite hct1 in hag.
      pose proof (g_slots_length _ _ _ _ _ hts1) as hl1.
      pose proof (g_slots_length _ _ _ _ _ hts2) as hl2.
      rewrite <- hgo, <- hnv.
      apply (same_code_cq L Q pb (ev_nvals e1) (ev_goff e1) ts1 ts2 _ _ hL hLQ);
        [lia|lia| | |exact (samec_fix _ _ _ _ _ hsame)|exact (cagree_fix _ _ _ _ _ _ _ _ hag)].
      + apply (hyg_tFix_idx _ idx1). rewrite <- hct1. exact (hch _ hc1).
      + apply (hyg_tFix_idx _ idx2). rewrite <- hct2. exact (hch _ hc2).
    - (* open values *)
      exact (cv_same_flat k hS hR L Q lo G pb _ _ w1 w2 e1 c1 e2 c2 rs s0 b rs' s' hm0 hr hv1 hv2
               hw1 hw2 (g_value_VOpen_inv _ _ _ _ _ _ hw1) ltac:(inversion hw1; assumption)
               (g_value_VOpen_inv _ _ _ _ _ _ hw2) ltac:(inversion hw2; assumption) he).
    - (* stuck matches and projections *)
      destruct (#|sp1| == #|sp2|) eqn:Ei; [|exact (hrows he)].
      pose proof hw1 as hw1'. pose proof hw2 as hw2'.
      apply g_value_VStuck_inv in hw1' as (H1 & T1 & hh1 & hT1 & ->).
      apply g_value_VStuck_inv in hw2' as (H2 & T2 & hh2 & hT2 & ->).
      destruct (g_susp_inv _ _ _ _ _ _ hh1) as (ts1 & hts1 & hn1 & ->).
      destruct (g_susp_inv _ _ _ _ _ _ hh2) as (ts2 & hts2 & hn2 & ->).
      pose proof (g_value_VStuck_cok _ _ _ _ _ _ _ hw1) as hc1.
      pose proof (g_value_VStuck_cok _ _ _ _ _ _ _ hw2) as hc2.
      apply (cv_same_spine k hS hC hR L Q lo G pb _ _ _ _ T1 T2 e1 c1 e2 c2 ts1 ts2 rs s0 b rs' s'
               hm0 hr hv1 hv2 hw1 hw2 hT1 hT2 hc1 hc2 hts1 hts2); [|exact he].
      intros hgo hnv hsame hag.
      pose proof (g_slots_length _ _ _ _ _ hts1) as hl1.
      pose proof (g_slots_length _ _ _ _ _ hts2) as hl2.
      rewrite <- hgo, <- hnv.
      apply (same_code_cq L Q pb (ev_nvals e1) (ev_goff e1) ts1 ts2 _ _ hL hLQ);
        [lia|lia|exact (hch _ hc1)|exact (hch _ hc2)|exact hsame|exact hag].
  Qed.

  (** ** The stuck-match rule: the branches *)

  Lemma rbody_lift d ts N br :
    rbody (map (lift0 d) ts) (d + N) br = lift d #|br.(bcontext)| (rbody ts N br).
  Proof. unfold rbody. rewrite length_map. apply lift_bodyk. reflexivity. Qed.

  (** A branch body read through [n] fresh variables pushed on its environment, at the master
    level, is the lift of the logical body. *)
  Lemma fresh_branch_read L Q n N ts t U :
    L <= Q ->
    subst ts n (lift N (n + #|ts|) t) = lift (Q - L) n U ->
    subst (map (lift0 (Q - L)) (idsn n) ++ map (lift0 n) ts) 0 (lift (n + N) (n + #|ts|) t)
    = lift0 (Q - L) U.
  Proof.
    intros hLQ e.
    rewrite subst_app_simpl, length_map, idsn_length. cbn [Nat.add].
    rewrite (lift_bodyk n ts N #|ts| n t eq_refl), e.
    rewrite simpl_lift by lia.
    replace (n + (Q - L)) with ((Q - L) + n) by lia. apply cg_subst_fresh_lift.
  Qed.

  Lemma branches_lift L Q QC ts1 ts2 N1 N2 l1 l2 :
    L <= Q -> Q <= QC ->
    Forall2 (fun br1 br2 => case_ctx_ok br1.(bcontext) br2.(bcontext) = true
      /\ cqb L QC #|br1.(bcontext)| Conv (rbody (map (lift0 (QC - Q)) ts1) ((QC - Q) + N1) br1)
                                         (rbody (map (lift0 (QC - Q)) ts2) ((QC - Q) + N2) br2))
      l1 l2 ->
    Forall2 (fun br1 br2 => case_ctx_ok br1.(bcontext) br2.(bcontext) = true
      /\ cqb L Q #|br1.(bcontext)| Conv (rbody ts1 N1 br1) (rbody ts2 N2 br2)) l1 l2.
  Proof.
    intros hLQ hQ h. induction h as [|br1 br2 l1 l2 [hc hq] _ ih]; constructor; [|exact ih].
    split; [exact hc|]. apply (cqb_lift L Q QC _ Conv _ _ hLQ hQ).
    rewrite !rbody_lift in hq. destruct (case_ctx_ok_spec _ _ hc) as [hx _ _].
    rewrite <- (All2_length hx) in hq. exact hq.
  Qed.

  Lemma case_branches_sound_g (k : unit -> cbn_fuel) :
    spec_term (k tt) -> spec_branches (k tt) -> spec_branches (FS k).
  Proof.
    intros hT hB L Q lo G e1 c1 e2 c2 i l1 l2 ts1 ts2 rs s b rs' s'
      hm hr hb1 hb2 hs1 hn1 hs2 hn2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite case_branches_eq in he.
    destruct l1 as [|br1 l1]; destruct l2 as [|br2 l2].
    - injection he as <- <- <-.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros _. constructor.
    - injection he as <- <- <-.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - injection he as <- <- <-.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - inversion hb1 as [|i1 z1 m1 hc1 hb1']; subst.
      inversion hb2 as [|i2 z2 m2 hc2 hb2']; subst.
      cbv beta iota in he.
      destruct (case_ctx_ok (bcontext br1) (bcontext br2)) eqn:Ectx;
        [|injection he as <- <- <-;
          split; [exact (post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
      destruct (case_ctx_ok_spec _ _ Ectx) as [hctx _ _].
      pose proof (All2_length hctx) as hn12.
      assert (hr0 : Forall (rwf Q) (RE e1 :: RE e2 :: rs))
        by (constructor; [exact I|constructor; [exact I|exact hr]]).
      pose proof (minv_raise L Q #|bcontext br1| lo G s hm) as hmR.
      pose proof (rwfs_mono Q (Q + #|bcontext br1|) _ ltac:(lia) hr0) as hrR.
      pose proof (grq_raise Q #|bcontext br1| G _ ltac:(lia) hr0) as hgR.
      pose proof (proj2 (g_slot_shift nctx Q #|bcontext br1| ltac:(lia) G) _ _ hs1) as [hs1R _].
      pose proof (proj2 (g_slot_shift nctx Q #|bcontext br1| ltac:(lia) G) _ _ hs2) as [hs2R _].
      destruct (push_fresh stress #|bcontext br1| L e1 e2 (RE e1 :: RE e2 :: rs) s)
        as [[[r rsP] sP]|w] eqn:EP; [|discriminate he].
      destruct (push_fresh_g #|bcontext br1| L (Q + #|bcontext br1|) lo (gshift #|bcontext br1| G)
                  L e1 e2 _ _ _ s r rsP sP hmR hrR ltac:(lia) hs1R hn1 hs2R hn2 EP)
        as (loP & GP & f1 & f2 & -> & hmP & hrP & hgP & hnf1 & hgf1 & hnf2 & hgf2 & hf1 & hf2).
      pose proof (push_fresh_skel stress _ _ _ _ _ _ _ _ _ EP) as hkP.
      cbv beta iota in he.
      pose proof (g_susp_of_slots nctx _ GP f1 (bbody br1) _ hf1 hnf1) as hB1.
      pose proof (g_susp_of_slots nctx _ GP f2 (bbody br2) _ hf2 hnf2) as hB2.
      destruct (conv_term X_type X Γ nctx stress (k tt) (L + #|bcontext br1|) Conv
                  f1 (child c1 (case_branch_step i) (bbody br1))
                  f2 (child c2 (case_branch_step i) (bbody br2)) rsP sP)
        as [[[bC rsC] sC]|w] eqn:EC; [|discriminate he].
      destruct (hT (L + #|bcontext br1|) (Q + #|bcontext br1|) loP GP Conv
                  f1 (child c1 (case_branch_step i) (bbody br1))
                  f2 (child c2 (case_branch_step i) (bbody br2)) _ _ rsP sP bC rsC sC
                  (minv_level L (L + #|bcontext br1|) (Q + #|bcontext br1|) loP GP sP hmP
                     ltac:(lia) ltac:(lia)) hrP hB1
                  (cok_gcx _ _ (proj1 hgP) _ hc1) hB2 (cok_gcx _ _ (proj1 hgP) _ hc2) EC)
        as [hpC hcC].
      (* the roots [push_fresh] handed back *)
      destruct (gren_cons_inv _ _ _ _ _ _ hgP) as (p1 & rsP1 & -> & hp1 & hgP1).
      destruct (gpres_RE_inv _ _ _ _ _ hp1) as (e1' & -> & (hne1 & hge1 & hke1)).
      destruct (gren_cons_inv _ _ _ _ _ _ hgP1) as (p2 & rsP' & -> & hp2 & hgP').
      destruct (gpres_RE_inv _ _ _ _ _ hp2) as (e2' & -> & (hne2 & hge2 & hke2)).
      assert (hgR' : grq Q (Q + #|bcontext br1|) G (gshift #|bcontext br1| G) rs rs).
      { destruct (grq_cons_inv _ _ _ _ _ _ _ hgR) as (a1 & ra & ea & _ & hga).
        injection ea as <- <-.
        destruct (grq_cons_inv _ _ _ _ _ _ _ hga) as (a2 & rb & eb & _ & hgb).
        injection eb as <- <-. exact hgb. }
      assert (hgP'' : grq (Q + #|bcontext br1|) (Q + #|bcontext br1|) (gshift #|bcontext br1| G)
                        GP rs rsP').
      { apply grq_of_gren; [exact hgP'|exact (sk_tl _ _ _ _ (sk_tl _ _ _ _ hkP))]. }
      destruct bC.
      + destruct hpC as (QC & loC & GC & hqC & hmC & hrC & hgC).
        destruct (grq_cons_inv _ _ _ _ _ _ _ hgC) as (q1 & rsC1 & -> & hqa & hgC1).
        destruct (gpq_RE_inv _ _ _ _ _ _ hqa) as (g1 & -> & hng1 & hgg1 & hkg1).
        destruct (grq_cons_inv _ _ _ _ _ _ _ hgC1) as (q2 & rsC' & -> & hqb & hgC').
        destruct (gpq_RE_inv _ _ _ _ _ _ hqb) as (g2 & -> & hng2 & hgg2 & hkg2).
        cbv beta iota in he.
        pose proof (hkg1 _ (hke1 _ hs1R)) as hg1s. pose proof (hkg2 _ (hke2 _ hs2R)) as hg2s.
        rewrite map_lift0_lift0 in hg1s, hg2s.
        replace (QC - (Q + #|bcontext br1|) + #|bcontext br1|) with (QC - Q) in hg1s, hg2s
          by lia.
        pose proof (g_slots_length _ _ _ _ _ hs1) as hl1.
        pose proof (g_slots_length _ _ _ _ _ hs2) as hl2.
        pose proof (g_slots_length _ _ _ _ _ hg1s) as hl1'. rewrite length_map in hl1'.
        pose proof (g_slots_length _ _ _ _ _ hg2s) as hl2'. rewrite length_map in hl2'.
        destruct (hB L QC loC GC g1 c1 g2 c2 (N.succ i) l1 l2 _ _ rsC' sC b rs' s'
                    (minv_level _ L _ _ _ _ hmC ltac:(lia) ltac:(lia))
                    (Forall_inv_tail (Forall_inv_tail hrC))
                    (bcodes_gcx _ _ _ _ _ (proj1 hgC)
                       (bcodes_gcx _ _ _ _ _ (proj1 hgP)
                          (bcodes_gcx G (gshift #|bcontext br1| G) _ _ _ (fun _ _ h => h) hb1')))
                    (bcodes_gcx _ _ _ _ _ (proj1 hgC)
                       (bcodes_gcx _ _ _ _ _ (proj1 hgP)
                          (bcodes_gcx G (gshift #|bcontext br1| G) _ _ _ (fun _ _ h => h) hb2')))
                    hg1s ltac:(lia) hg2s ltac:(lia) he) as [hp hc].
        split.
        * apply (post_compose L Q (Q + #|bcontext br1|) G _ rs rs s' rs' ltac:(lia) hgR').
          apply (post_compose L _ _ _ GP rs rsP' s' rs' (le_n _) hgP'').
          exact (post_compose L _ QC GP GC rsP' rsC' s' rs' hqC hgC' hp).
        * intros hb. constructor.
          -- split; [exact Ectx|]. intros U1 U2 eU1 eU2 sU1 sU2.
             apply (hcC eq_refl U1 U2); [| |exact sU1|exact sU2].
             ++ replace (Q + #|bcontext br1| - (L + #|bcontext br1|)) with (Q - L) by lia.
                rewrite hgf1, hnf1.
                pose proof (g_slots_length _ _ _ _ _ hf1) as hlf.
                rewrite length_app, length_map, idsn_length, length_map in hlf.
                rewrite <- hlf.
                replace (Q + #|bcontext br1| - nctx + ev_goff e1)
                  with (#|bcontext br1| + (Q - nctx + ev_goff e1)) by lia.
                replace (Q + #|bcontext br1| - (L + #|bcontext br1|)) with (Q - L) by lia.
                apply fresh_branch_read; [lia|]. exact eU1.
             ++ replace (Q + #|bcontext br1| - (L + #|bcontext br1|)) with (Q - L) by lia.
                rewrite hgf2, hnf2.
                pose proof (g_slots_length _ _ _ _ _ hf2) as hlf.
                rewrite length_app, length_map, idsn_length, length_map in hlf.
                rewrite <- hlf.
                replace (Q + #|bcontext br1| - nctx + ev_goff e2)
                  with (#|bcontext br1| + (Q - nctx + ev_goff e2)) by lia.
                replace (Q + #|bcontext br1| - (L + #|bcontext br1|)) with (Q - L) by lia.
                apply fresh_branch_read; [lia|]. unfold rbody in eU2. rewrite <- hn12 in eU2.
                exact eU2.
          -- apply (branches_lift L Q QC ts1 ts2 _ _ l1 l2 hLQ ltac:(lia)).
             rewrite hgg1, hge1, hgg2, hge2 in hc.
             replace (QC - nctx + ev_goff e1) with ((QC - Q) + (Q - nctx + ev_goff e1)) in hc
               by lia.
             replace (QC - nctx + ev_goff e2) with ((QC - Q) + (Q - nctx + ev_goff e2)) in hc
               by lia.
             exact (hc hb).
      + cbv beta iota in he. injection he as <- <- <-.
        split; [|intros hb; discriminate hb].
        apply (post_compose L Q (Q + #|bcontext br1|) G _ rs rs _ _ ltac:(lia) hgR').
        apply (post_compose L _ _ _ GP rs rsP' _ _ (le_n _) hgP'').
        apply (post_drop2 L _ GP (RE e1') (RE e2') rsP').
        exact (post_level L (L + #|bcontext br1|) (Q + #|bcontext br1|) GP _ _ _ hL
                 ltac:(lia) hpC).
  Qed.

End ConvGhost.

(** * Non-vacuity witnesses for the statements of [ConvGhost]

  Two concrete runs of [conv_term] at the real fuel [cbn_depth], from the state [cbn_run]
  starts in. Each theorem shows that the premises of [spec_term] hold at the run's inputs (the
  start state satisfies [minv], the inputs have readings, their codes are in the ghost's
  table), that the call returns, and that the conclusion holds: the state part [post] by the
  machine lemma [whnf_master_hwf] and, for the run that answers [true], the conversion part
  [cq] by hand, not by the fuel induction. The answers and final states are obtained by
  computation. The only hypotheses are [wf Σ] and [abstract_env_ext_rel X Σ]: the start
  invariant is [run_s2_gok] of [PCUICCallByNeedSoundLevel], and the section hypotheses of
  [ConvGhost] hold at both contexts ([w_section], [v_section]).
  - [witness_seam_run]: the run that refuted the old seam
    ([PCUICCallByNeedSoundHookFrame.term_seam_false]): [x := (fun n : nat => n) O] against
    [fun n : nat => n]. It answers [false], [post] holds after it, and the context cell of [x]
    has been forced while every ghost of [minv] still reads it as its let-body.
  - [witness_true_run]: [x := (fun n : y => n) y] against [y], at [Conv]. It answers [true]
    and [cq] holds. *)

(** [at_depth F dflt] runs [F] at the fuel one unit below [cbn_depth]. Stating the machine
  calls of a run this way lets [vm_compute] evaluate them at the real fuel with no equation
  between fuels to prove. *)
Definition at_depth {A : Type} (F : cbn_fuel -> A) (dflt : A) : A :=
  match cbn_depth with FS k => F (k tt) | FO => dflt end.

(** The concrete contexts and terms. *)
Definition w_na : aname := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition w_nat : inductive :=
  {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |}.
Definition w_O : term := tConstruct w_nat 0 [].
Definition w_body : term := tApp (tLambda w_na (tInd w_nat []) (tRel 0)) w_O.
Definition w_Γ : context := [vdef w_na w_body (tInd w_nat [])].
Definition w_t : term := tRel 0.
Definition w_u : term := tLambda w_na (tInd w_nat []) (tRel 0).

Definition v_Γ : context :=
  [vdef w_na (tApp (tLambda w_na (tRel 0) (tRel 0)) (tRel 0)) (tRel 0); vass w_na (tSort sProp)].
Definition v_t : term := tRel 0.
Definition v_u : term := tRel 1.

Section Witness.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Σ : global_env_ext) (wfΣ : wf Σ) (hΣ : abstract_env_ext_rel X Σ).

  (** [tick] keeps [minv]. *)
  Lemma r_minv_tick (Γ : context) (nctx L Q : nat) (lo : positive) (G : ghost)
      (s s' : cbn_state) :
    minv X_type X Γ nctx Σ L Q lo G s -> tick s = Some s' ->
    minv X_type X Γ nctx Σ L Q lo G s'.
  Proof.
    intros [hL hQ hok hw] e. destruct (tick_shape s s' e) as (th & tn & _ & tg & tm).
    constructor; [exact hL|exact hQ| |exact (hwf_heap Q s s' th hw)].
    apply (gok_same X_type X Γ nctx Σ _ Q lo G s s' hok th tn tg).
    exact (mok_memo X_type X Γ Σ _ s s' tm (@gk_memo _ X_type X Γ nctx Σ _ _ _ _ _ hok)).
  Qed.

  (** The start state of a run satisfies [minv] at [L = Q = nctx]. *)
  Lemma r_minv_start (Γ : context) (nctx : nat) (t u : term) (hnctx : nctx = #|Γ|) :
    consts_okb Σ t -> consts_okb Σ u -> on_free_vars xpredT t -> on_free_vars xpredT u ->
    minv X_type X Γ nctx Σ nctx nctx xH (run_ghost X_type X t u) (run_s2 X_type X t u).
  Proof.
    intros ht hu hht hhu.
    apply (minv_start X_type X Γ nctx Σ hnctx xH (run_ghost X_type X t u) _
             (run_s2_gok X_type X Γ nctx Σ [] nctx t u ht hu hht hhu)).
    intros a cl h. unfold heap_get in h. rewrite run_s2_heap, bh_get_holes in h.
    discriminate h.
  Qed.

  (** A run of [conv_term] at [cbn_depth] from [cbn_run]'s start state, split at its three
    machine calls. *)
  Lemma r_split (Γ : context) (nctx : nat) (t u : term) (v1 v2 : cbn_value)
      (s1 s2 s3 : cbn_state) (b : bool) :
    at_depth (fun d => whnf X_type X Γ nctx false d env_empty (run_c1 X_type X t) []
                         [RE env_empty] (run_s2 X_type X t u)) (CFail WDepth)
      = COk (v1, [RE env_empty], s1) ->
    at_depth (fun d => whnf X_type X Γ nctx false d env_empty (run_c2 X_type X t u) []
                         [RV v1] s1) (CFail WDepth)
      = COk (v2, [RV v1], s2) ->
    at_depth (fun d => conv_value X_type X Γ nctx false d nctx Conv v1 v2 [] s2) (CFail WDepth)
      = COk (b, [], s3) ->
    conv_term X_type X Γ nctx false cbn_depth nctx Conv env_empty (run_c1 X_type X t)
      env_empty (run_c2 X_type X t u) [] (run_s2 X_type X t u) = COk (b, [], s3)
    /\ exists d,
         whnf X_type X Γ nctx false d env_empty (run_c1 X_type X t) [] [RE env_empty]
           (run_s2 X_type X t u) = COk (v1, [RE env_empty], s1)
         /\ whnf X_type X Γ nctx false d env_empty (run_c2 X_type X t u) [] [RV v1] s1
              = COk (v2, [RV v1], s2).
  Proof.
    unfold at_depth. destruct cbn_depth as [|k]; intros E1 E2 E3; [discriminate E1|].
    cbv beta in E1, E2, E3.
    split; [|exists (k tt); split; assumption].
    rewrite conv_term_eq, E1. cbv beta iota. rewrite E2. cbv beta iota. exact E3.
  Qed.

  (** The state part: [post] holds after the two [whnf] calls and the [tick] of
    [conv_value], by [whnf_master_hwf]. *)
  Lemma r_post (Γ : context) (nctx : nat) (t u : term) (hnctx : nctx = #|Γ|)
      (hcio : forall j decl b, nth_error Γ j = Some decl -> decl.(decl_body) = Some b ->
                PCUICCallByNeedSoundHook.consts_okb Σ b)
      (d : cbn_fuel) (v1 v2 : cbn_value) (s1 s2 s3 : cbn_state) :
    minv X_type X Γ nctx Σ nctx nctx xH (run_ghost X_type X t u) (run_s2 X_type X t u) ->
    whnf X_type X Γ nctx false d env_empty (run_c1 X_type X t) [] [RE env_empty]
      (run_s2 X_type X t u) = COk (v1, [RE env_empty], s1) ->
    whnf X_type X Γ nctx false d env_empty (run_c2 X_type X t u) [] [RV v1] s1
      = COk (v2, [RV v1], s2) ->
    tick s2 = Some s3 ->
    post X_type X Γ nctx Σ nctx nctx (run_ghost X_type X t u) [] s3 [].
  Proof.
    intros hm0 E1 E2 E3.
    destruct (whnf_master_hwf X_type X Γ nctx false Σ wfΣ hΣ hnctx hcio d nctx nctx xH
                (run_ghost X_type X t u) env_empty (run_c1 X_type X t) [] [] t [RE env_empty]
                (run_s2 X_type X t u) v1 [RE env_empty] s1 hm0
                (Forall_cons (RE env_empty) I (Forall_nil _)) (run_c1_g_susp X_type X nctx t u)
                (run_c1_gcok X_type X t u) (g_slots_nil nctx nctx _) E1)
      as (lo1 & G1 & w1 & hm1 & hr1 & hv1 & hg1 & _ & _).
    assert (hs2 : g_susp nctx nctx G1 env_empty (run_c2 X_type X t u).(c_term) u).
    { rewrite run_c2_term. apply g_susp_env_empty. }
    destruct (whnf_master_hwf X_type X Γ nctx false Σ wfΣ hΣ hnctx hcio d nctx nctx lo1 G1
                env_empty (run_c2 X_type X t u) [] [] u [RV v1] s1 v2 [RV v1] s2 hm1
                (Forall_cons (RV v1) hv1 (Forall_inv_tail hr1)) hs2
                (cok_gcx _ _ (proj1 hg1) _ (run_c2_gcok X_type X t u))
                (g_slots_nil nctx nctx _) E2)
      as (lo2 & G2 & w2 & hm2 & hr2 & hv2 & hg2 & _ & _).
    exists nctx, lo2, G2. split; [lia|]. split; [exact (r_minv_tick _ _ _ _ _ _ _ _ hm2 E3)|].
    split; [constructor|]. split; [|split; [constructor|reflexivity]].
    intros i e hi. exact (proj1 hg2 _ _ (proj1 hg1 _ _ hi)).
  Qed.

  (** ** W1: the run that refuted the old seam answers [false], and [post] holds after it *)

  Definition w_G0 : ghost := run_ghost X_type X w_t w_u.

  (** The section hypotheses of [ConvGhost] at [w_Γ]. *)
  Lemma w_section :
    1 = #|w_Γ| /\ is_closed_context w_Γ /\ ctx_hyg w_Γ
    /\ (forall j decl b, nth_error w_Γ j = Some decl -> decl.(decl_body) = Some b ->
          PCUICCallByNeedSoundHook.consts_okb Σ b).
  Proof.
    split; [reflexivity|]. split; [reflexivity|]. split.
    - intros [|j] decl b hj hb; [|destruct j; discriminate hj].
      injection hj as <-. injection hb as <-. reflexivity.
    - intros [|j] decl b hj hb; [|destruct j; discriminate hj].
      injection hj as <-. injection hb as <-. reflexivity.
  Qed.

  Definition w_R1 :=
    at_depth (fun d => whnf X_type X w_Γ 1 false d env_empty (run_c1 X_type X w_t) []
                         [RE env_empty] (run_s2 X_type X w_t w_u)) (CFail WDepth).
  Definition w_s1 : cbn_state := match w_R1 with COk (_, _, s) => s | CFail _ => cbn_init end.
  Definition w_R2 :=
    at_depth (fun d => whnf X_type X w_Γ 1 false d env_empty (run_c2 X_type X w_t w_u) []
                         [RV (VCon w_O [])] w_s1) (CFail WDepth).
  Definition w_v2 : cbn_value := match w_R2 with COk (v, _, _) => v | CFail _ => VCon w_O [] end.
  Definition w_s2 : cbn_state := match w_R2 with COk (_, _, s) => s | CFail _ => cbn_init end.
  Definition w_s3 : cbn_state := match tick w_s2 with Some s => s | None => cbn_init end.

  Lemma w_E1 :
    at_depth (fun d => whnf X_type X w_Γ 1 false d env_empty (run_c1 X_type X w_t) []
                         [RE env_empty] (run_s2 X_type X w_t w_u)) (CFail WDepth)
    = COk (VCon w_O [], [RE env_empty], w_s1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma w_E2 :
    at_depth (fun d => whnf X_type X w_Γ 1 false d env_empty (run_c2 X_type X w_t w_u) []
                         [RV (VCon w_O [])] w_s1) (CFail WDepth)
    = COk (w_v2, [RV (VCon w_O [])], w_s2).
  Proof. vm_compute. reflexivity. Qed.

  Lemma w_E3 :
    at_depth (fun d => conv_value X_type X w_Γ 1 false d 1 Conv (VCon w_O []) w_v2 [] w_s2)
      (CFail WDepth) = COk (false, [], w_s3).
  Proof. vm_compute. reflexivity. Qed.

  Lemma w_tick : tick w_s2 = Some w_s3.
  Proof. vm_compute. reflexivity. Qed.

  Lemma w_body_lift (n k : nat) : lift n k w_body = w_body.
  Proof. reflexivity. Qed.

  Theorem witness_seam_run :
    minv X_type X w_Γ 1 Σ 1 1 xH w_G0 (run_s2 X_type X w_t w_u)
    /\ g_susp 1 1 w_G0 env_empty (run_c1 X_type X w_t).(c_term) w_t
    /\ PCUICCallByNeedSoundEval.cok w_G0 (run_c1 X_type X w_t)
    /\ g_susp 1 1 w_G0 env_empty (run_c2 X_type X w_t w_u).(c_term) w_u
    /\ PCUICCallByNeedSoundEval.cok w_G0 (run_c2 X_type X w_t w_u)
    /\ exists s',
         conv_term X_type X w_Γ 1 false cbn_depth 1 Conv env_empty (run_c1 X_type X w_t)
           env_empty (run_c2 X_type X w_t w_u) [] (run_s2 X_type X w_t w_u) = COk (false, [], s')
         /\ post X_type X w_Γ 1 Σ 1 1 w_G0 [] s' []
         /\ PTree.get (key_of_succ_nat 0) s'.(st_gam) = Some (HAddr 1)
         /\ heap_get (HAddr 1) s' = Some (CDone (VCon w_O []))
         /\ (forall Q' lo' G', minv X_type X w_Γ 1 Σ 1 Q' lo' G' s' -> G' (HAddr 1) = Some w_body).
  Proof.
    assert (hm0 : minv X_type X w_Γ 1 Σ 1 1 xH w_G0 (run_s2 X_type X w_t w_u))
      by exact (r_minv_start w_Γ 1 w_t w_u eq_refl eq_refl eq_refl eq_refl eq_refl).
    split; [exact hm0|].
    split; [exact (run_c1_g_susp X_type X 1 w_t w_u)|].
    split; [exact (run_c1_gcok X_type X w_t w_u)|].
    split; [exact (run_c2_g_susp X_type X 1 w_t w_u)|].
    split; [exact (run_c2_gcok X_type X w_t w_u)|].
    destruct (r_split w_Γ 1 w_t w_u (VCon w_O []) w_v2 w_s1 w_s2 w_s3 false
                w_E1 w_E2 w_E3) as [hrun (d & hd1 & hd2)].
    exists w_s3. split; [exact hrun|].
    assert (hgam : PTree.get (key_of_succ_nat 0) w_s3.(st_gam) = Some (HAddr 1))
      by (vm_compute; reflexivity).
    destruct w_section as (_ & _ & _ & hcio).
    split; [exact (r_post w_Γ 1 w_t w_u eq_refl hcio d _ _ _ _ _ hm0 hd1 hd2 w_tick)|].
    split; [exact hgam|].
    split; [vm_compute; reflexivity|].
    intros Q' lo' G' [_ _ hok _].
    destruct (@gk_gam _ X_type X w_Γ 1 Σ _ _ _ _ _ hok 0 (HAddr 1) hgam) as (tm & hden & hG).
    change (ctx_den w_Γ 1 Q' 0) with (Some (lift0 (Q' - 1 + 1) w_body)) in hden.
    rewrite w_body_lift in hden. injection hden as <-. exact hG.
  Qed.

  (** ** W2: a run that answers [true], with its conversion claim *)

  Definition v_G0 : ghost := run_ghost X_type X v_t v_u.

  (** The section hypotheses of [ConvGhost] at [v_Γ]. *)
  Lemma v_section :
    2 = #|v_Γ| /\ is_closed_context v_Γ /\ ctx_hyg v_Γ
    /\ (forall j decl b, nth_error v_Γ j = Some decl -> decl.(decl_body) = Some b ->
          PCUICCallByNeedSoundHook.consts_okb Σ b).
  Proof.
    split; [reflexivity|]. split; [reflexivity|]. split.
    - intros [|[|j]] decl b hj hb; [| |destruct j; discriminate hj].
      + injection hj as <-. injection hb as <-. reflexivity.
      + injection hj as <-. discriminate hb.
    - intros [|[|j]] decl b hj hb; [| |destruct j; discriminate hj].
      + injection hj as <-. injection hb as <-. reflexivity.
      + injection hj as <-. discriminate hb.
  Qed.

  Definition v_R1 :=
    at_depth (fun d => whnf X_type X v_Γ 2 false d env_empty (run_c1 X_type X v_t) []
                         [RE env_empty] (run_s2 X_type X v_t v_u)) (CFail WDepth).
  Definition v_v1 : cbn_value := match v_R1 with COk (v, _, _) => v | CFail _ => VCon w_O [] end.
  Definition v_s1 : cbn_state := match v_R1 with COk (_, _, s) => s | CFail _ => cbn_init end.
  Definition v_R2 :=
    at_depth (fun d => whnf X_type X v_Γ 2 false d env_empty (run_c2 X_type X v_t v_u) []
                         [RV v_v1] v_s1) (CFail WDepth).
  Definition v_v2 : cbn_value := match v_R2 with COk (v, _, _) => v | CFail _ => VCon w_O [] end.
  Definition v_s2 : cbn_state := match v_R2 with COk (_, _, s) => s | CFail _ => cbn_init end.
  Definition v_s3 : cbn_state := match tick v_s2 with Some s => s | None => cbn_init end.

  Lemma v_E1 :
    at_depth (fun d => whnf X_type X v_Γ 2 false d env_empty (run_c1 X_type X v_t) []
                         [RE env_empty] (run_s2 X_type X v_t v_u)) (CFail WDepth)
    = COk (v_v1, [RE env_empty], v_s1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma v_E2 :
    at_depth (fun d => whnf X_type X v_Γ 2 false d env_empty (run_c2 X_type X v_t v_u) []
                         [RV v_v1] v_s1) (CFail WDepth)
    = COk (v_v2, [RV v_v1], v_s2).
  Proof. vm_compute. reflexivity. Qed.

  Lemma v_E3 :
    at_depth (fun d => conv_value X_type X v_Γ 2 false d 2 Conv v_v1 v_v2 [] v_s2)
      (CFail WDepth) = COk (true, [], v_s3).
  Proof. vm_compute. reflexivity. Qed.

  Lemma v_tick : tick v_s2 = Some v_s3.
  Proof. vm_compute. reflexivity. Qed.

  (** The claim, by hand: [x] unfolds to [(fun n : y => n) y], which beta-reduces to [y]. *)
  Lemma v_red : PCUICReduction.red Σ v_Γ v_t v_u.
  Proof.
    eapply PCUICReduction.red_trans.
    - apply PCUICReduction.red1_red.
      exact (PCUICReduction.red_rel Σ v_Γ 0 (tApp (tLambda w_na (tRel 0) (tRel 0)) (tRel 0)) eq_refl).
    - apply PCUICReduction.red1_red. exact (PCUICReduction.red_beta Σ v_Γ w_na (tRel 1) (tRel 0) (tRel 1)).
  Qed.

  Lemma v_cq : cq v_Γ 2 Σ 2 2 Conv v_t v_u.
  Proof.
    intros u1 u2 e1 e2 _ _. rewrite Nat.sub_diag, lift0_id in e1, e2. subst u1 u2.
    intros Δ hΔ hcl. destruct Δ as [|? Δ]; [|discriminate hΔ].
    constructor. apply (red_ws_cumul_pb (wfΣ := wfΣ)).
    apply into_closed_red; [exact v_red|exact hcl|reflexivity].
  Qed.

  Theorem witness_true_run :
    minv X_type X v_Γ 2 Σ 2 2 xH v_G0 (run_s2 X_type X v_t v_u)
    /\ g_susp 2 2 v_G0 env_empty (run_c1 X_type X v_t).(c_term) v_t
    /\ PCUICCallByNeedSoundEval.cok v_G0 (run_c1 X_type X v_t)
    /\ g_susp 2 2 v_G0 env_empty (run_c2 X_type X v_t v_u).(c_term) v_u
    /\ PCUICCallByNeedSoundEval.cok v_G0 (run_c2 X_type X v_t v_u)
    /\ exists s',
         conv_term X_type X v_Γ 2 false cbn_depth 2 Conv env_empty (run_c1 X_type X v_t)
           env_empty (run_c2 X_type X v_t v_u) [] (run_s2 X_type X v_t v_u) = COk (true, [], s')
         /\ post X_type X v_Γ 2 Σ 2 2 v_G0 [] s' []
         /\ cq v_Γ 2 Σ 2 2 Conv v_t v_u.
  Proof.
    assert (hm0 : minv X_type X v_Γ 2 Σ 2 2 xH v_G0 (run_s2 X_type X v_t v_u))
      by exact (r_minv_start v_Γ 2 v_t v_u eq_refl eq_refl eq_refl eq_refl eq_refl).
    split; [exact hm0|].
    split; [exact (run_c1_g_susp X_type X 2 v_t v_u)|].
    split; [exact (run_c1_gcok X_type X v_t v_u)|].
    split; [exact (run_c2_g_susp X_type X 2 v_t v_u)|].
    split; [exact (run_c2_gcok X_type X v_t v_u)|].
    destruct (r_split v_Γ 2 v_t v_u v_v1 v_v2 v_s1 v_s2 v_s3 true
                v_E1 v_E2 v_E3) as [hrun (d & hd1 & hd2)].
    exists v_s3. split; [exact hrun|].
    destruct v_section as (_ & _ & _ & hcio).
    split; [exact (r_post v_Γ 2 v_t v_u eq_refl hcio d _ _ _ _ _ hm0 hd1 hd2 v_tick)|].
    exact v_cq.
  Qed.
End Witness.
