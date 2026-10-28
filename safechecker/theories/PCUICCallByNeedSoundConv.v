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
End Conv.
