(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require CanonicalTries.
From MetaRocq.Common Require Import config Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICReduction.
From MetaRocq.SafeChecker Require Import PCUICWfEnv PCUICCallByNeed PCUICCallByNeedSound
  PCUICCallByNeedSoundGC PCUICCallByNeedSoundCtx.

Import CanonicalTries.

(** * The evaluator of the call-by-need machine against PCUIC reduction (BET-298, step 2c)

  [whnf], [eval_slot], [force], [apply] (and [whnf_fix], which this file only rules out)
  turn a suspension into a weak-head value. This file proves that the term the input stands
  for reduces, in PCUIC, to the term the value stands for, for the rules beta, zeta, rel
  (including the forcing of a cell and its write-back) and delta.

  ** What a structure stands for

  The read-back used here is *not* [repr_value] of [PCUICCallByNeedSound]: it is a ghost
  read-back [g_value], which reads an address [a] as the term [G a] of a ghost map
  [G : haddr -> option term] instead of following the heap. The two differ exactly on a cell
  the machine has already forced: [repr] reads such a cell as the value now in it, the ghost
  map keeps the term the cell was allocated for.

  The ghost map is what makes the write-back compositional, and it is the "ghost allocation
  term" of REPORT-BET298 §4.3. With [repr], forcing an address changes what *every* other
  structure that names it stands for: the reading of a cell is a term built out of the
  readings of the addresses below it, so a write-back turns a third party's reading [u] into
  some reduct [u']. To put a value [v] back into a forced cell one then has to know that [v]
  is a reduct of the cell's reading *as it is when the forcing ends*, not of its reading when
  the forcing started, and the two are only joinable, not ordered: that is a confluence
  argument, not an induction. With the ghost map, [G] only ever grows at fresh addresses
  ([gext]), so a write-back changes no reading at all, and the heap invariant [gk_cells] —
  "the cell at [a] stands for a reduct of [G a]" — is restored at the forced address by
  transitivity and is untouched everywhere else.

  ** What the rules are restricted to

  [simple_term] holds of the terms built from [tRel], [tSort], [tConst], [tInd],
  [tConstruct], [tApp], [tLambda], [tProd] and [tLetIn]. It is a premise of every ghost
  reading of a code, so a structure whose code mentions [tCase], [tProj], [tFix], [tCoFix],
  [tPrim], [tEvar] or [tVar] stands for nothing, and the iota, fix, cofix, projection and
  primitive rules are exactly the branches whose hypotheses are contradictory here. They are
  left to a later task; nothing in the statement is weakened for them.

  ** What is assumed

  - [delta_ok] and [delta_inv_pres]: the delta memo of [PCUICCallByNeed] returns, for a
    constant with a body, a code whose term is the body at the right instance, and that
    term is what [tConst] reduces to. Proving it needs the laws of the [dtrie] memo (which
    step 2a does not have) and [red_delta] with [declared_constant_closed_body]; it is
    stated here against the concrete memo invariant [delta_inv], which [cbn_init]
    satisfies.
  - [Γ_simple]: the bodies of the let-entries of [Γ] are simple terms.
  - [hstress] and the budget: the run allocates fewer cells than [st_room] leaves it, so no
    allocation collects. A run that collects needs the renaming of [PCUICCallByNeedSoundGC],
    which relates [repr] readings, not ghost ones. *)

(** ** The terms the rules of this file cover *)

Fixpoint simple_term (t : term) : bool :=
  match t with
  | tRel _ => true
  | tSort _ => true
  | tConst _ _ => true
  | tInd _ _ => true
  | tConstruct _ _ _ => true
  | tApp f a => simple_term f && simple_term a
  | tLambda _ A b => simple_term A && simple_term b
  | tProd _ A B => simple_term A && simple_term B
  | tLetIn _ b A u => simple_term b && simple_term A && simple_term u
  | _ => false
  end.

Lemma simple_app f a : simple_term (tApp f a) = true ->
  simple_term f = true /\ simple_term a = true.
Proof. cbn. intros h. apply andb_true_iff in h. exact h. Qed.

Lemma simple_lam na A b : simple_term (tLambda na A b) = true ->
  simple_term A = true /\ simple_term b = true.
Proof. cbn. intros h. apply andb_true_iff in h. exact h. Qed.

Lemma simple_letin na b A u : simple_term (tLetIn na b A u) = true ->
  simple_term b = true /\ simple_term A = true /\ simple_term u = true.
Proof.
  cbn. intros h. apply andb_true_iff in h. destruct h as [h1 h2].
  apply andb_true_iff in h1. destruct h1 as [h3 h4]. split; [exact h3|split; assumption].
Qed.

Lemma Forall_app_g {A} (P : A -> Prop) (l1 l2 : list A) :
  Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  induction 1 as [|x l hx hl ih]; simpl; intros h2;
    [exact h2|constructor; [exact hx|exact (ih h2)]].
Qed.

Section Eval.
  Context {cf : checker_flags}.
  Context (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat) (stress : bool).

  (** The environment the readings live in: [Γ] under [lvl - nctx] fresh variables. *)
  (** The environment the readings live in: [Γ] under [lvl - nctx] fresh variables.
     [Σ] is the well-formed ambient environment the abstract one [X] stands for; the hook
     runs under both, and the delta rule needs them for the body it unfolds. *)
  Context (Σ : global_env_ext) (Δ : context) (lvl : nat).
  Hypothesis wfΣ : wf Σ.
  Hypothesis hΣ : abstract_env_ext_rel X Σ.
  Hypothesis hΔ : #|Δ| = lvl - nctx.
  (** Written so that [subst] never eliminates the section variable [stress]. *)
  Hypothesis hstress : negb stress = true.

  Lemma stress_false : stress = false.
  Proof. apply negb_true_iff. exact hstress. Qed.

  Local Notation ΓΔ := (Γ ,,, Δ).

  (** Reduction, squashed: [red1] lives in [Type], the readings here in [Prop]. *)
  Definition cred (t u : term) : Prop := ∥ red Σ ΓΔ t u ∥.

  Lemma cred_refl t : cred t t.
  Proof. constructor. apply refl_red. Qed.

  Lemma cred_trans t u v : cred t u -> cred u v -> cred t v.
  Proof. intros [h1] [h2]. constructor. exact (red_trans _ _ _ _ _ h1 h2). Qed.

  Lemma cred_one t u : red1 Σ ΓΔ t u -> cred t u.
  Proof. intros h. constructor. exact (red1_red _ _ _ _ h). Qed.

  Lemma cred_mkApps t u ts : cred t u -> cred (mkApps t ts) (mkApps u ts).
  Proof. intros [h]. constructor. exact (red_mkApps_f _ _ _ h). Qed.

  Lemma cred_app_r f t u : cred t u -> cred (tApp f t) (tApp f u).
  Proof. intros [h]. constructor. exact (red_app_r _ _ _ h). Qed.

  Lemma cred_letin na d0 d1 T b : cred d0 d1 -> cred (tLetIn na d0 T b) (tLetIn na d1 T b).
  Proof.
    intros [h]. constructor.
    exact (red_letin na d0 d1 T T b b h (refl_red _ _ _) (refl_red _ _ _)).
  Qed.

  (** ** The ghost read-back

    [G a] is the term the cell at [a] was allocated for. An inline suspension is read like
    [repr_susp]: the slots are read, then substituted into the code lifted over the
    environment's own variables. [simple_term] is a premise, so an out-of-scope code stands
    for nothing. *)

  Inductive g_slot (G : haddr -> option term) : cbn_slot -> term -> Prop :=
  | g_slot_addr a t : G a = Some t -> g_slot G (SAddr a) t
  | g_slot_inl vals nvals goff c ts :
      g_slots G vals ts -> nvals = #|vals| -> simple_term c.(c_term) = true ->
      g_slot G (SInl vals nvals goff c)
        (subst ts 0 (lift (lvl - nctx + goff) nvals c.(c_term)))

  with g_slots (G : haddr -> option term) : list cbn_slot -> list term -> Prop :=
  | g_slots_nil : g_slots G [] []
  | g_slots_cons x l t ts :
      g_slot G x t -> g_slots G l ts -> g_slots G (x :: l) (t :: ts).

  Scheme g_slot_min := Minimality for g_slot Sort Prop
  with g_slots_min := Minimality for g_slots Sort Prop.
  Combined Scheme g_slot_mutind from g_slot_min, g_slots_min.

  Inductive g_susp (G : haddr -> option term) : cbn_env -> term -> term -> Prop :=
  | g_susp_intro vals nvals goff t ts :
      g_slots G vals ts -> nvals = #|vals| -> simple_term t = true ->
      g_susp G (mkEnv vals nvals goff) t (subst ts 0 (lift (lvl - nctx + goff) nvals t)).

  Definition g_addrs (G : haddr -> option term) (l : list haddr) (ts : list term) : Prop :=
    Forall2 (fun a t => G a = Some t) l ts.

  (** No clause for [VFix] and [VStuckFix]: their code is a [tFix], which is not simple. *)
  Inductive g_value (G : haddr -> option term) : cbn_value -> term -> Prop :=
  | g_VCon h sp ts : g_addrs G sp ts -> g_value G (VCon h sp) (mkApps h ts)
  | g_VLam e c t : g_susp G e c.(c_term) t -> g_value G (VLam e c) t
  | g_VOpen e c t : g_susp G e c.(c_term) t -> g_value G (VOpen e c) t
  | g_VNeuVar l sp ts :
      g_addrs G sp ts -> g_value G (VNeu (NVar l) sp) (mkApps (tRel (lvl - S l)) ts)
  | g_VNeuConst h sp ts :
      g_addrs G sp ts -> g_value G (VNeu (NConst h) sp) (mkApps h ts)
  | g_VStuck e c sp h ts :
      g_susp G e c.(c_term) h -> g_addrs G sp ts ->
      g_value G (VStuck e c sp) (mkApps h ts).

  Inductive g_cell (G : haddr -> option term) : cbn_cell -> term -> Prop :=
  | g_cell_susp vals nvals goff c t :
      g_susp G (mkEnv vals nvals goff) c.(c_term) t ->
      g_cell G (CSusp vals nvals goff c) t
  | g_cell_done v t : g_value G v t -> g_cell G (CDone v) t.

  (** ** The ghost map only grows, and every reading survives *)

  Definition gext (G G' : haddr -> option term) : Prop :=
    forall a t, G a = Some t -> G' a = Some t.

  Lemma gext_refl G : gext G G.
  Proof. intros a t h. exact h. Qed.

  Lemma gext_trans G1 G2 G3 : gext G1 G2 -> gext G2 G3 -> gext G1 G3.
  Proof. intros h1 h2 a t h. apply h2, h1, h. Qed.

  Lemma g_slot_ext G G' (h : gext G G') :
    (forall x t, g_slot G x t -> g_slot G' x t)
    /\ (forall l ts, g_slots G l ts -> g_slots G' l ts).
  Proof using.
    apply (g_slot_mutind G (fun x t => g_slot G' x t) (fun l ts => g_slots G' l ts));
      intros; econstructor; eauto.
  Qed.

  Definition g_slot_mono G G' (h : gext G G') := proj1 (g_slot_ext G G' h).
  Definition g_slots_mono G G' (h : gext G G') := proj2 (g_slot_ext G G' h).

  Lemma g_susp_mono G G' (h : gext G G') e t u : g_susp G e t u -> g_susp G' e t u.
  Proof.
    intros hs. inversion hs; subst. constructor; try reflexivity; try assumption.
    eapply (g_slots_mono G G' h). eassumption.
  Qed.

  Lemma g_addrs_mono G G' (h : gext G G') l ts : g_addrs G l ts -> g_addrs G' l ts.
  Proof. intros ha. induction ha; constructor; auto. Qed.

  Lemma g_value_mono G G' (h : gext G G') v t : g_value G v t -> g_value G' v t.
  Proof.
    intros hv. destruct hv; econstructor;
      eauto using g_addrs_mono, g_susp_mono.
  Qed.

  Lemma g_cell_mono G G' (h : gext G G') cl t : g_cell G cl t -> g_cell G' cl t.
  Proof. intros hc. destruct hc; econstructor; eauto using g_value_mono, g_susp_mono. Qed.

  (** ** Every address a reading names has a ghost term *)

  Definition gdef (G : haddr -> option term) (a : haddr) : Prop := exists t, G a = Some t.

  Lemma g_slot_ad G :
    (forall x t, g_slot G x t -> Forall (gdef G) (ad_slot x))
    /\ (forall l ts, g_slots G l ts -> Forall (gdef G) (ad_slots l)).
  Proof using.
    apply (g_slot_mutind G
      (fun x t => Forall (gdef G) (ad_slot x))
      (fun l ts => Forall (gdef G) (ad_slots l))).
    - intros a t ha. constructor; [exists t; exact ha|constructor].
    - intros vals nvals goff c ts _ ih _ _. exact ih.
    - constructor.
    - intros x l t ts _ ih1 _ ih2. unfold ad_slots. cbn [flat_map].
      apply Forall_app_g; [exact ih1|exact ih2].
  Qed.

  Lemma g_addrs_ad G l ts : g_addrs G l ts -> Forall (gdef G) l.
  Proof. intros h. induction h; constructor; [eexists; eassumption|assumption]. Qed.

  Lemma g_susp_ad G e t u : g_susp G e t u -> Forall (gdef G) (ad_env e).
  Proof.
    intros h. inversion h; subst. unfold ad_env. cbn [ev_vals].
    eapply (proj2 (g_slot_ad G)). eassumption.
  Qed.

  Lemma g_value_ad G v t : g_value G v t -> Forall (gdef G) (ad_value v).
  Proof.
    intros h. destruct h; cbn [ad_value];
      try (eapply g_addrs_ad; eassumption);
      try (eapply g_susp_ad; eassumption).
    apply Forall_app_g;
      [eapply g_susp_ad; eassumption|eapply g_addrs_ad; eassumption].
  Qed.

  Lemma g_cell_ad G cl t : g_cell G cl t -> Forall (gdef G) (ad_cell cl).
  Proof.
    intros h. destruct h; cbn [ad_cell].
    - inversion H; subst. eapply (proj2 (g_slot_ad G)). eassumption.
    - exact (g_value_ad _ _ _ H).
  Qed.

  (** ** The shape of the heap, which every state operation keeps

    [hok] is what the machine keeps of the heap without any reading: the heap was built the
    way [bh_ok] says, and it holds no forwarding pointer, so the collector's theorem
    applies to it. It is all that is needed to see that [st_next] never goes down, which is
    what lets a caller spend the room budget across two calls in a row. *)

  Definition hok (s : cbn_state) : Prop :=
    (exists lo, bh_ok lo s.(st_next) s.(st_heap)) /\ heap_nofwd s.(st_heap).

  Definition hstep (s s' : cbn_state) : Prop :=
    (s.(st_next) <= s'.(st_next))%positive /\ hok s'.

  Lemma hstep_refl s : hok s -> hstep s s.
  Proof. intros h. split; [apply Pos.le_refl|exact h]. Qed.

  Lemma hstep_trans s1 s2 s3 : hstep s1 s2 -> hstep s2 s3 -> hstep s1 s3.
  Proof. intros [h1 _] [h2 h3]. split; [exact (Pos.le_trans _ _ _ h1 h2)|exact h3]. Qed.

  Lemma hok_alloc_now cl s : cell_fwd cl = None -> hok s -> hok (snd (alloc_now cl s)).
  Proof.
    intros hf [[lo hb] hn]. split; cbn.
    - exists lo. apply bh_ok_cons. exact hb.
    - intros a a' ha. cbn in ha.
      destruct (haddr_dec a (HAddr s.(st_next))) as [->|hne].
      + rewrite (bh_get_cons_new _ _ _ _ hb) in ha.
        inversion ha; subst. cbn in hf. discriminate.
      + rewrite (bh_get_cons_old _ _ _ _ _ hb hne) in ha. exact (hn _ _ ha).
  Qed.

  Lemma alloc_now_next cl s : (snd (alloc_now cl s)).(st_next) = Pos.succ s.(st_next).
  Proof. reflexivity. Qed.

  Lemma hstep_alloc_now cl s : cell_fwd cl = None -> hok s -> hstep s (snd (alloc_now cl s)).
  Proof.
    intros hf h. split; [cbn; lia|exact (hok_alloc_now cl s hf h)].
  Qed.

  Lemma heap_upd_shape a cl s s' :
    heap_upd a cl s = Some s' ->
    s'.(st_next) = s.(st_next) /\ s'.(st_room) = s.(st_room)
    /\ s'.(st_steps) = s.(st_steps) /\ s'.(st_gam) = s.(st_gam)
    /\ s'.(st_memo) = s.(st_memo) /\ bh_upd a cl s.(st_heap) = Some s'.(st_heap).
  Proof.
    unfold heap_upd. destruct (bh_upd a cl s.(st_heap)) as [h'|] eqn:e; cbn; [|discriminate].
    intros he. inversion he; subst. cbn. repeat split; try reflexivity.
  Qed.

  Lemma hstep_heap_upd a cl s s' :
    cell_fwd cl = None -> hok s -> heap_upd a cl s = Some s' -> hstep s s'.
  Proof.
    intros hf [[lo hb] hn] he.
    destruct (heap_upd_shape _ _ _ _ he) as (hn1 & _ & _ & _ & _ & hu).
    split; [rewrite hn1; apply Pos.le_refl|].
    split.
    - exists lo. rewrite hn1. exact (bh_upd_ok _ _ _ _ _ _ hb hu).
    - intros b b' hb'. destruct (haddr_dec b a) as [->|hne].
      + rewrite (bh_get_upd_same _ _ _ _ hu) in hb'.
        inversion hb'; subst. cbn in hf. discriminate.
      + rewrite (bh_get_upd_other _ _ _ _ _ hu hne) in hb'. exact (hn _ _ hb').
  Qed.

  Lemma tick_shape s s' :
    tick s = Some s' ->
    s'.(st_heap) = s.(st_heap) /\ s'.(st_next) = s.(st_next)
    /\ s'.(st_room) = s.(st_room) /\ s'.(st_gam) = s.(st_gam)
    /\ s'.(st_memo) = s.(st_memo).
  Proof.
    unfold tick. destruct s.(st_steps) eqn:e; [discriminate|].
    intros he. inversion he; subst. cbn. repeat split; reflexivity.
  Qed.

  Lemma hstep_tick s s' : hok s -> tick s = Some s' -> hstep s s'.
  Proof.
    intros [hb hn] he. destruct (tick_shape _ _ he) as (h1 & h2 & _).
    split; [rewrite h2; apply Pos.le_refl|].
    split; [rewrite h2, h1; exact hb|rewrite h1; exact hn].
  Qed.

  (** [new_entry], [once_body] and [delta] touch only the memo. *)

  Lemma new_entry_shape t u ns s :
    (snd (new_entry X_type X t u ns s)).(st_heap) = s.(st_heap)
    /\ (snd (new_entry X_type X t u ns s)).(st_next) = s.(st_next)
    /\ (snd (new_entry X_type X t u ns s)).(st_room) = s.(st_room)
    /\ (snd (new_entry X_type X t u ns s)).(st_steps) = s.(st_steps)
    /\ (snd (new_entry X_type X t u ns s)).(st_gam) = s.(st_gam)
    /\ ((snd (new_entry X_type X t u ns s)).(st_memo)).(m_delta)
       = (s.(st_memo)).(m_delta).
  Proof. repeat split; reflexivity. Qed.

  Lemma once_body_shape c s :
    (snd (once_body c s)).(st_heap) = s.(st_heap)
    /\ (snd (once_body c s)).(st_next) = s.(st_next)
    /\ (snd (once_body c s)).(st_room) = s.(st_room)
    /\ (snd (once_body c s)).(st_steps) = s.(st_steps)
    /\ (snd (once_body c s)).(st_gam) = s.(st_gam)
    /\ ((snd (once_body c s)).(st_memo)).(m_delta) = (s.(st_memo)).(m_delta).
  Proof.
    unfold once_body.
    destruct (get2 c.(c_entry) c.(c_path) ((s.(st_memo)).(m_once))) as [b|];
      cbn; repeat split; reflexivity.
  Qed.

  Lemma delta_shape kn u s r s' :
    delta X_type X kn u s = COk (r, s') ->
    s'.(st_heap) = s.(st_heap) /\ s'.(st_next) = s.(st_next)
    /\ s'.(st_room) = s.(st_room) /\ s'.(st_steps) = s.(st_steps)
    /\ s'.(st_gam) = s.(st_gam).
  Proof.
    unfold delta, delta_new.
    destruct (dt_find kn ((s.(st_memo)).(m_delta))) as [[|body insts]|].
    - intros he. inversion he; subst. repeat split; reflexivity.
    - destruct (find_inst u insts) as [[i t]|].
      + intros he. inversion he; subst. repeat split; reflexivity.
      + destruct (new_entry X_type X body u (NSConst kn) s) as [c s1] eqn:e1.
        intros he. inversion he; subst. cbn.
        change s1 with (snd (c, s1)). rewrite <- e1.
        destruct (new_entry_shape body u (NSConst kn) s) as (p1 & p2 & p3 & p4 & p5 & _).
        rewrite p1, p2, p3, p4, p5. repeat split; reflexivity.
    - destruct (abstract_env_lookup X kn) as [[cb|mib]|]; [|discriminate|discriminate].
      destruct cb.(cst_body) as [body|].
      + destruct (new_entry X_type X body u (NSConst kn) s) as [c s1] eqn:e1.
        intros he. inversion he; subst. cbn.
        change s1 with (snd (c, s1)). rewrite <- e1.
        destruct (new_entry_shape body u (NSConst kn) s) as (p1 & p2 & p3 & p4 & p5 & _).
        rewrite p1, p2, p3, p4, p5. repeat split; reflexivity.
      + intros he. inversion he; subst. repeat split; reflexivity.
  Qed.

  Lemma hstep_delta kn u s r s' : hok s -> delta X_type X kn u s = COk (r, s') -> hstep s s'.
  Proof.
    intros [hb hn] he. destruct (delta_shape _ _ _ _ _ he) as (h1 & h2 & _).
    split; [rewrite h2; apply Pos.le_refl|].
    split; [rewrite h2, h1; exact hb|rewrite h1; exact hn].
  Qed.

  Lemma hstep_new_entry t u ns s :
    hok s -> hstep s (snd (new_entry X_type X t u ns s)).
  Proof.
    intros [hb hn]. destruct (new_entry_shape t u ns s) as (p1 & p2 & _).
    split; [rewrite p2; apply Pos.le_refl|].
    split; [rewrite p2, p1; exact hb|rewrite p1; exact hn].
  Qed.

  Lemma hstep_once_body c s : hok s -> hstep s (snd (once_body c s)).
  Proof.
    intros [hb hn]. destruct (once_body_shape c s) as (p1 & p2 & _).
    split; [rewrite p2; apply Pos.le_refl|].
    split; [rewrite p2, p1; exact hb|rewrite p1; exact hn].
  Qed.

  Lemma hstep_set_gam g s : hok s -> hstep s (set_gam g s).
  Proof. intros h. split; [apply Pos.le_refl|exact h]. Qed.

  (** The renamed cell of a collection is a forwarding pointer only if the cell was one. *)
  Lemma rn_cell_fwd_none {G : Type} (f : haddr -> G -> cbn_res (haddr * G)) cl g cl' g' :
    cell_fwd cl = None -> rn_cell f cl g = COk (cl', g') -> cell_fwd cl' = None.
  Proof.
    destruct cl as [vals n o c|v| |b]; intros hf he; unfold rn_cell in he.
    - destruct (rn_slots f vals g) as [[vs' g1]|w] eqn:e1; [|discriminate].
      injection he as he1 he2. subst cl'. reflexivity.
    - destruct (rn_value f v g) as [[v' g1]|w] eqn:e1; [|discriminate].
      injection he as he1 he2. subst cl'. reflexivity.
    - injection he as he1 he2. subst cl'. reflexivity.
    - discriminate hf.
  Qed.

  Lemma collect_cell_nofwd cl rs rs' s s' :
    cell_fwd cl = None -> collect (RC cl :: rs) s = COk (rs', s') ->
    exists cl' rs2, rs' = RC cl' :: rs2 /\ cell_fwd cl' = None.
  Proof.
    intros hf e. destruct (collect_inv _ _ _ _ e) as [gm [g1 [g2 [hr _]]]].
    rewrite rn_roots_cons, rn_root_RC in hr.
    destruct (rn_cell (gc_copy (fuel_of_pos s.(st_next) (fun _ : unit => FO))) cl g1)
      as [[cl' ga]|w] eqn:e1; [|discriminate].
    destruct (rn_roots (gc_copy (fuel_of_pos s.(st_next) (fun _ : unit => FO))) rs ga)
      as [[l gb]|w] eqn:e2; [|discriminate].
    injection hr as hr1 hr2. subst rs'.
    exists cl', l. split; [reflexivity|].
    exact (rn_cell_fwd_none _ _ _ _ _ hf e1).
  Qed.

  Lemma hstep_alloc cl rs s a rs' s' :
    cell_fwd cl = None -> hok s -> alloc stress cl rs s = COk (a, rs', s') -> hstep s s'.
  Proof.
    intros hf hk he.
    destruct (gc_due stress s) eqn:eg.
    - rewrite (alloc_gc stress cl rs s eg) in he.
      destruct (collect (RC cl :: rs) s) as [[rs2 s2]|w] eqn:ec; [|discriminate].
      destruct (collect_cell_nofwd _ _ _ _ _ hf ec) as [cl2 [rs3 [-> hf2]]].
      inversion he; subst.
      destruct (collect_sound 0 _ _ _ _ (proj2 hk) ec) as (hso & hnf & hnext & _).
      assert (hk2 : hok s2).
      { split; [exists s.(st_next); exact (so_heap _ _ hso)|exact hnf]. }
      apply (hstep_trans s s2); [split; [exact hnext|exact hk2]|].
      exact (hstep_alloc_now cl2 s2 hf2 hk2).
    - rewrite (alloc_no_gc stress cl rs s eg) in he. inversion he; subst.
      exact (hstep_alloc_now cl s hf hk).
  Qed.

  (** Accumulating forms, so that a chain of steps is one [eauto] away. *)

  Lemma hstep_alloc' s s1 s2 cl rs a rs' :
    hstep s s1 -> cell_fwd cl = None -> alloc stress cl rs s1 = COk (a, rs', s2) ->
    hstep s s2.
  Proof.
    intros h1 hf he.
    exact (hstep_trans _ _ _ h1 (hstep_alloc _ _ _ _ _ _ hf (proj2 h1) he)).
  Qed.

  Lemma hstep_alloc_susp' s s1 s2 vals n o c rs a rs' :
    hstep s s1 -> alloc stress (CSusp vals n o c) rs s1 = COk (a, rs', s2) -> hstep s s2.
  Proof. intros h1 he. eapply hstep_alloc'; [exact h1| |exact he]. reflexivity. Qed.

  Lemma hstep_alloc_done' s s1 s2 v rs a rs' :
    hstep s s1 -> alloc stress (CDone v) rs s1 = COk (a, rs', s2) -> hstep s s2.
  Proof. intros h1 he. eapply hstep_alloc'; [exact h1| |exact he]. reflexivity. Qed.

  Lemma hstep_delta' s s1 s2 kn u r :
    hstep s s1 -> delta X_type X kn u s1 = COk (r, s2) -> hstep s s2.
  Proof.
    intros h1 he. exact (hstep_trans _ _ _ h1 (hstep_delta _ _ _ _ _ (proj2 h1) he)).
  Qed.

  Lemma hstep_tick' s s1 s2 : hstep s s1 -> tick s1 = Some s2 -> hstep s s2.
  Proof.
    intros h1 he. exact (hstep_trans _ _ _ h1 (hstep_tick _ _ (proj2 h1) he)).
  Qed.

  Lemma hstep_heap_upd' s s1 s2 a cl :
    hstep s s1 -> cell_fwd cl = None -> heap_upd a cl s1 = Some s2 -> hstep s s2.
  Proof.
    intros h1 hf he.
    exact (hstep_trans _ _ _ h1 (hstep_heap_upd _ _ _ _ hf (proj2 h1) he)).
  Qed.

  Lemma hstep_new_entry' s s1 t u ns :
    hstep s s1 -> hstep s (snd (new_entry X_type X t u ns s1)).
  Proof.
    intros h1. exact (hstep_trans _ _ _ h1 (hstep_new_entry t u ns s1 (proj2 h1))).
  Qed.

  Lemma hstep_once_body' s s1 c : hstep s s1 -> hstep s (snd (once_body c s1)).
  Proof. intros h1. exact (hstep_trans _ _ _ h1 (hstep_once_body c s1 (proj2 h1))). Qed.

  Lemma hstep_set_gam' s s1 g : hstep s s1 -> hstep s (set_gam g s1).
  Proof. intros h1. exact (hstep_trans _ _ _ h1 (hstep_set_gam g s1 (proj2 h1))). Qed.


  Lemma hstep_alloc3 s s1 s2 cl rs a rs' :
    hstep s s1 -> alloc stress cl rs s1 = COk (a, rs', s2) -> cell_fwd cl = None ->
    hstep s s2.
  Proof. intros h1 he hf. exact (hstep_alloc' _ _ _ _ _ _ _ h1 hf he). Qed.

  (** Forward chaining: the one [hstep s ?] hypothesis is extended by each equation in
    turn. There is no search, so a branch of the machine with a dozen state changes costs
    a dozen steps. *)
  Local Ltac chain_step :=
    repeat
      match goal with
      | h : CFail _ = COk _ |- _ => discriminate h
      | h : None = Some _ |- _ => discriminate h
      | h : COk _ = COk _ |- _ => inversion h; subst; clear h
      | h0 : hstep ?s ?s1, h : alloc stress _ _ ?s1 = COk (_, _, ?s2) |- _ =>
        let hx := fresh "hs" in
        assert (hx : hstep s s2) by (eapply hstep_alloc3; [exact h0|exact h|reflexivity]);
        clear h h0
      | h0 : hstep ?s ?s1, h : delta X_type X _ _ ?s1 = COk (_, ?s2) |- _ =>
        let hx := fresh "hs" in
        assert (hx : hstep s s2) by (exact (hstep_delta' _ _ _ _ _ _ h0 h)); clear h h0
      | h0 : hstep ?s ?s1, h : tick ?s1 = Some ?s2 |- _ =>
        let hx := fresh "hs" in
        assert (hx : hstep s s2) by (exact (hstep_tick' _ _ _ h0 h)); clear h h0
      | h0 : hstep ?s ?s1, h : new_entry X_type X ?t ?u ?ns ?s1 = (_, ?s2) |- _ =>
        let hx := fresh "hs" in
        assert (hx : hstep s s2) by
          (let hy := fresh "hy" in
           pose proof (hstep_new_entry' s s1 t u ns h0) as hy; rewrite h in hy;
           cbn in hy; exact hy);
        clear h h0
      | h0 : hstep ?s ?s1, h : once_body ?c ?s1 = (_, ?s2) |- _ =>
        let hx := fresh "hs" in
        assert (hx : hstep s s2) by
          (let hy := fresh "hy" in
           pose proof (hstep_once_body' s s1 c h0) as hy; rewrite h in hy;
           cbn in hy; exact hy);
        clear h h0
      | h0 : hstep ?s ?s1, h : heap_upd _ _ ?s1 = Some ?s2 |- _ =>
        let hx := fresh "hs" in
        assert (hx : hstep s s2) by
          (eapply hstep_heap_upd'; [exact h0| |exact h]; reflexivity);
        clear h h0
      end.

  Local Ltac chain_done :=
    chain_step;
    repeat (apply hstep_set_gam');
    match goal with h : hstep _ _ |- _ => exact h end.

  Lemma hstep_gam j rs s a rs' s' :
    hok s -> gam X_type X Γ nctx stress j rs s = COk (a, rs', s') -> hstep s s'.
  Proof.
    intros hk he. unfold gam in he. cbv zeta in he.
    assert (h0 : hstep s s) by exact (hstep_refl _ hk).
    destruct (PTree.get (key_of_succ_nat j) s.(st_gam)) as [a0|] eqn:eg.
    - inversion he; subst. exact h0.
    - destruct (nth_error Γ j) as [decl|] eqn:ed; [|discriminate].
      destruct decl.(decl_body) as [b|] eqn:eb.
      + destruct (new_entry X_type X b [] (NSCtx j) s) as [c s1] eqn:e1.
        destruct (alloc stress (CSusp [] 0 (S j) c) rs s1) as [[[a1 rs1] s2]|w] eqn:ea;
          [|discriminate].
        chain_done.
      + destruct (alloc stress (CDone (VNeu (NVar (nctx - S j)) [])) rs s)
          as [[[a1 rs1] s2]|w] eqn:ea; [|discriminate].
        chain_done.
  Qed.

  Lemma hstep_gam' s s1 s2 j rs a rs' :
    hstep s s1 -> gam X_type X Γ nctx stress j rs s1 = COk (a, rs', s2) -> hstep s s2.
  Proof.
    intros h1 he. exact (hstep_trans _ _ _ h1 (hstep_gam _ _ _ _ _ _ (proj2 h1) he)).
  Qed.

  Lemma hstep_env_var n e rs s x rs' s' :
    hok s -> env_var X_type X Γ nctx stress n e rs s = COk (x, rs', s') -> hstep s s'.
  Proof.
    intros hk he. unfold env_var in he.
    destruct (nth_error e.(ev_vals) n) as [x0|].
    - inversion he; subst. exact (hstep_refl _ hk).
    - destruct (gam X_type X Γ nctx stress (n - e.(ev_nvals) + e.(ev_goff)) rs s)
        as [[[a1 rs1] s1]|w] eqn:eg; [|discriminate].
      inversion he; subst. exact (hstep_gam _ _ _ _ _ _ hk eg).
  Qed.

  Lemma hstep_env_var' s s1 s2 n e rs x rs' :
    hstep s s1 -> env_var X_type X Γ nctx stress n e rs s1 = COk (x, rs', s2) -> hstep s s2.
  Proof.
    intros h1 he. exact (hstep_trans _ _ _ h1 (hstep_env_var _ _ _ _ _ _ _ (proj2 h1) he)).
  Qed.

  Lemma hstep_arg_slot e c rs s x rs' s' :
    hok s -> arg_slot X_type X Γ nctx stress e c rs s = COk (x, rs', s') -> hstep s s'.
  Proof.
    intros hk he. unfold arg_slot in he.
    destruct (c_term c); try (inversion he; subst; exact (hstep_refl _ hk)).
    exact (hstep_env_var _ _ _ _ _ _ _ hk he).
  Qed.

  Lemma hstep_arg_slot' s s1 s2 e c rs x rs' :
    hstep s s1 -> arg_slot X_type X Γ nctx stress e c rs s1 = COk (x, rs', s2) -> hstep s s2.
  Proof.
    intros h1 he. exact (hstep_trans _ _ _ h1 (hstep_arg_slot _ _ _ _ _ _ _ (proj2 h1) he)).
  Qed.

  Lemma hstep_alloc2 cl rs s a rs' s' :
    hok s -> alloc stress cl rs s = COk (a, rs', s') -> cell_fwd cl = None -> hstep s s'.
  Proof. intros hk he hf. exact (hstep_alloc _ _ _ _ _ _ hf hk he). Qed.

  Lemma hstep_materialize x rs s a rs' s' :
    hok s -> materialize X_type X stress x rs s = COk (a, rs', s') -> hstep s s'.
  Proof.
    intros hk he. unfold materialize in he.
    destruct x as [a0|vs n o c]; [inversion he; subst; exact (hstep_refl _ hk)|].
    destruct (c_term c) eqn:ec;
      try (exact (hstep_alloc2 _ _ _ _ _ _ hk he eq_refl)).
    - (* tConst: the delta memo may add an entry first *)
      destruct (delta X_type X k ui s) as [[[c'|] s1]|w] eqn:ed.
      + eapply hstep_alloc3;
          [exact (hstep_delta _ _ _ _ _ hk ed)|exact he|reflexivity].
      + eapply hstep_alloc3;
          [exact (hstep_delta _ _ _ _ _ hk ed)|exact he|reflexivity].
      + exact (hstep_alloc2 _ _ _ _ _ _ hk he eq_refl).
    - (* tFix *)
      destruct (nth_error mfix idx) as [def|];
        exact (hstep_alloc2 _ _ _ _ _ _ hk he eq_refl).
  Qed.

  Lemma hstep_materialize' s s1 s2 x rs a rs' :
    hstep s s1 -> materialize X_type X stress x rs s1 = COk (a, rs', s2) -> hstep s s2.
  Proof.
    intros h1 he.
    exact (hstep_trans _ _ _ h1 (hstep_materialize _ _ _ _ _ _ (proj2 h1) he)).
  Qed.

  Lemma hstep_bind x body rs s y rs' s' :
    hok s -> bind X_type X stress x body rs s = COk (y, rs', s') -> hstep s s'.
  Proof.
    intros hk he. unfold bind in he.
    destruct x as [a0|vs n o c]; [inversion he; subst; exact (hstep_refl _ hk)|].
    destruct (once_body body s) as [b s1] eqn:eo.
    assert (hs1 : hstep s s1).
    { pose proof (hstep_once_body body s hk) as hy. rewrite eo in hy. cbn in hy. exact hy. }
    destruct b.
    - inversion he; subst. exact hs1.
    - destruct (materialize X_type X stress (SInl vs n o c) rs s1) as [[[a1 rs1] s2]|w]
        eqn:em; [|discriminate].
      inversion he; subst.
      exact (hstep_trans _ _ _ hs1 (hstep_materialize _ _ _ _ _ _ (proj2 hs1) em)).
  Qed.

  Lemma hstep_bind' s s1 s2 x body rs y rs' :
    hstep s s1 -> bind X_type X stress x body rs s1 = COk (y, rs', s2) -> hstep s s2.
  Proof.
    intros h1 he. exact (hstep_trans _ _ _ h1 (hstep_bind _ _ _ _ _ _ _ (proj2 h1) he)).
  Qed.

  Lemma hstep_mat_all : forall d l rs s al rs' s',
    hok s -> mat_all X_type X stress d l rs s = COk (al, rs', s') -> hstep s s'.
  Proof.
    intros d. induction d as [|k ih]; intros l rs s al rs' s' hk he;
      destruct l as [|x l]; cbn [mat_all] in he;
      try (inversion he; subst; exact (hstep_refl _ hk)).
    destruct (materialize X_type X stress x (RSk l :: rs) s) as [[[a1 rs1] s1]|w] eqn:em;
      [|discriminate].
    destruct rs1 as [|r rs2]; [discriminate|]. destruct r; try discriminate.
    destruct (mat_all X_type X stress (k tt) l0 (RA a1 :: rs2) s1) as [[[al1 rs3] s2]|w]
      eqn:em2; [|discriminate].
    destruct rs3 as [|r rs4]; [discriminate|]. destruct r; try discriminate.
    assert (hs1 : hstep s s1) by exact (hstep_materialize _ _ _ _ _ _ hk em).
    assert (hs2 : hstep s s2)
      by exact (hstep_trans _ _ _ hs1 (ih tt _ _ _ _ _ _ (proj2 hs1) em2)).
    inversion he; subst. exact hs2.
  Qed.

  Lemma hstep_mat_all' s s1 s2 d l rs al rs' :
    hstep s s1 -> mat_all X_type X stress d l rs s1 = COk (al, rs', s2) -> hstep s s2.
  Proof.
    intros h1 he.
    exact (hstep_trans _ _ _ h1 (hstep_mat_all _ _ _ _ _ _ _ (proj2 h1) he)).
  Qed.

  Lemma hstep_push_fix_cells : forall n e c i acc rs s e' rs' s',
    hok s -> push_fix_cells stress e c i n acc rs s = COk (e', rs', s') ->
    hstep s s'.
  Proof.
    intros n. induction n as [|n ih]; intros e c i acc rs s e' rs' s' hk he;
      cbn [push_fix_cells] in he.
    - inversion he; subst. exact (hstep_refl _ hk).
    - destruct (alloc stress (CDone (VFix e c i [])) (RE e :: RE acc :: rs) s)
        as [[[a1 rs1] s1]|w] eqn:ea; [|discriminate].
      destruct rs1 as [|r rs2]; [discriminate|]. destruct r; try discriminate.
      destruct rs2 as [|r rs3]; [discriminate|]. destruct r; try discriminate.
      assert (hs1 : hstep s s1)
        by (eapply hstep_alloc3; [exact (hstep_refl _ hk)|exact ea|reflexivity]).
      exact (hstep_trans _ _ _ hs1 (ih _ _ _ _ _ _ _ _ _ (proj2 hs1) he)).
  Qed.

  Lemma hstep_push_fix_cells' s s1 s2 n e c i acc rs e' rs' :
    hstep s s1 -> push_fix_cells stress e c i n acc rs s1 = COk (e', rs', s2) ->
    hstep s s2.
  Proof.
    intros h1 he.
    exact (hstep_trans _ _ _ h1 (hstep_push_fix_cells _ _ _ _ _ _ _ _ _ _ (proj2 h1) he)).
  Qed.

  (** ** The machine itself never gives an address back

    This is what lets the budget below be spent across two calls in a row: the state after
    the first call is still under the bound the whole call has. It holds for every run,
    including one that collects, which is why it is proved before anything about
    readings. *)

  Local Ltac chain_m ihF ihS ihW ihX ihA :=
    repeat
      match goal with
      | h : CFail _ = COk _ |- _ => discriminate h
      | h : None = Some _ |- _ => discriminate h
      | h : COk _ = COk _ |- _ => inversion h; subst; clear h
      | h0 : hstep ?s ?s1, h : new_entry X_type X ?t ?u ?ns ?s1 = (_, ?s2) |- _ =>
        let hx := fresh "hs" in
        assert (hx : hstep s s2) by
          (let hy := fresh "hy" in
           pose proof (hstep_new_entry' s s1 t u ns h0) as hy; rewrite h in hy;
           cbn in hy; exact hy);
        clear h
      | h0 : hstep ?s ?s1, h : once_body ?c ?s1 = (_, ?s2) |- _ =>
        let hx := fresh "hs" in
        assert (hx : hstep s s2) by
          (let hy := fresh "hy" in
           pose proof (hstep_once_body' s s1 c h0) as hy; rewrite h in hy;
           cbn in hy; exact hy);
        clear h
      (** One clause for every call that returns a value, a root list and a state: the
        machine's own functions are matched up to the unfolding of their mutual
        fixpoint, so their head cannot be named here. *)
      | h0 : hstep ?s ?s1, h : _ = COk (_, _, ?s2) |- _ =>
        let hx := fresh "hs" in
        assert (hx : hstep s s2) by
          (first
            [ eapply hstep_trans; [exact h0|eapply ihF; [exact (proj2 h0)|exact h]]
            | eapply hstep_trans; [exact h0|eapply ihS; [exact (proj2 h0)|exact h]]
            | eapply hstep_trans; [exact h0|eapply ihW; [exact (proj2 h0)|exact h]]
            | eapply hstep_trans; [exact h0|eapply ihX; [exact (proj2 h0)|exact h]]
            | eapply hstep_trans; [exact h0|eapply ihA; [exact (proj2 h0)|exact h]]
            | eapply hstep_gam'; [exact h0|exact h]
            | eapply hstep_env_var'; [exact h0|exact h]
            | eapply hstep_arg_slot'; [exact h0|exact h]
            | eapply hstep_materialize'; [exact h0|exact h]
            | eapply hstep_bind'; [exact h0|exact h]
            | eapply hstep_mat_all'; [exact h0|exact h]
            | eapply hstep_push_fix_cells'; [exact h0|exact h]
            | eapply hstep_alloc3; [exact h0|exact h|reflexivity] ]);
        clear h
      | h0 : hstep ?s ?s1, h : delta X_type X _ _ ?s1 = COk (_, ?s2) |- _ =>
        let hx := fresh "hs" in
        assert (hx : hstep s s2) by (exact (hstep_delta' _ _ _ _ _ _ h0 h)); clear h
      | h0 : hstep ?s ?s1, h : tick ?s1 = Some ?s2 |- _ =>
        let hx := fresh "hs" in
        assert (hx : hstep s s2) by (exact (hstep_tick' _ _ _ h0 h)); clear h
      | h0 : hstep ?s ?s1, h : heap_upd _ _ ?s1 = Some ?s2 |- _ =>
        let hx := fresh "hs" in
        assert (hx : hstep s s2) by
          (eapply hstep_heap_upd'; [exact h0| |exact h]; reflexivity);
        clear h
      | h : context [match ?x with COk _ => _ | CFail _ => _ end] |- _ =>
        match type of x with
        | cbn_res (_ * _ * _) => destruct x as [[[? ?] ?]|?] eqn:?
        | cbn_res (_ * _) => destruct x as [[? ?]|?] eqn:?
        end
      | h : context [match ?x with Some _ => _ | None => _ end] |- _ =>
        destruct x eqn:?
      | h : context [match ?x with nil => _ | cons _ _ => _ end] |- _ =>
        destruct x as [|? ?]
      | h : context [match ?r with RA _ => _ | RSl _ => _ | RE _ => _ | RV _ => _
                     | RSk _ => _ | RSp _ => _ | RC _ => _ end] |- _ => destruct r
      | h : context [match ?x with true => _ | false => _ end] |- _ => destruct x eqn:?
      | h : context [match ?v with VCon _ _ => _ | VLam _ _ => _ | VFix _ _ _ _ => _
                     | VStuckFix _ _ _ _ => _ | VNeu _ _ => _ | VOpen _ _ => _
                     | VStuck _ _ _ => _ end] |- _ => destruct v eqn:?
      | h : context [match ?x with CSusp _ _ _ _ => _ | CDone _ => _ | CBusy => _
                     | CFwd _ => _ end] |- _ => destruct x eqn:?
      | h : context [match ?x with SAddr _ => _ | SInl _ _ _ _ => _ end] |- _ =>
        destruct x eqn:?
      | h : context [match ?x with _ => _ end] |- _ =>
        match type of x with
        | term => destruct x eqn:?
        | nat => destruct x eqn:?
        end
      end.

  Local Ltac chain_fin ihF ihS ihW ihX ihA :=
    chain_m ihF ihS ihW ihX ihA;
    first [ match goal with h : hstep _ _ |- _ => exact h end
          | match goal with h : hok _ |- _ => exact (hstep_refl _ h) end ].

  Lemma machine_hstep : forall d,
    (forall a rs s v rs' s', hok s ->
        force X_type X Γ nctx stress d a rs s = COk (v, rs', s') -> hstep s s')
    /\ (forall x stk rs s v rs' s', hok s ->
        eval_slot X_type X Γ nctx stress d x stk rs s = COk (v, rs', s') -> hstep s s')
    /\ (forall e c stk rs s v rs' s', hok s ->
        whnf X_type X Γ nctx stress d e c stk rs s = COk (v, rs', s') -> hstep s s')
    /\ (forall e c mfix idx stk rs s v rs' s', hok s ->
        whnf_fix X_type X Γ nctx stress d e c mfix idx stk rs s = COk (v, rs', s') ->
        hstep s s')
    /\ (forall v stk rs s w rs' s', hok s ->
        apply X_type X Γ nctx stress d v stk rs s = COk (w, rs', s') -> hstep s s').
  Proof.
    intros d. induction d as [|k ih].
    - split; [|split; [|split; [|split]]].
      + intros a0 rs0 s0 v0 rs1 s1 hk he. cbn [force] in he. discriminate.
      + intros x0 stk0 rs0 s0 v0 rs1 s1 hk he. cbn [eval_slot] in he. discriminate.
      + intros e0 c0 stk0 rs0 s0 v0 rs1 s1 hk he. cbn [whnf] in he. discriminate.
      + intros e0 c0 mf0 ix0 stk0 rs0 s0 v0 rs1 s1 hk he. cbn [whnf_fix] in he.
        discriminate.
      + intros v0 stk0 rs0 s0 w0 rs1 s1 hk he. cbn [apply] in he.
        destruct stk0 as [|y0 stk0];
          [inversion he; subst; exact (hstep_refl _ hk)|discriminate].
    - destruct (ih tt) as (ihF & ihS & ihW & ihX & ihA).
      split; [|split; [|split; [|split]]].
      + intros a0 rs0 s0 v0 rs1 s1 hk he. cbn [force] in he.
        assert (h0 : hstep s0 s0) by exact (hstep_refl _ hk).
        chain_fin ihF ihS ihW ihX ihA.
      + intros x0 stk0 rs0 s0 v0 rs1 s1 hk he. cbn [eval_slot] in he.
        assert (h0 : hstep s0 s0) by exact (hstep_refl _ hk).
        chain_fin ihF ihS ihW ihX ihA.
      + intros e0 c0 stk0 rs0 s0 v0 rs1 s1 hk he. cbn [whnf] in he.
        assert (h0 : hstep s0 s0) by exact (hstep_refl _ hk).
        chain_fin ihF ihS ihW ihX ihA.
      + intros e0 c0 mf0 ix0 stk0 rs0 s0 v0 rs1 s1 hk he. cbn [whnf_fix] in he.
        assert (h0 : hstep s0 s0) by exact (hstep_refl _ hk).
        chain_fin ihF ihS ihW ihX ihA.
      + intros v0 stk0 rs0 s0 w0 rs1 s1 hk he. cbn [apply] in he.
        assert (h0 : hstep s0 s0) by exact (hstep_refl _ hk).
        chain_fin ihF ihS ihW ihX ihA.
  Qed.

  (** ** The room budget

    A run that allocates fewer cells than [st_room] leaves it never collects, because
    [gc_due] is [false] while the room is not spent. [fits s s'] says exactly that of the
    run from [s] to its own result state [s']; [consv] is the conservation law an
    allocation obeys, and it carries the budget from one call to the next. *)

  Definition nextn (s : cbn_state) : nat := Pos.to_nat s.(st_next).
  Definition roomn (s : cbn_state) : nat := N.to_nat s.(st_room).
  Definition fits (s s' : cbn_state) : Prop := (nextn s' < nextn s + roomn s)%nat.
  Definition consv (s s' : cbn_state) : Prop :=
    (nextn s + roomn s = nextn s' + roomn s')%nat.

  Lemma consv_refl s : consv s s.
  Proof. reflexivity. Qed.

  Lemma consv_trans s1 s2 s3 : consv s1 s2 -> consv s2 s3 -> consv s1 s3.
  Proof. unfold consv. intros h1 h2. rewrite h1. exact h2. Qed.

  Lemma hstep_nextn s s' : hstep s s' -> (nextn s <= nextn s')%nat.
  Proof. intros [h _]. unfold nextn. lia. Qed.

  Lemma fits_room s s' : fits s s' -> hstep s s' -> roomn s <> 0.
  Proof. unfold fits. intros hf hs. pose proof (hstep_nextn _ _ hs). lia. Qed.

  (** The second of two calls in a row inherits the budget. *)
  Lemma fits_next s s1 s2 : fits s s2 -> consv s s1 -> fits s1 s2.
  Proof. unfold fits, consv. intros h1 h2. lia. Qed.

  Lemma fits_first s s1 s2 : fits s s2 -> hstep s1 s2 -> fits s s1.
  Proof. unfold fits. intros h1 h2. pose proof (hstep_nextn _ _ h2). lia. Qed.

  (** ** What the machine assumes of a state

    Beside the heap laws of [state_ok] and the absence of forwarding pointers, the state
    carries a ghost map: every cell has a ghost term, and the cell stands for a reduct of
    it, unless the cell is being forced, in which case its caller carries the reading. *)

  Definition delta_inv (s : cbn_state) : Prop :=
    forall kn d, dt_find kn ((s.(st_memo)).(m_delta)) = Some d ->
      match d with
      | DAxiom => True
      | DBody body insts =>
        simple_term body = true
        /\ (exists cb, abstract_env_lookup X kn = Some (ConstantDecl cb)
                       /\ cb.(cst_body) = Some body)
        /\ (forall u i t, In (u, i, t) insts -> t = inst_code u body)
      end.

  Record gok (lo : positive) (G : haddr -> option term) (s : cbn_state) : Prop := mkGok {
    gk_state : state_ok lo s;
    gk_nofwd : heap_nofwd s.(st_heap);
    gk_cells : forall a cl, heap_get a s = Some cl ->
      exists t, G a = Some t
        /\ (cl = CBusy \/ exists u, g_cell G cl u /\ cred t u);
    gk_dom : forall a t, G a = Some t ->
      (lo <= ha_p a)%positive /\ (ha_p a < s.(st_next))%positive;
    gk_gam : forall j a, PTree.get (key_of_succ_nat j) s.(st_gam) = Some a ->
      exists t, ctx_den Γ nctx lvl j = Some t /\ G a = Some t;
    gk_delta : delta_inv s }.

  Lemma gok_hok lo G s : gok lo G s -> hok s.
  Proof.
    intros [h1 h2 _ _ _ _]. split; [exists lo; exact (so_heap _ _ h1)|exact h2].
  Qed.

  (** ** The algebra of ghost readings *)

  Lemma g_susp_inv G e t u :
    g_susp G e t u ->
    exists ts, g_slots G e.(ev_vals) ts /\ e.(ev_nvals) = #|e.(ev_vals)|
      /\ simple_term t = true
      /\ u = subst ts 0 (lift (lvl - nctx + e.(ev_goff)) e.(ev_nvals) t).
  Proof.
    intros h. inversion h; subst. cbn [ev_vals ev_nvals ev_goff].
    exists ts. repeat split; assumption.
  Qed.

  Lemma g_slots_length G l ts : g_slots G l ts -> #|ts| = #|l|.
  Proof. induction 1; cbn; [reflexivity|]. rewrite IHg_slots. reflexivity. Qed.

  Lemma g_slots_nth G l ts n x :
    g_slots G l ts -> nth_error l n = Some x ->
    exists t, nth_error ts n = Some t /\ g_slot G x t.
  Proof.
    intros h. revert n. induction h as [|y l t ts hy hl ih]; intros n hn.
    - destruct n; discriminate.
    - destruct n as [|n]; cbn in hn.
      + injection hn as <-. exists t. split; [reflexivity|exact hy].
      + exact (ih n hn).
  Qed.

  (** The reading of a suspension whose code is an application, a lambda, a let or a
    constant: the machine's own decomposition, with [subst] and [lift] computed. *)

  Lemma subst_cons_app (tx : term) (ts : list term) (b : term) :
    subst (tx :: ts) 0 b = subst [tx] 0 (subst ts 1 b).
  Proof. pose proof (subst_app_simpl [tx] ts 0 b) as h. cbn in h. exact h. Qed.

  Lemma g_susp_app G e f a u :
    g_susp G e (tApp f a) u ->
    exists uf ua, u = tApp uf ua /\ g_susp G e f uf /\ g_susp G e a ua.
  Proof.
    intros h. destruct (g_susp_inv _ _ _ _ h) as [ts (h1 & h2 & h3 & ->)].
    destruct (simple_app _ _ h3) as [hf ha].
    destruct e as [vals nvals goff]. cbn [ev_vals ev_nvals ev_goff] in *. subst nvals.
    cbn [lift subst].
    eexists; eexists; split; [reflexivity|].
    split; constructor; (exact h1 || reflexivity || assumption).
  Qed.

  (** A [tConst] has no free variables, so a [lift] followed by a [subst] leaves it
    alone: the reading of a suspension whose code is a constant is that constant, whatever
    the environment. *)
  Lemma subst_lift_const ts n m p kn ui :
    subst ts n (lift m p (tConst kn ui)) = tConst kn ui.
  Proof. reflexivity. Qed.

  Lemma g_susp_const G e kn ui u : g_susp G e (tConst kn ui) u -> u = tConst kn ui.
  Proof.
    intros h. destruct (g_susp_inv _ _ _ _ h) as [ts (_ & _ & _ & ->)]. reflexivity.
  Qed.

  Lemma g_susp_tind G e i ui u : g_susp G e (tInd i ui) u -> u = tInd i ui.
  Proof.
    intros h. destruct (g_susp_inv _ _ _ _ h) as [ts (_ & _ & _ & ->)]. reflexivity.
  Qed.

  Lemma g_susp_construct G e i n ui u :
    g_susp G e (tConstruct i n ui) u -> u = tConstruct i n ui.
  Proof.
    intros h. destruct (g_susp_inv _ _ _ _ h) as [ts (_ & _ & _ & ->)]. reflexivity.
  Qed.

  (** Pushing a slot on the environment is PCUIC's substitution on the reading: this is
    the substitution-composition the beta and zeta rules need. *)

  Lemma g_susp_lam G e na A b u :
    g_susp G e (tLambda na A b) u ->
    exists A' B, u = tLambda na A' B
      /\ (forall x tx, g_slot G x tx -> g_susp G (env_push x e) b (subst [tx] 0 B)).
  Proof.
    intros h. destruct (g_susp_inv _ _ _ _ h) as [ts (h1 & h2 & h3 & ->)].
    destruct (simple_lam _ _ _ h3) as [hA hb].
    destruct e as [vals nvals goff]. cbn [ev_vals ev_nvals ev_goff] in *. subst nvals.
    cbn [lift subst].
    eexists; eexists; split; [reflexivity|].
    intros x tx hx.
    rewrite <- (subst_cons_app tx ts (lift (lvl - nctx + goff) (S #|vals|) b)).
    unfold env_push. cbn [ev_vals ev_nvals ev_goff].
    exact (g_susp_intro G (x :: vals) (S #|vals|) goff b (tx :: ts)
             (g_slots_cons G x vals tx ts hx h1) eq_refl hb).
  Qed.

  Lemma g_susp_letin G e na d T b u :
    g_susp G e (tLetIn na d T b) u ->
    exists d' T' B, u = tLetIn na d' T' B /\ g_susp G e d d'
      /\ (forall x tx, g_slot G x tx -> g_susp G (env_push x e) b (subst [tx] 0 B)).
  Proof.
    intros h. destruct (g_susp_inv _ _ _ _ h) as [ts (h1 & h2 & h3 & ->)].
    destruct (simple_letin _ _ _ _ h3) as (hd & hT & hb).
    destruct e as [vals nvals goff]. cbn [ev_vals ev_nvals ev_goff] in *. subst nvals.
    cbn [lift subst].
    eexists; eexists; eexists; split; [reflexivity|].
    split.
    - constructor; (exact h1 || reflexivity || assumption).
    - intros x tx hx.
      rewrite <- (subst_cons_app tx ts (lift (lvl - nctx + goff) (S #|vals|) b)).
      unfold env_push. cbn [ev_vals ev_nvals ev_goff].
      exact (g_susp_intro G (x :: vals) (S #|vals|) goff b (tx :: ts)
               (g_slots_cons G x vals tx ts hx h1) eq_refl hb).
  Qed.



  (** ** What this file assumes

    [hnctx] and [hlvl] say what the machine's comment says of its own parameters.
    [Γ_simple] keeps the let-bodies of the context inside the rules covered here.
    [delta_sound] and [delta_inv_pres] are the delta memo of [PCUICCallByNeed] against
    PCUIC: they need the laws of the [dtrie] (which step 2a does not have) and
    [red_delta] with [declared_constant_closed_body]. *)

  Hypothesis hnctx : nctx = #|Γ|.
  Hypothesis hlvl : nctx <= lvl.
  Hypothesis Γ_simple : forall j decl b,
    nth_error Γ j = Some decl -> decl.(decl_body) = Some b -> simple_term b = true.
  Hypothesis delta_sound : forall kn u s c s',
    delta_inv s -> delta X_type X kn u s = COk (Some c, s') ->
    simple_term c.(c_term) = true /\ cred (tConst kn u) (lift (lvl - nctx) 0 c.(c_term)).
  Hypothesis delta_inv_pres : forall kn u s r s',
    delta_inv s -> delta X_type X kn u s = COk (r, s') -> delta_inv s'.

  (** ** The state operations against the ghost map *)

  Lemma haddr_eqb_eq a b : haddr_eqb a b = true -> a = b.
  Proof.
    destruct a as [p], b as [q]. unfold haddr_eqb. cbn. intros h.
    apply Pos.eqb_eq in h. rewrite h. reflexivity.
  Qed.

  Lemma haddr_eqb_refl a : haddr_eqb a a = true.
  Proof. destruct a as [p]. unfold haddr_eqb. cbn. apply Pos.eqb_refl. Qed.

  Lemma gdom_addrs_in lo G s l :
    (forall a t, G a = Some t -> (lo <= ha_p a)%positive /\ (ha_p a < s.(st_next))%positive) ->
    Forall (gdef G) l -> addrs_in lo s.(st_next) l.
  Proof.
    intros hd. induction 1 as [|b l hb hl ih]; constructor; [|exact ih].
    destruct hb as [t ht]. exact (hd _ _ ht).
  Qed.

  Lemma delta_inv_memo s s' :
    ((s'.(st_memo)).(m_delta)) = ((s.(st_memo)).(m_delta)) -> delta_inv s -> delta_inv s'.
  Proof. intros he h kn d hd. rewrite he in hd. exact (h kn d hd). Qed.

  Lemma gok_same lo G s s1 :
    gok lo G s -> s1.(st_heap) = s.(st_heap) -> s1.(st_next) = s.(st_next) ->
    s1.(st_gam) = s.(st_gam) -> delta_inv s1 -> gok lo G s1.
  Proof.
    intros [h1 h2 h3 h4 h5 _] e1 e2 e3 hd. split.
    - destruct h1 as [p1 p2 p3]. split.
      + rewrite e1, e2. exact p1.
      + intros a cl hc. rewrite e1 in hc. rewrite e2. exact (p2 _ _ hc).
      + intros k a hk. rewrite e3 in hk. rewrite e2. exact (p3 _ _ hk).
    - rewrite e1. exact h2.
    - intros a cl hc. unfold heap_get in hc. rewrite e1 in hc. exact (h3 _ _ hc).
    - intros a t ht. rewrite e2. exact (h4 _ _ ht).
    - intros j a hj. rewrite e3 in hj. exact (h5 _ _ hj).
    - exact hd.
  Qed.

  Lemma consv_same s s1 :
    s1.(st_next) = s.(st_next) -> s1.(st_room) = s.(st_room) -> consv s s1.
  Proof. intros e1 e2. unfold consv, nextn, roomn. rewrite e1, e2. reflexivity. Qed.

  Lemma delta_gok lo G kn ui s r s1 :
    gok lo G s -> delta X_type X kn ui s = COk (r, s1) ->
    gok lo G s1 /\ consv s s1 /\ roomn s1 = roomn s.
  Proof.
    intros hok hd. destruct (delta_shape _ _ _ _ _ hd) as (e1 & e2 & e3 & _ & e5).
    split; [|split].
    - apply (gok_same lo G s); [exact hok|exact e1|exact e2|exact e5|].
      exact (delta_inv_pres kn ui s r s1 (gk_delta _ _ _ hok) hd).
    - apply consv_same; [exact e2|exact e3].
    - unfold roomn. rewrite e3. reflexivity.
  Qed.

  (** *** Allocation *)

  Lemma alloc_sound lo G cl u rs s a rs' s' :
    gok lo G s -> roomn s <> 0 -> g_cell G cl u -> cell_fwd cl = None ->
    alloc stress cl rs s = COk (a, rs', s') ->
    rs' = rs /\ consv s s'
    /\ exists G', gext G G' /\ gok lo G' s' /\ G' a = Some u.
  Proof.
    intros hok hroom hcl hfwd he.
    assert (hgc : gc_due stress s = false).
    { rewrite stress_false. destruct (gc_due false s) eqn:e; [|reflexivity].
      apply gc_due_room in e. exfalso. apply hroom. unfold roomn. rewrite e. reflexivity. }
    rewrite (alloc_no_gc stress cl rs s hgc) in he.
    inversion he; subst. clear he.
    pose (G' := fun b => if haddr_eqb b (HAddr s.(st_next)) then Some u else G b).
    assert (hnew : G' (HAddr s.(st_next)) = Some u).
    { unfold G'. rewrite haddr_eqb_refl. reflexivity. }
    assert (hold : gext G G').
    { intros b t hb. unfold G'. destruct (haddr_eqb b (HAddr s.(st_next))) eqn:eb;
        [|exact hb].
      apply haddr_eqb_eq in eb. subst b.
      destruct (gk_dom _ _ _ hok _ _ hb) as [_ hlt]. cbn in hlt. lia. }
    assert (hbok : bh_ok lo s.(st_next) s.(st_heap))
      by exact (so_heap _ _ (gk_state _ _ _ hok)).
    split; [reflexivity|].
    split.
    { unfold consv, nextn, roomn. cbn. rewrite Pos2Nat.inj_succ.
      destruct (s.(st_room)) eqn:er;
        [exfalso; apply hroom; unfold roomn; rewrite er; reflexivity|].
      cbn. lia. }
    exists G'. split; [exact hold|].
    split; [|exact hnew].
    split.
    - apply (alloc_now_state_ok lo cl s (gk_state _ _ _ hok)).
      apply (addrs_in_grow lo s.(st_next) (Pos.succ s.(st_next))); [lia|].
      apply (gdom_addrs_in lo G s); [exact (gk_dom _ _ _ hok)|].
      exact (g_cell_ad G cl u hcl).
    - exact (proj2 (hok_alloc_now cl s hfwd (gok_hok _ _ _ hok))).
    - intros b cl2 hb. unfold heap_get in hb. cbn in hb.
      destruct (haddr_dec b (HAddr s.(st_next))) as [->|hne].
      + rewrite (bh_get_cons_new _ _ _ _ hbok) in hb.
        inversion hb; subst cl2. exists u. split; [exact hnew|].
        right. exists u. split; [exact (g_cell_mono G G' hold cl u hcl)|apply cred_refl].
      + rewrite (bh_get_cons_old _ _ _ _ _ hbok hne) in hb.
        destruct (gk_cells _ _ _ hok _ _ hb) as [t [ht hrest]].
        exists t. split; [exact (hold _ _ ht)|].
        destruct hrest as [hbusy|[u1 [hu1 hred]]]; [left; exact hbusy|].
        right. exists u1. split; [exact (g_cell_mono G G' hold _ _ hu1)|exact hred].
    - intros b t hb. unfold G' in hb. cbn.
      destruct (haddr_eqb b (HAddr s.(st_next))) eqn:eb.
      + apply haddr_eqb_eq in eb. subst b. cbn.
        split; [exact (bh_ok_le _ _ _ hbok)|lia].
      + destruct (gk_dom _ _ _ hok _ _ hb) as [h1 h2]. split; [exact h1|]. cbn. lia.
    - intros j b hj. cbn in hj.
      destruct (gk_gam _ _ _ hok _ _ hj) as [t [ht hg]].
      exists t. split; [exact ht|exact (hold _ _ hg)].
    - exact (gk_delta _ _ _ hok).
  Qed.

  (** *** The context map *)

  Lemma ctx_den_red j t : ctx_den Γ nctx lvl j = Some t -> cred (tRel (lvl - nctx + j)) t.
  Proof.
    unfold ctx_den. destruct (nth_error Γ j) as [decl|] eqn:ed; [|discriminate].
    destruct decl.(decl_body) as [b|] eqn:eb; intros h; injection h as <-.
    - apply cred_one.
      assert (hn : nth_error (Γ ,,, Δ) (lvl - nctx + j) = Some decl).
      { unfold app_context. rewrite nth_error_app_ge; [|lia].
        replace (lvl - nctx + j - #|Δ|) with j by lia. exact ed. }
      pose proof (red_rel Σ ΓΔ (lvl - nctx + j) b) as hr.
      replace (lvl - nctx + S j) with (S (lvl - nctx + j)) by lia.
      apply hr. rewrite hn. cbn. rewrite eb. reflexivity.
    - apply nth_error_Some_length in ed.
      replace (lvl - S (nctx - S j)) with (lvl - nctx + j) by lia.
      apply cred_refl.
  Qed.

  Lemma gam_sound lo G j rs s a rs' s' :
    gok lo G s -> roomn s <> 0 ->
    gam X_type X Γ nctx stress j rs s = COk (a, rs', s') ->
    rs' = rs /\ consv s s'
    /\ exists G' t, gext G G' /\ gok lo G' s' /\ G' a = Some t
                    /\ cred (tRel (lvl - nctx + j)) t.
  Proof.
    intros hok hroom he. unfold gam in he. cbv zeta in he.
    destruct (PTree.get (key_of_succ_nat j) s.(st_gam)) as [a0|] eqn:eg.
    - inversion he; subst. clear he.
      destruct (gk_gam _ _ _ hok _ _ eg) as [t [ht hg]].
      split; [reflexivity|]. split; [apply consv_refl|].
      exists G, t. split; [apply gext_refl|].
      split; [exact hok|]. split; [exact hg|exact (ctx_den_red j t ht)].
    - destruct (nth_error Γ j) as [decl|] eqn:ed; [|discriminate].
      assert (hmain : forall cl t s1,
        ctx_den Γ nctx lvl j = Some t -> g_cell G cl t -> cell_fwd cl = None ->
        gok lo G s1 -> s1.(st_next) = s.(st_next) -> s1.(st_room) = s.(st_room) ->
        (match alloc stress cl rs s1 with
         | COk (a2, rs2, s2) =>
             COk (a2, rs2, set_gam (PTree.set (key_of_succ_nat j) a2 (st_gam s2)) s2)
         | CFail w => CFail w
         end) = COk (a, rs', s') ->
        rs' = rs /\ consv s s'
        /\ exists G' t2, gext G G' /\ gok lo G' s' /\ G' a = Some t2
                         /\ cred (tRel (lvl - nctx + j)) t2).
      { intros cl t s1 hden hcl hfwd hok1 e1n e1r hm.
        destruct (alloc stress cl rs s1) as [[[a1 rs1] s2]|w] eqn:ea; [|discriminate].
        inversion hm; subst. clear hm.
        assert (hroom1 : roomn s1 <> 0) by (unfold roomn; rewrite e1r; exact hroom).
        destruct (alloc_sound lo G cl t rs s1 _ _ _ hok1 hroom1 hcl hfwd ea)
          as (-> & hcons & G' & hext & hok2 & hga).
        destruct (gk_dom _ _ _ hok2 _ _ hga) as [hlo hlt].
        split; [reflexivity|].
        split.
        { unfold consv, nextn, roomn in *. cbn. rewrite e1n, e1r in hcons. exact hcons. }
        exists G', t. split; [exact hext|].
        split; [|split; [exact hga|exact (ctx_den_red j t hden)]].
        split; cbn.
        - exact (state_ok_set_gam lo j _ _ (gk_state _ _ _ hok2) hlo hlt).
        - exact (gk_nofwd _ _ _ hok2).
        - exact (gk_cells _ _ _ hok2).
        - exact (gk_dom _ _ _ hok2).
        - intros j2 a2 hj2.
          destruct (key_eqb (key_of_succ_nat j2) (key_of_succ_nat j)) eqn:ek.
          + apply key_eqb_spec, key_of_succ_nat_inj in ek. subst j2.
            rewrite PTree.gss in hj2. injection hj2 as <-.
            exists t. split; [exact hden|exact hga].
          + rewrite PTree.gso in hj2 by (apply key_neq_of_eqb, ek).
            exact (gk_gam _ _ _ hok2 _ _ hj2).
        - exact (gk_delta _ _ _ hok2). }
      destruct decl.(decl_body) as [b|] eqn:eb.
      + destruct (new_entry X_type X b [] (NSCtx j) s) as [c s1] eqn:e1.
        assert (hct : c.(c_term) = b).
        { change c with (fst (c, s1)). rewrite <- e1. rewrite new_entry_term. reflexivity. }
        assert (hs1 : s1 = snd (new_entry X_type X b [] (NSCtx j) s))
          by (rewrite e1; reflexivity).
        destruct (new_entry_shape b [] (NSCtx j) s) as (q1 & q2 & q3 & _ & q5 & q6).
        apply (hmain (CSusp [] 0 (S j) c) (lift (lvl - nctx + S j) 0 c.(c_term)) s1).
        * unfold ctx_den. rewrite ed, eb, hct. reflexivity.
        * constructor.
          rewrite <- (subst_empty 0 (lift (lvl - nctx + S j) 0 c.(c_term))).
          apply (g_susp_intro G [] 0 (S j) c.(c_term) [] (g_slots_nil G) eq_refl).
          rewrite hct. exact (Γ_simple j decl b ed eb).
        * reflexivity.
        * apply (gok_same lo G s).
          -- exact hok.
          -- rewrite hs1. exact q1.
          -- rewrite hs1. exact q2.
          -- rewrite hs1. exact q5.
          -- apply (delta_inv_memo s);
               [rewrite hs1; exact q6|exact (gk_delta _ _ _ hok)].
        * rewrite hs1. exact q2.
        * rewrite hs1. exact q3.
        * exact he.
      + apply (hmain (CDone (VNeu (NVar (nctx - S j)) [])) (tRel (lvl - S (nctx - S j))) s).
        * unfold ctx_den. rewrite ed, eb. reflexivity.
        * constructor. exact (g_VNeuVar G (nctx - S j) [] [] (Forall2_nil _)).
        * reflexivity.
        * exact hok.
        * reflexivity.
        * reflexivity.
        * exact he.
  Qed.

  (** *** Reading a variable of the environment *)

  Lemma env_var_sound lo G n e rs s x rs' s' tu :
    gok lo G s -> roomn s <> 0 -> g_susp G e (tRel n) tu ->
    env_var X_type X Γ nctx stress n e rs s = COk (x, rs', s') ->
    rs' = rs /\ consv s s'
    /\ exists G' t, gext G G' /\ gok lo G' s' /\ g_slot G' x t /\ cred tu t.
  Proof.
    intros hok hroom hsusp he. unfold env_var in he.
    destruct (g_susp_inv _ _ _ _ hsusp) as [ts (h1 & h2 & h3 & ->)].
    destruct (nth_error e.(ev_vals) n) as [x0|] eqn:en.
    - inversion he; subst. clear he.
      assert (hlt : n < #|e.(ev_vals)|) by (apply nth_error_Some_length in en; exact en).
      destruct (g_slots_nth _ _ _ _ _ h1 en) as [t [hnt hgt]].
      split; [reflexivity|]. split; [apply consv_refl|].
      exists G, t. split; [apply gext_refl|]. split; [exact hok|].
      split; [exact hgt|].
      rewrite h2, (lift_rel_lt (lvl - nctx + e.(ev_goff)) n #|e.(ev_vals)|); [|lia].
      rewrite (subst_rel_eq ts 0 n t n hnt eq_refl), lift0_id. apply cred_refl.
    - destruct (gam X_type X Γ nctx stress (n - e.(ev_nvals) + e.(ev_goff)) rs s)
        as [[[a1 rs1] s1]|w] eqn:eg; [|discriminate].
      inversion he; subst. clear he.
      destruct (gam_sound lo G (n - e.(ev_nvals) + e.(ev_goff)) rs s _ _ _ hok hroom eg)
        as (-> & hcons & G' & t & hext & hok1 & hga & hred).
      assert (hge : #|e.(ev_vals)| <= n) by (apply nth_error_None in en; exact en).
      split; [reflexivity|]. split; [exact hcons|].
      exists G', t. split; [exact hext|]. split; [exact hok1|].
      split; [constructor; exact hga|].
      rewrite h2.
      rewrite (lift_rel_ge (lvl - nctx + e.(ev_goff)) n #|e.(ev_vals)|); [|lia].
      rewrite (subst_rel_gt ts (lvl - nctx + e.(ev_goff) + n) 0);
        [|rewrite (g_slots_length _ _ _ h1); lia].
      rewrite (g_slots_length _ _ _ h1).
      replace (lvl - nctx + e.(ev_goff) + n - #|e.(ev_vals)|)
        with (lvl - nctx + (n - e.(ev_nvals) + e.(ev_goff))) by lia.
      exact hred.
  Qed.

  (** *** The slot of an argument *)

  Lemma arg_slot_sound lo G e c rs s x rs' s' tu :
    gok lo G s -> roomn s <> 0 -> g_susp G e c.(c_term) tu ->
    arg_slot X_type X Γ nctx stress e c rs s = COk (x, rs', s') ->
    rs' = rs /\ consv s s'
    /\ exists G' t, gext G G' /\ gok lo G' s' /\ g_slot G' x t /\ cred tu t.
  Proof.
    intros hok hroom hsusp he. unfold arg_slot in he.
    destruct (g_susp_inv _ _ _ _ hsusp) as [ts (h1 & h2 & h3 & ->)].
    destruct e as [vals nvals goff]. cbn [ev_vals ev_nvals ev_goff] in *.
    destruct (c_term c) eqn:ec;
      [ refine (env_var_sound lo G n (mkEnv vals nvals goff) rs s x rs' s' _ hok hroom
                  _ he);
        exact hsusp | .. ].
    all: inversion he; subst; clear he.
    all: split; [reflexivity|]; split; [apply consv_refl|].
    all: exists G; eexists; split; [apply gext_refl|]; split; [exact hok|];
         split; [|apply cred_refl].
    all: rewrite <- ec; constructor;
      [exact h1|try reflexivity; try assumption|rewrite ec; exact h3].
  Qed.

  (** *** Putting a slot in the heap *)

  Lemma materialize_sound lo G x rs s a rs' s' t :
    gok lo G s -> roomn s <> 0 -> g_slot G x t ->
    materialize X_type X stress x rs s = COk (a, rs', s') ->
    rs' = rs /\ consv s s' /\ exists G', gext G G' /\ gok lo G' s' /\ G' a = Some t.
  Proof.
    intros hok hroom hx he. unfold materialize in he.
    destruct x as [a0|vals n o c].
    - inversion hx; subst. inversion he; subst. clear he.
      split; [reflexivity|]. split; [apply consv_refl|].
      exists G. split; [apply gext_refl|]. split; [exact hok|assumption].
    - inversion hx; subst. clear hx.
      match goal with h1 : g_slots G vals ?ts0 |- _ =>
        assert (hsusp : g_susp G (mkEnv vals #|vals| o) c.(c_term)
                          (subst ts0 0 (lift (lvl - nctx + o) #|vals| c.(c_term))))
          by (constructor; [exact h1|reflexivity|assumption])
      end.
      remember (subst _ 0 (lift (lvl - nctx + o) #|vals| c.(c_term))) as t0 eqn:ht0.
      destruct (c_term c) eqn:ec.
      all: try (match goal with hs : simple_term _ = true |- _ =>
                  cbn in hs; discriminate end).
      all: try (assert (hcl : g_cell G (CSusp vals #|vals| o c) t0)
                  by (constructor; rewrite ec; exact hsusp);
                destruct (alloc_sound lo G _ _ rs s a rs' s' hok hroom hcl eq_refl he)
                  as (-> & hc & G2 & hx1 & hx2 & hx3);
                split; [reflexivity|]; split; [exact hc|];
                exists G2; split; [exact hx1|]; split; [exact hx2|exact hx3]).
      + (* tSort *)
        assert (hcl : g_cell G (CDone (VOpen (mkEnv vals #|vals| o) c)) t0)
          by (constructor; constructor; rewrite ec; exact hsusp).
        destruct (alloc_sound lo G _ _ rs s a rs' s' hok hroom hcl eq_refl he)
          as (-> & hc & G2 & hx1 & hx2 & hx3).
        split; [reflexivity|]; split; [exact hc|].
        exists G2; split; [exact hx1|]; split; [exact hx2|exact hx3].
      + (* tProd *)
        assert (hcl : g_cell G (CDone (VOpen (mkEnv vals #|vals| o) c)) t0)
          by (constructor; constructor; rewrite ec; exact hsusp).
        destruct (alloc_sound lo G _ _ rs s a rs' s' hok hroom hcl eq_refl he)
          as (-> & hc & G2 & hx1 & hx2 & hx3).
        split; [reflexivity|]; split; [exact hc|].
        exists G2; split; [exact hx1|]; split; [exact hx2|exact hx3].
      + (* tLambda *)
        assert (hcl : g_cell G (CDone (VLam (mkEnv vals #|vals| o) c)) t0)
          by (constructor; constructor; rewrite ec; exact hsusp).
        destruct (alloc_sound lo G _ _ rs s a rs' s' hok hroom hcl eq_refl he)
          as (-> & hc & G2 & hx1 & hx2 & hx3).
        split; [reflexivity|]; split; [exact hc|].
        exists G2; split; [exact hx1|]; split; [exact hx2|exact hx3].
      + (* tConst: the memo may add an entry first *)
        match type of he with context [delta X_type X ?kn ?ui s] =>
          destruct (delta X_type X kn ui s) as [[[c'|] s1]|w] eqn:ed
        end.
        * destruct (delta_gok lo G _ _ s _ s1 hok ed) as (hok1 & hc1 & hr1).
          assert (hroom1 : roomn s1 <> 0) by (rewrite hr1; exact hroom).
          assert (hcl : g_cell G (CSusp vals #|vals| o c) t0)
            by (constructor; rewrite ec; exact hsusp).
          destruct (alloc_sound lo G _ _ rs s1 a rs' s' hok1 hroom1 hcl eq_refl he)
            as (-> & hc & G2 & hx1 & hx2 & hx3).
          split; [reflexivity|]; split; [exact (consv_trans _ _ _ hc1 hc)|].
          exists G2; split; [exact hx1|]; split; [exact hx2|exact hx3].
        * destruct (delta_gok lo G _ _ s _ s1 hok ed) as (hok1 & hc1 & hr1).
          assert (hroom1 : roomn s1 <> 0) by (rewrite hr1; exact hroom).
          assert (hcl : g_cell G (CDone (VNeu (NConst (tConst k ui)) [])) t0).
          { constructor. rewrite ht0, subst_lift_const.
            exact (g_VNeuConst G (tConst k ui) [] [] (Forall2_nil _)). }
          destruct (alloc_sound lo G _ _ rs s1 a rs' s' hok1 hroom1 hcl eq_refl he)
            as (-> & hc & G2 & hx1 & hx2 & hx3).
          split; [reflexivity|]; split; [exact (consv_trans _ _ _ hc1 hc)|].
          exists G2; split; [exact hx1|]; split; [exact hx2|exact hx3].
        * assert (hcl : g_cell G (CSusp vals #|vals| o c) t0)
            by (constructor; rewrite ec; exact hsusp).
          destruct (alloc_sound lo G _ _ rs s a rs' s' hok hroom hcl eq_refl he)
            as (-> & hc & G2 & hx1 & hx2 & hx3).
          split; [reflexivity|]; split; [exact hc|].
          exists G2; split; [exact hx1|]; split; [exact hx2|exact hx3].
  Qed.

  (** *** Binding a slot to a binder *)

  Lemma bind_sound lo G x body rs s y rs' s' t :
    gok lo G s -> roomn s <> 0 -> g_slot G x t ->
    bind X_type X stress x body rs s = COk (y, rs', s') ->
    rs' = rs /\ consv s s' /\ exists G', gext G G' /\ gok lo G' s' /\ g_slot G' y t.
  Proof.
    intros hok hroom hx he. unfold bind in he.
    destruct x as [a0|vals n o c].
    - inversion he; subst. clear he.
      split; [reflexivity|]. split; [apply consv_refl|].
      exists G. split; [apply gext_refl|]. split; [exact hok|exact hx].
    - destruct (once_body body s) as [b s1] eqn:eo.
      destruct (once_body_shape body s) as (q1 & q2 & q3 & _ & q5 & q6).
      assert (hs1 : s1 = snd (once_body body s)) by (rewrite eo; reflexivity).
      assert (hok1 : gok lo G s1).
      { apply (gok_same lo G s);
          [exact hok|rewrite hs1; exact q1|rewrite hs1; exact q2|rewrite hs1; exact q5|].
        apply (delta_inv_memo s);
          [rewrite hs1; exact q6|exact (gk_delta _ _ _ hok)]. }
      assert (hc1 : consv s s1)
        by (apply consv_same; rewrite hs1; [exact q2|exact q3]).
      assert (hroom1 : roomn s1 <> 0)
        by (unfold roomn; rewrite hs1, q3; exact hroom).
      clear hs1.
      destruct b.
      + inversion he; subst. clear he.
        split; [reflexivity|]. split; [exact hc1|].
        exists G. split; [apply gext_refl|]. split; [exact hok1|exact hx].
      + destruct (materialize X_type X stress (SInl vals n o c) rs s1)
          as [[[a1 rs1] s2]|w] eqn:em; [|discriminate].
        destruct (materialize_sound lo G (SInl vals n o c) rs s1 a1 rs1 s2 t
                    hok1 hroom1 hx em) as (-> & hc2 & G2 & hx1 & hx2 & hx3).
        inversion he; subst. clear he.
        split; [reflexivity|]. split; [exact (consv_trans _ _ _ hc1 hc2)|].
        exists G2. split; [exact hx1|]. split; [exact hx2|constructor; exact hx3].
  Qed.

  (** *** A whole stack put in the heap *)

  Lemma mat_all_sound : forall d lo G l ts rs s al rs' s',
    gok lo G s -> fits s s' -> g_slots G l ts ->
    mat_all X_type X stress d l rs s = COk (al, rs', s') ->
    rs' = rs /\ consv s s' /\ exists G', gext G G' /\ gok lo G' s' /\ g_addrs G' al ts.
  Proof.
    intros d. induction d as [|k ih]; intros lo G l ts rs s al rs' s' hok hfits hl he;
      destruct l as [|x l]; cbn [mat_all] in he.
    1,3: inversion he; subst; clear he; inversion hl; subst;
         (split; [reflexivity|]); (split; [apply consv_refl|]);
         exists G; (split; [apply gext_refl|]); (split; [exact hok|constructor]).
    - discriminate.
    - inversion hl as [|x' l' tx ts0 hgx hgl hex hets]; subst; clear hl.
      assert (hhs : hstep s s') by
        exact (hstep_mat_all (FS k) (x :: l) rs s al rs' s' (gok_hok _ _ _ hok) he).
      assert (hroom : roomn s <> 0) by exact (fits_room s s' hfits hhs).
      destruct (materialize X_type X stress x (RSk l :: rs) s) as [[[a1 rs1] s1]|w] eqn:em;
        [|discriminate].
      destruct (materialize_sound lo G x (RSk l :: rs) s a1 rs1 s1 tx hok hroom hgx em)
        as (-> & hc1 & G1 & hx1 & hx2 & hx3).
      destruct (mat_all X_type X stress (k tt) l (RA a1 :: rs) s1)
        as [[[al1 rs2] s2]|w] eqn:em2; [|discriminate].
      destruct rs2 as [|r rs2t]; [discriminate he|].
      destruct r as [a0| | | | | |]; try discriminate he.
      injection he as hal hrs' hs'; subst al rs' s'.
      destruct (ih tt lo G1 l ts0 (RA a1 :: rs) s1 al1 (RA a0 :: rs2t) s2
                  hx2 (fits_next s s1 s2 hfits hc1)
                  (g_slots_mono G G1 hx1 _ _ hgl) em2)
        as (hr2 & hc2 & G2 & hy1 & hy2 & hy3).
      inversion hr2; subst. clear hr2.
      split; [reflexivity|]. split; [exact (consv_trans _ _ _ hc1 hc2)|].
      exists G2. split; [exact (gext_trans _ _ _ hx1 hy1)|].
      split; [exact hy2|].
      constructor; [exact (hy1 _ _ hx3)|exact hy3].
  Qed.

  (** *** The write-back

    Forcing a cell marks it [CBusy], evaluates, then writes the value back. Because the
    ghost map [G] is unchanged, the cell at [a] still stands for a reduct of [G a] after each
    write: [CBusy] trivially (it stands for nothing), and [CDone v] because [v] is a reduct
    of the cell's reading which is a reduct of [G a]. *)

  Lemma gok_heap_upd_busy lo G a s s' :
    gok lo G s -> heap_upd a CBusy s = Some s' -> gok lo G s'.
  Proof.
    intros hok he.
    destruct (heap_upd_shape _ _ _ _ he) as (he1 & he2 & he3 & he4 & he5 & hu).
    split.
    - apply (heap_upd_state_ok lo a CBusy s s' (gk_state _ _ _ hok)); [cbn; constructor|exact he].
    - apply (heap_nofwd_heap_upd a CBusy s s' (gk_nofwd _ _ _ hok));
        [intros b; discriminate|exact he].
    - intros b cl hb. unfold heap_get in hb.
      destruct (haddr_dec b a) as [->|hne].
      + rewrite (bh_get_upd_same _ _ _ _ hu) in hb. inversion hb; subst cl.
        assert (ha_in : exists cl0, bh_get a s.(st_heap) = Some cl0).
        { destruct (bh_get a s.(st_heap)) eqn:E; [eexists; reflexivity|].
          exfalso. apply (proj2 (bh_upd_none a CBusy s.(st_heap))) in E.
          rewrite E in hu; discriminate. }
        destruct ha_in as [cl0 h0].
        destruct (gk_cells _ _ _ hok a cl0 h0) as [t [hGa _]].
        exists t. split; [exact hGa|left; reflexivity].
      + rewrite (bh_get_upd_other _ _ _ _ _ hu hne) in hb.
        exact (gk_cells _ _ _ hok b cl hb).
    - intros b t ht. rewrite he1. exact (gk_dom _ _ _ hok b t ht).
    - intros j b hj. rewrite he4 in hj. exact (gk_gam _ _ _ hok j b hj).
    - apply (delta_inv_memo s s'); [rewrite he5; reflexivity|exact (gk_delta _ _ _ hok)].
  Qed.

  Lemma gok_heap_upd_done lo G a v u t s s' :
    gok lo G s -> G a = Some t -> g_value G v u -> cred t u ->
    heap_upd a (CDone v) s = Some s' -> gok lo G s'.
  Proof.
    intros hok hGa hv hred he.
    destruct (heap_upd_shape _ _ _ _ he) as (he1 & he2 & he3 & he4 & he5 & hu).
    split.
    - apply (heap_upd_state_ok lo a (CDone v) s s' (gk_state _ _ _ hok)); [|exact he].
      cbn [ad_cell]. apply (gdom_addrs_in lo G s); [exact (gk_dom _ _ _ hok)|].
      exact (g_value_ad G v u hv).
    - apply (heap_nofwd_heap_upd a (CDone v) s s' (gk_nofwd _ _ _ hok));
        [intros b; discriminate|exact he].
    - intros b cl hb. unfold heap_get in hb.
      destruct (haddr_dec b a) as [->|hne].
      + rewrite (bh_get_upd_same _ _ _ _ hu) in hb. inversion hb; subst cl.
        exists t. split; [exact hGa|].
        right. exists u. split; [constructor; exact hv|exact hred].
      + rewrite (bh_get_upd_other _ _ _ _ _ hu hne) in hb.
        exact (gk_cells _ _ _ hok b cl hb).
    - intros b t0 ht0. rewrite he1. exact (gk_dom _ _ _ hok b t0 ht0).
    - intros j b hj. rewrite he4 in hj. exact (gk_gam _ _ _ hok j b hj).
    - apply (delta_inv_memo s s'); [rewrite he5; reflexivity|exact (gk_delta _ _ _ hok)].
  Qed.

  (** Two shape facts: a [heap_upd] moves neither [st_next] nor [st_room], so it conserves
    the budget and keeps whatever [fits] bound held. *)
  Lemma consv_heap_upd a cl s s' : heap_upd a cl s = Some s' -> consv s s'.
  Proof.
    intros he. destruct (heap_upd_shape _ _ _ _ he) as (he1 & he2 & _).
    apply consv_same; [exact he1|exact he2].
  Qed.

  (** *** Inversions of the ghost value reading, by case on the value shape *)

  Lemma g_value_VCon_inv G h sp t :
    g_value G (VCon h sp) t -> exists ts, t = mkApps h ts /\ g_addrs G sp ts.
  Proof. intros hv; inversion hv; subst; eexists; split; [reflexivity|eassumption]. Qed.

  Lemma g_value_VLam_inv G e c t :
    g_value G (VLam e c) t -> g_susp G e c.(c_term) t.
  Proof. intros hv; inversion hv; subst; assumption. Qed.

  Lemma g_value_VOpen_inv G e c t :
    g_value G (VOpen e c) t -> g_susp G e c.(c_term) t.
  Proof. intros hv; inversion hv; subst; assumption. Qed.

  Lemma g_value_VNeu_inv G nn sp t :
    g_value G (VNeu nn sp) t ->
    (exists l ts, nn = NVar l /\ t = mkApps (tRel (lvl - S l)) ts /\ g_addrs G sp ts)
    \/ (exists h ts, nn = NConst h /\ t = mkApps h ts /\ g_addrs G sp ts).
  Proof.
    intros hv; inversion hv; subst.
    - left. eexists; eexists; split; [reflexivity|split; [reflexivity|eassumption]].
    - right. eexists; eexists; split; [reflexivity|split; [reflexivity|eassumption]].
  Qed.

  Lemma g_value_VStuck_inv G e c sp t :
    g_value G (VStuck e c sp) t ->
    exists h ts, g_susp G e c.(c_term) h /\ g_addrs G sp ts /\ t = mkApps h ts.
  Proof.
    intros hv; inversion hv; subst.
    eexists; eexists; split; [eassumption|split; [eassumption|reflexivity]].
  Qed.

  Lemma g_value_VFix_False G e c i args t : g_value G (VFix e c i args) t -> False.
  Proof. intros hv; inversion hv. Qed.

  Lemma g_value_VStuckFix_False G e c i sp t : g_value G (VStuckFix e c i sp) t -> False.
  Proof. intros hv; inversion hv. Qed.

  Lemma g_slot_addr_inv G a t : g_slot G (SAddr a) t -> G a = Some t.
  Proof. intros h; inversion h; subst; assumption. Qed.

  Lemma g_slot_inl_inv G vs n o c t :
    g_slot G (SInl vs n o c) t -> g_susp G (mkEnv vs n o) c.(c_term) t.
  Proof. intros h; inversion h; subst; econstructor; eauto. Qed.

  Lemma g_cell_susp_inv G vs n o c u :
    g_cell G (CSusp vs n o c) u -> g_susp G (mkEnv vs n o) c.(c_term) u.
  Proof. intros h; inversion h; subst; assumption. Qed.

  Lemma g_cell_done_inv G v u : g_cell G (CDone v) u -> g_value G v u.
  Proof. intros h; inversion h; subst; assumption. Qed.

  (** ** The evaluator against PCUIC reduction

    The input stands (through the ghost map) for a term that reduces, in PCUIC, to the term
    the output value stands for; the state invariant and the budget are re-established. The
    five functions are proved together by induction on the fuel. [whnf_fix] and the iota,
    fix, cofix, projection and primitive branches are ruled out: their code is not a
    [simple_term], so the ghost reading of their input is contradictory. *)

  Lemma machine_sound : forall d,
    (forall lo G a rs s v rs' s' t,
        gok lo G s -> fits s s' -> G a = Some t ->
        force X_type X Γ nctx stress d a rs s = COk (v, rs', s') ->
        rs' = rs /\ consv s s'
        /\ exists G' u, gext G G' /\ gok lo G' s' /\ g_value G' v u /\ cred t u)
    /\ (forall lo G x stk sts tx rs s v rs' s',
        gok lo G s -> fits s s' -> g_slot G x tx -> g_slots G stk sts ->
        eval_slot X_type X Γ nctx stress d x stk rs s = COk (v, rs', s') ->
        rs' = rs /\ consv s s'
        /\ exists G' u, gext G G' /\ gok lo G' s' /\ g_value G' v u
                        /\ cred (mkApps tx sts) u)
    /\ (forall lo G e c stk sts tc rs s v rs' s',
        gok lo G s -> fits s s' -> g_susp G e c.(c_term) tc -> g_slots G stk sts ->
        whnf X_type X Γ nctx stress d e c stk rs s = COk (v, rs', s') ->
        rs' = rs /\ consv s s'
        /\ exists G' u, gext G G' /\ gok lo G' s' /\ g_value G' v u
                        /\ cred (mkApps tc sts) u)
    /\ (forall lo G e c mfix idx stk sts tc rs s v rs' s',
        gok lo G s -> fits s s' -> g_susp G e c.(c_term) tc ->
        c.(c_term) = tFix mfix idx -> g_slots G stk sts ->
        whnf_fix X_type X Γ nctx stress d e c mfix idx stk rs s = COk (v, rs', s') ->
        rs' = rs /\ consv s s'
        /\ exists G' u, gext G G' /\ gok lo G' s' /\ g_value G' v u
                        /\ cred (mkApps tc sts) u)
    /\ (forall lo G v stk sts tv rs s w rs' s',
        gok lo G s -> fits s s' -> g_value G v tv -> g_slots G stk sts ->
        apply X_type X Γ nctx stress d v stk rs s = COk (w, rs', s') ->
        rs' = rs /\ consv s s'
        /\ exists G' u, gext G G' /\ gok lo G' s' /\ g_value G' w u
                        /\ cred (mkApps tv sts) u).
  Proof.
    intros d. induction d as [|k ih].
    - (* FO: every call fails, except [apply] with an empty stack *)
      split; [|split; [|split; [|split]]].
      + intros lo G a rs s v rs' s' t hok hfits hGa he. cbn [force] in he. discriminate he.
      + intros lo G x stk sts tx rs s v rs' s' hok hfits hx hsts he.
        cbn [eval_slot] in he. discriminate he.
      + intros lo G e c stk sts tc rs s v rs' s' hok hfits hsusp hsts he.
        cbn [whnf] in he. discriminate he.
      + intros lo G e c mfix idx stk sts tc rs s v rs' s' hok hfits hsusp hcfix hsts he.
        cbn [whnf_fix] in he. discriminate he.
      + intros lo G v stk sts tv rs s w rs' s' hok hfits hv hsts he.
        cbn [apply] in he. destruct stk as [|y stk].
        * inversion he; subst. inversion hsts; subst.
          split; [reflexivity|]. split; [apply consv_refl|].
          exists G, tv. split; [apply gext_refl|]. split; [exact hok|].
          split; [exact hv|]. apply cred_refl.
        * discriminate he.
    - destruct (ih tt) as (IHf & IHs & IHw & IHx & IHa).
      destruct (machine_hstep (FS k)) as (HFf & HFs & HFw & HFx & HFa).
      destruct (machine_hstep (k tt)) as (HKf & HKs & HKw & HKx & HKa).
      split; [|split; [|split; [|split]]].
      + (* force *)
        intros lo G a0 rs0 s0 v0 rs' s' t0 hok hfits hGa he.
        assert (hhs : hstep s0 s')
          by exact (HFf a0 rs0 s0 v0 rs' s' (gok_hok _ _ _ hok) he).
        assert (hroom0 : roomn s0 <> 0) by exact (fits_room s0 s' hfits hhs).
        cbv beta iota zeta delta [force] in he.
        destruct (heap_get a0 s0) as [cl|] eqn:ehc; [|discriminate he].
        destruct (gk_cells _ _ _ hok a0 cl ehc) as [t1 [hGa1 hcell]].
        assert (t1 = t0) by (rewrite hGa in hGa1; injection hGa1 as ->; reflexivity).
        subst t1.
        destruct cl as [vs n o c| vd | | b].
        * (* CSusp: force, then write back *)
          destruct hcell as [hbusy|[u [hgc hcred]]]; [discriminate hbusy|].
          pose proof (g_cell_susp_inv _ _ _ _ _ _ hgc) as hsusp.
          destruct (heap_upd a0 CBusy s0) as [sb|] eqn:ebusy; [|discriminate he].
          lazymatch type of he with
          | context [match ?x with COk _ => _ | CFail _ => _ end] =>
            destruct x as [[[vw rsw] sw]|w] eqn:ew
          end; [|discriminate he].
          destruct rsw as [|r1 rsw']; [discriminate he|].
          destruct r1 as [ar| | | | | |]; try discriminate he.
          destruct (heap_upd ar (CDone vw) sw) as [sd|] eqn:edone; [|discriminate he].
          injection he as hiv hirs his; subst v0 rs' s'.
          assert (hokb : gok lo G sb) by exact (gok_heap_upd_busy lo G a0 s0 sb hok ebusy).
          assert (hcons_b : consv s0 sb) by exact (consv_heap_upd a0 CBusy s0 sb ebusy).
          assert (hfits_b : fits sb sd) by exact (fits_next s0 sb sd hfits hcons_b).
          assert (hstep_sbsw : hstep sb sw)
            by exact (HKw (mkEnv vs n o) c [] (RA a0 :: rs0) sb vw (RA ar :: rsw') sw
                        (gok_hok _ _ _ hokb) ew).
          assert (hstep_swsd : hstep sw sd)
            by exact (hstep_heap_upd ar (CDone vw) sw sd eq_refl (proj2 hstep_sbsw) edone).
          assert (hfits_w : fits sb sw) by exact (fits_first sb sw sd hfits_b hstep_swsd).
          destruct (IHw lo G (mkEnv vs n o) c [] [] u (RA a0 :: rs0) sb vw
                      (RA ar :: rsw') sw hokb hfits_w hsusp (g_slots_nil G) ew)
            as (hreq & hcons_w & G' & uw & hext & hokw & hvw & hcredw).
          inversion hreq; subst ar rsw'.
          assert (hG'a : G' a0 = Some t0) by exact (hext a0 t0 hGa).
          assert (hcred_t_uw : cred t0 uw)
            by exact (cred_trans t0 u uw hcred hcredw).
          assert (hokd : gok lo G' sd)
            by exact (gok_heap_upd_done lo G' a0 vw uw t0 sw sd hokw hG'a hvw hcred_t_uw edone).
          split; [reflexivity|].
          split.
          { apply (consv_trans s0 sb sd hcons_b).
            apply (consv_trans sb sw sd hcons_w).
            exact (consv_heap_upd a0 (CDone vw) sw sd edone). }
          exists G', uw. split; [exact hext|]. split; [exact hokd|].
          split; [exact hvw|exact hcred_t_uw].
        * (* CDone vd: the value is already there *)
          destruct hcell as [hbusy|[u [hgc hcred]]]; [discriminate hbusy|].
          pose proof (g_cell_done_inv _ _ _ hgc) as hvd.
          inversion he; subst. clear he.
          split; [reflexivity|]. split; [apply consv_refl|].
          exists G, u. split; [apply gext_refl|]. split; [exact hok|].
          split; [exact hvd|exact hcred].
        * discriminate he.
        * discriminate he.
      + (* eval_slot *)
        intros lo G x stk sts tx rs0 s0 v0 rs' s' hok hfits hslot hsts he.
        assert (hhs : hstep s0 s')
          by exact (HFs x stk rs0 s0 v0 rs' s' (gok_hok _ _ _ hok) he).
        assert (hroom0 : roomn s0 <> 0) by exact (fits_room s0 s' hfits hhs).
        cbv beta iota zeta delta [eval_slot] in he.
        destruct x as [a|vs n o c].
        * (* SAddr a: force then apply *)
          pose proof (g_slot_addr_inv _ _ _ hslot) as hGa.
          lazymatch type of he with
          | context [match ?x with COk _ => _ | CFail _ => _ end] =>
            destruct x as [[[vf rsf] sf]|w] eqn:ef
          end; [|discriminate he].
          destruct rsf as [|r1 rsf']; [discriminate he|].
          destruct r1 as [| | | |lk| |]; try discriminate he.
          assert (hstep_s0sf : hstep s0 sf)
            by exact (HKf a (RSk stk :: rs0) s0 vf (RSk lk :: rsf') sf (gok_hok _ _ _ hok) ef).
          assert (hstep_sfs' : hstep sf s')
            by exact (HKa vf lk rsf' sf v0 rs' s' (proj2 hstep_s0sf) he).
          assert (hfits_f : fits s0 sf) by exact (fits_first s0 sf s' hfits hstep_sfs').
          destruct (IHf lo G a (RSk stk :: rs0) s0 vf (RSk lk :: rsf') sf tx
                      hok hfits_f hGa ef)
            as (hreqf & hconsf & Gf & uf & hextf & hokf & hvf & hcredf).
          inversion hreqf; subst lk rsf'.
          assert (hfits_a : fits sf s') by exact (fits_next s0 sf s' hfits hconsf).
          destruct (IHa lo Gf vf stk sts uf rs0 sf v0 rs' s' hokf hfits_a hvf
                      (g_slots_mono G Gf hextf stk sts hsts) he)
            as (hreqa & hconsa & G' & u' & hexta & hoka & hv' & hcreda).
          split; [exact hreqa|].
          split; [exact (consv_trans s0 sf s' hconsf hconsa)|].
          exists G', u'. split; [exact (gext_trans G Gf G' hextf hexta)|].
          split; [exact hoka|]. split; [exact hv'|].
          apply (cred_trans (mkApps tx sts) (mkApps uf sts) u').
          -- exact (cred_mkApps tx uf sts hcredf).
          -- exact hcreda.
        * (* SInl: whnf in place *)
          pose proof (g_slot_inl_inv _ _ _ _ _ _ hslot) as hsusp.
          destruct (IHw lo G (mkEnv vs n o) c stk sts tx rs0 s0 v0 rs' s'
                      hok hfits hsusp hsts he)
            as (hreq & hcons & G' & u' & hext & hokw & hv' & hcred).
          split; [exact hreq|]. split; [exact hcons|].
          exists G', u'. split; [exact hext|]. split; [exact hokw|].
          split; [exact hv'|exact hcred].
      + (* whnf *)
        intros lo G e c stk sts tc rs0 s0 v0 rs' s' hok hfits hsusp hsts he.
        assert (hhs : hstep s0 s')
          by exact (HFw e c stk rs0 s0 v0 rs' s' (gok_hok _ _ _ hok) he).
        assert (hroom0 : roomn s0 <> 0) by exact (fits_room s0 s' hfits hhs).
        cbv beta iota zeta delta [whnf] in he.
        destruct (tick s0) as [st|] eqn:etick; [|discriminate he].
        destruct (tick_shape _ _ etick) as (th & tn & tr & tg & tm).
        assert (hokt : gok lo G st)
          by (apply (gok_same lo G s0 st hok th tn tg);
              apply (delta_inv_memo s0 st); [rewrite tm; reflexivity|exact (gk_delta _ _ _ hok)]).
        assert (hcons_st : consv s0 st) by (apply consv_same; [exact tn|exact tr]).
        assert (hfits_st : fits st s') by exact (fits_next s0 st s' hfits hcons_st).
        assert (hroomt : roomn st <> 0) by (unfold roomn; rewrite tr; exact hroom0).
        pose proof (g_susp_inv _ _ _ _ hsusp) as (tsG & hslotsG & hnvalsG & hsimpleG & htcG).
        clear tsG hslotsG hnvalsG htcG.
        remember (c_term c) as ct eqn:ec;
        destruct ct as [n|vr|ev earg|srt|na A B|na A b|na b T body|f arg|k0 ui
                       |ind ui|ind n ui|ci p scrut brs|pr arg|mfix idx|cmfix cidx|prm];
          try (solve [discriminate he]);
          try (solve [cbn in hsimpleG; discriminate hsimpleG]).
        * (* tRel n *)
          destruct (env_var X_type X Γ nctx stress n e (RSk stk :: rs0) st)
            as [[[xr rsr] sr]|w] eqn:ev; [|discriminate he].
          destruct rsr as [|r1 rsr']; [discriminate he|].
          destruct r1 as [| | | |lk| |]; try discriminate he.
          destruct (env_var_sound lo G n e (RSk stk :: rs0) st xr (RSk lk :: rsr') sr tc
                      hokt hroomt hsusp ev)
            as (hreqv & hconsv & Gv & tv1 & hextv & hokv & hslotv & hcredv).
          inversion hreqv; subst lk rsr'.
          assert (hfits_sr : fits sr s') by exact (fits_next st sr s' hfits_st hconsv).
          destruct (IHs lo Gv xr stk sts tv1 rs0 sr v0 rs' s' hokv hfits_sr hslotv
                      (g_slots_mono G Gv hextv stk sts hsts) he)
            as (hreqs & hconss & G' & u' & hext' & hok' & hv' & hcred').
          split; [exact hreqs|].
          split; [exact (consv_trans s0 st s' hcons_st (consv_trans st sr s' hconsv hconss))|].
          exists G', u'. split; [exact (gext_trans G Gv G' hextv hext')|].
          split; [exact hok'|]. split; [exact hv'|].
          apply (cred_trans (mkApps tc sts) (mkApps tv1 sts) u').
          -- exact (cred_mkApps tc tv1 sts hcredv).
          -- exact hcred'.
        * (* tSort *)
          destruct stk as [|xh stk'].
          -- inversion he; subst; clear he. inversion hsts; subst.
             split; [reflexivity|]. split; [exact hcons_st|].
             exists G, tc. split; [apply gext_refl|]. split; [exact hokt|].
             split; [apply (g_VOpen G e c tc); rewrite <- ec; exact hsusp|]. apply cred_refl.
          -- discriminate he.
        * (* tProd *)
          destruct stk as [|xh stk'].
          -- inversion he; subst; clear he. inversion hsts; subst.
             split; [reflexivity|]. split; [exact hcons_st|].
             exists G, tc. split; [apply gext_refl|]. split; [exact hokt|].
             split; [apply (g_VOpen G e c tc); rewrite <- ec; exact hsusp|]. apply cred_refl.
          -- discriminate he.
        * (* tLambda na A b *)
          destruct stk as [|xh stk'].
          -- (* VLam *)
             inversion he; subst; clear he. inversion hsts; subst.
             split; [reflexivity|]. split; [exact hcons_st|].
             exists G, tc. split; [apply gext_refl|]. split; [exact hokt|].
             split; [apply (g_VLam G e c tc); rewrite <- ec; exact hsusp|]. apply cred_refl.
          -- (* beta *)
             inversion hsts as [|x0 l0 txh sts' hsloth hslots']; subst.
             destruct (bind X_type X stress xh (child c 1 b) (RE e :: RSk stk' :: rs0) st)
               as [[[xb rsb] sb]|w] eqn:eb; [|discriminate he].
             destruct rsb as [|r1 rsb1]; [discriminate he|].
             destruct r1 as [| |ee| | | |]; try discriminate he.
             destruct rsb1 as [|r2 rsb2]; [discriminate he|].
             destruct r2 as [| | | |lk| |]; try discriminate he.
             destruct (bind_sound lo G xh (child c 1 b) (RE e :: RSk stk' :: rs0) st xb
                         (RE ee :: RSk lk :: rsb2) sb txh hokt hroomt hsloth eb)
               as (hreqb & hconsb & Gv & hextb & hokb & hslotb).
             inversion hreqb; subst ee lk rsb2.
             destruct (g_susp_lam Gv e na A b tc
                         (g_susp_mono G Gv hextb e (tLambda na A b) tc hsusp))
               as (A' & B & htc & hlamprop).
             assert (hfits_sb : fits sb s') by exact (fits_next st sb s' hfits_st hconsb).
             destruct (IHw lo Gv (env_push xb e) (child c 1 b) stk' sts' (subst [txh] 0 B)
                         rs0 sb v0 rs' s' hokb hfits_sb (hlamprop xb txh hslotb)
                         (g_slots_mono G Gv hextb stk' sts' hslots') he)
               as (hreqw & hconsw & G' & u' & hext' & hok' & hv' & hcred').
             split; [exact hreqw|].
             split; [exact (consv_trans s0 st s' hcons_st (consv_trans st sb s' hconsb hconsw))|].
             exists G', u'. split; [exact (gext_trans G Gv G' hextb hext')|].
             split; [exact hok'|]. split; [exact hv'|].
             subst tc.
             apply (cred_trans (mkApps (tApp (tLambda na A' B) txh) sts')
                       (mkApps (subst [txh] 0 B) sts') u').
             ++ apply cred_mkApps. apply cred_one. apply red_beta.
             ++ exact hcred'.
        * (* tLetIn na b T body (zeta) *)
          destruct (g_susp_letin _ _ _ _ _ _ _ hsusp) as (d' & T' & B & htc & hsb & hletprop).
          destruct (arg_slot X_type X Γ nctx stress e (child c 0 b) (RE e :: RSk stk :: rs0) st)
            as [[[xa rsa] sa]|w] eqn:ea; [|discriminate he].
          destruct rsa as [|r1 rsa1]; [discriminate he|].
          destruct r1 as [| |ee| | | |]; try discriminate he.
          destruct rsa1 as [|r2 rsa2]; [discriminate he|].
          destruct r2 as [| | | |lk| |]; try discriminate he.
          destruct (arg_slot_sound lo G e (child c 0 b) (RE e :: RSk stk :: rs0) st xa
                      (RE ee :: RSk lk :: rsa2) sa d' hokt hroomt hsb ea)
            as (hreqa & hconsa & Ga & tb & hexta & hoka & hslota & hcreda).
          inversion hreqa; subst ee lk rsa2.
          destruct (bind X_type X stress xa (child c 2 body) (RE e :: RSk stk :: rs0) sa)
            as [[[xbnd rsb] sb]|w] eqn:eb; [|discriminate he].
          destruct rsb as [|r1 rsb1]; [discriminate he|].
          destruct r1 as [| |ee| | | |]; try discriminate he.
          destruct rsb1 as [|r2 rsb2]; [discriminate he|].
          destruct r2 as [| | | |lk| |]; try discriminate he.
          assert (hstep_sasb : hstep sa sb)
            by exact (hstep_bind xa (child c 2 body) (RE e :: RSk stk :: rs0) sa
                        xbnd (RE ee :: RSk lk :: rsb2) sb (gok_hok _ _ _ hoka) eb).
          assert (hstep_sbs' : hstep sb s')
            by exact (HKw (env_push xbnd ee) (child c 2 body) lk rsb2 sb v0 rs' s'
                        (proj2 hstep_sasb) he).
          assert (hstep_sas' : hstep sa s') by exact (hstep_trans sa sb s' hstep_sasb hstep_sbs').
          assert (hfits_sa : fits sa s') by exact (fits_next st sa s' hfits_st hconsa).
          assert (hrooma : roomn sa <> 0) by exact (fits_room sa s' hfits_sa hstep_sas').
          destruct (bind_sound lo Ga xa (child c 2 body) (RE e :: RSk stk :: rs0) sa xbnd
                      (RE ee :: RSk lk :: rsb2) sb tb hoka hrooma hslota eb)
            as (hreqb & hconsb & Gb & hextb & hokb & hslotb).
          inversion hreqb; subst ee lk rsb2.
          destruct (g_susp_letin Gb e na b T body tc
                      (g_susp_mono G Gb (gext_trans G Ga Gb hexta hextb) e
                         (tLetIn na b T body) tc hsusp))
            as (d'2 & T'2 & B2 & htc2 & hsb2 & hletprop2).
          assert (heqlet : tLetIn na d' T' B = tLetIn na d'2 T'2 B2)
            by (rewrite <- htc; exact htc2).
          inversion heqlet; subst d'2 T'2 B2.
          assert (hfits_sb : fits sb s') by exact (fits_next sa sb s' hfits_sa hconsb).
          destruct (IHw lo Gb (env_push xbnd e) (child c 2 body) stk sts (subst [tb] 0 B)
                      rs0 sb v0 rs' s' hokb hfits_sb (hletprop2 xbnd tb hslotb)
                      (g_slots_mono G Gb (gext_trans G Ga Gb hexta hextb) stk sts hsts) he)
            as (hreqw & hconsw & G' & u' & hext' & hok' & hv' & hcred').
          split; [exact hreqw|].
          split.
          { apply (consv_trans s0 st s' hcons_st).
            apply (consv_trans st sa s' hconsa).
            exact (consv_trans sa sb s' hconsb hconsw). }
          exists G', u'.
          split; [exact (gext_trans G Ga G' hexta (gext_trans Ga Gb G' hextb hext'))|].
          split; [exact hok'|]. split; [exact hv'|].
          subst tc.
          apply (cred_trans (mkApps (tLetIn na d' T' B) sts) (mkApps (subst [tb] 0 B) sts) u').
          -- apply cred_mkApps.
             apply (cred_trans (tLetIn na d' T' B) (tLetIn na tb T' B) (subst [tb] 0 B)).
             ++ exact (cred_letin na d' tb T' B hcreda).
             ++ apply cred_one. apply red_zeta.
          -- exact hcred'.
        * (* tApp f arg *)
          destruct (g_susp_app _ _ _ _ _ hsusp) as (uf & ua & htc & hsf & hsa).
          destruct (arg_slot X_type X Γ nctx stress e (child c 1 arg) (RE e :: RSk stk :: rs0) st)
            as [[[xr rsr] sr]|w] eqn:ea; [|discriminate he].
          destruct rsr as [|r1 rsr1]; [discriminate he|].
          destruct r1 as [| |ee| | | |]; try discriminate he.
          destruct rsr1 as [|r2 rsr2]; [discriminate he|].
          destruct r2 as [| | | |lk| |]; try discriminate he.
          destruct (arg_slot_sound lo G e (child c 1 arg) (RE e :: RSk stk :: rs0) st xr
                      (RE ee :: RSk lk :: rsr2) sr ua hokt hroomt hsa ea)
            as (hreqa & hconsa & Gv & ta & hexta & hoka & hslota & hcreda).
          inversion hreqa; subst ee lk rsr2.
          assert (hfits_sr : fits sr s') by exact (fits_next st sr s' hfits_st hconsa).
          destruct (IHw lo Gv e (child c 0 f) (xr :: stk) (ta :: sts) uf rs0 sr v0 rs' s'
                      hoka hfits_sr (g_susp_mono G Gv hexta e f uf hsf)
                      (g_slots_cons Gv xr stk ta sts hslota (g_slots_mono G Gv hexta stk sts hsts))
                      he)
            as (hreqw & hconsw & G' & u' & hext' & hok' & hv' & hcred').
          split; [exact hreqw|].
          split; [exact (consv_trans s0 st s' hcons_st (consv_trans st sr s' hconsa hconsw))|].
          exists G', u'. split; [exact (gext_trans G Gv G' hexta hext')|].
          split; [exact hok'|]. split; [exact hv'|].
          subst tc.
          apply (cred_trans (mkApps (tApp uf ua) sts) (mkApps (tApp uf ta) sts) u').
          -- exact (cred_mkApps (tApp uf ua) (tApp uf ta) sts (cred_app_r uf ua ta hcreda)).
          -- exact hcred'.
        * (* tConst kn ui (delta) *)
          pose proof (g_susp_const _ _ _ _ _ hsusp) as htc.
          destruct (delta X_type X k0 ui st) as [[[c'| ] sd]|w] eqn:ed; [| |discriminate he].
          -- (* Some c' *)
             destruct (delta_sound k0 ui st c' sd (gk_delta _ _ _ hokt) ed) as (hsimpc & hcredc).
             destruct (delta_gok lo G k0 ui st (Some c') sd hokt ed) as (hokd & hconsd & hroomd).
             assert (hsuspc : g_susp G env_empty c'.(c_term) (lift0 (lvl - nctx) c'.(c_term))).
             { unfold env_empty.
               replace (lift0 (lvl - nctx) c'.(c_term))
                 with (subst [] 0 (lift (lvl - nctx + 0) 0 c'.(c_term)))
                 by (rewrite subst_empty, Nat.add_0_r; reflexivity).
               exact (g_susp_intro G [] 0 0 c'.(c_term) [] (g_slots_nil G) eq_refl hsimpc). }
             assert (hfits_sd : fits sd s') by exact (fits_next st sd s' hfits_st hconsd).
             destruct (IHw lo G env_empty c' stk sts (lift0 (lvl - nctx) c'.(c_term))
                         rs0 sd v0 rs' s' hokd hfits_sd hsuspc hsts he)
               as (hreqw & hconsw & G' & u' & hext' & hok' & hv' & hcred').
             split; [exact hreqw|].
             split; [exact (consv_trans s0 st s' hcons_st (consv_trans st sd s' hconsd hconsw))|].
             exists G', u'. split; [exact hext'|]. split; [exact hok'|]. split; [exact hv'|].
             rewrite htc.
             apply (cred_trans (mkApps (tConst k0 ui) sts)
                       (mkApps (lift0 (lvl - nctx) c'.(c_term)) sts) u').
             ++ exact (cred_mkApps (tConst k0 ui) (lift0 (lvl - nctx) c'.(c_term)) sts hcredc).
             ++ exact hcred'.
          -- (* None: a neutral constant *)
             destruct (delta_gok lo G k0 ui st None sd hokt ed) as (hokd & hconsd & hroomd).
             destruct (mat_all X_type X stress (k tt) stk rs0 sd) as [[[sp rsm] sm]|w] eqn:em;
               [|discriminate he].
             injection he as hv0 hrs hsm; subst v0 rs' s'.
             assert (hfits_sd : fits sd sm) by
               exact (fits_next st sd sm (fits_next s0 st sm hfits hcons_st) hconsd).
             destruct (mat_all_sound (k tt) lo G stk sts rs0 sd sp rsm sm
                         hokd hfits_sd hsts em)
               as (hreqm & hconsm & G' & hextm & hokm & haddrm).
             split; [exact hreqm|].
             split; [exact (consv_trans s0 st sm hcons_st (consv_trans st sd sm hconsd hconsm))|].
             exists G', (mkApps (tConst k0 ui) sts).
             split; [exact hextm|]. split; [exact hokm|].
             split; [exact (g_VNeuConst G' (tConst k0 ui) sp sts haddrm)|].
             rewrite htc. apply cred_refl.
        * (* tInd i ui *)
          pose proof (g_susp_tind _ _ _ _ _ hsusp) as htc.
          destruct (mat_all X_type X stress (k tt) stk rs0 st) as [[[sp rsm] sm]|w] eqn:em;
            [|discriminate he].
          injection he as hv0 hrs hsm; subst v0 rs' s'.
          assert (hfits_sm : fits st sm) by exact (fits_next s0 st sm hfits hcons_st).
          destruct (mat_all_sound (k tt) lo G stk sts rs0 st sp rsm sm hokt hfits_sm hsts em)
            as (hreqm & hconsm & G' & hextm & hokm & haddrm).
          split; [exact hreqm|]. split; [exact (consv_trans s0 st sm hcons_st hconsm)|].
          exists G', (mkApps (tInd ind ui) sts). split; [exact hextm|]. split; [exact hokm|].
          split; [exact (g_VCon G' (tInd ind ui) sp sts haddrm)|].
          rewrite htc. apply cred_refl.
        * (* tConstruct ind n ui *)
          pose proof (g_susp_construct _ _ _ _ _ _ hsusp) as htc.
          destruct (mat_all X_type X stress (k tt) stk rs0 st) as [[[sp rsm] sm]|w] eqn:em;
            [|discriminate he].
          injection he as hv0 hrs hsm; subst v0 rs' s'.
          assert (hfits_sm : fits st sm) by exact (fits_next s0 st sm hfits hcons_st).
          destruct (mat_all_sound (k tt) lo G stk sts rs0 st sp rsm sm hokt hfits_sm hsts em)
            as (hreqm & hconsm & G' & hextm & hokm & haddrm).
          split; [exact hreqm|]. split; [exact (consv_trans s0 st sm hcons_st hconsm)|].
          exists G', (mkApps (tConstruct ind n ui) sts). split; [exact hextm|]. split; [exact hokm|].
          split; [exact (g_VCon G' (tConstruct ind n ui) sp sts haddrm)|].
          rewrite htc. apply cred_refl.
      + (* whnf_fix: ruled out, its code is not a simple term *)
        intros lo G e c mfix idx stk sts tc rs0 s0 v0 rs' s' hok hfits hsusp hcfix hsts he.
        destruct (g_susp_inv _ _ _ _ hsusp) as (ts0 & _ & _ & hsimp & _).
        rewrite hcfix in hsimp. cbn in hsimp. discriminate hsimp.
      + (* apply *)
        intros lo G vv stk sts tv rs0 s0 ww rs' s' hok hfits hv hsts he.
        assert (hhs : hstep s0 s')
          by exact (HFa vv stk rs0 s0 ww rs' s' (gok_hok _ _ _ hok) he).
        assert (hroom0 : roomn s0 <> 0) by exact (fits_room s0 s' hfits hhs).
        cbv beta iota zeta delta [apply] in he.
        destruct stk as [|xh stk'].
        * (* empty stack: the value itself *)
          inversion he; subst; clear he. inversion hsts; subst.
          split; [reflexivity|]. split; [apply consv_refl|].
          exists G, tv. split; [apply gext_refl|]. split; [exact hok|].
          split; [exact hv|]. apply cred_refl.
        * destruct vv as [h sp|e c|e c i args|e c i sp|nn sp|e c|e c sp].
          -- (* VCon *)
             destruct (g_value_VCon_inv _ _ _ _ hv) as (ts & htv & hadd).
             destruct (mat_all X_type X stress (k tt) (xh :: stk') (RV (VCon h sp) :: rs0) s0)
               as [[[sp2 rsm] sm]|w] eqn:em; [|discriminate he].
             destruct rsm as [|r1 rsm1]; [discriminate he|].
             destruct r1 as [| | |vc| | |]; try discriminate he.
             destruct (add_spine vc sp2) as [vres|] eqn:eadd; [|discriminate he].
             injection he as hww hrsm hsm; subst ww rs' s'.
             destruct (mat_all_sound (k tt) lo G (xh :: stk') sts (RV (VCon h sp) :: rs0) s0 sp2
                         (RV vc :: rsm1) sm hok hfits hsts em)
               as (hreqm & hconsm & G' & hextm & hokm & haddrm).
             inversion hreqm; subst vc rsm1.
             cbn in eadd. inversion eadd; subst vres.
             split; [reflexivity|]. split; [exact hconsm|].
             exists G', (mkApps h (ts ++ sts)).
             split; [exact hextm|]. split; [exact hokm|].
             split.
             ++ apply g_VCon. apply Forall2_app;
                  [exact (g_addrs_mono G G' hextm sp ts hadd)|exact haddrm].
             ++ subst tv. rewrite mkApps_app. apply cred_refl.
          -- (* VLam: beta *)
             pose proof (g_value_VLam_inv _ _ _ _ hv) as hsusp.
             remember (c_term c) as ct eqn:ec;
             destruct ct as [n|vr|ev earg|srt|na A B|na A b|na bd T bo|f arg|k0 ui
                            |ind ui|ind n ui|ci p scrut brs|pr arg|mfix idx|cmfix cidx|prm];
               try discriminate he.
             inversion hsts as [|x0 l0 txh sts' hsloth hslots']; subst.
             destruct (bind X_type X stress xh (child c 1 b) (RE e :: RSk stk' :: rs0) s0)
               as [[[xb rsb] sb]|w] eqn:eb; [|discriminate he].
             destruct rsb as [|r1 rsb1]; [discriminate he|].
             destruct r1 as [| |ee| | | |]; try discriminate he.
             destruct rsb1 as [|r2 rsb2]; [discriminate he|].
             destruct r2 as [| | | |lk| |]; try discriminate he.
             destruct (bind_sound lo G xh (child c 1 b) (RE e :: RSk stk' :: rs0) s0 xb
                         (RE ee :: RSk lk :: rsb2) sb txh hok hroom0 hsloth eb)
               as (hreqb & hconsb & Gv & hextb & hokb & hslotb).
             inversion hreqb; subst ee lk rsb2.
             destruct (g_susp_lam Gv e na A b tv
                         (g_susp_mono G Gv hextb e (tLambda na A b) tv hsusp))
               as (A' & B & htv & hlamprop).
             assert (hfits_sb : fits sb s') by exact (fits_next s0 sb s' hfits hconsb).
             destruct (IHw lo Gv (env_push xb e) (child c 1 b) stk' sts' (subst [txh] 0 B)
                         rs0 sb ww rs' s' hokb hfits_sb (hlamprop xb txh hslotb)
                         (g_slots_mono G Gv hextb stk' sts' hslots') he)
               as (hreqw & hconsw & G' & u' & hext' & hok' & hv' & hcred').
             split; [exact hreqw|]. split; [exact (consv_trans s0 sb s' hconsb hconsw)|].
             exists G', u'. split; [exact (gext_trans G Gv G' hextb hext')|].
             split; [exact hok'|]. split; [exact hv'|].
             subst tv.
             apply (cred_trans (mkApps (tApp (tLambda na A' B) txh) sts')
                       (mkApps (subst [txh] 0 B) sts') u').
             ++ apply cred_mkApps. apply cred_one. apply red_beta.
             ++ exact hcred'.
          -- (* VFix: impossible *)
             destruct (g_value_VFix_False _ _ _ _ _ _ hv).
          -- (* VStuckFix: impossible *)
             destruct (g_value_VStuckFix_False _ _ _ _ _ _ hv).
          -- (* VNeu *)
             destruct (mat_all X_type X stress (k tt) (xh :: stk') (RV (VNeu nn sp) :: rs0) s0)
               as [[[sp2 rsm] sm]|w] eqn:em; [|discriminate he].
             destruct rsm as [|r1 rsm1]; [discriminate he|].
             destruct r1 as [| | |vc| | |]; try discriminate he.
             destruct (add_spine vc sp2) as [vres|] eqn:eadd; [|discriminate he].
             injection he as hww hrsm hsm; subst ww rs' s'.
             destruct (mat_all_sound (k tt) lo G (xh :: stk') sts (RV (VNeu nn sp) :: rs0) s0 sp2
                         (RV vc :: rsm1) sm hok hfits hsts em)
               as (hreqm & hconsm & G' & hextm & hokm & haddrm).
             inversion hreqm; subst vc rsm1.
             cbn in eadd. inversion eadd; subst vres.
             destruct (g_value_VNeu_inv _ _ _ _ hv) as [(l & ts & hnn & htv & hadd)|(hh & ts & hnn & htv & hadd)].
             ++ subst nn tv.
                split; [reflexivity|]. split; [exact hconsm|].
                exists G', (mkApps (tRel (lvl - S l)) (ts ++ sts)).
                split; [exact hextm|]. split; [exact hokm|].
                split.
                ** exact (g_VNeuVar G' l (sp ++ sp2) (ts ++ sts)
                            (Forall2_app (g_addrs_mono G G' hextm sp ts hadd) haddrm)).
                ** rewrite mkApps_app. apply cred_refl.
             ++ subst nn tv.
                split; [reflexivity|]. split; [exact hconsm|].
                exists G', (mkApps hh (ts ++ sts)).
                split; [exact hextm|]. split; [exact hokm|].
                split.
                ** exact (g_VNeuConst G' hh (sp ++ sp2) (ts ++ sts)
                            (Forall2_app (g_addrs_mono G G' hextm sp ts hadd) haddrm)).
                ** rewrite mkApps_app. apply cred_refl.
          -- (* VOpen: cannot be applied *)
             discriminate he.
          -- (* VStuck *)
             destruct (mat_all X_type X stress (k tt) (xh :: stk') (RV (VStuck e c sp) :: rs0) s0)
               as [[[sp2 rsm] sm]|w] eqn:em; [|discriminate he].
             destruct rsm as [|r1 rsm1]; [discriminate he|].
             destruct r1 as [| | |vc| | |]; try discriminate he.
             destruct (add_spine vc sp2) as [vres|] eqn:eadd; [|discriminate he].
             injection he as hww hrsm hsm; subst ww rs' s'.
             destruct (mat_all_sound (k tt) lo G (xh :: stk') sts (RV (VStuck e c sp) :: rs0) s0 sp2
                         (RV vc :: rsm1) sm hok hfits hsts em)
               as (hreqm & hconsm & G' & hextm & hokm & haddrm).
             inversion hreqm; subst vc rsm1.
             cbn in eadd. inversion eadd; subst vres.
             destruct (g_value_VStuck_inv _ _ _ _ _ hv) as (hh & ts & hsuspc & hadd & htv).
             subst tv.
             split; [reflexivity|]. split; [exact hconsm|].
             exists G', (mkApps hh (ts ++ sts)).
             split; [exact hextm|]. split; [exact hokm|].
             split.
             ++ exact (g_VStuck G' e c (sp ++ sp2) hh (ts ++ sts)
                         (g_susp_mono G G' hextm e c.(c_term) hh hsuspc)
                         (Forall2_app (g_addrs_mono G G' hextm sp ts hadd) haddrm)).
             ++ rewrite mkApps_app. apply cred_refl.
  Qed.

End Eval.
