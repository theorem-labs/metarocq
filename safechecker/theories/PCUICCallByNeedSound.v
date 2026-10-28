(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require CanonicalTries.
From MetaRocq.Common Require Import config Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils.
From MetaRocq.SafeChecker Require Import PCUICCallByNeed.

Import CanonicalTries.

(** * Soundness of the call-by-need fast path (BET-298, step 2)

  The machine of [PCUICCallByNeed] answers [CbnYes] only when it has compared two values that
  read back to convertible terms. This file holds the relation that says what a machine
  structure stands for: [repr_value H lvl v t] reads "in heap [H], with [lvl] levels in scope,
  the value [v] stands for the term [t]". It is the relational form of the machine's own
  read-back functions [rb_slot], [rb_susp], [rb_value], which are partial (they can run out of
  fuel or steps) and so cannot carry a proof by themselves.

  Three facts about the relation are proved here, and nothing else is assumed:
  - it is a partial function: a structure stands for at most one term ([repr_det_*]);
  - it survives a heap that only grows ([repr_mono_*]), which is what an allocation does;
  - a cell that is being forced ([CBusy]) or that the collector has moved ([CFwd]) stands for
    no term, so a cycle through a black hole has no reading at all.

  [nctx] is the length of the context the call started in: the machine's read-back lifts a
  suspension's free variables by [lvl - nctx + goff], exactly as [rb_susp] does. *)

Section Repr.
  Context (nctx : nat).

  (** [H] is a parameter: the relation is read in one heap. A cell that points forward to an
    address with no cell, or round to itself, has no derivation, hence stands for no term. *)

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

  Scheme repr_addr_min := Minimality for repr_addr Sort Prop
  with repr_addrs_min := Minimality for repr_addrs Sort Prop
  with repr_cell_min := Minimality for repr_cell Sort Prop
  with repr_slot_min := Minimality for repr_slot Sort Prop
  with repr_slots_min := Minimality for repr_slots Sort Prop
  with repr_susp_min := Minimality for repr_susp Sort Prop
  with repr_value_min := Minimality for repr_value Sort Prop.

  Combined Scheme repr_mutind from repr_addr_min, repr_addrs_min, repr_cell_min,
    repr_slot_min, repr_slots_min, repr_susp_min, repr_value_min.

  (** ** A black hole and a forwarding pointer stand for no term *)

  Lemma repr_cell_busy H lvl t : repr_cell H lvl CBusy t -> False.
  Proof. intros h. inversion h. Qed.

  Lemma repr_cell_fwd H lvl a t : repr_cell H lvl (CFwd a) t -> False.
  Proof. intros h. inversion h. Qed.

  (** ** The relation survives a heap that only grows *)

  Definition heap_le (H H' : bheap cbn_cell) : Prop :=
    forall a cl, bh_get a H = Some cl -> bh_get a H' = Some cl.

  Lemma heap_le_refl H : heap_le H H.
  Proof. intros a cl e. exact e. Qed.

  Lemma heap_le_trans H1 H2 H3 : heap_le H1 H2 -> heap_le H2 H3 -> heap_le H1 H3.
  Proof. intros h1 h2 a cl e. apply h2, h1, e. Qed.

  Section Mono.
    Context (H H' : bheap cbn_cell) (hle : heap_le H H').

    Lemma repr_mono :
      (forall lvl a t, repr_addr H lvl a t -> repr_addr H' lvl a t)
      /\ (forall lvl l ts, repr_addrs H lvl l ts -> repr_addrs H' lvl l ts)
      /\ (forall lvl cl t, repr_cell H lvl cl t -> repr_cell H' lvl cl t)
      /\ (forall lvl x t, repr_slot H lvl x t -> repr_slot H' lvl x t)
      /\ (forall lvl l ts, repr_slots H lvl l ts -> repr_slots H' lvl l ts)
      /\ (forall lvl e t u, repr_susp H lvl e t u -> repr_susp H' lvl e t u)
      /\ (forall lvl v t, repr_value H lvl v t -> repr_value H' lvl v t).
    Proof using hle.
      apply (repr_mutind H
        (fun lvl a t => repr_addr H' lvl a t)
        (fun lvl l ts => repr_addrs H' lvl l ts)
        (fun lvl cl t => repr_cell H' lvl cl t)
        (fun lvl x t => repr_slot H' lvl x t)
        (fun lvl l ts => repr_slots H' lvl l ts)
        (fun lvl e t u => repr_susp H' lvl e t u)
        (fun lvl v t => repr_value H' lvl v t));
        intros; econstructor; eauto.
    Qed.
  End Mono.

  Definition repr_addr_mono H H' (h : heap_le H H') := proj1 (repr_mono H H' h).
  Definition repr_value_mono H H' (h : heap_le H H') :=
    proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (repr_mono H H' h)))))).
  Definition repr_slot_mono H H' (h : heap_le H H') :=
    proj1 (proj2 (proj2 (proj2 (repr_mono H H' h)))).
  Definition repr_susp_mono H H' (h : heap_le H H') :=
    proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (repr_mono H H' h)))))).

  (** ** Allocation only grows the heap

    [alloc_now] writes a cell at the address [st_next] names, which had no cell: every older
    address reads what it read before, so every reading survives. The hypothesis is the
    heap's own invariant [bh_ok] of [PCUICCallByNeed], which [cbn_init] starts and every
    machine step keeps. *)

  Lemma alloc_now_heap_le lo cl s :
    bh_ok lo s.(st_next) s.(st_heap) ->
    heap_le s.(st_heap) (snd (alloc_now cl s)).(st_heap).
  Proof.
    intros hok a cl' e. cbn.
    assert (a <> HAddr s.(st_next)) as hne.
    { intros ->. erewrite bh_get_above in e; [discriminate|eassumption|apply Pos.le_refl]. }
    erewrite bh_digits_get_cons_old; eauto using bh_ok_digits.
  Qed.

  Lemma repr_value_alloc lo cl s lvl v t :
    bh_ok lo s.(st_next) s.(st_heap) ->
    repr_value s.(st_heap) lvl v t ->
    repr_value (snd (alloc_now cl s)).(st_heap) lvl v t.
  Proof. intros hok. apply repr_value_mono, (alloc_now_heap_le lo cl s hok). Qed.

  Lemma repr_slot_alloc lo cl s lvl x t :
    bh_ok lo s.(st_next) s.(st_heap) ->
    repr_slot s.(st_heap) lvl x t ->
    repr_slot (snd (alloc_now cl s)).(st_heap) lvl x t.
  Proof. intros hok. apply repr_slot_mono, (alloc_now_heap_le lo cl s hok). Qed.

  (** The address allocation returns stands for whatever the cell written there stands for. *)
  Lemma repr_addr_alloc lo cl s lvl t :
    bh_ok lo s.(st_next) s.(st_heap) ->
    repr_cell (snd (alloc_now cl s)).(st_heap) lvl cl t ->
    repr_addr (snd (alloc_now cl s)).(st_heap) lvl (fst (alloc_now cl s)) t.
  Proof.
    intros hok hc. econstructor; [|eassumption].
    cbn. apply bh_digits_get_cons_new, (bh_ok_digits _ _ _ hok).
  Qed.

  (** ** The relation is a partial function

    A structure stands for at most one term. This is what lets a proof speak of "the" term a
    value reads back to, without the read-back functions ever being called. *)

  Lemma repr_det H :
    (forall lvl a t, repr_addr H lvl a t -> forall t', repr_addr H lvl a t' -> t = t')
    /\ (forall lvl l ts, repr_addrs H lvl l ts -> forall ts', repr_addrs H lvl l ts' -> ts = ts')
    /\ (forall lvl cl t, repr_cell H lvl cl t -> forall t', repr_cell H lvl cl t' -> t = t')
    /\ (forall lvl x t, repr_slot H lvl x t -> forall t', repr_slot H lvl x t' -> t = t')
    /\ (forall lvl l ts, repr_slots H lvl l ts -> forall ts', repr_slots H lvl l ts' -> ts = ts')
    /\ (forall lvl e t u, repr_susp H lvl e t u -> forall u', repr_susp H lvl e t u' -> u = u')
    /\ (forall lvl v t, repr_value H lvl v t -> forall t', repr_value H lvl v t' -> t = t').
  Proof.
    apply (repr_mutind H
      (fun lvl a t => forall t', repr_addr H lvl a t' -> t = t')
      (fun lvl l ts => forall ts', repr_addrs H lvl l ts' -> ts = ts')
      (fun lvl cl t => forall t', repr_cell H lvl cl t' -> t = t')
      (fun lvl x t => forall t', repr_slot H lvl x t' -> t = t')
      (fun lvl l ts => forall ts', repr_slots H lvl l ts' -> ts = ts')
      (fun lvl e t u => forall u', repr_susp H lvl e t u' -> u = u')
      (fun lvl v t => forall t', repr_value H lvl v t' -> t = t')).
    (* In each case the second derivation is the newest hypothesis: invert it once, match the
       two cells (or the two fixpoint codes) at the same address, then use the induction
       hypotheses. Nothing is inverted twice. *)
    all: intros; match goal with h : _ |- _ => inversion h; subst; clear h end.
    all: repeat match goal with
         | h : bh_get ?a ?hp = Some ?x, h' : bh_get ?a ?hp = Some ?y |- _ =>
           rewrite h in h'; inversion h'; subst; clear h'
         | h : ?x = tFix _ _, h' : ?x = tFix _ _ |- _ =>
           rewrite h in h'; inversion h'; subst; clear h'
         end.
    all: repeat match goal with
         | ih : forall z, repr_addr _ _ _ z -> _, h : repr_addr _ _ _ _ |- _ =>
           specialize (ih _ h); subst
         | ih : forall z, repr_addrs _ _ _ z -> _, h : repr_addrs _ _ _ _ |- _ =>
           specialize (ih _ h); subst
         | ih : forall z, repr_cell _ _ _ z -> _, h : repr_cell _ _ _ _ |- _ =>
           specialize (ih _ h); subst
         | ih : forall z, repr_slot _ _ _ z -> _, h : repr_slot _ _ _ _ |- _ =>
           specialize (ih _ h); subst
         | ih : forall z, repr_slots _ _ _ z -> _, h : repr_slots _ _ _ _ |- _ =>
           specialize (ih _ h); subst
         | ih : forall z, repr_susp _ _ _ _ z -> _, h : repr_susp _ _ _ _ _ |- _ =>
           specialize (ih _ h); subst
         | ih : forall z, repr_value _ _ _ z -> _, h : repr_value _ _ _ _ |- _ =>
           specialize (ih _ h); subst
         end; try reflexivity.
  Qed.

  (** ** The state invariant

    [state_ok lo s] is what every machine function assumes of the state it is given and
    re-establishes for the state it returns. [lo] is the first address the last collection
    kept: below it the addresses are gone, and nothing live may name them.

    - the heap was built the way [bh_ok] describes, so the laws of [PCUICCallByNeed] apply;
    - no cell names an address outside the heap, in either direction: this is the invariant
      the dangling-address counter of the measurement runs watches, and the one the collector
      must re-establish after it moves every live cell;
    - the context map [st_gam] names only addresses the heap has. *)

  Definition addrs_in (lo n : positive) (l : list haddr) : Prop :=
    Forall (fun b => (lo <= ha_p b)%positive /\ (ha_p b < n)%positive) l.

  Record state_ok (lo : positive) (s : cbn_state) : Prop := mkStateOk {
    so_heap : bh_ok lo s.(st_next) s.(st_heap);
    so_cells : forall a cl, bh_get a s.(st_heap) = Some cl ->
      addrs_in lo s.(st_next) (ad_cell cl);
    so_gam : forall k a, PTree.get k s.(st_gam) = Some a ->
      (lo <= ha_p a)%positive /\ (ha_p a < s.(st_next))%positive }.

  Lemma addrs_in_grow lo n n' l :
    (n <= n')%positive -> addrs_in lo n l -> addrs_in lo n' l.
  Proof.
    intros hn. induction 1 as [|b l [h1 h2] _ ih]; constructor.
    - split; [exact h1|]. eapply Pos.lt_le_trans; eassumption.
    - exact ih.
  Qed.

  Lemma haddr_dec (a b : haddr) : {a = b} + {a <> b}.
  Proof.
    destruct a as [p], b as [q]. destruct (Pos.eq_dec p q) as [->|hne].
    - left; reflexivity.
    - right. intros e. inversion e. contradiction.
  Qed.

  Lemma state_ok_init : state_ok xH cbn_init.
  Proof.
    split.
    - exact cbn_init_ok.
    - intros a cl e. unfold cbn_init in e. cbn [st_heap] in e.
      rewrite bh_get_holes in e. discriminate.
    - intros k a e. unfold cbn_init in e. cbn [st_gam] in e.
      rewrite PTree.gempty in e. discriminate.
  Qed.

  (** Allocation: the state stays good exactly when the cell written names no address the
    heap does not have. The new address itself is allowed, so a cell may point to itself. *)
  Lemma alloc_now_state_ok lo cl s :
    state_ok lo s ->
    addrs_in lo (Pos.succ s.(st_next)) (ad_cell cl) ->
    state_ok lo (snd (alloc_now cl s)).
  Proof.
    intros [hh hc hg] hcl. split; cbn.
    - apply (bh_ok_cons _ _ _ _ hh).
    - intros a cl' e.
      destruct (haddr_dec a (HAddr s.(st_next))) as [->|hne].
      + erewrite bh_digits_get_cons_new in e by eauto using bh_ok_digits.
        inversion e; subst. exact hcl.
      + erewrite bh_digits_get_cons_old in e by eauto using bh_ok_digits.
        apply (addrs_in_grow _ _ _ _ (Pos.lt_le_incl _ _ (Pos.lt_succ_diag_r _)) (hc _ _ e)).
    - intros k a e. destruct (hg _ _ e) as [h1 h2]. split; [exact h1|].
      exact (Pos.lt_trans _ _ _ h2 (Pos.lt_succ_diag_r _)).
  Qed.

  (** A write to an address the heap has: forcing writes [CBusy], then the value. *)
  Lemma heap_upd_state_ok lo a cl s s' :
    state_ok lo s ->
    addrs_in lo s.(st_next) (ad_cell cl) ->
    heap_upd a cl s = Some s' ->
    state_ok lo s'.
  Proof.
    intros [hh hc hg] hcl e.
    unfold heap_upd in e.
    destruct (bh_upd a cl s.(st_heap)) as [h'|] eqn:hu; [|discriminate].
    cbn in e. inversion e; subst; clear e. split; cbn.
    - exact (bh_upd_ok _ _ _ _ _ _ hh hu).
    - intros b cl' e.
      destruct (haddr_dec b a) as [->|hne].
      + rewrite (bh_get_upd_same _ _ _ _ hu) in e. inversion e; subst. exact hcl.
      + rewrite (bh_get_upd_other _ _ _ _ _ hu hne) in e. exact (hc _ _ e).
    - exact hg.
  Qed.

  Lemma tick_state_ok lo s s' : state_ok lo s -> tick s = Some s' -> state_ok lo s'.
  Proof.
    intros [hh hc hg] e. unfold tick in e.
    destruct s.(st_steps) eqn:hs; [discriminate|].
    inversion e; subst; clear e. split; cbn; assumption.
  Qed.

End Repr.
