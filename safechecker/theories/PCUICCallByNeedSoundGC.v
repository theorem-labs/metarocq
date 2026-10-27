(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require CanonicalTries.
From MetaRocq.Common Require Import config Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils.
From MetaRocq.SafeChecker Require Import PCUICCallByNeed PCUICCallByNeedSound.

Import CanonicalTries.

(** * The copying collector of the call-by-need fast path (BET-298, step 2c)

  [collect] of [PCUICCallByNeed] copies every cell the roots and [st_gam] reach into a fresh
  heap whose addresses start at the old [st_next], leaves a forwarding pointer [CFwd] in the
  old heap, and renames the roots and [st_gam] with the map the copy built. This file proves
  that the collection changes no reading: a structure that stood for a term before stands,
  renamed, for the same term in the new heap; that the state invariant [state_ok] of
  [PCUICCallByNeedSound] holds again, with the old [st_next] as the new first address; and
  that a failure is one of the two reasons the code gives.

  What the proof needs beyond [state_ok]: the heap handed to [collect] must hold no [CFwd]
  cell ([heap_nofwd]). [state_ok] does not say so, and it cannot be dropped: a stale [CFwd a]
  is returned unchanged by [gc_copy], so its [a] - an address of the old heap, below the new
  heap's first address - would be written into the new heap and [state_ok] would fail. The
  machine satisfies it, because [collect] is the only writer of [CFwd] and it throws the old
  heap away; [collect] re-establishes it ([collect_nofwd]), so repeated collections keep it.

  The walk of [gc_copy] is bounded by fuel ([st_next] units). A heap with a cycle through a
  cell that is not yet copied exhausts it and the collection fails with [WGcFuel]; every
  statement about what a collection preserves is therefore under the hypothesis that it
  returned [COk]. No fuel is added to the code. *)

(** ** Heaps without forwarding pointers *)

Definition cell_fwd (cl : cbn_cell) : option haddr :=
  match cl with CFwd a => Some a | _ => None end.

Definition heap_nofwd (Hp : bheap cbn_cell) : Prop :=
  forall a a', bh_get a Hp = Some (CFwd a') -> False.

(** ** Two small heap facts *)

Lemma addrs_in_app lo n l1 l2 :
  addrs_in lo n l1 -> addrs_in lo n l2 -> addrs_in lo n (l1 ++ l2).
Proof.
  unfold addrs_in. induction 1 as [|b l hb hl ih]; simpl; [trivial|].
  intros h2. constructor; [exact hb|exact (ih h2)].
Qed.

(** Pushing a cell only grows the heap: every older address reads what it read. *)
Lemma heap_le_cons lo n (hp : bheap cbn_cell) cl :
  bh_ok lo n hp -> heap_le hp (bh_cons cl hp).
Proof.
  intros hok a x e.
  assert (a <> HAddr n) as hne.
  { intros ->. rewrite (bh_get_above _ _ _ (HAddr n) hok (Pos.le_refl n)) in e. discriminate. }
  rewrite (bh_get_cons_old _ _ _ _ _ hok hne). exact e.
Qed.

(** ** What a renamed root stands for

  A root is a sum of the machine's structures, so "the renamed root stands for what the root
  stood for" is one clause per shape. *)
Definition root_pres (nctx : nat) (Hold Hnew : bheap cbn_cell) (r r' : root) : Prop :=
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

(** ** The two equations of [gc_copy]

  [gc_copy] is a fixpoint on its fuel; these are its body, written once, so that no proof
  below depends on how [simpl] unfolds it. *)

Lemma gc_copy_FO (a : haddr) (g : gc_state) :
  gc_copy FO a g =
  match bh_get a g.(g_old) with
  | None => CFail WGcDangling
  | Some (CFwd a') => COk (a', g)
  | Some _ => CFail WGcFuel
  end.
Proof. reflexivity. Qed.

Lemma gc_copy_FS (k : unit -> cbn_fuel) (a : haddr) (g : gc_state) :
  gc_copy (FS k) a g =
  match bh_get a g.(g_old) with
  | None => CFail WGcDangling
  | Some (CFwd a') => COk (a', g)
  | Some cl =>
    match rn_cell (gc_copy (k tt)) cl g with
    | COk (cl1, g1) =>
      match bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old) with
      | Some old =>
        COk (HAddr g1.(g_next), mkGc old (bh_cons cl1 g1.(g_heap)) (Pos.succ g1.(g_next)))
      | None => CFail WGcDangling
      end
    | CFail w => CFail w
    end
  end.
Proof. reflexivity. Qed.

Section Collector.
  Context (nctx : nat) (Hold : bheap cbn_cell) (onext : positive).

  (** ** The collector's invariant

    [Hold] is the heap the collection started from and [onext] the address the new heap
    starts at. A state [g] of the walk satisfies [gc_inv g] when

    - every cell of [g_old] that is not a forwarding pointer is the cell [Hold] had there;
    - every forwarding pointer names an address of the new heap, and that address stands in
      the new heap for whatever the old address stood for in [Hold];
    - the new heap was built by [bh_holes onext] and [bh_cons] (so the laws of
      [PCUICCallByNeed] apply to it), names no address outside itself, and holds no
      forwarding pointer of its own. *)
  Record gc_inv (g : gc_state) : Prop := mkGcInv {
    gi_keep : forall a cl, bh_get a g.(g_old) = Some cl -> cell_fwd cl = None ->
      bh_get a Hold = Some cl;
    gi_moved : forall a a', bh_get a g.(g_old) = Some (CFwd a') ->
      (onext <= ha_p a')%positive /\ (ha_p a' < g.(g_next))%positive
      /\ (forall lvl t, repr_addr nctx Hold lvl a t -> repr_addr nctx g.(g_heap) lvl a' t);
    gi_heap : bh_ok onext g.(g_next) g.(g_heap);
    gi_cells : forall b cl, bh_get b g.(g_heap) = Some cl ->
      addrs_in onext g.(g_next) (ad_cell cl);
    gi_nofwd : heap_nofwd g.(g_heap) }.

  Lemma inv_keep g : gc_inv g -> forall a cl,
    bh_get a g.(g_old) = Some cl -> cell_fwd cl = None -> bh_get a Hold = Some cl.
  Proof. intros [h _ _ _ _]. exact h. Qed.

  Lemma inv_moved g : gc_inv g -> forall a a', bh_get a g.(g_old) = Some (CFwd a') ->
    (onext <= ha_p a')%positive /\ (ha_p a' < g.(g_next))%positive
    /\ (forall lvl t, repr_addr nctx Hold lvl a t -> repr_addr nctx g.(g_heap) lvl a' t).
  Proof. intros [_ h _ _ _]. exact h. Qed.

  Lemma inv_heap g : gc_inv g -> bh_ok onext g.(g_next) g.(g_heap).
  Proof. intros [_ _ h _ _]. exact h. Qed.

  Lemma inv_cells g : gc_inv g -> forall b cl, bh_get b g.(g_heap) = Some cl ->
    addrs_in onext g.(g_next) (ad_cell cl).
  Proof. intros [_ _ _ h _]. exact h. Qed.

  Lemma inv_nofwd g : gc_inv g -> heap_nofwd g.(g_heap).
  Proof. intros [_ _ _ _ h]. exact h. Qed.

  (** A step of the walk: the invariant again, a new heap that only grew, and a first
    address that only moved up. *)
  Record gstep (g g' : gc_state) : Prop := mkGStep {
    gs_inv : gc_inv g';
    gs_heap : heap_le g.(g_heap) g'.(g_heap);
    gs_next : (g.(g_next) <= g'.(g_next))%positive }.

  Lemma step_inv g g' : gstep g g' -> gc_inv g'.
  Proof. intros [h _ _]. exact h. Qed.

  Lemma step_heap g g' : gstep g g' -> heap_le g.(g_heap) g'.(g_heap).
  Proof. intros [_ h _]. exact h. Qed.

  Lemma step_next g g' : gstep g g' -> (g.(g_next) <= g'.(g_next))%positive.
  Proof. intros [_ _ h]. exact h. Qed.

  Lemma gstep_refl g : gc_inv g -> gstep g g.
  Proof. intros h. constructor; [exact h|apply heap_le_refl|apply Pos.le_refl]. Qed.

  Lemma gstep_trans g1 g2 g3 : gstep g1 g2 -> gstep g2 g3 -> gstep g1 g3.
  Proof.
    intros [_ l1 n1] [i2 l2 n2].
    constructor; [exact i2|exact (heap_le_trans _ _ _ l1 l2)|exact (Pos.le_trans _ _ _ n1 n2)].
  Qed.

  (** ** What the collector asks of the address map it threads through the renamings *)
  Definition cp_ok (cp : haddr -> gc_state -> cbn_res (haddr * gc_state)) : Prop :=
    forall a g a' g', gc_inv g -> cp a g = COk (a', g') ->
      gstep g g'
      /\ (onext <= ha_p a')%positive /\ (ha_p a' < g'.(g_next))%positive
      /\ (forall lvl t, repr_addr nctx Hold lvl a t -> repr_addr nctx g'.(g_heap) lvl a' t).

  (** ** The pieces of [repr] this file takes apart and puts back together *)

  Lemma mono_addrs (Hp Hq : bheap cbn_cell) (h : heap_le Hp Hq) lvl l ts :
    repr_addrs nctx Hp lvl l ts -> repr_addrs nctx Hq lvl l ts.
  Proof. exact (proj1 (proj2 (repr_mono nctx Hp Hq h)) lvl l ts). Qed.

  Lemma mono_cell (Hp Hq : bheap cbn_cell) (h : heap_le Hp Hq) lvl cl t :
    repr_cell nctx Hp lvl cl t -> repr_cell nctx Hq lvl cl t.
  Proof. exact (proj1 (proj2 (proj2 (repr_mono nctx Hp Hq h))) lvl cl t). Qed.

  Lemma mono_slots (Hp Hq : bheap cbn_cell) (h : heap_le Hp Hq) lvl l ts :
    repr_slots nctx Hp lvl l ts -> repr_slots nctx Hq lvl l ts.
  Proof.
    exact (proj1 (proj2 (proj2 (proj2 (proj2 (repr_mono nctx Hp Hq h))))) lvl l ts).
  Qed.

  Lemma repr_addr_cell (Hp : bheap cbn_cell) lvl a t :
    repr_addr nctx Hp lvl a t ->
    exists cl, bh_get a Hp = Some cl /\ repr_cell nctx Hp lvl cl t.
  Proof. intros h. inversion h; subst. eexists; split; eassumption. Qed.

  Lemma repr_addrs_nil_inv (Hp : bheap cbn_cell) lvl ts :
    repr_addrs nctx Hp lvl [] ts -> ts = [].
  Proof. intros h. inversion h; subst. reflexivity. Qed.

  Lemma repr_addrs_cons_inv (Hp : bheap cbn_cell) lvl a l ts :
    repr_addrs nctx Hp lvl (a :: l) ts ->
    exists t ts0, ts = t :: ts0 /\ repr_addr nctx Hp lvl a t /\ repr_addrs nctx Hp lvl l ts0.
  Proof.
    intros h. inversion h; subst.
    do 2 eexists; split; [reflexivity|split; eassumption].
  Qed.

  Lemma repr_slots_nil_inv (Hp : bheap cbn_cell) lvl ts :
    repr_slots nctx Hp lvl [] ts -> ts = [].
  Proof. intros h. inversion h; subst. reflexivity. Qed.

  Lemma repr_slots_cons_inv (Hp : bheap cbn_cell) lvl x l ts :
    repr_slots nctx Hp lvl (x :: l) ts ->
    exists t ts0, ts = t :: ts0 /\ repr_slot nctx Hp lvl x t /\ repr_slots nctx Hp lvl l ts0.
  Proof.
    intros h. inversion h; subst.
    do 2 eexists; split; [reflexivity|split; eassumption].
  Qed.

  Lemma repr_slot_addr_inv (Hp : bheap cbn_cell) lvl a t :
    repr_slot nctx Hp lvl (SAddr a) t -> repr_addr nctx Hp lvl a t.
  Proof. intros h. inversion h; subst. assumption. Qed.

  Lemma repr_slot_inl_inv (Hp : bheap cbn_cell) lvl vals n o c t :
    repr_slot nctx Hp lvl (SInl vals n o c) t ->
    repr_susp nctx Hp lvl (mkEnv vals n o) c.(c_term) t.
  Proof. intros h. inversion h; subst. assumption. Qed.

  Lemma repr_cell_susp_inv (Hp : bheap cbn_cell) lvl vals n o c t :
    repr_cell nctx Hp lvl (CSusp vals n o c) t ->
    repr_susp nctx Hp lvl (mkEnv vals n o) c.(c_term) t.
  Proof. intros h. inversion h; subst. assumption. Qed.

  Lemma repr_cell_done_inv (Hp : bheap cbn_cell) lvl v t :
    repr_cell nctx Hp lvl (CDone v) t -> repr_value nctx Hp lvl v t.
  Proof. intros h. inversion h; subst. assumption. Qed.

  (** A suspension reads back through its slots only: replace them by slots that stand for
    the same terms in another heap and the suspension stands for the same term. *)
  Lemma repr_susp_transport (Hp : bheap cbn_cell) lvl vals n o tm u :
    repr_susp nctx Hp lvl (mkEnv vals n o) tm u ->
    forall (Hq : bheap cbn_cell) vals',
      (forall lvl' ts, repr_slots nctx Hp lvl' vals ts -> repr_slots nctx Hq lvl' vals' ts) ->
      repr_susp nctx Hq lvl (mkEnv vals' n o) tm u.
  Proof.
    intros h Hq vals' hs. inversion h; subst. constructor. apply hs. assumption.
  Qed.

  (** ** The renamings under an address map that satisfies [cp_ok] *)

  Section Structural.
    Context (cp : haddr -> gc_state -> cbn_res (haddr * gc_state)) (hcp : cp_ok cp).

    Lemma rn_addrs_ok : forall (l : list haddr) (g : gc_state) (l' : list haddr) (g' : gc_state),
      gc_inv g -> rn_addrs cp l g = COk (l', g') ->
      gstep g g' /\ addrs_in onext g'.(g_next) l'
      /\ (forall lvl ts, repr_addrs nctx Hold lvl l ts -> repr_addrs nctx g'.(g_heap) lvl l' ts).
    Proof.
      induction l as [|a l ih]; intros g l' g' hinv he; simpl in he.
      - inversion he; subst; clear he.
        split; [exact (gstep_refl _ hinv)|].
        split; [constructor|].
        intros lvl ts h. rewrite (repr_addrs_nil_inv _ _ _ h). constructor.
      - destruct (cp a g) as [[b g1]|w] eqn:e1; [|discriminate].
        destruct (rn_addrs cp l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (hcp _ _ _ _ hinv e1) as [hs1 [hb1 [hb2 hr1]]].
        destruct (ih _ _ _ (step_inv _ _ hs1) e2) as [hs2 [had2 hr2]].
        split; [exact (gstep_trans _ _ _ hs1 hs2)|].
        split.
        + constructor;
            [split; [exact hb1|exact (Pos.lt_le_trans _ _ _ hb2 (step_next _ _ hs2))]|exact had2].
        + intros lvl ts h.
          destruct (repr_addrs_cons_inv _ _ _ _ _ h) as [t [ts0 [-> [ha hl]]]].
          constructor.
          * exact (repr_addr_mono nctx _ _ (step_heap _ _ hs2) _ _ _ (hr1 _ _ ha)).
          * exact (hr2 _ _ hl).
    Qed.

    Lemma rn_slot_ok : forall (x : cbn_slot) (g : gc_state) (x' : cbn_slot) (g' : gc_state),
      gc_inv g -> rn_slot cp x g = COk (x', g') ->
      gstep g g' /\ addrs_in onext g'.(g_next) (ad_slot x')
      /\ (forall lvl t, repr_slot nctx Hold lvl x t -> repr_slot nctx g'.(g_heap) lvl x' t).
    Proof.
      intros x. induction x as [a|vs n o c ihvs] using slot_ind'; intros g x' g' hinv he.
      - simpl in he. destruct (cp a g) as [[b g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (hcp _ _ _ _ hinv e1) as [hs1 [hb1 [hb2 hr1]]].
        split; [exact hs1|].
        split; [constructor; [split; assumption|constructor]|].
        intros lvl t h. constructor. exact (hr1 _ _ (repr_slot_addr_inv _ _ _ _ h)).
      - rewrite rn_slot_SInl in he.
        destruct (rn_slots cp vs g) as [[vs' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        assert (hl : gstep g g' /\ addrs_in onext g'.(g_next) (ad_slots vs')
                /\ (forall lvl ts, repr_slots nctx Hold lvl vs ts ->
                                   repr_slots nctx g'.(g_heap) lvl vs' ts)).
        { revert g vs' g' hinv e1. induction ihvs as [|y vs hy hvs ihl];
            intros g vs' g1 hinv e1; simpl in e1.
          - inversion e1; subst; clear e1.
            split; [exact (gstep_refl _ hinv)|].
            split; [constructor|].
            intros lvl ts h. rewrite (repr_slots_nil_inv _ _ _ h). constructor.
          - destruct (rn_slot cp y g) as [[y' ga]|wa] eqn:ea; [|discriminate].
            destruct (rn_slots cp vs ga) as [[vs2 gb]|wb] eqn:eb; [|discriminate].
            inversion e1; subst; clear e1.
            destruct (hy _ _ _ hinv ea) as [hsa [hada hra]].
            destruct (ihl _ _ _ (step_inv _ _ hsa) eb) as [hsb [hadb hrb]].
            split; [exact (gstep_trans _ _ _ hsa hsb)|].
            split.
            + unfold ad_slots. simpl. apply addrs_in_app.
              * exact (addrs_in_grow _ _ _ _ (step_next _ _ hsb) hada).
              * exact hadb.
            + intros lvl ts h.
              destruct (repr_slots_cons_inv _ _ _ _ _ h) as [t [ts0 [-> [hy1 hl1]]]].
              constructor.
              * exact (repr_slot_mono nctx _ _ (step_heap _ _ hsb) _ _ _ (hra _ _ hy1)).
              * exact (hrb _ _ hl1). }
        destruct hl as [hs [had hr]].
        split; [exact hs|]. split; [exact had|].
        intros lvl t h.
        constructor.
        exact (repr_susp_transport _ _ _ _ _ _ _ (repr_slot_inl_inv _ _ _ _ _ _ _ h)
                 _ vs' hr).
    Qed.

    Lemma rn_slots_ok : forall (l : list cbn_slot) (g : gc_state) (l' : list cbn_slot)
        (g' : gc_state),
      gc_inv g -> rn_slots cp l g = COk (l', g') ->
      gstep g g' /\ addrs_in onext g'.(g_next) (ad_slots l')
      /\ (forall lvl ts, repr_slots nctx Hold lvl l ts -> repr_slots nctx g'.(g_heap) lvl l' ts).
    Proof.
      induction l as [|y l ih]; intros g l' g' hinv he; simpl in he.
      - inversion he; subst; clear he.
        split; [exact (gstep_refl _ hinv)|].
        split; [constructor|].
        intros lvl ts h. rewrite (repr_slots_nil_inv _ _ _ h). constructor.
      - destruct (rn_slot cp y g) as [[y' g1]|w] eqn:e1; [|discriminate].
        destruct (rn_slots cp l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_slot_ok _ _ _ _ hinv e1) as [hs1 [had1 hr1]].
        destruct (ih _ _ _ (step_inv _ _ hs1) e2) as [hs2 [had2 hr2]].
        split; [exact (gstep_trans _ _ _ hs1 hs2)|].
        split.
        + unfold ad_slots. simpl. apply addrs_in_app.
          * exact (addrs_in_grow _ _ _ _ (step_next _ _ hs2) had1).
          * exact had2.
        + intros lvl ts h.
          destruct (repr_slots_cons_inv _ _ _ _ _ h) as [t [ts0 [-> [hy1 hl1]]]].
          constructor.
          * exact (repr_slot_mono nctx _ _ (step_heap _ _ hs2) _ _ _ (hr1 _ _ hy1)).
          * exact (hr2 _ _ hl1).
    Qed.

    Lemma rn_env_ok (e : cbn_env) (g : gc_state) (e' : cbn_env) (g' : gc_state) :
      gc_inv g -> rn_env cp e g = COk (e', g') ->
      gstep g g' /\ addrs_in onext g'.(g_next) (ad_env e')
      /\ (forall lvl tm u, repr_susp nctx Hold lvl e tm u ->
                           repr_susp nctx g'.(g_heap) lvl e' tm u).
    Proof.
      destruct e as [vals n o]. intros hinv he.
      unfold rn_env in he. cbn [ev_vals ev_nvals ev_goff] in he.
      destruct (rn_slots cp vals g) as [[vs' g1]|w] eqn:e1; [|discriminate].
      inversion he; subst; clear he.
      destruct (rn_slots_ok _ _ _ _ hinv e1) as [hs [had hr]].
      split; [exact hs|]. split; [exact had|].
      intros lvl tm u h.
      exact (repr_susp_transport _ _ _ _ _ _ _ h _ vs' hr).
    Qed.

    Lemma rn_value_ok (v : cbn_value) (g : gc_state) (v' : cbn_value) (g' : gc_state) :
      gc_inv g -> rn_value cp v g = COk (v', g') ->
      gstep g g' /\ addrs_in onext g'.(g_next) (ad_value v')
      /\ (forall lvl t, repr_value nctx Hold lvl v t -> repr_value nctx g'.(g_heap) lvl v' t).
    Proof.
      destruct v as [hd sp|e c|e c i sp|e c i sp|hd sp|e c|e c sp]; intros hinv he;
        unfold rn_value in he.
      - destruct (rn_addrs cp sp g) as [[sp' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_addrs_ok _ _ _ _ hinv e1) as [hs [had hr]].
        split; [exact hs|]. split; [exact had|].
        intros lvl t h. inversion h; subst. constructor. apply hr. assumption.
      - destruct (rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_env_ok _ _ _ _ hinv e1) as [hs [had hr]].
        split; [exact hs|]. split; [exact had|].
        intros lvl t h. inversion h; subst. constructor. apply hr. assumption.
      - destruct (rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        destruct (rn_addrs cp sp g1) as [[sp' g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_env_ok _ _ _ _ hinv e1) as [hs1 [had1 hr1]].
        destruct (rn_addrs_ok _ _ _ _ (step_inv _ _ hs1) e2) as [hs2 [had2 hr2]].
        split; [exact (gstep_trans _ _ _ hs1 hs2)|].
        split.
        + apply addrs_in_app;
            [exact (addrs_in_grow _ _ _ _ (step_next _ _ hs2) had1)|exact had2].
        + intros lvl t h. inversion h; subst.
          eapply repr_VFix; [eassumption| |apply hr2; assumption].
          exact (repr_susp_mono nctx _ _ (step_heap _ _ hs2) _ _ _ _ (hr1 _ _ _ ltac:(eassumption))).
      - destruct (rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        destruct (rn_addrs cp sp g1) as [[sp' g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_env_ok _ _ _ _ hinv e1) as [hs1 [had1 hr1]].
        destruct (rn_addrs_ok _ _ _ _ (step_inv _ _ hs1) e2) as [hs2 [had2 hr2]].
        split; [exact (gstep_trans _ _ _ hs1 hs2)|].
        split.
        + apply addrs_in_app;
            [exact (addrs_in_grow _ _ _ _ (step_next _ _ hs2) had1)|exact had2].
        + intros lvl t h. inversion h; subst.
          eapply repr_VStuckFix; [eassumption| |apply hr2; assumption].
          exact (repr_susp_mono nctx _ _ (step_heap _ _ hs2) _ _ _ _ (hr1 _ _ _ ltac:(eassumption))).
      - destruct (rn_addrs cp sp g) as [[sp' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_addrs_ok _ _ _ _ hinv e1) as [hs [had hr]].
        split; [exact hs|]. split; [exact had|].
        intros lvl t h. inversion h; subst.
        + constructor. apply hr. assumption.
        + constructor. apply hr. assumption.
      - destruct (rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_env_ok _ _ _ _ hinv e1) as [hs [had hr]].
        split; [exact hs|]. split; [exact had|].
        intros lvl t h. inversion h; subst. constructor. apply hr. assumption.
      - destruct (rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        destruct (rn_addrs cp sp g1) as [[sp' g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_env_ok _ _ _ _ hinv e1) as [hs1 [had1 hr1]].
        destruct (rn_addrs_ok _ _ _ _ (step_inv _ _ hs1) e2) as [hs2 [had2 hr2]].
        split; [exact (gstep_trans _ _ _ hs1 hs2)|].
        split.
        + apply addrs_in_app;
            [exact (addrs_in_grow _ _ _ _ (step_next _ _ hs2) had1)|exact had2].
        + intros lvl t h. inversion h; subst.
          eapply repr_VStuck; [|apply hr2; assumption].
          exact (repr_susp_mono nctx _ _ (step_heap _ _ hs2) _ _ _ _ (hr1 _ _ _ ltac:(eassumption))).
    Qed.

    Lemma rn_cell_ok (cl : cbn_cell) (g : gc_state) (cl' : cbn_cell) (g' : gc_state) :
      gc_inv g -> rn_cell cp cl g = COk (cl', g') ->
      gstep g g' /\ addrs_in onext g'.(g_next) (ad_cell cl')
      /\ (forall lvl t, repr_cell nctx Hold lvl cl t -> repr_cell nctx g'.(g_heap) lvl cl' t).
    Proof.
      destruct cl as [vals n o c|v| |b]; intros hinv he; unfold rn_cell in he.
      - destruct (rn_slots cp vals g) as [[vs' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_slots_ok _ _ _ _ hinv e1) as [hs [had hr]].
        split; [exact hs|]. split; [exact had|].
        intros lvl t h. constructor.
        exact (repr_susp_transport _ _ _ _ _ _ _ (repr_cell_susp_inv _ _ _ _ _ _ _ h) _ vs' hr).
      - destruct (rn_value cp v g) as [[v' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_value_ok _ _ _ _ hinv e1) as [hs [had hr]].
        split; [exact hs|]. split; [exact had|].
        intros lvl t h. constructor. exact (hr _ _ (repr_cell_done_inv _ _ _ _ h)).
      - inversion he; subst; clear he.
        split; [exact (gstep_refl _ hinv)|].
        split; [constructor|].
        intros lvl t h. destruct (repr_cell_busy nctx _ _ _ h).
      - destruct (cp b g) as [[b' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (hcp _ _ _ _ hinv e1) as [hs [hb1 [hb2 _]]].
        split; [exact hs|].
        split; [constructor; [split; assumption|constructor]|].
        intros lvl t h. destruct (repr_cell_fwd nctx _ _ _ _ h).
    Qed.

    (** A renamed cell is a forwarding pointer only if the cell was one. *)
    Lemma rn_cell_nofwd (cl : cbn_cell) (g : gc_state) (cl' : cbn_cell) (g' : gc_state) :
      cell_fwd cl = None -> rn_cell cp cl g = COk (cl', g') -> cell_fwd cl' = None.
    Proof.
      destruct cl as [vals n o c|v| |b]; intros hf he; unfold rn_cell in he.
      - destruct (rn_slots cp vals g) as [[vs' g1]|w]; [|discriminate].
        inversion he; subst. reflexivity.
      - destruct (rn_value cp v g) as [[v' g1]|w]; [|discriminate].
        inversion he; subst. reflexivity.
      - inversion he; subst. reflexivity.
      - discriminate.
    Qed.

    Lemma rn_root_ok (r : root) (g : gc_state) (r' : root) (g' : gc_state) :
      gc_inv g -> rn_root cp r g = COk (r', g') ->
      gstep g g' /\ addrs_in onext g'.(g_next) (ad_root r')
      /\ root_pres nctx Hold g'.(g_heap) r r'.
    Proof.
      destruct r as [a|x|e|v|l|l|cl]; intros hinv he; unfold rn_root in he.
      - destruct (cp a g) as [[b g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (hcp _ _ _ _ hinv e1) as [hs [hb1 [hb2 hr]]].
        split; [exact hs|].
        split; [constructor; [split; assumption|constructor]|]. exact hr.
      - destruct (rn_slot cp x g) as [[x' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_slot_ok _ _ _ _ hinv e1) as [hs [had hr]].
        split; [exact hs|]. split; [exact had|]. exact hr.
      - destruct (rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_env_ok _ _ _ _ hinv e1) as [hs [had hr]].
        split; [exact hs|]. split; [exact had|]. exact hr.
      - destruct (rn_value cp v g) as [[v' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_value_ok _ _ _ _ hinv e1) as [hs [had hr]].
        split; [exact hs|]. split; [exact had|]. exact hr.
      - destruct (rn_slots cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_slots_ok _ _ _ _ hinv e1) as [hs [had hr]].
        split; [exact hs|]. split; [exact had|]. exact hr.
      - destruct (rn_addrs cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_addrs_ok _ _ _ _ hinv e1) as [hs [had hr]].
        split; [exact hs|]. split; [exact had|]. exact hr.
      - destruct (rn_cell cp cl g) as [[cl' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_cell_ok _ _ _ _ hinv e1) as [hs [had hr]].
        split; [exact hs|]. split; [exact had|]. exact hr.
    Qed.

    Lemma root_pres_mono (Hp Hq : bheap cbn_cell) r r' :
      heap_le Hp Hq -> root_pres nctx Hold Hp r r' -> root_pres nctx Hold Hq r r'.
    Proof.
      intros hle. destruct r, r'; simpl; intros h; try contradiction.
      - intros lvl t ht. exact (repr_addr_mono nctx _ _ hle _ _ _ (h lvl t ht)).
      - intros lvl t ht. exact (repr_slot_mono nctx _ _ hle _ _ _ (h lvl t ht)).
      - intros lvl tm u ht. exact (repr_susp_mono nctx _ _ hle _ _ _ _ (h lvl tm u ht)).
      - intros lvl t ht. exact (repr_value_mono nctx _ _ hle _ _ _ (h lvl t ht)).
      - intros lvl ts ht. exact (mono_slots _ _ hle _ _ _ (h lvl ts ht)).
      - intros lvl ts ht. exact (mono_addrs _ _ hle _ _ _ (h lvl ts ht)).
      - intros lvl t ht. exact (mono_cell _ _ hle _ _ _ (h lvl t ht)).
    Qed.

    Lemma rn_roots_ok : forall (l : list root) (g : gc_state) (l' : list root) (g' : gc_state),
      gc_inv g -> rn_roots cp l g = COk (l', g') ->
      gstep g g' /\ addrs_in onext g'.(g_next) (ad_roots l')
      /\ Forall2 (root_pres nctx Hold g'.(g_heap)) l l'.
    Proof.
      induction l as [|r l ih]; intros g l' g' hinv he; simpl in he.
      - inversion he; subst; clear he.
        split; [exact (gstep_refl _ hinv)|].
        split; [constructor|constructor].
      - destruct (rn_root cp r g) as [[r' g1]|w] eqn:e1; [|discriminate].
        destruct (rn_roots cp l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_root_ok _ _ _ _ hinv e1) as [hs1 [had1 hr1]].
        destruct (ih _ _ _ (step_inv _ _ hs1) e2) as [hs2 [had2 hr2]].
        split; [exact (gstep_trans _ _ _ hs1 hs2)|].
        split.
        + unfold ad_roots. simpl. apply addrs_in_app.
          * exact (addrs_in_grow _ _ _ _ (step_next _ _ hs2) had1).
          * exact had2.
        + constructor; [exact (root_pres_mono _ _ _ _ (step_heap _ _ hs2) hr1)|exact hr2].
    Qed.

    (** *** The context map [st_gam] *)

    Lemma rn_tree'_ok : forall (m : PTree.tree' haddr) (g : gc_state)
        (m' : PTree.tree' haddr) (g' : gc_state),
      gc_inv g -> rn_tree' cp m g = COk (m', g') ->
      gstep g g'
      /\ (forall p a', PTree.get' p m' = Some a' ->
            (onext <= ha_p a')%positive /\ (ha_p a' < g'.(g_next))%positive)
      /\ (forall p a, PTree.get' p m = Some a ->
            exists a', PTree.get' p m' = Some a'
              /\ (forall lvl t, repr_addr nctx Hold lvl a t ->
                                repr_addr nctx g'.(g_heap) lvl a' t)).
    Proof.
      induction m as [r ihr|x|x r ihr|l ihl|l ihl r ihr|l ihl x|l ihl x r ihr];
        intros g m' g' hinv he; simpl in he.
      - (* Node001 *)
        destruct (rn_tree' cp r g) as [[r' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (ihr _ _ _ hinv e1) as [hs1 [hb1 hr1]].
        split; [exact hs1|]. split.
        + intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
          exact (hb1 _ _ hb).
        + intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
          exact (hr1 _ _ hb).
      - (* Node010 *)
        destruct (cp x g) as [[x' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (hcp _ _ _ _ hinv e1) as [hs1 [hx1 [hx2 hxr]]].
        split; [exact hs1|]. split.
        + intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
          inversion hb; subst. split; assumption.
        + intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
          inversion hb; subst. exists x'. split; [reflexivity|exact hxr].
      - (* Node011 *)
        destruct (cp x g) as [[x' g1]|w] eqn:e1; [|discriminate].
        destruct (rn_tree' cp r g1) as [[r' g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (hcp _ _ _ _ hinv e1) as [hs1 [hx1 [hx2 hxr]]].
        destruct (ihr _ _ _ (step_inv _ _ hs1) e2) as [hs2 [hb2 hr2]].
        split; [exact (gstep_trans _ _ _ hs1 hs2)|]. split.
        + intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
          * exact (hb2 _ _ hb).
          * inversion hb; subst.
            split; [exact hx1|exact (Pos.lt_le_trans _ _ _ hx2 (step_next _ _ hs2))].
        + intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
          * exact (hr2 _ _ hb).
          * inversion hb; subst. exists x'. split; [reflexivity|].
            intros lvl t ht.
            exact (repr_addr_mono nctx _ _ (step_heap _ _ hs2) _ _ _ (hxr lvl t ht)).
      - (* Node100 *)
        destruct (rn_tree' cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (ihl _ _ _ hinv e1) as [hs1 [hb1 hr1]].
        split; [exact hs1|]. split.
        + intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
          exact (hb1 _ _ hb).
        + intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
          exact (hr1 _ _ hb).
      - (* Node101 *)
        destruct (rn_tree' cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
        destruct (rn_tree' cp r g1) as [[r' g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (ihl _ _ _ hinv e1) as [hs1 [hb1 hr1]].
        destruct (ihr _ _ _ (step_inv _ _ hs1) e2) as [hs2 [hb2 hr2]].
        split; [exact (gstep_trans _ _ _ hs1 hs2)|]. split.
        + intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
          * exact (hb2 _ _ hb).
          * destruct (hb1 _ _ hb) as [u1 u2].
            split; [exact u1|exact (Pos.lt_le_trans _ _ _ u2 (step_next _ _ hs2))].
        + intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
          * exact (hr2 _ _ hb).
          * destruct (hr1 _ _ hb) as [b' [hb' hrr]]. exists b'. split; [exact hb'|].
            intros lvl t ht.
            exact (repr_addr_mono nctx _ _ (step_heap _ _ hs2) _ _ _ (hrr lvl t ht)).
      - (* Node110 *)
        destruct (rn_tree' cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
        destruct (cp x g1) as [[x' g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (ihl _ _ _ hinv e1) as [hs1 [hb1 hr1]].
        destruct (hcp _ _ _ _ (step_inv _ _ hs1) e2) as [hs2 [hx1 [hx2 hxr]]].
        split; [exact (gstep_trans _ _ _ hs1 hs2)|]. split.
        + intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
          * destruct (hb1 _ _ hb) as [u1 u2].
            split; [exact u1|exact (Pos.lt_le_trans _ _ _ u2 (step_next _ _ hs2))].
          * inversion hb; subst. split; assumption.
        + intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
          * destruct (hr1 _ _ hb) as [b' [hb' hrr]]. exists b'. split; [exact hb'|].
            intros lvl t ht.
            exact (repr_addr_mono nctx _ _ (step_heap _ _ hs2) _ _ _ (hrr lvl t ht)).
          * inversion hb; subst. exists x'. split; [reflexivity|exact hxr].
      - (* Node111 *)
        destruct (rn_tree' cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
        destruct (cp x g1) as [[x' g2]|w] eqn:e2; [|discriminate].
        destruct (rn_tree' cp r g2) as [[r' g3]|w] eqn:e3; [|discriminate].
        inversion he; subst; clear he.
        destruct (ihl _ _ _ hinv e1) as [hs1 [hb1 hr1]].
        destruct (hcp _ _ _ _ (step_inv _ _ hs1) e2) as [hs2 [hx1 [hx2 hxr]]].
        destruct (ihr _ _ _ (step_inv _ _ hs2) e3) as [hs3 [hb3 hr3]].
        split; [exact (gstep_trans _ _ _ hs1 (gstep_trans _ _ _ hs2 hs3))|]. split.
        + intros p b hb. destruct p as [q|q|]; simpl in hb.
          * exact (hb3 _ _ hb).
          * destruct (hb1 _ _ hb) as [u1 u2]. split; [exact u1|].
            exact (Pos.lt_le_trans _ _ _ u2
                     (Pos.le_trans _ _ _ (step_next _ _ hs2) (step_next _ _ hs3))).
          * inversion hb; subst.
            split; [exact hx1|exact (Pos.lt_le_trans _ _ _ hx2 (step_next _ _ hs3))].
        + intros p b hb. destruct p as [q|q|]; simpl in hb.
          * exact (hr3 _ _ hb).
          * destruct (hr1 _ _ hb) as [b' [hb' hrr]]. exists b'. split; [exact hb'|].
            intros lvl t ht.
            exact (repr_addr_mono nctx _ _
                     (heap_le_trans _ _ _ (step_heap _ _ hs2) (step_heap _ _ hs3))
                     _ _ _ (hrr lvl t ht)).
          * inversion hb; subst. exists x'. split; [reflexivity|].
            intros lvl t ht.
            exact (repr_addr_mono nctx _ _ (step_heap _ _ hs3) _ _ _ (hxr lvl t ht)).
    Qed.

    Lemma rn_ptree_ok (m : PTree.t haddr) (g : gc_state) (m' : PTree.t haddr) (g' : gc_state) :
      gc_inv g -> rn_ptree cp m g = COk (m', g') ->
      gstep g g'
      /\ (forall p a', PTree.get p m' = Some a' ->
            (onext <= ha_p a')%positive /\ (ha_p a' < g'.(g_next))%positive)
      /\ (forall p a, PTree.get p m = Some a ->
            exists a', PTree.get p m' = Some a'
              /\ (forall lvl t, repr_addr nctx Hold lvl a t ->
                                repr_addr nctx g'.(g_heap) lvl a' t)).
    Proof.
      destruct m as [|m]; intros hinv he; unfold rn_ptree in he.
      - inversion he; subst; clear he.
        split; [exact (gstep_refl _ hinv)|].
        split; intros p b hb; discriminate.
      - destruct (rn_tree' cp m g) as [[m2 g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_tree'_ok _ _ _ _ hinv e1) as [hs [hb hr]].
        split; [exact hs|]. split.
        + intros p b hbb. exact (hb _ _ hbb).
        + intros p b hbb. exact (hr _ _ hbb).
    Qed.

    (** *** One copied cell

      The cell is read from the old heap, its children are renamed, the copy is pushed onto
      the new heap at [g_next] and the old cell is overwritten with [CFwd] of that address. *)
    Lemma gc_copy_write (a : haddr) (g : gc_state) (cl cl1 : cbn_cell) (g1 : gc_state)
        (old : bheap cbn_cell) :
      gc_inv g ->
      bh_get a g.(g_old) = Some cl ->
      cell_fwd cl = None ->
      rn_cell cp cl g = COk (cl1, g1) ->
      bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old) = Some old ->
      gstep g (mkGc old (bh_cons cl1 g1.(g_heap)) (Pos.succ g1.(g_next)))
      /\ (onext <= g1.(g_next))%positive
      /\ (g1.(g_next) < Pos.succ g1.(g_next))%positive
      /\ (forall lvl t, repr_addr nctx Hold lvl a t ->
            repr_addr nctx (bh_cons cl1 g1.(g_heap)) lvl (HAddr g1.(g_next)) t).
    Proof.
      intros hinv ha hf e1 e2.
      destruct (rn_cell_ok _ _ _ _ hinv e1) as [hs1 [had1 hr1]].
      pose proof (step_inv _ _ hs1) as hinv1.
      pose proof (inv_heap _ hinv1) as hok1.
      pose proof (heap_le_cons _ _ _ cl1 hok1) as hcons.
      pose proof (bh_ok_le _ _ _ hok1) as hlo1.
      pose proof (rn_cell_nofwd _ _ _ _ hf e1) as hf1.
      assert (hnew : forall lvl t, repr_addr nctx Hold lvl a t ->
                repr_addr nctx (bh_cons cl1 g1.(g_heap)) lvl (HAddr g1.(g_next)) t).
      { intros lvl t ht.
        destruct (repr_addr_cell _ _ _ _ ht) as [cl0 [hget hcell]].
        rewrite (inv_keep _ hinv _ _ ha hf) in hget. inversion hget; subst cl0.
        econstructor; [exact (bh_get_cons_new _ _ _ _ hok1)|].
        exact (mono_cell _ _ hcons _ _ _ (hr1 _ _ hcell)). }
      assert (hinv2 : gc_inv (mkGc old (bh_cons cl1 g1.(g_heap)) (Pos.succ g1.(g_next)))).
      { constructor; cbn.
        - intros b clb hb hfb. destruct (haddr_dec b a) as [->|hne].
          + rewrite (bh_get_upd_same _ _ _ _ e2) in hb.
            inversion hb; subst. discriminate.
          + rewrite (bh_get_upd_other _ _ _ _ _ e2 hne) in hb.
            exact (inv_keep _ hinv1 _ _ hb hfb).
        - intros b b' hb. destruct (haddr_dec b a) as [->|hne].
          + rewrite (bh_get_upd_same _ _ _ _ e2) in hb. inversion hb; subst.
            split; [exact hlo1|].
            split; [apply Pos.lt_succ_diag_r|exact hnew].
          + rewrite (bh_get_upd_other _ _ _ _ _ e2 hne) in hb.
            destruct (inv_moved _ hinv1 _ _ hb) as [u1 [u2 u3]].
            split; [exact u1|].
            split; [exact (Pos.lt_trans _ _ _ u2 (Pos.lt_succ_diag_r _))|].
            intros lvl t ht. exact (repr_addr_mono nctx _ _ hcons _ _ _ (u3 lvl t ht)).
        - exact (bh_ok_cons _ _ _ _ hok1).
        - intros b clb hb. destruct (haddr_dec b (HAddr g1.(g_next))) as [->|hne].
          + rewrite (bh_get_cons_new _ _ _ _ hok1) in hb. inversion hb; subst.
            exact (addrs_in_grow _ _ _ _ (Pos.lt_le_incl _ _ (Pos.lt_succ_diag_r _)) had1).
          + rewrite (bh_get_cons_old _ _ _ _ _ hok1 hne) in hb.
            exact (addrs_in_grow _ _ _ _ (Pos.lt_le_incl _ _ (Pos.lt_succ_diag_r _))
                     (inv_cells _ hinv1 _ _ hb)).
        - intros b b' hb. destruct (haddr_dec b (HAddr g1.(g_next))) as [->|hne].
          + rewrite (bh_get_cons_new _ _ _ _ hok1) in hb. inversion hb; subst. discriminate.
          + rewrite (bh_get_cons_old _ _ _ _ _ hok1 hne) in hb.
            exact (inv_nofwd _ hinv1 _ _ hb). }
      split.
      - constructor; cbn.
        + exact hinv2.
        + exact (heap_le_trans _ _ _ (step_heap _ _ hs1) hcons).
        + exact (Pos.le_trans _ _ _ (step_next _ _ hs1)
                   (Pos.lt_le_incl _ _ (Pos.lt_succ_diag_r _))).
      - split; [exact hlo1|].
        split; [apply Pos.lt_succ_diag_r|exact hnew].
    Qed.

  End Structural.

  (** ** The walk of [gc_copy] keeps the invariant

    Every address the collector returns is an address of the new heap, at or above [onext],
    and it stands there for whatever the old address stood for in [Hold]. *)
  Lemma gc_copy_ok : forall (f : cbn_fuel), cp_ok (gc_copy f).
  Proof.
    intros f. induction f as [|k ih]; intros a g a' g' hinv he.
    - rewrite gc_copy_FO in he.
      destruct (bh_get a g.(g_old)) as [cl|] eqn:ea; [|discriminate].
      destruct cl as [vals n o c|v| |b]; try discriminate.
      inversion he; subst; clear he.
      destruct (inv_moved _ hinv _ _ ea) as [hb1 [hb2 hr]].
      split; [exact (gstep_refl _ hinv)|].
      split; [exact hb1|]. split; [exact hb2|exact hr].
    - rewrite gc_copy_FS in he.
      destruct (bh_get a g.(g_old)) as [cl|] eqn:ea; [|discriminate].
      destruct cl as [vals n o c|v| |b].
      + destruct (rn_cell (gc_copy (k tt)) (CSusp vals n o c) g) as [[cl1 g1]|w] eqn:e1;
          [|discriminate].
        destruct (bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old)) as [old|] eqn:e2;
          [|discriminate].
        inversion he; subst; clear he.
        exact (gc_copy_write _ (ih tt) _ _ _ _ _ _ hinv ea eq_refl e1 e2).
      + destruct (rn_cell (gc_copy (k tt)) (CDone v) g) as [[cl1 g1]|w] eqn:e1;
          [|discriminate].
        destruct (bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old)) as [old|] eqn:e2;
          [|discriminate].
        inversion he; subst; clear he.
        exact (gc_copy_write _ (ih tt) _ _ _ _ _ _ hinv ea eq_refl e1 e2).
      + destruct (rn_cell (gc_copy (k tt)) CBusy g) as [[cl1 g1]|w] eqn:e1; [|discriminate].
        destruct (bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old)) as [old|] eqn:e2;
          [|discriminate].
        inversion he; subst; clear he.
        exact (gc_copy_write _ (ih tt) _ _ _ _ _ _ hinv ea eq_refl e1 e2).
      + inversion he; subst; clear he.
        destruct (inv_moved _ hinv _ _ ea) as [hb1 [hb2 hr]].
        split; [exact (gstep_refl _ hinv)|].
        split; [exact hb1|]. split; [exact hb2|exact hr].
  Qed.

  (** The address the collector returns has a cell in the new heap, and that heap starts at
    [onext]: nothing the collector hands back points below it. *)
  Lemma gc_copy_target (f : cbn_fuel) (a : haddr) (g : gc_state) (a' : haddr) (g' : gc_state) :
    gc_inv g -> gc_copy f a g = COk (a', g') ->
    (onext <= ha_p a')%positive /\ (ha_p a' < g'.(g_next))%positive
    /\ (exists cl, bh_get a' g'.(g_heap) = Some cl).
  Proof.
    intros hinv he.
    destruct (gc_copy_ok f _ _ _ _ hinv he) as [hs [hb1 [hb2 _]]].
    split; [exact hb1|]. split; [exact hb2|].
    exact (bh_get_below _ _ _ _ (inv_heap _ (step_inv _ _ hs)) hb1 hb2).
  Qed.

End Collector.

(** ** One address: what [gc_copy] leaves behind

  Whether the cell was copied here or had been copied before, the old heap names the
  returned address with a forwarding pointer when [gc_copy] succeeds. *)
Lemma gc_copy_old_fwd (f : cbn_fuel) (a : haddr) (g : gc_state) (a' : haddr) (g' : gc_state) :
  gc_copy f a g = COk (a', g') -> bh_get a g'.(g_old) = Some (CFwd a').
Proof.
  destruct f as [|k]; intros he.
  - rewrite gc_copy_FO in he.
    destruct (bh_get a g.(g_old)) as [cl|] eqn:ea; [|discriminate].
    destruct cl as [vals n o c|v| |b]; try discriminate.
    inversion he; subst. exact ea.
  - rewrite gc_copy_FS in he.
    destruct (bh_get a g.(g_old)) as [cl|] eqn:ea; [|discriminate].
    destruct cl as [vals n o c|v| |b].
    + destruct (rn_cell (gc_copy (k tt)) (CSusp vals n o c) g) as [[cl1 g1]|w] eqn:e1;
        [|discriminate].
      destruct (bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old)) as [old|] eqn:e2;
        [|discriminate].
      inversion he; subst. cbn. exact (bh_get_upd_same _ _ _ _ e2).
    + destruct (rn_cell (gc_copy (k tt)) (CDone v) g) as [[cl1 g1]|w] eqn:e1; [|discriminate].
      destruct (bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old)) as [old|] eqn:e2;
        [|discriminate].
      inversion he; subst. cbn. exact (bh_get_upd_same _ _ _ _ e2).
    + destruct (rn_cell (gc_copy (k tt)) CBusy g) as [[cl1 g1]|w] eqn:e1; [|discriminate].
      destruct (bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old)) as [old|] eqn:e2;
        [|discriminate].
      inversion he; subst. cbn. exact (bh_get_upd_same _ _ _ _ e2).
    + inversion he; subst. exact ea.
Qed.

(** ** A failure of a renaming is a failure of its address map *)

Section RenameFail.
  Context {G : Type} (f : haddr -> G -> cbn_res (haddr * G)) (P : cbn_why -> Prop)
          (hf : forall (a : haddr) (g : G) (w : cbn_why), f a g = CFail w -> P w).

  Lemma rn_addrs_fail : forall (l : list haddr) (g : G) (w : cbn_why),
    rn_addrs f l g = CFail w -> P w.
  Proof.
    induction l as [|a l ih]; intros g w he; simpl in he; [discriminate|].
    destruct (f a g) as [[b g1]|w1] eqn:e1.
    - destruct (rn_addrs f l g1) as [[l2 g2]|w2] eqn:e2; [discriminate|].
      inversion he; subst. exact (ih _ _ e2).
    - inversion he; subst. exact (hf _ _ _ e1).
  Qed.

  Lemma rn_slot_fail : forall (x : cbn_slot) (g : G) (w : cbn_why),
    rn_slot f x g = CFail w -> P w.
  Proof.
    intros x. induction x as [a|vs n o c ihvs] using slot_ind'.
    - intros g w he. simpl in he.
      destruct (f a g) as [[b g1]|w1] eqn:e1; [discriminate|].
      inversion he; subst. exact (hf _ _ _ e1).
    - assert (hL : forall (g0 : G) (w0 : cbn_why), rn_slots f vs g0 = CFail w0 -> P w0).
      { induction ihvs as [|y vs hy hvs ihl]; intros g0 w0 e0; simpl in e0; [discriminate|].
        destruct (rn_slot f y g0) as [[y' ga]|wa] eqn:ea.
        - destruct (rn_slots f vs ga) as [[vs2 gb]|wb] eqn:eb; [discriminate|].
          inversion e0; subst. exact (ihl _ _ eb).
        - inversion e0; subst. exact (hy _ _ ea). }
      intros g w he. rewrite rn_slot_SInl in he.
      destruct (rn_slots f vs g) as [[vs' g1]|w1] eqn:e1; [discriminate|].
      inversion he; subst. exact (hL _ _ e1).
  Qed.

  Lemma rn_slots_fail : forall (l : list cbn_slot) (g : G) (w : cbn_why),
    rn_slots f l g = CFail w -> P w.
  Proof.
    induction l as [|y l ih]; intros g w he; simpl in he; [discriminate|].
    destruct (rn_slot f y g) as [[y' g1]|w1] eqn:e1.
    - destruct (rn_slots f l g1) as [[l2 g2]|w2] eqn:e2; [discriminate|].
      inversion he; subst. exact (ih _ _ e2).
    - inversion he; subst. exact (rn_slot_fail _ _ _ e1).
  Qed.

  Lemma rn_env_fail (e : cbn_env) (g : G) (w : cbn_why) : rn_env f e g = CFail w -> P w.
  Proof.
    destruct e as [vals n o]. intros he.
    unfold rn_env in he. cbn [ev_vals ev_nvals ev_goff] in he.
    destruct (rn_slots f vals g) as [[vs' g1]|w1] eqn:e1; [discriminate|].
    inversion he; subst. exact (rn_slots_fail _ _ _ e1).
  Qed.

  Lemma rn_value_fail (v : cbn_value) (g : G) (w : cbn_why) : rn_value f v g = CFail w -> P w.
  Proof.
    destruct v as [hd sp|e c|e c i sp|e c i sp|hd sp|e c|e c sp]; intros he;
      unfold rn_value in he.
    - destruct (rn_addrs f sp g) as [[sp' g1]|w1] eqn:e1; [discriminate|].
      inversion he; subst. exact (rn_addrs_fail _ _ _ e1).
    - destruct (rn_env f e g) as [[e' g1]|w1] eqn:e1; [discriminate|].
      inversion he; subst. exact (rn_env_fail _ _ _ e1).
    - destruct (rn_env f e g) as [[e' g1]|w1] eqn:e1.
      + destruct (rn_addrs f sp g1) as [[sp' g2]|w2] eqn:e2; [discriminate|].
        inversion he; subst. exact (rn_addrs_fail _ _ _ e2).
      + inversion he; subst. exact (rn_env_fail _ _ _ e1).
    - destruct (rn_env f e g) as [[e' g1]|w1] eqn:e1.
      + destruct (rn_addrs f sp g1) as [[sp' g2]|w2] eqn:e2; [discriminate|].
        inversion he; subst. exact (rn_addrs_fail _ _ _ e2).
      + inversion he; subst. exact (rn_env_fail _ _ _ e1).
    - destruct (rn_addrs f sp g) as [[sp' g1]|w1] eqn:e1; [discriminate|].
      inversion he; subst. exact (rn_addrs_fail _ _ _ e1).
    - destruct (rn_env f e g) as [[e' g1]|w1] eqn:e1; [discriminate|].
      inversion he; subst. exact (rn_env_fail _ _ _ e1).
    - destruct (rn_env f e g) as [[e' g1]|w1] eqn:e1.
      + destruct (rn_addrs f sp g1) as [[sp' g2]|w2] eqn:e2; [discriminate|].
        inversion he; subst. exact (rn_addrs_fail _ _ _ e2).
      + inversion he; subst. exact (rn_env_fail _ _ _ e1).
  Qed.

  Lemma rn_cell_fail (cl : cbn_cell) (g : G) (w : cbn_why) : rn_cell f cl g = CFail w -> P w.
  Proof.
    destruct cl as [vals n o c|v| |b]; intros he; unfold rn_cell in he.
    - destruct (rn_slots f vals g) as [[vs' g1]|w1] eqn:e1; [discriminate|].
      inversion he; subst. exact (rn_slots_fail _ _ _ e1).
    - destruct (rn_value f v g) as [[v' g1]|w1] eqn:e1; [discriminate|].
      inversion he; subst. exact (rn_value_fail _ _ _ e1).
    - discriminate.
    - destruct (f b g) as [[b' g1]|w1] eqn:e1; [discriminate|].
      inversion he; subst. exact (hf _ _ _ e1).
  Qed.

  Lemma rn_root_fail (r : root) (g : G) (w : cbn_why) : rn_root f r g = CFail w -> P w.
  Proof.
    destruct r as [a|x|e|v|l|l|cl]; intros he; unfold rn_root in he.
    - destruct (f a g) as [[b g1]|w1] eqn:e1; [discriminate|].
      inversion he; subst. exact (hf _ _ _ e1).
    - destruct (rn_slot f x g) as [[x' g1]|w1] eqn:e1; [discriminate|].
      inversion he; subst. exact (rn_slot_fail _ _ _ e1).
    - destruct (rn_env f e g) as [[e' g1]|w1] eqn:e1; [discriminate|].
      inversion he; subst. exact (rn_env_fail _ _ _ e1).
    - destruct (rn_value f v g) as [[v' g1]|w1] eqn:e1; [discriminate|].
      inversion he; subst. exact (rn_value_fail _ _ _ e1).
    - destruct (rn_slots f l g) as [[l' g1]|w1] eqn:e1; [discriminate|].
      inversion he; subst. exact (rn_slots_fail _ _ _ e1).
    - destruct (rn_addrs f l g) as [[l' g1]|w1] eqn:e1; [discriminate|].
      inversion he; subst. exact (rn_addrs_fail _ _ _ e1).
    - destruct (rn_cell f cl g) as [[cl' g1]|w1] eqn:e1; [discriminate|].
      inversion he; subst. exact (rn_cell_fail _ _ _ e1).
  Qed.

  Lemma rn_roots_fail : forall (l : list root) (g : G) (w : cbn_why),
    rn_roots f l g = CFail w -> P w.
  Proof.
    induction l as [|r l ih]; intros g w he; simpl in he; [discriminate|].
    destruct (rn_root f r g) as [[r' g1]|w1] eqn:e1.
    - destruct (rn_roots f l g1) as [[l2 g2]|w2] eqn:e2; [discriminate|].
      inversion he; subst. exact (ih _ _ e2).
    - inversion he; subst. exact (rn_root_fail _ _ _ e1).
  Qed.

  Lemma rn_tree'_fail : forall (m : PTree.tree' haddr) (g : G) (w : cbn_why),
    rn_tree' f m g = CFail w -> P w.
  Proof.
    induction m as [r ihr|x|x r ihr|l ihl|l ihl r ihr|l ihl x|l ihl x r ihr];
      intros g w he; simpl in he.
    - destruct (rn_tree' f r g) as [[r' g1]|w1] eqn:e1; [discriminate|].
      inversion he; subst. exact (ihr _ _ e1).
    - destruct (f x g) as [[x' g1]|w1] eqn:e1; [discriminate|].
      inversion he; subst. exact (hf _ _ _ e1).
    - destruct (f x g) as [[x' g1]|w1] eqn:e1.
      + destruct (rn_tree' f r g1) as [[r' g2]|w2] eqn:e2; [discriminate|].
        inversion he; subst. exact (ihr _ _ e2).
      + inversion he; subst. exact (hf _ _ _ e1).
    - destruct (rn_tree' f l g) as [[l' g1]|w1] eqn:e1; [discriminate|].
      inversion he; subst. exact (ihl _ _ e1).
    - destruct (rn_tree' f l g) as [[l' g1]|w1] eqn:e1.
      + destruct (rn_tree' f r g1) as [[r' g2]|w2] eqn:e2; [discriminate|].
        inversion he; subst. exact (ihr _ _ e2).
      + inversion he; subst. exact (ihl _ _ e1).
    - destruct (rn_tree' f l g) as [[l' g1]|w1] eqn:e1.
      + destruct (f x g1) as [[x' g2]|w2] eqn:e2; [discriminate|].
        inversion he; subst. exact (hf _ _ _ e2).
      + inversion he; subst. exact (ihl _ _ e1).
    - destruct (rn_tree' f l g) as [[l' g1]|w1] eqn:e1.
      + destruct (f x g1) as [[x' g2]|w2] eqn:e2.
        * destruct (rn_tree' f r g2) as [[r' g3]|w3] eqn:e3; [discriminate|].
          inversion he; subst. exact (ihr _ _ e3).
        * inversion he; subst. exact (hf _ _ _ e2).
      + inversion he; subst. exact (ihl _ _ e1).
  Qed.

  Lemma rn_ptree_fail (m : PTree.t haddr) (g : G) (w : cbn_why) :
    rn_ptree f m g = CFail w -> P w.
  Proof.
    destruct m as [|m]; intros he; unfold rn_ptree in he; [discriminate|].
    destruct (rn_tree' f m g) as [[m' g1]|w1] eqn:e1; [discriminate|].
    inversion he; subst. exact (rn_tree'_fail _ _ _ e1).
  Qed.

End RenameFail.

(** ** Failure is honest

  The collector answers [COk] with a state or [CFail] with a reason; there is no third
  answer and no wrong state, because [cbn_res] carries a state only in [COk]. The only two
  reasons it gives are an address that the old heap does not have ([WGcDangling]) and a walk
  that ran out of fuel ([WGcFuel]); the machine turns either into "don't know". *)

Lemma gc_copy_fail : forall (f : cbn_fuel) (a : haddr) (g : gc_state) (w : cbn_why),
  gc_copy f a g = CFail w -> w = WGcDangling \/ w = WGcFuel.
Proof.
  intros f. induction f as [|k ih]; intros a g w he.
  - rewrite gc_copy_FO in he.
    destruct (bh_get a g.(g_old)) as [cl|] eqn:ea; [destruct cl|];
      inversion he; subst; auto.
  - rewrite gc_copy_FS in he.
    destruct (bh_get a g.(g_old)) as [cl|] eqn:ea; [|inversion he; subst; auto].
    destruct cl as [vals n o c|v| |b].
    + destruct (rn_cell (gc_copy (k tt)) (CSusp vals n o c) g) as [[cl1 g1]|w1] eqn:e1.
      * destruct (bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old)) as [old|] eqn:e2;
          [discriminate|]. inversion he; subst; auto.
      * inversion he; subst.
        exact (rn_cell_fail (gc_copy (k tt)) _ (ih tt) _ _ _ e1).
    + destruct (rn_cell (gc_copy (k tt)) (CDone v) g) as [[cl1 g1]|w1] eqn:e1.
      * destruct (bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old)) as [old|] eqn:e2;
          [discriminate|]. inversion he; subst; auto.
      * inversion he; subst.
        exact (rn_cell_fail (gc_copy (k tt)) _ (ih tt) _ _ _ e1).
    + destruct (rn_cell (gc_copy (k tt)) CBusy g) as [[cl1 g1]|w1] eqn:e1.
      * destruct (bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old)) as [old|] eqn:e2;
          [discriminate|]. inversion he; subst; auto.
      * inversion he; subst.
        exact (rn_cell_fail (gc_copy (k tt)) _ (ih tt) _ _ _ e1).
    + discriminate.
Qed.

(** ** [collect], written once *)

Lemma collect_eq (rs : list root) (s : cbn_state) :
  collect rs s =
  match rn_ptree (gc_copy (fuel_of_pos s.(st_next) (fun _ => FO))) s.(st_gam)
          (mkGc s.(st_heap) (bh_holes s.(st_next)) s.(st_next)) with
  | COk (gm, g1) =>
    match rn_roots (gc_copy (fuel_of_pos s.(st_next) (fun _ => FO))) rs g1 with
    | COk (rs2, g2) =>
      COk (rs2, mkState g2.(g_heap) g2.(g_next)
             (gc_room (N.sub (Npos g2.(g_next)) (Npos s.(st_next)))) s.(st_steps) gm
             s.(st_memo))
    | CFail w => CFail w
    end
  | CFail w => CFail w
  end.
Proof. reflexivity. Qed.

Lemma collect_fail (rs : list root) (s : cbn_state) (w : cbn_why) :
  collect rs s = CFail w -> w = WGcDangling \/ w = WGcFuel.
Proof.
  rewrite collect_eq. intros he.
  destruct (rn_ptree (gc_copy (fuel_of_pos s.(st_next) (fun _ => FO))) s.(st_gam)
              (mkGc s.(st_heap) (bh_holes s.(st_next)) s.(st_next))) as [[gm g1]|w1] eqn:e1.
  - destruct (rn_roots (gc_copy (fuel_of_pos s.(st_next) (fun _ => FO))) rs g1)
      as [[rs2 g2]|w2] eqn:e2; [discriminate|].
    inversion he; subst.
    exact (rn_roots_fail _ _ (gc_copy_fail _) _ _ _ e2).
  - inversion he; subst.
    exact (rn_ptree_fail _ _ (gc_copy_fail _) _ _ _ e1).
Qed.

(** Every answer of [collect] is one of the two shapes, and a failure carries no state. *)
Lemma collect_answer (rs : list root) (s : cbn_state) :
  (exists rs' s', collect rs s = COk (rs', s'))
  \/ (exists w, collect rs s = CFail w /\ (w = WGcDangling \/ w = WGcFuel)).
Proof.
  destruct (collect rs s) as [[rs' s']|w] eqn:he.
  - left. exists rs', s'. reflexivity.
  - right. exists w. split; [reflexivity|exact (collect_fail _ _ _ he)].
Qed.

(** ** A collection preserves every reading and re-establishes the state invariant *)

Theorem collect_sound (nctx : nat) (rs : list root) (s : cbn_state) (rs' : list root)
    (s' : cbn_state) :
  heap_nofwd s.(st_heap) -> collect rs s = COk (rs', s') ->
  state_ok s.(st_next) s'
  /\ heap_nofwd s'.(st_heap)
  /\ (s.(st_next) <= s'.(st_next))%positive
  /\ s'.(st_steps) = s.(st_steps)
  /\ Forall2 (root_pres nctx s.(st_heap) s'.(st_heap)) rs rs'
  /\ (forall k a, PTree.get k s.(st_gam) = Some a ->
        exists a', PTree.get k s'.(st_gam) = Some a'
          /\ (forall lvl t, repr_addr nctx s.(st_heap) lvl a t ->
                            repr_addr nctx s'.(st_heap) lvl a' t)).
Proof.
  rewrite collect_eq. intros hnf he.
  destruct (rn_ptree (gc_copy (fuel_of_pos s.(st_next) (fun _ => FO))) s.(st_gam)
              (mkGc s.(st_heap) (bh_holes s.(st_next)) s.(st_next))) as [[gm g1]|w1] eqn:e1;
    [|discriminate].
  destruct (rn_roots (gc_copy (fuel_of_pos s.(st_next) (fun _ => FO))) rs g1)
    as [[rs2 g2]|w2] eqn:e2; [|discriminate].
  inversion he; subst; clear he.
  assert (hinv0 : gc_inv nctx s.(st_heap) s.(st_next)
                    (mkGc s.(st_heap) (bh_holes s.(st_next)) s.(st_next))).
  { constructor; cbn.
    - intros a cl hc _. exact hc.
    - intros a a' hc. destruct (hnf _ _ hc).
    - apply bh_ok_holes.
    - intros b cl hc. rewrite bh_get_holes in hc. discriminate.
    - intros b b' hc. rewrite bh_get_holes in hc. discriminate. }
  destruct (rn_ptree_ok nctx s.(st_heap) s.(st_next) _
              (gc_copy_ok nctx s.(st_heap) s.(st_next) _) _ _ _ _ hinv0 e1)
    as [hs1 [hgb hgr]].
  destruct (rn_roots_ok nctx s.(st_heap) s.(st_next) _
              (gc_copy_ok nctx s.(st_heap) s.(st_next) _) _ _ _ _
              (step_inv _ _ _ _ _ hs1) e2) as [hs2 [had2 hroots]].
  pose proof (step_inv _ _ _ _ _ hs2) as hinv2.
  split.
  { split; cbn.
    - exact (inv_heap _ _ _ _ hinv2).
    - intros a cl hc. exact (inv_cells _ _ _ _ hinv2 _ _ hc).
    - intros k a hk. destruct (hgb _ _ hk) as [u1 u2].
      split; [exact u1|exact (Pos.lt_le_trans _ _ _ u2 (step_next _ _ _ _ _ hs2))]. }
  split; [exact (inv_nofwd _ _ _ _ hinv2)|].
  split.
  { cbn. exact (Pos.le_trans _ _ _ (step_next _ _ _ _ _ hs1) (step_next _ _ _ _ _ hs2)). }
  split; [reflexivity|].
  split; [exact hroots|].
  intros k a hk. destruct (hgr _ _ hk) as [a' [ha' hrr]].
  exists a'. split; [exact ha'|].
  intros lvl t ht.
  exact (repr_addr_mono nctx _ _ (step_heap _ _ _ _ _ hs2) _ _ _ (hrr lvl t ht)).
Qed.

(** The new heap holds no forwarding pointer, so a second collection may run on it. *)
Corollary collect_nofwd (rs : list root) (s : cbn_state) (rs' : list root) (s' : cbn_state) :
  heap_nofwd s.(st_heap) -> collect rs s = COk (rs', s') -> heap_nofwd s'.(st_heap).
Proof. intros hnf he. exact (proj1 (proj2 (collect_sound 0 _ _ _ _ hnf he))). Qed.

(** [state_ok lo s] before, [state_ok onext s'] after, where [onext] is the old [st_next]:
  in particular no cell of the new heap names an address below it. *)
Corollary collect_state_ok (lo : positive) (rs : list root) (s : cbn_state) (rs' : list root)
    (s' : cbn_state) :
  state_ok lo s -> heap_nofwd s.(st_heap) -> collect rs s = COk (rs', s') ->
  state_ok s.(st_next) s'.
Proof. intros _ hnf he. exact (proj1 (collect_sound 0 _ _ _ _ hnf he)). Qed.

Corollary collect_cells_above (rs : list root) (s : cbn_state) (rs' : list root)
    (s' : cbn_state) (b : haddr) (cl : cbn_cell) :
  heap_nofwd s.(st_heap) -> collect rs s = COk (rs', s') ->
  bh_get b s'.(st_heap) = Some cl -> addrs_in s.(st_next) s'.(st_next) (ad_cell cl).
Proof.
  intros hnf he hb.
  exact (so_cells _ _ (proj1 (collect_sound 0 _ _ _ _ hnf he)) _ _ hb).
Qed.

(** ** The readings the caller holds, one shape at a time *)

Lemma collect_root_cons (nctx : nat) (r : root) (rs : list root) (s : cbn_state)
    (rs' : list root) (s' : cbn_state) :
  heap_nofwd s.(st_heap) -> collect (r :: rs) s = COk (rs', s') ->
  exists r' rs2, rs' = r' :: rs2 /\ root_pres nctx s.(st_heap) s'.(st_heap) r r'.
Proof.
  intros hnf he.
  destruct (collect_sound nctx _ _ _ _ hnf he) as [_ [_ [_ [_ [hfa _]]]]].
  inversion hfa; subst. do 2 eexists; split; [reflexivity|assumption].
Qed.

(** A value a caller holds across the collection stands, renamed, for the same term. *)
Corollary collect_value (nctx : nat) (v : cbn_value) (rs : list root) (s : cbn_state)
    (rs' : list root) (s' : cbn_state) (lvl : nat) (t : term) :
  heap_nofwd s.(st_heap) -> collect (RV v :: rs) s = COk (rs', s') ->
  repr_value nctx s.(st_heap) lvl v t ->
  exists v' rs2, rs' = RV v' :: rs2 /\ repr_value nctx s'.(st_heap) lvl v' t.
Proof.
  intros hnf he hv.
  destruct (collect_root_cons nctx _ _ _ _ _ hnf he) as [r' [rs2 [-> hp]]].
  destruct r'; cbn in hp; try contradiction.
  exists v0, rs2. split; [reflexivity|exact (hp lvl t hv)].
Qed.

Corollary collect_slot (nctx : nat) (x : cbn_slot) (rs : list root) (s : cbn_state)
    (rs' : list root) (s' : cbn_state) (lvl : nat) (t : term) :
  heap_nofwd s.(st_heap) -> collect (RSl x :: rs) s = COk (rs', s') ->
  repr_slot nctx s.(st_heap) lvl x t ->
  exists x' rs2, rs' = RSl x' :: rs2 /\ repr_slot nctx s'.(st_heap) lvl x' t.
Proof.
  intros hnf he hv.
  destruct (collect_root_cons nctx _ _ _ _ _ hnf he) as [r' [rs2 [-> hp]]].
  destruct r'; cbn in hp; try contradiction.
  exists x0, rs2. split; [reflexivity|exact (hp lvl t hv)].
Qed.

(** An environment stands for the same suspensions: the code and the offsets do not move. *)
Corollary collect_env (nctx : nat) (e : cbn_env) (rs : list root) (s : cbn_state)
    (rs' : list root) (s' : cbn_state) (lvl : nat) (tm u : term) :
  heap_nofwd s.(st_heap) -> collect (RE e :: rs) s = COk (rs', s') ->
  repr_susp nctx s.(st_heap) lvl e tm u ->
  exists e' rs2, rs' = RE e' :: rs2 /\ repr_susp nctx s'.(st_heap) lvl e' tm u.
Proof.
  intros hnf he hv.
  destruct (collect_root_cons nctx _ _ _ _ _ hnf he) as [r' [rs2 [-> hp]]].
  destruct r'; cbn in hp; try contradiction.
  exists e0, rs2. split; [reflexivity|exact (hp lvl tm u hv)].
Qed.

Corollary collect_cell (nctx : nat) (cl : cbn_cell) (rs : list root) (s : cbn_state)
    (rs' : list root) (s' : cbn_state) (lvl : nat) (t : term) :
  heap_nofwd s.(st_heap) -> collect (RC cl :: rs) s = COk (rs', s') ->
  repr_cell nctx s.(st_heap) lvl cl t ->
  exists cl' rs2, rs' = RC cl' :: rs2 /\ repr_cell nctx s'.(st_heap) lvl cl' t.
Proof.
  intros hnf he hv.
  destruct (collect_root_cons nctx _ _ _ _ _ hnf he) as [r' [rs2 [-> hp]]].
  destruct r'; cbn in hp; try contradiction.
  exists c, rs2. split; [reflexivity|exact (hp lvl t hv)].
Qed.

Corollary collect_addr (nctx : nat) (a : haddr) (rs : list root) (s : cbn_state)
    (rs' : list root) (s' : cbn_state) (lvl : nat) (t : term) :
  heap_nofwd s.(st_heap) -> collect (RA a :: rs) s = COk (rs', s') ->
  repr_addr nctx s.(st_heap) lvl a t ->
  exists a' rs2, rs' = RA a' :: rs2 /\ repr_addr nctx s'.(st_heap) lvl a' t.
Proof.
  intros hnf he hv.
  destruct (collect_root_cons nctx _ _ _ _ _ hnf he) as [r' [rs2 [-> hp]]].
  destruct r'; cbn in hp; try contradiction.
  exists a0, rs2. split; [reflexivity|exact (hp lvl t hv)].
Qed.

Corollary collect_slots (nctx : nat) (l : list cbn_slot) (rs : list root) (s : cbn_state)
    (rs' : list root) (s' : cbn_state) (lvl : nat) (ts : list term) :
  heap_nofwd s.(st_heap) -> collect (RSk l :: rs) s = COk (rs', s') ->
  repr_slots nctx s.(st_heap) lvl l ts ->
  exists l' rs2, rs' = RSk l' :: rs2 /\ repr_slots nctx s'.(st_heap) lvl l' ts.
Proof.
  intros hnf he hv.
  destruct (collect_root_cons nctx _ _ _ _ _ hnf he) as [r' [rs2 [-> hp]]].
  destruct r'; cbn in hp; try contradiction.
  exists l0, rs2. split; [reflexivity|exact (hp lvl ts hv)].
Qed.

Corollary collect_addrs (nctx : nat) (l : list haddr) (rs : list root) (s : cbn_state)
    (rs' : list root) (s' : cbn_state) (lvl : nat) (ts : list term) :
  heap_nofwd s.(st_heap) -> collect (RSp l :: rs) s = COk (rs', s') ->
  repr_addrs nctx s.(st_heap) lvl l ts ->
  exists l' rs2, rs' = RSp l' :: rs2 /\ repr_addrs nctx s'.(st_heap) lvl l' ts.
Proof.
  intros hnf he hv.
  destruct (collect_root_cons nctx _ _ _ _ _ hnf he) as [r' [rs2 [-> hp]]].
  destruct r'; cbn in hp; try contradiction.
  exists l0, rs2. split; [reflexivity|exact (hp lvl ts hv)].
Qed.

(** ** When the collector runs, and that it makes room

  [gc_due] asks for a collection at every allocation in stress mode, and otherwise when the
  room left is zero. [gc_room] is never zero, so the state a collection returns is not due
  again: outside stress mode a collection is always followed by at least one allocation. *)

Lemma gc_room_nonzero (live : N) : gc_room live <> 0%N.
Proof. unfold gc_room. destruct (N.max (N.double live) gc_min); discriminate. Qed.

Lemma gc_due_stress (s : cbn_state) : gc_due true s = true.
Proof. reflexivity. Qed.

Lemma gc_due_room (s : cbn_state) : gc_due false s = true <-> s.(st_room) = 0%N.
Proof.
  unfold gc_due. destruct s.(st_room) eqn:hr; cbn.
  - split; [intros _; reflexivity|intros _; reflexivity].
  - split; [discriminate|discriminate].
Qed.

Lemma collect_room (rs : list root) (s : cbn_state) (rs' : list root) (s' : cbn_state) :
  collect rs s = COk (rs', s') ->
  s'.(st_room) = gc_room (N.sub (Npos s'.(st_next)) (Npos s.(st_next))).
Proof.
  rewrite collect_eq. intros he.
  destruct (rn_ptree (gc_copy (fuel_of_pos s.(st_next) (fun _ => FO))) s.(st_gam)
              (mkGc s.(st_heap) (bh_holes s.(st_next)) s.(st_next))) as [[gm g1]|w1];
    [|discriminate].
  destruct (rn_roots (gc_copy (fuel_of_pos s.(st_next) (fun _ => FO))) rs g1)
    as [[rs2 g2]|w2]; [|discriminate].
  inversion he; subst. reflexivity.
Qed.

Lemma collect_not_due (stress : bool) (rs : list root) (s : cbn_state) (rs' : list root)
    (s' : cbn_state) : collect rs s = COk (rs', s') -> gc_due stress s' = stress.
Proof.
  intros he. unfold gc_due. rewrite (collect_room _ _ _ _ he). unfold gc_room.
  destruct (N.max (N.double (N.sub (Npos s'.(st_next)) (Npos s.(st_next)))) gc_min);
    cbn; destruct stress; reflexivity.
Qed.
