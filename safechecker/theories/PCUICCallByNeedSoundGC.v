(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require CanonicalTries.
From MetaRocq.Common Require Import config Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils.
From MetaRocq.SafeChecker Require Import PCUICCallByNeed PCUICCallByNeedSound.

Import CanonicalTries.

(** * The copying collector of the call-by-need fast path

  [collect] of [PCUICCallByNeed] copies every cell the roots and [st_gam] reach into a fresh
  heap whose addresses start at the old [st_next], leaves a forwarding pointer [CFwd] in the
  old heap, and renames the roots and [st_gam] with the map the copy built. [collect_sound]
  proves that the state invariant [state_ok] of [PCUICCallByNeedSound] holds again after a
  collection, with the old [st_next] as the new first address, and that the new heap holds no
  forwarding pointer. The collector's invariant [gc_inv] on the states of the walk, and the
  lemma [gc_copy_ok] that the walk keeps it, are also what [PCUICCallByNeedSoundEval] uses to
  prove that a collection keeps the ghost readings ([collect_ghost]).

  What the proof needs beyond [state_ok]: the heap handed to [collect] must hold no [CFwd]
  cell ([heap_nofwd]). [state_ok] does not say so, and it cannot be dropped: a stale [CFwd a]
  is returned unchanged by [gc_copy], so its [a] - an address of the old heap, below the new
  heap's first address - would be written into the new heap and [state_ok] would fail. The
  machine satisfies it, because [collect] is the only writer of [CFwd] and it throws the old
  heap away; the second conjunct of [collect_sound] re-establishes it, so repeated
  collections keep it.

  The walk of [gc_copy] is bounded by fuel ([st_next] units). A heap with a cycle through a
  cell that is not yet copied exhausts it and the collection fails with [WGcFuel]; every
  statement about a collection is therefore under the hypothesis that it returned [COk]. *)

(** ** Heaps without forwarding pointers *)

Definition cell_fwd (cl : cbn_cell) : option haddr :=
  match cl with CFwd a => Some a | _ => None end.

Definition heap_nofwd (Hp : bheap cbn_cell) : Prop :=
  forall a a', bh_get a Hp = Some (CFwd a') -> False.

Lemma addrs_in_app lo n l1 l2 :
  addrs_in lo n l1 -> addrs_in lo n l2 -> addrs_in lo n (l1 ++ l2).
Proof.
  unfold addrs_in. induction 1 as [|b l hb hl ih]; simpl; [trivial|].
  intros h2. constructor; [exact hb|exact (ih h2)].
Qed.

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
  Context (Hold : bheap cbn_cell) (onext : positive).

  (** ** The collector's invariant

    [Hold] is the heap the collection started from and [onext] the address the new heap
    starts at. A state [g] of the walk satisfies [gc_inv g] when

    - every cell of [g_old] that is not a forwarding pointer is the cell [Hold] had there;
    - every forwarding pointer names an address of the new heap;
    - the new heap was built by [bh_holes onext] and [bh_cons] (so the laws of
      [PCUICCallByNeed] apply to it), names no address outside itself, and holds no
      forwarding pointer of its own. *)
  Record gc_inv (g : gc_state) : Prop := mkGcInv {
    gi_keep : forall a cl, bh_get a g.(g_old) = Some cl -> cell_fwd cl = None ->
      bh_get a Hold = Some cl;
    gi_moved : forall a a', bh_get a g.(g_old) = Some (CFwd a') ->
      (onext <= ha_p a')%positive /\ (ha_p a' < g.(g_next))%positive;
    gi_heap : bh_ok onext g.(g_next) g.(g_heap);
    gi_cells : forall b cl, bh_get b g.(g_heap) = Some cl ->
      addrs_in onext g.(g_next) (ad_cell cl);
    gi_nofwd : heap_nofwd g.(g_heap) }.

  Lemma inv_keep g : gc_inv g -> forall a cl,
    bh_get a g.(g_old) = Some cl -> cell_fwd cl = None -> bh_get a Hold = Some cl.
  Proof. intros [h _ _ _ _]. exact h. Qed.

  Lemma inv_moved g : gc_inv g -> forall a a', bh_get a g.(g_old) = Some (CFwd a') ->
    (onext <= ha_p a')%positive /\ (ha_p a' < g.(g_next))%positive.
  Proof. intros [_ h _ _ _]. exact h. Qed.

  Lemma inv_heap g : gc_inv g -> bh_ok onext g.(g_next) g.(g_heap).
  Proof. intros [_ _ h _ _]. exact h. Qed.

  Lemma inv_cells g : gc_inv g -> forall b cl, bh_get b g.(g_heap) = Some cl ->
    addrs_in onext g.(g_next) (ad_cell cl).
  Proof. intros [_ _ _ h _]. exact h. Qed.

  Lemma inv_nofwd g : gc_inv g -> heap_nofwd g.(g_heap).
  Proof. intros [_ _ _ _ h]. exact h. Qed.

  (** A step of the walk: the invariant again, and a first free address that only moved
    up. *)
  Record gstep (g g' : gc_state) : Prop := mkGStep {
    gs_inv : gc_inv g';
    gs_next : (g.(g_next) <= g'.(g_next))%positive }.

  Lemma step_inv g g' : gstep g g' -> gc_inv g'.
  Proof. intros [h _]. exact h. Qed.

  Lemma step_next g g' : gstep g g' -> (g.(g_next) <= g'.(g_next))%positive.
  Proof. intros [_ h]. exact h. Qed.

  Lemma gstep_refl g : gc_inv g -> gstep g g.
  Proof. intros h. constructor; [exact h|apply Pos.le_refl]. Qed.

  Lemma gstep_trans g1 g2 g3 : gstep g1 g2 -> gstep g2 g3 -> gstep g1 g3.
  Proof.
    intros [_ n1] [i2 n2]. constructor; [exact i2|exact (Pos.le_trans _ _ _ n1 n2)].
  Qed.

  (** ** What the collector asks of the address map it threads through the renamings *)
  Definition cp_ok (cp : haddr -> gc_state -> cbn_res (haddr * gc_state)) : Prop :=
    forall a g a' g', gc_inv g -> cp a g = COk (a', g') ->
      gstep g g' /\ (onext <= ha_p a')%positive /\ (ha_p a' < g'.(g_next))%positive.

  (** ** The renamings under an address map that satisfies [cp_ok] *)

  Section Structural.
    Context (cp : haddr -> gc_state -> cbn_res (haddr * gc_state)) (hcp : cp_ok cp).

    Lemma rn_addrs_ok : forall (l : list haddr) (g : gc_state) (l' : list haddr) (g' : gc_state),
      gc_inv g -> rn_addrs cp l g = COk (l', g') ->
      gstep g g' /\ addrs_in onext g'.(g_next) l'.
    Proof.
      induction l as [|a l ih]; intros g l' g' hinv he; simpl in he.
      - inversion he; subst; clear he.
        split; [exact (gstep_refl _ hinv)|constructor].
      - destruct (cp a g) as [[b g1]|w] eqn:e1; [|discriminate].
        destruct (rn_addrs cp l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (hcp _ _ _ _ hinv e1) as [hs1 [hb1 hb2]].
        destruct (ih _ _ _ (step_inv _ _ hs1) e2) as [hs2 had2].
        split; [exact (gstep_trans _ _ _ hs1 hs2)|].
        constructor;
          [split; [exact hb1|exact (Pos.lt_le_trans _ _ _ hb2 (step_next _ _ hs2))]|exact had2].
    Qed.

    Lemma rn_slot_ok : forall (x : cbn_slot) (g : gc_state) (x' : cbn_slot) (g' : gc_state),
      gc_inv g -> rn_slot cp x g = COk (x', g') ->
      gstep g g' /\ addrs_in onext g'.(g_next) (ad_slot x').
    Proof.
      intros x. induction x as [a|vs n o c ihvs] using slot_ind'; intros g x' g' hinv he.
      - simpl in he. destruct (cp a g) as [[b g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (hcp _ _ _ _ hinv e1) as [hs1 [hb1 hb2]].
        split; [exact hs1|constructor; [split; assumption|constructor]].
      - rewrite rn_slot_SInl in he.
        destruct (rn_slots cp vs g) as [[vs' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        assert (hl : gstep g g' /\ addrs_in onext g'.(g_next) (ad_slots vs')).
        { revert g vs' g' hinv e1. induction ihvs as [|y vs hy hvs ihl];
            intros g vs' g1 hinv e1; simpl in e1.
          - inversion e1; subst; clear e1.
            split; [exact (gstep_refl _ hinv)|constructor].
          - destruct (rn_slot cp y g) as [[y' ga]|wa] eqn:ea; [|discriminate].
            destruct (rn_slots cp vs ga) as [[vs2 gb]|wb] eqn:eb; [|discriminate].
            inversion e1; subst; clear e1.
            destruct (hy _ _ _ hinv ea) as [hsa hada].
            destruct (ihl _ _ _ (step_inv _ _ hsa) eb) as [hsb hadb].
            split; [exact (gstep_trans _ _ _ hsa hsb)|].
            unfold ad_slots. simpl. apply addrs_in_app.
            + exact (addrs_in_grow _ _ _ _ (step_next _ _ hsb) hada).
            + exact hadb. }
        destruct hl as [hs had].
        split; [exact hs|exact had].
    Qed.

    Lemma rn_slots_ok : forall (l : list cbn_slot) (g : gc_state) (l' : list cbn_slot)
        (g' : gc_state),
      gc_inv g -> rn_slots cp l g = COk (l', g') ->
      gstep g g' /\ addrs_in onext g'.(g_next) (ad_slots l').
    Proof.
      induction l as [|y l ih]; intros g l' g' hinv he; simpl in he.
      - inversion he; subst; clear he.
        split; [exact (gstep_refl _ hinv)|constructor].
      - destruct (rn_slot cp y g) as [[y' g1]|w] eqn:e1; [|discriminate].
        destruct (rn_slots cp l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_slot_ok _ _ _ _ hinv e1) as [hs1 had1].
        destruct (ih _ _ _ (step_inv _ _ hs1) e2) as [hs2 had2].
        split; [exact (gstep_trans _ _ _ hs1 hs2)|].
        unfold ad_slots. simpl. apply addrs_in_app.
        + exact (addrs_in_grow _ _ _ _ (step_next _ _ hs2) had1).
        + exact had2.
    Qed.

    Lemma rn_env_ok (e : cbn_env) (g : gc_state) (e' : cbn_env) (g' : gc_state) :
      gc_inv g -> rn_env cp e g = COk (e', g') ->
      gstep g g' /\ addrs_in onext g'.(g_next) (ad_env e').
    Proof.
      destruct e as [vals n o]. intros hinv he.
      unfold rn_env in he. cbn [ev_vals ev_nvals ev_goff] in he.
      destruct (rn_slots cp vals g) as [[vs' g1]|w] eqn:e1; [|discriminate].
      inversion he; subst; clear he.
      destruct (rn_slots_ok _ _ _ _ hinv e1) as [hs had].
      split; [exact hs|exact had].
    Qed.

    Lemma rn_value_ok (v : cbn_value) (g : gc_state) (v' : cbn_value) (g' : gc_state) :
      gc_inv g -> rn_value cp v g = COk (v', g') ->
      gstep g g' /\ addrs_in onext g'.(g_next) (ad_value v').
    Proof.
      destruct v as [hd sp|e c|e c i sp|e c i sp|hd sp|e c|e c sp]; intros hinv he;
        unfold rn_value in he.
      - destruct (rn_addrs cp sp g) as [[sp' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_addrs_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - destruct (rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_env_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - destruct (rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        destruct (rn_addrs cp sp g1) as [[sp' g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_env_ok _ _ _ _ hinv e1) as [hs1 had1].
        destruct (rn_addrs_ok _ _ _ _ (step_inv _ _ hs1) e2) as [hs2 had2].
        split; [exact (gstep_trans _ _ _ hs1 hs2)|].
        apply addrs_in_app;
          [exact (addrs_in_grow _ _ _ _ (step_next _ _ hs2) had1)|exact had2].
      - destruct (rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        destruct (rn_addrs cp sp g1) as [[sp' g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_env_ok _ _ _ _ hinv e1) as [hs1 had1].
        destruct (rn_addrs_ok _ _ _ _ (step_inv _ _ hs1) e2) as [hs2 had2].
        split; [exact (gstep_trans _ _ _ hs1 hs2)|].
        apply addrs_in_app;
          [exact (addrs_in_grow _ _ _ _ (step_next _ _ hs2) had1)|exact had2].
      - destruct (rn_addrs cp sp g) as [[sp' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_addrs_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - destruct (rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_env_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - destruct (rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        destruct (rn_addrs cp sp g1) as [[sp' g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_env_ok _ _ _ _ hinv e1) as [hs1 had1].
        destruct (rn_addrs_ok _ _ _ _ (step_inv _ _ hs1) e2) as [hs2 had2].
        split; [exact (gstep_trans _ _ _ hs1 hs2)|].
        apply addrs_in_app;
          [exact (addrs_in_grow _ _ _ _ (step_next _ _ hs2) had1)|exact had2].
    Qed.

    Lemma rn_cell_ok (cl : cbn_cell) (g : gc_state) (cl' : cbn_cell) (g' : gc_state) :
      gc_inv g -> rn_cell cp cl g = COk (cl', g') ->
      gstep g g' /\ addrs_in onext g'.(g_next) (ad_cell cl').
    Proof.
      destruct cl as [vals n o c|v| |b]; intros hinv he; unfold rn_cell in he.
      - destruct (rn_slots cp vals g) as [[vs' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_slots_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - destruct (rn_value cp v g) as [[v' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_value_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - inversion he; subst; clear he.
        split; [exact (gstep_refl _ hinv)|constructor].
      - destruct (cp b g) as [[b' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (hcp _ _ _ _ hinv e1) as [hs [hb1 hb2]].
        split; [exact hs|constructor; [split; assumption|constructor]].
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
      gstep g g' /\ addrs_in onext g'.(g_next) (ad_root r').
    Proof.
      destruct r as [a|x|e|v|l|l|cl]; intros hinv he; unfold rn_root in he.
      - destruct (cp a g) as [[b g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (hcp _ _ _ _ hinv e1) as [hs [hb1 hb2]].
        split; [exact hs|constructor; [split; assumption|constructor]].
      - destruct (rn_slot cp x g) as [[x' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_slot_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - destruct (rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_env_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - destruct (rn_value cp v g) as [[v' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_value_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - destruct (rn_slots cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_slots_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - destruct (rn_addrs cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_addrs_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - destruct (rn_cell cp cl g) as [[cl' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_cell_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
    Qed.

    Lemma rn_roots_ok : forall (l : list root) (g : gc_state) (l' : list root) (g' : gc_state),
      gc_inv g -> rn_roots cp l g = COk (l', g') ->
      gstep g g' /\ addrs_in onext g'.(g_next) (ad_roots l').
    Proof.
      induction l as [|r l ih]; intros g l' g' hinv he; simpl in he.
      - inversion he; subst; clear he.
        split; [exact (gstep_refl _ hinv)|constructor].
      - destruct (rn_root cp r g) as [[r' g1]|w] eqn:e1; [|discriminate].
        destruct (rn_roots cp l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_root_ok _ _ _ _ hinv e1) as [hs1 had1].
        destruct (ih _ _ _ (step_inv _ _ hs1) e2) as [hs2 had2].
        split; [exact (gstep_trans _ _ _ hs1 hs2)|].
        unfold ad_roots. simpl. apply addrs_in_app.
        + exact (addrs_in_grow _ _ _ _ (step_next _ _ hs2) had1).
        + exact had2.
    Qed.

    (** *** The context map [st_gam] *)

    Lemma rn_tree'_ok : forall (m : PTree.tree' haddr) (g : gc_state)
        (m' : PTree.tree' haddr) (g' : gc_state),
      gc_inv g -> rn_tree' cp m g = COk (m', g') ->
      gstep g g'
      /\ (forall p a', PTree.get' p m' = Some a' ->
            (onext <= ha_p a')%positive /\ (ha_p a' < g'.(g_next))%positive).
    Proof.
      induction m as [r ihr|x|x r ihr|l ihl|l ihl r ihr|l ihl x|l ihl x r ihr];
        intros g m' g' hinv he; simpl in he.
      - (* Node001 *)
        destruct (rn_tree' cp r g) as [[r' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (ihr _ _ _ hinv e1) as [hs1 hb1].
        split; [exact hs1|].
        intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
        exact (hb1 _ _ hb).
      - (* Node010 *)
        destruct (cp x g) as [[x' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (hcp _ _ _ _ hinv e1) as [hs1 [hx1 hx2]].
        split; [exact hs1|].
        intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
        inversion hb; subst. split; assumption.
      - (* Node011 *)
        destruct (cp x g) as [[x' g1]|w] eqn:e1; [|discriminate].
        destruct (rn_tree' cp r g1) as [[r' g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (hcp _ _ _ _ hinv e1) as [hs1 [hx1 hx2]].
        destruct (ihr _ _ _ (step_inv _ _ hs1) e2) as [hs2 hb2].
        split; [exact (gstep_trans _ _ _ hs1 hs2)|].
        intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
        + exact (hb2 _ _ hb).
        + inversion hb; subst.
          split; [exact hx1|exact (Pos.lt_le_trans _ _ _ hx2 (step_next _ _ hs2))].
      - (* Node100 *)
        destruct (rn_tree' cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (ihl _ _ _ hinv e1) as [hs1 hb1].
        split; [exact hs1|].
        intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
        exact (hb1 _ _ hb).
      - (* Node101 *)
        destruct (rn_tree' cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
        destruct (rn_tree' cp r g1) as [[r' g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (ihl _ _ _ hinv e1) as [hs1 hb1].
        destruct (ihr _ _ _ (step_inv _ _ hs1) e2) as [hs2 hb2].
        split; [exact (gstep_trans _ _ _ hs1 hs2)|].
        intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
        + exact (hb2 _ _ hb).
        + destruct (hb1 _ _ hb) as [u1 u2].
          split; [exact u1|exact (Pos.lt_le_trans _ _ _ u2 (step_next _ _ hs2))].
      - (* Node110 *)
        destruct (rn_tree' cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
        destruct (cp x g1) as [[x' g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (ihl _ _ _ hinv e1) as [hs1 hb1].
        destruct (hcp _ _ _ _ (step_inv _ _ hs1) e2) as [hs2 [hx1 hx2]].
        split; [exact (gstep_trans _ _ _ hs1 hs2)|].
        intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
        + destruct (hb1 _ _ hb) as [u1 u2].
          split; [exact u1|exact (Pos.lt_le_trans _ _ _ u2 (step_next _ _ hs2))].
        + inversion hb; subst. split; assumption.
      - (* Node111 *)
        destruct (rn_tree' cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
        destruct (cp x g1) as [[x' g2]|w] eqn:e2; [|discriminate].
        destruct (rn_tree' cp r g2) as [[r' g3]|w] eqn:e3; [|discriminate].
        inversion he; subst; clear he.
        destruct (ihl _ _ _ hinv e1) as [hs1 hb1].
        destruct (hcp _ _ _ _ (step_inv _ _ hs1) e2) as [hs2 [hx1 hx2]].
        destruct (ihr _ _ _ (step_inv _ _ hs2) e3) as [hs3 hb3].
        split; [exact (gstep_trans _ _ _ hs1 (gstep_trans _ _ _ hs2 hs3))|].
        intros p b hb. destruct p as [q|q|]; simpl in hb.
        + exact (hb3 _ _ hb).
        + destruct (hb1 _ _ hb) as [u1 u2]. split; [exact u1|].
          exact (Pos.lt_le_trans _ _ _ u2
                   (Pos.le_trans _ _ _ (step_next _ _ hs2) (step_next _ _ hs3))).
        + inversion hb; subst.
          split; [exact hx1|exact (Pos.lt_le_trans _ _ _ hx2 (step_next _ _ hs3))].
    Qed.

    Lemma rn_ptree_ok (m : PTree.t haddr) (g : gc_state) (m' : PTree.t haddr) (g' : gc_state) :
      gc_inv g -> rn_ptree cp m g = COk (m', g') ->
      gstep g g'
      /\ (forall p a', PTree.get p m' = Some a' ->
            (onext <= ha_p a')%positive /\ (ha_p a' < g'.(g_next))%positive).
    Proof.
      destruct m as [|m]; intros hinv he; unfold rn_ptree in he.
      - inversion he; subst; clear he.
        split; [exact (gstep_refl _ hinv)|].
        intros p b hb; discriminate.
      - destruct (rn_tree' cp m g) as [[m2 g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_tree'_ok _ _ _ _ hinv e1) as [hs hb].
        split; [exact hs|].
        intros p b hbb. exact (hb _ _ hbb).
    Qed.

    (** *** One copied cell

      The cell is read from the old heap, its children are renamed, the copy is pushed onto
      the new heap at [g_next] and the old cell is overwritten with [CFwd] of that address. *)
    Lemma gc_copy_write (a : haddr) (g : gc_state) (cl cl1 : cbn_cell) (g1 : gc_state)
        (old : bheap cbn_cell) :
      gc_inv g ->
      cell_fwd cl = None ->
      rn_cell cp cl g = COk (cl1, g1) ->
      bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old) = Some old ->
      gstep g (mkGc old (bh_cons cl1 g1.(g_heap)) (Pos.succ g1.(g_next)))
      /\ (onext <= g1.(g_next))%positive
      /\ (g1.(g_next) < Pos.succ g1.(g_next))%positive.
    Proof.
      intros hinv hf e1 e2.
      destruct (rn_cell_ok _ _ _ _ hinv e1) as [hs1 had1].
      pose proof (step_inv _ _ hs1) as hinv1.
      pose proof (inv_heap _ hinv1) as hok1.
      pose proof (bh_ok_le _ _ _ hok1) as hlo1.
      pose proof (rn_cell_nofwd _ _ _ _ hf e1) as hf1.
      assert (hinv2 : gc_inv (mkGc old (bh_cons cl1 g1.(g_heap)) (Pos.succ g1.(g_next)))).
      { constructor; cbn.
        - intros b clb hb hfb. destruct (haddr_dec b a) as [->|hne].
          + rewrite (bh_get_upd_same _ _ _ _ e2) in hb.
            inversion hb; subst. discriminate.
          + rewrite (bh_get_upd_other _ _ _ _ _ e2 hne) in hb.
            exact (inv_keep _ hinv1 _ _ hb hfb).
        - intros b b' hb. destruct (haddr_dec b a) as [->|hne].
          + rewrite (bh_get_upd_same _ _ _ _ e2) in hb. inversion hb; subst.
            split; [exact hlo1|apply Pos.lt_succ_diag_r].
          + rewrite (bh_get_upd_other _ _ _ _ _ e2 hne) in hb.
            destruct (inv_moved _ hinv1 _ _ hb) as [u1 u2].
            split; [exact u1|exact (Pos.lt_trans _ _ _ u2 (Pos.lt_succ_diag_r _))].
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
        + exact (Pos.le_trans _ _ _ (step_next _ _ hs1)
                   (Pos.lt_le_incl _ _ (Pos.lt_succ_diag_r _))).
      - split; [exact hlo1|apply Pos.lt_succ_diag_r].
    Qed.

  End Structural.

  (** ** The walk of [gc_copy] keeps the invariant

    Every address the collector returns is an address of the new heap, at or above
    [onext]. *)
  Lemma gc_copy_ok : forall (f : cbn_fuel), cp_ok (gc_copy f).
  Proof.
    intros f. induction f as [|k ih]; intros a g a' g' hinv he.
    - rewrite gc_copy_FO in he.
      destruct (bh_get a g.(g_old)) as [cl|] eqn:ea; [|discriminate].
      destruct cl as [vals n o c|v| |b]; try discriminate.
      inversion he; subst; clear he.
      destruct (inv_moved _ hinv _ _ ea) as [hb1 hb2].
      split; [exact (gstep_refl _ hinv)|]. split; assumption.
    - rewrite gc_copy_FS in he.
      destruct (bh_get a g.(g_old)) as [cl|] eqn:ea; [|discriminate].
      destruct cl as [vals n o c|v| |b].
      + destruct (rn_cell (gc_copy (k tt)) (CSusp vals n o c) g) as [[cl1 g1]|w] eqn:e1;
          [|discriminate].
        destruct (bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old)) as [old|] eqn:e2;
          [|discriminate].
        inversion he; subst; clear he.
        exact (gc_copy_write _ (ih tt) a g (CSusp vals n o c) _ _ _ hinv eq_refl e1 e2).
      + destruct (rn_cell (gc_copy (k tt)) (CDone v) g) as [[cl1 g1]|w] eqn:e1;
          [|discriminate].
        destruct (bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old)) as [old|] eqn:e2;
          [|discriminate].
        inversion he; subst; clear he.
        exact (gc_copy_write _ (ih tt) a g (CDone v) _ _ _ hinv eq_refl e1 e2).
      + destruct (rn_cell (gc_copy (k tt)) CBusy g) as [[cl1 g1]|w] eqn:e1; [|discriminate].
        destruct (bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old)) as [old|] eqn:e2;
          [|discriminate].
        inversion he; subst; clear he.
        exact (gc_copy_write _ (ih tt) a g CBusy _ _ _ hinv eq_refl e1 e2).
      + inversion he; subst; clear he.
        destruct (inv_moved _ hinv _ _ ea) as [hb1 hb2].
        split; [exact (gstep_refl _ hinv)|]. split; assumption.
  Qed.

End Collector.

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

(** ** A collection re-establishes the state invariant *)

Theorem collect_sound (rs : list root) (s : cbn_state) (rs' : list root) (s' : cbn_state) :
  heap_nofwd s.(st_heap) -> collect rs s = COk (rs', s') ->
  state_ok s.(st_next) s'
  /\ heap_nofwd s'.(st_heap)
  /\ (s.(st_next) <= s'.(st_next))%positive
  /\ s'.(st_steps) = s.(st_steps).
Proof.
  rewrite collect_eq. intros hnf he.
  destruct (rn_ptree (gc_copy (fuel_of_pos s.(st_next) (fun _ => FO))) s.(st_gam)
              (mkGc s.(st_heap) (bh_holes s.(st_next)) s.(st_next))) as [[gm g1]|w1] eqn:e1;
    [|discriminate].
  destruct (rn_roots (gc_copy (fuel_of_pos s.(st_next) (fun _ => FO))) rs g1)
    as [[rs2 g2]|w2] eqn:e2; [|discriminate].
  inversion he; subst; clear he.
  assert (hinv0 : gc_inv s.(st_heap) s.(st_next)
                    (mkGc s.(st_heap) (bh_holes s.(st_next)) s.(st_next))).
  { constructor; cbn.
    - intros a cl hc _. exact hc.
    - intros a a' hc. destruct (hnf _ _ hc).
    - apply bh_ok_holes.
    - intros b cl hc. rewrite bh_get_holes in hc. discriminate.
    - intros b b' hc. rewrite bh_get_holes in hc. discriminate. }
  destruct (rn_ptree_ok s.(st_heap) s.(st_next) _
              (gc_copy_ok s.(st_heap) s.(st_next) _) _ _ _ _ hinv0 e1)
    as [hs1 hgb].
  destruct (rn_roots_ok s.(st_heap) s.(st_next) _
              (gc_copy_ok s.(st_heap) s.(st_next) _) _ _ _ _
              (step_inv _ _ _ _ hs1) e2) as [hs2 _].
  pose proof (step_inv _ _ _ _ hs2) as hinv2.
  split.
  { split; cbn.
    - exact (inv_heap _ _ _ hinv2).
    - intros a cl hc. exact (inv_cells _ _ _ hinv2 _ _ hc).
    - intros k a hk. destruct (hgb _ _ hk) as [u1 u2].
      split; [exact u1|exact (Pos.lt_le_trans _ _ _ u2 (step_next _ _ _ _ hs2))]. }
  split; [exact (inv_nofwd _ _ _ hinv2)|].
  split.
  { cbn. exact (Pos.le_trans _ _ _ (step_next _ _ _ _ hs1) (step_next _ _ _ _ hs2)). }
  reflexivity.
Qed.
