(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require CanonicalTries.
From MetaRocq.Common Require Import config Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils.
From MetaRocq.SafeChecker Require Import PCUICCallByNeed PCUICCallByNeedSound.

Import CanonicalTries.

(** * The copying collector of the call-by-need fast path

  [cbn_collect] of [PCUICCallByNeed] copies every cell the roots and [cbn_st_gam] reach into a fresh
  heap whose addresses start at the old [cbn_st_next], leaves a forwarding pointer [CbnCFwd] in the
  old heap, and renames the roots and [cbn_st_gam] with the map the copy built. [cbn_collect_sound]
  proves that the state invariant [cbn_state_ok] of [PCUICCallByNeedSound] holds again after a
  collection, with the old [cbn_st_next] as the new first address, and that the new heap holds no
  forwarding pointer. The collector's invariant [cbn_gc_inv] on the states of the walk, and the
  lemma [cbn_gc_copy_ok] that the walk keeps it, are also what [PCUICCallByNeedSoundEval] uses to
  prove that a collection keeps the ghost readings ([cbn_collect_ghost]).

  What the proof needs beyond [cbn_state_ok]: the heap handed to [cbn_collect] must hold no
  [CbnCFwd] cell ([cbn_heap_nofwd]). [cbn_state_ok] does not say so, and it cannot be dropped: a
  stale [CbnCFwd a] is returned unchanged by [cbn_gc_copy], so its [a] - an address of the old heap,
  below the new heap's first address - would be written into the new heap and [cbn_state_ok] would
  fail. The machine satisfies it, because [cbn_collect] is the only writer of [CbnCFwd] and it
  throws the old heap away; the second conjunct of [cbn_collect_sound] re-establishes it, so
  repeated collections keep it.

  The walk of [cbn_gc_copy] is bounded by fuel ([cbn_st_next] units). A heap with a cycle through a
  cell that is not yet copied exhausts it and the collection fails with [CbnWGcFuel]; every
  statement about a collection is therefore under the hypothesis that it returned [CbnCOk]. *)

(** ** Heaps without forwarding pointers *)

Definition cbn_cell_fwd (cl : cbn_cell) : option cbn_haddr :=
  match cl with CbnCFwd a => Some a | _ => None end.

Definition cbn_heap_nofwd (Hp : cbn_bheap cbn_cell) : Prop :=
  forall a a', cbn_bh_get a Hp = Some (CbnCFwd a') -> False.

Lemma cbn_addrs_in_app lo n l1 l2 :
  cbn_addrs_in lo n l1 -> cbn_addrs_in lo n l2 -> cbn_addrs_in lo n (l1 ++ l2).
Proof.
  unfold cbn_addrs_in. induction 1 as [|b l hb hl ih]; simpl; [trivial|].
  intros h2. constructor; [exact hb|exact (ih h2)].
Qed.

(** ** The two equations of [cbn_gc_copy]

  [cbn_gc_copy] is a fixpoint on its fuel; these are its body, written once, so that no proof
  below depends on how [simpl] unfolds it. *)

Lemma cbn_gc_copy_FO (a : cbn_haddr) (g : cbn_gc_state) :
  cbn_gc_copy CbnFO a g =
  match cbn_bh_get a g.(cbn_g_old) with
  | None => CbnCFail CbnWGcDangling
  | Some (CbnCFwd a') => CbnCOk (a', g)
  | Some _ => CbnCFail CbnWGcFuel
  end.
Proof. reflexivity. Qed.

Lemma cbn_gc_copy_FS (k : unit -> cbn_fuel) (a : cbn_haddr) (g : cbn_gc_state) :
  cbn_gc_copy (CbnFS k) a g =
  match cbn_bh_get a g.(cbn_g_old) with
  | None => CbnCFail CbnWGcDangling
  | Some (CbnCFwd a') => CbnCOk (a', g)
  | Some cl =>
    match cbn_rn_cell (cbn_gc_copy (k tt)) cl g with
    | CbnCOk (cl1, g1) =>
      match cbn_bh_upd a (CbnCFwd (CbnHAddr g1.(cbn_g_next))) g1.(cbn_g_old) with
      | Some old =>
        CbnCOk (CbnHAddr g1.(cbn_g_next),
          cbn_mkGc old (cbn_bh_cons cl1 g1.(cbn_g_heap)) (Pos.succ g1.(cbn_g_next)))
      | None => CbnCFail CbnWGcDangling
      end
    | CbnCFail w => CbnCFail w
    end
  end.
Proof. reflexivity. Qed.

Section Collector.
  Context (Hold : cbn_bheap cbn_cell) (onext : positive).

  (** ** The collector's invariant

    [Hold] is the heap the collection started from and [onext] the address the new heap
    starts at. A state [g] of the walk satisfies [cbn_gc_inv g] when

    - every cell of [cbn_g_old] that is not a forwarding pointer is the cell [Hold] had there;
    - every forwarding pointer names an address of the new heap;
    - the new heap was built by [cbn_bh_holes onext] and [cbn_bh_cons] (so the laws of
      [PCUICCallByNeed] apply to it), names no address outside itself, and holds no
      forwarding pointer of its own. *)
  Record cbn_gc_inv (g : cbn_gc_state) : Prop := cbn_mkGcInv {
    cbn_gi_keep : forall a cl, cbn_bh_get a g.(cbn_g_old) = Some cl -> cbn_cell_fwd cl = None ->
      cbn_bh_get a Hold = Some cl;
    cbn_gi_moved : forall a a', cbn_bh_get a g.(cbn_g_old) = Some (CbnCFwd a') ->
      (onext <= cbn_ha_p a')%positive /\ (cbn_ha_p a' < g.(cbn_g_next))%positive;
    cbn_gi_heap : cbn_bh_ok onext g.(cbn_g_next) g.(cbn_g_heap);
    cbn_gi_cells : forall b cl, cbn_bh_get b g.(cbn_g_heap) = Some cl ->
      cbn_addrs_in onext g.(cbn_g_next) (cbn_ad_cell cl);
    cbn_gi_nofwd : cbn_heap_nofwd g.(cbn_g_heap) }.

  Lemma cbn_inv_keep g : cbn_gc_inv g -> forall a cl,
    cbn_bh_get a g.(cbn_g_old) = Some cl -> cbn_cell_fwd cl = None -> cbn_bh_get a Hold = Some cl.
  Proof. intros [h _ _ _ _]. exact h. Qed.

  Lemma cbn_inv_moved g : cbn_gc_inv g -> forall a a',
    cbn_bh_get a g.(cbn_g_old) = Some (CbnCFwd a') ->
    (onext <= cbn_ha_p a')%positive /\ (cbn_ha_p a' < g.(cbn_g_next))%positive.
  Proof. intros [_ h _ _ _]. exact h. Qed.

  Lemma cbn_inv_heap g : cbn_gc_inv g -> cbn_bh_ok onext g.(cbn_g_next) g.(cbn_g_heap).
  Proof. intros [_ _ h _ _]. exact h. Qed.

  Lemma cbn_inv_cells g : cbn_gc_inv g -> forall b cl, cbn_bh_get b g.(cbn_g_heap) = Some cl ->
    cbn_addrs_in onext g.(cbn_g_next) (cbn_ad_cell cl).
  Proof. intros [_ _ _ h _]. exact h. Qed.

  Lemma cbn_inv_nofwd g : cbn_gc_inv g -> cbn_heap_nofwd g.(cbn_g_heap).
  Proof. intros [_ _ _ _ h]. exact h. Qed.

  (** A step of the walk: the invariant again, and a first free address that only moved
    up. *)
  Record cbn_gstep (g g' : cbn_gc_state) : Prop := cbn_mkGStep {
    cbn_gs_inv : cbn_gc_inv g';
    cbn_gs_next : (g.(cbn_g_next) <= g'.(cbn_g_next))%positive }.

  Lemma cbn_step_inv g g' : cbn_gstep g g' -> cbn_gc_inv g'.
  Proof. intros [h _]. exact h. Qed.

  Lemma cbn_step_next g g' : cbn_gstep g g' -> (g.(cbn_g_next) <= g'.(cbn_g_next))%positive.
  Proof. intros [_ h]. exact h. Qed.

  Lemma cbn_gstep_refl g : cbn_gc_inv g -> cbn_gstep g g.
  Proof. intros h. constructor; [exact h|apply Pos.le_refl]. Qed.

  Lemma cbn_gstep_trans g1 g2 g3 : cbn_gstep g1 g2 -> cbn_gstep g2 g3 -> cbn_gstep g1 g3.
  Proof.
    intros [_ n1] [i2 n2]. constructor; [exact i2|exact (Pos.le_trans _ _ _ n1 n2)].
  Qed.

  (** ** What the collector asks of the address map it threads through the renamings *)
  Definition cbn_cp_ok (cp : cbn_haddr -> cbn_gc_state -> cbn_res (cbn_haddr * cbn_gc_state)) : Prop
    :=
    forall a g a' g', cbn_gc_inv g -> cp a g = CbnCOk (a', g') ->
      cbn_gstep g g' /\ (onext <= cbn_ha_p a')%positive /\ (cbn_ha_p a' < g'.(cbn_g_next))%positive.

  (** ** The renamings under an address map that satisfies [cbn_cp_ok] *)

  Section Structural.
    Context (cp : cbn_haddr -> cbn_gc_state -> cbn_res (cbn_haddr * cbn_gc_state))
      (hcp : cbn_cp_ok cp).

    Lemma cbn_rn_addrs_ok : forall (l : list cbn_haddr) (g : cbn_gc_state) (l' : list cbn_haddr)
      (g' : cbn_gc_state),
      cbn_gc_inv g -> cbn_rn_addrs cp l g = CbnCOk (l', g') ->
      cbn_gstep g g' /\ cbn_addrs_in onext g'.(cbn_g_next) l'.
    Proof.
      induction l as [|a l ih]; intros g l' g' hinv he; simpl in he.
      - inversion he; subst; clear he.
        split; [exact (cbn_gstep_refl _ hinv)|constructor].
      - destruct (cp a g) as [[b g1]|w] eqn:e1; [|discriminate].
        destruct (cbn_rn_addrs cp l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (hcp _ _ _ _ hinv e1) as [hs1 [hb1 hb2]].
        destruct (ih _ _ _ (cbn_step_inv _ _ hs1) e2) as [hs2 had2].
        split; [exact (cbn_gstep_trans _ _ _ hs1 hs2)|].
        constructor;
          [split; [exact hb1|exact (Pos.lt_le_trans _ _ _ hb2 (cbn_step_next _ _ hs2))]|exact had2].
    Qed.

    Lemma cbn_rn_slot_ok : forall (x : cbn_slot) (g : cbn_gc_state) (x' : cbn_slot)
      (g' : cbn_gc_state),
      cbn_gc_inv g -> cbn_rn_slot cp x g = CbnCOk (x', g') ->
      cbn_gstep g g' /\ cbn_addrs_in onext g'.(cbn_g_next) (cbn_ad_slot x').
    Proof.
      intros x. induction x as [a|vs n o c ihvs] using cbn_slot_ind'; intros g x' g' hinv he.
      - simpl in he. destruct (cp a g) as [[b g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (hcp _ _ _ _ hinv e1) as [hs1 [hb1 hb2]].
        split; [exact hs1|constructor; [split; assumption|constructor]].
      - rewrite cbn_rn_slot_SInl in he.
        destruct (cbn_rn_slots cp vs g) as [[vs' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        assert (hl : cbn_gstep g g' /\ cbn_addrs_in onext g'.(cbn_g_next) (cbn_ad_slots vs')).
        { revert g vs' g' hinv e1. induction ihvs as [|y vs hy hvs ihl];
            intros g vs' g1 hinv e1; simpl in e1.
          - inversion e1; subst; clear e1.
            split; [exact (cbn_gstep_refl _ hinv)|constructor].
          - destruct (cbn_rn_slot cp y g) as [[y' ga]|wa] eqn:ea; [|discriminate].
            destruct (cbn_rn_slots cp vs ga) as [[vs2 gb]|wb] eqn:eb; [|discriminate].
            inversion e1; subst; clear e1.
            destruct (hy _ _ _ hinv ea) as [hsa hada].
            destruct (ihl _ _ _ (cbn_step_inv _ _ hsa) eb) as [hsb hadb].
            split; [exact (cbn_gstep_trans _ _ _ hsa hsb)|].
            unfold cbn_ad_slots. simpl. apply cbn_addrs_in_app.
            + exact (cbn_addrs_in_grow _ _ _ _ (cbn_step_next _ _ hsb) hada).
            + exact hadb. }
        destruct hl as [hs had].
        split; [exact hs|exact had].
    Qed.

    Lemma cbn_rn_slots_ok : forall (l : list cbn_slot) (g : cbn_gc_state) (l' : list cbn_slot)
        (g' : cbn_gc_state),
      cbn_gc_inv g -> cbn_rn_slots cp l g = CbnCOk (l', g') ->
      cbn_gstep g g' /\ cbn_addrs_in onext g'.(cbn_g_next) (cbn_ad_slots l').
    Proof.
      induction l as [|y l ih]; intros g l' g' hinv he; simpl in he.
      - inversion he; subst; clear he.
        split; [exact (cbn_gstep_refl _ hinv)|constructor].
      - destruct (cbn_rn_slot cp y g) as [[y' g1]|w] eqn:e1; [|discriminate].
        destruct (cbn_rn_slots cp l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (cbn_rn_slot_ok _ _ _ _ hinv e1) as [hs1 had1].
        destruct (ih _ _ _ (cbn_step_inv _ _ hs1) e2) as [hs2 had2].
        split; [exact (cbn_gstep_trans _ _ _ hs1 hs2)|].
        unfold cbn_ad_slots. simpl. apply cbn_addrs_in_app.
        + exact (cbn_addrs_in_grow _ _ _ _ (cbn_step_next _ _ hs2) had1).
        + exact had2.
    Qed.

    Lemma cbn_rn_env_ok (e : cbn_env) (g : cbn_gc_state) (e' : cbn_env) (g' : cbn_gc_state) :
      cbn_gc_inv g -> cbn_rn_env cp e g = CbnCOk (e', g') ->
      cbn_gstep g g' /\ cbn_addrs_in onext g'.(cbn_g_next) (cbn_ad_env e').
    Proof.
      destruct e as [vals n o]. intros hinv he.
      unfold cbn_rn_env in he. cbn [cbn_ev_vals cbn_ev_nvals cbn_ev_goff] in he.
      destruct (cbn_rn_slots cp vals g) as [[vs' g1]|w] eqn:e1; [|discriminate].
      inversion he; subst; clear he.
      destruct (cbn_rn_slots_ok _ _ _ _ hinv e1) as [hs had].
      split; [exact hs|exact had].
    Qed.

    Lemma cbn_rn_value_ok (v : cbn_value) (g : cbn_gc_state) (v' : cbn_value) (g' : cbn_gc_state) :
      cbn_gc_inv g -> cbn_rn_value cp v g = CbnCOk (v', g') ->
      cbn_gstep g g' /\ cbn_addrs_in onext g'.(cbn_g_next) (cbn_ad_value v').
    Proof.
      destruct v as [hd sp|e c|e c i sp|e c i sp|hd sp|e c|e c sp]; intros hinv he;
        unfold cbn_rn_value in he.
      - destruct (cbn_rn_addrs cp sp g) as [[sp' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (cbn_rn_addrs_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - destruct (cbn_rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (cbn_rn_env_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - destruct (cbn_rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        destruct (cbn_rn_addrs cp sp g1) as [[sp' g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (cbn_rn_env_ok _ _ _ _ hinv e1) as [hs1 had1].
        destruct (cbn_rn_addrs_ok _ _ _ _ (cbn_step_inv _ _ hs1) e2) as [hs2 had2].
        split; [exact (cbn_gstep_trans _ _ _ hs1 hs2)|].
        apply cbn_addrs_in_app;
          [exact (cbn_addrs_in_grow _ _ _ _ (cbn_step_next _ _ hs2) had1)|exact had2].
      - destruct (cbn_rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        destruct (cbn_rn_addrs cp sp g1) as [[sp' g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (cbn_rn_env_ok _ _ _ _ hinv e1) as [hs1 had1].
        destruct (cbn_rn_addrs_ok _ _ _ _ (cbn_step_inv _ _ hs1) e2) as [hs2 had2].
        split; [exact (cbn_gstep_trans _ _ _ hs1 hs2)|].
        apply cbn_addrs_in_app;
          [exact (cbn_addrs_in_grow _ _ _ _ (cbn_step_next _ _ hs2) had1)|exact had2].
      - destruct (cbn_rn_addrs cp sp g) as [[sp' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (cbn_rn_addrs_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - destruct (cbn_rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (cbn_rn_env_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - destruct (cbn_rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        destruct (cbn_rn_addrs cp sp g1) as [[sp' g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (cbn_rn_env_ok _ _ _ _ hinv e1) as [hs1 had1].
        destruct (cbn_rn_addrs_ok _ _ _ _ (cbn_step_inv _ _ hs1) e2) as [hs2 had2].
        split; [exact (cbn_gstep_trans _ _ _ hs1 hs2)|].
        apply cbn_addrs_in_app;
          [exact (cbn_addrs_in_grow _ _ _ _ (cbn_step_next _ _ hs2) had1)|exact had2].
    Qed.

    Lemma cbn_rn_cell_ok (cl : cbn_cell) (g : cbn_gc_state) (cl' : cbn_cell) (g' : cbn_gc_state) :
      cbn_gc_inv g -> cbn_rn_cell cp cl g = CbnCOk (cl', g') ->
      cbn_gstep g g' /\ cbn_addrs_in onext g'.(cbn_g_next) (cbn_ad_cell cl').
    Proof.
      destruct cl as [vals n o c|v| |b]; intros hinv he; unfold cbn_rn_cell in he.
      - destruct (cbn_rn_slots cp vals g) as [[vs' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (cbn_rn_slots_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - destruct (cbn_rn_value cp v g) as [[v' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (cbn_rn_value_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - inversion he; subst; clear he.
        split; [exact (cbn_gstep_refl _ hinv)|constructor].
      - destruct (cp b g) as [[b' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (hcp _ _ _ _ hinv e1) as [hs [hb1 hb2]].
        split; [exact hs|constructor; [split; assumption|constructor]].
    Qed.

    (** A renamed cell is a forwarding pointer only if the cell was one. *)
    Lemma cbn_rn_cell_nofwd (cl : cbn_cell) (g : cbn_gc_state) (cl' : cbn_cell)
      (g' : cbn_gc_state) :
      cbn_cell_fwd cl = None -> cbn_rn_cell cp cl g = CbnCOk (cl', g') -> cbn_cell_fwd cl' = None.
    Proof.
      destruct cl as [vals n o c|v| |b]; intros hf he; unfold cbn_rn_cell in he.
      - destruct (cbn_rn_slots cp vals g) as [[vs' g1]|w]; [|discriminate].
        inversion he; subst. reflexivity.
      - destruct (cbn_rn_value cp v g) as [[v' g1]|w]; [|discriminate].
        inversion he; subst. reflexivity.
      - inversion he; subst. reflexivity.
      - discriminate.
    Qed.

    Lemma cbn_rn_root_ok (r : cbn_root) (g : cbn_gc_state) (r' : cbn_root) (g' : cbn_gc_state) :
      cbn_gc_inv g -> cbn_rn_root cp r g = CbnCOk (r', g') ->
      cbn_gstep g g' /\ cbn_addrs_in onext g'.(cbn_g_next) (cbn_ad_root r').
    Proof.
      destruct r as [a|x|e|v|l|l|cl]; intros hinv he; unfold cbn_rn_root in he.
      - destruct (cp a g) as [[b g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (hcp _ _ _ _ hinv e1) as [hs [hb1 hb2]].
        split; [exact hs|constructor; [split; assumption|constructor]].
      - destruct (cbn_rn_slot cp x g) as [[x' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (cbn_rn_slot_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - destruct (cbn_rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (cbn_rn_env_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - destruct (cbn_rn_value cp v g) as [[v' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (cbn_rn_value_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - destruct (cbn_rn_slots cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (cbn_rn_slots_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - destruct (cbn_rn_addrs cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (cbn_rn_addrs_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
      - destruct (cbn_rn_cell cp cl g) as [[cl' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (cbn_rn_cell_ok _ _ _ _ hinv e1) as [hs had].
        split; [exact hs|exact had].
    Qed.

    Lemma cbn_rn_roots_ok : forall (l : list cbn_root) (g : cbn_gc_state) (l' : list cbn_root)
      (g' : cbn_gc_state),
      cbn_gc_inv g -> cbn_rn_roots cp l g = CbnCOk (l', g') ->
      cbn_gstep g g' /\ cbn_addrs_in onext g'.(cbn_g_next) (cbn_ad_roots l').
    Proof.
      induction l as [|r l ih]; intros g l' g' hinv he; simpl in he.
      - inversion he; subst; clear he.
        split; [exact (cbn_gstep_refl _ hinv)|constructor].
      - destruct (cbn_rn_root cp r g) as [[r' g1]|w] eqn:e1; [|discriminate].
        destruct (cbn_rn_roots cp l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (cbn_rn_root_ok _ _ _ _ hinv e1) as [hs1 had1].
        destruct (ih _ _ _ (cbn_step_inv _ _ hs1) e2) as [hs2 had2].
        split; [exact (cbn_gstep_trans _ _ _ hs1 hs2)|].
        unfold cbn_ad_roots. simpl. apply cbn_addrs_in_app.
        + exact (cbn_addrs_in_grow _ _ _ _ (cbn_step_next _ _ hs2) had1).
        + exact had2.
    Qed.

    (** *** The context map [cbn_st_gam] *)

    Lemma cbn_rn_tree'_ok : forall (m : PTree.tree' cbn_haddr) (g : cbn_gc_state)
        (m' : PTree.tree' cbn_haddr) (g' : cbn_gc_state),
      cbn_gc_inv g -> cbn_rn_tree' cp m g = CbnCOk (m', g') ->
      cbn_gstep g g'
      /\ (forall p a', PTree.get' p m' = Some a' ->
            (onext <= cbn_ha_p a')%positive /\ (cbn_ha_p a' < g'.(cbn_g_next))%positive).
    Proof.
      induction m as [r ihr|x|x r ihr|l ihl|l ihl r ihr|l ihl x|l ihl x r ihr];
        intros g m' g' hinv he; simpl in he.
      - (* Node001 *)
        destruct (cbn_rn_tree' cp r g) as [[r' g1]|w] eqn:e1; [|discriminate].
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
        destruct (cbn_rn_tree' cp r g1) as [[r' g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (hcp _ _ _ _ hinv e1) as [hs1 [hx1 hx2]].
        destruct (ihr _ _ _ (cbn_step_inv _ _ hs1) e2) as [hs2 hb2].
        split; [exact (cbn_gstep_trans _ _ _ hs1 hs2)|].
        intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
        + exact (hb2 _ _ hb).
        + inversion hb; subst.
          split; [exact hx1|exact (Pos.lt_le_trans _ _ _ hx2 (cbn_step_next _ _ hs2))].
      - (* Node100 *)
        destruct (cbn_rn_tree' cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (ihl _ _ _ hinv e1) as [hs1 hb1].
        split; [exact hs1|].
        intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
        exact (hb1 _ _ hb).
      - (* Node101 *)
        destruct (cbn_rn_tree' cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
        destruct (cbn_rn_tree' cp r g1) as [[r' g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (ihl _ _ _ hinv e1) as [hs1 hb1].
        destruct (ihr _ _ _ (cbn_step_inv _ _ hs1) e2) as [hs2 hb2].
        split; [exact (cbn_gstep_trans _ _ _ hs1 hs2)|].
        intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
        + exact (hb2 _ _ hb).
        + destruct (hb1 _ _ hb) as [u1 u2].
          split; [exact u1|exact (Pos.lt_le_trans _ _ _ u2 (cbn_step_next _ _ hs2))].
      - (* Node110 *)
        destruct (cbn_rn_tree' cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
        destruct (cp x g1) as [[x' g2]|w] eqn:e2; [|discriminate].
        inversion he; subst; clear he.
        destruct (ihl _ _ _ hinv e1) as [hs1 hb1].
        destruct (hcp _ _ _ _ (cbn_step_inv _ _ hs1) e2) as [hs2 [hx1 hx2]].
        split; [exact (cbn_gstep_trans _ _ _ hs1 hs2)|].
        intros p b hb. destruct p as [q|q|]; simpl in hb; try discriminate.
        + destruct (hb1 _ _ hb) as [u1 u2].
          split; [exact u1|exact (Pos.lt_le_trans _ _ _ u2 (cbn_step_next _ _ hs2))].
        + inversion hb; subst. split; assumption.
      - (* Node111 *)
        destruct (cbn_rn_tree' cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
        destruct (cp x g1) as [[x' g2]|w] eqn:e2; [|discriminate].
        destruct (cbn_rn_tree' cp r g2) as [[r' g3]|w] eqn:e3; [|discriminate].
        inversion he; subst; clear he.
        destruct (ihl _ _ _ hinv e1) as [hs1 hb1].
        destruct (hcp _ _ _ _ (cbn_step_inv _ _ hs1) e2) as [hs2 [hx1 hx2]].
        destruct (ihr _ _ _ (cbn_step_inv _ _ hs2) e3) as [hs3 hb3].
        split; [exact (cbn_gstep_trans _ _ _ hs1 (cbn_gstep_trans _ _ _ hs2 hs3))|].
        intros p b hb. destruct p as [q|q|]; simpl in hb.
        + exact (hb3 _ _ hb).
        + destruct (hb1 _ _ hb) as [u1 u2]. split; [exact u1|].
          exact (Pos.lt_le_trans _ _ _ u2
                   (Pos.le_trans _ _ _ (cbn_step_next _ _ hs2) (cbn_step_next _ _ hs3))).
        + inversion hb; subst.
          split; [exact hx1|exact (Pos.lt_le_trans _ _ _ hx2 (cbn_step_next _ _ hs3))].
    Qed.

    Lemma cbn_rn_ptree_ok (m : PTree.t cbn_haddr) (g : cbn_gc_state) (m' : PTree.t cbn_haddr)
      (g' : cbn_gc_state) :
      cbn_gc_inv g -> cbn_rn_ptree cp m g = CbnCOk (m', g') ->
      cbn_gstep g g'
      /\ (forall p a', PTree.get p m' = Some a' ->
            (onext <= cbn_ha_p a')%positive /\ (cbn_ha_p a' < g'.(cbn_g_next))%positive).
    Proof.
      destruct m as [|m]; intros hinv he; unfold cbn_rn_ptree in he.
      - inversion he; subst; clear he.
        split; [exact (cbn_gstep_refl _ hinv)|].
        intros p b hb; discriminate.
      - destruct (cbn_rn_tree' cp m g) as [[m2 g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (cbn_rn_tree'_ok _ _ _ _ hinv e1) as [hs hb].
        split; [exact hs|].
        intros p b hbb. exact (hb _ _ hbb).
    Qed.

    (** *** One copied cell

      The cell is read from the old heap, its children are renamed, the copy is pushed onto
      the new heap at [cbn_g_next] and the old cell is overwritten with [CbnCFwd] of that address.
      *)
    Lemma cbn_gc_copy_write (a : cbn_haddr) (g : cbn_gc_state) (cl cl1 : cbn_cell)
      (g1 : cbn_gc_state)
        (old : cbn_bheap cbn_cell) :
      cbn_gc_inv g ->
      cbn_cell_fwd cl = None ->
      cbn_rn_cell cp cl g = CbnCOk (cl1, g1) ->
      cbn_bh_upd a (CbnCFwd (CbnHAddr g1.(cbn_g_next))) g1.(cbn_g_old) = Some old ->
      cbn_gstep g (cbn_mkGc old (cbn_bh_cons cl1 g1.(cbn_g_heap)) (Pos.succ g1.(cbn_g_next)))
      /\ (onext <= g1.(cbn_g_next))%positive
      /\ (g1.(cbn_g_next) < Pos.succ g1.(cbn_g_next))%positive.
    Proof.
      intros hinv hf e1 e2.
      destruct (cbn_rn_cell_ok _ _ _ _ hinv e1) as [hs1 had1].
      pose proof (cbn_step_inv _ _ hs1) as hinv1.
      pose proof (cbn_inv_heap _ hinv1) as hok1.
      pose proof (cbn_bh_ok_le _ _ _ hok1) as hlo1.
      pose proof (cbn_rn_cell_nofwd _ _ _ _ hf e1) as hf1.
      assert (hinv2 : cbn_gc_inv (cbn_mkGc old (cbn_bh_cons cl1 g1.(cbn_g_heap))
        (Pos.succ g1.(cbn_g_next)))).
      { constructor; cbn.
        - intros b clb hb hfb. destruct (cbn_haddr_dec b a) as [->|hne].
          + rewrite (cbn_bh_get_upd_same _ _ _ _ e2) in hb.
            inversion hb; subst. discriminate.
          + rewrite (cbn_bh_get_upd_other _ _ _ _ _ e2 hne) in hb.
            exact (cbn_inv_keep _ hinv1 _ _ hb hfb).
        - intros b b' hb. destruct (cbn_haddr_dec b a) as [->|hne].
          + rewrite (cbn_bh_get_upd_same _ _ _ _ e2) in hb. inversion hb; subst.
            split; [exact hlo1|apply Pos.lt_succ_diag_r].
          + rewrite (cbn_bh_get_upd_other _ _ _ _ _ e2 hne) in hb.
            destruct (cbn_inv_moved _ hinv1 _ _ hb) as [u1 u2].
            split; [exact u1|exact (Pos.lt_trans _ _ _ u2 (Pos.lt_succ_diag_r _))].
        - exact (cbn_bh_ok_cons _ _ _ _ hok1).
        - intros b clb hb. destruct (cbn_haddr_dec b (CbnHAddr g1.(cbn_g_next))) as [->|hne].
          + rewrite (cbn_bh_get_cons_new _ _ _ _ hok1) in hb. inversion hb; subst.
            exact (cbn_addrs_in_grow _ _ _ _ (Pos.lt_le_incl _ _ (Pos.lt_succ_diag_r _)) had1).
          + rewrite (cbn_bh_get_cons_old _ _ _ _ _ hok1 hne) in hb.
            exact (cbn_addrs_in_grow _ _ _ _ (Pos.lt_le_incl _ _ (Pos.lt_succ_diag_r _))
                     (cbn_inv_cells _ hinv1 _ _ hb)).
        - intros b b' hb. destruct (cbn_haddr_dec b (CbnHAddr g1.(cbn_g_next))) as [->|hne].
          + rewrite (cbn_bh_get_cons_new _ _ _ _ hok1) in hb. inversion hb; subst. discriminate.
          + rewrite (cbn_bh_get_cons_old _ _ _ _ _ hok1 hne) in hb.
            exact (cbn_inv_nofwd _ hinv1 _ _ hb). }
      split.
      - constructor; cbn.
        + exact hinv2.
        + exact (Pos.le_trans _ _ _ (cbn_step_next _ _ hs1)
                   (Pos.lt_le_incl _ _ (Pos.lt_succ_diag_r _))).
      - split; [exact hlo1|apply Pos.lt_succ_diag_r].
    Qed.

  End Structural.

  (** ** The walk of [cbn_gc_copy] keeps the invariant

    Every address the collector returns is an address of the new heap, at or above
    [onext]. *)
  Lemma cbn_gc_copy_ok : forall (f : cbn_fuel), cbn_cp_ok (cbn_gc_copy f).
  Proof.
    intros f. induction f as [|k ih]; intros a g a' g' hinv he.
    - rewrite cbn_gc_copy_FO in he.
      destruct (cbn_bh_get a g.(cbn_g_old)) as [cl|] eqn:ea; [|discriminate].
      destruct cl as [vals n o c|v| |b]; try discriminate.
      inversion he; subst; clear he.
      destruct (cbn_inv_moved _ hinv _ _ ea) as [hb1 hb2].
      split; [exact (cbn_gstep_refl _ hinv)|]. split; assumption.
    - rewrite cbn_gc_copy_FS in he.
      destruct (cbn_bh_get a g.(cbn_g_old)) as [cl|] eqn:ea; [|discriminate].
      destruct cl as [vals n o c|v| |b].
      + destruct (cbn_rn_cell (cbn_gc_copy (k tt)) (CbnCSusp vals n o c) g) as [[cl1 g1]|w] eqn:e1;
          [|discriminate].
        destruct (cbn_bh_upd a (CbnCFwd (CbnHAddr g1.(cbn_g_next))) g1.(cbn_g_old)) as
          [old|] eqn:e2;
          [|discriminate].
        inversion he; subst; clear he.
        exact (cbn_gc_copy_write _ (ih tt) a g (CbnCSusp vals n o c) _ _ _ hinv eq_refl e1 e2).
      + destruct (cbn_rn_cell (cbn_gc_copy (k tt)) (CbnCDone v) g) as [[cl1 g1]|w] eqn:e1;
          [|discriminate].
        destruct (cbn_bh_upd a (CbnCFwd (CbnHAddr g1.(cbn_g_next))) g1.(cbn_g_old)) as
          [old|] eqn:e2;
          [|discriminate].
        inversion he; subst; clear he.
        exact (cbn_gc_copy_write _ (ih tt) a g (CbnCDone v) _ _ _ hinv eq_refl e1 e2).
      + destruct (cbn_rn_cell (cbn_gc_copy (k tt)) CbnCBusy g) as [[cl1 g1]|w] eqn:e1;
        [|discriminate].
        destruct (cbn_bh_upd a (CbnCFwd (CbnHAddr g1.(cbn_g_next))) g1.(cbn_g_old)) as
          [old|] eqn:e2;
          [|discriminate].
        inversion he; subst; clear he.
        exact (cbn_gc_copy_write _ (ih tt) a g CbnCBusy _ _ _ hinv eq_refl e1 e2).
      + inversion he; subst; clear he.
        destruct (cbn_inv_moved _ hinv _ _ ea) as [hb1 hb2].
        split; [exact (cbn_gstep_refl _ hinv)|]. split; assumption.
  Qed.

End Collector.

(** ** [cbn_collect], written once *)

Lemma cbn_collect_eq (rs : list cbn_root) (s : cbn_state) :
  cbn_collect rs s =
  match cbn_rn_ptree (cbn_gc_copy (cbn_fuel_of_pos s.(cbn_st_next) (fun _ => CbnFO))) s.(cbn_st_gam)
          (cbn_mkGc s.(cbn_st_heap) (cbn_bh_holes s.(cbn_st_next)) s.(cbn_st_next)) with
  | CbnCOk (gm, g1) =>
    match cbn_rn_roots (cbn_gc_copy (cbn_fuel_of_pos s.(cbn_st_next) (fun _ => CbnFO))) rs g1 with
    | CbnCOk (rs2, g2) =>
      CbnCOk (rs2, cbn_mkState g2.(cbn_g_heap) g2.(cbn_g_next)
             (cbn_gc_room (N.sub (Npos g2.(cbn_g_next)) (Npos s.(cbn_st_next)))) s.(cbn_st_steps) gm
             s.(cbn_st_memo))
    | CbnCFail w => CbnCFail w
    end
  | CbnCFail w => CbnCFail w
  end.
Proof. reflexivity. Qed.

(** ** A collection re-establishes the state invariant *)

Theorem cbn_collect_sound (rs : list cbn_root) (s : cbn_state) (rs' : list cbn_root)
  (s' : cbn_state) :
  cbn_heap_nofwd s.(cbn_st_heap) -> cbn_collect rs s = CbnCOk (rs', s') ->
  cbn_state_ok s.(cbn_st_next) s'
  /\ cbn_heap_nofwd s'.(cbn_st_heap)
  /\ (s.(cbn_st_next) <= s'.(cbn_st_next))%positive
  /\ s'.(cbn_st_steps) = s.(cbn_st_steps).
Proof.
  rewrite cbn_collect_eq. intros hnf he.
  destruct (cbn_rn_ptree (cbn_gc_copy (cbn_fuel_of_pos s.(cbn_st_next) (fun _ => CbnFO)))
    s.(cbn_st_gam)
              (cbn_mkGc s.(cbn_st_heap) (cbn_bh_holes s.(cbn_st_next)) s.(cbn_st_next))) as
                [[gm g1]|w1] eqn:e1;
    [|discriminate].
  destruct (cbn_rn_roots (cbn_gc_copy (cbn_fuel_of_pos s.(cbn_st_next) (fun _ => CbnFO))) rs g1)
    as [[rs2 g2]|w2] eqn:e2; [|discriminate].
  inversion he; subst; clear he.
  assert (hinv0 : cbn_gc_inv s.(cbn_st_heap) s.(cbn_st_next)
                    (cbn_mkGc s.(cbn_st_heap) (cbn_bh_holes s.(cbn_st_next)) s.(cbn_st_next))).
  { constructor; cbn.
    - intros a cl hc _. exact hc.
    - intros a a' hc. destruct (hnf _ _ hc).
    - apply cbn_bh_ok_holes.
    - intros b cl hc. rewrite cbn_bh_get_holes in hc. discriminate.
    - intros b b' hc. rewrite cbn_bh_get_holes in hc. discriminate. }
  destruct (cbn_rn_ptree_ok s.(cbn_st_heap) s.(cbn_st_next) _
              (cbn_gc_copy_ok s.(cbn_st_heap) s.(cbn_st_next) _) _ _ _ _ hinv0 e1)
    as [hs1 hgb].
  destruct (cbn_rn_roots_ok s.(cbn_st_heap) s.(cbn_st_next) _
              (cbn_gc_copy_ok s.(cbn_st_heap) s.(cbn_st_next) _) _ _ _ _
              (cbn_step_inv _ _ _ _ hs1) e2) as [hs2 _].
  pose proof (cbn_step_inv _ _ _ _ hs2) as hinv2.
  split.
  { split; cbn.
    - exact (cbn_inv_heap _ _ _ hinv2).
    - intros a cl hc. exact (cbn_inv_cells _ _ _ hinv2 _ _ hc).
    - intros k a hk. destruct (hgb _ _ hk) as [u1 u2].
      split; [exact u1|exact (Pos.lt_le_trans _ _ _ u2 (cbn_step_next _ _ _ _ hs2))]. }
  split; [exact (cbn_inv_nofwd _ _ _ hinv2)|].
  split.
  { cbn. exact (Pos.le_trans _ _ _ (cbn_step_next _ _ _ _ hs1) (cbn_step_next _ _ _ _ hs2)). }
  reflexivity.
Qed.
