(* Distributed under the terms of the MIT license. *)
(** ETA-COPY (wip/etak-cbne-2026-10-30) of integ-all8's [PCUICCallByNeedSound] (1a92b56c) over the η environment
    ([PCUICWfEnvEta], [PCUICCallByNeedEta]): see [PCUICCallByNeedEtaSoundHookProof] for what differs. *)
From Stdlib Require Import BinPos BinNat.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require CanonicalTries.
From MetaRocq.Common Require Import config Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils.
From MetaRocq.SafeChecker Require Import PCUICCallByNeedEta.

Import CanonicalTries.

(** * The state invariant of the call-by-need machine

  [cbn_state_ok lo s] is what every machine function assumes of the state it is given and
  re-establishes for the state it returns. [lo] is the first address the last collection
  kept: below it the addresses are gone, and nothing live may name them.

  - the heap was built the way [cbn_bh_ok] describes, so the laws of [PCUICCallByNeedEta] apply;
  - no cell names an address outside the heap, in either direction: the collector must
    re-establish this after it moves every live cell ([PCUICCallByNeedEtaSoundGC.cbn_collect_sound]);
  - the context map [cbn_st_gam] names only addresses the heap has.

  This file proves that the start state satisfies it and that allocation and a write keep
  it. The readings the soundness proof uses are the ghost readings of
  [PCUICCallByNeedEtaSoundEval], which take [cbn_state_ok] as one clause of their invariant. *)

Definition cbn_addrs_in (lo n : positive) (l : list cbn_haddr) : Prop :=
  Forall (fun b => (lo <= cbn_ha_p b)%positive /\ (cbn_ha_p b < n)%positive) l.

Record cbn_state_ok (lo : positive) (s : cbn_state) : Prop := cbn_mkStateOk {
  cbn_so_heap : cbn_bh_ok lo s.(cbn_st_next) s.(cbn_st_heap);
  cbn_so_cells : forall a cl, cbn_bh_get a s.(cbn_st_heap) = Some cl ->
    cbn_addrs_in lo s.(cbn_st_next) (cbn_ad_cell cl);
  cbn_so_gam : forall k a, PTree.get k s.(cbn_st_gam) = Some a ->
    (lo <= cbn_ha_p a)%positive /\ (cbn_ha_p a < s.(cbn_st_next))%positive }.

Lemma cbn_addrs_in_grow lo n n' l :
  (n <= n')%positive -> cbn_addrs_in lo n l -> cbn_addrs_in lo n' l.
Proof.
  intros hn. induction 1 as [|b l [h1 h2] _ ih]; constructor.
  - split; [exact h1|]. eapply Pos.lt_le_trans; eassumption.
  - exact ih.
Qed.

Lemma cbn_haddr_dec (a b : cbn_haddr) : {a = b} + {a <> b}.
Proof.
  destruct a as [p], b as [q]. destruct (Pos.eq_dec p q) as [->|hne].
  - left; reflexivity.
  - right. intros e. inversion e. contradiction.
Qed.

Lemma cbn_state_ok_init : cbn_state_ok xH cbn_init.
Proof.
  split.
  - exact cbn_init_ok.
  - intros a cl e. unfold cbn_init in e. cbn [cbn_st_heap] in e.
    rewrite cbn_bh_get_holes in e. discriminate.
  - intros k a e. unfold cbn_init in e. cbn [cbn_st_gam] in e.
    rewrite PTree.gempty in e. discriminate.
Qed.

(** Allocation: the state stays good exactly when the cell written names no address the
  heap does not have. The new address itself is allowed, so a cell may point to itself. *)
Lemma cbn_alloc_now_state_ok lo cl s :
  cbn_state_ok lo s ->
  cbn_addrs_in lo (Pos.succ s.(cbn_st_next)) (cbn_ad_cell cl) ->
  cbn_state_ok lo (snd (cbn_alloc_now cl s)).
Proof.
  intros [hh hc hg] hcl. split; cbn.
  - apply (cbn_bh_ok_cons _ _ _ _ hh).
  - intros a cl' e.
    destruct (cbn_haddr_dec a (CbnHAddr s.(cbn_st_next))) as [->|hne].
    + erewrite cbn_bh_digits_get_cons_new in e by eauto using cbn_bh_ok_digits.
      inversion e; subst. exact hcl.
    + erewrite cbn_bh_digits_get_cons_old in e by eauto using cbn_bh_ok_digits.
      apply (cbn_addrs_in_grow _ _ _ _ (Pos.lt_le_incl _ _ (Pos.lt_succ_diag_r _)) (hc _ _ e)).
  - intros k a e. destruct (hg _ _ e) as [h1 h2]. split; [exact h1|].
    exact (Pos.lt_trans _ _ _ h2 (Pos.lt_succ_diag_r _)).
Qed.

(** A write to an address the heap has: forcing writes [CbnCBusy], then the value. *)
Lemma cbn_heap_upd_state_ok lo a cl s s' :
  cbn_state_ok lo s ->
  cbn_addrs_in lo s.(cbn_st_next) (cbn_ad_cell cl) ->
  cbn_heap_upd a cl s = Some s' ->
  cbn_state_ok lo s'.
Proof.
  intros [hh hc hg] hcl e.
  unfold cbn_heap_upd in e.
  destruct (cbn_bh_upd a cl s.(cbn_st_heap)) as [h'|] eqn:hu; [|discriminate].
  cbn in e. inversion e; subst; clear e. split; cbn.
  - exact (cbn_bh_upd_ok _ _ _ _ _ _ hh hu).
  - intros b cl' e.
    destruct (cbn_haddr_dec b a) as [->|hne].
    + rewrite (cbn_bh_get_upd_same _ _ _ _ hu) in e. inversion e; subst. exact hcl.
    + rewrite (cbn_bh_get_upd_other _ _ _ _ _ hu hne) in e. exact (hc _ _ e).
  - exact hg.
Qed.
