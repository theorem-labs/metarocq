(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require CanonicalTries.
From MetaRocq.Common Require Import config Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils.
From MetaRocq.SafeChecker Require Import PCUICCallByNeed.

Import CanonicalTries.

(** * The state invariant of the call-by-need machine

  [state_ok lo s] is what every machine function assumes of the state it is given and
  re-establishes for the state it returns. [lo] is the first address the last collection
  kept: below it the addresses are gone, and nothing live may name them.

  - the heap was built the way [bh_ok] describes, so the laws of [PCUICCallByNeed] apply;
  - no cell names an address outside the heap, in either direction: the collector must
    re-establish this after it moves every live cell ([PCUICCallByNeedSoundGC.collect_sound]);
  - the context map [st_gam] names only addresses the heap has.

  This file proves that the start state satisfies it and that allocation and a write keep
  it. The readings the soundness proof uses are the ghost readings of
  [PCUICCallByNeedSoundEval], which take [state_ok] as one clause of their invariant. *)

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
