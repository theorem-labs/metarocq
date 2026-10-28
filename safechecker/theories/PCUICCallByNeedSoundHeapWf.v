(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require CanonicalTries.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping.
From MetaRocq.SafeChecker Require Import PCUICWfEnv PCUICCallByNeed PCUICCallByNeedSound
  PCUICCallByNeedSoundGC PCUICCallByNeedSoundCtx PCUICCallByNeedSoundEval
  PCUICCallByNeedSoundLevel.

Import CanonicalTries.

(** * The structural invariant survives the machine (BET-298, step 3b, slice B)

  [PCUICCallByNeedSoundLevel] states two interfaces, [machine_hwf] and [alloc_hwf]: every
  machine function and an allocation keep [hwf Q] of the heap, [rwf Q] of the roots and
  [vwf Q] of the value they return, at any master level [Q >= nctx]. This file proves both
  ([machine_hwf_holds], [alloc_hwf_holds]).

  Why it holds: a fresh variable [NVar l] is made only by [gam], at the level
  [nctx - S j] of an entry [j] of [Γ], so below [nctx] when [#|Γ| <= nctx]; the head of a
  [VCon] or of a neutral constant comes only from a [tConstruct], [tInd] or [tConst] code,
  which is closed; every other value the machine builds copies existing structure ([add_spine],
  a collection's renaming) or has no head ([VLam], [VFix], [VOpen], [VStuck], [VStuckFix]).

  The heap needs one law that holds for every digit list, not only the ones [bh_ok] describes,
  because [hwf] is stated over [heap_get] alone: a cell [bh_get] finds after [bh_cons] is the
  new cell or a cell it found before ([bh_get_cons_any]).

  [machine_hwf_holds] needs [#|Γ| <= nctx]; without it the interface is false
  ([machine_hwf_needs_len]): with [nctx = 0] and one assumption in [Γ], [gam] makes
  [NVar 0], which is not below the master level [0]. The machine's runs have [nctx = #|Γ|]
  ([cbn_conv_answer]), and [machine_hwf_run] is that instance. [whnf_master_hwf] and
  [eval_slot_master_hwf] are [whnf_master] and [eval_slot_master] with the interface
  discharged from the master section's own [nctx = #|Γ|]. *)

(** ** The heap: what [bh_cons] adds, for any digit list *)

Section HeapCons.
  Context {A : Type}.

  Definition bh_zeros (zs : bheap A) : Prop := Forall (fun d => d = DZero) zs.

  Lemma bh_top_zeros zs acc cand : bh_zeros zs -> bh_top zs acc cand = cand.
  Proof.
    intros hz. revert acc cand.
    induction hz as [|d zs hd hz ih]; intros acc cand; [reflexivity|].
    subst d. cbn. apply ih.
  Qed.

  Lemma bh_top_app_zeros h zs acc cand :
    bh_zeros zs -> bh_top (h ++ zs) acc cand = bh_top h acc cand.
  Proof.
    intros hz. revert acc cand. induction h as [|d h ih]; intros acc cand; cbn.
    - apply bh_top_zeros. exact hz.
    - destruct d; apply ih.
  Qed.

  Lemma bh_scan_nil p acc cand : @bh_scan A p [] acc cand = None.
  Proof. destruct p; reflexivity. Qed.

  Lemma bh_scan_zeros p zs acc cand : bh_zeros zs -> bh_scan p zs acc cand = None.
  Proof.
    intros hz. revert p acc cand.
    induction hz as [|d zs hd hz ih]; intros p acc cand; [apply bh_scan_nil|].
    subst d. destruct p as [p|p|]; cbn.
    - apply ih.
    - apply ih.
    - apply bh_top_zeros. exact hz.
  Qed.

  Lemma bh_scan_app_zeros p h zs acc cand :
    bh_zeros zs -> bh_scan p (h ++ zs) acc cand = bh_scan p h acc cand.
  Proof.
    intros hz. revert p acc cand. induction h as [|d h ih]; intros p acc cand.
    - cbn [app]. rewrite (bh_scan_zeros p zs acc cand hz). symmetry. apply bh_scan_nil.
    - destruct p as [p|p|], d as [|t]; cbn [app bh_scan]; try apply ih;
        apply bh_top_app_zeros; exact hz.
  Qed.

  Lemma bh_get_app_zeros a h zs : bh_zeros zs -> bh_get a (h ++ zs) = bh_get a h.
  Proof.
    intros hz. unfold bh_get, bh_find. rewrite (bh_scan_app_zeros _ _ _ _ _ hz). reflexivity.
  Qed.

  Lemma bh_carry_app_zeros t h zs :
    bh_zeros zs -> exists zs', bh_zeros zs' /\ bh_carry t (h ++ zs) = bh_carry t h ++ zs'.
  Proof.
    intros hz. revert t. induction h as [|d h ih]; intros t.
    - cbn [app]. destruct hz as [|d zs0 hd hz0].
      + exists []. split; [constructor|reflexivity].
      + subst d. exists zs0. split; [exact hz0|reflexivity].
    - destruct d as [|t'].
      + exists zs. split; [exact hz|reflexivity].
      + destruct (ih (BNode t' t)) as (zs' & hz' & e). exists zs'. split; [exact hz'|].
        cbn [app bh_carry]. rewrite e. reflexivity.
  Qed.

  (** Every digit list is a list with digits, or the empty list, followed by zeros. *)
  Lemma bh_split (h : bheap A) :
    exists h0 zs, h = h0 ++ zs /\ bh_zeros zs /\ (h0 = [] \/ exists n, bh_digits h0 n).
  Proof.
    induction h as [|d h ih].
    - exists [], []. split; [reflexivity|]. split; [constructor|left; reflexivity].
    - destruct ih as (h0 & zs & -> & hz & [-> | (n & hn)]).
      + destruct d as [|t].
        * exists [], (DZero :: zs). split; [reflexivity|].
          split; [constructor; [reflexivity|exact hz]|left; reflexivity].
        * exists [DOne t], zs. split; [reflexivity|].
          split; [exact hz|right; exists xH; constructor].
      + exists (d :: h0), zs. split; [reflexivity|]. split; [exact hz|right].
        destruct d as [|t]; [exists (xO n)|exists (xI n)]; constructor; exact hn.
  Qed.

  (** The one cell of a single tree of depth 0 is address 0, which no address reaches. *)
  Lemma bh_get_one a (t : btree A) : bh_get a [DOne t] = None.
  Proof.
    destruct a as [p]. unfold bh_get, bh_find. cbn [ha_p].
    destruct p as [p|p|]; cbn [bh_scan bh_top]; rewrite ?bh_scan_nil; reflexivity.
  Qed.

  (** A cell [bh_get] finds after [bh_cons] is the new cell or one it found before. *)
  Lemma bh_get_cons_any (y x : A) h a :
    bh_get a (bh_cons y h) = Some x -> x = y \/ bh_get a h = Some x.
  Proof.
    destruct (bh_split h) as (h0 & zs & -> & hz & hh0).
    unfold bh_cons. destruct (bh_carry_app_zeros (BLeaf y) h0 zs hz) as (zs' & hz' & ->).
    rewrite (bh_get_app_zeros a _ _ hz'), (bh_get_app_zeros a _ _ hz).
    change (bh_carry (BLeaf y) h0) with (bh_cons y h0).
    destruct hh0 as [-> | (n & hn)].
    - change (bh_cons y []) with [DOne (BLeaf y)]. rewrite bh_get_one. intros h. discriminate h.
    - destruct (haddr_dec a (HAddr n)) as [-> | hne].
      + rewrite (bh_digits_get_cons_new y h0 n hn). intros h. injection h as ->. left.
        reflexivity.
      + rewrite (bh_digits_get_cons_old y h0 n a hn hne). intros h. right. exact h.
  Qed.
End HeapCons.

(** ** The invariant over the state operations that keep the heap or write one cell *)

Lemma rwf_tl Q r rs : Forall (rwf Q) (r :: rs) -> Forall (rwf Q) rs.
Proof. intros h. inversion h; assumption. Qed.

Lemma rwf_hd Q r rs : Forall (rwf Q) (r :: rs) -> rwf Q r.
Proof. intros h. inversion h; assumption. Qed.

Lemma hwf_heap Q s s' : s'.(st_heap) = s.(st_heap) -> hwf Q s -> hwf Q s'.
Proof. intros he h a cl ha. unfold heap_get in ha. rewrite he in ha. exact (h a cl ha). Qed.

Lemma hwf_upd Q a cl s s' : hwf Q s -> cwf Q cl -> heap_upd a cl s = Some s' -> hwf Q s'.
Proof.
  intros h hc hu b cl' hb.
  destruct (haddr_dec b a) as [-> | hne].
  - rewrite (heap_get_upd_same a cl s s' hu) in hb. injection hb as <-. exact hc.
  - rewrite (heap_get_upd_other a b cl s s' hu hne) in hb. exact (h b cl' hb).
Qed.

Lemma hwf_alloc_now Q cl s : hwf Q s -> cwf Q cl -> hwf Q (snd (alloc_now cl s)).
Proof.
  intros h hc b cl' hb. unfold heap_get in hb. cbn [alloc_now snd st_heap] in hb.
  destruct (bh_get_cons_any cl cl' _ b hb) as [-> | hb']; [exact hc|exact (h b cl' hb')].
Qed.

Lemma add_spine_wf Q v l v' : vwf Q v -> add_spine v l = Some v' -> vwf Q v'.
Proof.
  intros hv he. destruct v; cbn in he; try discriminate he; injection he as <-; exact hv.
Qed.

(** ** A renaming keeps the heads and levels of what it renames *)

Section RenameWf.
  Context {G : Type} (f : haddr -> G -> cbn_res (haddr * G)) (Pg : G -> Prop)
    (hf : forall a g a' g', Pg g -> f a g = COk (a', g') -> Pg g').

  Lemma rn_addrs_wf : forall l g l' g', Pg g -> rn_addrs f l g = COk (l', g') -> Pg g'.
  Proof.
    induction l as [|a l ih]; intros g l' g' hg he; simpl in he.
    - injection he as <- <-. exact hg.
    - destruct (f a g) as [[b g1]|w] eqn:e1; [|discriminate].
      destruct (rn_addrs f l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
      injection he as <- <-. exact (ih _ _ _ (hf _ _ _ _ hg e1) e2).
  Qed.

  Lemma rn_slot_wf : forall x g x' g', Pg g -> rn_slot f x g = COk (x', g') -> Pg g'.
  Proof.
    intros x. induction x as [a|vs n o c ihvs] using slot_ind'; intros g x' g' hg he.
    - simpl in he. destruct (f a g) as [[b g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. exact (hf _ _ _ _ hg e1).
    - rewrite rn_slot_SInl in he.
      destruct (rn_slots f vs g) as [[vs' g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-.
      revert g vs' g1 hg e1.
      induction ihvs as [|y vs hy hvs ihl]; intros g vs' g1 hg e1; simpl in e1.
      + injection e1 as <- <-. exact hg.
      + destruct (rn_slot f y g) as [[y' ga]|wa] eqn:ea; [|discriminate].
        destruct (rn_slots f vs ga) as [[vs2 gb]|wb] eqn:eb; [|discriminate].
        injection e1 as <- <-. exact (ihl _ _ _ (hy _ _ _ hg ea) eb).
  Qed.

  Lemma rn_slots_wf : forall l g l' g', Pg g -> rn_slots f l g = COk (l', g') -> Pg g'.
  Proof.
    induction l as [|y l ih]; intros g l' g' hg he; simpl in he.
    - injection he as <- <-. exact hg.
    - destruct (rn_slot f y g) as [[y' g1]|w] eqn:e1; [|discriminate].
      destruct (rn_slots f l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
      injection he as <- <-. exact (ih _ _ _ (rn_slot_wf _ _ _ _ hg e1) e2).
  Qed.

  Lemma rn_env_wf e g e' g' : Pg g -> rn_env f e g = COk (e', g') -> Pg g'.
  Proof. intros hg he. exact (rn_slots_wf _ _ _ _ hg (rn_env_vals _ _ _ _ _ he)). Qed.

  Lemma rn_value_wf Q v g v' g' :
    Pg g -> rn_value f v g = COk (v', g') -> Pg g' /\ (vwf Q v -> vwf Q v').
  Proof.
    intros hg he. unfold rn_value in he.
    destruct v as [h sp|e c|e c i sp|e c i sp|h sp|e c|e c sp].
    - destruct (rn_addrs f sp g) as [[sp1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. split; [exact (rn_addrs_wf _ _ _ _ hg e1)|exact (fun x => x)].
    - destruct (rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      injection he as <- <-. split; [exact (rn_env_wf _ _ _ _ hg E1)|intros _; exact I].
    - destruct (rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      destruct (rn_addrs f sp g1) as [[sp1 g2]|w] eqn:E2; [|discriminate].
      injection he as <- <-.
      split; [exact (rn_addrs_wf _ _ _ _ (rn_env_wf _ _ _ _ hg E1) E2)|intros _; exact I].
    - destruct (rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      destruct (rn_addrs f sp g1) as [[sp1 g2]|w] eqn:E2; [|discriminate].
      injection he as <- <-.
      split; [exact (rn_addrs_wf _ _ _ _ (rn_env_wf _ _ _ _ hg E1) E2)|intros _; exact I].
    - destruct (rn_addrs f sp g) as [[sp1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. split; [exact (rn_addrs_wf _ _ _ _ hg e1)|exact (fun x => x)].
    - destruct (rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      injection he as <- <-. split; [exact (rn_env_wf _ _ _ _ hg E1)|intros _; exact I].
    - destruct (rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      destruct (rn_addrs f sp g1) as [[sp1 g2]|w] eqn:E2; [|discriminate].
      injection he as <- <-.
      split; [exact (rn_addrs_wf _ _ _ _ (rn_env_wf _ _ _ _ hg E1) E2)|intros _; exact I].
  Qed.

  Lemma rn_cell_wf Q cl g cl' g' :
    Pg g -> rn_cell f cl g = COk (cl', g') -> Pg g' /\ (cwf Q cl -> cwf Q cl').
  Proof.
    intros hg he. unfold rn_cell in he. destruct cl as [vs n o c|v| |b].
    - destruct (rn_slots f vs g) as [[vs1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. split; [exact (rn_slots_wf _ _ _ _ hg e1)|intros _; exact I].
    - destruct (rn_value f v g) as [[v1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. exact (rn_value_wf Q _ _ _ _ hg e1).
    - injection he as <- <-. split; [exact hg|intros _; exact I].
    - destruct (f b g) as [[b1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. split; [exact (hf _ _ _ _ hg e1)|intros _; exact I].
  Qed.

  Lemma rn_root_wf Q r g r' g' :
    Pg g -> rn_root f r g = COk (r', g') -> Pg g' /\ (rwf Q r -> rwf Q r').
  Proof.
    intros hg he. unfold rn_root in he. destruct r as [a|x|e|v|l|l|cl].
    - destruct (f a g) as [[b g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. split; [exact (hf _ _ _ _ hg e1)|intros _; exact I].
    - destruct (rn_slot f x g) as [[x1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. split; [exact (rn_slot_wf _ _ _ _ hg e1)|intros _; exact I].
    - destruct (rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      injection he as <- <-. split; [exact (rn_env_wf _ _ _ _ hg E1)|intros _; exact I].
    - destruct (rn_value f v g) as [[v1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. exact (rn_value_wf Q _ _ _ _ hg e1).
    - destruct (rn_slots f l g) as [[l1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. split; [exact (rn_slots_wf _ _ _ _ hg e1)|intros _; exact I].
    - destruct (rn_addrs f l g) as [[l1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. split; [exact (rn_addrs_wf _ _ _ _ hg e1)|intros _; exact I].
    - destruct (rn_cell f cl g) as [[cl1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. exact (rn_cell_wf Q _ _ _ _ hg e1).
  Qed.

  Lemma rn_roots_wf Q : forall l g l' g',
    Pg g -> rn_roots f l g = COk (l', g') ->
    Pg g' /\ (Forall (rwf Q) l -> Forall (rwf Q) l').
  Proof.
    induction l as [|r l ih]; intros g l' g' hg he; simpl in he.
    - injection he as <- <-. split; [exact hg|intros h; exact h].
    - destruct (rn_root f r g) as [[r1 g1]|w] eqn:e1; [|discriminate].
      destruct (rn_roots f l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
      injection he as <- <-.
      destruct (rn_root_wf Q _ _ _ _ hg e1) as [hg1 hr1].
      destruct (ih _ _ _ hg1 e2) as [hg2 hr2].
      split; [exact hg2|].
      intros h. inversion h as [|? ? hr hl]; subst.
      constructor; [exact (hr1 hr)|exact (hr2 hl)].
  Qed.

  Lemma rn_tree'_wf : forall m g m' g', Pg g -> rn_tree' f m g = COk (m', g') -> Pg g'.
  Proof.
    induction m as [r ihr|x|x r ihr|l ihl|l ihl r ihr|l ihl x|l ihl x r ihr];
      intros g m' g' hg he; simpl in he.
    - destruct (rn_tree' f r g) as [[r' g1]|w1] eqn:e1; [|discriminate].
      injection he as <- <-. exact (ihr _ _ _ hg e1).
    - destruct (f x g) as [[x' g1]|w1] eqn:e1; [|discriminate].
      injection he as <- <-. exact (hf _ _ _ _ hg e1).
    - destruct (f x g) as [[x' g1]|w1] eqn:e1; [|discriminate].
      destruct (rn_tree' f r g1) as [[r' g2]|w2] eqn:e2; [|discriminate].
      injection he as <- <-. exact (ihr _ _ _ (hf _ _ _ _ hg e1) e2).
    - destruct (rn_tree' f l g) as [[l' g1]|w1] eqn:e1; [|discriminate].
      injection he as <- <-. exact (ihl _ _ _ hg e1).
    - destruct (rn_tree' f l g) as [[l' g1]|w1] eqn:e1; [|discriminate].
      destruct (rn_tree' f r g1) as [[r' g2]|w2] eqn:e2; [|discriminate].
      injection he as <- <-. exact (ihr _ _ _ (ihl _ _ _ hg e1) e2).
    - destruct (rn_tree' f l g) as [[l' g1]|w1] eqn:e1; [|discriminate].
      destruct (f x g1) as [[x' g2]|w2] eqn:e2; [|discriminate].
      injection he as <- <-. exact (hf _ _ _ _ (ihl _ _ _ hg e1) e2).
    - destruct (rn_tree' f l g) as [[l' g1]|w1] eqn:e1; [|discriminate].
      destruct (f x g1) as [[x' g2]|w2] eqn:e2; [|discriminate].
      destruct (rn_tree' f r g2) as [[r' g3]|w3] eqn:e3; [|discriminate].
      injection he as <- <-. exact (ihr _ _ _ (hf _ _ _ _ (ihl _ _ _ hg e1) e2) e3).
  Qed.

  Lemma rn_ptree_wf m g m' g' : Pg g -> rn_ptree f m g = COk (m', g') -> Pg g'.
  Proof.
    intros hg he. destruct m as [|m]; unfold rn_ptree in he.
    - injection he as <- <-. exact hg.
    - destruct (rn_tree' f m g) as [[m1 g1]|w1] eqn:e1; [|discriminate].
      injection he as <- <-. exact (rn_tree'_wf _ _ _ _ hg e1).
  Qed.
End RenameWf.

(** ** A collection, and an allocation *)

(** Every cell [bh_get] finds in the old and in the new heap of a collection. *)
Definition gcw (Q : nat) (g : gc_state) : Prop :=
  (forall a cl, bh_get a g.(g_old) = Some cl -> cwf Q cl)
  /\ (forall a cl, bh_get a g.(g_heap) = Some cl -> cwf Q cl).

Lemma gc_copy_step Q (cp : haddr -> gc_state -> cbn_res (haddr * gc_state)) a x g cl cl1 g1 old n :
  (forall a g a' g', gcw Q g -> cp a g = COk (a', g') -> gcw Q g') ->
  gcw Q g -> cwf Q cl -> rn_cell cp cl g = COk (cl1, g1) ->
  bh_upd a (CFwd x) g1.(g_old) = Some old ->
  gcw Q (mkGc old (bh_cons cl1 g1.(g_heap)) n).
Proof.
  intros hcp hg hcl he hu.
  destruct (rn_cell_wf cp (gcw Q) hcp Q _ _ _ _ hg he) as [[ho hh] hc1].
  split; cbn [g_old g_heap].
  - intros b cl' hb. destruct (haddr_dec b a) as [-> | hne].
    + rewrite (bh_get_upd_same _ _ _ _ hu) in hb. injection hb as <-. exact I.
    + rewrite (bh_get_upd_other _ _ _ _ _ hu hne) in hb. exact (ho b cl' hb).
  - intros b cl' hb.
    destruct (bh_get_cons_any cl1 cl' _ b hb) as [-> | hb']; [exact (hc1 hcl)|exact (hh b cl' hb')].
Qed.

Lemma gc_copy_wf Q : forall f a g a' g', gcw Q g -> gc_copy f a g = COk (a', g') -> gcw Q g'.
Proof.
  intros f. induction f as [|k ih]; intros a g a' g' hg he.
  - rewrite gc_copy_FO in he.
    destruct (bh_get a g.(g_old)) as [[| | |b]|]; try discriminate he.
    injection he as <- <-. exact hg.
  - rewrite gc_copy_FS in he.
    destruct (bh_get a g.(g_old)) as [cl|] eqn:ea; [|discriminate he].
    pose proof (proj1 hg a cl ea) as hcl.
    assert (hcp : forall a g a' g', gcw Q g -> gc_copy (k tt) a g = COk (a', g') -> gcw Q g')
      by (intros; eapply ih; eassumption).
    destruct cl as [vs n o c|v| |b].
    4: injection he as <- <-; exact hg.
    all: lazymatch type of he with
         | context [rn_cell ?cp ?cl0 ?g0] =>
           destruct (rn_cell cp cl0 g0) as [[cl1 g1]|w] eqn:e1; [|discriminate he]
         end;
         lazymatch type of he with
         | context [bh_upd ?a0 ?x0 ?o0] =>
           destruct (bh_upd a0 x0 o0) as [old|] eqn:e2; [|discriminate he]
         end;
         injection he as <- <-;
         exact (gc_copy_step Q _ _ _ _ _ _ _ _ _ hcp hg hcl e1 e2).
Qed.

Lemma collect_wf Q rs s rs' s' :
  collect rs s = COk (rs', s') ->
  hwf Q s -> Forall (rwf Q) rs -> hwf Q s' /\ Forall (rwf Q) rs'.
Proof.
  intros he hs hrs. rewrite collect_eq in he.
  set (cp := gc_copy (fuel_of_pos s.(st_next) (fun _ => FO))) in he.
  assert (hcp : forall a g a' g', gcw Q g -> cp a g = COk (a', g') -> gcw Q g')
    by (intros; eapply gc_copy_wf; eassumption).
  assert (hg0 : gcw Q (mkGc s.(st_heap) (bh_holes s.(st_next)) s.(st_next))).
  { split; cbn [g_old g_heap].
    - exact hs.
    - intros a cl ha. rewrite bh_get_holes in ha. discriminate ha. }
  destruct (rn_ptree cp s.(st_gam) (mkGc s.(st_heap) (bh_holes s.(st_next)) s.(st_next)))
    as [[gm g1]|w] eqn:e1; [|discriminate he].
  destruct (rn_roots cp rs g1) as [[rs2 g2]|w] eqn:e2; [|discriminate he].
  injection he as <- <-.
  pose proof (rn_ptree_wf cp (gcw Q) hcp _ _ _ _ hg0 e1) as hg1.
  destruct (rn_roots_wf cp (gcw Q) hcp Q _ _ _ _ hg1 e2) as [hg2 hr2].
  split; [|exact (hr2 hrs)].
  intros a cl ha. exact (proj2 hg2 a cl ha).
Qed.

Lemma alloc_wf stress Q cl rs s a rs' s' :
  alloc stress cl rs s = COk (a, rs', s') ->
  hwf Q s -> cwf Q cl -> Forall (rwf Q) rs -> hwf Q s' /\ Forall (rwf Q) rs'.
Proof.
  intros he hs hc hrs. destruct (gc_due stress s) eqn:eg.
  - rewrite (alloc_gc stress cl rs s eg) in he.
    destruct (collect (RC cl :: rs) s) as [[rs2 s2]|w] eqn:ec; [|discriminate he].
    destruct (collect_wf Q _ _ _ _ ec hs (Forall_cons (RC cl) hc hrs)) as [hs2 hr2].
    destruct rs2 as [|[| | | | | |cl2] rs2]; try discriminate he.
    injection he as <- <- <-.
    split; [exact (hwf_alloc_now Q cl2 s2 hs2 (rwf_hd _ _ _ hr2))|exact (rwf_tl _ _ _ hr2)].
  - rewrite (alloc_no_gc stress cl rs s eg) in he. injection he as <- <- <-.
    split; [exact (hwf_alloc_now Q cl s hs hc)|exact hrs].
Qed.

(** The interface [alloc_hwf] of [PCUICCallByNeedSoundLevel]. *)
Lemma alloc_hwf_holds nctx stress : alloc_hwf nctx stress.
Proof.
  intros Q cl rs s a rs' s' _ hs hc hrs he. exact (alloc_wf stress Q cl rs s a rs' s' he hs hc hrs).
Qed.

(** ** The machine *)

(** The first call whose answer [he] matches on: its answer is [COk (x, y, z)], named by [e]. *)
Local Ltac dcall he e x y z :=
  lazymatch type of he with
  | context [match ?t with COk _ => _ | CFail _ => _ end] =>
      destruct t as [[[x y] z]|?] eqn:e; [|discriminate he]
  end.

(** The roots a call is given: the roots held, or new ones without a value or cell. *)
Local Ltac rok :=
  first [ assumption
        | match goal with h : Forall (rwf _) (_ :: ?l) |- Forall (rwf _) ?l =>
            exact (rwf_tl _ _ _ h) end
        | match goal with h : Forall (rwf _) (_ :: _ :: ?l) |- Forall (rwf _) ?l =>
            exact (rwf_tl _ _ _ (rwf_tl _ _ _ h)) end
        | apply Forall_cons; [first [exact I|assumption]|rok]
        | apply Forall_nil ].

(** The decisions of a match or projection on a constructor: each test that fails fails. *)
Local Ltac dtests he :=
  repeat (match type of he with
          | context [if ?b then _ else _] => destruct b
          | context [match ?o with Some _ => _ | None => _ end] => destruct o
          | context [match ?m with O => _ | S _ => _ end] => destruct m
          end; try discriminate he).

Section Machine.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat) (stress : bool).
  Context (hlen : #|Γ| <= nctx) (Q : nat) (hQ : nctx <= Q).

  Lemma tick_wf s s' : tick s = Some s' -> hwf Q s -> hwf Q s'.
  Proof. intros he. apply hwf_heap. exact (proj1 (tick_shape s s' he)). Qed.

  Lemma delta_wf kn u s r s' : delta X_type X kn u s = COk (r, s') -> hwf Q s -> hwf Q s'.
  Proof. intros he. apply hwf_heap. exact (proj1 (delta_shape X_type X kn u s r s' he)). Qed.

  Lemma gam_wf j rs s a rs' s' :
    gam X_type X Γ nctx stress j rs s = COk (a, rs', s') ->
    hwf Q s -> Forall (rwf Q) rs -> hwf Q s' /\ Forall (rwf Q) rs'.
  Proof.
    intros he hs hrs. unfold gam in he. cbv zeta in he.
    destruct (PTree.get (key_of_succ_nat j) s.(st_gam)) as [a0|].
    { injection he as <- <- <-. split; assumption. }
    destruct (nth_error Γ j) as [decl|] eqn:ed; [|discriminate he].
    assert (hj : j < nctx) by (pose proof (nth_error_Some_length ed); lia).
    destruct (decl_body decl) as [b|].
    - destruct (new_entry X_type X b [] (NSCtx j) s) as [c s1] eqn:en.
      cbv beta iota in he.
      assert (hs1 : hwf Q s1).
      { apply (hwf_heap Q s s1); [|exact hs].
        change s1 with (snd (c, s1)). rewrite <- en.
        exact (proj1 (new_entry_shape X_type X b [] (NSCtx j) s)). }
      dcall he ea a1 rs1 s2.
      injection he as <- <- <-.
      destruct (alloc_wf _ _ _ _ _ _ _ _ ea hs1 I hrs) as [hs2 hr2].
      split; [exact (hwf_heap Q s2 _ eq_refl hs2)|exact hr2].
    - cbv beta iota in he. dcall he ea a1 rs1 s2.
      injection he as <- <- <-.
      assert (hc : cwf Q (CDone (VNeu (NVar (nctx - S j)) []))) by (cbn; lia).
      destruct (alloc_wf _ _ _ _ _ _ _ _ ea hs hc hrs) as [hs2 hr2].
      split; [exact (hwf_heap Q s2 _ eq_refl hs2)|exact hr2].
  Qed.

  Lemma env_var_wf n e rs s x rs' s' :
    env_var X_type X Γ nctx stress n e rs s = COk (x, rs', s') ->
    hwf Q s -> Forall (rwf Q) rs -> hwf Q s' /\ Forall (rwf Q) rs'.
  Proof.
    intros he hs hrs. unfold env_var in he.
    destruct (nth_error e.(ev_vals) n) as [y|].
    - injection he as <- <- <-. split; assumption.
    - dcall he eg a1 rs1 s1. injection he as <- <- <-. exact (gam_wf _ _ _ _ _ _ eg hs hrs).
  Qed.

  Lemma arg_slot_wf e c rs s x rs' s' :
    arg_slot X_type X Γ nctx stress e c rs s = COk (x, rs', s') ->
    hwf Q s -> Forall (rwf Q) rs -> hwf Q s' /\ Forall (rwf Q) rs'.
  Proof.
    intros he hs hrs. unfold arg_slot in he.
    destruct (c_term c); try (injection he as <- <- <-; split; assumption).
    exact (env_var_wf _ _ _ _ _ _ _ he hs hrs).
  Qed.

  Lemma materialize_wf x rs s a rs' s' :
    materialize X_type X stress x rs s = COk (a, rs', s') ->
    hwf Q s -> Forall (rwf Q) rs -> hwf Q s' /\ Forall (rwf Q) rs'.
  Proof.
    intros he hs hrs. unfold materialize in he.
    destruct x as [a0|vs n o c]; [injection he as <- <- <-; split; assumption|].
    destruct (c_term c) eqn:ec; try exact (alloc_wf _ _ _ _ _ _ _ _ he hs I hrs).
    - (* tConst: an axiom is a neutral whose head is the code, closed *)
      lazymatch type of he with
      | context [delta X_type X ?kn ?ui s] =>
        destruct (delta X_type X kn ui s) as [[[c'|] s1]|w] eqn:ed
      end.
      + exact (alloc_wf _ _ _ _ _ _ _ _ he (delta_wf _ _ _ _ _ ed hs) I hrs).
      + exact (alloc_wf _ _ _ _ _ _ _ _ he (delta_wf _ _ _ _ _ ed hs) eq_refl hrs).
      + exact (alloc_wf _ _ _ _ _ _ _ _ he hs I hrs).
    - (* tFix *)
      lazymatch type of he with
      | context [nth_error ?m ?i] => destruct (nth_error m i)
      end; exact (alloc_wf _ _ _ _ _ _ _ _ he hs I hrs).
  Qed.

  Lemma bind_wf x body rs s y rs' s' :
    bind X_type X stress x body rs s = COk (y, rs', s') ->
    hwf Q s -> Forall (rwf Q) rs -> hwf Q s' /\ Forall (rwf Q) rs'.
  Proof.
    intros he hs hrs. unfold bind in he. destruct x as [a0|vals n o c].
    - injection he as <- <- <-. split; assumption.
    - destruct (once_body body s) as [b s1] eqn:eo.
      assert (hs1 : hwf Q s1).
      { apply (hwf_heap Q s s1); [|exact hs].
        change s1 with (snd (b, s1)). rewrite <- eo. exact (proj1 (once_body_shape body s)). }
      destruct b.
      + injection he as <- <- <-. split; assumption.
      + dcall he em a1 rs1 s2. injection he as <- <- <-.
        exact (materialize_wf _ _ _ _ _ _ em hs1 hrs).
  Qed.

  Lemma mat_all_wf : forall d l rs s al rs' s',
    mat_all X_type X stress d l rs s = COk (al, rs', s') ->
    hwf Q s -> Forall (rwf Q) rs -> hwf Q s' /\ Forall (rwf Q) rs'.
  Proof.
    intros d. induction d as [|k ih]; intros l rs s al rs' s' he hs hrs;
      destruct l as [|x l]; cbn [mat_all] in he.
    1,3: injection he as <- <- <-; split; assumption.
    - discriminate he.
    - dcall he em a1 rs1 s1.
      destruct rs1 as [|[| | | |l1| |] rs1]; try discriminate he.
      destruct (materialize_wf _ _ _ _ _ _ em hs ltac:(rok)) as [hs1 hr1].
      dcall he em2 al1 rs2 s2.
      destruct rs2 as [|[a0| | | | | |] rs2]; try discriminate he.
      injection he as <- <- <-.
      destruct (ih tt _ _ _ _ _ _ em2 hs1 ltac:(rok)) as [hs2 hr2].
      split; [exact hs2|exact (rwf_tl _ _ _ hr2)].
  Qed.

  Lemma push_fix_cells_wf : forall n e c i acc rs s e' rs' s',
    push_fix_cells stress e c i n acc rs s = COk (e', rs', s') ->
    hwf Q s -> Forall (rwf Q) rs -> hwf Q s' /\ Forall (rwf Q) rs'.
  Proof.
    induction n as [|n ih]; intros e c i acc rs s e' rs' s' he hs hrs;
      cbn [push_fix_cells] in he.
    - injection he as <- <- <-. split; assumption.
    - dcall he ea a1 rs1 s1.
      destruct rs1 as [|[| |e1| | | |] [|[| |acc1| | | |] rs1]]; try discriminate he.
      destruct (alloc_wf _ _ _ _ _ _ _ _ ea hs I ltac:(rok)) as [hs1 hr1].
      exact (ih _ _ _ _ _ _ _ _ _ he hs1 ltac:(rok)).
  Qed.

  (** The five functions of the machine at one fuel. *)
  Definition mwf (d : cbn_fuel) : Prop :=
    (forall a rs s v rs' s',
       force X_type X Γ nctx stress d a rs s = COk (v, rs', s') ->
       hwf Q s -> Forall (rwf Q) rs -> hwf Q s' /\ Forall (rwf Q) rs' /\ vwf Q v)
    /\ (forall x stk rs s v rs' s',
       eval_slot X_type X Γ nctx stress d x stk rs s = COk (v, rs', s') ->
       hwf Q s -> Forall (rwf Q) rs -> hwf Q s' /\ Forall (rwf Q) rs' /\ vwf Q v)
    /\ (forall e c stk rs s v rs' s',
       whnf X_type X Γ nctx stress d e c stk rs s = COk (v, rs', s') ->
       hwf Q s -> Forall (rwf Q) rs -> hwf Q s' /\ Forall (rwf Q) rs' /\ vwf Q v)
    /\ (forall e c mfix idx stk rs s v rs' s',
       whnf_fix X_type X Γ nctx stress d e c mfix idx stk rs s = COk (v, rs', s') ->
       hwf Q s -> Forall (rwf Q) rs -> hwf Q s' /\ Forall (rwf Q) rs' /\ vwf Q v)
    /\ (forall v stk rs s w rs' s',
       apply X_type X Γ nctx stress d v stk rs s = COk (w, rs', s') ->
       hwf Q s -> Forall (rwf Q) rs -> vwf Q v ->
       hwf Q s' /\ Forall (rwf Q) rs' /\ vwf Q w).

  Lemma machine_wf : forall d, mwf d.
  Proof.
    intros d. induction d as [|k ih].
    - (* FO: every call fails, except [apply] with an empty stack *)
      split; [|split; [|split; [|split]]].
      + intros a rs s v rs' s' he. cbn [force] in he. discriminate he.
      + intros x stk rs s v rs' s' he. cbn [eval_slot] in he. discriminate he.
      + intros e c stk rs s v rs' s' he. cbn [whnf] in he. discriminate he.
      + intros e c mfix idx stk rs s v rs' s' he. cbn [whnf_fix] in he. discriminate he.
      + intros v stk rs s w rs' s' he hs hrs hv. cbn [apply] in he.
        destruct stk; [injection he as <- <- <-; split; [|split]; assumption|discriminate he].
    - destruct (ih tt) as (IHf & IHs & IHw & IHx & IHa).
      split; [|split; [|split; [|split]]].
      + (* force *)
        intros a0 rs0 s0 v0 rs' s' he hs hrs.
        cbv beta iota zeta delta [force] in he.
        destruct (heap_get a0 s0) as [cl|] eqn:ehc; [|discriminate he].
        destruct cl as [vs n o c|vd| |b]; try discriminate he.
        * (* a suspension: evaluate it, then write the value back *)
          destruct (heap_upd a0 CBusy s0) as [sb|] eqn:ebusy; [|discriminate he].
          dcall he ew vw rsw sw.
          destruct rsw as [|[ar| | | | | |] rsw]; try discriminate he.
          destruct (heap_upd ar (CDone vw) sw) as [sd|] eqn:edone; [|discriminate he].
          injection he as <- <- <-.
          pose proof (hwf_upd Q a0 CBusy s0 sb hs I ebusy) as hsb.
          destruct (IHw _ _ _ _ _ _ _ _ ew hsb ltac:(rok)) as (hsw & hrw & hvw).
          split; [exact (hwf_upd Q ar (CDone vw) sw sd hsw hvw edone)|].
          split; [exact (rwf_tl _ _ _ hrw)|exact hvw].
        * (* a value: the heap has it *)
          injection he as <- <- <-. split; [exact hs|]. split; [exact hrs|exact (hs a0 _ ehc)].
      + (* eval_slot *)
        intros x stk rs0 s0 v0 rs' s' he hs hrs.
        cbv beta iota zeta delta [eval_slot] in he.
        destruct x as [a|vs n o c].
        * dcall he ef vf rsf sf.
          destruct rsf as [|[| | | |lk| |] rsf]; try discriminate he.
          destruct (IHf _ _ _ _ _ _ ef hs ltac:(rok)) as (hsf & hrf & hvf).
          exact (IHa _ _ _ _ _ _ _ he hsf ltac:(rok) hvf).
        * exact (IHw _ _ _ _ _ _ _ _ he hs hrs).
      + (* whnf *)
        intros e c stk rs0 s0 v0 rs' s' he hs0 hrs.
        cbv beta iota zeta delta [whnf] in he.
        destruct (tick s0) as [st|] eqn:etick; [|discriminate he].
        pose proof (tick_wf _ _ etick hs0) as hs. clear hs0.
        destruct (c_term c) as [n|vr|ev earg|srt|na A B|na A b|na b T body|f arg|kn ui
                               |ind ui|ind n ui|ci p scrut brs|pr arg|mfix idx|cmfix cidx|prm]
          eqn:ec; try solve [discriminate he].
        * (* tRel *)
          dcall he ev xr rsr sr.
          destruct rsr as [|[| | | |lk| |] rsr]; try discriminate he.
          destruct (env_var_wf _ _ _ _ _ _ _ ev hs ltac:(rok)) as [hsr hrr].
          exact (IHs _ _ _ _ _ _ _ he hsr ltac:(rok)).
        * (* tSort *)
          destruct stk; [|discriminate he]. injection he as <- <- <-.
          split; [exact hs|]. split; [exact hrs|exact I].
        * (* tProd *)
          destruct stk; [|discriminate he]. injection he as <- <- <-.
          split; [exact hs|]. split; [exact hrs|exact I].
        * (* tLambda *)
          destruct stk as [|xh stk'].
          -- injection he as <- <- <-. split; [exact hs|]. split; [exact hrs|exact I].
          -- dcall he eb xb rsb sb.
             destruct rsb as [|[| |e1| | | |] [|[| | | |k1| |] rsb]]; try discriminate he.
             destruct (bind_wf _ _ _ _ _ _ _ eb hs ltac:(rok)) as [hsb hrb].
             exact (IHw _ _ _ _ _ _ _ _ he hsb ltac:(rok)).
        * (* tLetIn *)
          dcall he ea xa rsa sa.
          destruct rsa as [|[| |e1| | | |] [|[| | | |k1| |] rsa]]; try discriminate he.
          destruct (arg_slot_wf _ _ _ _ _ _ _ ea hs ltac:(rok)) as [hsa hra].
          dcall he eb xb rsb sb.
          destruct rsb as [|[| |e2| | | |] [|[| | | |k2| |] rsb]]; try discriminate he.
          destruct (bind_wf _ _ _ _ _ _ _ eb hsa ltac:(rok)) as [hsb hrb].
          exact (IHw _ _ _ _ _ _ _ _ he hsb ltac:(rok)).
        * (* tApp *)
          dcall he ea xa rsa sa.
          destruct rsa as [|[| |e1| | | |] [|[| | | |k1| |] rsa]]; try discriminate he.
          destruct (arg_slot_wf _ _ _ _ _ _ _ ea hs ltac:(rok)) as [hsa hra].
          exact (IHw _ _ _ _ _ _ _ _ he hsa ltac:(rok)).
        * (* tConst: delta, or a neutral whose head is the code *)
          destruct (delta X_type X kn ui st) as [[r s1]|w] eqn:ed; [|discriminate he].
          pose proof (delta_wf _ _ _ _ _ ed hs) as hs1.
          destruct r as [c'|].
          -- exact (IHw _ _ _ _ _ _ _ _ he hs1 hrs).
          -- dcall he em sp rs1 s2.
             destruct (mat_all_wf _ _ _ _ _ _ _ em hs1 hrs) as [hs2 hr2].
             injection he as <- <- <-. split; [exact hs2|]. split; [exact hr2|].
             first [reflexivity|rewrite ec; reflexivity].
        * (* tInd: a constructor value whose head is the code *)
          dcall he em sp rs1 s1.
          destruct (mat_all_wf _ _ _ _ _ _ _ em hs hrs) as [hs1 hr1].
          injection he as <- <- <-. split; [exact hs1|]. split; [exact hr1|].
          first [reflexivity|rewrite ec; reflexivity].
        * (* tConstruct *)
          dcall he em sp rs1 s1.
          destruct (mat_all_wf _ _ _ _ _ _ _ em hs hrs) as [hs1 hr1].
          injection he as <- <- <-. split; [exact hs1|]. split; [exact hr1|].
          first [reflexivity|rewrite ec; reflexivity].
        * (* tCase *)
          dcall he ewc vc rsc sc.
          destruct rsc as [|[| |e1| | | |] [|[| | | |k1| |] rsc]]; try discriminate he.
          destruct (IHw _ _ _ _ _ _ _ _ ewc hs ltac:(rok)) as (hsc & hrc & _).
          destruct vc as [h sp| | | |nn sp| |]; try discriminate he.
          1: { destruct h; try discriminate he. dtests he.
               exact (IHw _ _ _ _ _ _ _ _ he hsc ltac:(rok)). }
          all: dcall he em sp1 rsm sm;
               destruct rsm as [|[| |e5| | | |] rsm]; try discriminate he;
               destruct (mat_all_wf _ _ _ _ _ _ _ em hsc ltac:(rok)) as [hsm hrm];
               injection he as <- <- <-;
               split; [exact hsm|]; split; [exact (rwf_tl _ _ _ hrm)|exact I].
        * (* tProj *)
          dcall he ewc vc rsc sc.
          destruct rsc as [|[| |e1| | | |] [|[| | | |k1| |] rsc]]; try discriminate he.
          destruct (IHw _ _ _ _ _ _ _ _ ewc hs ltac:(rok)) as (hsc & hrc & _).
          destruct vc as [h sp| | | |nn sp| |]; try discriminate he.
          1: { destruct h; try discriminate he. dtests he.
               exact (IHs _ _ _ _ _ _ _ he hsc ltac:(rok)). }
          all: dcall he em sp1 rsm sm;
               destruct rsm as [|[| |e5| | | |] rsm]; try discriminate he;
               destruct (mat_all_wf _ _ _ _ _ _ _ em hsc ltac:(rok)) as [hsm hrm];
               injection he as <- <- <-;
               split; [exact hsm|]; split; [exact (rwf_tl _ _ _ hrm)|exact I].
        * (* tFix *)
          exact (IHx _ _ _ _ _ _ _ _ _ _ he hs hrs).
        * (* tPrim *)
          destruct stk; [|discriminate he]. injection he as <- <- <-.
          split; [exact hs|]. split; [exact hrs|exact I].
      + (* whnf_fix *)
        intros e c mfix idx stk rs0 s0 v0 rs' s' he hs hrs.
        cbv beta iota zeta delta [whnf_fix] in he.
        destruct (nth_error mfix idx) as [def|]; [|discriminate he].
        destruct (nth_error stk (rarg def)) as [x|].
        * dcall he ea a1 rs1 s1.
          destruct rs1 as [|[| |e1| | | |] [|[| | | |k1| |] rs1]]; try discriminate he.
          destruct (materialize_wf _ _ _ _ _ _ ea hs ltac:(rok)) as [hs1 hr1].
          dcall he ef vf rsf sf.
          destruct rsf as [|[| |e2| | | |] [|[| | | |k2| |] rsf]]; try discriminate he.
          destruct (IHf _ _ _ _ _ _ ef hs1 ltac:(rok)) as (hsf & hrf & hvf).
          destruct vf as [h sp| | | |nn sp| |]; try discriminate he.
          1: { (* the guard holds: the forced constructor goes to a fresh cell *)
               destruct h; try discriminate he.
               dcall he ea2 a2 rs2 s2.
               destruct rs2 as [|[| |e3| | | |] [|[| | | |k3| |] rs2]]; try discriminate he.
               destruct (alloc_wf _ _ _ _ _ _ _ _ ea2 hsf hvf ltac:(rok)) as [hs2 hr2].
               dcall he ep e4 rs3 s3.
               destruct rs3 as [|[| | | |k4| |] rs3]; try discriminate he.
               destruct (push_fix_cells_wf _ _ _ _ _ _ _ _ _ _ ep hs2 ltac:(rok)) as [hs3 hr3].
               exact (IHw _ _ _ _ _ _ _ _ he hs3 ltac:(rok)). }
          all: dcall he em sp1 rsm sm;
               destruct rsm as [|[| |e5| | | |] rsm]; try discriminate he;
               destruct (mat_all_wf _ _ _ _ _ _ _ em hsf ltac:(rok)) as [hsm hrm];
               injection he as <- <- <-;
               split; [exact hsm|]; split; [exact (rwf_tl _ _ _ hrm)|exact I].
        * dcall he em sp rs1 s1.
          destruct rs1 as [|[| |e1| | | |] rs1]; try discriminate he.
          destruct (mat_all_wf _ _ _ _ _ _ _ em hs ltac:(rok)) as [hs1 hr1].
          injection he as <- <- <-.
          split; [exact hs1|]. split; [exact (rwf_tl _ _ _ hr1)|exact I].
      + (* apply *)
        intros v stk rs0 s0 w rs' s' he hs hrs hv.
        cbv beta iota zeta delta [apply] in he.
        destruct stk as [|y stk']; [injection he as <- <- <-; split; [|split]; assumption|].
        destruct v as [h sp|e c|e c idx sp|e c idx sp|nn sp|e c|e c sp]; try discriminate he.
        2: { (* a lambda: beta *)
             destruct (c_term c); try discriminate he.
             dcall he eb xb rsb sb.
             destruct rsb as [|[| |e1| | | |] [|[| | | |k1| |] rsb]]; try discriminate he.
             destruct (bind_wf _ _ _ _ _ _ _ eb hs ltac:(rok)) as [hsb hrb].
             exact (IHw _ _ _ _ _ _ _ _ he hsb ltac:(rok)). }
        2: { (* a fixpoint: its spine goes back on the stack *)
             destruct (c_term c); try discriminate he.
             exact (IHx _ _ _ _ _ _ _ _ _ _ he hs hrs). }
        all: (* the spine grows *)
             dcall he em sp1 rsm sm;
             destruct rsm as [|[| | |v1| | |] rsm]; try discriminate he;
             destruct (mat_all_wf _ _ _ _ _ _ _ em hs ltac:(rok)) as [hsm hrm];
             destruct (add_spine v1 sp1) as [v2|] eqn:eadd; [|discriminate he];
             injection he as <- <- <-;
             split; [exact hsm|]; split; [exact (rwf_tl _ _ _ hrm)|];
             exact (add_spine_wf _ _ _ _ (rwf_hd _ _ _ hrm) eadd).
  Qed.
End Machine.

(** The interface [machine_hwf] of [PCUICCallByNeedSoundLevel], for every context no longer
  than [nctx]. *)
Lemma machine_hwf_holds {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1)
    (Γ : context) (nctx : nat) (stress : bool) (hlen : #|Γ| <= nctx) :
  machine_hwf X_type X Γ nctx stress.
Proof.
  intros d Q hQ.
  destruct (machine_wf X_type X Γ nctx stress hlen Q hQ d) as (hf & hs & hw & hx & ha).
  split; [|split; [|split; [|split]]].
  - intros a rs s v rs' s' h1 h2 he. exact (hf _ _ _ _ _ _ he h1 h2).
  - intros x stk rs s v rs' s' h1 h2 he. exact (hs _ _ _ _ _ _ _ he h1 h2).
  - intros e c stk rs s v rs' s' h1 h2 he. exact (hw _ _ _ _ _ _ _ _ he h1 h2).
  - intros e c mfix idx stk rs s v rs' s' h1 h2 he. exact (hx _ _ _ _ _ _ _ _ _ _ he h1 h2).
  - intros v stk rs s w rs' s' h1 h2 h3 he. exact (ha _ _ _ _ _ _ _ he h1 h2 h3).
Qed.

(** The instance the machine runs at: [cbn_conv_answer] takes [nctx = #|Γ|]. *)
Lemma machine_hwf_run {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1)
    (Γ : context) (stress : bool) : machine_hwf X_type X Γ #|Γ| stress.
Proof. exact (machine_hwf_holds X_type X Γ #|Γ| stress (le_n _)). Qed.

(** The premise [#|Γ| <= nctx] is needed: with [nctx = 0], one assumption in [Γ] and the
  master level [0], the variable [tRel 0] evaluates to [NVar 0], which is not below [0]. *)
Lemma machine_hwf_needs_len {cf : checker_flags} (X_type : abstract_env_impl)
    (X : X_type.π2.π1) (stress : bool) :
  ~ machine_hwf X_type X [jdecl] 0 stress.
Proof.
  intros h.
  destruct (h (FS (fun _ => FS (fun _ => FS (fun _ => FO)))) 0 (le_n 0))
    as (_ & _ & hw & _ & _).
  assert (hs0 : hwf 0 cbn_init).
  { intros a cl ha. unfold heap_get in ha. cbn [cbn_init st_heap] in ha.
    rewrite bh_get_holes in ha. discriminate ha. }
  assert (E : exists s', whnf X_type X [jdecl] 0 stress
                           (FS (fun _ => FS (fun _ => FS (fun _ => FO))))
                           env_empty (mkCode path_nil path_nil (tRel 0)) [] [] cbn_init
                         = COk (VNeu (NVar 0) [], [], s')).
  { destruct stress; eexists; reflexivity. }
  destruct E as [s' E].
  destruct (hw _ _ _ _ _ _ _ _ hs0 (Forall_nil _) E) as (_ & _ & hv).
  cbn in hv. lia.
Qed.

(** ** The machine at the master level, with the interface discharged *)

Section MasterProved.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat) (stress : bool) (Σ : global_env_ext).
  Context (wfΣ : wf Σ) (hΣ : abstract_env_ext_rel X Σ) (hnctx : nctx = #|Γ|).
  Context (hcio : forall j decl b, nth_error Γ j = Some decl -> decl.(decl_body) = Some b ->
                    PCUICCallByNeedSoundHook.consts_okb Σ b).

  Lemma machine_hwf_master : machine_hwf X_type X Γ nctx stress.
  Proof. apply machine_hwf_holds. rewrite hnctx. apply le_n. Qed.

  Lemma whnf_master_hwf d L Q lo G e c stk sts tc rs s v rs' s' :
    minv X_type X Γ nctx Σ L Q lo G s -> Forall (rwf Q) rs ->
    g_susp nctx Q G e c.(c_term) tc -> PCUICCallByNeedSoundEval.cok G c ->
    g_slots nctx Q G stk sts ->
    whnf X_type X Γ nctx stress d e c stk rs s = COk (v, rs', s') ->
    exists lo' G' u, minv X_type X Γ nctx Σ L Q lo' G' s' /\ Forall (rwf Q) rs' /\ vwf Q v
      /\ gren nctx Q G G' rs rs' /\ g_value nctx Q G' v u
      /\ cred Γ Σ (jctx (Q - nctx)) (mkApps tc sts) u.
  Proof. exact (whnf_master X_type X Γ nctx stress Σ wfΣ hΣ hnctx hcio machine_hwf_master d L Q lo G e c stk sts tc rs s v rs' s'). Qed.

  Lemma eval_slot_master_hwf d L Q lo G x stk sts tx rs s v rs' s' :
    minv X_type X Γ nctx Σ L Q lo G s -> Forall (rwf Q) rs ->
    g_slot nctx Q G x tx -> g_slots nctx Q G stk sts ->
    eval_slot X_type X Γ nctx stress d x stk rs s = COk (v, rs', s') ->
    exists lo' G' u, minv X_type X Γ nctx Σ L Q lo' G' s' /\ Forall (rwf Q) rs' /\ vwf Q v
      /\ gren nctx Q G G' rs rs' /\ g_value nctx Q G' v u
      /\ cred Γ Σ (jctx (Q - nctx)) (mkApps tx sts) u.
  Proof. exact (eval_slot_master X_type X Γ nctx stress Σ wfΣ hΣ hnctx hcio machine_hwf_master d L Q lo G x stk sts tx rs s v rs' s'). Qed.
End MasterProved.
