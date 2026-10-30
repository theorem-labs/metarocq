(* Distributed under the terms of the MIT license. *)
(** ETA-COPY (wip/etak-cbne-2026-10-30) of integ-all8's [PCUICCallByNeedSoundHeapWf] (1a92b56c) over the η environment
    ([PCUICWfEnvEta], [PCUICCallByNeedEta]): see [PCUICCallByNeedEtaSoundHookProof] for what differs. *)
(** Declared shadow: this file declares [cbn_bh_scan_nil], and so does [PCUICCallByNeedEta] (a [Local Lemma], the same statement), as in base; the references to this file's lemma are written fully qualified (inside the open section HeapCons its full name carries the section). *)
From Stdlib Require Import BinPos BinNat Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require CanonicalTries.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping.
From MetaRocq.SafeChecker Require Import PCUICWfEnvEta PCUICCallByNeedEta PCUICCallByNeedEtaSound
  PCUICCallByNeedEtaSoundGC PCUICCallByNeedEtaSoundCtx PCUICCallByNeedEtaSoundEval.

Import CanonicalTries.

(** * The structural invariant of the heap, and the machine keeps it

  [cbn_hwf Q s]: no cell of the heap holds a fresh variable at a level [>= Q], and the head of
  every constructor and neutral constant value in it is closed ([cbn_vwf] of a value, [cbn_cwf] of a
  cell, [cbn_rwf] of a root). [PCUICCallByNeedEtaSoundLevel] needs it at the master level [Q] to
  raise that level ([cbn_gok_raise]). The ghost reading cannot see it, so its preservation is a
  separate theorem, proved here for two interfaces: [cbn_machine_hwf], every machine function
  keeps [cbn_hwf Q] of the heap, [cbn_rwf Q] of the roots and [cbn_vwf Q] of the value it returns,
  at any master level [Q >= nctx] ([cbn_machine_hwf_holds]); [cbn_alloc_hwf], so does an allocation
  of a cell that has it ([cbn_alloc_hwf_holds]).

  Why it holds: a fresh variable [CbnNVar l] is made only by [cbn_gam], at the level
  [nctx - S j] of an entry [j] of [Γ], so below [nctx] when [#|Γ| <= nctx]; the head of a
  [CbnVCon] or of a neutral constant comes only from a [tConstruct], [tInd] or [tConst] code,
  which is closed; every other value the machine builds copies existing structure ([cbn_add_spine],
  a collection's renaming) or has no head ([CbnVLam], [CbnVFix], [CbnVOpen], [CbnVStuck],
  [CbnVStuckFix]).

  The heap needs one law that holds for every digit list, not only the ones [cbn_bh_ok] describes,
  because [cbn_hwf] is stated over [cbn_heap_get] alone: a cell [cbn_bh_get] finds after
  [cbn_bh_cons] is the new cell or a cell it found before ([cbn_bh_get_cons_any]).

  [cbn_machine_hwf_holds] needs [#|Γ| <= nctx]; without it the interface is false
  ([cbn_machine_hwf_needs_len]): with [nctx = 0] and one assumption in [Γ], [cbn_gam] makes
  [CbnNVar 0], which is not below the master level [0]. The machine's runs have [nctx = #|Γ|]
  ([cbn_conv_answer]), which is how [PCUICCallByNeedEtaSoundLevel.cbn_whnf_master] and
  [cbn_eval_slot_master] use [cbn_machine_hwf_holds], and [cbn_machine_hwf_master] is that
  instance. *)

(** ** The invariant *)

Definition cbn_vwf (lvl : nat) (v : cbn_value) : Prop :=
  match v with
  | CbnVNeu (CbnNVar l) _ => l < lvl
  | CbnVNeu (CbnNConst h) _ | CbnVCon h _ => closedn 0 h
  | _ => True
  end.

Definition cbn_cwf (lvl : nat) (cl : cbn_cell) : Prop :=
  match cl with CbnCDone v => cbn_vwf lvl v | _ => True end.

Definition cbn_hwf (lvl : nat) (s : cbn_state) : Prop :=
  forall a cl, cbn_heap_get a s = Some cl -> cbn_cwf lvl cl.

Definition cbn_rwf (lvl : nat) (r : cbn_root) : Prop :=
  match r with CbnRV v => cbn_vwf lvl v | CbnRC cl => cbn_cwf lvl cl | _ => True end.

Lemma cbn_vwf_mono lvl lvl' v : lvl <= lvl' -> cbn_vwf lvl v -> cbn_vwf lvl' v.
Proof. intros hle. destruct v as [| | | |[l|h] sp| |]; cbn; try tauto; lia. Qed.

Lemma cbn_cwf_mono lvl lvl' cl : lvl <= lvl' -> cbn_cwf lvl cl -> cbn_cwf lvl' cl.
Proof. intros hle. destruct cl; cbn; try tauto. apply cbn_vwf_mono, hle. Qed.

Lemma cbn_hwf_mono lvl lvl' s : lvl <= lvl' -> cbn_hwf lvl s -> cbn_hwf lvl' s.
Proof. intros hle h a cl ha. exact (cbn_cwf_mono _ _ _ hle (h a cl ha)). Qed.

(** ** The heap: what [cbn_bh_cons] adds, for any digit list *)

Section HeapCons.
  Context {A : Type}.

  Definition cbn_bh_zeros (zs : cbn_bheap A) : Prop := Forall (fun d => d = CbnDZero) zs.

  Lemma cbn_bh_top_zeros zs acc cand : cbn_bh_zeros zs -> cbn_bh_top zs acc cand = cand.
  Proof.
    intros hz. revert acc cand.
    induction hz as [|d zs hd hz ih]; intros acc cand; [reflexivity|].
    subst d. cbn. apply ih.
  Qed.

  Lemma cbn_bh_top_app_zeros h zs acc cand :
    cbn_bh_zeros zs -> cbn_bh_top (h ++ zs) acc cand = cbn_bh_top h acc cand.
  Proof.
    intros hz. revert acc cand. induction h as [|d h ih]; intros acc cand; cbn.
    - apply cbn_bh_top_zeros. exact hz.
    - destruct d; apply ih.
  Qed.

  Lemma cbn_bh_scan_nil p acc cand : @cbn_bh_scan A p [] acc cand = None.
  Proof. destruct p; reflexivity. Qed.

  Lemma cbn_bh_scan_zeros p zs acc cand : cbn_bh_zeros zs -> cbn_bh_scan p zs acc cand = None.
  Proof.
    intros hz. revert p acc cand.
    induction hz as [|d zs hd hz ih]; intros p acc cand;
      [apply MetaRocq.SafeChecker.PCUICCallByNeedEtaSoundHeapWf.HeapCons.cbn_bh_scan_nil|].
    subst d. destruct p as [p|p|]; cbn.
    - apply ih.
    - apply ih.
    - apply cbn_bh_top_zeros. exact hz.
  Qed.

  Lemma cbn_bh_scan_app_zeros p h zs acc cand :
    cbn_bh_zeros zs -> cbn_bh_scan p (h ++ zs) acc cand = cbn_bh_scan p h acc cand.
  Proof.
    intros hz. revert p acc cand. induction h as [|d h ih]; intros p acc cand.
    - cbn [app]. rewrite (cbn_bh_scan_zeros p zs acc cand hz). symmetry.
      apply MetaRocq.SafeChecker.PCUICCallByNeedEtaSoundHeapWf.HeapCons.cbn_bh_scan_nil.
    - destruct p as [p|p|], d as [|t]; cbn [app cbn_bh_scan]; try apply ih;
        apply cbn_bh_top_app_zeros; exact hz.
  Qed.

  Lemma cbn_bh_get_app_zeros a h zs : cbn_bh_zeros zs -> cbn_bh_get a (h ++ zs) = cbn_bh_get a h.
  Proof.
    intros hz. unfold cbn_bh_get, cbn_bh_find. rewrite (cbn_bh_scan_app_zeros _ _ _ _ _ hz).
    reflexivity.
  Qed.

  Lemma cbn_bh_carry_app_zeros t h zs :
    cbn_bh_zeros zs -> exists zs', cbn_bh_zeros zs' /\
      cbn_bh_carry t (h ++ zs) = cbn_bh_carry t h ++ zs'.
  Proof.
    intros hz. revert t. induction h as [|d h ih]; intros t.
    - cbn [app]. destruct hz as [|d zs0 hd hz0].
      + exists []. split; [constructor|reflexivity].
      + subst d. exists zs0. split; [exact hz0|reflexivity].
    - destruct d as [|t'].
      + exists zs. split; [exact hz|reflexivity].
      + destruct (ih (CbnBNode t' t)) as (zs' & hz' & e). exists zs'. split; [exact hz'|].
        cbn [app cbn_bh_carry]. rewrite e. reflexivity.
  Qed.

  (** Every digit list is a list with digits, or the empty list, followed by zeros. *)
  Lemma cbn_bh_split (h : cbn_bheap A) :
    exists h0 zs, h = h0 ++ zs /\ cbn_bh_zeros zs /\ (h0 = [] \/ exists n, cbn_bh_digits h0 n).
  Proof.
    induction h as [|d h ih].
    - exists [], []. split; [reflexivity|]. split; [constructor|left; reflexivity].
    - destruct ih as (h0 & zs & -> & hz & [-> | (n & hn)]).
      + destruct d as [|t].
        * exists [], (CbnDZero :: zs). split; [reflexivity|].
          split; [constructor; [reflexivity|exact hz]|left; reflexivity].
        * exists [CbnDOne t], zs. split; [reflexivity|].
          split; [exact hz|right; exists xH; constructor].
      + exists (d :: h0), zs. split; [reflexivity|]. split; [exact hz|right].
        destruct d as [|t]; [exists (xO n)|exists (xI n)]; constructor; exact hn.
  Qed.

  (** The one cell of a single tree of depth 0 is address 0, which no address reaches. *)
  Lemma cbn_bh_get_one a (t : cbn_btree A) : cbn_bh_get a [CbnDOne t] = None.
  Proof.
    destruct a as [p]. unfold cbn_bh_get, cbn_bh_find. cbn [cbn_ha_p].
    destruct p as [p|p|]; cbn [cbn_bh_scan cbn_bh_top];
      rewrite ?MetaRocq.SafeChecker.PCUICCallByNeedEtaSoundHeapWf.HeapCons.cbn_bh_scan_nil; reflexivity.
  Qed.

  (** A cell [cbn_bh_get] finds after [cbn_bh_cons] is the new cell or one it found before. *)
  Lemma cbn_bh_get_cons_any (y x : A) h a :
    cbn_bh_get a (cbn_bh_cons y h) = Some x -> x = y \/ cbn_bh_get a h = Some x.
  Proof.
    destruct (cbn_bh_split h) as (h0 & zs & -> & hz & hh0).
    unfold cbn_bh_cons. destruct (cbn_bh_carry_app_zeros (CbnBLeaf y) h0 zs hz) as (zs' & hz' & ->).
    rewrite (cbn_bh_get_app_zeros a _ _ hz'), (cbn_bh_get_app_zeros a _ _ hz).
    change (cbn_bh_carry (CbnBLeaf y) h0) with (cbn_bh_cons y h0).
    destruct hh0 as [-> | (n & hn)].
    - change (cbn_bh_cons y []) with [CbnDOne (CbnBLeaf y)]. rewrite cbn_bh_get_one. intros h.
      discriminate h.
    - destruct (cbn_haddr_dec a (CbnHAddr n)) as [-> | hne].
      + rewrite (cbn_bh_digits_get_cons_new y h0 n hn). intros h. injection h as ->. left.
        reflexivity.
      + rewrite (cbn_bh_digits_get_cons_old y h0 n a hn hne). intros h. right. exact h.
  Qed.
End HeapCons.

(** ** The invariant over the state operations that keep the heap or write one cell *)

Lemma cbn_rwf_tl Q r rs : Forall (cbn_rwf Q) (r :: rs) -> Forall (cbn_rwf Q) rs.
Proof. intros h. inversion h; assumption. Qed.

Lemma cbn_rwf_hd Q r rs : Forall (cbn_rwf Q) (r :: rs) -> cbn_rwf Q r.
Proof. intros h. inversion h; assumption. Qed.

Lemma cbn_hwf_heap Q s s' : s'.(cbn_st_heap) = s.(cbn_st_heap) -> cbn_hwf Q s -> cbn_hwf Q s'.
Proof. intros he h a cl ha. unfold cbn_heap_get in ha. rewrite he in ha. exact (h a cl ha). Qed.

Lemma cbn_hwf_upd Q a cl s s' : cbn_hwf Q s -> cbn_cwf Q cl -> cbn_heap_upd a cl s = Some s' ->
  cbn_hwf Q s'.
Proof.
  intros h hc hu b cl' hb.
  destruct (cbn_haddr_dec b a) as [-> | hne].
  - rewrite (cbn_heap_get_upd_same a cl s s' hu) in hb. injection hb as <-. exact hc.
  - rewrite (cbn_heap_get_upd_other a b cl s s' hu hne) in hb. exact (h b cl' hb).
Qed.

Lemma cbn_hwf_alloc_now Q cl s : cbn_hwf Q s -> cbn_cwf Q cl ->
  cbn_hwf Q (snd (cbn_alloc_now cl s)).
Proof.
  intros h hc b cl' hb. unfold cbn_heap_get in hb. cbn [cbn_alloc_now snd cbn_st_heap] in hb.
  destruct (cbn_bh_get_cons_any cl cl' _ b hb) as [-> | hb']; [exact hc|exact (h b cl' hb')].
Qed.

Lemma cbn_add_spine_wf Q v l v' : cbn_vwf Q v -> cbn_add_spine v l = Some v' -> cbn_vwf Q v'.
Proof.
  intros hv he. destruct v; cbn in he; try discriminate he; injection he as <-; exact hv.
Qed.

(** ** A renaming keeps the heads and levels of what it renames *)

Section RenameWf.
  Context {G : Type} (f : cbn_haddr -> G -> cbn_res (cbn_haddr * G)) (Pg : G -> Prop)
    (hf : forall a g a' g', Pg g -> f a g = CbnCOk (a', g') -> Pg g').

  Lemma cbn_rn_addrs_wf : forall l g l' g', Pg g -> cbn_rn_addrs f l g = CbnCOk (l', g') -> Pg g'.
  Proof.
    induction l as [|a l ih]; intros g l' g' hg he; simpl in he.
    - injection he as <- <-. exact hg.
    - destruct (f a g) as [[b g1]|w] eqn:e1; [|discriminate].
      destruct (cbn_rn_addrs f l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
      injection he as <- <-. exact (ih _ _ _ (hf _ _ _ _ hg e1) e2).
  Qed.

  Lemma cbn_rn_slot_wf : forall x g x' g', Pg g -> cbn_rn_slot f x g = CbnCOk (x', g') -> Pg g'.
  Proof.
    intros x. induction x as [a|vs n o c ihvs] using cbn_slot_ind'; intros g x' g' hg he.
    - simpl in he. destruct (f a g) as [[b g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. exact (hf _ _ _ _ hg e1).
    - rewrite cbn_rn_slot_SInl in he.
      destruct (cbn_rn_slots f vs g) as [[vs' g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-.
      revert g vs' g1 hg e1.
      induction ihvs as [|y vs hy hvs ihl]; intros g vs' g1 hg e1; simpl in e1.
      + injection e1 as <- <-. exact hg.
      + destruct (cbn_rn_slot f y g) as [[y' ga]|wa] eqn:ea; [|discriminate].
        destruct (cbn_rn_slots f vs ga) as [[vs2 gb]|wb] eqn:eb; [|discriminate].
        injection e1 as <- <-. exact (ihl _ _ _ (hy _ _ _ hg ea) eb).
  Qed.

  Lemma cbn_rn_slots_wf : forall l g l' g', Pg g -> cbn_rn_slots f l g = CbnCOk (l', g') -> Pg g'.
  Proof.
    induction l as [|y l ih]; intros g l' g' hg he; simpl in he.
    - injection he as <- <-. exact hg.
    - destruct (cbn_rn_slot f y g) as [[y' g1]|w] eqn:e1; [|discriminate].
      destruct (cbn_rn_slots f l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
      injection he as <- <-. exact (ih _ _ _ (cbn_rn_slot_wf _ _ _ _ hg e1) e2).
  Qed.

  Lemma cbn_rn_env_wf e g e' g' : Pg g -> cbn_rn_env f e g = CbnCOk (e', g') -> Pg g'.
  Proof. intros hg he. exact (cbn_rn_slots_wf _ _ _ _ hg (cbn_rn_env_vals _ _ _ _ _ he)). Qed.

  Lemma cbn_rn_value_wf Q v g v' g' :
    Pg g -> cbn_rn_value f v g = CbnCOk (v', g') -> Pg g' /\ (cbn_vwf Q v -> cbn_vwf Q v').
  Proof.
    intros hg he. unfold cbn_rn_value in he.
    destruct v as [h sp|e c|e c i sp|e c i sp|h sp|e c|e c sp].
    - destruct (cbn_rn_addrs f sp g) as [[sp1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. split; [exact (cbn_rn_addrs_wf _ _ _ _ hg e1)|exact (fun x => x)].
    - destruct (cbn_rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      injection he as <- <-. split; [exact (cbn_rn_env_wf _ _ _ _ hg E1)|intros _; exact I].
    - destruct (cbn_rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      destruct (cbn_rn_addrs f sp g1) as [[sp1 g2]|w] eqn:E2; [|discriminate].
      injection he as <- <-.
      split; [exact (cbn_rn_addrs_wf _ _ _ _ (cbn_rn_env_wf _ _ _ _ hg E1) E2)|intros _; exact I].
    - destruct (cbn_rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      destruct (cbn_rn_addrs f sp g1) as [[sp1 g2]|w] eqn:E2; [|discriminate].
      injection he as <- <-.
      split; [exact (cbn_rn_addrs_wf _ _ _ _ (cbn_rn_env_wf _ _ _ _ hg E1) E2)|intros _; exact I].
    - destruct (cbn_rn_addrs f sp g) as [[sp1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. split; [exact (cbn_rn_addrs_wf _ _ _ _ hg e1)|exact (fun x => x)].
    - destruct (cbn_rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      injection he as <- <-. split; [exact (cbn_rn_env_wf _ _ _ _ hg E1)|intros _; exact I].
    - destruct (cbn_rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      destruct (cbn_rn_addrs f sp g1) as [[sp1 g2]|w] eqn:E2; [|discriminate].
      injection he as <- <-.
      split; [exact (cbn_rn_addrs_wf _ _ _ _ (cbn_rn_env_wf _ _ _ _ hg E1) E2)|intros _; exact I].
  Qed.

  Lemma cbn_rn_cell_wf Q cl g cl' g' :
    Pg g -> cbn_rn_cell f cl g = CbnCOk (cl', g') -> Pg g' /\ (cbn_cwf Q cl -> cbn_cwf Q cl').
  Proof.
    intros hg he. unfold cbn_rn_cell in he. destruct cl as [vs n o c|v| |b].
    - destruct (cbn_rn_slots f vs g) as [[vs1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. split; [exact (cbn_rn_slots_wf _ _ _ _ hg e1)|intros _; exact I].
    - destruct (cbn_rn_value f v g) as [[v1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. exact (cbn_rn_value_wf Q _ _ _ _ hg e1).
    - injection he as <- <-. split; [exact hg|intros _; exact I].
    - destruct (f b g) as [[b1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. split; [exact (hf _ _ _ _ hg e1)|intros _; exact I].
  Qed.

  Lemma cbn_rn_root_wf Q r g r' g' :
    Pg g -> cbn_rn_root f r g = CbnCOk (r', g') -> Pg g' /\ (cbn_rwf Q r -> cbn_rwf Q r').
  Proof.
    intros hg he. unfold cbn_rn_root in he. destruct r as [a|x|e|v|l|l|cl].
    - destruct (f a g) as [[b g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. split; [exact (hf _ _ _ _ hg e1)|intros _; exact I].
    - destruct (cbn_rn_slot f x g) as [[x1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. split; [exact (cbn_rn_slot_wf _ _ _ _ hg e1)|intros _; exact I].
    - destruct (cbn_rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      injection he as <- <-. split; [exact (cbn_rn_env_wf _ _ _ _ hg E1)|intros _; exact I].
    - destruct (cbn_rn_value f v g) as [[v1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. exact (cbn_rn_value_wf Q _ _ _ _ hg e1).
    - destruct (cbn_rn_slots f l g) as [[l1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. split; [exact (cbn_rn_slots_wf _ _ _ _ hg e1)|intros _; exact I].
    - destruct (cbn_rn_addrs f l g) as [[l1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. split; [exact (cbn_rn_addrs_wf _ _ _ _ hg e1)|intros _; exact I].
    - destruct (cbn_rn_cell f cl g) as [[cl1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. exact (cbn_rn_cell_wf Q _ _ _ _ hg e1).
  Qed.

  Lemma cbn_rn_roots_wf Q : forall l g l' g',
    Pg g -> cbn_rn_roots f l g = CbnCOk (l', g') ->
    Pg g' /\ (Forall (cbn_rwf Q) l -> Forall (cbn_rwf Q) l').
  Proof.
    induction l as [|r l ih]; intros g l' g' hg he; simpl in he.
    - injection he as <- <-. split; [exact hg|intros h; exact h].
    - destruct (cbn_rn_root f r g) as [[r1 g1]|w] eqn:e1; [|discriminate].
      destruct (cbn_rn_roots f l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
      injection he as <- <-.
      destruct (cbn_rn_root_wf Q _ _ _ _ hg e1) as [hg1 hr1].
      destruct (ih _ _ _ hg1 e2) as [hg2 hr2].
      split; [exact hg2|].
      intros h. inversion h as [|? ? hr hl]; subst.
      constructor; [exact (hr1 hr)|exact (hr2 hl)].
  Qed.

  Lemma cbn_rn_tree'_wf : forall m g m' g', Pg g -> cbn_rn_tree' f m g = CbnCOk (m', g') -> Pg g'.
  Proof.
    induction m as [r ihr|x|x r ihr|l ihl|l ihl r ihr|l ihl x|l ihl x r ihr];
      intros g m' g' hg he; simpl in he.
    - destruct (cbn_rn_tree' f r g) as [[r' g1]|w1] eqn:e1; [|discriminate].
      injection he as <- <-. exact (ihr _ _ _ hg e1).
    - destruct (f x g) as [[x' g1]|w1] eqn:e1; [|discriminate].
      injection he as <- <-. exact (hf _ _ _ _ hg e1).
    - destruct (f x g) as [[x' g1]|w1] eqn:e1; [|discriminate].
      destruct (cbn_rn_tree' f r g1) as [[r' g2]|w2] eqn:e2; [|discriminate].
      injection he as <- <-. exact (ihr _ _ _ (hf _ _ _ _ hg e1) e2).
    - destruct (cbn_rn_tree' f l g) as [[l' g1]|w1] eqn:e1; [|discriminate].
      injection he as <- <-. exact (ihl _ _ _ hg e1).
    - destruct (cbn_rn_tree' f l g) as [[l' g1]|w1] eqn:e1; [|discriminate].
      destruct (cbn_rn_tree' f r g1) as [[r' g2]|w2] eqn:e2; [|discriminate].
      injection he as <- <-. exact (ihr _ _ _ (ihl _ _ _ hg e1) e2).
    - destruct (cbn_rn_tree' f l g) as [[l' g1]|w1] eqn:e1; [|discriminate].
      destruct (f x g1) as [[x' g2]|w2] eqn:e2; [|discriminate].
      injection he as <- <-. exact (hf _ _ _ _ (ihl _ _ _ hg e1) e2).
    - destruct (cbn_rn_tree' f l g) as [[l' g1]|w1] eqn:e1; [|discriminate].
      destruct (f x g1) as [[x' g2]|w2] eqn:e2; [|discriminate].
      destruct (cbn_rn_tree' f r g2) as [[r' g3]|w3] eqn:e3; [|discriminate].
      injection he as <- <-. exact (ihr _ _ _ (hf _ _ _ _ (ihl _ _ _ hg e1) e2) e3).
  Qed.

  Lemma cbn_rn_ptree_wf m g m' g' : Pg g -> cbn_rn_ptree f m g = CbnCOk (m', g') -> Pg g'.
  Proof.
    intros hg he. destruct m as [|m]; unfold cbn_rn_ptree in he.
    - injection he as <- <-. exact hg.
    - destruct (cbn_rn_tree' f m g) as [[m1 g1]|w1] eqn:e1; [|discriminate].
      injection he as <- <-. exact (cbn_rn_tree'_wf _ _ _ _ hg e1).
  Qed.
End RenameWf.

(** ** A collection, and an allocation *)

(** Every cell [cbn_bh_get] finds in the old and in the new heap of a collection. *)
#[local] Definition cbn_gcw (Q : nat) (g : cbn_gc_state) : Prop :=
  (forall a cl, cbn_bh_get a g.(cbn_g_old) = Some cl -> cbn_cwf Q cl)
  /\ (forall a cl, cbn_bh_get a g.(cbn_g_heap) = Some cl -> cbn_cwf Q cl).

Lemma cbn_gc_copy_step Q (cp : cbn_haddr -> cbn_gc_state -> cbn_res (cbn_haddr * cbn_gc_state)) a x
  g cl cl1 g1 old n :
  (forall a g a' g', cbn_gcw Q g -> cp a g = CbnCOk (a', g') -> cbn_gcw Q g') ->
  cbn_gcw Q g -> cbn_cwf Q cl -> cbn_rn_cell cp cl g = CbnCOk (cl1, g1) ->
  cbn_bh_upd a (CbnCFwd x) g1.(cbn_g_old) = Some old ->
  cbn_gcw Q (cbn_mkGc old (cbn_bh_cons cl1 g1.(cbn_g_heap)) n).
Proof.
  intros hcp hg hcl he hu.
  destruct (cbn_rn_cell_wf cp (cbn_gcw Q) hcp Q _ _ _ _ hg he) as [[ho hh] hc1].
  split; cbn [cbn_g_old cbn_g_heap].
  - intros b cl' hb. destruct (cbn_haddr_dec b a) as [-> | hne].
    + rewrite (cbn_bh_get_upd_same _ _ _ _ hu) in hb. injection hb as <-. exact I.
    + rewrite (cbn_bh_get_upd_other _ _ _ _ _ hu hne) in hb. exact (ho b cl' hb).
  - intros b cl' hb.
    destruct (cbn_bh_get_cons_any cl1 cl' _ b hb) as [-> | hb'];
      [exact (hc1 hcl)|exact (hh b cl' hb')].
Qed.

Lemma cbn_gc_copy_wf Q : forall f a g a' g', cbn_gcw Q g -> cbn_gc_copy f a g = CbnCOk (a', g') ->
  cbn_gcw Q g'.
Proof.
  intros f. induction f as [|k ih]; intros a g a' g' hg he.
  - rewrite cbn_gc_copy_FO in he.
    destruct (cbn_bh_get a g.(cbn_g_old)) as [[| | |b]|]; try discriminate he.
    injection he as <- <-. exact hg.
  - rewrite cbn_gc_copy_FS in he.
    destruct (cbn_bh_get a g.(cbn_g_old)) as [cl|] eqn:ea; [|discriminate he].
    pose proof (proj1 hg a cl ea) as hcl.
    assert (hcp : forall a g a' g', cbn_gcw Q g -> cbn_gc_copy (k tt) a g = CbnCOk (a', g') ->
      cbn_gcw Q g')
      by (intros; eapply ih; eassumption).
    destruct cl as [vs n o c|v| |b].
    4: injection he as <- <-; exact hg.
    all: lazymatch type of he with
         | context [cbn_rn_cell ?cp ?cl0 ?g0] =>
           destruct (cbn_rn_cell cp cl0 g0) as [[cl1 g1]|w] eqn:e1; [|discriminate he]
         end;
         lazymatch type of he with
         | context [cbn_bh_upd ?a0 ?x0 ?o0] =>
           destruct (cbn_bh_upd a0 x0 o0) as [old|] eqn:e2; [|discriminate he]
         end;
         injection he as <- <-;
         exact (cbn_gc_copy_step Q _ _ _ _ _ _ _ _ _ hcp hg hcl e1 e2).
Qed.

Lemma cbn_collect_wf Q rs s rs' s' :
  cbn_collect rs s = CbnCOk (rs', s') ->
  cbn_hwf Q s -> Forall (cbn_rwf Q) rs -> cbn_hwf Q s' /\ Forall (cbn_rwf Q) rs'.
Proof.
  intros he hs hrs. rewrite cbn_collect_eq in he.
  set (cp := cbn_gc_copy (cbn_fuel_of_pos s.(cbn_st_next) (fun _ => CbnFO))) in he.
  assert (hcp : forall a g a' g', cbn_gcw Q g -> cp a g = CbnCOk (a', g') -> cbn_gcw Q g')
    by (intros; eapply cbn_gc_copy_wf; eassumption).
  assert (hg0 : cbn_gcw Q (cbn_mkGc s.(cbn_st_heap) (cbn_bh_holes s.(cbn_st_next))
    s.(cbn_st_next))).
  { split; cbn [cbn_g_old cbn_g_heap].
    - exact hs.
    - intros a cl ha. rewrite cbn_bh_get_holes in ha. discriminate ha. }
  destruct (cbn_rn_ptree cp s.(cbn_st_gam)
    (cbn_mkGc s.(cbn_st_heap) (cbn_bh_holes s.(cbn_st_next)) s.(cbn_st_next)))
    as [[cbn_gm g1]|w] eqn:e1; [|discriminate he].
  destruct (cbn_rn_roots cp rs g1) as [[rs2 g2]|w] eqn:e2; [|discriminate he].
  injection he as <- <-.
  pose proof (cbn_rn_ptree_wf cp (cbn_gcw Q) hcp _ _ _ _ hg0 e1) as hg1.
  destruct (cbn_rn_roots_wf cp (cbn_gcw Q) hcp Q _ _ _ _ hg1 e2) as [hg2 hr2].
  split; [|exact (hr2 hrs)].
  intros a cl ha. exact (proj2 hg2 a cl ha).
Qed.

Lemma cbn_alloc_wf Q cl rs s a rs' s' :
  cbn_alloc cl rs s = CbnCOk (a, rs', s') ->
  cbn_hwf Q s -> cbn_cwf Q cl -> Forall (cbn_rwf Q) rs -> cbn_hwf Q s' /\ Forall (cbn_rwf Q) rs'.
Proof.
  intros he hs hc hrs. destruct (cbn_gc_due s) eqn:eg.
  - rewrite (cbn_alloc_gc cl rs s eg) in he.
    destruct (cbn_collect (CbnRC cl :: rs) s) as [[rs2 s2]|w] eqn:ec; [|discriminate he].
    destruct (cbn_collect_wf Q _ _ _ _ ec hs (Forall_cons (CbnRC cl) hc hrs)) as [hs2 hr2].
    destruct rs2 as [|[| | | | | |cl2] rs2]; try discriminate he.
    injection he as <- <- <-.
    split; [exact (cbn_hwf_alloc_now Q cl2 s2 hs2 (cbn_rwf_hd _ _ _ hr2))|exact
      (cbn_rwf_tl _ _ _ hr2)].
  - rewrite (cbn_alloc_no_gc cl rs s eg) in he. injection he as <- <- <-.
    split; [exact (cbn_hwf_alloc_now Q cl s hs hc)|exact hrs].
Qed.

(** An allocation of a cell that keeps the invariant keeps it, at any master level
  [Q >= nctx]. *)
Definition cbn_alloc_hwf (nctx : nat) : Prop := forall Q cl rs s a rs' s', nctx <= Q ->
  cbn_hwf Q s -> cbn_cwf Q cl -> Forall (cbn_rwf Q) rs ->
  cbn_alloc cl rs s = CbnCOk (a, rs', s') -> cbn_hwf Q s' /\ Forall (cbn_rwf Q) rs'.

Lemma cbn_alloc_hwf_holds nctx : cbn_alloc_hwf nctx.
Proof.
  intros Q cl rs s a rs' s' _ hs hc hrs he. exact (cbn_alloc_wf Q cl rs s a rs' s' he hs hc hrs).
Qed.

(** ** The machine *)

(** The roots a call is given: the roots held, or new ones without a value or cell. *)
Local Ltac cbn_rok :=
  first [ assumption
        | match goal with h : Forall (cbn_rwf _) (_ :: ?l) |- Forall (cbn_rwf _) ?l =>
            exact (cbn_rwf_tl _ _ _ h) end
        | match goal with h : Forall (cbn_rwf _) (_ :: _ :: ?l) |- Forall (cbn_rwf _) ?l =>
            exact (cbn_rwf_tl _ _ _ (cbn_rwf_tl _ _ _ h)) end
        | apply Forall_cons; [first [exact I|assumption]|cbn_rok]
        | apply Forall_nil ].

(** The decisions of a match or projection on a constructor: each test that fails fails. *)
Local Ltac cbn_dtests he :=
  repeat (match type of he with
          | context [if ?b then _ else _] => destruct b
          | context [match ?o with Some _ => _ | None => _ end] => destruct o
          | context [match ?m with O => _ | S _ => _ end] => destruct m
          end; try discriminate he).

Section Machine.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat).
  Context (hlen : #|Γ| <= nctx) (Q : nat) (hQ : nctx <= Q).

  Lemma cbn_tick_wf s s' : cbn_tick s = Some s' -> cbn_hwf Q s -> cbn_hwf Q s'.
  Proof. intros he. apply cbn_hwf_heap. exact (proj1 (cbn_tick_shape s s' he)). Qed.

  Lemma cbn_delta_wf kn u s r s' : cbn_delta X_type X kn u s = CbnCOk (r, s') -> cbn_hwf Q s ->
    cbn_hwf Q s'.
  Proof. intros he. apply cbn_hwf_heap. exact
    (proj1 (cbn_delta_shape X_type X kn u s r s' he)). Qed.

  Lemma cbn_gam_wf j rs s a rs' s' :
    cbn_gam X_type X Γ nctx j rs s = CbnCOk (a, rs', s') ->
    cbn_hwf Q s -> Forall (cbn_rwf Q) rs -> cbn_hwf Q s' /\ Forall (cbn_rwf Q) rs'.
  Proof.
    intros he hs hrs. unfold cbn_gam in he. cbv zeta in he.
    destruct (PTree.get (cbn_key_of_succ_nat j) s.(cbn_st_gam)) as [a0|].
    { injection he as <- <- <-. split; assumption. }
    destruct (nth_error Γ j) as [decl|] eqn:ed; [|discriminate he].
    assert (hj : j < nctx) by (pose proof (nth_error_Some_length ed); lia).
    destruct (decl_body decl) as [b|].
    - destruct (cbn_new_entry X_type X b [] s) as [c s1] eqn:en.
      cbv beta iota in he.
      assert (hs1 : cbn_hwf Q s1).
      { apply (cbn_hwf_heap Q s s1); [|exact hs].
        change s1 with (snd (c, s1)). rewrite <- en.
        exact (proj1 (cbn_new_entry_shape X_type X b [] s)). }
      cbn_dcall he ea a1 rs1 s2.
      injection he as <- <- <-.
      destruct (cbn_alloc_wf _ _ _ _ _ _ _ ea hs1 I hrs) as [hs2 hr2].
      split; [exact (cbn_hwf_heap Q s2 _ eq_refl hs2)|exact hr2].
    - cbv beta iota in he. cbn_dcall he ea a1 rs1 s2.
      injection he as <- <- <-.
      assert (hc : cbn_cwf Q (CbnCDone (CbnVNeu (CbnNVar (nctx - S j)) []))) by (cbn; lia).
      destruct (cbn_alloc_wf _ _ _ _ _ _ _ ea hs hc hrs) as [hs2 hr2].
      split; [exact (cbn_hwf_heap Q s2 _ eq_refl hs2)|exact hr2].
  Qed.

  Lemma cbn_env_var_wf n e rs s x rs' s' :
    cbn_env_var X_type X Γ nctx n e rs s = CbnCOk (x, rs', s') ->
    cbn_hwf Q s -> Forall (cbn_rwf Q) rs -> cbn_hwf Q s' /\ Forall (cbn_rwf Q) rs'.
  Proof.
    intros he hs hrs. unfold cbn_env_var in he.
    destruct (nth_error e.(cbn_ev_vals) n) as [y|].
    - injection he as <- <- <-. split; assumption.
    - cbn_dcall he eg a1 rs1 s1. injection he as <- <- <-. exact (cbn_gam_wf _ _ _ _ _ _ eg hs hrs).
  Qed.

  Lemma cbn_arg_slot_wf e c rs s x rs' s' :
    cbn_arg_slot X_type X Γ nctx e c rs s = CbnCOk (x, rs', s') ->
    cbn_hwf Q s -> Forall (cbn_rwf Q) rs -> cbn_hwf Q s' /\ Forall (cbn_rwf Q) rs'.
  Proof.
    intros he hs hrs. unfold cbn_arg_slot in he.
    destruct (cbn_c_term c); try (injection he as <- <- <-; split; assumption).
    exact (cbn_env_var_wf _ _ _ _ _ _ _ he hs hrs).
  Qed.

  Lemma cbn_materialize_wf x rs s a rs' s' :
    cbn_materialize X_type X x rs s = CbnCOk (a, rs', s') ->
    cbn_hwf Q s -> Forall (cbn_rwf Q) rs -> cbn_hwf Q s' /\ Forall (cbn_rwf Q) rs'.
  Proof.
    intros he hs hrs. unfold cbn_materialize in he.
    destruct x as [a0|vs n o c]; [injection he as <- <- <-; split; assumption|].
    destruct (cbn_c_term c) eqn:ec; try exact (cbn_alloc_wf _ _ _ _ _ _ _ he hs I hrs).
    - (* tConst: an axiom is a neutral whose head is the code, closed *)
      lazymatch type of he with
      | context [cbn_delta X_type X ?kn ?ui s] =>
        destruct (cbn_delta X_type X kn ui s) as [[[c'|] s1]|w] eqn:ed
      end.
      + exact (cbn_alloc_wf _ _ _ _ _ _ _ he (cbn_delta_wf _ _ _ _ _ ed hs) I hrs).
      + exact (cbn_alloc_wf _ _ _ _ _ _ _ he (cbn_delta_wf _ _ _ _ _ ed hs) eq_refl hrs).
      + exact (cbn_alloc_wf _ _ _ _ _ _ _ he hs I hrs).
    - (* tFix *)
      lazymatch type of he with
      | context [nth_error ?m ?i] => destruct (nth_error m i)
      end; exact (cbn_alloc_wf _ _ _ _ _ _ _ he hs I hrs).
  Qed.

  Lemma cbn_bind_wf x body rs s y rs' s' :
    cbn_bind X_type X x body rs s = CbnCOk (y, rs', s') ->
    cbn_hwf Q s -> Forall (cbn_rwf Q) rs -> cbn_hwf Q s' /\ Forall (cbn_rwf Q) rs'.
  Proof.
    intros he hs hrs. unfold cbn_bind in he. destruct x as [a0|vals n o c].
    - injection he as <- <- <-. split; assumption.
    - destruct (cbn_once_body body s) as [b s1] eqn:eo.
      assert (hs1 : cbn_hwf Q s1).
      { apply (cbn_hwf_heap Q s s1); [|exact hs].
        change s1 with (snd (b, s1)). rewrite <- eo. exact (proj1 (cbn_once_body_shape body s)). }
      destruct (b && negb (cbn_slots_has_inl vals)).
      + injection he as <- <- <-. split; assumption.
      + cbn_dcall he em a1 rs1 s2. injection he as <- <- <-.
        exact (cbn_materialize_wf _ _ _ _ _ _ em hs1 hrs).
  Qed.

  Lemma cbn_mat_all_wf : forall d l rs s al rs' s',
    cbn_mat_all X_type X d l rs s = CbnCOk (al, rs', s') ->
    cbn_hwf Q s -> Forall (cbn_rwf Q) rs -> cbn_hwf Q s' /\ Forall (cbn_rwf Q) rs'.
  Proof.
    intros d. induction d as [|k ih]; intros l rs s al rs' s' he hs hrs;
      destruct l as [|x l]; cbn [cbn_mat_all] in he.
    1,3: injection he as <- <- <-; split; assumption.
    - discriminate he.
    - cbn_dcall he em a1 rs1 s1.
      destruct rs1 as [|[| | | |l1| |] rs1]; try discriminate he.
      destruct (cbn_materialize_wf _ _ _ _ _ _ em hs ltac:(cbn_rok)) as [hs1 hr1].
      cbn_dcall he em2 al1 rs2 s2.
      destruct rs2 as [|[a0| | | | | |] rs2]; try discriminate he.
      injection he as <- <- <-.
      destruct (ih tt _ _ _ _ _ _ em2 hs1 ltac:(cbn_rok)) as [hs2 hr2].
      split; [exact hs2|exact (cbn_rwf_tl _ _ _ hr2)].
  Qed.

  Lemma cbn_push_fix_cells_wf : forall n e c i acc rs s e' rs' s',
    cbn_push_fix_cells e c i n acc rs s = CbnCOk (e', rs', s') ->
    cbn_hwf Q s -> Forall (cbn_rwf Q) rs -> cbn_hwf Q s' /\ Forall (cbn_rwf Q) rs'.
  Proof.
    induction n as [|n ih]; intros e c i acc rs s e' rs' s' he hs hrs;
      cbn [cbn_push_fix_cells] in he.
    - injection he as <- <- <-. split; assumption.
    - cbn_dcall he ea a1 rs1 s1.
      destruct rs1 as [|[| |e1| | | |] [|[| |acc1| | | |] rs1]]; try discriminate he.
      destruct (cbn_alloc_wf _ _ _ _ _ _ _ ea hs I ltac:(cbn_rok)) as [hs1 hr1].
      exact (ih _ _ _ _ _ _ _ _ _ he hs1 ltac:(cbn_rok)).
  Qed.

  (** The five functions of the machine at one fuel keep the invariant at [Q]. *)
  Definition cbn_machine_hwf_at (d : cbn_fuel) : Prop :=
    (forall a rs s v rs' s',
       cbn_force X_type X Γ nctx d a rs s = CbnCOk (v, rs', s') ->
       cbn_hwf Q s -> Forall (cbn_rwf Q) rs -> cbn_hwf Q s' /\ Forall (cbn_rwf Q) rs' /\
         cbn_vwf Q v)
    /\ (forall x stk rs s v rs' s',
       cbn_eval_slot X_type X Γ nctx d x stk rs s = CbnCOk (v, rs', s') ->
       cbn_hwf Q s -> Forall (cbn_rwf Q) rs -> cbn_hwf Q s' /\ Forall (cbn_rwf Q) rs' /\
         cbn_vwf Q v)
    /\ (forall e c stk rs s v rs' s',
       cbn_whnf X_type X Γ nctx d e c stk rs s = CbnCOk (v, rs', s') ->
       cbn_hwf Q s -> Forall (cbn_rwf Q) rs -> cbn_hwf Q s' /\ Forall (cbn_rwf Q) rs' /\
         cbn_vwf Q v)
    /\ (forall e c mfix idx stk rs s v rs' s',
       cbn_whnf_fix X_type X Γ nctx d e c mfix idx stk rs s = CbnCOk (v, rs', s') ->
       cbn_hwf Q s -> Forall (cbn_rwf Q) rs -> cbn_hwf Q s' /\ Forall (cbn_rwf Q) rs' /\
         cbn_vwf Q v)
    /\ (forall v stk rs s w rs' s',
       cbn_apply X_type X Γ nctx d v stk rs s = CbnCOk (w, rs', s') ->
       cbn_hwf Q s -> Forall (cbn_rwf Q) rs -> cbn_vwf Q v ->
       cbn_hwf Q s' /\ Forall (cbn_rwf Q) rs' /\ cbn_vwf Q w).

  Lemma cbn_machine_wf : forall d, cbn_machine_hwf_at d.
  Proof.
    intros d. induction d as [|k ih].
    - (* CbnFO: every call fails, except [cbn_apply] with an empty stack *)
      split; [|split; [|split; [|split]]].
      + intros a rs s v rs' s' he. cbn [cbn_force] in he. discriminate he.
      + intros x stk rs s v rs' s' he. cbn [cbn_eval_slot] in he. discriminate he.
      + intros e c stk rs s v rs' s' he. cbn [cbn_whnf] in he. discriminate he.
      + intros e c mfix idx stk rs s v rs' s' he. cbn [cbn_whnf_fix] in he. discriminate he.
      + intros v stk rs s w rs' s' he hs hrs hv. cbn [cbn_apply] in he.
        destruct stk; [injection he as <- <- <-; split; [|split]; assumption|discriminate he].
    - destruct (ih tt) as (IHf & IHs & IHw & IHx & IHa).
      split; [|split; [|split; [|split]]].
      + (* cbn_force *)
        intros a0 rs0 s0 v0 rs' s' he hs hrs.
        cbv beta iota zeta delta [cbn_force] in he.
        destruct (cbn_heap_get a0 s0) as [cl|] eqn:ehc; [|discriminate he].
        destruct cl as [vs n o c|vd| |b]; try discriminate he.
        * (* a suspension: evaluate it, then write the value back *)
          destruct (cbn_heap_upd a0 CbnCBusy s0) as [sb|] eqn:ebusy; [|discriminate he].
          cbn_dcall he ew vw rsw sw.
          destruct rsw as [|[ar| | | | | |] rsw]; try discriminate he.
          destruct (cbn_heap_upd ar (CbnCDone vw) sw) as [sd|] eqn:edone; [|discriminate he].
          injection he as <- <- <-.
          pose proof (cbn_hwf_upd Q a0 CbnCBusy s0 sb hs I ebusy) as hsb.
          destruct (IHw _ _ _ _ _ _ _ _ ew hsb ltac:(cbn_rok)) as (hsw & hrw & hvw).
          split; [exact (cbn_hwf_upd Q ar (CbnCDone vw) sw sd hsw hvw edone)|].
          split; [exact (cbn_rwf_tl _ _ _ hrw)|exact hvw].
        * (* a value: the heap has it *)
          injection he as <- <- <-. split; [exact hs|]. split; [exact hrs|exact (hs a0 _ ehc)].
      + (* cbn_eval_slot *)
        intros x stk rs0 s0 v0 rs' s' he hs hrs.
        cbv beta iota zeta delta [cbn_eval_slot] in he.
        destruct x as [a|vs n o c].
        * cbn_dcall he ef vf rsf sf.
          destruct rsf as [|[| | | |lk| |] rsf]; try discriminate he.
          destruct (IHf _ _ _ _ _ _ ef hs ltac:(cbn_rok)) as (hsf & hrf & hvf).
          exact (IHa _ _ _ _ _ _ _ he hsf ltac:(cbn_rok) hvf).
        * exact (IHw _ _ _ _ _ _ _ _ he hs hrs).
      + (* cbn_whnf *)
        intros e c stk rs0 s0 v0 rs' s' he hs0 hrs.
        cbv beta iota zeta delta [cbn_whnf] in he.
        destruct (cbn_tick s0) as [st|] eqn:etick; [|discriminate he].
        pose proof (cbn_tick_wf _ _ etick hs0) as hs. clear hs0.
        destruct (cbn_c_term c) as [n|vr|ev earg|srt|na A B|na A b|na b T body|f arg|kn ui
                               |ind ui|ind n ui|ci p scrut brs|pr arg|mfix idx|cmfix cidx|prm]
          eqn:ec; try solve [discriminate he].
        * (* tRel *)
          cbn_dcall he ev xr rsr sr.
          destruct rsr as [|[| | | |lk| |] rsr]; try discriminate he.
          destruct (cbn_env_var_wf _ _ _ _ _ _ _ ev hs ltac:(cbn_rok)) as [hsr hrr].
          exact (IHs _ _ _ _ _ _ _ he hsr ltac:(cbn_rok)).
        * (* tSort *)
          destruct stk; [|discriminate he]. injection he as <- <- <-.
          split; [exact hs|]. split; [exact hrs|exact I].
        * (* tProd *)
          destruct stk; [|discriminate he]. injection he as <- <- <-.
          split; [exact hs|]. split; [exact hrs|exact I].
        * (* tLambda *)
          destruct stk as [|xh stk'].
          -- injection he as <- <- <-. split; [exact hs|]. split; [exact hrs|exact I].
          -- cbn_dcall he eb xb rsb sb.
             destruct rsb as [|[| |e1| | | |] [|[| | | |k1| |] rsb]]; try discriminate he.
             destruct (cbn_bind_wf _ _ _ _ _ _ _ eb hs ltac:(cbn_rok)) as [hsb hrb].
             exact (IHw _ _ _ _ _ _ _ _ he hsb ltac:(cbn_rok)).
        * (* tLetIn *)
          cbn_dcall he ea xa rsa sa.
          destruct rsa as [|[| |e1| | | |] [|[| | | |k1| |] rsa]]; try discriminate he.
          destruct (cbn_arg_slot_wf _ _ _ _ _ _ _ ea hs ltac:(cbn_rok)) as [hsa hra].
          cbn_dcall he eb xb rsb sb.
          destruct rsb as [|[| |e2| | | |] [|[| | | |k2| |] rsb]]; try discriminate he.
          destruct (cbn_bind_wf _ _ _ _ _ _ _ eb hsa ltac:(cbn_rok)) as [hsb hrb].
          exact (IHw _ _ _ _ _ _ _ _ he hsb ltac:(cbn_rok)).
        * (* tApp *)
          cbn_dcall he ea xa rsa sa.
          destruct rsa as [|[| |e1| | | |] [|[| | | |k1| |] rsa]]; try discriminate he.
          destruct (cbn_arg_slot_wf _ _ _ _ _ _ _ ea hs ltac:(cbn_rok)) as [hsa hra].
          exact (IHw _ _ _ _ _ _ _ _ he hsa ltac:(cbn_rok)).
        * (* tConst: delta; the primitive-operation rule, whose reduct is a new code and whose
             arguments are forced; or a neutral whose head is the code *)
          destruct (cbn_delta X_type X kn ui st) as [[r s1]|w] eqn:ed; [|discriminate he].
          pose proof (cbn_delta_wf _ _ _ _ _ ed hs) as hs1.
          destruct r as [c'|].
          -- exact (IHw _ _ _ _ _ _ _ _ he hs1 hrs).
          -- cbv beta iota in he.
             destruct (cbn_prim_step_of X_type X kn stk s1) as [|t rest|i x].
             ++ cbn_dcall he em sp rs1 s2.
                destruct (cbn_mat_all_wf _ _ _ _ _ _ _ em hs1 hrs) as [hs2 hr2].
                injection he as <- <- <-. split; [exact hs2|]. split; [exact hr2|].
                first [reflexivity|rewrite ec; reflexivity].
             ++ destruct (cbn_new_entry X_type X t [] s1) as [c2 s2] eqn:en.
                assert (hs2 : cbn_hwf Q s2).
                { apply (cbn_hwf_heap Q s1 s2); [|exact hs1].
                  change s2 with (snd (c2, s2)). rewrite <- en.
                  exact (proj1 (cbn_new_entry_shape X_type X t [] s1)). }
                exact (IHw _ _ _ _ _ _ _ _ he hs2 hrs).
             ++ cbn_dcall he ea a1 rs1 s2.
                destruct rs1 as [|[| | | |k1| |] rs1]; try discriminate he.
                destruct (cbn_materialize_wf _ _ _ _ _ _ ea hs1 ltac:(cbn_rok)) as [hs2 hr2].
                cbn_dcall he ef vf rsf sf.
                destruct rsf as [|[| | | |k2| |] rsf]; try discriminate he.
                destruct (IHf _ _ _ _ _ _ ef hs2 ltac:(cbn_rok)) as (hsf & hrf & _).
                destruct (cbn_value_is_lit vf).
                ** exact (IHw _ _ _ _ _ _ _ _ he hsf ltac:(cbn_rok)).
                ** cbn_dcall he em sp rs3 s3.
                   destruct (cbn_mat_all_wf _ _ _ _ _ _ _ em hsf ltac:(cbn_rok)) as [hs3 hr3].
                   injection he as <- <- <-. split; [exact hs3|]. split; [exact hr3|].
                   first [reflexivity|rewrite ec; reflexivity].
        * (* tInd: a constructor value whose head is the code *)
          cbn_dcall he em sp rs1 s1.
          destruct (cbn_mat_all_wf _ _ _ _ _ _ _ em hs hrs) as [hs1 hr1].
          injection he as <- <- <-. split; [exact hs1|]. split; [exact hr1|].
          first [reflexivity|rewrite ec; reflexivity].
        * (* tConstruct *)
          cbn_dcall he em sp rs1 s1.
          destruct (cbn_mat_all_wf _ _ _ _ _ _ _ em hs hrs) as [hs1 hr1].
          injection he as <- <- <-. split; [exact hs1|]. split; [exact hr1|].
          first [reflexivity|rewrite ec; reflexivity].
        * (* tCase *)
          cbn_dcall he ewc vc rsc sc.
          destruct rsc as [|[| |e1| | | |] [|[| | | |k1| |] rsc]]; try discriminate he.
          destruct (IHw _ _ _ _ _ _ _ _ ewc hs ltac:(cbn_rok)) as (hsc & hrc & _).
          destruct vc as [h sp| | | |nn sp| |]; try discriminate he.
          1: { destruct h; try discriminate he. cbn_dtests he.
               exact (IHw _ _ _ _ _ _ _ _ he hsc ltac:(cbn_rok)). }
          all: cbn_dcall he em sp1 rsm sm;
               destruct rsm as [|[| |e5| | | |] rsm]; try discriminate he;
               destruct (cbn_mat_all_wf _ _ _ _ _ _ _ em hsc ltac:(cbn_rok)) as [hsm hrm];
               injection he as <- <- <-;
               split; [exact hsm|]; split; [exact (cbn_rwf_tl _ _ _ hrm)|exact I].
        * (* tProj *)
          cbn_dcall he ewc vc rsc sc.
          destruct rsc as [|[| |e1| | | |] [|[| | | |k1| |] rsc]]; try discriminate he.
          destruct (IHw _ _ _ _ _ _ _ _ ewc hs ltac:(cbn_rok)) as (hsc & hrc & _).
          destruct vc as [h sp| | | |nn sp| |]; try discriminate he.
          1: { destruct h; try discriminate he. cbn_dtests he.
               exact (IHs _ _ _ _ _ _ _ he hsc ltac:(cbn_rok)). }
          all: cbn_dcall he em sp1 rsm sm;
               destruct rsm as [|[| |e5| | | |] rsm]; try discriminate he;
               destruct (cbn_mat_all_wf _ _ _ _ _ _ _ em hsc ltac:(cbn_rok)) as [hsm hrm];
               injection he as <- <- <-;
               split; [exact hsm|]; split; [exact (cbn_rwf_tl _ _ _ hrm)|exact I].
        * (* tFix *)
          exact (IHx _ _ _ _ _ _ _ _ _ _ he hs hrs).
        * (* tPrim *)
          destruct stk; [|discriminate he]. injection he as <- <- <-.
          split; [exact hs|]. split; [exact hrs|exact I].
      + (* cbn_whnf_fix *)
        intros e c mfix idx stk rs0 s0 v0 rs' s' he hs hrs.
        cbv beta iota zeta delta [cbn_whnf_fix] in he.
        destruct (nth_error mfix idx) as [def|]; [|discriminate he].
        destruct (nth_error stk (rarg def)) as [x|].
        * cbn_dcall he ea a1 rs1 s1.
          destruct rs1 as [|[| |e1| | | |] [|[| | | |k1| |] rs1]]; try discriminate he.
          destruct (cbn_materialize_wf _ _ _ _ _ _ ea hs ltac:(cbn_rok)) as [hs1 hr1].
          cbn_dcall he ef vf rsf sf.
          destruct rsf as [|[| |e2| | | |] [|[| | | |k2| |] rsf]]; try discriminate he.
          destruct (IHf _ _ _ _ _ _ ef hs1 ltac:(cbn_rok)) as (hsf & hrf & hvf).
          destruct vf as [h sp| | | |nn sp| |]; try discriminate he.
          1: { (* the guard holds: the forced constructor goes to a fresh cell *)
               destruct h; try discriminate he.
               cbn_dcall he ea2 a2 rs2 s2.
               destruct rs2 as [|[| |e3| | | |] [|[| | | |k3| |] rs2]]; try discriminate he.
               destruct (cbn_alloc_wf _ _ _ _ _ _ _ ea2 hsf hvf ltac:(cbn_rok)) as [hs2 hr2].
               cbn_dcall he ep e4 rs3 s3.
               destruct rs3 as [|[| | | |k4| |] rs3]; try discriminate he.
               destruct (cbn_push_fix_cells_wf _ _ _ _ _ _ _ _ _ _ ep hs2 ltac:(cbn_rok))
                 as [hs3 hr3].
               exact (IHw _ _ _ _ _ _ _ _ he hs3 ltac:(cbn_rok)). }
          all: cbn_dcall he em sp1 rsm sm;
               destruct rsm as [|[| |e5| | | |] rsm]; try discriminate he;
               destruct (cbn_mat_all_wf _ _ _ _ _ _ _ em hsf ltac:(cbn_rok)) as [hsm hrm];
               injection he as <- <- <-;
               split; [exact hsm|]; split; [exact (cbn_rwf_tl _ _ _ hrm)|exact I].
        * cbn_dcall he em sp rs1 s1.
          destruct rs1 as [|[| |e1| | | |] rs1]; try discriminate he.
          destruct (cbn_mat_all_wf _ _ _ _ _ _ _ em hs ltac:(cbn_rok)) as [hs1 hr1].
          injection he as <- <- <-.
          split; [exact hs1|]. split; [exact (cbn_rwf_tl _ _ _ hr1)|exact I].
      + (* cbn_apply *)
        intros v stk rs0 s0 w rs' s' he hs hrs hv.
        cbv beta iota zeta delta [cbn_apply] in he.
        destruct stk as [|y stk']; [injection he as <- <- <-; split; [|split]; assumption|].
        destruct v as [h sp|e c|e c idx sp|e c idx sp|nn sp|e c|e c sp]; try discriminate he.
        2: { (* a lambda: beta *)
             destruct (cbn_c_term c); try discriminate he.
             cbn_dcall he eb xb rsb sb.
             destruct rsb as [|[| |e1| | | |] [|[| | | |k1| |] rsb]]; try discriminate he.
             destruct (cbn_bind_wf _ _ _ _ _ _ _ eb hs ltac:(cbn_rok)) as [hsb hrb].
             exact (IHw _ _ _ _ _ _ _ _ he hsb ltac:(cbn_rok)). }
        2: { (* a fixpoint: its spine goes back on the stack *)
             destruct (cbn_c_term c); try discriminate he.
             exact (IHx _ _ _ _ _ _ _ _ _ _ he hs hrs). }
        all: (* the spine grows *)
             cbn_dcall he em sp1 rsm sm;
             destruct rsm as [|[| | |v1| | |] rsm]; try discriminate he;
             destruct (cbn_mat_all_wf _ _ _ _ _ _ _ em hs ltac:(cbn_rok)) as [hsm hrm];
             destruct (cbn_add_spine v1 sp1) as [v2|] eqn:eadd; [|discriminate he];
             injection he as <- <- <-;
             split; [exact hsm|]; split; [exact (cbn_rwf_tl _ _ _ hrm)|];
             exact (cbn_add_spine_wf _ _ _ _ (cbn_rwf_hd _ _ _ hrm) eadd).
  Qed.
End Machine.

(** The machine keeps the invariant at every fuel and every master level [Q >= nctx]. *)
Definition cbn_machine_hwf {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1)
    (Γ : context) (nctx : nat) : Prop :=
  forall d Q, nctx <= Q -> cbn_machine_hwf_at X_type X Γ nctx Q d.

(** [cbn_machine_hwf] holds for every context no longer than [nctx]. *)
Lemma cbn_machine_hwf_holds {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1)
    (Γ : context) (nctx : nat) (hlen : #|Γ| <= nctx) :
  cbn_machine_hwf X_type X Γ nctx.
Proof. intros d Q hQ. exact (cbn_machine_wf X_type X Γ nctx hlen Q hQ d). Qed.

(** The satisfying instance of [cbn_machine_hwf] at the level the machine runs at:
  [cbn_conv_answer] takes [nctx = #|Γ|]. *)
Lemma cbn_machine_hwf_master {cf : checker_flags} (X_type : abstract_env_impl)
    (X : X_type.π2.π1) (Γ : context) (nctx : nat) (hnctx : nctx = #|Γ|) :
  cbn_machine_hwf X_type X Γ nctx.
Proof. apply cbn_machine_hwf_holds. rewrite hnctx. apply le_n. Qed.

(** The premise [#|Γ| <= nctx] is needed: with [nctx = 0], one assumption in [Γ] and the
  master level [0], the variable [tRel 0] evaluates to [CbnNVar 0], which is not below [0]. *)
Lemma cbn_machine_hwf_needs_len {cf : checker_flags} (X_type : abstract_env_impl)
    (X : X_type.π2.π1) :
  ~ cbn_machine_hwf X_type X [vass {| binder_name := nAnon; binder_relevance := Relevant |}
                            (tSort sProp)] 0.
Proof.
  intros h.
  destruct (h (CbnFS (fun _ => CbnFS (fun _ => CbnFS (fun _ => CbnFO)))) 0 (le_n 0))
    as (_ & _ & hw & _ & _).
  assert (hs0 : cbn_hwf 0 cbn_init).
  { intros a cl ha. unfold cbn_heap_get in ha. cbn [cbn_init cbn_st_heap] in ha.
    rewrite cbn_bh_get_holes in ha. discriminate ha. }
  assert (E : exists s',
    cbn_whnf X_type X [vass {| binder_name := nAnon; binder_relevance := Relevant |} (tSort sProp)]
      0 (CbnFS (fun _ => CbnFS (fun _ => CbnFS (fun _ => CbnFO))))
      cbn_env_empty (cbn_mkCode cbn_path_nil cbn_path_nil (tRel 0)) [] [] cbn_init
    = CbnCOk (CbnVNeu (CbnNVar 0) [], [], s')).
  { eexists; reflexivity. }
  destruct E as [s' E].
  destruct (hw _ _ _ _ _ _ _ _ E hs0 (Forall_nil _)) as (_ & _ & hv).
  cbn in hv. lia.
Qed.
