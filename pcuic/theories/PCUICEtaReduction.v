(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICLiftSubst
     PCUICCases.
From MetaRocq.PCUIC Require Export PCUICEtaDefs.
From MetaRocq.PCUIC Require Import PCUICEtaConfluence.

Import ListNotations.
Set Default Goal Selector "!".

(** * η closure on application spines (plan §3 U4, L1)

  The definitions [eta1], [eta1_ind_all], [eta := clos_refl_trans eta1] and
  [upto_domain] live in [PCUICEtaDefs] (L2); the substitution/lifting cluster
  ([eta1_subst], [eta_subst_term], [subst_eta], [eta_subst], [eta1_lift],
  [weakening_eta]) and the one-hole congruence toolkit live in
  [PCUICEtaConfluence] (L2). This file adds only the spine lemmas that the C3
  provers require, under the names agreed with EtaL2 / C3Prover3. *)

Derive Signature for eta1.

(** ** Head and argument congruence for [mkApps] *)

Lemma eta1_mkApps_head f f' l : eta1 f f' -> eta1 (mkApps f l) (mkApps f' l).
Proof.
  induction l as [|a l IH] in f, f' |- *; cbn; [trivial|].
  intro h. apply IH. now apply app_eta_l.
Qed.

Lemma eta_mkApps_head f f' l : eta f f' -> eta (mkApps f l) (mkApps f' l).
Proof.
  induction 1.
  - apply rt_step. now apply eta1_mkApps_head.
  - apply rt_refl.
  - eapply rt_trans; eassumption.
Qed.

Lemma eta1_mkApps_args l l' :
  OnOne2 eta1 l l' -> forall f, eta1 (mkApps f l) (mkApps f l').
Proof.
  induction 1 as [hd hd' tl h|hd tl tl' h IH]; intro f; cbn.
  - apply eta1_mkApps_head. now apply app_eta_r.
  - apply IH.
Qed.

Lemma eta_mkApps_args f l l' :
  OnOne2 eta1 l l' -> eta (mkApps f l) (mkApps f l').
Proof. intro h. apply rt_step. now apply eta1_mkApps_args. Qed.

(** ** Inversion of a single η step on an application spine *)

Lemma eta1_mkApps_inv M l : forall N,
  eta1 (mkApps M l) N ->
  (∑ M', eta1 M M' × N = mkApps M' l) + (∑ l', OnOne2 eta1 l l' × N = mkApps M l').
Proof.
  induction l as [|x l IH] using MRList.rev_ind; intros N h.
  - cbn in h. left. exists N. split; [exact h|reflexivity].
  - rewrite mkApps_app /= in h. depelim h.
    + destruct (IH _ h) as [[M' [hM ->]]|[l' [hl ->]]].
      * left. exists M'. split; [exact hM|]. now rewrite mkApps_app.
      * right. exists (l' ++ [x]). split.
        -- now apply OnOne2_app_r.
        -- now rewrite mkApps_app.
    + right. exists (l ++ [N2]). split.
      * apply OnOne2_app. now constructor.
      * now rewrite mkApps_app.
Qed.

(** ** η preserves a constructor head *)

Lemma eta1_isConstruct_app a a' :
  eta1 a a' -> isConstruct_app a = true -> isConstruct_app a' = true.
Proof.
  intros h hc.
  unfold isConstruct_app in hc.
  destruct (decompose_app a) as [f args] eqn:E; cbn in hc.
  destruct f; try discriminate.
  apply decompose_app_inv in E. subst a.
  apply eta1_mkApps_inv in h as [[M' [hM ->]]|[l' [hl ->]]].
  - depelim hM.
  - unfold isConstruct_app. now rewrite decompose_app_mkApps.
Qed.

(** ** An [OnOne2] step seen through [nth_error] *)

Lemma onone2_eta_nth_error l l' k a :
  OnOne2 eta1 l l' ->
  nth_error l k = Some a ->
  ∑ a', nth_error l' k = Some a' × clos_refl eta1 a a'.
Proof.
  intro h. revert k a.
  induction h as [hd hd' tl hr|hd tl tl' hr IH]; intros [|k] b hb; cbn in hb |- *.
  - noconf hb. exists hd'. split; [reflexivity|]. now apply r_step.
  - exists b. split; [exact hb|]. apply r_refl.
  - exists b. split; [exact hb|]. apply r_refl.
  - now apply IH.
Qed.

(** ** η unfolding of (co)fixpoints (needs L2's [eta_subst]) *)

Lemma All2_fix_subst mfix mfix' :
  #|mfix| = #|mfix'| ->
  (forall j, eta (tFix mfix j) (tFix mfix' j)) ->
  All2 eta (fix_subst mfix) (fix_subst mfix').
Proof.
  intros Hlen Hj. unfold fix_subst. rewrite Hlen.
  generalize #|mfix'| as n. induction n as [|n IH]; cbn.
  - constructor.
  - constructor; [apply Hj|exact IH].
Qed.

Lemma All2_cofix_subst mfix mfix' :
  #|mfix| = #|mfix'| ->
  (forall j, eta (tCoFix mfix j) (tCoFix mfix' j)) ->
  All2 eta (cofix_subst mfix) (cofix_subst mfix').
Proof.
  intros Hlen Hj. unfold cofix_subst. rewrite Hlen.
  generalize #|mfix'| as n. induction n as [|n IH]; cbn.
  - constructor.
  - constructor; [apply Hj|exact IH].
Qed.

Lemma eta1_fix_unfold mfix idx N narg fn :
  eta1 (tFix mfix idx) N ->
  unfold_fix mfix idx = Some (narg, fn) ->
  ∑ mfix' fn', [× N = tFix mfix' idx,
                  unfold_fix mfix' idx = Some (narg, fn') & eta fn fn'].
Proof.
  intros H Hunf.
  unfold unfold_fix in Hunf.
  destruct (nth_error mfix idx) as [d|] eqn:Hd; [|discriminate].
  noconf Hunf.
  depelim H.
  - (* fix_eta_ty *)
    match goal with o : OnOne2 _ _ _ |- _ => rename o into HO end.
    pose proof (Hlen := OnOne2_length HO).
    destruct (OnOne2_nth_error _ _ _ _ _ HO Hd) as [d1 [Hd1 Hdd]].
    assert (Hr : (rarg d = rarg d1) × eta (dbody d) (dbody d1)).
    { destruct Hdd as [->|[_ Heq]].
      - split; [reflexivity|apply rt_refl].
      - assert (Hbd : dbody d = dbody d1) by exact (f_equal (fun z => snd (fst z)) Heq).
        split; [exact (f_equal snd Heq)| rewrite Hbd; apply rt_refl]. }
    destruct Hr as [Hr Hb].
    exists mfix1, (subst0 (fix_subst mfix1) (dbody d1)). split.
    + reflexivity.
    + unfold unfold_fix. rewrite Hd1 -Hr. reflexivity.
    + eapply eta_subst; [|exact Hb].
      apply All2_fix_subst; [exact Hlen|].
      intro j. apply rt_step. solve [econstructor; eassumption].
  - (* fix_eta_body *)
    match goal with o : OnOne2 _ _ _ |- _ => rename o into HO end.
    pose proof (Hlen := OnOne2_length HO).
    destruct (OnOne2_nth_error _ _ _ _ _ HO Hd) as [d1 [Hd1 Hdd]].
    assert (Hr : (rarg d = rarg d1) × eta (dbody d) (dbody d1)).
    { destruct Hdd as [->|[He Heq]].
      - split; [reflexivity|apply rt_refl].
      - split; [exact (f_equal snd Heq)|apply rt_step; exact He]. }
    destruct Hr as [Hr Hb].
    exists mfix1, (subst0 (fix_subst mfix1) (dbody d1)). split.
    + reflexivity.
    + unfold unfold_fix. rewrite Hd1 -Hr. reflexivity.
    + eapply eta_subst; [|exact Hb].
      apply All2_fix_subst; [exact Hlen|].
      intro j. apply rt_step. solve [econstructor; eassumption].
Qed.

Lemma eta1_cofix_unfold mfix idx N narg fn :
  eta1 (tCoFix mfix idx) N ->
  unfold_cofix mfix idx = Some (narg, fn) ->
  ∑ mfix' fn', [× N = tCoFix mfix' idx,
                  unfold_cofix mfix' idx = Some (narg, fn') & eta fn fn'].
Proof.
  intros H Hunf.
  unfold unfold_cofix in Hunf.
  destruct (nth_error mfix idx) as [d|] eqn:Hd; [|discriminate].
  noconf Hunf.
  depelim H.
  - (* cofix_eta_ty *)
    match goal with o : OnOne2 _ _ _ |- _ => rename o into HO end.
    pose proof (Hlen := OnOne2_length HO).
    destruct (OnOne2_nth_error _ _ _ _ _ HO Hd) as [d1 [Hd1 Hdd]].
    assert (Hr : (rarg d = rarg d1) × eta (dbody d) (dbody d1)).
    { destruct Hdd as [->|[_ Heq]].
      - split; [reflexivity|apply rt_refl].
      - assert (Hbd : dbody d = dbody d1) by exact (f_equal (fun z => snd (fst z)) Heq).
        split; [exact (f_equal snd Heq)| rewrite Hbd; apply rt_refl]. }
    destruct Hr as [Hr Hb].
    exists mfix1, (subst0 (cofix_subst mfix1) (dbody d1)). split.
    + reflexivity.
    + unfold unfold_cofix. rewrite Hd1 -Hr. reflexivity.
    + eapply eta_subst; [|exact Hb].
      apply All2_cofix_subst; [exact Hlen|].
      intro j. apply rt_step. solve [econstructor; eassumption].
  - (* cofix_eta_body *)
    match goal with o : OnOne2 _ _ _ |- _ => rename o into HO end.
    pose proof (Hlen := OnOne2_length HO).
    destruct (OnOne2_nth_error _ _ _ _ _ HO Hd) as [d1 [Hd1 Hdd]].
    assert (Hr : (rarg d = rarg d1) × eta (dbody d) (dbody d1)).
    { destruct Hdd as [->|[He Heq]].
      - split; [reflexivity|apply rt_refl].
      - split; [exact (f_equal snd Heq)|apply rt_step; exact He]. }
    destruct Hr as [Hr Hb].
    exists mfix1, (subst0 (cofix_subst mfix1) (dbody d1)). split.
    + reflexivity.
    + unfold unfold_cofix. rewrite Hd1 -Hr. reflexivity.
    + eapply eta_subst; [|exact Hb].
      apply All2_cofix_subst; [exact Hlen|].
      intro j. apply rt_step. solve [econstructor; eassumption].
Qed.
