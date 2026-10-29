(* Distributed under the terms of the MIT license. *)

(** * A6, part 2: inductive and axiom spines (untyped)

  Over [ws_cumul_pbE]:
  - one side an inductive spine ([ws_cumul_pbE_Ind_l_inv], [_r_inv]): the other
    side's canonical form reaches the spine;
  - both sides inductive spines ([ws_cumul_pbE_Ind_inv]): the instances are
    compared by F-inst,
    [cmp_global_instance_finst r Σ (compare_universe Σ) pb (IndRef ind) #|l|],
    i.e. at the variance of [max #|l| arity] with the [finst_mode] disjunction;
    base's [cumul_Ind_univ] at [#|l|] is false for under-applied heads;
  - axiom spines ([ws_cumul_pbE_Axiom_l_inv], [_r_inv]);
  - head clashes, at every [pb] ([invert_cumul_ind_prodE], [invert_cumul_sort_indE],
    [invert_cumul_axiom_indE], ...).

  Method as in part 1: a chain from [mkApps (tInd …) l] (or an axiom spine) keeps
  the head and gives a [BE] chain per argument ([chain_mkApps_Ind],
  [chain_mkApps_Const]); U1' keeps the spine ([finst_mkApps_Ind_l/_r],
  [finst_mkApps_Const_l/_r]).

  **The hypotheses are satisfiable:** [ClosedBodies Σ] by any well-formed
  environment ([wf_ClosedBodies]; [wfE_ClosedBodies] for [wfE]);
  [declared_constant Σ cst cdecl] with [cst_body cdecl = None] and
  [prim_op_of Σ cst = None] by an environment with one axiom; every
  [ws_cumul_pbE] premise by reflexivity. Instances: [PCUICEtaA6Instances]. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICEquality PCUICReduction
     PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICWellScopedCumulativity PCUICConversion
     PCUICEtaDefs PCUICEtaScope PCUICEtaCanon PCUICEtaCanonRed PCUICEtaCanonEta PCUICEtaFInst
     PCUICEtaFInstEquiv PCUICEtaI5 PCUICEtaI5Trans PCUICEtaI5A2 PCUICEtaC1b
     PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICWsCumulEtaSubst PCUICEtaA6 PCUICClosedBodies.

(** ** Spine shapes *)

Lemma mkApps_head_inj h h' l l' :
  ~~ isApp h -> ~~ isApp h' -> mkApps h l = mkApps h' l' -> h = h' /\ l = l'.
Proof.
  intros ha ha' e. have e' := f_equal decompose_app e.
  rewrite (decompose_app_mkApps h l ha) (decompose_app_mkApps h' l' ha') in e'.
  now injection e'.
Qed.

Lemma mkApps_rigid_not_Prod h l na A B : isApp h = false -> (forall na A B, h <> tProd na A B) ->
  mkApps h l = tProd na A B -> False.
Proof.
  intros ha hp. destruct l as [|a l] using rev_ind; cbn; [apply hp|].
  rewrite mkApps_app; cbn; discriminate.
Qed.

Lemma mkApps_rigid_not_Sort h l s : isApp h = false -> (forall s, h <> tSort s) ->
  mkApps h l = tSort s -> False.
Proof.
  intros ha hp. destruct l as [|a l] using rev_ind; cbn; [apply hp|].
  rewrite mkApps_app; cbn; discriminate.
Qed.

Lemma eta1_tApp_inv f a y : eta1 (tApp f a) y ->
  (∑ f', eta1 f f' × (y = tApp f' a)) + (∑ a', eta1 a a' × (y = tApp f a')).
Proof.
  intros h. inv_eta h.
  all: first [ left; eexists; split; [eassumption|reflexivity]
             | right; eexists; split; [eassumption|reflexivity] ].
Qed.

Lemma eta1_mkApps_rigid_inv h l y :
  (forall w, eta1 h w -> False) ->
  eta1 (mkApps h l) y -> ∑ l', (y = mkApps h l') × OnOne2 eta1 l l'.
Proof.
  intros hn. revert y. induction l as [|a l IH] using rev_ind; intros y he.
  - exfalso. exact (hn _ he).
  - rewrite mkApps_app in he. cbn in he.
    destruct (eta1_tApp_inv _ _ _ he) as [(f' & hf & ->)|(a' & ha' & ->)].
    + destruct (IH _ hf) as (l' & -> & hl). exists (l' ++ [a]). split; [now rewrite mkApps_app|].
      now apply OnOne2_app_r.
    + exists (l ++ [a']). split; [now rewrite mkApps_app|]. apply OnOne2_app. constructor. exact ha'.
Qed.

Lemma eta_normal_Ind ind u w : eta1 (tInd ind u) w -> False.
Proof. intros h. inv_eta h. Qed.

Lemma eta_normal_Const c u w : eta1 (tConst c u) w -> False.
Proof. intros h. inv_eta h. Qed.

Section A6Ind.

  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ} {r : finst_construct_rule}.

  Local Notation RE Γ := (union (R_c Σ Γ) eta1).
  Local Notation chain Γ := (clos_refl_trans (RE Γ)).
  Local Notation BE Γ := (clos_refl_trans (be_step Σ Γ)).
  Local Notation RF pb n := (eq_term_upto_univ_eta_napp r Σ.1 (compare_universe Σ) (compare_sort Σ) pb n).
  Local Notation WS pb Γ := (ws_cumul_pbE r pb Σ Γ).

  (** ** List plumbing *)

  Lemma All2_BE_red_compose Γ l l0 l' :
    All2 (closed_red Σ Γ) l l0 -> All2 (fun a a' => BE Γ a a') (map canon l0) l' ->
    All2 (fun a a' => BE Γ a a') l l'.
  Proof.
    intros h1. induction h1 as [|x y l l0 hxy _ IH] in l' |- *; cbn; intros h2; depelim h2; constructor.
    - eapply rt_trans; [exact (BE_red Σ Γ _ _ (clrel_rel hxy))|].
      eapply rt_trans; [apply BE_to_canon|eassumption].
    - apply IH. assumption.
  Qed.

  Lemma All2_BE_eta_compose Γ l l0 l' :
    OnOne2 eta1 l l0 -> All2 (fun a a' => BE Γ a a') l0 l' -> All2 (fun a a' => BE Γ a a') l l'.
  Proof.
    intros h1. induction h1 as [x y l hxy|x l l0 _ IH] in l' |- *; intros h2; depelim h2; constructor.
    - eapply rt_trans; [apply BE_eta1; exact hxy|eassumption].
    - assumption.
    - assumption.
    - apply IH. assumption.
  Qed.

  Lemma All2_BE_refl Γ l : All2 (fun a a' => BE Γ a a') l l.
  Proof. apply All2_refl. intros; apply rt_refl. Qed.

  Lemma All2_BE_from_canon Γ l l1 :
    All2 (fun a a' => BE Γ a a') (map canon l) l1 -> All2 (fun a a' => BE Γ a a') l l1.
  Proof.
    induction l as [|a l IH] in l1 |- *; cbn; intros h; depelim h; constructor.
    - eapply rt_trans; [apply BE_to_canon|eassumption].
    - apply IH. assumption.
  Qed.

  Lemma All2_WS_zip Γ l l' l1 l1' :
    is_closed_context Γ -> forallb (is_open_term Γ) l -> forallb (is_open_term Γ) l' ->
    All2 (fun a a' => BE Γ a a') l l1 -> All2 (fun a a' => BE Γ a a') l' l1' ->
    All2 (RF Conv 0) l1 l1' -> All2 (WS Conv Γ) l l'.
  Proof.
    intros hΓ hl hl' h1 h2 e. induction e as [|a1 a1' l1 l1' ea _ IH] in l, l', hl, hl', h1, h2 |- *.
    - depelim h1; depelim h2; constructor.
    - depelim h1. depelim h2. move: hl hl' => /= /andP [ha hl] /andP [ha' hl'].
      constructor; [|eapply IH; eassumption].
      constructor; [exact hΓ|exact ha|exact ha'|].
      apply (BE_JoinE Σ r Γ Conv _ _ a1 a1'); [eassumption|eassumption|exact (RF_canon Σ r _ _ _ _ ea)].
  Qed.

  Lemma forallb_open_mkApps (Γ : context) h l : is_open_term Γ (mkApps h l) -> forallb (is_open_term Γ) l.
  Proof. rewrite on_free_vars_mkApps. move/andP => [_ h']. exact h'. Qed.

  Lemma open_mkApps_canon (Γ : context) h l : canon h = h -> is_open_term Γ (mkApps h l) ->
    is_open_term Γ (mkApps h (map canon l)).
  Proof.
    intros ch ho. have := canon_is_open_term Γ _ ho. rewrite canon_mkApps ch. exact id.
  Qed.

  (** ** Chains from rigid spines *)

  Lemma chain_mkApps_Ind Γ ind u l v :
    is_closed_context Γ -> is_open_term Γ (mkApps (tInd ind u) l) ->
    chain Γ (mkApps (tInd ind u) l) v ->
    ∑ l', (v = mkApps (tInd ind u) l') × All2 (fun a a' => BE Γ a a') l l'.
  Proof.
    intros hΓ hl h. apply clos_rt_rt1n_iff in h.
    remember (mkApps (tInd ind u) l) as x eqn:Ex.
    induction h as [x|x y v s _ IH] in l, hl, Ex |- *; subst x.
    - exists l. split; [reflexivity|apply All2_BE_refl].
    - destruct s as [[y0 [hr ->]]|he].
      + have hcr : Σ ;;; Γ ⊢ mkApps (tInd ind u) l ⇝ y0 := closed_red_of hΓ hl (red1_red _ _ _ _ hr).
        have hy0 := closed_red_open_right_cb (wfΣ := wfΣ) hcr.
        destruct (invert_red_mkApps_tInd_cb (Σ := Σ) (cbΣ := wfΣ) l y0 hcr) as (l0 & [-> _ hl0]).
        have e0 : canon (mkApps (tInd ind u) l0) = mkApps (tInd ind u) (map canon l0) by now rewrite canon_mkApps.
        destruct (IH (map canon l0) e0 (canon_is_open_term Γ _ hy0)) as (l' & -> & hl').
        exists l'. split; [reflexivity|]. exact (All2_BE_red_compose Γ l l0 l' hl0 hl').
      + destruct (eta1_mkApps_rigid_inv (tInd ind u) l y (eta_normal_Ind ind u) he) as (l0 & -> & hl0).
        destruct (IH l0 eq_refl (eta1_on_free_vars _ _ he _ hl)) as (l' & -> & hl').
        exists l'. split; [reflexivity|]. exact (All2_BE_eta_compose Γ l l0 l' hl0 hl').
  Qed.

  Lemma chain_mkApps_Const Γ cst cdecl u l v :
    declared_constant Σ cst cdecl -> cst_body cdecl = None ->
    (* trunk's premise of [invert_red_axiom_app_cb]: [cst] is not a primitive
       operation, whose saturated application would reduce *)
    prim_op_of Σ cst = None ->
    is_closed_context Γ -> is_open_term Γ (mkApps (tConst cst u) l) ->
    chain Γ (mkApps (tConst cst u) l) v ->
    ∑ l', (v = mkApps (tConst cst u) l') × All2 (fun a a' => BE Γ a a') l l'.
  Proof.
    intros hd hb hnop hΓ hl h. apply clos_rt_rt1n_iff in h.
    remember (mkApps (tConst cst u) l) as x eqn:Ex.
    induction h as [x|x y v s _ IH] in l, hl, Ex |- *; subst x.
    - exists l. split; [reflexivity|apply All2_BE_refl].
    - destruct s as [[y0 [hr ->]]|he].
      + have hcr : Σ ;;; Γ ⊢ mkApps (tConst cst u) l ⇝ y0 := closed_red_of hΓ hl (red1_red _ _ _ _ hr).
        have hy0 := closed_red_open_right_cb (wfΣ := wfΣ) hcr.
        destruct (invert_red_axiom_app_cb (Σ := Σ) (cbΣ := wfΣ) hd hb hnop hcr) as (l0 & -> & hl0).
        have e0 : canon (mkApps (tConst cst u) l0) = mkApps (tConst cst u) (map canon l0) by now rewrite canon_mkApps.
        destruct (IH (map canon l0) e0 (canon_is_open_term Γ _ hy0)) as (l' & -> & hl').
        exists l'. split; [reflexivity|]. exact (All2_BE_red_compose Γ l l0 l' hl0 hl').
      + destruct (eta1_mkApps_rigid_inv (tConst cst u) l y (eta_normal_Const cst u) he) as (l0 & -> & hl0).
        destruct (IH l0 eq_refl (eta1_on_free_vars _ _ he _ hl)) as (l' & -> & hl').
        exists l'. split; [reflexivity|]. exact (All2_BE_eta_compose Γ l l0 l' hl0 hl').
  Qed.

  (** ** U1' keeps rigid spines *)

  Lemma finst_tApp_l pb n f a v : RF pb n (tApp f a) v ->
    ∑ f' a', [× v = tApp f' a', RF pb (S n) f f' & RF Conv 0 a a'].
  Proof. intros e. depelim e. do 2 eexists; split; [reflexivity|eassumption|eassumption]. Qed.

  Lemma finst_tApp_r pb n f a v : RF pb n v (tApp f a) ->
    ∑ f' a', [× v = tApp f' a', RF pb (S n) f' f & RF Conv 0 a' a].
  Proof. intros e. depelim e. do 2 eexists; split; [reflexivity|eassumption|eassumption]. Qed.

  Lemma finst_mkApps_Ind_l pb n ind u l v : RF pb n (mkApps (tInd ind u) l) v ->
    ∑ u' l', [× v = mkApps (tInd ind u') l',
      cmp_global_instance_finst r Σ.1 (compare_universe Σ) pb (IndRef ind) (#|l| + n) u u'
      & All2 (RF Conv 0) l l'].
  Proof.
    revert n v. induction l as [|a l IH] using rev_ind; intros n v e.
    - cbn in e. depelim e. eexists _, []. split; [reflexivity|eassumption|constructor].
    - rewrite mkApps_app in e. cbn in e.
      destruct (finst_tApp_l _ _ _ _ _ e) as (f' & a' & [-> ef ea]).
      destruct (IH _ _ ef) as (u' & l' & [-> hu hl]).
      exists u', (l' ++ [a']). split.
      + now rewrite mkApps_app.
      + rewrite length_app /=. replace (#|l| + 1 + n) with (#|l| + S n) by lia. exact hu.
      + apply All2_app; [exact hl|constructor; [exact ea|constructor]].
  Qed.

  Lemma finst_mkApps_Ind_r pb n ind u l v : RF pb n v (mkApps (tInd ind u) l) ->
    ∑ u' l', [× v = mkApps (tInd ind u') l',
      cmp_global_instance_finst r Σ.1 (compare_universe Σ) pb (IndRef ind) (#|l| + n) u' u
      & All2 (RF Conv 0) l' l].
  Proof.
    revert n v. induction l as [|a l IH] using rev_ind; intros n v e.
    - cbn in e. depelim e. eexists _, []. split; [reflexivity|eassumption|constructor].
    - rewrite mkApps_app in e. cbn in e.
      destruct (finst_tApp_r _ _ _ _ _ e) as (f' & a' & [-> ef ea]).
      destruct (IH _ _ ef) as (u' & l' & [-> hu hl]).
      exists u', (l' ++ [a']). split.
      + now rewrite mkApps_app.
      + rewrite length_app /=. replace (#|l| + 1 + n) with (#|l| + S n) by lia. exact hu.
      + apply All2_app; [exact hl|constructor; [exact ea|constructor]].
  Qed.

  Lemma finst_mkApps_Const_l pb n c u l v : RF pb n (mkApps (tConst c u) l) v ->
    ∑ u' l', [× v = mkApps (tConst c u') l',
      cmp_universe_instance (compare_universe Σ Conv) u u' & All2 (RF Conv 0) l l'].
  Proof.
    revert n v. induction l as [|a l IH] using rev_ind; intros n v e.
    - cbn in e. depelim e. eexists _, []. split; [reflexivity|eassumption|constructor].
    - rewrite mkApps_app in e. cbn in e.
      destruct (finst_tApp_l _ _ _ _ _ e) as (f' & a' & [-> ef ea]).
      destruct (IH _ _ ef) as (u' & l' & [-> hu hl]).
      exists u', (l' ++ [a']). split; [now rewrite mkApps_app|exact hu|].
      apply All2_app; [exact hl|constructor; [exact ea|constructor]].
  Qed.

  Lemma finst_mkApps_Const_r pb n c u l v : RF pb n v (mkApps (tConst c u) l) ->
    ∑ u' l', [× v = mkApps (tConst c u') l',
      cmp_universe_instance (compare_universe Σ Conv) u' u & All2 (RF Conv 0) l' l].
  Proof.
    revert n v. induction l as [|a l IH] using rev_ind; intros n v e.
    - cbn in e. depelim e. eexists _, []. split; [reflexivity|eassumption|constructor].
    - rewrite mkApps_app in e. cbn in e.
      destruct (finst_tApp_r _ _ _ _ _ e) as (f' & a' & [-> ef ea]).
      destruct (IH _ _ ef) as (u' & l' & [-> hu hl]).
      exists u', (l' ++ [a']). split; [now rewrite mkApps_app|exact hu|].
      apply All2_app; [exact hl|constructor; [exact ea|constructor]].
  Qed.

  (** ** Inductive spines (i30-i32, i42-i46) *)

  Lemma ws_cumul_pbE_Ind_l_inv {pb Γ ind ui l T} :
    WS pb Γ (mkApps (tInd ind ui) l) T ->
    ∑ ui' l', [× chain Γ (canon T) (mkApps (tInd ind ui') l'),
      cmp_global_instance_finst r Σ.1 (compare_universe Σ) pb (IndRef ind) #|l| ui ui'
      & All2 (WS Conv Γ) l l'].
  Proof.
    intros [hΓ hl hr (v & v' & hv & hv' & e)].
    rewrite canon_mkApps in hv. cbn [canon] in hv.
    destruct (chain_mkApps_Ind Γ ind ui (map canon l) v hΓ (open_mkApps_canon Γ _ l eq_refl hl) hv)
      as (l1 & -> & hl1).
    destruct (finst_mkApps_Ind_l _ _ _ _ _ _ e) as (ui' & l2 & [-> hu hl2]).
    have ho := chain_open (wfΣ := wfΣ) Γ T _ hΓ hr hv'.
    exists ui', l2. split.
    - exact hv'.
    - rewrite Nat.add_0_r -(All2_length hl1) length_map in hu. exact hu.
    - exact (All2_WS_zip Γ l l2 l1 l2 hΓ (forallb_open_mkApps Γ _ _ hl) (forallb_open_mkApps Γ _ _ ho)
               (All2_BE_from_canon Γ l l1 hl1) (All2_BE_refl Γ l2) hl2).
  Qed.

  Lemma ws_cumul_pbE_Ind_r_inv {pb Γ ind ui l T} :
    WS pb Γ T (mkApps (tInd ind ui) l) ->
    ∑ ui' l', [× chain Γ (canon T) (mkApps (tInd ind ui') l'),
      cmp_global_instance_finst r Σ.1 (compare_universe Σ) pb (IndRef ind) #|l| ui' ui
      & ws_cumul_pbE_terms r Σ Γ l' l].
  Proof.
    intros [hΓ hl hr (v & v' & hv & hv' & e)].
    rewrite canon_mkApps in hv'. cbn [canon] in hv'.
    destruct (chain_mkApps_Ind Γ ind ui (map canon l) v' hΓ (open_mkApps_canon Γ _ l eq_refl hr) hv')
      as (l1 & -> & hl1).
    destruct (finst_mkApps_Ind_r _ _ _ _ _ _ e) as (ui' & l2 & [-> hu hl2]).
    have ho := chain_open (wfΣ := wfΣ) Γ T _ hΓ hl hv.
    exists ui', l2. split.
    - exact hv.
    - rewrite Nat.add_0_r -(All2_length hl1) length_map in hu. exact hu.
    - exact (All2_WS_zip Γ l2 l l2 l1 hΓ (forallb_open_mkApps Γ _ _ ho) (forallb_open_mkApps Γ _ _ hr)
               (All2_BE_refl Γ l2) (All2_BE_from_canon Γ l l1 hl1) hl2).
  Qed.

  Lemma ws_cumul_pbE_Ind_inv {pb Γ ind ind' ui ui' l l'} :
    WS pb Γ (mkApps (tInd ind ui) l) (mkApps (tInd ind' ui') l') ->
    [× ind = ind', cmp_global_instance_finst r Σ.1 (compare_universe Σ) pb (IndRef ind) #|l| ui ui',
       is_closed_context Γ & ws_cumul_pbE_terms r Σ Γ l l'].
  Proof.
    intros [hΓ hl hr (v & v' & hv & hv' & e)].
    rewrite canon_mkApps in hv. rewrite canon_mkApps in hv'. cbn [canon] in hv, hv'.
    destruct (chain_mkApps_Ind Γ ind ui (map canon l) v hΓ (open_mkApps_canon Γ _ l eq_refl hl) hv)
      as (l1 & -> & hl1).
    destruct (chain_mkApps_Ind Γ ind' ui' (map canon l') v' hΓ (open_mkApps_canon Γ _ l' eq_refl hr) hv')
      as (l1' & -> & hl1').
    destruct (finst_mkApps_Ind_l _ _ _ _ _ _ e) as (ui2 & l2 & [E hu hl2]).
    destruct (mkApps_head_inj (tInd ind' ui') (tInd ind ui2) _ _ eq_refl eq_refl E) as [E1 <-].
    injection E1 as -> ->.
    split.
    - reflexivity.
    - rewrite Nat.add_0_r -(All2_length hl1) length_map in hu. exact hu.
    - exact hΓ.
    - exact (All2_WS_zip Γ l l' l1 l1' hΓ (forallb_open_mkApps Γ _ _ hl) (forallb_open_mkApps Γ _ _ hr)
               (All2_BE_from_canon Γ l l1 hl1) (All2_BE_from_canon Γ l' l1' hl1') hl2).
  Qed.

  (** i44, base's [Cumul] form with [eqb]. *)
  Lemma invert_cumul_ind_indE {Γ ind ind' u u' args args'} :
    WS Cumul Γ (mkApps (tInd ind u) args) (mkApps (tInd ind' u') args') ->
    (eqb ind ind' * cmp_global_instance_finst r Σ.1 (compare_universe Σ) Cumul (IndRef ind) #|args| u u'
     * ws_cumul_pbE_terms r Σ Γ args args').
  Proof.
    intros h. destruct (ws_cumul_pbE_Ind_inv h) as [-> hu _ ha].
    split; [split; [apply eqb_refl|exact hu]|exact ha].
  Qed.

  (** Head clashes (i42, i43, i45, i46), at every [pb]. *)
  Lemma invert_cumul_prod_indE {pb Γ na dom codom ind u args} :
    WS pb Γ (tProd na dom codom) (mkApps (tInd ind u) args) -> False.
  Proof.
    intros [hΓ hl hr (v & v' & hv & hv' & e)].
    rewrite canon_mkApps in hv'. cbn [canon] in hv, hv'.
    destruct (chain_Prod _ _ _ _ _ hv) as (na1 & A1 & B1 & [-> _ _ _]).
    destruct (chain_mkApps_Ind Γ ind u (map canon args) v' hΓ (open_mkApps_canon Γ _ args eq_refl hr) hv')
      as (l1 & -> & _).
    destruct (finst_Prod_l _ _ _ _ _ _ e) as (na2 & A2 & B2 & [E _ _ _]).
    exact (mkApps_rigid_not_Prod (tInd ind u) _ _ _ _ eq_refl (fun _ _ _ => ltac:(discriminate)) E).
  Qed.

  Lemma invert_cumul_ind_prodE {pb Γ na dom codom ind u args} :
    WS pb Γ (mkApps (tInd ind u) args) (tProd na dom codom) -> False.
  Proof.
    intros [hΓ hl hr (v & v' & hv & hv' & e)].
    rewrite canon_mkApps in hv. cbn [canon] in hv, hv'.
    destruct (chain_Prod _ _ _ _ _ hv') as (na1 & A1 & B1 & [-> _ _ _]).
    destruct (chain_mkApps_Ind Γ ind u (map canon args) v hΓ (open_mkApps_canon Γ _ args eq_refl hl) hv)
      as (l1 & -> & _).
    destruct (finst_Prod_r _ _ _ _ _ _ e) as (na2 & A2 & B2 & [E _ _ _]).
    exact (mkApps_rigid_not_Prod (tInd ind u) _ _ _ _ eq_refl (fun _ _ _ => ltac:(discriminate)) E).
  Qed.

  Lemma invert_cumul_sort_indE {pb Γ s ind u args} :
    WS pb Γ (tSort s) (mkApps (tInd ind u) args) -> False.
  Proof.
    intros [hΓ hl hr (v & v' & hv & hv' & e)].
    rewrite canon_mkApps in hv'. cbn [canon] in hv, hv'.
    apply chain_Sort in hv. subst v.
    destruct (chain_mkApps_Ind Γ ind u (map canon args) v' hΓ (open_mkApps_canon Γ _ args eq_refl hr) hv')
      as (l1 & -> & _).
    destruct (finst_Sort_l _ _ _ _ e) as (s' & E & _).
    exact (mkApps_rigid_not_Sort (tInd ind u) _ _ eq_refl (fun _ => ltac:(discriminate)) E).
  Qed.

  Lemma invert_cumul_ind_sortE {pb Γ s ind u args} :
    WS pb Γ (mkApps (tInd ind u) args) (tSort s) -> False.
  Proof.
    intros [hΓ hl hr (v & v' & hv & hv' & e)].
    rewrite canon_mkApps in hv. cbn [canon] in hv, hv'.
    apply chain_Sort in hv'. subst v'.
    destruct (chain_mkApps_Ind Γ ind u (map canon args) v hΓ (open_mkApps_canon Γ _ args eq_refl hl) hv)
      as (l1 & -> & _).
    destruct (finst_Sort_r _ _ _ _ e) as (s' & E & _).
    exact (mkApps_rigid_not_Sort (tInd ind u) _ _ eq_refl (fun _ => ltac:(discriminate)) E).
  Qed.

  (** ** Axiom spines (i33-i36) *)

  Lemma ws_cumul_pbE_Axiom_l_inv {pb Γ cst u args cdecl T} :
    declared_constant Σ cst cdecl -> cst_body cdecl = None -> prim_op_of Σ cst = None ->
    WS pb Γ (mkApps (tConst cst u) args) T ->
    ∑ u' args', [× chain Γ (canon T) (mkApps (tConst cst u') args'),
      All2 (WS Conv Γ) args args' & cmp_universe_instance (compare_universe Σ Conv) u u'].
  Proof.
    intros hd hb hnop [hΓ hl hr (v & v' & hv & hv' & e)].
    rewrite canon_mkApps in hv. cbn [canon] in hv.
    destruct (chain_mkApps_Const Γ cst cdecl u (map canon args) v hd hb hnop hΓ
                (open_mkApps_canon Γ _ args eq_refl hl) hv) as (l1 & -> & hl1).
    destruct (finst_mkApps_Const_l _ _ _ _ _ _ e) as (u' & l2 & [-> hu hl2]).
    have ho := chain_open (wfΣ := wfΣ) Γ T _ hΓ hr hv'.
    exists u', l2. split; [exact hv'| |exact hu].
    exact (All2_WS_zip Γ args l2 l1 l2 hΓ (forallb_open_mkApps Γ _ _ hl) (forallb_open_mkApps Γ _ _ ho)
             (All2_BE_from_canon Γ args l1 hl1) (All2_BE_refl Γ l2) hl2).
  Qed.

  Lemma ws_cumul_pbE_Axiom_r_inv {pb Γ cst u args cdecl T} :
    declared_constant Σ cst cdecl -> cst_body cdecl = None -> prim_op_of Σ cst = None ->
    WS pb Γ T (mkApps (tConst cst u) args) ->
    ∑ u' args', [× chain Γ (canon T) (mkApps (tConst cst u') args'),
      All2 (WS Conv Γ) args' args & cmp_universe_instance (compare_universe Σ Conv) u' u].
  Proof.
    intros hd hb hnop [hΓ hl hr (v & v' & hv & hv' & e)].
    rewrite canon_mkApps in hv'. cbn [canon] in hv'.
    destruct (chain_mkApps_Const Γ cst cdecl u (map canon args) v' hd hb hnop hΓ
                (open_mkApps_canon Γ _ args eq_refl hr) hv') as (l1 & -> & hl1).
    destruct (finst_mkApps_Const_r _ _ _ _ _ _ e) as (u' & l2 & [-> hu hl2]).
    have ho := chain_open (wfΣ := wfΣ) Γ T _ hΓ hl hv.
    exists u', l2. split; [exact hv| |exact hu].
    exact (All2_WS_zip Γ l2 args l2 l1 hΓ (forallb_open_mkApps Γ _ _ ho) (forallb_open_mkApps Γ _ _ hr)
             (All2_BE_refl Γ l2) (All2_BE_from_canon Γ args l1 hl1) hl2).
  Qed.

  Lemma invert_cumul_axiom_indE {pb Γ cst cdecl u ind u' args args'} :
    declared_constant Σ cst cdecl -> cst_body cdecl = None -> prim_op_of Σ cst = None ->
    WS pb Γ (mkApps (tConst cst u) args) (mkApps (tInd ind u') args') -> False.
  Proof.
    intros hd hb hnop [hΓ hl hr (v & v' & hv & hv' & e)].
    rewrite canon_mkApps in hv. rewrite canon_mkApps in hv'. cbn [canon] in hv, hv'.
    destruct (chain_mkApps_Const Γ cst cdecl u (map canon args) v hd hb hnop hΓ
                (open_mkApps_canon Γ _ args eq_refl hl) hv) as (l1 & -> & _).
    destruct (chain_mkApps_Ind Γ ind u' (map canon args') v' hΓ (open_mkApps_canon Γ _ args' eq_refl hr) hv')
      as (l1' & -> & _).
    destruct (finst_mkApps_Const_l _ _ _ _ _ _ e) as (u2 & l2 & [E _ _]).
    destruct (mkApps_head_inj (tInd ind u') (tConst cst u2) _ _ eq_refl eq_refl E) as [E1 _].
    discriminate E1.
  Qed.

  Lemma invert_cumul_axiom_prodE {pb Γ cst cdecl u args na dom codom} :
    declared_constant Σ cst cdecl -> cst_body cdecl = None -> prim_op_of Σ cst = None ->
    WS pb Γ (mkApps (tConst cst u) args) (tProd na dom codom) -> False.
  Proof.
    intros hd hb hnop [hΓ hl hr (v & v' & hv & hv' & e)].
    rewrite canon_mkApps in hv. cbn [canon] in hv, hv'.
    destruct (chain_Prod _ _ _ _ _ hv') as (na1 & A1 & B1 & [-> _ _ _]).
    destruct (chain_mkApps_Const Γ cst cdecl u (map canon args) v hd hb hnop hΓ
                (open_mkApps_canon Γ _ args eq_refl hl) hv) as (l1 & -> & _).
    destruct (finst_Prod_r _ _ _ _ _ _ e) as (na2 & A2 & B2 & [E _ _ _]).
    exact (mkApps_rigid_not_Prod (tConst cst u) _ _ _ _ eq_refl (fun _ _ _ => ltac:(discriminate)) E).
  Qed.


End A6Ind.
