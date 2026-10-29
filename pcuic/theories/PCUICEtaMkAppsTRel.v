(* Distributed under the terms of the MIT license. *)

(** * Variable-headed spines under [ws_cumul_pbE]

  [ws_cumul_pbE_mkApps_tRel]: two applications of one local assumption [tRel n]
  (its declaration in [Γ] has no body) related by [ws_cumul_pbE Cumul] have
  pointwise convertible arguments ([ws_cumul_pbE_terms]): the same number of
  arguments, each pair related by [ws_cumul_pbE Conv]. It is the η counterpart of
  base [ws_cumul_pb_mkApps_tRel] ([PCUICInductiveInversion]); it takes
  [ClosedBodies Σ] where base takes [wf Σ], and every [wf] environment gives it
  ([wf_ClosedBodies]).

  ** Route

  Base's proof reads common reducts compared by [compare_term]
  ([ws_cumul_pb_red]); that route is false with η ([ws_cumul_pbE_red_false],
  [PCUICWsCumulEtaCtx]). This proof reads the join [JoinE] that defines
  [ws_cumul_pbE], as the inversions of [PCUICEtaA6Ind] do:
  - a [(R_c ∪ eta1)*] chain from [mkApps (tRel n) l] keeps the head and the number
    of arguments, and gives a [BE] chain per argument ([chain_mkApps_Rel]).
    Reduction of the spine is argumentwise, because [tRel n] has no body
    ([invert_red_mkApps_tRel_cb], from [red_mkApps_tRel_cb]). An η step contracts
    a λ; the spine is an application with a variable head ([eta_normal_Rel]), so
    the step falls inside one argument ([eta1_mkApps_rigid_inv]);
  - the comparison that ends the join keeps the spine and compares the arguments
    at [Conv], also when the spines are compared at [Cumul]
    ([finst_mkApps_Rel_l]; [eqη_App] compares its argument at [Conv]);
  - the argument pairs then join pointwise ([All2_WS_zip]).

  **The hypotheses are satisfiable:** [ClosedBodies Σ] by any well-formed
  environment ([wf_ClosedBodies]); the [nth_error] and [decl_body] premises by any
  local assumption; the relation premise by reflexivity. The instance below
  ([ws_cumul_pbE_mkApps_tRel_inst]) applies the lemma to two spines that differ by
  one η step in an argument, [f (λx:Prop. g x)] and [f g], in the context
  [g : Prop → Prop, f : (Prop → Prop) → Prop] of the empty environment. The
  environment is proved [wf] and [wfE], the context [wf_localE], and both spines
  have type [Prop] over [typingE] ([tr_spines_typed]). *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Environment.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICEquality PCUICReduction
     PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICWellScopedCumulativity PCUICConfluence PCUICConversion
     PCUICEtaDefs PCUICEtaScope PCUICEtaCanon PCUICEtaCanonRed PCUICEtaFInst
     PCUICEtaI5 PCUICEtaI5A2 PCUICEtaC1b
     PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICEtaA6 PCUICEtaA6Ind
     PCUICTypingEta PCUICClosedBodies PCUICClosedTyp.

(** A variable is η-normal. *)
Lemma eta_normal_Rel n w : eta1 (tRel n) w -> False.
Proof. intros h. inv_eta h. Qed.

Section MkAppsRel.

  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ}.

  Local Notation RE Γ := (union (R_c Σ Γ) eta1).
  Local Notation chain Γ := (clos_refl_trans (RE Γ)).
  Local Notation BE Γ := (clos_refl_trans (be_step Σ Γ)).
  Local Notation RF pb n := (eq_term_upto_univ_eta_napp Σ.1 (compare_universe Σ) (compare_sort Σ) pb n).

  (** Reduction of a spine whose head is a local assumption is argumentwise. *)
  Lemma invert_red_mkApps_tRel_cb {Γ n d args c} :
    nth_error Γ n = Some d -> decl_body d = None ->
    Σ ;;; Γ ⊢ mkApps (tRel n) args ⇝ c ->
    ∑ args', (c = mkApps (tRel n) args') × All2 (closed_red Σ Γ) args args'.
  Proof.
    move=> hnth hb [clΓ].
    rewrite on_free_vars_mkApps => /andP [_ hargs] r.
    destruct (red_mkApps_tRel_cb (wfΣ := wfΣ) (Γ := exist Γ clΓ) hargs hnth hb r) as [args' [-> hr]].
    exists args'; split; [reflexivity|].
    solve_all; split; eauto with fvs.
  Qed.

  (** A chain from a spine whose head is a local assumption keeps the head and the
      number of arguments. *)
  Lemma chain_mkApps_Rel Γ n d l v :
    nth_error Γ n = Some d -> decl_body d = None ->
    is_closed_context Γ -> is_open_term Γ (mkApps (tRel n) l) ->
    chain Γ (mkApps (tRel n) l) v ->
    ∑ l', (v = mkApps (tRel n) l') × All2 (fun a a' => BE Γ a a') l l'.
  Proof.
    intros hnth hb hΓ hl h. apply clos_rt_rt1n_iff in h.
    remember (mkApps (tRel n) l) as x eqn:Ex.
    induction h as [x|x y v s _ IH] in l, hl, Ex |- *; subst x.
    - exists l. split; [reflexivity|apply All2_BE_refl].
    - destruct s as [[y0 [hr ->]]|he].
      + have hcr : Σ ;;; Γ ⊢ mkApps (tRel n) l ⇝ y0 := closed_red_of hΓ hl (red1_red _ _ _ _ hr).
        have hy0 := closed_red_open_right_cb (wfΣ := wfΣ) hcr.
        destruct (invert_red_mkApps_tRel_cb hnth hb hcr) as (l0 & -> & hl0).
        have e0 : canon (mkApps (tRel n) l0) = mkApps (tRel n) (map canon l0) by now rewrite canon_mkApps.
        destruct (IH (map canon l0) e0 (canon_is_open_term Γ _ hy0)) as (l' & -> & hl').
        exists l'. split; [reflexivity|]. exact (All2_BE_red_compose Γ l l0 l' hl0 hl').
      + destruct (eta1_mkApps_rigid_inv (tRel n) l y (eta_normal_Rel n) he) as (l0 & -> & hl0).
        destruct (IH l0 eq_refl (eta1_on_free_vars _ _ he _ hl)) as (l' & -> & hl').
        exists l'. split; [reflexivity|]. exact (All2_BE_eta_compose Γ l l0 l' hl0 hl').
  Qed.

  (** The comparison U1' keeps a variable-headed spine, at every [pb] and [napp], and
      compares the arguments at [Conv]. *)
  Lemma finst_mkApps_Rel_l pb k n l v : RF pb k (mkApps (tRel n) l) v ->
    ∑ l', (v = mkApps (tRel n) l') × All2 (RF Conv 0) l l'.
  Proof.
    revert k v. induction l as [|a l IH] using rev_ind; intros k v e.
    - cbn in e. depelim e. exists []. split; [reflexivity|constructor].
    - rewrite mkApps_app in e. cbn in e.
      destruct (finst_tApp_l _ _ _ _ _ e) as (f' & a' & [-> ef ea]).
      destruct (IH _ _ ef) as (l' & -> & hl).
      exists (l' ++ [a']). split; [now rewrite mkApps_app|].
      apply All2_app; [exact hl|constructor; [exact ea|constructor]].
  Qed.

End MkAppsRel.

(** **The η twin of base [ws_cumul_pb_mkApps_tRel].** *)
Lemma ws_cumul_pbE_mkApps_tRel {cf : checker_flags} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ}
  {Γ n d u u'} :
  nth_error Γ n = Some d -> decl_body d = None ->
  Σ ;;; Γ ⊢E mkApps (tRel n) u ≤ mkApps (tRel n) u' ->
  ws_cumul_pbE_terms Σ Γ u u'.
Proof.
  intros hnth hb [hΓ hl hr (v & v' & hv & hv' & e)].
  rewrite canon_mkApps in hv. rewrite canon_mkApps in hv'. cbn [canon] in hv, hv'.
  destruct (chain_mkApps_Rel (wfΣ := wfΣ) Γ n d (map canon u) v hnth hb hΓ
              (open_mkApps_canon Γ _ u eq_refl hl) hv) as (l1 & -> & hl1).
  destruct (chain_mkApps_Rel (wfΣ := wfΣ) Γ n d (map canon u') v' hnth hb hΓ
              (open_mkApps_canon Γ _ u' eq_refl hr) hv') as (l1' & -> & hl1').
  destruct (finst_mkApps_Rel_l _ _ _ _ _ e) as (l2 & E & hl2).
  destruct (mkApps_head_inj (tRel n) (tRel n) _ _ eq_refl eq_refl E) as [_ <-].
  exact (All2_WS_zip Γ u u' l1 l1' hΓ (forallb_open_mkApps Γ _ _ hl) (forallb_open_mkApps Γ _ _ hr)
           (All2_BE_from_canon Γ u l1 hl1) (All2_BE_from_canon Γ u' l1' hl1') hl2).
Qed.

(** ** A satisfying instance: an η step in an argument *)

Section Instance.

#[local] Existing Instance default_checker_flags.

Definition tr_na : aname := mkBindAnn nAnon Relevant.
Definition tr_P : term := tSort sProp.
(** [Prop → Prop], the type of [g]. *)
Definition tr_F : term := tProd tr_na tr_P tr_P.
(** [(Prop → Prop) → Prop], the type of [f]. *)
Definition tr_G : term := tProd tr_na tr_F tr_P.
Definition tr_Σ : global_env_ext := (empty_global_env, Monomorphic_ctx).
(** [g : Prop → Prop, f : (Prop → Prop) → Prop]: [f] is [tRel 0], [g] is [tRel 1]. *)
Definition tr_Γ : context := [vass tr_na tr_G; vass tr_na tr_F].
(** [λx:Prop. g x], one η step above [g]. *)
Definition tr_eta : term := eta_redex tr_na tr_P (tRel 1).

Lemma tr_wf : wf tr_Σ.
Proof. exact (@wf_empty_global_env default_checker_flags). Qed.

Definition tr_cb : ClosedBodies tr_Σ := @wf_ClosedBodies _ tr_Σ tr_wf.

(** [f (λx:Prop. g x) ≤ f g]: one η step inside the argument. *)
Lemma tr_premise :
  tr_Σ ;;; tr_Γ ⊢E mkApps (tRel 0) [tr_eta] ≤ mkApps (tRel 0) [tRel 1].
Proof.
  apply (eta1_ws_cumul_pbE (Σ := tr_Σ)); [reflexivity|reflexivity|].
  cbn [mkApps]. apply app_eta_r. exact (eta_red tr_na (tRel 1) tr_P).
Qed.

(** The lemma applied: [λx:Prop. g x] and [g] are convertible. *)
Lemma ws_cumul_pbE_mkApps_tRel_inst : ws_cumul_pbE_terms tr_Σ tr_Γ [tr_eta] [tRel 1].
Proof.
  exact (ws_cumul_pbE_mkApps_tRel (wfΣ := tr_cb) (Γ := tr_Γ) (n := 0) (d := vass tr_na tr_G)
           eq_refl eq_refl tr_premise).
Qed.

(** Both spines are typed. *)
Lemma tr_P_typed (Γ : context) : wf_localE tr_Σ Γ -> tr_Σ ;;; Γ |-E tr_P : tSort (Sort.super sProp).
Proof. intros h. apply typeE_Sort; [exact h|cbn; trivial]. Qed.

Lemma tr_vass_s (Γ : context) A s :
  tr_Σ ;;; Γ |-E A : tSort s -> relevance_of_sort s = Relevant ->
  lift_typing typingE tr_Σ Γ (j_vass_s tr_na A s).
Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [reflexivity|exact r]. Qed.

Lemma tr_vass (Γ : context) A s :
  tr_Σ ;;; Γ |-E A : tSort s -> relevance_of_sort s = Relevant ->
  lift_typing typingE tr_Σ Γ (j_vass tr_na A).
Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [exact I|exact r]. Qed.

Lemma tr_wf_P (Γ : context) : wf_localE tr_Σ Γ -> wf_localE tr_Σ (Γ ,, vass tr_na tr_P).
Proof. intros h. apply localenv_cons_abs; [exact h|exact (tr_vass Γ _ _ (tr_P_typed Γ h) eq_refl)]. Qed.

Lemma tr_F_typed (Γ : context) : wf_localE tr_Σ Γ ->
  tr_Σ ;;; Γ |-E tr_F : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)).
Proof.
  intros h. apply typeE_Prod.
  - exact (tr_vass_s Γ _ _ (tr_P_typed Γ h) eq_refl).
  - exact (tr_P_typed _ (tr_wf_P Γ h)).
Qed.

Lemma tr_wf_F (Γ : context) : wf_localE tr_Σ Γ -> wf_localE tr_Σ (Γ ,, vass tr_na tr_F).
Proof. intros h. apply localenv_cons_abs; [exact h|exact (tr_vass Γ _ _ (tr_F_typed Γ h) eq_refl)]. Qed.

Lemma tr_G_typed (Γ : context) : wf_localE tr_Σ Γ ->
  tr_Σ ;;; Γ |-E tr_G : tSort (Sort.sort_of_product
                                 (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp))
                                 (Sort.super sProp)).
Proof.
  intros h. apply typeE_Prod.
  - exact (tr_vass_s Γ _ _ (tr_F_typed Γ h) eq_refl).
  - exact (tr_P_typed _ (tr_wf_F Γ h)).
Qed.

Lemma tr_wf_Γ : wf_localE tr_Σ tr_Γ.
Proof.
  have h1 := tr_wf_F [] localenv_nil.
  apply localenv_cons_abs; [exact h1|exact (tr_vass _ _ _ (tr_G_typed _ h1) eq_refl)].
Qed.

Lemma tr_eta_typed : tr_Σ ;;; tr_Γ |-E tr_eta : tr_F.
Proof.
  have hx := tr_wf_P tr_Γ tr_wf_Γ.
  unfold tr_eta, tr_F. apply typeE_Lambda; [exact (tr_vass _ _ _ (tr_P_typed _ tr_wf_Γ) eq_refl)|].
  apply (typeE_App _ _ (tRel 2) tr_na tr_P tr_P
           (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) (tRel 0)).
  - exact (tr_F_typed _ hx).
  - exact (typeE_Rel _ _ 2 (vass tr_na tr_F) hx eq_refl).
  - exact (typeE_Rel _ _ 0 (vass tr_na tr_P) hx eq_refl).
Qed.

Lemma tr_spine_typed (a : term) : tr_Σ ;;; tr_Γ |-E a : tr_F ->
  tr_Σ ;;; tr_Γ |-E mkApps (tRel 0) [a] : tr_P.
Proof.
  intros ha. cbn [mkApps].
  apply (typeE_App _ _ (tRel 0) tr_na tr_F tr_P
           (Sort.sort_of_product (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp))
              (Sort.super sProp)) a).
  - exact (tr_G_typed _ tr_wf_Γ).
  - exact (typeE_Rel _ _ 0 (vass tr_na tr_G) tr_wf_Γ eq_refl).
  - exact ha.
Qed.

(** The environment is [wf] and [wfE], the context is well formed, and both spines
    have type [Prop]. *)
Lemma tr_spines_typed :
  [× wf tr_Σ, wfE tr_Σ, wf_localE tr_Σ tr_Γ,
     tr_Σ ;;; tr_Γ |-E mkApps (tRel 0) [tr_eta] : tr_P &
     tr_Σ ;;; tr_Γ |-E mkApps (tRel 0) [tRel 1] : tr_P].
Proof.
  split.
  - exact tr_wf.
  - exact (wf_incl_E tr_wf).
  - exact tr_wf_Γ.
  - exact (tr_spine_typed _ tr_eta_typed).
  - apply tr_spine_typed. exact (typeE_Rel _ _ 1 (vass tr_na tr_F) tr_wf_Γ eq_refl).
Qed.

End Instance.
