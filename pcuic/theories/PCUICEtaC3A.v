(* Distributed under the terms of the MIT license. *)
(* BET-315 eta lane, C3 prover A (branch frac/eta-c3-a).
   C3 (plan.md rev 11 §3): Hindley strong commutation of red1 over eta1 modulo upto_domain.
   Proved against the SHARED definitions in PCUICEtaDefs (eta1/eta1_ind_all/eta/upto_domain);
   this file adds NO new relation and does NOT redefine them. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Primitive.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICInduction PCUICPrimitive
     PCUICCases PCUICClosed PCUICTactics PCUICEquality PCUICReduction
     PCUICEtaDefs.

From Stdlib Require Import ssreflect ssrbool CRelationClasses.
From Equations.Prop Require Import DepElim.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
Set Equations Transparent.
Set Default Goal Selector "!".

Local Open Scope type_scope.
Import ListNotations.

Derive Signature for eta1.
Derive Signature for upto_domain.

(** [upto_domain] is reflexive (endpoints of the C3 conclusion meet up to domain). *)
#[global] Instance upto_domain_refl : Reflexive upto_domain.
Proof.
  intro t.
  induction t using term_forall_list_ind; try solve [constructor; auto].
  - constructor. eapply All_All2; eauto.
  - destruct X as (IHpars & _ & IHret).
    constructor; auto; try reflexivity.
    + eapply All_All2; eauto.
    + eapply All_All2; [eassumption|]. intros x [_ Hbody]. split; [reflexivity|exact Hbody].
  - constructor. eapply All_All2; eauto. intros x [? ?]; repeat split; auto.
  - constructor. eapply All_All2; eauto. intros x [? ?]; repeat split; auto.
  - constructor. destruct p as [? m]; destruct m; cbn in X |- *; try solve [constructor; auto].
    destruct X as (IHty & IHdef & IHval).
    constructor; cbn; auto. eapply All_All2; eauto.
Qed.

(** ** The C3 statement (plan §3, row C3), with the naming of the plan:
    [red1 Σ Γ t v] is the β/ι/δ step and [eta1 t u] the η-contraction. *)
Definition C3_concl {cf : checker_flags} (Σ : global_env) (Γ : context) (v u : term) :=
  ∑ w w', clos_refl (red1 Σ Γ) u w × clos_refl_trans eta1 v w' × upto_domain w w'.

(** ** Inversion: an η-step on a spine is either at the head or in one argument. *)
Lemma eta1_mkApps_inv M l N :
  eta1 (mkApps M l) N ->
  (∑ M', eta1 M M' × N = mkApps M' l) + (∑ l', OnOne2 eta1 l l' × N = mkApps M l').
Proof.
  induction l in M, N |- *; cbn.
  - intro H; left; now exists N.
  - intro H; apply IHl in H as [[M' [HM ->]]|[l' [Hl ->]]].
    + depelim HM.
      * left. exists N1. split; [assumption|reflexivity].
      * right. exists (N2 :: l). split; [constructor; assumption|reflexivity].
    + right. exists (a :: l'). split; [constructor; assumption|reflexivity].
Qed.

(** Helper: [eta1] propagates through a spine head. *)
Lemma eta1_mkApps_head f g l :
  eta1 f g -> eta1 (mkApps f l) (mkApps g l).
Proof.
  induction l in f, g |- *; cbn; [exact (fun h => h)|].
  intro h. apply IHl. now apply app_eta_l.
Qed.

(** Helper: a single [OnOne2 eta1] on a spine is one [eta1] step on [mkApps f _]. *)
Lemma eta1_mkApps_spine f l l' :
  OnOne2 eta1 l l' -> eta1 (mkApps f l) (mkApps f l').
Proof.
  induction 1 in f |- *; cbn.
  - apply eta1_mkApps_head. now apply app_eta_r.
  - now apply IHX.
Qed.

(** *** Unlocking case [red_proj] (lane-lead routing: no collision — the constructor
    head carries no η, so η lands in one projected/other argument). *)
Lemma c3_red_proj {cf : checker_flags} (Σ : global_env) Γ pr ui args arg u :
  nth_error args (pr.(proj_npars) + pr.(proj_arg)) = Some arg ->
  eta1 (tProj pr (mkApps (tConstruct pr.(proj_ind) 0 ui) args)) u ->
  ∑ w w', clos_refl (red1 Σ Γ) u w × clos_refl_trans eta1 arg w' × upto_domain w w'.
Proof.
  intros hnth He.
  depelim He.
  apply eta1_mkApps_inv in He as [[M' [HM ->]]|[args' [Hargs ->]]].
  - depelim HM.
  - destruct (OnOne2_nth_error _ _ _ _ _ Hargs hnth) as [arg' [hnth' [<-|He']]].
    + exists arg, arg. repeat split.
      * apply r_step. now eapply red_proj.
      * apply rt_refl.
      * reflexivity.
    + exists arg', arg'. repeat split.
      * apply r_step. now eapply red_proj.
      * apply rt_step. exact He'.
      * reflexivity.
Qed.
