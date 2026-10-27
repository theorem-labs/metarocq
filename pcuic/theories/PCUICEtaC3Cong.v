(* Distributed under the terms of the MIT license. *)
(** * BET-315 eta lane, row C3 — the ordinary [red1] congruence cases (prover C)

  The eta1-route C3 main induction ([red1_ind_all]) splits into:
  - the four unlocking cases ([red_fix], [red_cofix_case], [red_cofix_proj],
    [red_proj]) — owned by C3Prover1/2/3;
  - the [tCase] reduction rows ([case_red_param/return/discr/brs], [red_iota]) —
    owned by C3Falsifier (PCUICEtaC3Falsify.v);
  - **the ordinary congruence rows and the base rewrite rows — this file.**

  Each case is a square of the *unscoped* C3 (matching C3Falsifier's [C3]/[joinable]),
  proved from the full-C3 induction hypothesis [IH : C3 Σ] (discharged on structurally
  smaller terms by the outer induction) plus the η congruence toolkit of
  [PCUICEtaC3C].  The pure congruence rows need neither [wf Σ] nor scoping nor
  [eta_subst]; the base rewrite rows ([red_beta], [red_zeta], [red_rel], [red_delta])
  are separated out because they overlap η nontrivially and are the remaining work. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations.Prop Require Import DepElim.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICInduction PCUICPrimitive
     PCUICCases PCUICReduction PCUICEtaDefs PCUICEtaC3C.

Import ListNotations.
Set Default Goal Selector "!".
Local Open Scope type_scope.

Notation eta_rt := (clos_refl_trans eta1).
Definition red_le Σ Γ := clos_refl (red1 Σ Γ).

Definition joinable {cf:checker_flags} (Σ : global_env) (Γ : context) (u v : term) : Type :=
  ∑ w w', red_le Σ Γ u w × eta_rt v w' × upto_domain w w'.

Definition C3 {cf:checker_flags} (Σ : global_env) : Type :=
  forall Γ t u v, red1 Σ Γ t v -> eta1 t u -> joinable Σ Γ u v.

(** [red_le] (reflexive closure of [red1]) congruences used to transport the join. *)

Lemma red_le_App_l Σ Γ a b c : red_le Σ Γ a b -> red_le Σ Γ (tApp a c) (tApp b c).
Proof. destruct 1; [apply r_step; now constructor|apply r_refl]. Qed.
Lemma red_le_App_r Σ Γ a b c : red_le Σ Γ b c -> red_le Σ Γ (tApp a b) (tApp a c).
Proof. destruct 1; [apply r_step; now constructor|apply r_refl]. Qed.
Lemma red_le_Prod_l Σ Γ na a b c : red_le Σ Γ a b -> red_le Σ Γ (tProd na a c) (tProd na b c).
Proof. destruct 1; [apply r_step; now constructor|apply r_refl]. Qed.
Lemma red_le_Proj Σ Γ p a b : red_le Σ Γ a b -> red_le Σ Γ (tProj p a) (tProj p b).
Proof. destruct 1; [apply r_step; now constructor|apply r_refl]. Qed.

Section Cong.
  Context {cf : checker_flags} (Σ : global_env).
  Context (IH : C3 Σ).

  (** A joined pair stays joined under any [red_le]/[eta_rt]-preserving frame given
      explicitly. *)

  (** *** app_red_l : red1 in the function, η anywhere in [tApp M1 M2]. *)
  Lemma c3_app_red_l Γ M1 N1 M2 u :
    red1 Σ Γ M1 N1 -> eta1 (tApp M1 M2) u -> joinable Σ Γ u (tApp N1 M2).
  Proof.
    intros hr he. depelim he.
    - (* app_eta_l : eta1 M1 N1' *)
      destruct (IH _ _ _ _ hr he) as (w & w' & hw & hw' & hd).
      exists (tApp w M2), (tApp w' M2). split; [|split].
      + now apply red_le_App_l.
      + now apply eta_App_l.
      + constructor; [exact hd|apply upto_domain_refl].
    - (* app_eta_r : eta1 M2 N2 *)
      exists (tApp N1 N2), (tApp N1 N2). split; [|split].
      + apply r_step. now constructor.
      + apply rt_step. now apply app_eta_r.
      + apply upto_domain_refl.
  Qed.

  (** *** app_red_r : red1 in the argument. *)
  Lemma c3_app_red_r Γ M1 M2 N2 u :
    red1 Σ Γ M2 N2 -> eta1 (tApp M1 M2) u -> joinable Σ Γ u (tApp M1 N2).
  Proof.
    intros hr he. depelim he.
    - (* app_eta_l : eta1 M1 N1 *)
      exists (tApp N1 N2), (tApp N1 N2). split; [|split].
      + apply r_step. now constructor.
      + apply rt_step. now apply app_eta_l.
      + apply upto_domain_refl.
    - (* app_eta_r : eta1 M2 N2' *)
      destruct (IH _ _ _ _ hr he) as (w & w' & hw & hw' & hd).
      exists (tApp M1 w), (tApp M1 w'). split; [|split].
      + now apply red_le_App_r.
      + now apply eta_App_r.
      + constructor; [apply upto_domain_refl|exact hd].
  Qed.

  (** *** prod_red_l : red1 in the domain. *)
  Lemma c3_prod_red_l Γ na M1 N1 M2 u :
    red1 Σ Γ M1 N1 -> eta1 (tProd na M1 M2) u -> joinable Σ Γ u (tProd na N1 M2).
  Proof.
    intros hr he. depelim he.
    - destruct (IH _ _ _ _ hr he) as (w & w' & hw & hw' & hd).
      exists (tProd na w M2), (tProd na w' M2). split; [|split].
      + now apply red_le_Prod_l.
      + now apply eta_Prod_l.
      + constructor; [exact hd|apply upto_domain_refl].
    - exists (tProd na N1 N2), (tProd na N1 N2). split; [|split].
      + apply r_step. now constructor.
      + apply rt_step. now apply prod_eta_r.
      + apply upto_domain_refl.
  Qed.

  (** *** proj_red : red1 in the projected term. *)
  Lemma c3_proj_red Γ p c c' u :
    red1 Σ Γ c c' -> eta1 (tProj p c) u -> joinable Σ Γ u (tProj p c').
  Proof.
    intros hr he. depelim he.
    destruct (IH _ _ _ _ hr he) as (w & w' & hw & hw' & hd).
    exists (tProj p w), (tProj p w'). split; [|split].
    - now apply red_le_Proj.
    - now apply eta_Proj.
    - now constructor.
  Qed.

  (** *** abs_red_l : red1 in the λ domain.  All three η-inversions are clean
      (the [eta_red] overlap contracts the whole redex; the domain reduction only
      changes the ignored domain, so one η-step on [v] rejoins). *)
  Lemma c3_abs_red_l Γ na M N1 N u :
    red1 Σ Γ M N1 -> eta1 (tLambda na M N) u -> joinable Σ Γ u (tLambda na N1 N).
  Proof.
    intros hr he. depelim he.
    - (* eta_red : N = tApp (lift0 1 u) (tRel 0), M is the ignored domain *)
      eexists; eexists. split; [apply r_refl|split].
      + apply rt_step. apply eta_red.
      + apply upto_domain_refl.
    - (* abs_eta_l : eta1 M M' *)
      destruct (IH _ _ _ _ hr he) as (w & w' & hw & hw' & hd).
      exists (tLambda na w N), (tLambda na w' N). split; [|split].
      + destruct hw; [apply r_step; now constructor|apply r_refl].
      + now apply eta_Lambda_l.
      + now constructor.
    - (* abs_eta_r : eta1 N N' (parallel to the domain reduction) *)
      eexists; eexists. split; [|split].
      + apply r_step. apply abs_red_l. exact hr.
      + apply rt_step. apply abs_eta_r. exact he.
      + apply upto_domain_refl.
  Qed.

  (** *** letin congruences (def / ty / body).  Parallel η / IH as for app. *)
  Lemma c3_letin_red_def Γ na b t b' r u :
    red1 Σ Γ b r -> eta1 (tLetIn na b t b') u -> joinable Σ Γ u (tLetIn na r t b').
  Proof.
    intros hr he. depelim he.
    - destruct (IH _ _ _ _ hr he) as (w & w' & hw & hw' & hd).
      exists (tLetIn na w t b'), (tLetIn na w' t b'). split; [|split].
      + destruct hw; [apply r_step; now constructor|apply r_refl].
      + now apply eta_LetIn_b.
      + constructor; [exact hd|apply upto_domain_refl|apply upto_domain_refl].
    - exists (tLetIn na r r0 b'), (tLetIn na r r0 b'). split; [|split].
      + apply r_step. now constructor.
      + apply rt_step. now apply letin_eta_ty.
      + apply upto_domain_refl.
    - exists (tLetIn na r t r0), (tLetIn na r t r0). split; [|split].
      + apply r_step. now constructor.
      + apply rt_step. now apply letin_eta_body.
      + apply upto_domain_refl.
  Qed.
  Lemma c3_letin_red_ty Γ na b t b' r u :
    red1 Σ Γ t r -> eta1 (tLetIn na b t b') u -> joinable Σ Γ u (tLetIn na b r b').
  Proof.
    intros hr he. depelim he.
    - exists (tLetIn na r0 r b'), (tLetIn na r0 r b'). split; [|split].
      + apply r_step. now constructor.
      + apply rt_step. now apply letin_eta_def.
      + apply upto_domain_refl.
    - destruct (IH _ _ _ _ hr he) as (w & w' & hw & hw' & hd).
      exists (tLetIn na b w b'), (tLetIn na b w' b'). split; [|split].
      + destruct hw; [apply r_step; now constructor|apply r_refl].
      + now apply eta_LetIn_t.
      + constructor; [apply upto_domain_refl|exact hd|apply upto_domain_refl].
    - exists (tLetIn na b r r0), (tLetIn na b r r0). split; [|split].
      + apply r_step. now constructor.
      + apply rt_step. now apply letin_eta_body.
      + apply upto_domain_refl.
  Qed.

End Cong.
