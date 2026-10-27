(* Distributed under the terms of the MIT license. *)

(** * C3 — Hindley strong commutation of β-reduction with one η step, mod domains

  (BET-315 eta lane, plan §3 row C3; prover C3Prover1.)

  Target statement (plan line 546):
    red1 Σ Γ t v -> eta1 t u ->
      ∑ w w', clos_refl (red1 Σ Γ) u w × clos_refl_trans eta1 v w' × upto_domain w w'.

  Route: a dedicated [red1_ind_all] induction with this stronger conclusion
  (C2's statement is too weak). The FOUR UNLOCKING CASES come first —
  [red_proj], [red_fix], [red_cofix_case], [red_cofix_proj]. Per the lane lead's
  structural fact (falsifier-verified): eta_red is the only redex-creating
  constructor, and its exposed body [tApp (lift0 1 s) (tRel 0)] has a tApp head,
  on which only red_beta/red_fix fire; so an η-unlocked redex sits strictly below
  a proj_red/case_red node. Hence [red_proj]/[red_cofix_case]/[red_cofix_proj]
  are independent-position (congruence) cases, and [red_fix] is the ONE genuine
  one-step-each collision. We prove each unlocking case as a standalone lemma.

  Shared η relations [eta1]/[upto_domain] come from [PCUICEtaDefs] (NOT retyped). *)

From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils
     PCUICLiftSubst PCUICEquality PCUICReduction PCUICEtaDefs.
From MetaRocq.PCUIC Require Import PCUICInduction.

Import ListNotations.

Set Default Goal Selector "!".

Local Ltac invs H := inversion H; subst; clear H.

(** ** Inversion of one η step on an application spine (port of the 2020
    [eta1_mkApps_inv], 9.2 AST — mkApps/tApp unchanged). *)
Lemma eta1_mkApps_inv M l N :
  eta1 (mkApps M l) N ->
  (∑ M', eta1 M M' × N = mkApps M' l) + (∑ l', OnOne2 eta1 l l' × N = mkApps M l').
Proof.
  induction l in M, N |- *; cbn.
  - left; now exists N.
  - intro H; apply IHl in H as [[M' [e ?]]|[l' [o ?]]]; subst.
    + invs e.
      * left; now exists N1.
      * right; exists (N2 :: l). split; now constructor.
    + right; exists (a :: l'). split; now constructor.
Defined.

(** A rigid constructor head admits no η step. *)
Lemma eta1_tConstruct_inv ind k u N : eta1 (tConstruct ind k u) N -> False.
Proof. intro H; invs H. Qed.

Section C3Cases.
  (* Assumed U-row lemmas (plan U1-U8), discharged by L2/L1; listed in the report.
     Each is a standard closure/equivalence property of the shared relations. *)

  (* U1: [upto_domain] is reflexive (the 2020 [upto_domain_refl],
     origin/eta_postpo:PCUICEquality.v:1503-1511). *)
  Context (upto_domain_refl : forall t, upto_domain t t).

  Context {Σ : global_env} {Γ : context}.

  (** ** Unlocking case 1: [red_proj] (independent position)

    [t = tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)], [red_proj] fires
    to [arg]. An η step from [t] stays inside the spine (rigid constructor head),
    so [red_proj] re-fires on the η-reduct and the projected argument changes by
    at most one η step. Only U1 (refl) is used. *)
  Lemma C3_red_proj p args u arg :
    nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
    forall w,
      eta1 (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) w ->
      ∑ a b, clos_refl (red1 Σ Γ) w a
           × clos_refl_trans eta1 arg b
           × upto_domain a b.
  Proof.
    intros hnth w He.
    invs He.
    match goal with
    | H : eta1 (mkApps _ _) _ |- _ =>
        apply eta1_mkApps_inv in H as [[M0 [e ?]]|[args' [o ?]]]
    end; subst.
    - now apply eta1_tConstruct_inv in e.
    - eapply OnOne2_nth_error in o as [arg' [hnth' [heq | hstep]]]; tea.
      + subst arg'.
        exists arg, arg. split; [|split].
        * apply r_step. eapply red_proj; exact hnth'.
        * apply rt_refl.
        * apply upto_domain_refl.
      + exists arg', arg'. split; [|split].
        * apply r_step. eapply red_proj; exact hnth'.
        * apply rt_step. exact hstep.
        * apply upto_domain_refl.
  Qed.

End C3Cases.
