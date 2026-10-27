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
