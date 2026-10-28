(* Distributed under the terms of the MIT license. *)
(** * BET-315 eta lane: the closed-constant-bodies premise ([lanes/eta/t0-plan.md] §1)

  Base confluence ([PCUICParallelReduction], [PCUICParallelReductionConfluence],
  [PCUICConfluence]) assumes [wf Σ], and uses it ONLY to know that the body of a
  declared constant is closed: [PCUICParallelReduction.v:1405] and [:2375] call
  [declared_constant_closed_body]; [PCUICParallelReductionConfluence.v:1986] calls
  [declared_decl_closed] for a constant's body; [:2660] calls
  [declared_constant_closed_body]. [ClosedBodies Σ] states exactly that fact, so
  that the confluence spine and the η chain built on it can be stated under a
  premise that both base [wf Σ] and the η environment [wfE Σ] provide.

  The instance from [wf] is here. The instance from [wfE] needs the closedness of
  [typingE]-typed terms and is in [Typing/PCUICClosedTypEta.v]. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICClosedTyp.

Class ClosedBodies (Σ : global_env) : Prop :=
  closed_bodies : forall cst decl body,
    declared_constant Σ cst decl -> decl.(cst_body) = Some body -> closed body.

#[global] Instance wf_ClosedBodies {cf : checker_flags} (Σ : global_env) {wfΣ : wf Σ} :
  ClosedBodies Σ.
Proof. intros cst decl body h e. exact (declared_constant_closed_body Σ cst decl body wfΣ h e). Qed.
