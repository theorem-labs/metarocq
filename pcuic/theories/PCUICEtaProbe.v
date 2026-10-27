From Stdlib Require Import CRelationClasses.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICTactics
     PCUICLiftSubst PCUICUnivSubst PCUICInduction PCUICReduction PCUICCases
     PCUICTyping PCUICOnFreeVars PCUICSigmaCalculus PCUICClosed.
From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.

Set Default Goal Selector "!".

Ltac dump s := idtac "=== goal" s;
  repeat match goal with H : ?T |- _ => idtac "  HYP>>>" H ":" T; revert H end.

Section P.
  Context {cf : checker_flags}.
  Context {Σ : global_env_ext}.

  Lemma probe_tRel0 Γ na A N : red1 Σ (Γ ,, vass na A) (tRel 0) N -> False.
  Proof.
    intros r. depelim r.
    all: dump "tRel0".
  Abort.

  Lemma probe_eta_body Γ na A s M' :
    red1 Σ (Γ ,, vass na A) (tApp (lift0 1 s) (tRel 0)) M' -> False.
  Proof.
    intros r. depelim r.
    all: dump "etabody".
  Abort.

End P.
