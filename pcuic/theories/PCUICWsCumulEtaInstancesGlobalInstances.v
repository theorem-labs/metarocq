(* Distributed under the terms of the MIT license. *)

(** * Uses of the instances of [PCUICWsCumulEtaInstancesGlobal]

  Each lemma below is proved by a [symmetry] or [transitivity] call that resolves an
  instance of [PCUICWsCumulEtaInstancesGlobal], on two different things related by an
  η step, in [si_Σ] ([PCUICCumulativitySpecEtaClosureInstances]; its [ClosedBodies]
  instance [si_cb] is the premise of the three instances). The terms are those of
  [PCUICEtaFracInstances]: [fi_P := Prop], the η-redex [fi_eta := λx:Prop. Prop x] and
  the β-redex [fi_beta := (λx:Prop. x) Prop]; [ci_WT_eta] relates [[fi_eta]] to [[fi_P]]
  and [ci_WT] relates [[fi_beta]] to [[fi_P]] ([PCUICWsCumulEtaCtxInstances]).
  - [conv_context_symE_inst]: [symmetry] on the contexts [ci_Γd2 = [x := Prop : Prop]] and
    [ci_Γd1 = [x := fi_eta : Prop]], whose let-bodies are the η-pair ([gi_ctx_conv]).
  - [ws_cumul_pbE_terms_sym_inst], [ws_cumul_pbE_terms_sym_All2_inst]: [symmetry] on
    [[fi_P]] and [[fi_eta]], with the goal written with [ws_cumul_pbE_terms] and with
    [All2].
  - [ws_cumul_pbE_terms_trans_inst], [ws_cumul_pbE_terms_trans_All2_inst]:
    [transitivity [fi_P]] from [[fi_eta]] to [[fi_beta]] (an η step, then a β step taken
    backwards by [symmetry]), with the goal written with [ws_cumul_pbE_terms] and with
    [All2]. Without [ws_cumul_pbE_terms_trans], [transitivity] finds no instance on
    either form. *)

From Stdlib Require Import ssreflect ssrbool CRelationClasses.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICTyping PCUICClosedBodies
     PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICContextConversionEta
     PCUICCumulativitySpecEtaClosureInstances PCUICEtaFracInstances PCUICWsCumulEtaCtxInstances
     PCUICWsCumulEtaInstancesGlobal.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

(** The one-let contexts [ci_Γd1] and [ci_Γd2], whose let-bodies are the η-pair, related
    at [Conv]. *)
Lemma gi_ctx_conv : ws_cumul_ctx_pbE Conv si_Σ ci_Γd1 ci_Γd2.
Proof.
  constructor; [constructor|]. constructor; [reflexivity|exact (ci_WS_eta Conv)|].
  apply ws_cumul_pbE_refl; reflexivity.
Qed.

Lemma conv_context_symE_inst : ws_cumul_ctx_pbE Conv si_Σ ci_Γd2 ci_Γd1.
Proof. symmetry. exact gi_ctx_conv. Qed.

Lemma ws_cumul_pbE_terms_sym_inst : ws_cumul_pbE_terms si_Σ [] [fi_P] [fi_eta].
Proof. symmetry. exact ci_WT_eta. Qed.

Lemma ws_cumul_pbE_terms_sym_All2_inst : All2 (ws_cumul_pbE Conv si_Σ []) [fi_P] [fi_eta].
Proof. symmetry. exact ci_WT_eta. Qed.

Lemma ws_cumul_pbE_terms_trans_inst : ws_cumul_pbE_terms si_Σ [] [fi_eta] [fi_beta].
Proof. transitivity [fi_P]; [exact ci_WT_eta|symmetry; exact ci_WT]. Qed.

Lemma ws_cumul_pbE_terms_trans_All2_inst : All2 (ws_cumul_pbE Conv si_Σ []) [fi_eta] [fi_beta].
Proof. transitivity [fi_P]; [exact ci_WT_eta|symmetry; exact ci_WT]. Qed.
