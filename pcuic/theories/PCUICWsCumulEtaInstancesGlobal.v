(* Distributed under the terms of the MIT license. *)

(** * Typeclass instances for the η context and term-list relations

  Base proofs call [symmetry] and [transitivity] on the context relation and on lists of
  convertible terms; base resolves them with [conv_context_sym]
  ([PCUICContextConversion]), [ws_cumul_pb_terms_sym] and [ws_cumul_pb_terms_trans]
  ([PCUICConversion]). This file declares their twins over the η relations, as global
  instances:
  - [conv_context_symE] : [Symmetric (ws_cumul_ctx_pbE Conv Σ)], by [ws_cumul_ctx_pbE_sym];
  - [ws_cumul_pbE_terms_sym] : [Symmetric (ws_cumul_pbE_terms Σ Γ)], by [ws_cumul_pbE_sym]
    at each position;
  - [ws_cumul_pbE_terms_trans] : [Transitive (All2 (ws_cumul_pbE Conv Σ Γ))], by
    [ws_cumul_pbE_trans] at each position.
  Each takes [ClosedBodies Σ] where its base twin takes [wf Σ]. [ws_cumul_pbE_sym] needs
  no premise, so [ws_cumul_pbE_terms_sym] does not use its [ClosedBodies] argument.

  Base's [ws_cumul_pb_terms Σ Γ] is a notation for [All2 (ws_cumul_pb Conv Σ Γ)], and its
  transitivity instance is stated on [All2]. [ws_cumul_pbE_terms] is a [Definition] of
  [All2 (ws_cumul_pbE Conv Σ Γ)]; typeclass resolution unfolds it, so [symmetry] and
  [transitivity] find these instances on a goal written with [ws_cumul_pbE_terms] and on
  one written with [All2]. [PCUICWsCumulEtaInstancesGlobalInstances] proves one use of
  each instance on each form.

  A file that needs the instances imports this file; [PCUICContextConversionEta] and
  [PCUICConversionEtaCongr] do not declare them, so importing those files does not put
  them in scope. *)

From Stdlib Require Import CRelationClasses.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICClosedBodies PCUICWellScopedCumulativityEta
     PCUICConversionEtaCongr PCUICContextConversionEta.

(** Base [conv_context_sym] ([PCUICContextConversion]). *)
#[global] Instance conv_context_symE {cf : checker_flags} {Σ : global_env_ext} {cbΣ : ClosedBodies Σ} :
  CRelationClasses.Symmetric (ws_cumul_ctx_pbE Conv Σ).
Proof. intros Γ Γ' h. exact (ws_cumul_ctx_pbE_sym (wfΣ := cbΣ) h). Qed.

(** Base [ws_cumul_pb_terms_sym] ([PCUICConversion]). *)
#[global] Instance ws_cumul_pbE_terms_sym {cf : checker_flags} {Σ : global_env_ext}
  {cbΣ : ClosedBodies Σ} {Γ : context} :
  CRelationClasses.Symmetric (ws_cumul_pbE_terms Σ Γ).
Proof. exact (All2_symmetry (ws_cumul_pbE Conv Σ Γ) ws_cumul_pbE_sym). Qed.

(** Base [ws_cumul_pb_terms_trans] ([PCUICConversion]), on the same head [All2]. *)
#[global] Instance ws_cumul_pbE_terms_trans {cf : checker_flags} {Σ : global_env_ext}
  {cbΣ : ClosedBodies Σ} {Γ : context} :
  CRelationClasses.Transitive (All2 (ws_cumul_pbE Conv Σ Γ)).
Proof. exact (All2_transitivity (ws_cumul_pbE Conv Σ Γ) (ws_cumul_pbE_trans (wfΣ := cbΣ))). Qed.
