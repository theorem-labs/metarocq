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
  [ws_cumul_pbE_sym] needs no premise, so [ws_cumul_pbE_terms_sym] does not use its
  [ClosedBodies] argument.

  Compiled forms against the base twins ([About]). Each instance takes [ClosedBodies Σ]
  where its base twin takes [wf Σ]; in addition:
  - [conv_context_symE]: no other difference. Both have [Σ] implicit
    ([Arguments conv_context_symE {cf Σ cbΣ} x y _], base [{cf Σ wfΣ} x y _]).
  - [ws_cumul_pbE_terms_sym]: base [ws_cumul_pb_terms_sym] has [Σ] and [Γ] EXPLICIT
    ([Arguments ws_cumul_pb_terms_sym {cf} Σ {wfΣ} Γ x y _]); here both are implicit
    ([{cf Σ cbΣ Γ} x y _]). Base's head is [All2 (ws_cumul_pb Conv Σ Γ)] (its
    [ws_cumul_pb_terms] is a notation); here the head is the definition [ws_cumul_pbE_terms].
  - [ws_cumul_pbE_terms_trans]: base [ws_cumul_pb_terms_trans] has [Γ] EXPLICIT
    ([Arguments ws_cumul_pb_terms_trans {cf Σ wfΣ} Γ x y z _ _]); here it is implicit
    ([{cf Σ cbΣ Γ} x y z _ _]). Both heads are [All2].
  Resolution by [symmetry] and [transitivity] does not see the difference in implicit
  status. A proof that names a base term-list instance with explicit [Σ] or [Γ] must drop
  them for the twin; no base proof names [ws_cumul_pb_terms_sym] or
  [ws_cumul_pb_terms_trans].

  Base's [ws_cumul_pb_terms Σ Γ] is a notation for [All2 (ws_cumul_pb Conv Σ Γ)], and its
  transitivity instance is stated on [All2]. [ws_cumul_pbE_terms] is a [Definition] of
  [All2 (ws_cumul_pbE Conv Σ Γ)]; typeclass resolution unfolds it, so [symmetry] and
  [transitivity] find these instances on a goal written with [ws_cumul_pbE_terms] and on
  one written with [All2]. [PCUICWsCumulEtaInstancesGlobalInstances] proves one use of
  each instance on each form.

  Importing this file changes what [symmetry] resolves to on term lists. Without it,
  [symmetry] on a term list (either form) already succeeds with no premise, through
  [All2_symP] ([PCUICEquality]) and [ws_cumul_pbE_sym]. With it imported, and a
  [ClosedBodies Σ] instance in scope, [symmetry] resolves to [ws_cumul_pbE_terms_sym],
  and the proof term contains that instance. The instance can be a section variable
  [{cb : ClosedBodies Σ}], or [wfE_ClosedBodies] ([PCUICClosedTypEta]) applied to a section
  variable [{wfΣ : wfE Σ}]. So a lemma whose only use of that variable is such a [symmetry]
  keeps the variable in its compiled statement once this file is imported, where without
  the import Rocq drops it. With no such instance in scope, [symmetry] still takes the
  premise-free route. [symmetry] on [ws_cumul_ctx_pbE Conv] and [transitivity] on term
  lists find no instance without this file, so their uses need the import and its premise
  in any case. Base behaves the same way: [ws_cumul_pb_sym] needs no premise, and once
  [PCUICConversion] is imported, [symmetry] on [ws_cumul_pb_terms] resolves to
  [ws_cumul_pb_terms_sym] and keeps a [{wfΣ : wf Σ}] section variable.

  Rule for a file that imports this one: list its lemmas whose proofs call [symmetry] or
  [transitivity] on [ws_cumul_ctx_pbE Conv] or on term lists ([ws_cumul_pbE_terms], or
  [All2 (ws_cumul_pbE Conv Σ Γ)]), and compare each one's compiled binder list ([About])
  with and without the import. The only importer is
  [PCUICWsCumulEtaInstancesGlobalInstances]; its lemmas are stated on the concrete
  environment [si_Σ], so they have no binder to gain.

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
