(* Distributed under the terms of the MIT license. *)
(** * The guard's closure lemmas over the eta relations

  [guard_cl] ([PCUICGuardClosure]) is the guard predicate of both [typing] and
  [typingE]. Two of the closure lemmas of [GuardCheckerCorrect]
  ([PCUICGuardCondition]) mention a base relation: [guard_context_cumulativity]
  (context cumulativity over [cumulSpec0]) and [guard_inst] (a substitution well
  typed in [typing]). This file proves their copies over the eta relations:

  - [gc_ctxE] and [guard_context_cumulativityE]: the guard is closed under context
    cumulativity over [cumulSpecE0]. They are the copies of the constructor [gc_ctx]
    and of the field [guard_context_cumulativity].
  - [guard_instE]: the copy of the field [guard_inst], with a substitution well typed
    in [typingE] ([well_substE]).

  The proofs use no conversion and no typing. [guard_cl] does not depend on its
  context ([guard_cl_context]): its renaming constructor [gc_ren] takes no premise,
  and renaming a block by the identity leaves it unchanged ([rename_mfix_id]). So
  [gc_ctxE] does not use its cumulativity premise, which is kept so that the
  statement is base's with the relation renamed. [guard_instE] is [gc_inst], whose
  premises do not include the typing of the substitution. The other five fields of
  [GuardCheckerCorrect] mention no conversion and no typing, and apply to [typingE]
  as they are. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICSigmaCalculus
     PCUICCumulativitySpec PCUICGuardClosure PCUICTyping PCUICGuardCondition
     PCUICCumulativitySpecEta PCUICInstDefEta.

From Stdlib Require Import ssreflect.

(** Renaming a block by the identity leaves it unchanged. *)
Lemma rename_mfix_id mfix : rename_mfix mfix id = mfix.
Proof.
  rewrite /rename_mfix. apply map_id_f => d.
  apply map_def_id_spec.
  - exact (rename_ren_id (dtype d)).
  - rewrite (rename_ext _ _ (shiftn_id #|mfix|) (dbody d)).
    exact (rename_ren_id (dbody d)).
Qed.

(** A block guarded in one context is guarded in every context, by [gc_ren] at the
    identity renaming. *)
Lemma guard_cl_context b Σ Γ Δ mfix :
  guard_cl b Σ Γ mfix -> guard_cl b Σ Δ mfix.
Proof.
  intros h. rewrite -(rename_mfix_id mfix).
  exact (gc_ren b Σ Γ Δ mfix id h).
Qed.

(** The copy of the constructor [gc_ctx] over [cumulSpecE0]. *)
Lemma gc_ctxE {cf : checker_flags} b (Σ : global_env_ext) (Γ Γ' : context)
  (mfix : mfixpoint term) :
  ∥ All2_fold (cumul_decls cumulSpecE0 Σ) Γ' Γ ∥ ->
  guard_cl b Σ Γ mfix -> guard_cl b Σ Γ' mfix.
Proof. intros _. apply guard_cl_context. Qed.

(** The copy of the field [guard_context_cumulativity] over [cumulSpecE0]. *)
Lemma guard_context_cumulativityE `{checker_flags} b Σ Γ Γ' mfix :
  All2_fold (cumul_decls cumulSpecE0 Σ) Γ' Γ ->
  guard b Σ Γ mfix ->
  guard b Σ Γ' mfix.
Proof. intros hcum. exact (gc_ctxE b Σ Γ Γ' mfix (sq hcum)). Qed.

(** The copy of the field [guard_inst] with a substitution well typed in [typingE]. *)
Lemma guard_instE `{checker_flags} b Σ Γ Δ mfix σ :
  well_substE Σ Δ σ Γ ->
  closedn_mfix #|Δ| mfix ->
  (forall x, x < #|Δ| -> wf_cases Σ.1 (σ x)) ->
  guard b Σ Δ mfix ->
  guard b Σ Γ (inst_mfix mfix σ).
Proof. intros _ hcl hwf hg. now eapply gc_inst. Qed.

Definition fix_guard_context_cumulativityE `{checker_flags} := guard_context_cumulativityE Fix.
Definition fix_guard_instE `{checker_flags} := guard_instE Fix.

Definition cofix_guard_context_cumulativityE `{checker_flags} := guard_context_cumulativityE CoFix.
Definition cofix_guard_instE `{checker_flags} := guard_instE CoFix.
