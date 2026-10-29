(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICTypingEta.

(** * Types, relative contexts and context instances over [typingE]

  The E twins of the typing notions that base defines in
  [common/theories/EnvironmentTyping.v] generically in the typing relation:
  [isTypeRel] (:2752), [isType] (:2755), the coercion from [isTypeRel] to
  [isType] (base: [isTypeRel_isType] / [lift_sorting_forget_rel]),
  [wf_local_rel] (:2783), and [ctx_inst] (:1011). Each is base's definition
  with [typing] replaced by [typingE]; [ctx_instE] is the instantiation of the
  generic [ctx_inst] at [typingE], as base [PCUICTyping] instantiates it at
  [typing]. *)

(** ** Types over [typingE] *)

Definition isTypeRelE `{checker_flags} (Σ : global_env_ext) (Γ : context) (t : term) (rel : relevance) :=
  on_type_rel (lift_typing typingE) Σ Γ t rel.

Definition isTypeE `{checker_flags} (Σ : global_env_ext) (Γ : context) (t : term) :=
  on_type (lift_typing typingE) Σ Γ t.

Definition isTypeRelE_isTypeE `{checker_flags} (Σ : global_env_ext) (Γ : context) (t : term) (r : relevance) :
  isTypeRelE Σ Γ t r -> isTypeE Σ Γ t.
Proof. apply lift_sorting_forget_rel. Defined.
Coercion isTypeRelE_isTypeE : isTypeRelE >-> isTypeE.

Definition wf_local_relE `{checker_flags} Σ := All_local_rel (lift_typing1 (typingE Σ)).

Notation ctx_instE Σ := (PCUICTyping.ctx_inst (typingE Σ)).
