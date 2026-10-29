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
  [typing]. The last section adds the twins of base [PCUICTyping]'s [isWfArity],
  [isType_welltyped], [isTypeRel_welltyped], [has_sort_isType] and
  [has_sort_isTypeRel], over [welltypedE] ([PCUICTypingEta]). *)

Implicit Types (cf : checker_flags) (Σ : global_env_ext) (Γ : context).

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

(** ** Base [PCUICTyping] ([isWfArity], [isType_welltyped], [isTypeRel_welltyped],
    [has_sort_isType], [has_sort_isTypeRel]) over [typingE] and [welltypedE] *)

Definition isWfArityE {cf : checker_flags} Σ (Γ : context) T :=
  (isTypeE Σ Γ T × { ctx & { s & (destArity [] T = Some (ctx, s)) } }).

Definition isTypeE_welltypedE {cf Σ} {Γ T} : isTypeE Σ Γ T -> welltypedE Σ Γ T.
Proof. intros [_ [s []]]. now econstructor. Qed.

Definition isTypeRelE_welltypedE {cf Σ} {Γ T r} : isTypeRelE Σ Γ T r -> welltypedE Σ Γ T.
Proof. intros [_ [s []]]. now econstructor. Qed.

Definition has_sort_isTypeE {cf Σ} {Γ T} s : Σ ;;; Γ |-E T : tSort s -> isTypeE Σ Γ T.
Proof. repeat (eexists; tea). Defined.

Definition has_sort_isTypeRelE {cf Σ} {Γ T} s r :
  isSortRel s r -> Σ ;;; Γ |-E T : tSort s -> isTypeRelE Σ Γ T r.
Proof. repeat (eexists; tea). Defined.
