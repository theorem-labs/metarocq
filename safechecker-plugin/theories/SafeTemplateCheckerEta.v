(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.Template Require Import AstUtils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICProgram
     PCUICTypingEta PCUICSN.
From MetaRocq.SafeChecker Require Import PCUICErrorsEta PCUICWfEnvEta PCUICWfEnvImplEta
  PCUICSafeReduceEta
  PCUICTypingEtaDefs PCUICTypeCheckerEta PCUICSafeCheckerEta PCUICTypingEtaHyps.
(* ETAK ship: the proved instance of the η typing facts (opened by [sq] in [infer_translated_program]'s
   obligation); Required only. *)
From MetaRocq.SafeChecker Require PCUICTypingEtaDischarge.

Import MonadNotation.

From MetaRocq.TemplatePCUIC Require Import TemplateToPCUIC TemplateToPCUICShared.

(** * ETAK (EtaK7): the η copy of [SafeTemplateChecker] (plan row K7)

  BET-64 EtaCheckerLane, worker EtaK7, 2026-10-29; base [frac/eta] @ [0cb773a4]; text of base
  [safechecker-plugin/theories/SafeTemplateChecker.v] over the η checker [PCUICSafeCheckerEta].

  Premises of the entry points, beyond base's: none (ETAK ship). The η conversion is the closed
  [SafeTemplateCheckerEtaConv.eta_conv_oracle] (EtaConv's [isconv_term] / [isconv_term_sound], CONTRACTS.md
  CONV 11:35Z, from the proved instances; a change of that contract is a one-site fix there), and EtaReduce's
  [ReduceTypedFacts welltypedE wf_extE] and the η typing facts [EtaFacts] are proved instances
  ([PCUICTypingEtaDischarge]); [PCUICSafeCheckerEta.typecheck_program] takes all three as its section's
  instances, so these entries bind none of them. No normalization premise: the η checker's recursions
  terminate by fuel ([PCUICFuelEta], BET-64 FUEL; base takes [NormalizationIn]); an empty fuel is printed
  as a refusal for lack of fuel ([print_env_error]).

  Exported for the plugin's OCaml glue, same names and types as base ([SafeTemplateChecker]):
  [trans_program], [infer_template_program], [infer_and_print_template_program], so at the cutover (F0)
  the glue can point at this module and the extracted closure contains no base [SafeTemplateChecker]. *)

(** FORECAST-ONLY (fc/etak-forecast1, FO3): integ-all7's trans_memo sharing.  [trans_program] is
    integ-all7's [SafeTemplateChecker.trans_program] (the shared translation, then the memo's release)
    and [trans_program_unshared] its plain translation; [infer_translated_program] checks an already
    translated program, so [infer_and_print_template_program] computes the translation once, as in
    integ-all7.  [frac/eta] has no [TemplateToPCUICShared]; reconciled when F0 lands integ-all7's
    [SafeTemplateChecker.v] text on the E plugin, with [trans_program_unshared_eq] rechecked there.
    The call-by-need fast path's soundness is no premise of these entries: [PCUICTypeCheckerEta.convert]
    uses the proved instance [PCUICCallByNeedSoundEta.cbn_conv_soundE_proved]. *)

Definition trans_program_unshared (p : Ast.Env.program) : program :=
  let Σ' := trans_global_env p.1 in
  (Σ', trans Σ' p.2).

(** The checker translates with [trans_shared], which keeps the sharing of the
    quoted program at extraction (see [TemplateToPCUICShared]), then releases
    the memo's table.  In Rocq it is the plain translation:
    [trans_program_unshared_eq]. *)
Definition trans_program (p : Ast.Env.program) : program :=
  trans_memo_release
    (let Σ' := trans_global_env_shared p.1 in
     (Σ', trans_shared Σ' p.2)).

Lemma trans_program_unshared_eq p : trans_program p = trans_program_unshared p.
Proof. reflexivity. Qed.

Definition EnvCheck_wf_env_ext {cf:checker_flags} {guard : abstract_guard_impl} := EnvCheck wf_env_ext.

Local Instance Monad_EnvCheck_wf_env_ext {cf:checker_flags} {guard : abstract_guard_impl} : Monad EnvCheck_wf_env_ext := _.

#[local] Existing Instance PCUICTypingEtaDischarge.EtaFacts_discharged.

(** Checking an already translated program [p'].  [infer_template_program]
    is this check on [trans_program p]; [infer_and_print_template_program]
    calls it directly, so the translation is computed once and the Template
    program has no use after it. *)
Program Definition infer_translated_program {cf : checker_flags} {nor : normalizing_flags} {guard : abstract_guard_impl}
  (p' : program) φ
  : EnvCheck_wf_env_ext (∑ A, { X : wf_env_ext |
    ∥ (p'.1, φ) = X.(wf_env_ext_reference).(reference_impl_env_ext) × wf_extE (p'.1, φ) ×
      (p'.1, φ) ;;; [] |-E p'.2 : A ∥ }) :=
  pp <- typecheck_program (cf := cf) (nor:=nor) optimized_abstract_env_impl p' φ ;;
  ret (pp.π1 ; (exist (proj1_sig pp.π2) _)).
Next Obligation.
  sq. destruct H; split; eauto. destruct p; split; eauto. eapply infering_typing; tea. eapply w. constructor.
Qed.

Program Definition infer_template_program {cf : checker_flags} {nor : normalizing_flags} {guard : abstract_guard_impl}
  (p : Ast.Env.program) φ
  : EnvCheck_wf_env_ext (let p' := trans_program p in ∑ A, { X : wf_env_ext |
    ∥ (p'.1, φ) = X.(wf_env_ext_reference).(reference_impl_env_ext) × wf_extE (p'.1, φ) ×
      (p'.1, φ) ;;; [] |-E p'.2 : A ∥ }) :=
  infer_translated_program (cf := cf) (nor := nor) (trans_program p) φ.

(** The plugin's message for an environment error. An empty fuel ([PCUICFuelEta]) is printed as a
    refusal for lack of fuel, never as a type error. *)
Definition print_env_error (Σ : global_env_ext) (e : env_error) : string :=
  match e with
  | AlreadyDeclared id => "Already declared: " ^ id
  | IllFormedDecl id (NotEnoughFuel s) =>
    "Refused: the checker ran out of fuel in " ^ s ^
    " (a refusal for lack of fuel, not a type error), while checking " ^ id
  | IllFormedDecl id e => "Type error: " ^ string_of_type_error Σ e ^ ", while checking " ^ id
  end.

Program Definition infer_and_print_template_program {cf : checker_flags} {nor : normalizing_flags} {guard : abstract_guard_impl}
  (p : Ast.Env.program) φ
  : string + string :=
  let p' := trans_program p in
  match infer_translated_program (cf := cf) (nor := nor) p' φ return string + string with
  | CorrectDecl t =>
    (* Print the term of the program already translated and checked. *)
    inl ("Environment is well-formed and " ^ string_of_term p'.2 ^
         " has type: " ^ string_of_term t.π1)
  | EnvError Σ e => inr (print_env_error Σ e)
  end.
