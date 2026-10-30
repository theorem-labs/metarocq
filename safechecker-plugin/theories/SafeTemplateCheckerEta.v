(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.Template Require Import AstUtils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICProgram
     PCUICTypingEta PCUICSN PCUICSNEta.
From MetaRocq.SafeChecker Require Import PCUICErrorsEta PCUICWfEnvEta PCUICWfEnvImplEta
  PCUICSafeReduceEta
  PCUICTypingEtaDefs PCUICTypeCheckerEta PCUICSafeCheckerEta PCUICTypingEtaHyps.

Import MonadNotation.

From MetaRocq.TemplatePCUIC Require Import TemplateToPCUIC TemplateToPCUICShared.

(** * ETAK (EtaK7): the η copy of [SafeTemplateChecker] (plan row K7)

  BET-64 EtaCheckerLane, worker EtaK7, 2026-10-29; base [frac/eta] @ [0cb773a4]; text of base
  [safechecker-plugin/theories/SafeTemplateChecker.v] over the η checker [PCUICSafeCheckerEta].

  Premises of the entry points, beyond base's:
  - [CO : conv_oracle], the η conversion. It is instantiated with EtaConv's [isconv_term] /
    [isconv_term_sound] (CONTRACTS.md CONV 11:35Z) in the separate file [SafeTemplateCheckerEtaConv]
    ([eta_conv_oracle]), so a change of that contract is a one-site fix;
  - EtaReduce's [reduce_factsE : ReduceTypedFacts welltypedE wf_extE] and the η typing facts
    [EtaF : EtaFacts] ([PCUICTypingEtaHyps]); both are Props, erased by extraction;
  - the normalization premises, over [wf_extE]/[NormalizationInE] (base takes [NormalizationIn]).

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

(** Checking an already translated program [p'].  [infer_template_program]
    is this check on [trans_program p]; [infer_and_print_template_program]
    calls it directly, so the translation is computed once and the Template
    program has no use after it. *)
Program Definition infer_translated_program {cf : checker_flags} {nor : normalizing_flags} {guard : abstract_guard_impl}
  {CO : conv_oracle} {reduce_factsE : ReduceTypedFacts welltypedE wf_extE} {EtaF : EtaFacts}
  (p' : program) φ
  {normalization_in
    : forall (g : global_decl) (Hdecls' : nat) (X : X_env_type optimized_abstract_env_impl),
      (forall Σ0 : global_env,
          Σ0 ∼ X ->
          Σ0 =
            {|
              universes := p'.1;
              declarations := skipn Hdecls' (declarations p'.1);
              retroknowledge := retroknowledge p'.1
            |}) ->
      forall X' : X_env_ext_type optimized_abstract_env_impl,
        check_wf_env_ext_prop optimized_abstract_env_impl X X' (universes_decl_of_decl g) ->
        forall Σ0 : global_env_ext, wf_extE Σ0 -> Σ0 ∼_ext X' -> NormalizationInE Σ0}
  {normalization_in'
    : forall x : X_env_ext_type optimized_abstract_env_impl,
      (p'.1, φ) ∼_ext x ->
      forall Σ : global_env_ext, wf_extE Σ -> Σ ∼_ext x -> NormalizationInE Σ}
  : EnvCheck_wf_env_ext (∑ A, { X : wf_env_ext |
    ∥ (p'.1, φ) = X.(wf_env_ext_reference).(reference_impl_env_ext) × wf_extE (p'.1, φ) ×
      (p'.1, φ) ;;; [] |-E p'.2 : A ∥ }) :=
  pp <- typecheck_program (cf := cf) (nor:=nor) optimized_abstract_env_impl p' φ ;;
  ret (pp.π1 ; (exist (proj1_sig pp.π2) _)).
Next Obligation.
  sq. destruct H; split; eauto. destruct p; split; eauto. eapply infering_typing; tea. eapply w. constructor.
Qed.

Program Definition infer_template_program {cf : checker_flags} {nor : normalizing_flags} {guard : abstract_guard_impl}
  {CO : conv_oracle} {reduce_factsE : ReduceTypedFacts welltypedE wf_extE} {EtaF : EtaFacts}
  (p : Ast.Env.program) φ
  {normalization_in
    : forall (g : global_decl) (Hdecls' : nat) (X : X_env_type optimized_abstract_env_impl),
      (forall Σ0 : global_env,
          Σ0 ∼ X ->
          Σ0 =
            {|
              universes := (trans_program p).1;
              declarations := skipn Hdecls' (declarations (trans_program p).1);
              retroknowledge := retroknowledge (trans_program p).1
            |}) ->
      forall X' : X_env_ext_type optimized_abstract_env_impl,
        check_wf_env_ext_prop optimized_abstract_env_impl X X' (universes_decl_of_decl g) ->
        forall Σ0 : global_env_ext, wf_extE Σ0 -> Σ0 ∼_ext X' -> NormalizationInE Σ0}
  {normalization_in'
    : forall x : X_env_ext_type optimized_abstract_env_impl,
      ((trans_program p).1, φ) ∼_ext x ->
      forall Σ : global_env_ext, wf_extE Σ -> Σ ∼_ext x -> NormalizationInE Σ}
  : EnvCheck_wf_env_ext (let p' := trans_program p in ∑ A, { X : wf_env_ext |
    ∥ (p'.1, φ) = X.(wf_env_ext_reference).(reference_impl_env_ext) × wf_extE (p'.1, φ) ×
      (p'.1, φ) ;;; [] |-E p'.2 : A ∥ }) :=
  infer_translated_program (cf := cf) (nor := nor) (normalization_in := normalization_in)
    (normalization_in' := normalization_in') (trans_program p) φ.

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
  {CO : conv_oracle} {reduce_factsE : ReduceTypedFacts welltypedE wf_extE} {EtaF : EtaFacts}
  (p : Ast.Env.program) φ
  {normalization_in
    : forall (g : global_decl) (Hdecls' : nat) (X : X_env_type optimized_abstract_env_impl),
      (forall Σ0 : global_env,
          Σ0 ∼ X ->
          Σ0 =
            {|
              universes := (trans_program p).1;
              declarations := skipn Hdecls' (declarations (trans_program p).1);
              retroknowledge := retroknowledge (trans_program p).1
            |}) ->
      forall X' : X_env_ext_type optimized_abstract_env_impl,
        check_wf_env_ext_prop optimized_abstract_env_impl X X' (universes_decl_of_decl g) ->
        forall Σ0 : global_env_ext, wf_extE Σ0 -> Σ0 ∼_ext X' -> NormalizationInE Σ0}
  {normalization_in'
    : forall x : X_env_ext_type optimized_abstract_env_impl,
      ((trans_program p).1, φ) ∼_ext x ->
      forall Σ : global_env_ext, wf_extE Σ -> Σ ∼_ext x -> NormalizationInE Σ}  : string + string :=
  let p' := trans_program p in
  match infer_translated_program (cf := cf) (nor := nor) (normalization_in := normalization_in)
          (normalization_in' := normalization_in') p' φ return string + string with
  | CorrectDecl t =>
    (* Print the term of the program already translated and checked. *)
    inl ("Environment is well-formed and " ^ string_of_term p'.2 ^
         " has type: " ^ string_of_term t.π1)
  | EnvError Σ e => inr (print_env_error Σ e)
  end.
