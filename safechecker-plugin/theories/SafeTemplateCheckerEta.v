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

From MetaRocq.TemplatePCUIC Require Import TemplateToPCUIC.

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

Definition trans_program (p : Ast.Env.program) : program :=
  let Σ' := trans_global_env p.1 in
  (Σ', trans Σ' p.2).

Definition EnvCheck_wf_env_ext {cf:checker_flags} {guard : abstract_guard_impl} := EnvCheck wf_env_ext.

Local Instance Monad_EnvCheck_wf_env_ext {cf:checker_flags} {guard : abstract_guard_impl} : Monad EnvCheck_wf_env_ext := _.

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
  pp <- typecheck_program (cf := cf) (nor:=nor) optimized_abstract_env_impl (trans_program p) φ ;;
  ret (pp.π1 ; (exist (proj1_sig pp.π2) _)).
Next Obligation.
  sq. destruct H; split; eauto. destruct p0; split; eauto. eapply infering_typing; tea. eapply w. constructor.
Qed.

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
  match infer_template_program (cf:=cf) p φ return string + string with
  | CorrectDecl t =>
    let Σ' := trans_global_env p.1 in
    inl ("Environment is well-formed and " ^ string_of_term (trans Σ' p.2) ^
         " has type: " ^ string_of_term t.π1)
  | EnvError Σ (AlreadyDeclared id) =>
    inr ("Already declared: " ^ id)
  | EnvError Σ (IllFormedDecl id e) =>
    inr ("Type error: " ^ string_of_type_error Σ e ^ ", while checking " ^ id)
  end.
