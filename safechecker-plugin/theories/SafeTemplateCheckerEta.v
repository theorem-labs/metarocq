(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.Template Require Import AstUtils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICProgram
     PCUICTypingEta PCUICSNEta.
From MetaRocq.SafeChecker Require Import PCUICErrorsEta PCUICWfEnvEta PCUICWfEnvImplEta
  PCUICSafeReduceEta PCUICSafeConversionEta
  PCUICTypingEtaDefs PCUICTypeCheckerEta PCUICSafeCheckerEta PCUICTypingEtaHyps.

Import MonadNotation.

From MetaRocq.TemplatePCUIC Require Import TemplateToPCUIC.

(** * ETAK (EtaK7): the η copy of [SafeTemplateChecker] (plan row K7)

  BET-64 EtaCheckerLane, worker EtaK7, 2026-10-29; base [frac/eta] @ [0cb773a4]; text of base
  [safechecker-plugin/theories/SafeTemplateChecker.v] over the η checker [PCUICSafeCheckerEta].

  The η conversion enters here: [eta_conv_oracle] builds the [conv_oracle] the η checker takes from
  EtaConv's [PCUICSafeConversionEta.isconv_term] and [isconv_term_sound] (K6 statements; G7: a failure
  carries no proof). The remaining premises are Props, so the extracted entry point
  [infer_and_print_template_program] has base's signature:
  - the normalization premises over [wf_extE]/[NormalizationInE] (row O1, as base takes [NormalizationIn]);
  - EtaReduce's [reduce_factsE : ReduceTypedFacts welltypedE wf_extE] and the η typing facts
    [EtaF : EtaFacts] ([PCUICTypingEtaHyps]), the named hypotheses of rows T0/T1/T2a/T6/A/U;
  - EtaConv's own section premises, passed through unchanged. *)

Definition trans_program (p : Ast.Env.program) : program :=
  let Σ' := trans_global_env p.1 in
  (Σ', trans Σ' p.2).

Section EtaOracle.
  Context {cf : checker_flags} {nor : normalizing_flags}.
  Context {reduce_factsE : ReduceTypedFacts welltypedE wf_extE}.

  (** K6 at the checker: [None] when EtaConv's conversion succeeds; its soundness is
      [isconv_term_sound]. *)
  Program Definition eta_conv_oracle : conv_oracle :=
    {| oracle_conv X_type X normalization_in Γ pb t ht u hu :=
         match @isconv_term cf nor X_type X normalization_in Γ pb t ht u hu with
         | ConvSuccess => None
         | ConvError e => Some e
         end |}.
  Next Obligation.
    intros X_type X normalization_in Γ pb t ht u hu e Σ wfΣ.
    destruct isconv_term eqn:hc; [|discriminate].
    exact (isconv_term_sound _ _ Σ wfΣ Γ pb t ht u hu hc).
  Qed.
End EtaOracle.

#[global] Existing Instance eta_conv_oracle.

Definition EnvCheck_wf_env_ext {cf:checker_flags} {guard : abstract_guard_impl} := EnvCheck wf_env_ext.

Local Instance Monad_EnvCheck_wf_env_ext {cf:checker_flags} {guard : abstract_guard_impl} : Monad EnvCheck_wf_env_ext := _.

Program Definition infer_template_program {cf : checker_flags} {nor : normalizing_flags} {guard : abstract_guard_impl}
  {reduce_factsE : ReduceTypedFacts welltypedE wf_extE} {EtaF : EtaFacts}
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
  {reduce_factsE : ReduceTypedFacts welltypedE wf_extE} {EtaF : EtaFacts}
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
