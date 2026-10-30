(** FORECAST-ONLY (fc/etak-forecast1): Print Assumptions of the four checker roots of the E (eta)
    checker, in the order of [lanes/GuardLane/PrintAssumptions.v] (base roots) so that the blocks
    compare one-to-one with integ-all7's recorded [verify/assumptions.txt]:
    1. the extracted entry point (after the forecast extraction commit, the E checker's);
    2. [SafeTemplateCheckerEta.infer_template_program];
    3. [PCUICSafeCheckerEta.typecheck_program];
    4. [PCUICWfEnvImplEta.canonical_abstract_env_prop].
    Then, blocks 5-14, the ten roots of EtaK7's record [/mnt/frac/work/etak/EtaK7/out/pa-roots-35307b14.log]
    (K7 at 35307b14), in its order, so that they compare one-to-one with that record.
    Print Assumptions shows axioms only, never arguments. ETAK ship: blocks 1-3, [typecheck_program],
    [infer_and_print_template_program] and [eta_conv_oracle] take no class premise (proved instances);
    [PCUICTypeCheckerEta.infer] keeps the section parameter [CO : conv_oracle], which [typecheck_program]
    instantiates with the closed oracle, and the conversion's lemmas keep their section parameters, which
    [eta_conv_oracle] instantiates. [SafeTemplateCheckerEtaConv] is in [MetaRocq.SafeChecker] on the ship
    branch (moved from [MetaRocq.SafeCheckerPlugin], module name unchanged). *)
From MetaRocq.SafeChecker Require Import PCUICWfEnvImplEta PCUICSafeCheckerEta.
From MetaRocq.SafeChecker Require PCUICTypeCheckerEta PCUICSafeConversionEta.
From MetaRocq.SafeCheckerPlugin Require Import SafeTemplateCheckerEta Extraction.
From MetaRocq.SafeChecker Require SafeTemplateCheckerEtaConv.

Print Assumptions MetaRocq.SafeCheckerPlugin.Extraction.infer_and_print_template_program_with_guard.
Print Assumptions MetaRocq.SafeCheckerPlugin.SafeTemplateCheckerEta.infer_template_program.
Print Assumptions MetaRocq.SafeChecker.PCUICSafeCheckerEta.typecheck_program.
Print Assumptions MetaRocq.SafeChecker.PCUICWfEnvImplEta.canonical_abstract_env_prop.

(* The ten roots of pa-roots-35307b14.log, same order. *)
Print Assumptions MetaRocq.SafeChecker.PCUICTypeCheckerEta.infer.
Print Assumptions MetaRocq.SafeChecker.PCUICSafeCheckerEta.typecheck_program.
Print Assumptions MetaRocq.SafeCheckerPlugin.SafeTemplateCheckerEta.infer_and_print_template_program.
Print Assumptions MetaRocq.SafeChecker.SafeTemplateCheckerEtaConv.eta_conv_oracle.
Print Assumptions MetaRocq.SafeChecker.PCUICSafeConversionEta.isconv_term.
Print Assumptions MetaRocq.SafeChecker.PCUICSafeConversionEta.isconv_term_sound.
Print Assumptions MetaRocq.SafeChecker.PCUICSafeConversionEta.isconv.
Print Assumptions MetaRocq.SafeChecker.PCUICSafeConversionEta.isconv_sound.
Print Assumptions MetaRocq.SafeChecker.PCUICSafeConversionEta._isconv.
Print Assumptions MetaRocq.SafeChecker.PCUICSafeConversionEta.isconv_full.
