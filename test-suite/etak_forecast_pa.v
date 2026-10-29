(** FORECAST-ONLY (fc/etak-forecast1): Print Assumptions of the four checker roots of the E (eta)
    checker, in the order of [lanes/GuardLane/PrintAssumptions.v] (base roots) so that the blocks
    compare one-to-one with integ-all7's recorded [verify/assumptions.txt]:
    1. the extracted entry point (after the forecast extraction commit, the E checker's);
    2. [SafeTemplateCheckerEta.infer_template_program];
    3. [PCUICSafeCheckerEta.typecheck_program];
    4. [PCUICWfEnvImplEta.canonical_abstract_env_prop].
    The named hypotheses of the E checker are section premises (arguments), not axioms: they do not
    appear here (Print Assumptions shows axioms). *)
From MetaRocq.SafeChecker Require Import PCUICWfEnvImplEta PCUICSafeCheckerEta.
From MetaRocq.SafeCheckerPlugin Require Import SafeTemplateCheckerEta Extraction.

Print Assumptions MetaRocq.SafeCheckerPlugin.Extraction.infer_and_print_template_program_with_guard.
Print Assumptions MetaRocq.SafeCheckerPlugin.SafeTemplateCheckerEta.infer_template_program.
Print Assumptions MetaRocq.SafeChecker.PCUICSafeCheckerEta.typecheck_program.
Print Assumptions MetaRocq.SafeChecker.PCUICWfEnvImplEta.canonical_abstract_env_prop.
