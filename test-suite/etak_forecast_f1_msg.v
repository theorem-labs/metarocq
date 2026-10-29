(** FORECAST-ONLY (fc/etak-forecast1): the refusal MESSAGE of [eta_f1.kf_unfold_first].
    [rocq compile] prints no [Fail] message, so [Fail] alone shows only that the command failed, for any
    reason. [Redirect] writes the failure message to [etak_f1_kf_unfold_first.out] in the build directory,
    where the build reads it (expected: "Types are not convertible", the recorded completeness gap B1). *)
From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.
From MetaRocq.TestSuite Require eta_f1.

Redirect "etak_f1_kf_unfold_first" Fail MetaRocq SafeCheck eta_f1.kf_unfold_first.
