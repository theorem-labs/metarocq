(* Private diagnostic test for frac/probe-nested.  This file is never merged. *)
From MetaRocq.Template Require Import Loader.
From MetaRocq.SafeCheckerPlugin Require Import Loader.

Inductive probe_rose :=
| ProbeNode : list probe_rose -> probe_rose.

(* This is the nested constructor-argument shape that blocks
   Stdlib.micromega.ZMicromega.ZArithProof. *)
Inductive probe_zarithproof_shape :=
| ProbeDeprecatedEnumProof : list probe_zarithproof_shape -> probe_zarithproof_shape.

MetaRocq SafeCheck probe_rose.
MetaRocq SafeCheck probe_zarithproof_shape.

(* This remains invalid in Rocq: the recursive occurrence is to the left of an
   arrow, so neither the kernel nor the diagnostic probe accepts it. *)
Fail Inductive probe_bad :=
| ProbeBad : (list probe_bad -> nat) -> probe_bad.
