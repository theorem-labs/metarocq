(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICTypingEta.
From Equations Require Import Equations.

(** * ETAK (EtaK7): the E typing notions the η checker uses — CANONICAL, imported

  BET-64 EtaCheckerLane, worker EtaK7, 2026-10-29. This file defines none of them (stream lead's ruling,
  2026-10-29: it must in the end import those definitions and redefine none of them). Canonical switch against
  [frac/eta] @ [d49d1c19] (lane lead, 16:5xZ). Each of the 15 notions below was checked, before its copy here was
  deleted, by a machine diff (comments stripped, token level) and a compiled identity both ways (rule v11:
  [eq_refl] in both directions for the definitions, structure-preserving maps in both directions for the
  inductives and the record), against the copy at [614301b6] (record: [lanes/eta/etak/EtaK7.md], "CANONICAL
  SWITCH, REVISED"):
  - [PCUICTypingEtaNotions] (ArityLane, T0): [isTypeRelE], [isTypeE], [isTypeRelE_isTypeE] (and its coercion),
    [wf_local_relE], [ctx_instE], [isWfArityE], [isTypeE_welltypedE], [isTypeRelE_welltypedE],
    [has_sort_isTypeE], [has_sort_isTypeRelE];
  - [PCUICSubstitutionEta]: [subsletE]; [PCUICAritiesEta]: [typing_spineE];
  - [PCUICSpineEta] (copy 15): [spine_substE], [ctx_inst_subE];
  - the notations [Σ ;;; Γ ⊢E t ≤[pb] u], [⊢E t ≤ u], [⊢E t = u]: [PCUICWellScopedCumulativityEta], which every
    user of this file imports.
  This file re-exports the four modules above (not their own imports: [PCUICAritiesEta] Requires, and does not
  Import, [PCUICGenerationEta], so the import guard holds), and the bidirectional judgments below. *)

From MetaRocq.PCUIC Require Export PCUICTypingEtaNotions PCUICSubstitutionEta PCUICAritiesEta PCUICSpineEta.

(** ** Bidirectional typing over E: CANONICAL, imported

  Stream lead's ruling (2026-10-29, ~09:45Z): the bidirectional judgments are EtaMetaLane's [BDTypingEta]
  ([pcuic/theories/Bidirectional/BDTypingEta.v], landed on [frac/eta] as [da1eb84b], text identical to
  [b0523fbf] which this branch merged). This file no longer defines them. [BDTypingEta]'s [checkE_Cumul] and the
  case rule's parameters compare with [JoinE] (base's unscoped [cumulAlgo]/[convAlgo] twin); the checker
  builds them from its [ws_cumul_pbE] results with [checkE_Cumul_ws] / [All2_ws_cumul_pbE_JoinE], and a
  consumer that needs the scoped relation back uses [JoinE_ws_cumul_pbE]. [BDTypingEta] derives no
  signature; the checker's proofs ([depelim]) need one, so it is derived here. *)

From MetaRocq.PCUIC Require Export BDTypingEta.

Derive Signature for inferingE infering_sortE infering_prodE infering_induE checkingE.
