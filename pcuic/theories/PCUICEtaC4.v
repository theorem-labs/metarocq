(* Distributed under the terms of the MIT license. *)
(** * BET-315 eta lane, C4 / I4: βη confluence up to [upto_domain] — ASSEMBLY.

   P-INST (EtaL2). This file proves [C4_statement] from STAGED hypotheses, each
   stated EXACTLY as the dispatched prover delivers it; landed ones are swapped
   for the real lemma.
     HA   theorem (A)  [HR_strong_commutation_modulo_statement]  (C4A1, C4A2) staged
     HB   theorem (B)  [HR_modulo_statement]                     (C4B)  LANDED:
          [HR_modulo], [PCUICEtaHRModulo] (from wip/c4-C4B-2026-10-28 @ 18f37f50)
     C1a  [C1a_fixed_statement]                                   (C4C1a) staged
     C1b  [C1b_statement]                                         (C4C1b) staged
     U8   [U8_statement]                                          (C4U6U8) staged
   Everything else is discharged by lemmas that already exist: [red_confluence]
   (the β leg, base), P-SCOPE ([PCUICEtaScope]), the [upto_domain] equivalence
   ([PCUICEtaConfluence]) and the (A) shape guard ([PCUICEtaC4Shape], which
   itself consumes C3). When a prover lands, its [Context] hypothesis is replaced
   by the real lemma; nothing else in the instantiation should move.

   THIS IS THE FIRST FILE THAT JOINS C4 TO BASE CONFLUENCE ([PCUICConfluence]).
   That is ruled and allowed for C4. DIRECTION (binding, checked at the C4 gate):
   no C3 file may Require this file, directly or transitively. *)

From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICReduction PCUICOnFreeVars PCUICTyping
     PCUICConfluence PCUICEtaDefs PCUICEtaConfluence PCUICEtaBetaEta PCUICEtaScope
     PCUICEtaC4Shape PCUICEtaC3B PCUICEtaHRModulo.

(** ** Staged statements: [C1a_fixed_statement], [C1b_statement] and
    [U8_statement] live in the confluence-free shared file [PCUICEtaBetaEta]
    (byte-identical), NOT here: this file Requires [PCUICConfluence], and a
    prover that Required its pinned statement from here would inherit base
    confluence for a statement that is itself confluence-free. *)

(** ######################################################################
    RETIRED (2026-10-28). P-INST below is no longer a target of any lane.
    WHY: it proves [C4_statement], which is FALSE ([C4_false], PCUICEtaC1b.v,
    cherry-picked here as ce081fa7 from 99136ff0), and it does so from staged
    hypotheses that include the false [C1b_statement] ([C1b_false]). So its
    [Context] hypotheses can never be discharged. The HA swap was never made.
    REPLACED BY: the canonical-domain route, lanes/eta/plan.md §6.2 —
    [canon_beta_eta_confluence] (PCUICEtaCanonC4.v, c13e90d3) applies the same
    (A) and (B) AS PROVED at [E := eq] on canonical terms, and the restated I5
    is proved as [I5_FollowKernel] (PCUICEtaI5EtaL.v, f1f86e47). This file is
    kept only as the record of the Hindley-Rosen route; nothing Requires it.
    ###################################################################### *)

(** ** The assembly. *)

Section C4Assembly.
  Context (HA  : HR_strong_commutation_modulo_statement)
          (C1a : C1a_fixed_statement)
          (C1b : C1b_statement)
          (U8  : U8_statement).

  Theorem beta_eta_confluence : C4_statement.
  Proof.
    intros cf Σ wfΣ Γ t u v HΓ Ht Hu Hv.
    rewrite /beta_eta /beta_eta1 in Hu Hv |- *.
    have HΓ' : on_ctx_free_vars (shiftnP #|Γ| xpred0) Γ
      by rewrite on_free_vars_ctx_on_ctx_free_vars.
    (* (B): the real lemma, no longer a hypothesis *)
    eapply (HR_modulo term (red1 Σ Γ) eta1 upto_domain (is_open_term Γ)).
    - (* R preserves Q (P-SCOPE, base half) *)
      intros a b Ha Hr.
      apply (@beta_eta1_on_free_vars cf Σ (PCUICClosedTyp.wf_ClosedBodies Σ) _ Γ a b HΓ'); [left; exact Hr | exact Ha].
    - (* S preserves Q (P-SCOPE, new half) *)
      intros a b Ha He. exact (eta1_on_free_vars _ _ He _ Ha).
    - exact upto_domain_refl.
    - exact upto_domain_sym.
    - exact upto_domain_trans.
    - (* E vs R *)
      intros a a' b _ _ He Hr. exact (C1a Σ Γ a a' b He Hr).
    - (* E vs S *)
      intros a a' b _ _ He Hs. exact (C1b a a' b He Hs).
    - (* R confluent on Q: base [red_confluence], packing the subtypes *)
      intros a b c Ha Hb Hc.
      destruct (@red_confluence cf (empty_ext Σ) wfΣ (exist Γ HΓ) (exist a Ha) b c Hb Hc)
        as [w [Hw1 Hw2]].
      exists w. split; assumption.
    - (* S confluent modulo E on Q: U8 *)
      intros a b c _ Hb Hc. exact (U8 a b c Hb Hc).
    - (* R* and S* commute modulo E on Q: (A), via the shape guard (C3 inside) *)
      intros a b c Ha Hb Hc.
      exact (HR_A_instantiable Σ (PCUICClosedTyp.wf_ClosedBodies Σ) Γ HΓ HA (C1a Σ Γ) C1b a b c Ha Hb Hc).
    - exact Ht.
    - exact Hu.
    - exact Hv.
  Qed.
End C4Assembly.
