(* Distributed under the terms of the MIT license. *)
(** * BET-315 eta lane, C4 / I4: βη confluence up to [upto_domain] — ASSEMBLY.

   P-INST (EtaL2). This file proves [C4_statement] from five STAGED hypotheses,
   each stated EXACTLY as the dispatched prover delivers it:
     HA   theorem (A)  [HR_strong_commutation_modulo_statement]  (C4A1, C4A2)
     HB   theorem (B)  [HR_modulo_statement]                     (C4B)
     C1a  [C1a_fixed_statement]                                   (C4C1a)
     C1b  [C1b_statement]                                         (C4C1b)
     U8   [U8_statement]                                          (C4U6U8)
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
     PCUICEtaC4Shape PCUICEtaC3B.

(** ** Staged statements — exact, as dispatched. *)

(** C1a at a FIXED context: all C4 needs ([HR_A_instantiable] takes it at
    [Γ' := Γ]). The one-step form is FALSE (B3(b)); [clos_refl] is required. *)
Definition C1a_fixed_statement : Type :=
  forall (Σ : global_env) (Γ : context) (t t' u : term),
    upto_domain t t' -> red1 Σ Γ t u ->
    ∑ u', clos_refl (red1 Σ Γ) t' u' × upto_domain u u'.

Definition C1b_statement : Type :=
  forall (t t' u : term),
    upto_domain t t' -> eta1 t u ->
    ∑ u', clos_refl eta1 t' u' × upto_domain u u'.

(** U8: η confluence modulo [upto_domain]. Unscoped, as η is context-free and
    upstream's U7 ([eta1_local_confluence], origin/eta_postpo
    PCUICEtaReduction.v:152) is unscoped. NOTE: upstream U7 is EXACT local
    confluence ([∑ v, eta u1 v × eta u2 v], no [upto_domain]), so U8 may be
    proved exactly by Newman from U6 + U7 and then weakened by [upto_domain_refl]
    — C1b is not needed for U8. Newman IS valid here: η alone is SN (U6). *)
Definition U8_statement : Type :=
  forall (t u v : term),
    clos_refl_trans eta1 t u -> clos_refl_trans eta1 t v ->
    ∑ u' v', clos_refl_trans eta1 u u' × clos_refl_trans eta1 v v' × upto_domain u' v'.

(** ** The assembly. *)

Section C4Assembly.
  Context (HA  : HR_strong_commutation_modulo_statement)
          (HB  : HR_modulo_statement)
          (C1a : C1a_fixed_statement)
          (C1b : C1b_statement)
          (U8  : U8_statement).

  Theorem beta_eta_confluence : C4_statement.
  Proof.
    intros cf Σ wfΣ Γ t u v HΓ Ht Hu Hv.
    rewrite /beta_eta /beta_eta1 in Hu Hv |- *.
    have HΓ' : on_ctx_free_vars (shiftnP #|Γ| xpred0) Γ
      by rewrite on_free_vars_ctx_on_ctx_free_vars.
    eapply (HB term (red1 Σ Γ) eta1 upto_domain (is_open_term Γ)).
    - (* R preserves Q (P-SCOPE, base half) *)
      intros a b Ha Hr.
      apply (@beta_eta1_on_free_vars cf Σ wfΣ _ Γ a b HΓ'); [left; exact Hr | exact Ha].
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
      exact (HR_A_instantiable Σ wfΣ Γ HΓ HA (C1a Σ Γ) C1b a b c Ha Hb Hc).
    - exact Ht.
    - exact Hu.
    - exact Hv.
  Qed.
End C4Assembly.
