(* Distributed under the terms of the MIT license. *)
(** * BET-315 eta lane, C4: SHAPE GUARD for theorem (A).

   A machine-checked proof that theorem (A) as stated in [PCUICEtaBetaEta] IS
   instantiable at the PCUIC instance by the lemmas we actually have — C3,
   P-SCOPE and the [upto_domain] equivalence — leaving only C1a/C1b as
   hypotheses. This designs out, rather than merely warns about, the failure
   "a correct abstract theorem that cannot be instantiated": if (A)'s hypothesis
   shapes drift from C3's, this file stops compiling.

   DIRECTION (binding): this is a C4 file and may Require C3 files. No C3 file
   may Require this one. *)

From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICReduction PCUICOnFreeVars PCUICTyping
     PCUICEtaDefs PCUICEtaConfluence PCUICEtaBetaEta PCUICEtaScope PCUICEtaC3B PCUICClosedBodies.

Lemma HR_A_instantiable {cf : checker_flags} (Σ : global_env) (wfΣ : ClosedBodies Σ) (Γ : context) :
  is_closed_context Γ ->
  HR_strong_commutation_modulo_statement ->
  (* C1a, at a fixed context *)
  (forall t t' u, upto_domain t t' -> red1 Σ Γ t u ->
     ∑ u', clos_refl (red1 Σ Γ) t' u' × upto_domain u u') ->
  (* C1b *)
  (forall t t' u, upto_domain t t' -> eta1 t u ->
     ∑ u', clos_refl eta1 t' u' × upto_domain u u') ->
  forall t u v, is_open_term Γ t ->
    clos_refl_trans (red1 Σ Γ) t u -> clos_refl_trans eta1 t v ->
    ∑ u' v', clos_refl_trans eta1 u u' × clos_refl_trans (red1 Σ Γ) v v' × upto_domain u' v'.
Proof.
  intros HΓ HA C1a C1b.
  have HΓ' : on_ctx_free_vars (shiftnP #|Γ| xpred0) Γ
    by rewrite on_free_vars_ctx_on_ctx_free_vars.
  apply (HA term (red1 Σ Γ) eta1 upto_domain (is_open_term Γ)).
  - (* R preserves Q: base, via P-SCOPE *)
    intros t u Ht Hr.
    (* [left] head-normalises [beta_eta1] to the sum; a bare [inl] does not unify *)
    apply (@beta_eta1_on_free_vars cf Σ wfΣ _ Γ t u HΓ'); [left; exact Hr | exact Ht].
  - (* S preserves Q: P-SCOPE's new content *)
    intros t u Ht He. exact (eta1_on_free_vars _ _ He _ Ht).
  - exact upto_domain_refl.
  - exact upto_domain_sym.
  - exact upto_domain_trans.
  - intros t t' u _ _ He Hr. exact (C1a t t' u He Hr).
  - intros t t' u _ _ He Hs. exact (C1b t t' u He Hs).
  - (* strong commutation: C3, VERBATIM *)
    intros t u v Ht Hr Hs. eapply red1_eta1_strong_commutation; eassumption.
Qed.
