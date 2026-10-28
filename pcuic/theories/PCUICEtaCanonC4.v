(* Distributed under the terms of the MIT license. *)

(** * BET-315 eta lane, §6.2 obligation 7: the NEW C4 — EXACT βη-confluence of
      [R_c ∪ eta1] on canonical, scoped terms

    [canon_beta_eta_confluence] : wf Σ -> is_closed_context Γ ->
      is_open_term Γ t -> canon t = t ->
      (R_c ∪ eta1)* t u -> (R_c ∪ eta1)* t v ->
      ∑ w, (R_c ∪ eta1)* u w × (R_c ∪ eta1)* v w

  This replaces the REFUTED modulo-[upto_domain] C4 ([C4_false], wip/c4-C4C1b
  @ 73bbb2d1; plan.md risk row 4, §6.1). It is EXACT: no equivalence in the
  conclusion. It is the theorem A3 consumes.

  **Theorems (A) and (B) are applied AS PROVED, at [E := eq].** Nothing in
  their files is edited:
  - (A) [HR_strong_commutation_modulo], C4A1's, cherry-picked from 0536d1f2;
  - (B) [HR_modulo], C4B's 18f37f50 (byte-identical to the copy carried by
    EtaL2's 2f55b23a, both cherry-picked).
  Every [E]-hypothesis is trivial at [E := eq] (reflexivity, or a [subst]),
  exactly as plan.md §6.2 forecast. The invariant is
  [Q t := is_open_term Γ t × canon t = t].

  **What each premise comes from.**
  - [R_c] preserves [Q]: base [red1] scoping (P-SCOPE's [beta_eta_is_open_term],
    EtaL2's 168bf406) then [canon_is_open_term]; canonicity by [canon_idem].
  - [eta1] preserves [Q]: P-SCOPE's [eta1_on_free_vars] and [eta1_canonical].
  - strong commutation: [R_c_eta1_strong_commutation] (obligation 5), which is
    already EXACT, so the two join points coincide.
  - [R_c] confluent on [Q]: [R_c_confluence] (obligation 4; C4-side).
  - [eta1] confluent: C4U6U8's [eta1_confluence] (363f2174), exact, which at
    [E := eq] is (B)'s "confluent modulo E" premise.
  - [R_c*] and [eta1*] commute: (A)'s conclusion.

  **This is a C4-side file**: through obligation 4 it reaches base
  [PCUICConfluence], as the lane rules allow. No C3-side file may Require it. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICReduction PCUICTyping
     PCUICOnFreeVars PCUICEtaDefs PCUICEtaBetaEta PCUICEtaScope
     PCUICEtaHRCommutationA1 PCUICEtaHRModulo PCUICEtaU8
     PCUICEtaCanon PCUICEtaCanonRed PCUICEtaCanonConfluence PCUICEtaCanonEta
     PCUICEtaCanonCommute.

Local Open Scope type_scope.

(** ** The invariant [Q]: canonical and scoped *)

Definition Qc (Γ : context) (t : term) : Type := is_open_term Γ t × canon t = t.

Lemma red1_is_open_term {cf : checker_flags} {Σ : global_env} (wfΣ : wf Σ) {Γ t u} :
  is_closed_context Γ -> red1 Σ Γ t u -> is_open_term Γ t -> is_open_term Γ u.
Proof.
  intros HΓ r ht. eapply (beta_eta_is_open_term (wfΣ := wfΣ)); [exact HΓ| |exact ht].
  apply rt_step. left. exact r.
Qed.

Lemma Qc_R_c {cf : checker_flags} (Σ : global_env) (wfΣ : wf Σ) Γ :
  is_closed_context Γ -> forall t u, Qc Γ t -> R_c Σ Γ t u -> Qc Γ u.
Proof.
  intros HΓ t u [ht ct] [u0 [r ->]]. split.
  - apply canon_is_open_term. exact (red1_is_open_term wfΣ HΓ r ht).
  - apply canon_idem.
Qed.

Lemma Qc_eta1 Γ : forall t u, Qc Γ t -> eta1 t u -> Qc Γ u.
Proof.
  intros t u [ht ct] e. split.
  - exact (eta1_on_free_vars t u e _ ht).
  - exact (eta1_canonical t u ct e).
Qed.

(** ** [E := eq]: every [E]-hypothesis is trivial *)

Lemma eq_commutes {A} (R : A -> A -> Type) (Q : A -> Type) :
  forall t t' u, Q t -> Q t' -> t = t' -> R t u -> ∑ u', clos_refl R t' u' × u = u'.
Proof. intros t t' u _ _ <- r. exists u. split; [now apply r_step|reflexivity]. Qed.

Lemma eq_refl_c {A} : CRelationClasses.Reflexive (fun x y : A => x = y).
Proof. intros x; reflexivity. Qed.
Lemma eq_sym_c {A} : CRelationClasses.Symmetric (fun x y : A => x = y).
Proof. intros x y e; now symmetry. Qed.
Lemma eq_trans_c {A} : CRelationClasses.Transitive (fun x y : A => x = y).
Proof. intros x y z e1 e2; now transitivity y. Qed.

(** ** (A)'s strong-commutation premise, from obligation 5 *)

Lemma Qc_strong_commutation {cf : checker_flags} (Σ : global_env) (wfΣ : wf Σ) Γ :
  is_closed_context Γ ->
  forall t u v, Qc Γ t -> R_c Σ Γ t v -> eta1 t u ->
    ∑ w w', clos_refl (R_c Σ Γ) u w × clos_refl_trans eta1 v w' × w = w'.
Proof.
  intros HΓ t u v [ht ct] r e.
  destruct (R_c_eta1_strong_commutation Σ Γ t u v wfΣ HΓ ht ct r e) as (z & hz & hz').
  exists z, z. repeat split; [exact hz|exact hz'].
Qed.

(** ** (A) applied: [R_c*] and [eta1*] commute EXACTLY on [Q] *)

Lemma R_c_eta1_commute {cf : checker_flags} (Σ : global_env) (wfΣ : wf Σ) Γ :
  is_closed_context Γ ->
  forall t u v, Qc Γ t -> clos_refl_trans (R_c Σ Γ) t u -> clos_refl_trans eta1 t v ->
    ∑ u' v', clos_refl_trans eta1 u u' × clos_refl_trans (R_c Σ Γ) v v' × u' = v'.
Proof.
  intros HΓ.
  exact (HR_strong_commutation_modulo term (R_c Σ Γ) eta1 (fun x y => x = y) (Qc Γ)
           (Qc_R_c Σ wfΣ Γ HΓ) (Qc_eta1 Γ) eq_refl_c eq_sym_c eq_trans_c
           (eq_commutes (R_c Σ Γ) (Qc Γ)) (eq_commutes eta1 (Qc Γ))
           (Qc_strong_commutation Σ wfΣ Γ HΓ)).
Qed.

(** ** (B) applied: the NEW C4 *)

Theorem canon_beta_eta_confluence {cf : checker_flags} (Σ : global_env_ext) (wfΣ : wf Σ)
  Γ t u v :
  is_closed_context Γ -> is_open_term Γ t -> canon t = t ->
  clos_refl_trans (union (R_c Σ Γ) eta1) t u ->
  clos_refl_trans (union (R_c Σ Γ) eta1) t v ->
  ∑ w, clos_refl_trans (union (R_c Σ Γ) eta1) u w ×
       clos_refl_trans (union (R_c Σ Γ) eta1) v w.
Proof.
  intros HΓ ht ct hu hv.
  destruct (HR_modulo term (R_c Σ Γ) eta1 (fun x y => x = y) (Qc Γ)
              (Qc_R_c Σ wfΣ Γ HΓ) (Qc_eta1 Γ) eq_refl_c eq_sym_c eq_trans_c
              (eq_commutes (R_c Σ Γ) (Qc Γ)) (eq_commutes eta1 (Qc Γ))
              (fun t0 u0 v0 '(ht0, ct0) h1 h2 => R_c_confluence Σ wfΣ Γ t0 u0 v0 HΓ ht0 ct0 h1 h2)
              (fun t0 u0 v0 _ h1 h2 =>
                 let '(w; (hw1, hw2)) := eta1_confluence t0 u0 v0 h1 h2 in
                 (w; (w; (hw1, (hw2, eq_refl)))))
              (R_c_eta1_commute Σ wfΣ Γ HΓ)
              t u v (ht, ct) hu hv) as (u' & v' & hu' & hv' & e).
  exists u'. split; [exact hu'|]. rewrite e. exact hv'.
Qed.
