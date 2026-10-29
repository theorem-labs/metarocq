(* Distributed under the terms of the MIT license. *)

(** * β-reduction simulated on canonical forms

  [R_c] is the canonical-domain reduction: one [red1] step, then re-canonicalise
  (after every step, because δ, ι, [red_rel] and steps under instantiated contexts
  all produce non-canonical λ-domains).

    [R_c Σ Γ t v := ∑ v0, red1 Σ Γ t v0 × v = canon v0]

  This file proves that [red1] and [R_c] simulate each other through [canon], in
  both directions and lifted to reflexive-transitive closures:

    [red1_R_c]   red1 t u            -> R_c^= (canon t) (canon u)
    [red_R_c]    red t u             -> R_c* (canon t) (canon u)
    [R_c_red]    R_c* t v            -> ∑ v0, red t v0 × canon v0 = canon v

  These transfer base confluence to [R_c] ([R_c_confluence],
  [PCUICEtaCanonConfluence]): map an [R_c*] chain back to a [red*] chain up to
  [canon] ([R_c_red]), join there, map forward ([red_R_c]).

  **No scoping premise.** Both inputs hold for all terms
  ([upto_domain_r_canon_self] and [red1_upto_domain_r_fixed] have no [is_open_term]
  premise), so the simulations do too.

  **Why it needs nothing else.** [upto_domain_r t (canon t)] plus C1a turns a step
  from [t] into a step-or-nothing from [canon t] whose result is
  [upto_domain_r]-related, hence [canon]-equal ([upto_domain_r_canon_iff]).

  Dependencies: [PCUICEtaCanon], [PCUICEtaC1aR]. No confluence file. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICReduction
     PCUICEtaDefs PCUICEtaCanon PCUICEtaC1aR.

Local Open Scope type_scope.

(** ** [R_c] *)

Definition R_c Σ Γ (t v : term) : Type := ∑ v0, red1 Σ Γ t v0 × v = canon v0.

(** [canon]-equality from [upto_domain_r], in the direction used here. *)
Lemma canon_eq_of_upto_domain_r t u : upto_domain_r t u -> canon t = canon u.
Proof. apply upto_domain_r_canon_iff. Qed.

(** ** One step

  A [red1] step from [t] becomes at most one [R_c] step from [canon t].
  [upto_domain_r (canon t) t] is [upto_domain_r_canon_self], read backwards; C1a
  then moves the step across the relation. *)

Lemma red1_from_canon Σ Γ t u :
  red1 Σ Γ t u ->
  ∑ u', clos_refl (red1 Σ Γ) (canon t) u' × canon u = canon u'.
Proof.
  intros r.
  have e : upto_domain_r t (canon t) := upto_domain_r_canon_self t.
  destruct (red1_upto_domain_r_fixed e r) as (u' & hu' & eu).
  exists u'. split; [exact hu'|]. now apply canon_eq_of_upto_domain_r.
Qed.

Lemma red1_R_c Σ Γ t u :
  red1 Σ Γ t u -> clos_refl (R_c Σ Γ) (canon t) (canon u).
Proof.
  intros r. destruct (red1_from_canon Σ Γ t u r) as (u' & hu' & eu).
  destruct hu' as [u'' hr|].
  - apply r_step. exists u''. split; [exact hr|exact eu].
  - (* no step: [u' = canon t], so [canon u = canon (canon t) = canon t] *)
    rewrite eu canon_idem. apply r_refl.
Qed.

(** ** Closures *)

Lemma red_R_c Σ Γ t u :
  red Σ Γ t u -> clos_refl_trans (R_c Σ Γ) (canon t) (canon u).
Proof.
  induction 1 as [t u r|t|t u w _ IH1 _ IH2].
  - destruct (red1_R_c Σ Γ t u r) as [? h|]; [now apply rt_step|apply rt_refl].
  - apply rt_refl.
  - eapply rt_trans; [exact IH1|exact IH2].
Qed.

(** The backward direction. A chain of [R_c] steps from an ARBITRARY [t] is a
    [red] chain from [t], up to [canon]. Each step starts at a CANONICAL term
    [canon v0], but the [red] chain must continue from [v0] itself, so C1a is
    used once more, against [upto_domain_r (canon v0) v0]. *)
Lemma R_c_red Σ Γ t v :
  clos_refl_trans (R_c Σ Γ) t v -> ∑ v0, red Σ Γ t v0 × canon v0 = canon v.
Proof.
  intros h. apply clos_rt_rt1n_iff in h.
  induction h as [t|t v w hs _ IH].
  - exists t. split; [apply rt_refl|reflexivity].
  - destruct hs as (v1 & r1 & ->).
    destruct IH as (w0 & hw0 & ew0).
    (* [red (canon v1) w0]; move it across [upto_domain_r (canon v1) v1]. *)
    have e : upto_domain_r (canon v1) v1 := upto_domain_r_sym _ _ (upto_domain_r_canon_self v1).
    assert (move : forall a b a', red Σ Γ a b -> upto_domain_r a a' ->
                     ∑ b', red Σ Γ a' b' × upto_domain_r b b').
    { clear. intros a b a' hab. revert a'.
      apply clos_rt_rt1n_iff in hab.
      induction hab as [a|a b c hs _ IH]; intros a' ea.
      - exists a'. split; [apply rt_refl|exact ea].
      - destruct (red1_upto_domain_r_fixed ea hs) as (b' & hb' & eb).
        destruct (IH b' eb) as (c' & hc' & ec).
        exists c'. split; [|exact ec].
        eapply rt_trans; [|exact hc'].
        destruct hb' as [? hb'|]; [now apply rt_step|apply rt_refl]. }
    destruct (move _ _ _ hw0 e) as (w1 & hw1 & ew1).
    exists w1. split.
    + eapply rt_trans; [now apply rt_step|exact hw1].
    + rewrite <- ew0. symmetry. now apply canon_eq_of_upto_domain_r.
Qed.
