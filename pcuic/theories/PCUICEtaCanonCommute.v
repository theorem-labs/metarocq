(* Distributed under the terms of the MIT license. *)

(** * Exact strong commutation of [R_c] and [eta1]

    [R_c_eta1_strong_commutation] : ClosedBodies Σ -> is_closed_context Γ ->
      is_open_term Γ t -> canon t = t ->
      R_c Σ Γ t v -> eta1 t u ->
      ∑ z, clos_refl (R_c Σ Γ) u z × clos_refl_trans eta1 v z

  This is (A)'s strong-commutation premise at [E := eq] ([PCUICEtaCanonC4]): at
  most one [R_c] step on the η side, any number of η steps on the [R_c] side, and
  the two meet exactly, with no modulo relation. That exactness is the point of
  the canonical-domain route: the refuted C4 ([C4_false], [PCUICEtaC1b]) needed a
  join modulo [upto_domain], which does not compose.

  **Route.** C3 ([C3R.red1_eta1_strong_commutation], [PCUICEtaC3BR]) joins the
  underlying [red1] step and the η step up to [upto_domain_r]. Then:
  - [upto_domain_r w w'] gives [canon w = canon w'] ([upto_domain_r_canon_iff]),
    so both sides meet at [z := canon w];
  - the η side: a [red1] step from [u] is an [R_c] step by definition; no step
    leaves [u], which is canonical by [eta1_canonical];
  - the [R_c] side: [eta1* v0 w'] maps through [canon] to
    [eta1* (canon v0) (canon w')] by [eta1_canon], and [v = canon v0].

  Dependencies: [PCUICEtaC3BR], [PCUICEtaCanonRed], [PCUICEtaCanonEta]. No
  confluence file. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICReduction PCUICTyping
     PCUICOnFreeVars PCUICEtaDefs PCUICEtaCanon PCUICEtaC3BR PCUICEtaCanonRed
     PCUICEtaCanonEta PCUICClosedBodies.

Local Open Scope type_scope.

(** [eta1_canon], lifted to reflexive-transitive closures. *)
Lemma eta1_star_canon a b :
  clos_refl_trans eta1 a b -> clos_refl_trans eta1 (canon a) (canon b).
Proof.
  induction 1 as [a b h|a|a b c _ IH1 _ IH2].
  - destruct (clos_refl_case _ _ _ (eta1_canon a b h)) as [h'|e];
      [now apply rt_step|rewrite e; apply rt_refl].
  - apply rt_refl.
  - eapply rt_trans; [exact IH1|exact IH2].
Qed.

Theorem R_c_eta1_strong_commutation {cf : checker_flags} Σ Γ t u v :
  ClosedBodies Σ -> is_closed_context Γ -> is_open_term Γ t -> canon t = t ->
  R_c Σ Γ t v -> eta1 t u ->
  ∑ z, clos_refl (R_c Σ Γ) u z × clos_refl_trans eta1 v z.
Proof.
  intros wfΣ hΓ ht ct [v0 [r ->]] e.
  destruct (C3R.red1_eta1_strong_commutation Σ Γ t u v0 wfΣ hΓ ht r e)
    as (w & w' & hw & hw' & ew).
  have cu : canon u = u := eta1_canonical t u ct e.
  have eww : canon w = canon w' := canon_eq_of_upto_domain_r w w' ew.
  exists (canon w). split.
  - destruct (clos_refl_case _ _ _ hw) as [hw1|<-].
    + apply r_step. exists w. split; [exact hw1|reflexivity].
    + (* no step on the η side: [u] is canonical *) rewrite cu. apply r_refl.
  - rewrite eww. now apply eta1_star_canon.
Qed.
