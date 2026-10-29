(* Distributed under the terms of the MIT license. *)

(** * [R_c] is confluent on canonical terms

    [R_c_confluence] : ClosedBodies Σ -> is_closed_context Γ -> is_open_term Γ t ->
      canon t = t ->
      R_c* t u -> R_c* t v -> ∑ w, R_c* u w × R_c* v w

  **Route.** Base [red_confluence_cb] ([PCUICConfluence]) through the simulations
  of [PCUICEtaCanonRed]: map each [R_c*] chain back to a [red*] chain up to
  [canon] ([R_c_red]), join there, and map the join forward ([red_R_c]).

  **Why [canon t = t] is needed.** [red_R_c] lands in [R_c*] from [canon u], not
  from [u]. The two coincide exactly when [u] is canonical, and
  [R_c_star_canonical] says every [R_c*]-reduct of a canonical term is canonical,
  because each [R_c] step ends in [canon]. The scoping premises are
  [red_confluence_cb]'s own; the simulations need none.

  This file Requires base [PCUICConfluence]. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICReduction PCUICTyping
     PCUICOnFreeVars PCUICConfluence PCUICEtaDefs PCUICEtaCanon PCUICEtaCanonRed PCUICClosedBodies.

Local Open Scope type_scope.

(** Every [R_c*]-reduct of a canonical term is canonical. *)
Lemma R_c_star_canonical Σ Γ t u :
  canon t = t -> clos_refl_trans (R_c Σ Γ) t u -> canon u = u.
Proof.
  intros ct h. revert ct.
  induction h as [t u [u0 [_ ->]]|t|t u w _ IH1 _ IH2]; intros ct.
  - apply canon_idem.
  - exact ct.
  - apply IH2, IH1, ct.
Qed.

Theorem R_c_confluence {cf : checker_flags} (Σ : global_env_ext) (wfΣ : ClosedBodies Σ) Γ t u v :
  is_closed_context Γ -> is_open_term Γ t -> canon t = t ->
  clos_refl_trans (R_c Σ Γ) t u -> clos_refl_trans (R_c Σ Γ) t v ->
  ∑ w, clos_refl_trans (R_c Σ Γ) u w × clos_refl_trans (R_c Σ Γ) v w.
Proof.
  intros hΓ ht ct hu hv.
  destruct (R_c_red _ _ _ _ hu) as (u0 & ru & eu).
  destruct (R_c_red _ _ _ _ hv) as (v0 & rv & ev).
  destruct (@red_confluence_cb cf Σ wfΣ (exist Γ hΓ) (exist t ht) u0 v0 ru rv)
    as (w & ruw & rvw).
  exists (canon w). split.
  - rewrite -(R_c_star_canonical _ _ _ _ ct hu) -eu. now apply red_R_c.
  - rewrite -(R_c_star_canonical _ _ _ _ ct hv) -ev. now apply red_R_c.
Qed.
