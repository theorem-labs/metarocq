(* Distributed under the terms of the MIT license. *)

(** * BET-315 eta lane, K6: the I7 η step, mapped into the spec and into the join

  The checker's η branch (plan I7, the kernel's [conversion.ml:560-580]) compares
  [t] against [(↑u) (tRel 0)] under the λ's binder, at [Conv], and concludes
  that [λx:A. t] and [u] are convertible. [isconv_sound] over E needs that step
  in the spec ([K6_eta_step]), and A3/A6 need it in the canonical join
  ([K6_eta_step_join]).

    [K6_eta_step]      : JoinE r Σ (Γ ,, vass na A) Conv t ((↑u) (tRel 0)) ->
                         Σ ;;; Γ ⊢ λ na:A. t ≤sE[pb] u
    [K6_eta_step_join] : the same premise -> JoinE r Σ Γ pb (λ na:A. t) u

  [K6_eta_step]: A4 ([I5_join_to_spec]) turns the join into the spec premise of
  [cumul_eta_l]. [K6_eta_step_join] is obligation 9 ([I5_eta_l_case_holds]),
  whose factorisation (F) is where [is_constructor_app_tRel0] is used: [red_fix]
  at the root of [(↑x) (tRel 0)] fires only on an earlier argument.

  It edits no base file and none of prim-ops' files ([PCUICSafeReduce.v],
  [PCUICSafeConversion.v], [Syntax/PCUICPosition.v]).

  **Hypotheses satisfiable (FRAC's rule):** [wf Σ] by any well-formed
  environment; the scoping premises by any scoped context and terms; the join
  by [t := (↑u) (tRel 0)] (the join of a term with itself). C4-side. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICCumulativitySpecEta PCUICEtaFInst PCUICEtaI5 PCUICEtaI5A2 PCUICEtaI5EtaL.

Section K6.

  Context {cf : checker_flags} (Σ : global_env_ext) (wfΣ : wf Σ) (r : finst_construct_rule).

  (** The η step, into the spec. *)
  Theorem K6_eta_step Γ pb na A t u :
    is_closed_context Γ -> is_open_term Γ (tLambda na A t) -> is_open_term Γ u ->
    JoinE r Σ (Γ ,, vass na A) Conv t (tApp (lift0 1 u) (tRel 0)) ->
    Σ ;;; Γ ⊢ tLambda na A t ≤sE[pb] u.
  Proof.
    intros hΓ hl hu hj. apply cumul_eta_l.
    move: (hl). cbn [on_free_vars]. move/andP => [hA ht].
    apply (I5_join_to_spec Σ wfΣ r (Γ ,, vass na A) Conv t (tApp (lift0 1 u) (tRel 0))).
    - exact (closed_snoc_vass Γ na A hΓ hA).
    - exact (open_snoc Γ _ t ht).
    - apply open_snoc. cbn [on_free_vars]. apply/andP; split; [|reflexivity].
      apply on_free_vars_lift0. rewrite (on_free_vars_ext _ _ u (addnP_shiftnP 1 _)). exact hu.
    - exact hj.
  Qed.

  (** The η step, into the canonical join (obligation 9). *)
  Theorem K6_eta_step_join Γ pb na A t u :
    is_closed_context Γ -> is_open_term Γ (tLambda na A t) -> is_open_term Γ u ->
    JoinE r Σ (Γ ,, vass na A) Conv t (tApp (lift0 1 u) (tRel 0)) ->
    JoinE r Σ Γ pb (tLambda na A t) u.
  Proof. exact (I5_eta_l_case_holds Σ wfΣ r Γ pb na A t u). Qed.

End K6.
