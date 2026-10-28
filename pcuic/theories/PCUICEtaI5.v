(* Distributed under the terms of the MIT license. *)

(** * BET-315 eta lane, §6.2 obligation 8 — STAGED AT FollowSpec: I5 restated,
      and A4 (join ⇒ spec)

  NAMING, AS RULED: this is "8 staged at FollowSpec". "Obligation 8 done" is
  reserved for FollowKernel after repair (a). "I5 in full" is reported only when
  obligations 8 AND 9 are both green.

  ** The restated I5 (pinned here, parametric in the open constructor clause [r])

  The join relation [JoinE] runs on CANONICAL terms under [R_c ∪ eta1] and ends
  in U1' ([compare_term_eta], corrected at 0ca53659):

    [JoinE r Σ Γ pb t u := ∑ v v', (R_c ∪ eta1)* (canon t) v ×
                                   (R_c ∪ eta1)* (canon u) v' ×
                                   v ≈F[pb, 0] v']

    [I5_statement r Σ := ∀ Γ pb t u, closed Γ → open t → open u →
                           (t ≤sE[pb] u <~> JoinE r Σ Γ pb t u)]

  A4 (← : join ⇒ spec) is proved HERE, in full, as [I5_join_to_spec].
  A2 (→ : spec ⇒ join) is the remaining part of obligation 8; its [cumul_eta_l]
  case is obligation 9's premise, pinned below as [I5_eta_l_case].

  ** A4's route

    t ≤ canon t ≤* v ≤[pb] v' *≥ canon u ≥ u

  - [t ≤ canon t] and back: [canon_cumulSpecE] (+ [cumulE_Sym]);
  - each [R_c] step is [red1] then [canon]: [red1_cumulSpecE], [canon_cumulSpecE];
  - each [eta1] step: [eta1_cumulSpecE];
  - [v ≤[pb] v']: [compare_term_eta_cumulSpecE] (S4 under the under-applied heads);
  - every [cumulE_Trans] intermediate is scoped: [red1] scoping (P-SCOPE's
    [beta_eta_is_open_term]), [canon_is_open_term], [eta1_on_free_vars].

  **Hypotheses satisfiable (FRAC's rule).** [I5_join_to_spec]: [wf Σ] for any
  well-formed environment; scoping for any scoped pair; [JoinE] is inhabited by
  any term with itself ([canon t ⇝⁰ canon t], comparison reflexive). Non-vacuous
  witness: [JoinE] relates [λx:nat. id x] and [id] in an environment declaring
  [id], via one η step on the left ([lanes/eta/obligation9-probe.md] §4).

  Dependencies: confluence-free ([PCUICEtaScope], the A4 bridges, S4). *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICEquality PCUICReduction
     PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICEtaDefs PCUICEtaBetaEta PCUICEtaScope PCUICEtaCanon PCUICEtaCanonRed
     PCUICEtaFInst PCUICEtaJoinSpec PCUICEtaCanonSpec PCUICEtaFInstSpec PCUICClosedBodies.

(** ** The pinned restatement *)

Definition JoinE {cf : checker_flags} (r : finst_construct_rule) (Σ : global_env_ext)
  (Γ : context) (pb : conv_pb) (t u : term) : Type :=
  ∑ v v', clos_refl_trans (union (R_c Σ Γ) eta1) (canon t) v ×
          clos_refl_trans (union (R_c Σ Γ) eta1) (canon u) v' ×
          eq_term_upto_univ_eta_napp r Σ.1 (compare_universe Σ) (compare_sort Σ) pb 0 v v'.

Definition I5_statement {cf : checker_flags} (r : finst_construct_rule) (Σ : global_env_ext) : Type :=
  forall Γ pb t u,
    is_closed_context Γ -> is_open_term Γ t -> is_open_term Γ u ->
    (Σ ;;; Γ ⊢ t ≤sE[pb] u) <~> JoinE r Σ Γ pb t u.

(** **Obligation 9's premise, pinned as a Definition (lane lead's ruling).** The
    [cumul_eta_l] case of A2 (spec ⇒ join): from the induction hypothesis on
    [cumul_eta_l]'s premise ([PCUICCumulativitySpecEta.v:168-170]) to the join of
    the conclusion. Its exact statement and proof route are in
    [lanes/eta/obligation9-probe.md]. *)
Definition I5_eta_l_case {cf : checker_flags} (r : finst_construct_rule) (Σ : global_env_ext) : Type :=
  forall Γ pb na A t u,
    is_closed_context Γ ->
    is_open_term Γ (tLambda na A t) -> is_open_term Γ u ->
    JoinE r Σ (Γ ,, vass na A) Conv t (tApp (lift0 1 u) (tRel 0)) ->
    JoinE r Σ Γ pb (tLambda na A t) u.

(** ** A4: join ⇒ spec *)

Section A4.

  Context {cf : checker_flags} (Σ : global_env_ext) (wfΣ : ClosedBodies Σ.1) (r : finst_construct_rule).

  Lemma red1_open Γ x y : is_closed_context Γ -> red1 Σ Γ x y -> is_open_term Γ x -> is_open_term Γ y.
  Proof.
    intros hΓ hr hx. eapply (beta_eta_is_open_term (wfΣ := wfΣ)); [exact hΓ| |exact hx].
    apply rt_step. left. exact hr.
  Qed.

  (** One step of the join, in the spec, with the target scoped. *)
  Lemma join_step_spec Γ a b :
    is_closed_context Γ -> is_open_term Γ a -> union (R_c Σ Γ) eta1 a b ->
    (Σ ;;; Γ ⊢ a ≤sE[Conv] b) × is_open_term Γ b.
  Proof.
    intros hΓ ha [[b0 [hr ->]]|he].
    - have hb0 : is_open_term Γ b0 := red1_open Γ a b0 hΓ hr ha.
      split; [|exact (canon_is_open_term Γ b0 hb0)].
      eapply cumulE_Trans with (u := b0); [exact hΓ|exact hb0| |].
      + exact (red1_cumulSpecE Σ Γ a b0 hr).
      + exact (canon_cumulSpecE Σ b0 Γ hΓ hb0).
    - split; [exact (eta1_cumulSpecE Σ a b he Γ)|exact (eta1_on_free_vars a b he _ ha)].
  Qed.

  Lemma join_star_spec Γ a b :
    is_closed_context Γ -> is_open_term Γ a -> clos_refl_trans (union (R_c Σ Γ) eta1) a b ->
    (Σ ;;; Γ ⊢ a ≤sE[Conv] b) × is_open_term Γ b.
  Proof.
    intros hΓ ha h. apply clos_rt_rt1n_iff in h.
    induction h as [a|a a1 b hs _ IH]; [split; [reflexivity|exact ha]|].
    destruct (join_step_spec Γ a a1 hΓ ha hs) as [h1 ha1].
    destruct (IH ha1) as [h2 hb].
    split; [|exact hb].
    eapply cumulE_Trans with (u := a1); [exact hΓ|exact ha1|exact h1|exact h2].
  Qed.

  (** **A4, in full.** *)
  Theorem I5_join_to_spec Γ pb t u :
    is_closed_context Γ -> is_open_term Γ t -> is_open_term Γ u ->
    JoinE r Σ Γ pb t u -> Σ ;;; Γ ⊢ t ≤sE[pb] u.
  Proof.
    intros hΓ ht hu (v & v' & hv & hv' & hcmp).
    have hct : is_open_term Γ (canon t) := canon_is_open_term Γ t ht.
    have hcu : is_open_term Γ (canon u) := canon_is_open_term Γ u hu.
    destruct (join_star_spec Γ _ _ hΓ hct hv) as [sv hvo].
    destruct (join_star_spec Γ _ _ hΓ hcu hv') as [sv' hvo'].
    (* t ≤ canon t ≤ v ≤[pb] v' ≤ canon u ≤ u *)
    eapply cumulE_Trans with (u := canon t); [exact hΓ|exact hct| |].
    { apply convSpecE_cumulSpecE. exact (canon_cumulSpecE Σ t Γ hΓ ht). }
    eapply cumulE_Trans with (u := v); [exact hΓ|exact hvo| |].
    { apply convSpecE_cumulSpecE. exact sv. }
    eapply cumulE_Trans with (u := v'); [exact hΓ|exact hvo'| |].
    { exact (compare_term_eta_cumulSpecE Σ wfΣ r Γ pb v v' hΓ hvo hvo' hcmp). }
    eapply cumulE_Trans with (u := canon u); [exact hΓ|exact hcu| |].
    { apply cumulE_Sym. exact sv'. }
    apply cumulE_Sym. exact (canon_cumulSpecE Σ u Γ hΓ hu).
  Qed.

End A4.
