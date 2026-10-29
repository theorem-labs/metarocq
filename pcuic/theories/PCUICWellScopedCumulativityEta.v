(* Distributed under the terms of the MIT license. *)

(** * The well-scoped relation [ws_cumul_pbE]

  The E counterpart of base [ws_cumul_pb] ([PCUICWellScopedCumulativity.v]),
  built on the canonical join [JoinE] ([PCUICEtaI5]):

    [ws_cumul_pbE pb Σ Γ t u] := [Γ] closed, [t] and [u] open in [Γ], and
                                 [JoinE Σ Γ pb t u].

  It is new statements over [JoinE] and the canonical-join results ([PCUICEtaI5]), not a copy of the base file:
  - [_forget] to the unscoped join and to the spec [≤sE];
  - [into_ws_cumul_pbE] from the join, and from the spec ([PCUICEtaI5A2], with
    [I5_eta_l_case_holds]);
  - [ws_cumul_pbE_spec_iff]: the relation is the scoped spec ([I5_join_to_spec], [I5_spec_to_join]);
  - reflexivity, symmetry at [Conv], transitivity ([PCUICEtaI5Trans]), [Conv ⊆ pb];
  - base [ws_cumul_pb ⊆ ws_cumul_pbE] ([cumulAlgo_cumulSpec], [cumulSpec0_incl_E]);
  - the notations [Σ ;;; Γ ⊢E t ≤[pb] u], [Σ ;;; Γ ⊢E t ≤ u] and [Σ ;;; Γ ⊢E t = u],
    the counterparts of base's [⊢] notations for [ws_cumul_pb];
  - closed reduction and closed η steps are in the relation, on either side.

**The hypotheses are satisfiable:** [ClosedBodies Σ] by any well-formed
  environment ([wf_ClosedBodies]; [wfE_ClosedBodies] for [wfE]); the scoping premises by any scoped context and
  terms; each [JoinE]/[ws_cumul_pbE] premise by [t = u] ([ws_cumul_pbE_refl]). *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICEquality PCUICReduction
     PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICWellScopedCumulativity PCUICConversion
     PCUICEtaDefs PCUICEtaScope PCUICEtaCanon PCUICEtaFInst PCUICEtaFInstEquiv
     PCUICEtaI5 PCUICEtaI5Trans PCUICEtaI5A2 PCUICEtaI5EtaL PCUICClosedBodies.

Record ws_cumul_pbE {cf : checker_flags} (pb : conv_pb)
  (Σ : global_env_ext) (Γ : context) (t u : term) : Type :=
  { wsE_ctx : is_closed_context Γ;
    wsE_left : is_open_term Γ t;
    wsE_right : is_open_term Γ u;
    wsE_join : JoinE Σ Γ pb t u }.

Arguments wsE_ctx {cf pb Σ Γ t u}.
Arguments wsE_left {cf pb Σ Γ t u}.
Arguments wsE_right {cf pb Σ Γ t u}.
Arguments wsE_join {cf pb Σ Γ t u}.

Notation " Σ ;;; Γ ⊢E t ≤[ pb ] u " := (ws_cumul_pbE pb Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢E  t  ≤[ pb ]  u") : type_scope.
Notation " Σ ;;; Γ ⊢E t ≤ u " := (ws_cumul_pbE Cumul Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢E  t  ≤  u") : type_scope.
Notation " Σ ;;; Γ ⊢E t = u " := (ws_cumul_pbE Conv Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢E  t  =  u") : type_scope.

(** The E twin of base's [Derive Signature NoConfusion for ws_cumul_pb]
    ([PCUICWellScopedCumulativity.v:50]). Base's relation is a family indexed by the two
    terms; [ws_cumul_pbE] is a record with the terms as parameters, so it has no indices
    and Equations derives no signature for it ("No signature to derive for
    non-dependent inductive types"): only [NoConfusion] has a twin. *)
Derive NoConfusion for ws_cumul_pbE.

#[global] Hint Resolve wsE_ctx wsE_left wsE_right : fvs.

(** ** Joins that need no scoping *)

Section Joins.

  Context {cf : checker_flags} (Σ : global_env_ext).

  Lemma JoinE_refl Γ pb t : JoinE Σ Γ pb t t.
  Proof. now apply JoinE_canon_eq. Qed.

  Lemma BE_red Γ t u : red Σ Γ t u -> clos_refl_trans (be_step Σ Γ) t u.
  Proof.
    induction 1 as [x y s|x|x y z _ IH1 _ IH2].
    - apply rt_step; left; left; exact s.
    - apply rt_refl.
    - eapply rt_trans; eassumption.
  Qed.

  (** A reduction, in either direction, is a join. *)
  Lemma JoinE_red_l Γ pb t u : red Σ Γ t u -> JoinE Σ Γ pb t u.
  Proof.
    intros h. apply (BE_JoinE Σ Γ pb t u u u); [exact (BE_red Γ t u h)|apply rt_refl|apply RF_refl].
  Qed.

  Lemma JoinE_red_r Γ pb t u : red Σ Γ u t -> JoinE Σ Γ pb t u.
  Proof.
    intros h. apply (BE_JoinE Σ Γ pb t u t t); [apply rt_refl|exact (BE_red Γ u t h)|apply RF_refl].
  Qed.

  (** An η step, in either direction, is a join. *)
  Lemma JoinE_eta1_l Γ pb t u : eta1 t u -> JoinE Σ Γ pb t u.
  Proof.
    intros h. apply (BE_JoinE Σ Γ pb t u u u); [apply rt_step; left; right; exact h|apply rt_refl|apply RF_refl].
  Qed.

  Lemma JoinE_eta1_r Γ pb t u : eta1 u t -> JoinE Σ Γ pb t u.
  Proof.
    intros h. apply (BE_JoinE Σ Γ pb t u t t); [apply rt_refl|apply rt_step; left; right; exact h|apply RF_refl].
  Qed.

End Joins.

Section A1.

  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ}.

  (** ** Forgetting the scoping *)

  Lemma ws_cumul_pbE_forget {pb Γ t u} : ws_cumul_pbE pb Σ Γ t u -> JoinE Σ Γ pb t u.
  Proof. intros []; assumption. Qed.

  Lemma ws_cumul_pbE_forget_spec {pb Γ t u} : ws_cumul_pbE pb Σ Γ t u -> Σ ;;; Γ ⊢ t ≤sE[pb] u.
  Proof. intros [hΓ ht hu hj]. exact (I5_join_to_spec Σ wfΣ Γ pb t u hΓ ht hu hj). Qed.

  Lemma ws_cumul_pbE_is_open_term {pb Γ t u} :
    ws_cumul_pbE pb Σ Γ t u -> [&& is_closed_context Γ, is_open_term Γ t & is_open_term Γ u].
  Proof. intros [hΓ ht hu _]. now rewrite hΓ ht hu. Qed.

  (** ** Building the relation *)

  Lemma into_ws_cumul_pbE {pb Γ t u} :
    JoinE Σ Γ pb t u -> is_closed_context Γ -> is_open_term Γ t -> is_open_term Γ u ->
    ws_cumul_pbE pb Σ Γ t u.
  Proof. intros hj hΓ ht hu. now constructor. Qed.

  Lemma into_ws_cumul_pbE_spec {pb Γ t u} :
    Σ ;;; Γ ⊢ t ≤sE[pb] u -> is_closed_context Γ -> is_open_term Γ t -> is_open_term Γ u ->
    ws_cumul_pbE pb Σ Γ t u.
  Proof.
    intros h hΓ ht hu. constructor; try assumption.
    exact (I5_spec_to_join Σ wfΣ (I5_eta_l_case_holds Σ wfΣ) Γ pb t u hΓ ht hu h).
  Qed.

  (** The relation is the scoped spec (I5). *)
  Lemma ws_cumul_pbE_spec_iff {pb Γ t u} :
    ws_cumul_pbE pb Σ Γ t u <~>
    [× is_closed_context Γ, is_open_term Γ t, is_open_term Γ u & Σ ;;; Γ ⊢ t ≤sE[pb] u].
  Proof.
    split.
    - intros h. split; [exact (wsE_ctx h)|exact (wsE_left h)|exact (wsE_right h)|exact (ws_cumul_pbE_forget_spec h)].
    - intros [hΓ ht hu h]. exact (into_ws_cumul_pbE_spec h hΓ ht hu).
  Qed.

  (** The base relation is included (plan I0: base ⊆ E). *)
  Lemma ws_cumul_pb_incl_E {pb Γ t u} : ws_cumul_pb pb Σ Γ t u -> ws_cumul_pbE pb Σ Γ t u.
  Proof.
    intros h. apply into_ws_cumul_pbE_spec.
    - apply cumulSpec0_incl_E. eapply cumulAlgo_cumulSpec. exact h.
    - exact (ws_cumul_pb_is_closed_context_cb h).
    - exact (ws_cumul_pb_is_open_term_left_cb h).
    - exact (ws_cumul_pb_is_open_term_right_cb h).
  Qed.

  (** ** Equivalence-relation structure *)

  Lemma ws_cumul_pbE_refl {pb Γ t} : is_closed_context Γ -> is_open_term Γ t -> ws_cumul_pbE pb Σ Γ t t.
  Proof. intros hΓ ht. constructor; try assumption. apply JoinE_refl. Qed.

  Lemma ws_cumul_pbE_sym_pb {pb Γ t u} : ws_cumul_pbE Conv Σ Γ u t -> ws_cumul_pbE pb Σ Γ t u.
  Proof. intros [hΓ hu ht hj]. constructor; try assumption. exact (JoinE_sym Σ Γ pb t u hj). Qed.

  #[global] Instance ws_cumul_pbE_sym {Γ} : Symmetric (ws_cumul_pbE Conv Σ Γ).
  Proof. intros t u h. exact (ws_cumul_pbE_sym_pb h). Qed.

  (** A3. *)
  #[global] Instance ws_cumul_pbE_trans {pb Γ} : Transitive (ws_cumul_pbE pb Σ Γ).
  Proof.
    intros t u w [hΓ ht hu h1] [_ _ hw h2]. constructor; try assumption.
    exact (I5_join_trans Σ wfΣ Γ pb t u w hΓ hu h1 h2).
  Qed.

  Lemma ws_cumul_eq_pbE {pb Γ t u} : ws_cumul_pbE Conv Σ Γ t u -> ws_cumul_pbE pb Σ Γ t u.
  Proof. intros h. apply ws_cumul_pbE_sym_pb. symmetry. exact h. Qed.

  (** ** Reduction and η *)

  Lemma red_ws_cumul_pbE {pb Γ t u} : Σ ;;; Γ ⊢ t ⇝ u -> ws_cumul_pbE pb Σ Γ t u.
  Proof.
    intros h. constructor; [exact (clrel_ctx h)|exact (clrel_src h)|exact (closed_red_open_right_cb h)|].
    exact (JoinE_red_l Σ Γ pb t u (clrel_rel h)).
  Qed.

  Lemma red_ws_cumul_pbE_inv {pb Γ t u} : Σ ;;; Γ ⊢ t ⇝ u -> ws_cumul_pbE pb Σ Γ u t.
  Proof.
    intros h. constructor; [exact (clrel_ctx h)|exact (closed_red_open_right_cb h)|exact (clrel_src h)|].
    exact (JoinE_red_r Σ Γ pb u t (clrel_rel h)).
  Qed.

  Lemma red_ws_cumul_pbE_left {pb Γ t u v} :
    Σ ;;; Γ ⊢ t ⇝ u -> ws_cumul_pbE pb Σ Γ u v -> ws_cumul_pbE pb Σ Γ t v.
  Proof. intros h1 h2. transitivity u; [exact (red_ws_cumul_pbE h1)|exact h2]. Qed.

  Lemma red_ws_cumul_pbE_right {pb Γ t u v} :
    Σ ;;; Γ ⊢ t ⇝ u -> ws_cumul_pbE pb Σ Γ v u -> ws_cumul_pbE pb Σ Γ v t.
  Proof. intros h1 h2. transitivity u; [exact h2|exact (red_ws_cumul_pbE_inv h1)]. Qed.

  Lemma eta1_ws_cumul_pbE {pb Γ t u} :
    is_closed_context Γ -> is_open_term Γ t -> eta1 t u -> ws_cumul_pbE pb Σ Γ t u.
  Proof.
    intros hΓ ht h. constructor; [exact hΓ|exact ht|exact (eta1_on_free_vars t u h _ ht)|].
    exact (JoinE_eta1_l Σ Γ pb t u h).
  Qed.

  Lemma eta1_ws_cumul_pbE_inv {pb Γ t u} :
    is_closed_context Γ -> is_open_term Γ t -> eta1 t u -> ws_cumul_pbE pb Σ Γ u t.
  Proof.
    intros hΓ ht h. constructor; [exact hΓ|exact (eta1_on_free_vars t u h _ ht)|exact ht|].
    exact (JoinE_eta1_r Σ Γ pb u t h).
  Qed.

End A1.

(** The E twins of base's registrations [PCUICWellScopedCumulativity.v:353] and [:400]. *)
#[global] Hint Immediate ws_cumul_pbE_refl : pcuic.
#[global] Hint Resolve red_ws_cumul_pbE red_ws_cumul_pbE_inv : pcuic.
