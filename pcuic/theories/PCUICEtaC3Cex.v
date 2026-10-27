(* Distributed under the terms of the MIT license. *)

(** * C3 needs [wf Σ]: a mechanised counterexample (BET-315 eta lane, C3Prover1)

  The hardened C3 statement without a [wf Σ] premise,
    is_closed_context Γ -> is_open_term Γ t -> red1 Σ Γ t v -> eta1 t u ->
      ∑ w w', clos_refl (red1 Σ Γ) u w × clos_refl_trans eta1 v w' × upto_domain w w',
  is FALSE. A constant with an OPEN body ([cst_body = Some (tRel 0)]), which a
  well-formed environment forbids, lets [red_delta] destroy an η-redex under its
  binder: [red_delta] does not lift the body.

    Σ  := [c := tRel 0]                     (open body)
    Γ  := []
    t  := λ(na : Sort s). (tConst c u) (tRel 0)    (= eta_redex na (Sort s) (tConst c u))
    v  := λ(na : Sort s). (tRel 0) (tRel 0)        (abs_red_r ∘ app_red_l ∘ red_delta)
    u0 := tConst c u                               (eta_red)

  [u0] reaches only [tConst c u] or [tRel 0]; every η-reduct of [v] is a λ
  (eta_red would need [tRel 0 = lift0 1 _]); [upto_domain] never relates a λ to
  [tConst]/[tRel]. So C3 must carry [wf Σ], exactly as C2's statement did
  (origin/eta_postpo:PCUICEtaReduction.v:1471). This file proves all of that,
  with no assumptions. *)

From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils
     PCUICLiftSubst PCUICCases PCUICReduction PCUICOnFreeVars PCUICEtaDefs.

Import ListNotations.

Set Default Goal Selector "!".

Section C3NeedsWf.
  Context (c : kername) (na : aname) (s : sort) (u : Instance.t).

  Definition cex_body : constant_body :=
    {| cst_type := tSort s; cst_body := Some (tRel 0);
       cst_universes := Monomorphic_ctx; cst_relevance := Relevant |}.

  Definition cex_env : global_env :=
    {| universes := ContextSet.empty;
       declarations := [(c, ConstantDecl cex_body)];
       retroknowledge := Retroknowledge.empty |}.

  Definition cex_t := tLambda na (tSort s) (tApp (tConst c u) (tRel 0)).
  Definition cex_v := tLambda na (tSort s) (tApp (tRel 0) (tRel 0)).

  Lemma cex_scoping : is_closed_context ([] : context)
                      × is_open_term ([] : context) cex_t.
  Proof. split; reflexivity. Qed.

  Lemma cex_red : red1 cex_env [] cex_t cex_v.
  Proof.
    unfold cex_t, cex_v. apply abs_red_r. apply app_red_l.
    exact (red_delta cex_env _ c cex_body (tRel 0) ltac:(now left) u eq_refl).
  Qed.

  Lemma cex_eta : eta1 cex_t (tConst c u).
  Proof. exact (eta_red na (tConst c u) (tSort s)). Qed.

  Lemma lift0_1_not_rel0 x : lift0 1 x <> tRel 0.
  Proof. destruct x; cbn; discriminate. Qed.

  Lemma no_eta1_rel0app y : eta1 (tApp (tRel 0) (tRel 0)) y -> False.
  Proof.
    intro H. remember (tApp (tRel 0) (tRel 0)) as x eqn:Hx.
    destruct H; try discriminate Hx.
    - assert (M1 = tRel 0) as -> by congruence.
      match goal with E : eta1 (tRel 0) _ |- _ => inversion E end.
    - assert (M2 = tRel 0) as -> by congruence.
      match goal with E : eta1 (tRel 0) _ |- _ => inversion E end.
  Qed.

  Lemma cex_eta_inv A y :
    eta1 (tLambda na A (tApp (tRel 0) (tRel 0))) y ->
    ∑ A', y = tLambda na A' (tApp (tRel 0) (tRel 0)).
  Proof.
    intro H. remember (tLambda na A (tApp (tRel 0) (tRel 0))) as x eqn:Hx.
    destruct H; try discriminate Hx.
    - (* eta_red: would need lift0 1 t = tRel 0 *)
      exfalso. apply (lift0_1_not_rel0 t). congruence.
    - (* abs_eta_l: the domain moves *)
      exists M'. congruence.
    - (* abs_eta_r: the body tApp (tRel 0) (tRel 0) has no η step *)
      assert (M = tApp (tRel 0) (tRel 0)) as -> by congruence.
      exfalso. eapply no_eta1_rel0app; eassumption.
  Qed.

  Lemma cex_eta_star x y : clos_refl_trans eta1 x y ->
    forall A, x = tLambda na A (tApp (tRel 0) (tRel 0)) ->
    ∑ A', y = tLambda na A' (tApp (tRel 0) (tRel 0)).
  Proof.
    intro H. apply clos_rt_rt1n_iff in H.
    induction H as [x | x y z r Hrest IH]; intros A0 Heq; subst.
    - now exists A0.
    - destruct (cex_eta_inv _ _ r) as [A1 ->]. now apply (IH A1).
  Qed.

  Lemma cex_red_from_const w :
    clos_refl (red1 cex_env []) (tConst c u) w -> (w = tConst c u) + (w = tRel 0).
  Proof.
    intro H. destruct H as [y Hr|].
    - right. depelim Hr; solve_discr.
      match goal with
      | D : declared_constant _ _ ?d, E : cst_body ?d = Some _ |- _ =>
          cbn in D; destruct D as [D|[]]; noconf D; cbn in E; noconf E
      end.
      reflexivity.
    - left; reflexivity.
  Qed.

  Lemma cex_no_join :
    (∑ w w', clos_refl (red1 cex_env []) (tConst c u) w
           × clos_refl_trans eta1 cex_v w' × upto_domain w w') -> False.
  Proof.
    intros (w & w' & hw & hw' & hu).
    destruct (cex_eta_star _ _ hw' (tSort s) eq_refl) as [A' ->].
    destruct (cex_red_from_const _ hw) as [-> | ->]; inversion hu.
  Qed.

  (** C3 without [wf Σ] is false (for any choice of c, na, s, u). *)
  Theorem C3_without_wf_false :
    (forall (Σ : global_env) (Γ : context) (t u0 v : term),
        is_closed_context Γ -> is_open_term Γ t ->
        red1 Σ Γ t v -> eta1 t u0 ->
        ∑ w w', clos_refl (red1 Σ Γ) u0 w
              × clos_refl_trans eta1 v w' × upto_domain w w') -> False.
  Proof.
    intro C3. apply cex_no_join.
    exact (C3 cex_env [] cex_t (tConst c u) cex_v
              (fst cex_scoping) (snd cex_scoping) cex_red cex_eta).
  Qed.
End C3NeedsWf.

(** A fully concrete instance (no section variables). *)
Definition cex_kn : kername := (MPfile ["EtaC3Cex"%bs], "c"%bs).
Definition cex_na : aname := {| binder_name := nAnon; binder_relevance := Relevant |}.

Theorem C3_without_wf_false_concrete :
  (forall (Σ : global_env) (Γ : context) (t u0 v : term),
      is_closed_context Γ -> is_open_term Γ t ->
      red1 Σ Γ t v -> eta1 t u0 ->
      ∑ w w', clos_refl (red1 Σ Γ) u0 w
            × clos_refl_trans eta1 v w' × upto_domain w w') -> False.
Proof. exact (C3_without_wf_false cex_kn cex_na sProp []). Qed.

Print Assumptions C3_without_wf_false_concrete.
