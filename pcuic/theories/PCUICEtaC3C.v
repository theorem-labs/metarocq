(* Distributed under the terms of the MIT license. *)
(** * BET-315 eta lane, row C3 (prover C, branch frac/eta-c3-c)

  Hindley strong commutation of one [red1] step with one [eta1] step, modulo
  [upto_domain]:

  [[
  C3_statement :=
    forall Σ (wfΣ : wf Σ) Γ t u v,
      red1 Σ Γ t v -> eta1 t u ->
      ∑ w w', clos_refl (red1 Σ Γ) u w × clos_refl_trans eta1 v w' × upto_domain w w'.
  ]]

  [eta1], [eta1_ind_all], [eta] and [upto_domain] are the SHARED definitions of
  [PCUICEtaDefs] (plan rows U1/U3); this file ports a proof to THOSE, never a
  variant.  The running log of sources read, routes tried, cases closed and cases
  that failed is [lanes/eta/EtaC3C.md].

  Route (prover C): induction on [red1] via [red1_ind_all], inverting [eta1] in
  each case, reusing the *structure* of [origin/eta_postpo]'s [red1_eta1_diamond]
  ([PCUICEtaReduction.v:1471-2198]) but with the one-sided conclusion (≤1 red1 on
  the η side, eta* on the red side).  The four unlocking cases ([red_fix],
  [red_cofix_case], [red_cofix_proj], [red_proj]) come before the congruences. *)

From Stdlib Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Reflect.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICCases
     PCUICLiftSubst PCUICUnivSubst PCUICOnFreeVars PCUICSigmaCalculus
     PCUICReduction PCUICEtaDefs PCUICInduction PCUICTyping.

From Stdlib Require Import ssreflect ssrbool.

Set Default Goal Selector "!".

Implicit Types (cf : checker_flags).

Derive Signature for eta1.
Derive Signature for upto_domain.
Derive Signature for clos_refl.
Derive Signature for clos_refl_trans.

(** ** [upto_domain] is reflexive (plan U1). *)

Lemma upto_domain_refl t : upto_domain t t.
Proof.
  induction t using term_forall_list_ind; try solve [constructor; auto].
  - constructor. induction X; constructor; auto.
  - destruct X as [IHpars [IHctx IHret]]. constructor; auto; try reflexivity.
    + induction IHpars; constructor; auto.
    + induction X0 as [|?? [? ?]]; constructor; auto. split; [reflexivity|assumption].
  - constructor. induction X; constructor; auto. split; [|split]; auto. 1-2:apply p.
  - constructor. induction X; constructor; auto. split; [|split]; auto. 1-2:apply p.
  - destruct p as [? p]; destruct p; cbn in X; try solve [constructor; constructor].
    constructor. destruct X as [hd [hty hval]]. constructor; auto.
    induction hval; constructor; auto.
Qed.

#[global] Instance upto_domain_Reflexive : Reflexive upto_domain := upto_domain_refl.

(** ** The C3 statement (plan §3 row C3). *)

Definition C3_statement {cf : checker_flags} :=
  forall (Σ : global_env) (wfΣ : wf Σ) (Γ : context) (t u v : term),
    red1 Σ Γ t v -> eta1 t u ->
    ∑ w w', clos_refl (red1 Σ Γ) u w × clos_refl_trans eta1 v w' × upto_domain w w'.
