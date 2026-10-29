(* Distributed under the terms of the MIT license. *)

(** * The [cumul_eta_l] case of A2, and I5 in full

    [I5_eta_l_case_holds] : I5_eta_l_case Σ
    [I5_FollowKernel]     : I5_statement Σ

  The case: from a join of [t] and [(↑u) (tRel 0)] in [Γ ,, vass na A], a join of
  [λ na:A. t] and [u] in [Γ].

  ** (F), the factorisation, first ([eta_app_factor])

  A chain [(↑ cu) (tRel 0) ⇝* w] of [R_c ∪ eta1] steps in [Γ ,, vass na A], from
  a canonical scoped [cu], is either
  - (A) [w = (↑ x') (tRel 0)] with [cu ⇝* x'] in [Γ], or
  - (B) [cu ⇝* λ_:S. b] in [Γ] and [b ⇝* w] in [Γ ,, vass na A].
  One step from [(↑ x) (tRel 0)] ([eta_app_step]):
  - [app_red_l]: [red1_strengthening] gives the step from [x];
  - [red_beta]: [x = λ_:S. b] (canonical), contractum [(lift 1 1 b){0 := tRel 0} = b];
  - [red_fix]: the recursive argument is not the [tRel 0]
    ([is_constructor_app_tRel0]), so the fix already unfolds on [↑ x], and that is
    a step of [x] by strengthening;
  - [app_red_r]: none, [tRel 0] is an assumption;
  - [eta1]: only inside [↑ x], and [eta1_lift_inv] gives the step from [x].

  ** Cases
  - (A): [v ≈[Conv,0] (↑ x') (tRel 0)] forces [v = (↑ m') (tRel 0)] with
    [x' ≈ m'] ([finst_eta_root]); the left side then η-contracts to [m'].
  - (B): both sides end in a λ; [eqη_Lambda].

  **The hypotheses are satisfiable:** [ClosedBodies Σ], which every well-formed environment satisfies
  ([wf_ClosedBodies]; [wfE_ClosedBodies] for [wfE]).
  [I5_FollowKernel] has no other premise. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst
     PCUICEquality PCUICReduction PCUICOnFreeVars PCUICTyping
     PCUICCumulativitySpecEta
     PCUICEtaDefs PCUICEtaScope PCUICEtaCanon PCUICEtaCanonRed PCUICEtaCanonEta
     PCUICEtaStrengthening PCUICEtaFInst PCUICEtaFInstEquiv PCUICEtaFInstC1c
     PCUICEtaFInstEtaC1c PCUICEtaI5 PCUICEtaI5Trans PCUICEtaI5A2 PCUICClosedBodies.
From MetaRocq.PCUIC Require PCUICEtaC3BR PCUICEtaU8.

Lemma eta1_tRel_absurd n v : eta1 (tRel n) v -> False.
Proof.
  intros h. remember (tRel n) as w eqn:Hw. destruct h; discriminate Hw.
Qed.

Lemma closed_ctx_xpredT (Γ : context) : is_closed_context Γ -> on_ctx_free_vars xpredT Γ.
Proof. intros h. exact (on_free_vars_ctx_on_ctx_free_vars_xpredT h). Qed.

Lemma open_xpredT (Γ : context) t : is_open_term Γ t -> on_free_vars xpredT t.
Proof. intros h. eapply on_free_vars_impl; [|exact h]. done. Qed.

Section EtaL.

  Context {cf : checker_flags} (Σ : global_env_ext) (wfΣ : ClosedBodies Σ).

  Local Notation cu := (compare_universe Σ).
  Local Notation cs := (compare_sort Σ).
  Local Notation RF pb n := (eq_term_upto_univ_eta_napp Σ.1 cu cs pb n).
  Local Notation RE Γ := (union (R_c Σ Γ) eta1).
  Local Notation J Γ pb := (JoinE Σ Γ pb).
  Local Notation BE Γ := (clos_refl_trans (be_step Σ Γ)).

  Lemma RE_canonical Γ x y : canon x = x -> RE Γ x y -> canon y = y.
  Proof.
    intros cx [[y0 [_ ->]]|he]; [apply canon_idem|exact (eta1_canonical x y cx he)].
  Qed.

  (** ** One step from [(↑ x) (tRel 0)] *)
  Lemma eta_app_step Γ na A x s :
    is_closed_context Γ -> is_open_term Γ x -> canon x = x ->
    RE (Γ ,, vass na A) (tApp (lift0 1 x) (tRel 0)) s ->
    (∑ x', RE Γ x x' × s = tApp (lift0 1 x') (tRel 0)) +
    (∑ b, (x = tLambda canon_la canon_dom b) × (s = b)).
  Proof.
    intros hΓ hx cx [[y0 [hr ->]]|he].
    - destruct (PCUICEtaC3BR.C3R.red1_eta_body_inv hr)
        as [[(N1 & -> & hN)|(nb & B & b & hl & ->)]|(mfix & idx & args & narg & fn & hf & hu & hc & ->)].
      + (* inside the function part *)
        destruct (@red1_strengthening cf Σ wfΣ Γ (vass na A) x N1 (closed_ctx_xpredT Γ hΓ) (open_xpredT Γ x hx) hN)
          as (x1 & -> & hx1).
        left. exists (canon x1). split; [left; exists x1; split; [exact hx1|reflexivity]|].
        cbn [canon]. now rewrite canon_lift.
      + (* head β: the function part is a canonical λ *)
        destruct (PCUICEtaC3BR.C3R.lift_tLambda_inv _ _ _ _ _ _ hl) as (B0 & b0 & -> & _ & ->).
        right. exists b0. rewrite PCUICEtaC3BR.C3R.subst_rel0_lift_id0.
        cbn [canon] in cx. injection cx as e1 e2 e3. rewrite -e1 -e2.
        split; [reflexivity|exact e3].
      + (* fix: its recursive argument is in the real spine *)
        assert (hsplit : ∑ args', (args = args' ++ [tRel 0]) × (mkApps (tFix mfix idx) args' = lift0 1 x)).
        { clear hc. induction args as [|a args' _] using rev_ind; [cbn in hf; discriminate hf|].
          rewrite mkApps_app in hf. cbn in hf. injection hf as e1 e2. subst a.
          exists args'. split; [reflexivity|exact e1]. }
        destruct hsplit as (args' & -> & e).
        have hlt := PCUICEtaC3BR.C3R.is_constructor_app_tRel0 narg args' hc.
        rewrite (PCUICEtaC3BR.C3R.is_constructor_app_lt narg args' [tRel 0] hlt) in hc.
        have hred : red1 Σ (Γ ,, vass na A) (lift0 1 x) (mkApps fn args').
        { rewrite -e. exact (red_fix _ _ mfix idx args' narg fn hu hc). }
        destruct (@red1_strengthening cf Σ wfΣ Γ (vass na A) x _ (closed_ctx_xpredT Γ hΓ) (open_xpredT Γ x hx) hred)
          as (x1 & e1 & hx1).
        left. exists (canon x1). split; [left; exists x1; split; [exact hx1|reflexivity]|].
        rewrite mkApps_app /= e1. cbn [canon]. now rewrite canon_lift.
    - (* η: only inside the function part *)
      left. remember (tApp (lift0 1 x) (tRel 0)) as w eqn:Hw.
      destruct he; try discriminate Hw.
      + injection Hw as e1 e2. subst M2.
        destruct (PCUICEtaU8.eta1_lift_inv 1 M1 N1 he 0 x e1) as (N & hN & ->).
        exists N. split; [right; exact hN|reflexivity].
      + injection Hw as e1 e2. subst M2. exfalso. exact (eta1_tRel_absurd 0 N2 he).
  Qed.

  (** ** (F) *)
  Lemma eta_app_factor Γ na A x w :
    is_closed_context Γ -> is_open_term Γ x -> canon x = x ->
    clos_refl_trans (RE (Γ ,, vass na A)) (tApp (lift0 1 x) (tRel 0)) w ->
    (∑ x', clos_refl_trans (RE Γ) x x' × (w = tApp (lift0 1 x') (tRel 0))) +
    (∑ b, clos_refl_trans (RE Γ) x (tLambda canon_la canon_dom b) × clos_refl_trans (RE (Γ ,, vass na A)) b w).
  Proof.
    intros hΓ hx cx h. apply clos_rt_rt1n_iff in h.
    remember (tApp (lift0 1 x) (tRel 0)) as s eqn:Hs.
    revert x hx cx Hs. induction h as [s|s s1 w hs hrest IH]; intros x hx cx ->.
    - left. exists x. split; [apply rt_refl|reflexivity].
    - destruct (eta_app_step Γ na A x s1 hΓ hx cx hs) as [(x1 & hx1 & ->)|(b & -> & ->)].
      + have hx1o : is_open_term Γ x1 := step_open Σ wfΣ Γ x x1 hΓ hx hx1.
        have cx1 : canon x1 = x1 := RE_canonical Γ x x1 cx hx1.
        destruct (IH x1 hx1o cx1 eq_refl) as [(x' & hx' & ->)|(b & hb & hbw)].
        * left. exists x'. split; [eapply rt_trans; [apply rt_step; exact hx1|exact hx']|reflexivity].
        * right. exists b. split; [eapply rt_trans; [apply rt_step; exact hx1|exact hb]|exact hbw].
      + right. exists b. split; [apply rt_refl|]. apply clos_rt_rt1n_iff. exact hrest.
  Qed.

  (** ** The [cumul_eta_l] case *)
  Theorem I5_eta_l_case_holds : I5_eta_l_case Σ.
  Proof.
    intros Γ pb na A t u hΓ hl hu hj.
    move: (hl). cbn [on_free_vars]. move/andP => [hA ht].
    destruct hj as (v & v' & hv & hv' & e).
    cbn [canon] in hv'. rewrite canon_lift in hv'.
    have hcu : is_open_term Γ (canon u) := canon_is_open_term Γ u hu.
    have hbv : BE (Γ ,, vass na A) t v.
    { eapply rt_trans; [apply BE_canon|exact (RE_BE Σ _ _ _ hv)]. }
    have hleft : forall z, BE (Γ ,, vass na A) t z -> BE Γ (tLambda na A t) (tLambda na A z).
    { intros z hz. eapply (BE_map Σ (Γ ,, vass na A) Γ (tLambda na A)); [| | |exact hz].
      - intros a b s. exact (abs_red_r _ _ na a b A s).
      - intros a b s. exact (abs_eta_r na a b A s).
      - intros a b ec. cbn [canon]. now rewrite ec. }
    have hright : forall z, clos_refl_trans (RE Γ) (canon u) z -> BE Γ u z.
    { intros z hz. eapply rt_trans; [apply BE_canon|exact (RE_BE Σ _ _ _ hz)]. }
    destruct (eta_app_factor Γ na A (canon u) v' hΓ hcu (canon_idem u) hv')
      as [(x' & hx' & ->)|(b & hb & hbw)].
    - (* (A): the left side is an η-redex at the end *)
      depelim e.
      match goal with
      | e1 : eq_term_upto_univ_eta_napp _ _ _ Conv 1 ?v1 (lift0 1 x'),
        e2 : eq_term_upto_univ_eta_napp _ _ _ Conv 0 ?v2 (tRel 0) |- _ =>
          rename e1 into ef; rename e2 into ea
      end.
      depelim ea.
      have hx'o : is_open_term Γ x' := star_open Σ wfΣ Γ _ _ hΓ hcu hx'.
      destruct (finst_eta_root Σ.1 cu cs _ Conv 0 x' _ (fun _ _ h => h) (fun _ _ h => h) hx'o
                  (compare_term_eta_sym Σ.1 Σ 1 _ _ ef)) as (m' & -> & em).
      apply (BE_JoinE Σ Γ pb _ _ m' x').
      + eapply rt_trans; [exact (hleft _ hbv)|].
        apply rt_step; left; right. exact (eta_red na m' A).
      + exact (hright _ hx').
      + apply (RF_canon Σ).
        exact (finst_term_Conv_pb Σ.1 cu cs Conv 0 m' x' (compare_term_eta_sym Σ.1 Σ 0 _ _ em) eq_refl
                 pb 0 (a3_sub_u Σ pb) (a3_sub_s Σ pb)).
    - (* (B): both sides end in a canonical λ *)
      apply (BE_JoinE Σ Γ pb _ _ (tLambda na A v) (tLambda canon_la canon_dom v')).
      + exact (hleft _ hbv).
      + eapply rt_trans; [exact (hright _ hb)|].
        apply (BE_map Σ (Γ ,, vass canon_la canon_dom) Γ (tLambda canon_la canon_dom)).
        * intros a c s. exact (abs_red_r _ _ canon_la a c canon_dom s).
        * intros a c s. exact (abs_eta_r canon_la a c canon_dom s).
        * intros a c ec. cbn [canon]. now rewrite ec.
        * exact (BE_ctx Σ _ _ _ _ (bodies_vass Γ na canon_la A canon_dom) (RE_BE Σ _ _ _ hbw)).
      + cbn [canon]. constructor; [apply eq_binder_annot_refl'|apply (RF_refl Σ)|exact (RF_canon Σ _ _ _ _ e)].
  Qed.

End EtaL.

(** ** I5 in full, at the kernel's constructor rule

  **The hypotheses are satisfiable:** [ClosedBodies Σ], which every well-formed environment satisfies
  ([wf_ClosedBodies]; [wfE_ClosedBodies] for [wfE]); the statement's own
  scoping premises by any scoped pair. *)
Theorem I5_FollowKernel {cf : checker_flags} (Σ : global_env_ext) (wfΣ : ClosedBodies Σ) :
  I5_statement Σ.
Proof. exact (I5_obligation8_FollowKernel Σ wfΣ (I5_eta_l_case_holds Σ wfΣ)). Qed.
