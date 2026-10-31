(* Distributed under the terms of the MIT license. *)

(* NONDEGEN tags: an INSTANCE NONDEGEN tag is a reader judgment backed by a compiled nontriviality
   lemma, not a mechanical guarantee.
   Measured reader miss rate, a FLOOR (a ruling made after 2026-10-31T09:00Z can only raise it): at least 24 of 60 instances sampled (seed 202610301905) from the 323 that the focused review of 11092806 had not covered (40.0%, 95% upper bound 51.4%, one-sided Clopper-Pearson): 17 from the union of the verdicts held by two independent reviews (Opus 5: 10; Opus 5.5: 15, 6 of its verdicts borderline at confidence 0.5-0.6), plus seven further rows that both reviews had passed and root rulings made between 2026-10-31T01:29Z and 05:41Z reclassified under the same standard (S12, S13, S19, S31, S36, S51, S57), which raised the count from at least 17 to at least 24. 22 of the 24 are false NONDEGEN tags (22 of the 52 sampled NONDEGEN instances, 42.3%); 2 are false prose under a correct tag. All 24 are corrected at frac/eta 6978492e, but the sample estimates the rate over ALL instance tags: a comparable share of the unsampled instances is expected to be wrong and is NOT corrected.
   P4 at frac/eta 6978492e: 313 lemmas with a base twin are accounted for: 208 have at least one NONDEGEN instance, 83 are undemonstrable by their own statements (IMPOSSIBLE-only), and 22 have no working instance (NOT-BUILT-only): BDStrengtheningEta.on_free_vars_typeE; BDToPCUICEta.wf_rel_weakE; PCUICAlphaEta.eq_context_conversionE, isType_eq_context_conversionE, typing_alpha_propE, wf_local_alphaE; PCUICClassificationEta.eval_whneE, fix_app_is_constructorE, invert_cumul_arity_lE, invert_cumul_arity_l_genE, invert_cumul_arity_rE, invert_cumul_arity_r_genE, isArity_typing_spineE, typing_cofix_coindE, value_whnfE, wf_cofixpoint_spineE, wf_fixpoint_spineE; PCUICInversionEta.into_ws_cumulE; PCUICSREta.prim_app_typing_invE, sr_prim_opE, typing_spine_prim_arg_typesE, typing_spine_prim_argsE. No NONDEGEN tag at frac/eta 6978492e is judged false by a root ruling made by 2026-10-31T09:00Z. The 208 is a CEILING, not a count of sound demonstrations: every root ruling made between 2026-10-31T01:29Z and 07:30Z that re-examined NONDEGEN tags in place found more false ones (the next, at 08:29Z, judged its one row weak, not false); retags from those rulings moved 25 targets out between frac/eta c825ec02 (229) and 6978492e, and rebuilt instances moved 4 in. The miss rate above (a floor) and this ceiling measure the same thing two ways. Combined at frac/eta 6978492e (the sample's false-tag rate, 22 of 52, applied to every NONDEGEN instance outside the sample, including the 36 that root rulings judged sound; the instances of one file counted as one cluster), they give an expected 131 of the 208 with at least one sound instance, 90% interval 89 to 170; about 77 of the 208 are expected to have none. Corrections pull in both directions (90% intervals with the rate fixed): counting the 36 root-judged instances as sound gives 147 (137 to 156); the 38 false instances found in the sampled frame outside the sample, between the sample's head 39ff4f31 and frac/eta 6978492e, lower the rate that remains, giving 143 (133 to 154); and sampled rows judged sound are not certain (S12, S13, S19, S31, S36, S51 and S57 were each passed by both reviews and judged false), which gives 127 (115 to 138). Context of the 208 (context = a judgment argument of type list (context_decl term), empty or not by computing its length, not the lemma's Γ parameter): 84 use a non-empty context (in 2 of them, typing_eq_termE and typing_leq_termE, it occurs but does no work); 23 have the context as their subject; 19 have a non-empty context that no term or type mentions; 4 undecided; 58 work only at the empty context (7 forced by the statement, 51 by the instance's choice; up to 77 under stricter readings); 20 have no context argument, which is not the same as the empty context. A mechanical detector run over all 413 instances at frac/eta 2e26fc93 (does an input sub-derivation inhabit the conclusion, at any depth and through squash, existential and pair packages; does the conclusion close by computation alone) finds 30 of the 56 blocks (53 instances) that root rulings had judged false, 11 of the 22 such tags in the sample; it finds none of the reflexive-step, identity-only or translation cases and 7 of 16 round trips (it cannot see a round trip inside the target lemma's own proof), and on closed equations it flags every row, sound or not; root rulings made by 2026-10-31T08:29Z judged its 20 flags on unruled NONDEGEN tags (8 false). A first mechanical sweep flagged at least 31 of the 338 NONDEGEN instances at 0bf9899a, before the tag changes of LAND8a (eede40b7, 86d983ce), LAND9 (016ec167, 727d49e9), LAND11-A (6568a017), LAND12 (07786120, e2c9c6b2), LAND13-A (af1fa399), LAND10 (fc8627b8), GAMMA9 (1f0c66a6, 201d23cc) and LAND13-C (46b62a8a to 8c0b7bcd), whose conclusion is convertible to an input sub-derivation (3 of the 31 match the instance itself or its helper rather than an input); all 31 were judged by 2026-10-31T08:29Z: its 9 non-equation flags 9 bad, with the kind-label correct in 6 of 9; its 22 closed-equation flags, which it cannot discriminate, 10 bad, 4 weak only, 8 not degenerate. Prose overclaims were not mechanically enumerated, because that detector failed its controls. The 45-row marker census had 2 reopened as of 2026-10-31T03:30Z. *)

(** * Satisfying instance of [PCUICConsistencyEta.pcuic_consistentE]

  **The environment** [cs_Σ] declares base's [False_mib] ([Inductive False : Prop :=], no
  parameter, no constructor) under the name [cs_kn]; [cs_wf] proves it well-formed for base
  typing, [cs_wfext] for the η typing ([wf_incl_E]), [cs_axiom_free] proves it has no axiom, and
  [cs_declared_False] that [False_mib] is declared there. The checking environment of the
  declaration is base's empty one, so the typing lemmas of [PCUICCumulativitySpecEtaClosureInstances]
  for [si_Σ0] are reused. [cs_False_typed] shows that the type of the theorem's typing premise,
  [tInd cs_ind []], is a well-typed type ([: Prop]) in [cs_Σ], so the premise is not ill-formed.

  **Section variables.** Base's normalization premise [NormalizationInE cs_Σ] only: unprovable by
  design (strong normalization, [PCUICSNEta]'s header), a premise of base's [pcuic_consistent]
  too, never discharged. (The forecast class [CanonForecastCopy20] of [PCUICCanonicityEta] was a
  second section variable; the class is deleted.)

  **Non-degeneracy.** [pcuic_consistentE_inst] discharges every premise of the theorem on the
  concrete [cs_Σ] except two: the normalization premise (above) and the typing premise
  [cs_Σ ;;; [] |-E t : tInd cs_ind []]. Its tag records why the instance is IMPOSSIBLE to make
  non-degenerate: the theorem's conclusion is [False]. *)

From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICArityRed PCUICSN
     PCUICClassification PCUICConsistency PCUICTypingEta PCUICCumulativitySpecEtaClosureInstances
     PCUICSNEta PCUICValidityEta PCUICSREta PCUICClassificationEta PCUICCanonicityEta
     PCUICConsistencyEta.

(* The environment and its derivations, used by the instance below.
   WITNESSES: cs_* *)

#[local] Existing Instance default_checker_flags.

(** ** The environment *)

Definition cs_kn : kername := (MPfile ["CsInst"], "False").
Definition cs_ind : inductive := {| inductive_mind := cs_kn; inductive_ind := 0 |}.

Definition cs_env : global_env :=
  {| universes := ContextSet.empty; declarations := [(cs_kn, InductiveDecl False_mib)];
     retroknowledge := Retroknowledge.empty |}.

Definition cs_Σ : global_env_ext := (cs_env, Monomorphic_ctx).

(** [False_oib] in the empty environment [si_Σ0]: [Prop] is its arity, no constructor. *)
Lemma cs_on_ind_body :
  on_ind_body cumulSpec0 (lift_typing typing) si_Σ0 cs_kn False_mib 0 False_oib.
Proof.
  unshelve econstructor.
  - exact [].
  - exists (tSort sProp). split; [reflexivity|].
    apply arity_red_sort. apply whd_stop. reflexivity.
  - exact (si_vass _ (mkBindAnn nAnon rel_of_Type) _ _ (si_P_typed [] si_wf_nil) eq_refl).
  - exact (si_vass _ (mkBindAnn nAnon rel_of_Type) _ _ (si_P_typed [] si_wf_nil) eq_refl).
  - constructor.
  - exact I.
  - reflexivity.
  - reflexivity.
  - exact I.
Qed.

Lemma cs_on_inductive : on_inductive cumulSpec0 (lift_typing typing) si_Σ0 cs_kn False_mib.
Proof.
  constructor.
  - constructor; [exact cs_on_ind_body|constructor].
  - exact si_wf_nil.
  - reflexivity.
  - reflexivity.
Qed.

Lemma cs_wf : wf cs_env.
Proof.
  split.
  - split; [|split].
    + intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
    + intros x Hx.
      change (LevelSet.In x (LevelSet.union (ContextSet.levels ContextSet.empty)
                                            (LevelSet.singleton Level.lzero))) in Hx.
      apply LevelSet.union_spec in Hx as [Hx|Hx].
      * exfalso. eapply LevelSet.empty_spec. exact Hx.
      * apply LevelSet.singleton_spec in Hx. hnf in Hx. subst x. reflexivity.
    + exists si_val. intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
  - split.
    { constructor; cbn; [constructor|intros c []|repeat split; intros c h; discriminate h
                        |intros i h; discriminate h]. }
    apply globenv_decl; [constructor|].
    constructor.
    + constructor.
    + exact si_on_udecl.
    + exact cs_on_inductive.
    + cbn. intros i h; discriminate h.
Qed.

Definition cs_wfE : wfE cs_env := wf_incl_E cs_wf.
Definition cs_wfext : wf_extE cs_Σ := (cs_wfE, si_on_udecl).

Lemma cs_axiom_free : axiom_free cs_Σ.
Proof.
  intros c decl h. exfalso. red in h. cbn in h.
  destruct h as [h|h]; [discriminate h|exact h].
Qed.

Lemma cs_declared_False : declared_inductive cs_Σ cs_ind False_mib False_oib.
Proof. split; [left; reflexivity|reflexivity]. Qed.

(** The type of the typing premise is a type: [False : Prop] in [cs_Σ]. *)
Lemma cs_False_typed : cs_Σ ;;; [] |-E tInd cs_ind [] : tSort sProp.
Proof. exact (typeE_Ind _ _ cs_ind [] False_mib False_oib localenv_nil cs_declared_False eq_refl). Qed.

(** ** The theorem, applied in a section that holds the normalization premise *)

Section ConsistencyEtaInstances.

(* Base's normalization premise (by design, never discharged). *)
Context {nor : normalizing_flags} {nin : NormalizationInE cs_Σ}.

(** The theorem refutes the typing premise for every [t].
    INSTANCE IMPOSSIBLE: the conclusion of pcuic_consistentE is False (no closed term has type tInd cs_ind [], the False_mib of the axiom-free cs_Σ); the instance applies it to every t, its typing premise cs_Σ ;;; [] |-E t : tInd cs_ind [] left as a hypothesis. *)
Definition pcuic_consistentE_inst : forall t, cs_Σ ;;; [] |-E t : tInd cs_ind [] -> False :=
  fun t => pcuic_consistentE cs_Σ t cs_ind cs_declared_False cs_wfext cs_axiom_free.

End ConsistencyEtaInstances.
