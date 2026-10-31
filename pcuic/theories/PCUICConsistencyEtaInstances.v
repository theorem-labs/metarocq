(* Distributed under the terms of the MIT license. *)

(* NONDEGEN tags: an INSTANCE NONDEGEN tag is a reader judgment backed by a compiled nontriviality
   lemma, not a mechanical guarantee.
   Measured reader miss rate: at least 19 of 60 instances sampled (seed 202610301905) from the 323 that an earlier focused review had not covered (31.7%, 95% upper bound 42.9%, one-sided Clopper-Pearson): 17 from the union of the verdicts held by two independent reviews (Opus 5: 10; Opus 5.5: 15, 6 of its verdicts borderline at confidence 0.5-0.6), plus two further rows that both reviews had passed and later root rulings reclassified under the same standard (S12, S36). 18 of the 19 sampled misses are corrected at this head (S36 is not yet), but the sample estimates the rate over ALL instance tags: a comparable share of the unsampled instances is expected to be wrong and is NOT corrected.
   P4 at this head: 313 lemmas with a base twin are accounted for: 229 demonstrated (at least one NONDEGEN instance; this count still includes 2 targets whose only NONDEGEN instance is already judged false and not yet corrected: PCUICClassificationEta.wf_fixpoint_spineE and wf_cofixpoint_spineE), 70 undemonstrable by their own statements (IMPOSSIBLE-only), and 14 with no working instance (NOT-BUILT-only): BDToPCUICEta.wf_rel_weakE; PCUICAlphaEta.eq_context_conversionE, isType_eq_context_conversionE, typing_alpha_propE, wf_local_alphaE; PCUICClassificationEta.typing_spine_nth_errorE, typing_spine_nth_error_NoneE, typing_spine_nth_error_None_prodE (non-degenerate instances of these 3 are built and under review, not yet landed); PCUICInversionEta.into_ws_cumulE; PCUICPrincipalityEta.typing_leq_termE; PCUICSREta.prim_app_typing_invE, sr_prim_opE, typing_spine_prim_arg_typesE, typing_spine_prim_argsE. The demonstrated count rests on NONDEGEN tags with the measured miss rate above. As of 2026-10-31T02:35Z, 11 NONDEGEN tags are judged false and not yet corrected, all conv → red cases whose input conversion was built from a reduction (for wf_fixpoint_spineE_inst the conv → red step sits inside its target's proof): 7 in BDFromPCUICEtaInstances (red_fix_witnessE_inst, mfix_body_on_conv_redE_fix_inst, red_cofix_witnessE_inst, mfix_body_on_conv_redE_cofix_inst, mfix_on_ind_conv_redE_cofix_inst, wf_fixpointE_wf_fixpoint_red_typed_inst, and sampled row S36 = wf_cofixpointE_wf_cofixpoint_red_inst) and PCUICPrincipalityEtaInstances.T8_Prod_l_plug_inst and T8_Prod_l_of_r_inst, whose targets are outside P4's input set, and PCUICClassificationEtaInstances.wf_fixpoint_spineE_inst and wf_cofixpoint_spineE_inst, whose targets are the 2 above. Context of the demonstrations (context = a judgment argument of type list (context_decl term), empty or not by computing its length, not the lemma's Γ parameter): 79 use a non-empty context; 23 have the context as their subject; 20 have a non-empty context that no term or type mentions; 4 undecided; 70 work only at the empty context (10 forced by the statement, 60 by the instance's choice; up to 89 under stricter readings); 33 have no context argument, which is not the same as the empty context. A mechanical sweep flagged at least 31 of the 338 NONDEGEN instances at 0bf9899a, before the later retags, whose conclusion is convertible to an input sub-derivation (3 of the 31 match the instance itself or its helper rather than an input); of its 9 non-equation flags, 9 were judged bad, with the kind-label correct in 6 of 9; it cannot see a cancellation inside the target lemma's own proof or a conclusion that is one part of a pair, and it does not discriminate the 22 closed equations. Prose overclaims were not mechanically enumerated, because that detector failed its controls. Later root rulings reclassified two sampled rows that both reviews had passed, S36 (the red → conv → red class) and S12 (its conclusion is the input's own cumulativity), raising the sampled rate from at least 17 to at least 19 of 60; the 45-row marker census stayed at 2 reopened. *)

(** * Satisfying instance of [PCUICConsistencyEta.pcuic_consistentE] (row T9)

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
  second section variable until copy 20 (bfe54de2) and the class was deleted.)

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
