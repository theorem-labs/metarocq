(* Distributed under the terms of the MIT license. *)

(* NONDEGEN tags: an INSTANCE NONDEGEN tag is a reader judgment backed by a compiled nontriviality
   lemma, not a mechanical guarantee.
   Measured reader miss rate: 10 of 60 sampled instances (residual 16.7%, 95% upper bound 26.6%), seed 202610301905, measured on the pre-retag head; H' additionally corrects 10 tags and 7 prose rows that review found false, so the figure is conservative here. *)

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

(** BET-339's premise of [pcuic_consistentE] holds in [cs_Σ]: it has no coinductive block
    ([no_closed_stuck_cofix_case_at_no_cofiniteE], as base's [Σ_False] instance). *)
Lemma cs_no_stuck : no_closed_stuck_cofix_case_atE cs_Σ cs_ind.
Proof.
  apply no_closed_stuck_cofix_case_at_no_cofiniteE.
  intros mind. unfold check_recursivity_kind, lookup_env, cs_Σ, cs_env; cbn.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

(** ** The theorem, applied in a section that holds the normalization premise *)

Section ConsistencyEtaInstances.

(* Base's normalization premise (by design, never discharged). *)
Context {nor : normalizing_flags} {nin : NormalizationInE cs_Σ}.

(** The theorem refutes the typing premise for every [t].
    INSTANCE IMPOSSIBLE: the conclusion of pcuic_consistentE is False (no closed term has type tInd cs_ind [], the False_mib of the axiom-free cs_Σ); the instance applies it to every t, its typing premise cs_Σ ;;; [] |-E t : tInd cs_ind [] left as a hypothesis. *)
Definition pcuic_consistentE_inst : forall t, cs_Σ ;;; [] |-E t : tInd cs_ind [] -> False :=
  fun t => pcuic_consistentE cs_Σ t cs_ind cs_declared_False cs_wfext cs_axiom_free cs_no_stuck.

End ConsistencyEtaInstances.
