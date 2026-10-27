(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICTyping PCUICEquality PCUICAst PCUICAstUtils
  PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICGeneration PCUICArities
  PCUICWcbvEval PCUICSR PCUICInversion
  PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
  PCUICElimination PCUICSigmaCalculus PCUICContextConversion
  PCUICUnivSubst PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICCumulativity PCUICConfluence
  PCUICInduction PCUICLiftSubst PCUICContexts PCUICSpine
  PCUICConversion PCUICValidity PCUICInductives PCUICConversion
  PCUICInductiveInversion PCUICNormal PCUICSafeLemmata
  PCUICParallelReductionConfluence
  PCUICWcbvEval PCUICClosed PCUICClosedTyp
  PCUICReduction PCUICCSubst PCUICOnFreeVars PCUICWellScopedCumulativity
  PCUICWcbvEval PCUICClassification PCUICCanonicity PCUICSN PCUICNormalization PCUICViews.

From Equations Require Import Equations.

Definition False_oib : one_inductive_body :=
  {| ind_name := "False";
     ind_indices := [];
     ind_sort := sProp;
     ind_type := tSort sProp;
     ind_kelim := IntoAny;
     ind_ctors := [];
     ind_projs := [];
     ind_relevance := Relevant |}.

Definition False_mib : mutual_inductive_body :=
  {| ind_finite := BiFinite;
     ind_npars := 0;
     ind_params := [];
     ind_bodies := [False_oib];
     ind_universes := Monomorphic_ctx;
     ind_variance := None |}.

(** The one case the proof below cannot close: a closed well-typed term of the empty
    type whose weak-head normal form is a case blocked on a cofixpoint. Rocq's kernel
    types such a match, because its rule for the type of a case makes no coinductivity
    test (kernel/typeops.ml:547-583); its machine unfolds the cofixpoint under the case
    (kernel/cClosure.ml:1925-1932), which is the step that breaks subject reduction
    here; Rocq's manual records that failure as a known caveat
    (doc/sphinx/language/core/coinductive.rst:75-86). This hypothesis is not proved
    here, and we found no proof of it anywhere. What would refute it is a closed term of
    that shape at type False, that is a proof of False of that shape; it would reach us
    as a closed proof of False that the checker accepts. *)
Definition no_closed_stuck_cofix_case_at {cf : checker_flags} (Σ : global_env_ext)
    (ind : inductive) :=
  forall t, stuck_cofix_case t -> Σ ;;; [] |- t : tInd ind [] -> False.

Theorem pcuic_consistent {cf:checker_flags} {nor : normalizing_flags} Σ
  {normalization_in: NormalizationIn Σ} t False_pcuic :
  declared_inductive Σ False_pcuic False_mib False_oib ->
  wf_ext Σ -> axiom_free Σ ->
  no_closed_stuck_cofix_case_at Σ False_pcuic ->
  Σ ;;; [] |- t : tInd False_pcuic []  -> False.
Proof.
  intros Hdecl wfΣ axΣ nostuck typ_false.
  destruct (pcuic_canonicity Σ t False_pcuic [] []) as [t' [[typ_false' eqtt'] ctor]]; eauto.
  destruct ctor as [ctor|stuck].
  2:{ now eapply nostuck. }
  destruct Hdecl as [Hdecl Hidecl].
  destruct False_pcuic as [kn n]. destruct n; cbn in *; [| now rewrite nth_error_nil in Hidecl].
  rewrite /construct_cofix_discr /head in ctor.
  destruct decompose_app eqn:decomp.
  apply decompose_app_inv in decomp; subst.
  destruct t0; try discriminate ctor.
  - apply PCUICValidity.inversion_mkApps in typ_false' as H; auto.
    destruct H as (?&typ_ctor&_).
    apply inversion_Construct in typ_ctor as (?&?&?&?&?&?&?); auto.
    eapply Construct_Ind_ind_eq with (args' := []) in typ_false'; tea.
    2: eauto.
    destruct (on_declared_constructor d).
    destruct p.
    destruct s.
    destruct p.
    destruct typ_false' as (((((->&_)&_)&_)&_)&_).
    clear -Hdecl d wfΣ. destruct wfΣ.
    cbn in *.
    destruct d as ((?&?)&?).
    unshelve eapply declared_minductive_to_gen in Hdecl; eauto.
    unshelve eapply declared_minductive_to_gen in H; eauto.
    red in H, Hdecl. cbn in *. rewrite Hdecl in H; noconf H.
    cbn in H0. noconf H0.
    cbn in H1. rewrite nth_error_nil in H1.
    discriminate.
  - eapply @typing_cofix_coind with (indargs := []) in typ_false'; eauto.
    unfold check_recursivity_kind in typ_false'. destruct wfΣ.
    unshelve eapply declared_minductive_to_gen in Hdecl; eauto.
    red in Hdecl. rewrite Hdecl in typ_false'.
    cbn in typ_false'. inversion typ_false'.
Qed.
