(* Distributed under the terms of the MIT license. *)
(** * BET-315 eta lane, row O1: the normalization premise over [typingE]

  A copy of [PCUICSN.v:44-51] over [welltypedE] (plan.md row O1;
  [lanes/eta/t0-plan.md] §4): [NormalizationInE Σ] is the premise the E checker
  ([PCUICWfReductionEta], K4's [R_aux_Acc], the E copies of [PCUICWfEnv],
  [PCUICSafeConversion], [PCUICSafeChecker], [SafeTemplateChecker]) takes in place
  of [NormalizationIn Σ]. Like base's, it is an ASSUMPTION of the checker's
  statements: it has no proof here and no satisfying instance (base's
  [NormalizationIn] has none either).

  [NormalizationInE] is the stronger premise: it implies base [NormalizationIn]
  in a base-well-formed environment ([NormalizationInE_NormalizationIn]), because
  [welltyped] implies [welltypedE] ([typing_incl_E]). *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICReduction
     PCUICSafeLemmata PCUICSN PCUICTypingEta.

Class NormalizationInE {cf : checker_flags} {no : normalizing_flags} (Σ : global_env_ext) :=
  normalization_inE :
    forall Γ t,
      welltypedE Σ Γ t ->
      Acc (cored Σ Γ) t.
Class NormalizationE {cf : checker_flags} {no : normalizing_flags} :=
  normalizationE : forall Σ, wf_extE Σ -> NormalizationInE Σ.
#[export] Hint Mode NormalizationInE - - + : typeclass_instances.
#[export] Typeclasses Opaque NormalizationE.

Lemma NormalizationInE_NormalizationIn {cf : checker_flags} {no : normalizing_flags}
  (Σ : global_env_ext) (wfΣ : wf Σ) :
  NormalizationInE Σ -> NormalizationIn Σ.
Proof.
  intros h Γ t [A ht]. apply h. econstructor. exact (typing_incl_E wfΣ ht).
Qed.

Lemma NormalizationE_Normalization {cf : checker_flags} {no : normalizing_flags} :
  NormalizationE -> Normalization.
Proof.
  intros h Σ wfΣ. apply NormalizationInE_NormalizationIn; [exact wfΣ|].
  apply h. now apply wf_ext_incl_E.
Qed.
