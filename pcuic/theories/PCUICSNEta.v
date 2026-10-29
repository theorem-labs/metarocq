(* Distributed under the terms of the MIT license. *)
(** * The normalization premise over [typingE]

  [NormalizationInE] and [NormalizationE] are the copies of [NormalizationIn] and
  [Normalization] ([PCUICSN.v]) with [welltyped] replaced by [welltypedE]
  ([PCUICTypingEta.v]). They are what the η checker takes as its normalization
  premise, where the base checker takes [NormalizationIn].

  **Nothing in this development proves [NormalizationInE], and nothing proves
  [NormalizationE].** They are assumptions, exactly as base [NormalizationIn] and
  [Normalization] are: the library states strong normalization as a class and takes
  it as a hypothesis of every function that needs it, and this file does the same for
  the η relation. There is no satisfying instance here, and no instance is possible
  here: [welltypedE Σ Γ t] holds of terms with β-redexes in every environment, so a
  satisfying instance of [NormalizationInE Σ] for a concrete [Σ] would be a proof of
  strong normalization of PCUIC, which the library does not have for base
  [NormalizationIn] either. A reader must treat a theorem with this premise as
  conditional on it.

  **How it relates to base's.** [NormalizationInE] is the STRONGER assumption, and
  the only implication proved here runs from it to base's:

  - [NormalizationInE_NormalizationIn] : for [Σ] with [wf Σ],
    [NormalizationInE Σ -> NormalizationIn Σ].
  - [NormalizationE_Normalization] : [NormalizationE -> Normalization], with no
    premise on the environment ([NormalizationE] quantifies over [wf_extE]
    environments, [Normalization] over the [wf_ext] ones, and [wf_ext_incl_E] maps
    the latter into the former).

  Both hold because [welltyped Σ Γ t -> welltypedE Σ Γ t] under [wf Σ]
  ([typing_incl_E], [PCUICTypingEta.v]): a term typable in the base system is typable
  in the η system, so quantifying over the η-typable terms quantifies over more
  terms. The reverse implication is NOT proved and is not expected to hold: a term
  typable only up to η is in [welltypedE] and not in [welltyped], so
  [NormalizationIn Σ] says nothing about it. Both conclusions are about the SAME
  reduction [cored Σ Γ] (base reduction); the two classes differ only in which terms
  they are asserted of. *)
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
