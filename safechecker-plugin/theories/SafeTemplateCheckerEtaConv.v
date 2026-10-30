(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
(* Same-name rule (C6): neither [PCUICPosition] nor [PCUICPositionEta] is imported here; no name of either is
   used (the η stack's [welltypedE_context] is the field of [WelltypedEContextE], [PCUICEtaFactsCompose]). *)
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICOnFreeVars PCUICEquality
     PCUICSN PCUICTypingEta PCUICSNEta PCUICWellScopedCumulativityEta PCUICConversionEtaCongr
     PCUICContextConversionEta.
From MetaRocq.SafeChecker Require Import PCUICErrorsEta PCUICWfEnvEta PCUICSafeReduceEta
  PCUICSafeConversionEtaFacts PCUICSafeConversionEta PCUICTypeCheckerEta PCUICTypingEtaHyps PCUICEtaFactsCompose.

(** * ETAK (EtaK7): the η conversion as the checker's [conv_oracle] (K6 at the checker)

  BET-64 EtaCheckerLane, worker EtaK7, 2026-10-29. Coded against EtaConv's CONV contract
  (lanes/eta/etak/CONTRACTS.md, CONV, 2026-10-29 11:35Z, INTENDED, final when K3 compiles) and the
  section [Conversion] of [PCUICSafeConversionEta] at [fork/wip/etak-conv-skel-2026-10-29] @ [d38d5b9f]:
  [isconv_term] / [isconv_term_sound], soundness concluding [conv_cumE leq Σ Γ t1 t2 =
  ∥ ws_cumul_pbE leq Σ Γ t1 t2 ∥]. This is the only file that names EtaConv's conversion; a change of that
  contract is a fix here only. It builds once [PCUICSafeConversionEta] builds on this branch.

  Section parameters of [Conversion]: the Prop classes [ReduceTypedFactsE] and [ConvTypedFactsE] (implicit),
  the SQUASHED [closed_context_conversionE], and [welltypedE_context] (a Prop: it concludes [welltypedE]).
  This section does NOT bind the first three: it supplies them from the checker's own hypotheses
  ([PCUICEtaFactsCompose]; lane lead's dedup, 2026-10-29), so the composed checker assumes each of these
  facts once: [ReduceTypedFactsE] by [reduce_typed_facts_E_of_core] from the six-field
  [ReduceTypedFactsCoreE], [EtaFacts] (T1 [subject_reduction], U [whnf_red_inv]) and [WelltypedEContextE];
  [ConvTypedFactsE] by [conv_typed_facts_E_of_ctx] from [WelltypedEContextE]; [closed_context_conversionE]
  by [closed_context_conversionE_of_facts] from [EtaFacts]'s T0 [closed_context_cumulativity].
  [welltypedE_context] is the field of [WelltypedEContextE] (EtaPosK4's statement). No parameter is
  Type-valued, so extraction erases all of them: the extracted oracle takes only the environment and the terms.
  The explicit arguments of [isconv_term] are passed in the order of the section's [Context] lines
  (X_type, X, closed_context_conversionE, welltypedE_context, then Γ pb t1 h1 t2 h2); if EtaConv's built
  [About isconv_term] lists another order, this is the one place to change. *)

Section EtaOracle.
  Context {cf : checker_flags} {nor : normalizing_flags}.
  (* The checker's [EtaFacts] (the same instance as the checker's at the composition), the six REDUCE facts
     that nothing else states, and EtaPosK4's [welltypedE_context]; the conversion's four parameters are
     built from these (header). *)
  Context {EtaF : EtaFacts} {reduce_coreE : ReduceTypedFactsCoreE} {wt_contextE : WelltypedEContextE}.

  (** [None] when EtaConv's conversion succeeds (soundness: [isconv_term_sound]); [Some e] carries its
      error and no proof (G7). The conversion terminates by fuel ([PCUICFuelEta]): an empty fuel is the error
      [ConvNotEnoughFuel], which the checker reports as a refusal for lack of fuel. *)
  Definition eta_oracle_conv (X_type : abstract_env_impl) (X : X_type.π2.π1)
    (Γ : context) (pb : conv_pb)
    (t : term) (ht : forall Σ, abstract_env_ext_rel X Σ -> welltypedE Σ Γ t)
    (u : term) (hu : forall Σ, abstract_env_ext_rel X Σ -> welltypedE Σ Γ u) : option ConversionError :=
    match isconv_term X_type X (reduce_factsE := reduce_typed_facts_E_of_core)
            (conv_factsE := conv_typed_facts_E_of_ctx) closed_context_conversionE_of_facts welltypedE_context Γ pb t ht u hu with
    | ConvSuccess => None
    | ConvError e => Some e
    end.

  (* Without this hint the kernel check of the [Qed] below did not finish (> 60 s, out/probe-or2.log): the kernel
     unfolded [isconv_term] instead of comparing its arguments; with it the [Qed] takes 0.002 s (out/probe-or3.log).
     It changes the unfolding order only, not the term and not the statement; [Local] keeps it out of every file
     that imports this one; it is not soundness-relevant (the kernel still unfolds when it must). *)
  Local Strategy opaque [isconv_term].

  Lemma eta_oracle_conv_sound (X_type : abstract_env_impl) (X : X_type.π2.π1) Γ pb t ht u hu :
    eta_oracle_conv X_type X Γ pb t ht u hu = None ->
    forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pbE pb Σ Γ t u ∥.
  Proof.
    intros hc Σ wfΣ. unfold eta_oracle_conv in hc.
    destruct (isconv_term X_type X (reduce_factsE := reduce_typed_facts_E_of_core)
             (conv_factsE := conv_typed_facts_E_of_ctx) closed_context_conversionE_of_facts welltypedE_context Γ pb t ht u hu) eqn:hconv; [|discriminate].
    exact (isconv_term_sound X_type X (reduce_factsE := reduce_typed_facts_E_of_core)
             (conv_factsE := conv_typed_facts_E_of_ctx) closed_context_conversionE_of_facts welltypedE_context Σ wfΣ Γ pb t ht u hu hconv).
  Qed.

  Definition eta_conv_oracle : conv_oracle :=
    {| oracle_conv := @eta_oracle_conv; oracle_conv_sound := @eta_oracle_conv_sound |}.
End EtaOracle.
