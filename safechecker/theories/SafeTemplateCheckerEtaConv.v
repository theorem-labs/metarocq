(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
(* Same-name rule (C6): neither [PCUICPosition] nor [PCUICPositionEta] is imported here; no name of either is
   used (the η stack's [welltypedE_context] is the field of [WelltypedEContextE], [PCUICEtaFactsCompose]). *)
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICOnFreeVars PCUICEquality
     PCUICSN PCUICTypingEta PCUICWellScopedCumulativityEta PCUICConversionEtaCongr
     PCUICContextConversionEta.
From MetaRocq.SafeChecker Require Import PCUICErrorsEta PCUICWfEnvEta PCUICSafeReduceEta
  PCUICSafeConversionEtaFacts PCUICSafeConversionEta PCUICTypeCheckerEta PCUICTypingEtaHyps PCUICEtaFactsCompose.
(* The proved instances of the classes (ETAK discharge); Required only and named qualified. *)
From MetaRocq.SafeChecker Require PCUICTypingEtaDischarge.

(** * ETAK (EtaK7): the η conversion as the checker's [conv_oracle] (K6 at the checker)

  BET-64 EtaCheckerLane, worker EtaK7, 2026-10-29. Coded against EtaConv's CONV contract
  (lanes/eta/etak/CONTRACTS.md, CONV, 2026-10-29 11:35Z, INTENDED, final when K3 compiles) and the
  section [Conversion] of [PCUICSafeConversionEta] at [fork/wip/etak-conv-skel-2026-10-29] @ [d38d5b9f]:
  [isconv_term] / [isconv_term_sound], soundness concluding [conv_cumE leq Σ Γ t1 t2 =
  ∥ ws_cumul_pbE leq Σ Γ t1 t2 ∥]. This is the only file that names EtaConv's conversion; a change of that
  contract is a fix here only.

  Section parameters of [Conversion]: the Prop classes [ReduceTypedFactsE] and [ConvTypedFactsE] (implicit),
  the SQUASHED [closed_context_conversionE], and [welltypedE_context] (a Prop: it concludes [welltypedE]).
  This section binds none of them: each is passed explicitly at the [isconv_term] call, built ONLY from the
  proved instances of [PCUICTypingEtaDischarge] (ETAK discharge, lanes/eta/etak/discharge-transcriptions.md):
  [ReduceTypedFactsE] by [reduce_typed_facts_E_of_core] at [ReduceTypedFactsCoreE_discharged],
  [EtaFacts_discharged] and [WelltypedEContextE_discharged]; [ConvTypedFactsE] by [conv_typed_facts_E_of_ctx]
  at [WelltypedEContextE_discharged]; [closed_context_conversionE] by [closed_context_conversionE_squashed]
  (the squash of [closed_context_conversionE_proved], [PCUICContextConversionTypEta.closed_context_conversionE]);
  [welltypedE_context] by the field of [WelltypedEContextE_discharged]. Each instance takes only [cf], and
  every premise about the environment is inside its fields' statements, so [eta_conv_oracle] below is a
  closed term, polymorphic in [cf] and [nor]; the record [conv_oracle] itself quantifies over every
  abstract environment implementation [X_type], every environment [X] and every [Σ] related to it.
  No parameter is Type-valued, so extraction erases all of them: the extracted oracle takes only the
  environment and the terms. The explicit arguments of [isconv_term] are passed in the order of the
  section's [Context] lines (X_type, X, closed_context_conversionE, welltypedE_context, then Γ pb t1 h1 t2
  h2).

  The file is in [safechecker] (moved from [safechecker-plugin/theories] on the ship branch, module name
  unchanged) because the root [PCUICSafeCheckerEta.typecheck_program] uses [eta_conv_oracle] as its
  [conv_oracle] instance, and [safechecker] builds before the plugin. *)

Section EtaOracle.
  Context {cf : checker_flags} {nor : normalizing_flags}.

  (* The four parameters of the section [Conversion] of [PCUICSafeConversionEta], each built ONLY from the
     proved instances (header); named once here, used at the three [isconv_term] sites below. *)
  Local Notation rfE := (@reduce_typed_facts_E_of_core cf
    (@PCUICTypingEtaDischarge.ReduceTypedFactsCoreE_discharged cf)
    (@PCUICTypingEtaDischarge.EtaFacts_discharged cf)
    (@PCUICTypingEtaDischarge.WelltypedEContextE_discharged cf)).
  Local Notation cfE := (@conv_typed_facts_E_of_ctx cf (@PCUICTypingEtaDischarge.WelltypedEContextE_discharged cf)).
  Local Notation cccE := (@PCUICTypingEtaDischarge.closed_context_conversionE_squashed cf).
  Local Notation wtcE := (@welltypedE_context cf (@PCUICTypingEtaDischarge.WelltypedEContextE_discharged cf)).

  (** [None] when EtaConv's conversion succeeds (soundness: [isconv_term_sound]); [Some e] carries its
      error and no proof (G7). The conversion terminates by fuel ([PCUICFuelEta]): an empty fuel is the error
      [ConvNotEnoughFuel], which the checker reports as a refusal for lack of fuel. *)
  Definition eta_oracle_conv (X_type : abstract_env_impl) (X : X_type.π2.π1)
    (Γ : context) (pb : conv_pb)
    (t : term) (ht : forall Σ, abstract_env_ext_rel X Σ -> welltypedE Σ Γ t)
    (u : term) (hu : forall Σ, abstract_env_ext_rel X Σ -> welltypedE Σ Γ u) : option ConversionError :=
    match isconv_term X_type X (reduce_factsE := rfE) (conv_factsE := cfE) cccE wtcE Γ pb t ht u hu with
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
    destruct (isconv_term X_type X (reduce_factsE := rfE) (conv_factsE := cfE) cccE wtcE Γ pb t ht u hu)
      eqn:hconv; [|discriminate].
    exact (isconv_term_sound X_type X (reduce_factsE := rfE) (conv_factsE := cfE) cccE wtcE
             Σ wfΣ Γ pb t ht u hu hconv).
  Qed.

  (** The checker's conversion, CLOSED: its only binders are [cf] and [nor] (the section's), it is built
      only from the proved instances above, and its type is the roots' [conv_oracle] signature
      ([PCUICTypeCheckerEta.conv_oracle]), whose two fields quantify over every [X_type], [X], [Γ], [pb],
      [t], [u] and every [Σ] with [abstract_env_ext_rel X Σ]. *)
  Definition eta_conv_oracle : conv_oracle :=
    {| oracle_conv := @eta_oracle_conv; oracle_conv_sound := @eta_oracle_conv_sound |}.
End EtaOracle.
