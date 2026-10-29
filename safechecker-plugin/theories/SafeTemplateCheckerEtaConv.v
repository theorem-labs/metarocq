(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICOnFreeVars PCUICEquality
     PCUICPosition PCUICTypingEta PCUICSNEta PCUICWellScopedCumulativityEta PCUICConversionEtaCongr
     PCUICContextConversionEta PCUICPositionEta.
From MetaRocq.SafeChecker Require Import PCUICErrorsEta PCUICWfEnvEta PCUICSafeReduceEta
  PCUICSafeConversionEtaFacts PCUICSafeConversionEta PCUICTypeCheckerEta.

(** * ETAK (EtaK7): the η conversion as the checker's [conv_oracle] (K6 at the checker)

  BET-64 EtaCheckerLane, worker EtaK7, 2026-10-29. Coded against EtaConv's CONV contract
  (lanes/eta/etak/CONTRACTS.md, CONV, 2026-10-29 11:35Z, INTENDED, final when K3 compiles) and the
  section [Conversion] of [PCUICSafeConversionEta] at [fork/wip/etak-conv-skel-2026-10-29] @ [d38d5b9f]:
  [isconv_term] / [isconv_term_sound], soundness concluding [conv_cumE leq Σ Γ t1 t2 =
  ∥ ws_cumul_pbE leq Σ Γ t1 t2 ∥]. This is the only file that names EtaConv's conversion; a change of that
  contract is a fix here only. It builds once [PCUICSafeConversionEta] builds on this branch.

  Section parameters of [Conversion] at [d38d5b9f], taken here verbatim: the Prop classes
  [ReduceTypedFacts] and [ConvTypedFacts] (implicit), the SQUASHED [closed_context_conversionE], and
  [welltypedE_context] (a Prop: it concludes [welltypedE]). [typingE_rename_P] is now EtaConv's proved
  definition and [cmpb_heads_ws] a proved lemma, so neither is a parameter. No parameter is Type-valued, so
  extraction erases all of them: the extracted oracle takes only the environment and the terms.
  The explicit arguments of [isconv_term] are passed in the order of the section's [Context] lines
  (X_type, X, closed_context_conversionE, welltypedE_context, then Γ pb t1 h1 t2 h2); if EtaConv's built
  [About isconv_term] lists another order, this is the one place to change. *)

Section EtaOracle.
  Context {cf : checker_flags} {nor : normalizing_flags}.
  Context {reduce_factsE : ReduceTypedFacts welltypedE wf_extE}.
  Context {conv_factsE : ConvTypedFacts welltypedE wf_extE}.
  Context (closed_context_conversionE : ∥ forall (Σ : global_env_ext), wfE Σ.1 -> forall Γ t T Γ',
    Σ ;;; Γ |-E t : T -> wf_localE Σ Γ' -> ws_cumul_ctx_pbE Conv Σ Γ Γ' -> Σ ;;; Γ' |-E t : T ∥).
  Context (welltypedE_context : forall (Σ : global_env_ext), wfE Σ.1 -> forall Γ t,
    no_Eta_arg (snd t) -> welltypedE Σ Γ (zip t) -> welltypedE Σ (Γ ,,, stack_context (snd t)) (fst t)).

  (** [None] when EtaConv's conversion succeeds (soundness: [isconv_term_sound]); [Some e] carries its
      error and no proof (G7). *)
  Program Definition eta_conv_oracle : conv_oracle :=
    {| oracle_conv X_type X normalization_in Γ pb t ht u hu :=
         match isconv_term X_type X (normalization_in := normalization_in)
                 closed_context_conversionE welltypedE_context Γ pb t ht u hu with
         | ConvSuccess => None
         | ConvError e => Some e
         end |}.
  Next Obligation.
    intros X_type X normalization_in Γ pb t ht u hu hc Σ wfΣ.
    destruct (isconv_term X_type X (normalization_in := normalization_in)
                closed_context_conversionE welltypedE_context Γ pb t ht u hu) eqn:hconv; [|discriminate].
    exact (isconv_term_sound X_type X (normalization_in := normalization_in)
             closed_context_conversionE welltypedE_context Γ pb t ht u hu hconv Σ wfΣ).
  Qed.
End EtaOracle.
