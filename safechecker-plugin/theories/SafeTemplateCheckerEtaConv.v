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
  (lanes/eta/etak/CONTRACTS.md, CONV, 2026-10-29 11:35Z, INTENDED, final when K3 compiles):
  [isconv_term] / [isconv_term_sound] over the section parameters of [PCUICSafeConversionEta]'s
  section [Conversion], soundness concluding [conv_cumE leq Σ Γ t1 t2 = ∥ ws_cumul_pbE leq Σ Γ t1 t2 ∥].
  This is the only file that names EtaConv's conversion; a change of that contract is a fix here only.
  It builds once [PCUICSafeConversionEta] builds (not before: the copy on this branch is EtaConv's early
  one).

  The section parameters of [Conversion] other than the environment (EtaConv's class [ConvTypedFacts],
  EtaPosK4's three named hypotheses of section [EtaTypingE], and [cmpb_heads_ws]) are this file's section
  parameters too, verbatim, and so premises of [eta_conv_oracle]. NOTE for the extraction (F2-early):
  [typingE_rename_P] and [closed_context_conversionE] conclude a [typingE] derivation (a [Type]), so
  extraction would keep them as arguments of the extracted conversion; the forecast tree needs them
  squashed or in a [Prop] class on EtaConv's side (raised with the lane lead). *)

Section EtaOracle.
  Context {cf : checker_flags} {nor : normalizing_flags}.
  Context {reduce_factsE : ReduceTypedFacts welltypedE wf_extE}.
  Context {conv_factsE : ConvTypedFacts welltypedE wf_extE}.
  Context (typingE_rename_P : forall P (Σ : global_env_ext) Γ Δ f t A, wfE Σ.1 ->
    wf_localE Σ Δ × urenaming (shiftnP #|Γ| P) Γ Δ f ->
    Σ ;;; Γ |-E t : A -> Σ ;;; Δ |-E rename f t : rename f A).
  Context (closed_context_conversionE : forall (Σ : global_env_ext), wfE Σ.1 -> forall Γ t T Γ',
    Σ ;;; Γ |-E t : T -> wf_localE Σ Γ' -> ws_cumul_ctx_pbE Conv Σ Γ Γ' -> Σ ;;; Γ' |-E t : T).
  Context (welltypedE_context : forall (Σ : global_env_ext), wfE Σ.1 -> forall Γ t,
    no_Eta_arg (snd t) -> welltypedE Σ Γ (zip t) -> welltypedE Σ (Γ ,,, stack_context (snd t)) (fst t)).
  Context (cmpb_heads_ws : forall (Σ : global_env_ext) Γ pb t1 args1 t2 args2, wf_extE Σ ->
    is_closed_context Γ -> is_open_term Γ (mkApps t1 args1) -> is_open_term Γ (mkApps t2 args2) ->
    compare_term_napp Σ Σ pb #|args1| t1 t2 ->
    ws_cumul_pbE_terms Σ Γ args1 args2 ->
    ws_cumul_pbE pb Σ Γ (mkApps t1 args1) (mkApps t2 args2)).

  Local Notation isconvE X_type X normalization_in :=
    (@isconv_term cf nor X_type X normalization_in reduce_factsE conv_factsE
       typingE_rename_P closed_context_conversionE welltypedE_context cmpb_heads_ws).

  (** [None] when EtaConv's conversion succeeds (soundness: [isconv_term_sound]); [Some e] carries its
      error and no proof (G7). *)
  Program Definition eta_conv_oracle : conv_oracle :=
    {| oracle_conv X_type X normalization_in Γ pb t ht u hu :=
         match isconvE X_type X normalization_in Γ pb t ht u hu with
         | ConvSuccess => None
         | ConvError e => Some e
         end |}.
  Next Obligation.
    intros X_type X normalization_in Γ pb t ht u hu hc Σ wfΣ.
    destruct (isconvE X_type X normalization_in Γ pb t ht u hu) eqn:hconv; [|discriminate].
    exact (@isconv_term_sound cf nor X_type X normalization_in reduce_factsE conv_factsE
             typingE_rename_P closed_context_conversionE welltypedE_context cmpb_heads_ws
             Σ wfΣ Γ pb t ht u hu hconv).
  Qed.
End EtaOracle.
