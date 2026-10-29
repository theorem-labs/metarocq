(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICLiftSubst PCUICTyping
     PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd PCUICTypingEtaNotions.

From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

(** * Typing spines and generation lemmas over [typingE]

  The E copy of [PCUICGeneration]. Every declaration of the base file mentions
  typing or cumulativity, so all three are copied, with only the relations
  renamed ([typing] → [typingE], [isType] → [isTypeE], [cumulSpec] →
  [cumulSpecE]):
  - [typing_spineE] (constructors [type_spine_nilE], [type_spine_consE]) is base
    [typing_spine] ([type_spine_nil], [type_spine_cons]) of [PCUICGeneration],
    over [cumulSpecE]. Base [PCUICArities] defines a second, different
    [typing_spine] (with [isType] of both types and [ws_cumul_pb]); its twin,
    [PCUICAritiesEta.typing_spineE], is the one the later copies use. This file
    is never exported, and no file imports it together with [PCUICAritiesEta]
    unqualified;
  - [type_mkAppsE] is base [type_mkApps];
  - [type_it_mkLambda_or_LetInE] is base [type_it_mkLambda_or_LetIn].
  No base declaration is left out. *)

Section GenerationE.
  Context `{cf : config.checker_flags}.

  Inductive typing_spineE (Σ : global_env_ext) (Γ : context) :
    term -> list term -> term -> Type :=
  | type_spine_nilE ty ty' :
      isTypeE Σ Γ ty' ->
      cumulSpecE Σ Γ ty ty' ->
      typing_spineE Σ Γ ty [] ty'

  | type_spine_consE hd tl na A B T B' :
      isTypeE Σ Γ (tProd na A B) ->
      cumulSpecE Σ Γ T (tProd na A B) ->
      Σ ;;; Γ |-E hd : A ->
      typing_spineE Σ Γ (subst10 hd B) tl B' ->
      typing_spineE Σ Γ T (hd :: tl) B'.

  Lemma type_mkAppsE Σ Γ t u T t_ty :
    Σ ;;; Γ |-E t : t_ty ->
    typing_spineE Σ Γ t_ty u T ->
    Σ ;;; Γ |-E mkApps t u : T.
  Proof using Type.
    intros Ht Hsp.
    revert t Ht. induction Hsp; simpl; auto.
    intros t Ht. eapply typeE_Cumul; eauto. eapply i.2.π2.1.

    intros.
    specialize (IHHsp (tApp t0 hd)). apply IHHsp.
    eapply typeE_App; eauto. eapply i.2.π2.1.
    eapply typeE_Cumul; eauto. eapply i.2.π2.1.
  Qed.

  Lemma type_it_mkLambda_or_LetInE :
    forall Σ Γ Δ t A,
      Σ ;;; Γ ,,, Δ |-E t : A ->
      Σ ;;; Γ |-E it_mkLambda_or_LetIn Δ t : it_mkProd_or_LetIn Δ A.
  Proof using Type.
    intros Σ Γ Δ t A h.
    induction Δ as [| [na [b|] B] Δ ih ] in t, A, h |- *.
    - assumption.
    - simpl. cbn. eapply ih.
      simpl in h. pose proof (typingE_wf_local h) as hc.
      apply All_local_env_tip in hc as [hc ona].
      econstructor; try eassumption.
    - simpl. cbn. eapply ih.
      pose proof (typingE_wf_local h) as hc. cbn in hc.
      apply All_local_env_tip in hc as [hc ona].
      econstructor; try eassumption.
  Qed.

End GenerationE.
