(* Distributed under the terms of the MIT license. *)

(** * A8: context conversion for [ws_cumul_pbE]

  [ws_cumul_ctx_pbE] is base's [ws_cumul_ctx_pb] ([PCUICWellScopedCumulativity])
  with [ws_cumul_pbE] in place of [ws_cumul_pb], so it copies base's scoping: each
  declaration is compared by [ws_cumul_pbE], which carries [is_closed_context] and
  [is_open_term].

  ** Method: telescopes
  [Γ ⊢ T ≤ U] is turned into [⊢ Π Γ. T ≤ Π Γ. U] (A7's codomain congruence over every
  context); [Π Γ. X ≡ Π Γ'. X] by A5's binder congruences along [Γ ≡ Γ']
  ([it_mkProd_ctx_congr]); A3 joins the three; the telescope is peeled again on the
  [Γ'] side ([it_mkProd_inv]: the Π inversion for an assumption, [letin_body_inv]
  for a definition).
  No context-reduction confluence is needed.

  Lemmas: [ws_cumul_pbE_ws_cumul_ctx]; its symmetry; and the inversions under a
  reduced context [cumul_red_ctx_invE], [ws_cumul_pbE_red_ctx_inv] and
  [conv_cum_red_conv_invE].

**The hypotheses are satisfiable:** [ClosedBodies Σ] by any well-formed
  environment ([wf_ClosedBodies]; [wfE_ClosedBodies] for [wfE]); the context relations by reflexivity
  ([ws_cumul_ctx_pbE_refl]); every [ws_cumul_pbE] premise by reflexivity. Instances:
  [PCUICEtaA6Instances]. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICEquality PCUICReduction
     PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICWellScopedCumulativity PCUICConversion
     PCUICContextConversion
     PCUICEtaFInst PCUICEtaI5 PCUICEtaI5Trans PCUICEtaI5A2
     PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICWsCumulEtaSubst
     PCUICEtaA6 PCUICEtaA6More PCUICClosedBodies.

Definition ws_cumul_declsE {cf : checker_flags} (pb : conv_pb)
  (Σ : global_env_ext) (Γ : context) (d d' : context_decl) :=
  All_decls_alpha_pb pb (fun pb => ws_cumul_pbE pb Σ Γ) d d'.

Definition ws_cumul_ctx_pbE {cf : checker_flags} (pb : conv_pb)
  (Σ : global_env_ext) (Γ Γ' : context) :=
  All2_fold (fun Γ Γ' => ws_cumul_declsE pb Σ Γ) Γ Γ'.

Section A8.

  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ}.

  Local Notation WS pb Γ := (ws_cumul_pbE pb Σ Γ).
  Local Notation CTX Γ Γ' := (ws_cumul_ctx_pbE Conv Σ Γ Γ').

  Lemma WS8_trans {pb Γ t u v} : WS pb Γ t u -> WS pb Γ u v -> WS pb Γ t v.
  Proof. exact (fun h1 h2 => ws_cumul_pbE_trans (Σ := Σ) (wfΣ := wfΣ) _ _ _ h1 h2). Qed.

  (** ** Telescopes *)

  (** [Π Γ. X ≡ Π Γ'. X'] from [Γ ≡ Γ'] and [Γ ⊢ X ≡ X']. *)
  Lemma it_mkProd_ctx_congr {Γ Γ' X X'} :
    CTX Γ Γ' -> WS Conv Γ X X' -> WS Conv [] (it_mkProd_or_LetIn Γ X) (it_mkProd_or_LetIn Γ' X').
  Proof.
    intros h. induction h as [|d d' Γ Γ' h IH hd] in X, X' |- *; cbn; intros hX; [exact hX|].
    apply IH. unfold ws_cumul_declsE in hd.
    destruct hd as [na na' A A' hna hA|na na' b A b' A' hna hb hA]; cbn.
    - eapply ws_cumul_pbE_Prod; eassumption.
    - eapply ws_cumul_pbE_LetIn; eassumption.
  Qed.

  Lemma letin_body_inv {pb Γ na b A X Y} :
    WS pb Γ (tLetIn na b A X) (tLetIn na b A Y) -> WS pb (Γ ,, vdef na b A) X Y.
  Proof.
    intros h.
    have hΓ := wsE_ctx h.
    move: (wsE_left h). cbn [on_free_vars]. move/and3P => [hb hA hX].
    move: (wsE_right h). cbn [on_free_vars]. move/and3P => [_ _ hY].
    have hΓ1 : is_closed_context (Γ ,, vdef na b A) := closed_snoc_vdef Γ na b A hΓ hb hA.
    have hrX : red Σ (Γ ,, vdef na b A) X (lift 1 0 (X {0 := b}))
      := red_rel_all (Σ := Σ) (Γ := Γ ,, vdef na b A) (i := 0) (body := b) (t := X) eq_refl.
    have hrY : red Σ (Γ ,, vdef na b A) Y (lift 1 0 (Y {0 := b}))
      := red_rel_all (Σ := Σ) (Γ := Γ ,, vdef na b A) (i := 0) (body := b) (t := Y) eq_refl.
    have h1 := red_ws_cumul_pbE (Σ := Σ) (wfΣ := wfΣ) (pb := pb)
                 (closed_red_of hΓ1 (open_snoc Γ _ X hX) hrX).
    have h4 := red_ws_cumul_pbE_inv (Σ := Σ) (wfΣ := wfΣ) (pb := pb)
                 (closed_red_of hΓ1 (open_snoc Γ _ Y hY) hrY).
    have h2 := ws_cumul_pbE_LetIn_inv (wfΣ := wfΣ) h.
    have h3 := weakening_ws_cumul_pbE (Σ := Σ) (wfΣ := wfΣ) (pb := pb) (Γ := Γ) (Γ' := [])
                 (Γ'' := [vdef na b A]) h2 hΓ1.
    exact (WS8_trans h1 (WS8_trans h3 h4)).
  Qed.

  Lemma mkProd_or_LetIn_inv {pb Γ d X Y} :
    WS pb Γ (mkProd_or_LetIn d X) (mkProd_or_LetIn d Y) -> WS pb (Γ ,, d) X Y.
  Proof.
    destruct d as [na [b|] A]; cbn; intros h.
    - exact (letin_body_inv h).
    - destruct (ws_cumul_pbE_Prod_Prod_inv_l h) as [_ _ h3]. exact h3.
  Qed.

  Lemma it_mkProd_inv {pb Δ Γ X Y} :
    WS pb Δ (it_mkProd_or_LetIn Γ X) (it_mkProd_or_LetIn Γ Y) -> WS pb (Δ ,,, Γ) X Y.
  Proof.
    induction Γ as [|d Γ IH] in X, Y |- *; cbn; intros h; [exact h|].
    exact (mkProd_or_LetIn_inv (IH _ _ h)).
  Qed.

  (** ** A8: conversion in convertible contexts *)

  Lemma ws_cumul_pbE_ws_cumul_ctx {pb Γ Γ' T U} : CTX Γ Γ' -> WS pb Γ T U -> WS pb Γ' T U.
  Proof.
    intros hc h.
    have hΓ := wsE_ctx h.
    have h0 : WS pb ([] ,,, Γ) T U by rewrite app_context_nil_l; exact h.
    have h1 := ws_cumul_pbE_it_mkProd_or_LetIn_codom_pb (wfΣ := wfΣ) (Δ := []) (Γ := Γ) h0.
    have hT := it_mkProd_ctx_congr hc (ws_cumul_pbE_refl hΓ (wsE_left h)).
    have hU := it_mkProd_ctx_congr hc (ws_cumul_pbE_refl hΓ (wsE_right h)).
    have hT' : WS pb [] (it_mkProd_or_LetIn Γ' T) (it_mkProd_or_LetIn Γ T).
    { apply ws_cumul_eq_pbE. symmetry. exact hT. }
    have hU' : WS pb [] (it_mkProd_or_LetIn Γ U) (it_mkProd_or_LetIn Γ' U) := ws_cumul_eq_pbE hU.
    have h2 := it_mkProd_inv (WS8_trans hT' (WS8_trans h1 hU')).
    rewrite app_context_nil_l in h2. exact h2.
  Qed.

  Lemma ws_cumul_ctx_pbE_refl Γ : is_closed_context Γ -> CTX Γ Γ.
  Proof.
    induction Γ as [|[na [b|] A] Γ IH]; intros h; constructor.
    all: try (move: h; rewrite on_free_vars_ctx_snoc => /andP [h1 h2]).
    all: try (apply IH; exact h1).
    all: unfold ws_cumul_declsE; constructor; try reflexivity.
    all: move: h2; rewrite /on_free_vars_decl /test_decl /=; try move/andP => [h2 h3].
    all: apply ws_cumul_pbE_refl; assumption.
  Qed.

  (** Symmetry, through A8 on the prefix. *)
  Lemma ws_cumul_ctx_pbE_sym {Γ Γ'} : CTX Γ Γ' -> CTX Γ' Γ.
  Proof.
    induction 1 as [|d d' Γ Γ' h IH hd]; constructor; [exact IH|].
    unfold ws_cumul_declsE in *.
    destruct hd as [na na' A A' hna hA|na na' b A b' A' hna hb hA]; constructor.
    - exact (eq_binder_annot_sym _ _ hna).
    - exact (ws_cumul_pbE_ws_cumul_ctx h (ws_cumul_pbE_sym _ _ hA)).
    - exact (eq_binder_annot_sym _ _ hna).
    - exact (ws_cumul_pbE_ws_cumul_ctx h (ws_cumul_pbE_sym _ _ hb)).
    - exact (ws_cumul_pbE_ws_cumul_ctx h (ws_cumul_pbE_sym _ _ hA)).
  Qed.

  (** ** The T rows that waited for A8 *)

  Lemma closed_red_ctx_ctx {Γ Γ'} : Σ ⊢ Γ ⇝ Γ' -> CTX Γ Γ'.
  Proof.
    induction 1 as [|d d' Γ Γ' h IH hd]; constructor; [exact IH|].
    unfold ws_cumul_declsE. destruct hd; constructor.
    all: try reflexivity.
    all: eapply (red_ws_cumul_pbE (Σ := Σ) (wfΣ := wfΣ)); eassumption.
  Qed.

  (** x5, x6. *)
  Lemma ws_cumul_pbE_red_ctx_inv {pb Γ Γ'} {T U} : Σ ⊢ Γ' ⇝ Γ -> WS pb Γ T U -> WS pb Γ' T U.
  Proof. intros hr h. exact (ws_cumul_pbE_ws_cumul_ctx (ws_cumul_ctx_pbE_sym (closed_red_ctx_ctx hr)) h). Qed.

  (** x4. *)
  Lemma cumul_red_ctx_invE {pb} {Γ Γ' : context} {T U : term} :
    WS pb Γ T U -> Σ ⊢ Γ' ⇝ Γ -> WS pb Γ' T U.
  Proof. intros h hr. exact (ws_cumul_pbE_red_ctx_inv hr h). Qed.

  (** i49. *)
  Lemma conv_cum_red_conv_invE pb Γ Γ' t1 t2 t1' t2' :
    CTX Γ Γ' -> Σ ;;; Γ ⊢ t1 ⇝ t1' -> Σ ;;; Γ' ⊢ t2 ⇝ t2' -> WS pb Γ t1 t2 -> WS pb Γ t1' t2'.
  Proof.
    intros hc h1 h2 h.
    have h2' : WS Conv Γ t2 t2' :=
      ws_cumul_pbE_ws_cumul_ctx (ws_cumul_ctx_pbE_sym hc)
        (red_ws_cumul_pbE (Σ := Σ) (wfΣ := wfΣ) (pb := Conv) h2).
    eapply WS8_trans; [|exact (ws_cumul_eq_pbE h2')].
    exact (ws_cumul_pbE_red_l_inv (wfΣ := wfΣ) _ h (clrel_rel h1)).
  Qed.

End A8.
