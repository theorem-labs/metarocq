(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the lemmas of [PCUICNormalizationEta] (T0 copy 20), and the
      compiled-form check against the forecast field of [PCUICCanonicityEta]

  **Section variables.** The five forecast classes the copy's section takes (T2a's
  [ValForecastCopy16], T1's [SRForecastCopy16]/[SRForecastCopy18], [ClassifForecastCopy16] and
  [ProgForecastCopy18]) and the normalization hypothesis [NormalizationInE si_Σ].
  [NormalizationInE] ([PCUICSNEta]) is base's [NormalizationIn] over [welltypedE]: a premise
  unprovable by design (it is strong normalization), inherited from base, where every one of
  these five lemmas takes [NormalizationIn Σ]. It is not a forecast and is never discharged;
  it is the one hypothesis of this file with no satisfying instance, as in
  [PCUICCanonicityEtaInstances].

  **Non-degeneracy.** Every instance runs on the β-redex [sri_A = (λx:Prop. x) (∀P:Prop. P)]
  in [si_Σ], typed at [Prop] ([iv_app_typed]), with [axiom_free si_Σ] ([cli_axiom_free]) and
  [wfE si_Σ] proved. The redex is not a value and not [whnf], so each lemma must find the β
  step: [wh_normalizationE_inst] and [wcbv_normalizationE_inst] go through
  [progress_env_propE], and the two standardization instances reduce it to [∀P:Prop. P].
  [SN_to_WNE_inst] takes a REAL accessibility proof ([c20_acc_sri_A], built from the two
  normal forms below), not the normalization hypothesis.

  **The reduction behaviour of the witness, proved here.** [sri_A] has exactly one [red1]
  reduct, [iv_False = ∀P:Prop. P] ([c20_sri_A_red1]), and [iv_False] has none
  ([PCUICProgressEtaInstances.pgi_False_normal]). Both facts are needed as the irreducibility
  premise of the standardization lemmas and for the accessibility proof.

  **Compiled-form identity with the forecast field.** [PCUICCanonicityEta] carries base
  [wh_normalization] as the single field [wh_normalizationE] of its forecast class
  [CanonForecastCopy20]. [c20_lemma_has_field_type] and [c20_field_has_lemma_type] ascribe each
  of the two against the other's exact type, so the type checker decides the identity in both
  directions (the rule for a delete-and-import: identical types accept each other both ways).
  The lemma is applied to the five forecast classes first, which is the only difference between
  the two compiled types: the copy's section premises, which disappear when those classes are
  deleted. The name [wh_normalizationE] denotes two objects while this file is in scope (the
  field and the copy's lemma), so every reference to either is written qualified. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars
     PCUICTyping PCUICReduction PCUICConfluence PCUICWcbvEval PCUICNormal PCUICSafeLemmata
     PCUICSN PCUICClassification PCUICWellScopedCumulativity
     PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaNotions PCUICClosedBodies
     PCUICWellScopedCumulativityEta PCUICEtaA6 PCUICCumulativitySpecEtaClosureInstances
     PCUICInversionEtaInstances PCUICSREtaInstances PCUICSNEta PCUICValidityEta PCUICSREta
     PCUICClassificationEta PCUICClassificationEtaInstances PCUICProgressEta
     PCUICProgressEtaInstances PCUICCanonicityEta PCUICNormalizationEta.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.
#[local] Existing Instance si_wfE.

(** ** The witness and its reduction behaviour, without any class *)

(** [sri_A = (λx:Prop. x) (∀P:Prop. P)] steps only to [∀P:Prop. P]. *)
Lemma c20_sri_A_red1 v : red1 si_Σ [] sri_A v -> v = iv_False.
Proof.
  unfold sri_A, iv_id, iv_False, si_P. intros H. inv_red H.
  - now cbn.
  - exfalso. eapply red_normal_Sort; eassumption.
  - exfalso. eapply red_normal_Rel0; eassumption.
  - exfalso. eapply pgi_False_normal; eassumption.
Qed.

(** A [red1]-normal term is accessible for [cored]. *)
Lemma c20_acc_nf t : (forall v, red1 si_Σ [] t v -> False) -> Acc (cored si_Σ []) t.
Proof.
  intros h. constructor. intros y Hy. exfalso.
  induction Hy; eauto.
Qed.

Lemma c20_acc_False : Acc (cored si_Σ []) iv_False.
Proof. apply c20_acc_nf. intros v H. eapply pgi_False_normal; eassumption. Qed.

(** Everything [sri_A] reaches in one or more steps is [∀P:Prop. P]. *)
Lemma c20_cored_sri_A y : cored si_Σ [] y sri_A -> y = iv_False.
Proof.
  intros Hy. induction Hy.
  - now apply c20_sri_A_red1.
  - exfalso. subst. eapply pgi_False_normal; eassumption.
Qed.

Lemma c20_acc_sri_A : Acc (cored si_Σ []) sri_A.
Proof.
  constructor. intros y Hy. rewrite (c20_cored_sri_A y Hy). exact c20_acc_False.
Qed.

(** The two terms are closed, so they are [ws_term (fun _ => false)]. *)
Lemma c20_sri_A_closed : on_free_vars (fun _ => false) sri_A.
Proof. reflexivity. Qed.

Lemma c20_False_closed : on_free_vars (fun _ => false) iv_False.
Proof. reflexivity. Qed.

Definition c20_wsA : ws_term (fun _ => false) := exist _ sri_A c20_sri_A_closed.
Definition c20_wsF : ws_term (fun _ => false) := exist _ iv_False c20_False_closed.

Lemma c20_red_A_False : red si_Σ [] sri_A iv_False.
Proof. exact (red1_red _ _ _ _ (sri_beta [])). Qed.

Lemma c20_closed_red_A_False : closed_red si_Σ [] c20_wsA c20_wsF.
Proof.
  exact (closed_red_of (Σ := si_Σ) (Γ := []) (t := sri_A) eq_refl eq_refl c20_red_A_False).
Qed.

Lemma c20_False_irred : ¬ { t' & si_Σ ;;; [] |- iv_False ⇝ t'}.
Proof. intros [t' H]. eapply pgi_False_normal; eassumption. Qed.

Section NormalizationEtaInstances.

(* FORECAST-ONLY: the five classes the copy's section takes; delete each when its copy lands. *)
Context {V16 : ValForecastCopy16} {F16 : SRForecastCopy16} {F18 : SRForecastCopy18}
  {C16 : ClassifForecastCopy16} {P18 : ProgForecastCopy18}.

(* Base's normalization premise (by design, never discharged). *)
Context {nor : normalizing_flags} {nin : NormalizationInE si_Σ}.

Definition c20_A_typed : {A & si_Σ ;;; [] |-E sri_A : A} :=
  (si_P; iv_app_typed si_Σ [] localenv_nil).

Definition wh_normalizationE_inst :
  { v & whnf RedFlags.default si_Σ [] v * red si_Σ [] sri_A v} :=
  PCUICNormalizationEta.wh_normalizationE (Σ := si_Σ) (t := sri_A) si_wfE cli_axiom_free c20_A_typed.

Definition SN_to_WNE_inst : { v & eval si_Σ sri_A v} :=
  SN_to_WNE (Σ := si_Σ) (A := si_P) (t := sri_A) si_wfE cli_axiom_free c20_acc_sri_A
    (iv_app_typed si_Σ [] localenv_nil).

Definition wcbv_normalizationE_inst : { v & eval si_Σ sri_A v} :=
  wcbv_normalizationE (Σ := si_Σ) (A := si_P) (t := sri_A) si_wfE cli_axiom_free
    (iv_app_typed si_Σ [] localenv_nil).

Definition ws_wcbv_standardizationE_inst :
  {v' & eval si_Σ sri_A v' * (si_Σ ;;; [] ⊢ v' ⇝ iv_False)} :=
  ws_wcbv_standardizationE (Σ := si_Σ) (T := si_P) (t := c20_wsA) (v := c20_wsF)
    si_wfE cli_axiom_free (iv_app_typed si_Σ [] localenv_nil) c20_closed_red_A_False
    c20_False_irred.

Definition wcbv_standardizationE_inst :
  {v' & eval si_Σ sri_A v' * (si_Σ ;;; [] ⊢ v' ⇝ iv_False)} :=
  wcbv_standardizationE (Σ := si_Σ) (T := si_P) (t := sri_A) (v := iv_False)
    si_wfE cli_axiom_free (iv_app_typed si_Σ [] localenv_nil) c20_red_A_False c20_False_irred.

(** ** The compiled-form check against [CanonForecastCopy20] *)

Context {N20 : CanonForecastCopy20}.

(** The copy's lemma, at the five forecast classes, has EXACTLY the type of the forecast
    field. *)
Definition c20_lemma_has_field_type :
  ltac:(let T := type of (@PCUICCanonicityEta.wh_normalizationE N20) in exact T) :=
  @PCUICNormalizationEta.wh_normalizationE V16 F16 F18 C16 P18.

(** And the forecast field has EXACTLY the type of the copy's lemma at those classes. *)
Definition c20_field_has_lemma_type :
  ltac:(let T := type of (@PCUICNormalizationEta.wh_normalizationE V16 F16 F18 C16 P18) in exact T) :=
  @PCUICCanonicityEta.wh_normalizationE N20.

End NormalizationEtaInstances.
