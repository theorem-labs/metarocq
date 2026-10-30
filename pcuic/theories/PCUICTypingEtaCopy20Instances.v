(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the lemmas of [PCUICNormalizationEta] (T0 copy 20), and the
      compiled-form check against the forecast field of [PCUICCanonicityEta]

  **Section variables.** The two forecast classes the copy's section takes (T1's
  [SRForecastCopy18] and [ProgForecastCopy18]) and the normalization hypothesis
  [NormalizationInE]. [NormalizationInE] ([PCUICSNEta]) is base's [NormalizationIn] over
  [welltypedE]: a premise unprovable by design (it is strong normalization), inherited from
  base, where every one of these lemmas takes [NormalizationIn Σ]. It is not a forecast and is
  never discharged; it is the one hypothesis of this file with no satisfying instance, as in
  [PCUICCanonicityEtaInstances].

  **Non-degeneracy.**
  - The five lemmas with no first-order premise run on the β-redex
    [sri_A = (λx:Prop. x) (∀P:Prop. P)] in [si_Σ], typed at [Prop] ([iv_app_typed]), with
    [axiom_free si_Σ] ([cli_axiom_free]) and [wfE si_Σ] proved. The redex is neither a value
    nor [whnf], so each lemma must find the β step: [wh_normalizationE_inst] and
    [wcbv_normalizationE_inst] go through [progress_env_propE], and the two standardization
    instances reduce it to [∀P:Prop. P]. [SN_to_WNE_inst] takes a REAL accessibility proof
    ([c20_acc_sri_A]), not the normalization hypothesis.
  - The three first-order lemmas run in [fo_Σ] ([PCUICFirstorderEtaInstances]: the inductive
    [N] with [z] and [s]), on the zeta redex [c20_fo_let = let x := s z : N in x], which is
    not a value, and whose reduct [fo_sz = s z] is a first-order value. So
    [ws_wcbv_standardization_fstE_inst] and [wcbv_standardization_fstE_inst] must take the
    zeta step and then recognise the constructor application;
    [firstorder_value_irredE_inst] is the irreducibility of [s z] itself, which those two
    instances need as their premise.

  **The reduction behaviour of the two witnesses, proved here.** [sri_A] has exactly one
  [red1] reduct, [iv_False = ∀P:Prop. P] ([c20_sri_A_red1]), and [iv_False] has none
  ([PCUICProgressEtaInstances.pgi_False_normal]); [c20_fo_let] steps to [fo_sz]
  ([c20_fo_let_red]), and [fo_sz] is [red1]-normal, which here is NOT proved by inversion but
  obtained from [firstorder_value_irredE] on [fo_sz_value] — the instance of that lemma.

  **Compiled-form identity with the forecast field.** [PCUICCanonicityEta] carries base
  [wh_normalization] as the single field [wh_normalizationE] of its forecast class
  [CanonForecastCopy20]. [c20_lemma_has_field_type] and [c20_field_has_lemma_type] ascribe each
  of the two against the other's exact type, so the type checker decides the identity in both
  directions (the rule for a delete-and-import: identical types accept each other both ways).
  The lemma is applied to the two forecast classes first, which is the only difference between
  the two compiled types: the copy's section premises, which disappear when those classes are
  deleted. The name [wh_normalizationE] denotes two objects while this file is in scope (the
  field and the copy's lemma), so every reference to either is written qualified. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars
     PCUICTyping PCUICReduction PCUICConfluence PCUICWcbvEval PCUICNormal PCUICSafeLemmata
     PCUICSN PCUICClassification PCUICWellScopedCumulativity PCUICFirstorder
     PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaNotions PCUICClosedBodies
     PCUICClosedTypEta PCUICWellScopedCumulativityEta PCUICEtaA6
     PCUICCumulativitySpecEtaClosureInstances PCUICInversionEtaInstances PCUICSREtaInstances
     PCUICSNEta PCUICValidityEta PCUICSREta PCUICClassificationEta
     PCUICClassificationEtaInstances PCUICProgressEta PCUICProgressEtaInstances
     PCUICFirstorderEta PCUICFirstorderEtaInstances PCUICCanonicityEta PCUICNormalizationEta.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.
#[local] Existing Instance si_wfE.

(** ** The β-redex witness and its reduction behaviour, without any class *)

(** [sri_A = (λx:Prop. x) (∀P:Prop. P)] steps only to [∀P:Prop. P]. *)
Lemma c20_sri_A_red1 v : red1 si_Σ [] sri_A v -> v = iv_False.
Proof.
  unfold sri_A, iv_id. intros H. inv_red H.
  - reflexivity.
  - exfalso. eapply pgi_False_normal; eassumption.
Qed.

(** A [red1]-normal term is accessible for [cored]. *)
Lemma c20_acc_nf (Σ : global_env) t :
  (forall v, red1 Σ [] t v -> False) -> Acc (cored Σ []) t.
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

(** ** The first-order witness in [fo_Σ]: the zeta redex [let x := s z : N in x] *)

Definition c20_fo_let : term := tLetIn fo_na fo_sz fo_N (tRel 0).

Lemma c20_fo_axiom_free : axiom_free fo_Σ.
Proof.
  intros c decl h. exfalso. red in h. cbn in h.
  destruct h as [h|[h|h]]; [discriminate h|discriminate h|exact h].
Qed.

Lemma c20_fo_lookup :
  lookup_env fo_Σ (fo_ind.(inductive_mind)) = Some (InductiveDecl fo_mdecl).
Proof. reflexivity. Qed.

Lemma c20_fo_let_typed : fo_Σ ;;; [] |-E c20_fo_let : fo_N.
Proof.
  have hN := fo_N_typed [] localenv_nil.
  have hdef : lift_typing typingE fo_Σ [] (j_vdef fo_na fo_sz fo_N) :=
    iv_vdef fo_Σ [] fo_na fo_sz fo_N _ fo_sz_typed hN eq_refl.
  have hΓ' : wf_localE fo_Σ ([] ,, vdef fo_na fo_sz fo_N)
    by (apply localenv_cons_def; [exact localenv_nil|exact hdef]).
  have hlet : fo_Σ ;;; [] |-E c20_fo_let : tLetIn fo_na fo_sz fo_N fo_N :=
    typeE_LetIn _ _ fo_na fo_sz fo_N (tRel 0) fo_N hdef
      (typeE_Rel _ _ 0 (vdef fo_na fo_sz fo_N) hΓ' eq_refl).
  eapply (type_ws_cumul_pbE (Σ := fo_Σ) (cbΣ := wfE_ClosedBodies fo_Σ (wfΣ := fo_wfE))
            (pb := Cumul) _ hlet).
  - exact (fo_N_isType [] localenv_nil).
  - eapply (red_ws_cumul_pbE (Σ := fo_Σ) (wfΣ := wfE_ClosedBodies fo_Σ (wfΣ := fo_wfE))).
    constructor; [reflexivity|exact (type_is_open_termE (Σ := fo_Σ) (wfΣ := fo_wfE) hlet)|].
    apply rt_step. apply red_zeta.
Qed.

Lemma c20_fo_let_red1 : red1 fo_Σ [] c20_fo_let fo_sz.
Proof. exact (red_zeta fo_Σ [] fo_na fo_sz fo_N (tRel 0)). Qed.

Lemma c20_fo_let_red : red fo_Σ [] c20_fo_let fo_sz.
Proof. exact (red1_red _ _ _ _ c20_fo_let_red1). Qed.

Lemma c20_fo_let_closed : on_free_vars (fun _ => false) c20_fo_let.
Proof. reflexivity. Qed.

Lemma c20_fo_sz_closed : on_free_vars (fun _ => false) fo_sz.
Proof. reflexivity. Qed.

Definition c20_ws_fo_let : ws_term (fun _ => false) := exist _ c20_fo_let c20_fo_let_closed.
Definition c20_ws_fo_sz : ws_term (fun _ => false) := exist _ fo_sz c20_fo_sz_closed.

Lemma c20_closed_red_fo : closed_red fo_Σ [] c20_ws_fo_let c20_ws_fo_sz.
Proof.
  exact (closed_red_of (Σ := fo_Σ) (Γ := []) (t := c20_fo_let) eq_refl eq_refl c20_fo_let_red).
Qed.

Section NormalizationEtaInstances.

(* FORECAST-ONLY: the two classes the copy's section takes; delete each when its copy lands. *)
Context {F18 : SRForecastCopy18} {P18 : ProgForecastCopy18}.

(** [s z] is [red1]-normal, by the copy's own [firstorder_value_irredE] on [fo_sz_value]. *)
Lemma c20_fo_sz_irred : ¬ { t' & fo_Σ ;;; [] |- fo_sz ⇝ t'}.
Proof.
  intros [t' H]. eapply firstorder_value_irredE; [exact fo_sz_value|exact H].
Qed.

Definition firstorder_value_irredE_inst : forall t', red1 fo_Σ [] fo_sz t' -> False :=
  fun t' H => firstorder_value_irredE fo_Σ fo_sz t' fo_sz_value H.

Definition c20_A_typed : {A & si_Σ ;;; [] |-E sri_A : A} :=
  (si_P; iv_app_typed si_Σ [] localenv_nil).

Definition wh_normalizationE_inst :
  { v & whnf RedFlags.default si_Σ [] v * red si_Σ [] sri_A v} :=
  PCUICNormalizationEta.wh_normalizationE (Σ := si_Σ) (t := sri_A) si_wfE cli_axiom_free
    c20_A_typed.

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

Definition ws_wcbv_standardization_fstE_inst : eval fo_Σ c20_fo_let fo_sz :=
  ws_wcbv_standardization_fstE (Σ := fo_Σ) (i := fo_ind) (u := []) (args := []) (mind := fo_mdecl)
    (t := c20_ws_fo_let) (v := c20_ws_fo_sz) fo_wfE c20_fo_axiom_free c20_fo_let_typed
    c20_fo_lookup fo_firstorder c20_closed_red_fo c20_fo_sz_irred.

Definition wcbv_standardization_fstE_inst : eval fo_Σ c20_fo_let fo_sz :=
  wcbv_standardization_fstE (Σ := fo_Σ) (i := fo_ind) (u := []) (args := []) (mind := fo_mdecl)
    (t := c20_fo_let) (v := fo_sz) fo_wfE c20_fo_axiom_free c20_fo_let_typed c20_fo_lookup
    fo_firstorder c20_fo_let_red c20_fo_sz_irred.

(** ** The compiled-form check against [CanonForecastCopy20] *)

Context {N20 : CanonForecastCopy20}.

(** The copy's lemma, at the two forecast classes, has EXACTLY the type of the forecast
    field. *)
Definition c20_lemma_has_field_type :
  ltac:(let T := type of (@PCUICCanonicityEta.wh_normalizationE N20) in exact T) :=
  @PCUICNormalizationEta.wh_normalizationE F18 P18.

(** And the forecast field has EXACTLY the type of the copy's lemma at those classes. *)
Definition c20_field_has_lemma_type :
  ltac:(let T := type of (@PCUICNormalizationEta.wh_normalizationE F18 P18) in exact T) :=
  @PCUICCanonicityEta.wh_normalizationE N20.

End NormalizationEtaInstances.
