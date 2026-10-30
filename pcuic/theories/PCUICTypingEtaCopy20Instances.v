(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the lemmas of [PCUICNormalizationEta]

  **Section variables.** The normalization hypothesis [NormalizationInE] only.
  [NormalizationInE] ([PCUICSNEta]) is base's [NormalizationIn] over [welltypedE]: a premise
  unprovable by design (it is strong normalization), inherited from base, where every one of
  these lemmas takes [NormalizationIn Σ]. It is not a forecast and is never discharged; it is
  the one hypothesis of this file with no satisfying instance.

  **The η content, and how it is tagged.** Every instance below carries a tag comment of the
  form [INSTANCE NONDEGEN <lemma>] or [INSTANCE NOT-BUILT: <reason>] directly above it. A
  NONDEGEN tag names a compiled lemma, [<instance>_nondeg], whose statement holds the η step
  the instance runs on: the two witness terms, that they are DIFFERENT terms, that they are
  related by [convSpecE] (a relation whose only rule for this pair is [cumul_eta_l]), and the
  typing the instance needs on both sides of that step.

  - Eight of the nine instances run on a subject whose typing passes through one η step.
    In [si_Σ] ([PCUICCumulativitySpecEtaClosureInstances]: the inductive [I (A : Prop) : Prop])
    the step is [I ≡ λA:Prop. I A], between the inductive's type former and its η expansion,
    which are related by no other rule: both are [red1]-normal and have different heads. The
    subject is [c20_eta_t = (λ_ : T (λA:Prop. I A). ∀P:Prop. P) idt], where
    [T F := ∀ G : (Prop → Prop) → Prop. G F → G F] and [idt = λG. λy : G I. y] is typed at
    [T I]; typing [c20_eta_t] therefore needs [T I ≡ T (λA:Prop. I A)], i.e. the η step under
    the variable [G]. The subject is a closed β-redex, neither a value nor [whnf], and its one
    reduct is [∀P:Prop. P], which is [red1]-normal; [SN_to_WNE_inst] takes a REAL accessibility
    proof ([c20_eta_acc]), not the normalization hypothesis.
  - The two first-order standardization instances run on the same shape in [fo_Σ]
    ([PCUICFirstorderEtaInstances]: the inductive [N] with [z] and [s]), where the η step is
    [s ≡ λx:N. s x] on the constructor [s : N → N] and the subject
    [c20_fo_t = (λ_ : T (λx:N. s x). s z) idt] is typed at [N], the first-order inductive the
    two lemmas require; it reduces to the first-order value [s z], which is irreducible.
  - [wcbv_red1_evalE_inst] has no typing premise: its only typed premise is [wfE Σ], so it runs
    in [PCUICTypingEtaCopy17Instances.c17_Σ], whose environment declares a constant whose type
    is typed only through an η step ([F ≡ λy:Prop. F y] under a variable [F]).
  - [firstorder_value_irredE_inst] is NOT BUILT for η; its tag carries the cost. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars
     PCUICTyping PCUICReduction PCUICConfluence PCUICWcbvEval PCUICNormal PCUICSafeLemmata
     PCUICSN PCUICClassification PCUICWellScopedCumulativity PCUICFirstorder PCUICProgress
     PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaNotions PCUICClosedBodies
     PCUICClosedTypEta PCUICWellScopedCumulativityEta PCUICEtaA6
     PCUICCumulativitySpecEtaClosureInstances PCUICInversionEtaInstances PCUICSREtaInstances
     PCUICEtaC1b PCUICAritiesEta
     PCUICSNEta PCUICValidityEta PCUICSREta PCUICClassificationEta
     PCUICClassificationEtaInstances PCUICProgressEta PCUICProgressEtaInstances
     PCUICFirstorderEta PCUICFirstorderEtaInstances PCUICNormalizationEta.
From MetaRocq.PCUIC Require PCUICTypingEtaCopy17Instances.
From Equations.Type Require Import Relation.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.
#[local] Existing Instance si_wfE.

(** ** Generic normality pieces *)

Lemma c20_Ind_normal (S : global_env) Γ i u v :
  MetaRocq.PCUIC.PCUICReduction.red1 S Γ (tInd i u) v -> False.
Proof. intros H. inv_red H. Qed.

Lemma c20_Rel_normal (S : global_env) (Γ : context) n v :
  option_map decl_body (nth_error Γ n) = Some None ->
  MetaRocq.PCUIC.PCUICReduction.red1 S Γ (tRel n) v -> False.
Proof.
  intros hn H. inv_red H.
  match goal with e : option_map decl_body _ = _ |- _ => rewrite hn in e; discriminate e end.
Qed.

(** A [red1]-normal term is accessible for [cored]. *)
Lemma c20_acc_nf (Σ : global_env) t :
  (forall v, MetaRocq.PCUIC.PCUICReduction.red1 Σ [] t v -> False) -> Acc (cored Σ []) t.
Proof.
  intros h. constructor. intros y Hy. exfalso.
  induction Hy; eauto.
Qed.

Lemma c20_acc_False : Acc (cored si_Σ []) iv_False.
Proof. apply c20_acc_nf. intros v H. eapply pgi_False_normal; eassumption. Qed.

Lemma c20_False_closed : on_free_vars (fun _ => false) iv_False.
Proof. reflexivity. Qed.

Definition c20_wsF : ws_term (fun _ => false) :=
  @exist term (on_free_vars (fun _ => false)) iv_False c20_False_closed.

Lemma c20_False_irred : ¬ { t' & si_Σ ;;; [] |- iv_False ⇝ t'}.
Proof. intros [t' H]. eapply pgi_False_normal; eassumption. Qed.

(** ** The η witness in [si_Σ]

  [I] and its η expansion, and the type [T F := ∀ G : (Prop → Prop) → Prop. G F → G F]. *)

Definition c20_eta_I : term := tInd si_ind [].
Definition c20_eta_Ieta : term := tLambda si_na si_P (tApp (tInd si_ind []) (tRel 0)).

Definition c20_eta_T (F : term) : term :=
  tProd si_na iv_K (tProd si_na (tApp (tRel 0) F) (tApp (tRel 1) F)).

Definition c20_eta_idt : term :=
  tLambda si_na iv_K (tLambda si_na (tApp (tRel 0) c20_eta_I) (tRel 0)).

(** The subject: a closed β-redex whose argument is typed only through the η step. *)
Definition c20_eta_t : term :=
  tApp (tLambda si_na (c20_eta_T c20_eta_Ieta) iv_False) c20_eta_idt.

Lemma c20_eta_I_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E c20_eta_I : iv_PP.
Proof. intros h. exact (iv_ind_typed Γ h). Qed.

Lemma c20_eta_Ieta_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E c20_eta_Ieta : iv_PP.
Proof.
  intros h. unfold c20_eta_Ieta, iv_PP. apply typeE_Lambda.
  - exact (iv_vass si_Σ Γ si_na si_P _ (iv_P_typed si_Σ Γ h) Corelib.Init.Logic.eq_refl).
  - exact (iv_IX_typed _ (tRel 0) (iv_wf_P si_Σ Γ h)
             (typeE_Rel _ _ 0 (vass si_na si_P) (iv_wf_P si_Σ Γ h) Corelib.Init.Logic.eq_refl)).
Qed.

Lemma c20_eta_T_typed (F : term)
  (hF : forall Γ, wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E F : iv_PP) (Γ : context) :
  wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E c20_eta_T F : si_P.
Proof.
  intros h. unfold c20_eta_T.
  have wK : wf_localE si_Σ (Γ ,, vass si_na iv_K) :=
    iv_wf_vass si_Σ Γ si_na iv_K _ h (iv_K_typed Γ h) Corelib.Init.Logic.eq_refl.
  have hGF : si_Σ ;;; (Γ ,, vass si_na iv_K) |-E tApp (tRel 0) F : si_P :=
    typeE_App _ _ (tRel 0) si_na iv_PP si_P _ F (iv_K_typed _ wK)
      (typeE_Rel _ _ 0 (vass si_na iv_K) wK Corelib.Init.Logic.eq_refl) (hF _ wK).
  have wGF : wf_localE si_Σ ((Γ ,, vass si_na iv_K) ,, vass si_na (tApp (tRel 0) F)) :=
    iv_wf_vass si_Σ _ si_na (tApp (tRel 0) F) sProp wK hGF Corelib.Init.Logic.eq_refl.
  apply (typeE_Prod _ _ si_na iv_K _ (Sort.sort_of_product iv_sPP (Sort.super sProp)) sProp).
  - exact (iv_vass_s si_Σ Γ si_na iv_K _ (iv_K_typed Γ h) Corelib.Init.Logic.eq_refl).
  - apply (typeE_Prod _ _ si_na (tApp (tRel 0) F) _ sProp sProp).
    + exact (iv_vass_s si_Σ _ si_na (tApp (tRel 0) F) sProp hGF Corelib.Init.Logic.eq_refl).
    + exact (typeE_App _ _ (tRel 1) si_na iv_PP si_P _ F (iv_K_typed _ wGF)
               (typeE_Rel _ _ 1 (vass si_na iv_K) wGF Corelib.Init.Logic.eq_refl) (hF _ wGF)).
Qed.

Lemma c20_eta_idt_typed (Γ : context) :
  wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E c20_eta_idt : c20_eta_T c20_eta_I.
Proof.
  intros h. unfold c20_eta_idt, c20_eta_T.
  have wK : wf_localE si_Σ (Γ ,, vass si_na iv_K) :=
    iv_wf_vass si_Σ Γ si_na iv_K _ h (iv_K_typed Γ h) Corelib.Init.Logic.eq_refl.
  have hGI : si_Σ ;;; (Γ ,, vass si_na iv_K) |-E tApp (tRel 0) c20_eta_I : si_P :=
    typeE_App _ _ (tRel 0) si_na iv_PP si_P _ c20_eta_I (iv_K_typed _ wK)
      (typeE_Rel _ _ 0 (vass si_na iv_K) wK Corelib.Init.Logic.eq_refl) (c20_eta_I_typed _ wK).
  have wGI : wf_localE si_Σ ((Γ ,, vass si_na iv_K) ,, vass si_na (tApp (tRel 0) c20_eta_I)) :=
    iv_wf_vass si_Σ _ si_na (tApp (tRel 0) c20_eta_I) sProp wK hGI Corelib.Init.Logic.eq_refl.
  apply typeE_Lambda.
  - exact (iv_vass si_Σ Γ si_na iv_K _ (iv_K_typed Γ h) Corelib.Init.Logic.eq_refl).
  - apply typeE_Lambda.
    + exact (iv_vass si_Σ _ si_na (tApp (tRel 0) c20_eta_I) sProp hGI Corelib.Init.Logic.eq_refl).
    + exact (typeE_Rel _ _ 0 (vass si_na (tApp (tRel 0) c20_eta_I)) wGI Corelib.Init.Logic.eq_refl).
Qed.

(** The η step itself: [I] against [λA:Prop. I A]. *)
Lemma c20_eta_conv (Γ : context) : convSpecE si_Σ Γ c20_eta_I c20_eta_Ieta.
Proof.
  unfold convSpecE, c20_eta_I, c20_eta_Ieta.
  apply cumulE_Sym.
  exact (cumulSpecE_eta_contract si_Σ Γ Conv si_na si_P (tInd si_ind [])).
Qed.

Lemma c20_eta_spec : cumulSpecE si_Σ [] (c20_eta_T c20_eta_I) (c20_eta_T c20_eta_Ieta).
Proof.
  unfold cumulSpecE, c20_eta_T.
  apply cumulE_Prod; [reflexivity|apply cumulE_Refl|].
  apply cumulE_Prod; [reflexivity| |].
  - apply cumulE_App; [apply cumulE_Refl|apply c20_eta_conv].
  - apply cumulE_App; [apply cumulE_Refl|apply c20_eta_conv].
Qed.

(** The argument of the β-redex, at the η-expanded type. *)
Lemma c20_eta_idt_eta_typed : si_Σ ;;; [] |-E c20_eta_idt : c20_eta_T c20_eta_Ieta.
Proof.
  exact (typeE_Cumul _ _ c20_eta_idt (c20_eta_T c20_eta_I) (c20_eta_T c20_eta_Ieta) sProp
           (c20_eta_idt_typed [] localenv_nil)
           (c20_eta_T_typed c20_eta_Ieta c20_eta_Ieta_typed [] localenv_nil)
           c20_eta_spec).
Qed.

Lemma c20_eta_t_typed : si_Σ ;;; [] |-E c20_eta_t : si_P.
Proof.
  have hT := c20_eta_T_typed c20_eta_Ieta c20_eta_Ieta_typed [] localenv_nil.
  have wT : wf_localE si_Σ ([] ,, vass si_na (c20_eta_T c20_eta_Ieta)) :=
    iv_wf_vass si_Σ [] si_na (c20_eta_T c20_eta_Ieta) sProp localenv_nil hT
      Corelib.Init.Logic.eq_refl.
  have hlam : si_Σ ;;; [] |-E tLambda si_na (c20_eta_T c20_eta_Ieta) iv_False
                : tProd si_na (c20_eta_T c20_eta_Ieta) si_P.
  { apply typeE_Lambda.
    - exact (iv_vass si_Σ [] si_na (c20_eta_T c20_eta_Ieta) sProp hT Corelib.Init.Logic.eq_refl).
    - exact (iv_False_typed si_Σ _ wT). }
  have hprod : si_Σ ;;; [] |-E tProd si_na (c20_eta_T c20_eta_Ieta) si_P
                 : tSort (Sort.sort_of_product sProp (Sort.super sProp)).
  { apply typeE_Prod.
    - exact (iv_vass_s si_Σ [] si_na (c20_eta_T c20_eta_Ieta) sProp hT Corelib.Init.Logic.eq_refl).
    - exact (iv_P_typed si_Σ _ wT). }
  exact (typeE_App _ _ (tLambda si_na (c20_eta_T c20_eta_Ieta) iv_False) si_na
           (c20_eta_T c20_eta_Ieta) si_P _ c20_eta_idt hprod hlam c20_eta_idt_eta_typed).
Qed.

Lemma c20_eta_t_red1 : MetaRocq.PCUIC.PCUICReduction.red1 si_Σ [] c20_eta_t iv_False.
Proof.
  exact (MetaRocq.PCUIC.PCUICReduction.red_beta si_Σ [] si_na (c20_eta_T c20_eta_Ieta) iv_False
           c20_eta_idt).
Qed.

(** ** The subject's reduction behaviour: one reduct, and accessibility *)

Lemma c20_PP_normal (S : global_env) Γ v :
  MetaRocq.PCUIC.PCUICReduction.red1 S Γ iv_PP v -> False.
Proof.
  unfold iv_PP. intros H. inv_red H.
  - eapply red_normal_Sort; eassumption.
  - eapply red_normal_Sort; eassumption.
Qed.

Lemma c20_K_normal (S : global_env) Γ v :
  MetaRocq.PCUIC.PCUICReduction.red1 S Γ iv_K v -> False.
Proof.
  unfold iv_K. intros H. inv_red H.
  - eapply c20_PP_normal; eassumption.
  - eapply red_normal_Sort; eassumption.
Qed.

Lemma c20_eta_Ieta_normal (S : global_env) Γ v :
  MetaRocq.PCUIC.PCUICReduction.red1 S Γ c20_eta_Ieta v -> False.
Proof.
  unfold c20_eta_Ieta. revert v. apply red_normal_lam.
  - intros w. apply red_normal_Sort.
  - intros w H. inv_red H.
    + eapply c20_Ind_normal; eassumption.
    + eapply red_normal_Rel0; eassumption.
Qed.

Lemma c20_eta_I_normal (S : global_env) Γ v :
  MetaRocq.PCUIC.PCUICReduction.red1 S Γ c20_eta_I v -> False.
Proof. unfold c20_eta_I. apply c20_Ind_normal. Qed.

Lemma c20_eta_T_normal (F : term)
  (hF : forall (S : global_env) Γ v, MetaRocq.PCUIC.PCUICReduction.red1 S Γ F v -> False)
  (S : global_env) Γ v : MetaRocq.PCUIC.PCUICReduction.red1 S Γ (c20_eta_T F) v -> False.
Proof.
  unfold c20_eta_T. intros H. inv_red H.
  - eapply c20_K_normal; eassumption.
  - match goal with h : MetaRocq.PCUIC.PCUICReduction.red1 _ _ (tProd _ _ _) _ |- _ => inv_red h end.
    + match goal with h : MetaRocq.PCUIC.PCUICReduction.red1 _ _ (tApp _ _) _ |- _ => inv_red h end.
      * eapply red_normal_Rel0; eassumption.
      * eapply hF; eassumption.
    + match goal with h : MetaRocq.PCUIC.PCUICReduction.red1 _ _ (tApp _ _) _ |- _ => inv_red h end.
      * exact (c20_Rel_normal _ ((Γ ,, vass si_na iv_K) ,, vass si_na (tApp (tRel 0) F)) 1 _
                 Corelib.Init.Logic.eq_refl ltac:(eassumption)).
      * eapply hF; eassumption.
Qed.

Lemma c20_eta_idt_normal (S : global_env) Γ v :
  MetaRocq.PCUIC.PCUICReduction.red1 S Γ c20_eta_idt v -> False.
Proof.
  unfold c20_eta_idt. revert v. apply red_normal_lam.
  - intros w. apply c20_K_normal.
  - intros w. apply red_normal_lam.
    + intros x H. inv_red H.
      * eapply red_normal_Rel0; eassumption.
      * eapply c20_eta_I_normal; eassumption.
    + intros x. apply red_normal_Rel0.
Qed.

Lemma c20_eta_t_red1_inv v :
  MetaRocq.PCUIC.PCUICReduction.red1 si_Σ [] c20_eta_t v -> v = iv_False.
Proof.
  unfold c20_eta_t. intros H. inv_red H.
  - reflexivity.
  - exfalso. eapply (red_normal_lam si_Σ [] si_na (c20_eta_T c20_eta_Ieta) iv_False
                       (fun w => c20_eta_T_normal c20_eta_Ieta
                                   (fun S Γ x => c20_eta_Ieta_normal S Γ x) si_Σ [] w)
                       (fun w => pgi_False_normal si_Σ _ w)); eassumption.
  - exfalso. eapply c20_eta_idt_normal; eassumption.
Qed.

Lemma c20_eta_cored y : cored si_Σ [] y c20_eta_t -> y = iv_False.
Proof.
  intros Hy. remember c20_eta_t as t0 eqn:Et0. revert Et0.
  induction Hy; intros Et0; subst.
  - now apply c20_eta_t_red1_inv.
  - exfalso. specialize (IHHy Corelib.Init.Logic.eq_refl). subst v.
    eapply pgi_False_normal; eassumption.
Qed.

Lemma c20_eta_acc : Acc (cored si_Σ []) c20_eta_t.
Proof.
  constructor. intros y Hy. rewrite (c20_eta_cored y Hy). exact c20_acc_False.
Qed.

Lemma c20_eta_t_closed : on_free_vars (fun _ => false) c20_eta_t.
Proof. reflexivity. Qed.

Definition c20_ws_eta_t : ws_term (fun _ => false) :=
  @exist term (on_free_vars (fun _ => false)) c20_eta_t c20_eta_t_closed.

Lemma c20_eta_red_t_False : red si_Σ [] c20_eta_t iv_False.
Proof. exact (red1_red _ _ _ _ c20_eta_t_red1). Qed.

Lemma c20_closed_red_eta_t : closed_red si_Σ [] c20_ws_eta_t c20_wsF.
Proof.
  exact (closed_red_of (Σ := si_Σ) (Γ := []) (t := c20_eta_t) Corelib.Init.Logic.eq_refl
           Corelib.Init.Logic.eq_refl c20_eta_red_t_False).
Qed.

(** ** The η witness in [fo_Σ]: the same shape on the constructor [s : N → N] *)

Definition c20_fo_s : term := tConstruct fo_ind 1 [].
Definition c20_fo_seta : term := tLambda fo_na fo_N (tApp (tConstruct fo_ind 1 []) (tRel 0)).
Definition c20_fo_NN : term := tProd fo_na fo_N fo_N.
Definition c20_fo_K : term := tProd fo_na c20_fo_NN si_P.

Definition c20_fo_T (F : term) : term :=
  tProd fo_na c20_fo_K (tProd fo_na (tApp (tRel 0) F) (tApp (tRel 1) F)).

Definition c20_fo_idt : term :=
  tLambda fo_na c20_fo_K (tLambda fo_na (tApp (tRel 0) c20_fo_s) (tRel 0)).

Definition c20_fo_t : term := tApp (tLambda fo_na (c20_fo_T c20_fo_seta) fo_sz) c20_fo_idt.

Lemma c20_fo_sz_typed (Γ : context) : wf_localE fo_Σ Γ -> fo_Σ ;;; Γ |-E fo_sz : fo_N.
Proof.
  intros h.
  exact (typeE_App _ _ _ fo_na fo_N fo_N _ _ (fo_NN_typed Γ h) (fo_s_typed Γ h) (fo_z_typed Γ h)).
Qed.

Lemma c20_fo_s_typed (Γ : context) : wf_localE fo_Σ Γ -> fo_Σ ;;; Γ |-E c20_fo_s : c20_fo_NN.
Proof. intros h. exact (fo_s_typed Γ h). Qed.

Lemma c20_fo_seta_typed (Γ : context) : wf_localE fo_Σ Γ -> fo_Σ ;;; Γ |-E c20_fo_seta : c20_fo_NN.
Proof.
  intros h. unfold c20_fo_seta, c20_fo_NN. apply typeE_Lambda.
  - exact (iv_vass fo_Σ Γ fo_na fo_N _ (fo_N_typed Γ h) Corelib.Init.Logic.eq_refl).
  - have w : wf_localE fo_Σ (Γ ,, vass fo_na fo_N) :=
      iv_wf_vass fo_Σ Γ fo_na fo_N _ h (fo_N_typed Γ h) Corelib.Init.Logic.eq_refl.
    exact (typeE_App _ _ (tConstruct fo_ind 1 []) fo_na fo_N fo_N _ (tRel 0)
             (fo_NN_typed _ w) (fo_s_typed _ w)
             (typeE_Rel _ _ 0 (vass fo_na fo_N) w Corelib.Init.Logic.eq_refl)).
Qed.

Lemma c20_fo_K_typed (Γ : context) : wf_localE fo_Σ Γ ->
  fo_Σ ;;; Γ |-E c20_fo_K
    : tSort (Sort.sort_of_product (Sort.sort_of_product Sort.type1 Sort.type1) (Sort.super sProp)).
Proof.
  intros h. unfold c20_fo_K. apply typeE_Prod.
  - exact (iv_vass_s fo_Σ Γ fo_na c20_fo_NN _ (fo_NN_typed Γ h) Corelib.Init.Logic.eq_refl).
  - exact (iv_P_typed fo_Σ _ (iv_wf_vass fo_Σ Γ fo_na c20_fo_NN _ h (fo_NN_typed Γ h)
                               Corelib.Init.Logic.eq_refl)).
Qed.

Lemma c20_fo_T_typed (F : term)
  (hF : forall Γ, wf_localE fo_Σ Γ -> fo_Σ ;;; Γ |-E F : c20_fo_NN) (Γ : context) :
  wf_localE fo_Σ Γ -> fo_Σ ;;; Γ |-E c20_fo_T F : si_P.
Proof.
  intros h. unfold c20_fo_T.
  have wK : wf_localE fo_Σ (Γ ,, vass fo_na c20_fo_K) :=
    iv_wf_vass fo_Σ Γ fo_na c20_fo_K _ h (c20_fo_K_typed Γ h) Corelib.Init.Logic.eq_refl.
  have hGF : fo_Σ ;;; (Γ ,, vass fo_na c20_fo_K) |-E tApp (tRel 0) F : si_P :=
    typeE_App _ _ (tRel 0) fo_na c20_fo_NN si_P _ F (c20_fo_K_typed _ wK)
      (typeE_Rel _ _ 0 (vass fo_na c20_fo_K) wK Corelib.Init.Logic.eq_refl) (hF _ wK).
  have wGF : wf_localE fo_Σ ((Γ ,, vass fo_na c20_fo_K) ,, vass fo_na (tApp (tRel 0) F)) :=
    iv_wf_vass fo_Σ _ fo_na (tApp (tRel 0) F) sProp wK hGF Corelib.Init.Logic.eq_refl.
  apply (typeE_Prod _ _ fo_na c20_fo_K _
           (Sort.sort_of_product (Sort.sort_of_product Sort.type1 Sort.type1) (Sort.super sProp))
           sProp).
  - exact (iv_vass_s fo_Σ Γ fo_na c20_fo_K _ (c20_fo_K_typed Γ h) Corelib.Init.Logic.eq_refl).
  - apply (typeE_Prod _ _ fo_na (tApp (tRel 0) F) _ sProp sProp).
    + exact (iv_vass_s fo_Σ _ fo_na (tApp (tRel 0) F) sProp hGF Corelib.Init.Logic.eq_refl).
    + exact (typeE_App _ _ (tRel 1) fo_na c20_fo_NN si_P _ F (c20_fo_K_typed _ wGF)
               (typeE_Rel _ _ 1 (vass fo_na c20_fo_K) wGF Corelib.Init.Logic.eq_refl) (hF _ wGF)).
Qed.

Lemma c20_fo_idt_typed (Γ : context) :
  wf_localE fo_Σ Γ -> fo_Σ ;;; Γ |-E c20_fo_idt : c20_fo_T c20_fo_s.
Proof.
  intros h. unfold c20_fo_idt, c20_fo_T.
  have wK : wf_localE fo_Σ (Γ ,, vass fo_na c20_fo_K) :=
    iv_wf_vass fo_Σ Γ fo_na c20_fo_K _ h (c20_fo_K_typed Γ h) Corelib.Init.Logic.eq_refl.
  have hGs : fo_Σ ;;; (Γ ,, vass fo_na c20_fo_K) |-E tApp (tRel 0) c20_fo_s : si_P :=
    typeE_App _ _ (tRel 0) fo_na c20_fo_NN si_P _ c20_fo_s (c20_fo_K_typed _ wK)
      (typeE_Rel _ _ 0 (vass fo_na c20_fo_K) wK Corelib.Init.Logic.eq_refl) (c20_fo_s_typed _ wK).
  have wGs : wf_localE fo_Σ ((Γ ,, vass fo_na c20_fo_K) ,, vass fo_na (tApp (tRel 0) c20_fo_s)) :=
    iv_wf_vass fo_Σ _ fo_na (tApp (tRel 0) c20_fo_s) sProp wK hGs Corelib.Init.Logic.eq_refl.
  apply typeE_Lambda.
  - exact (iv_vass fo_Σ Γ fo_na c20_fo_K _ (c20_fo_K_typed Γ h) Corelib.Init.Logic.eq_refl).
  - apply typeE_Lambda.
    + exact (iv_vass fo_Σ _ fo_na (tApp (tRel 0) c20_fo_s) sProp hGs Corelib.Init.Logic.eq_refl).
    + exact (typeE_Rel _ _ 0 (vass fo_na (tApp (tRel 0) c20_fo_s)) wGs Corelib.Init.Logic.eq_refl).
Qed.

Lemma c20_fo_conv (Γ : context) : convSpecE fo_Σ Γ c20_fo_s c20_fo_seta.
Proof.
  unfold convSpecE, c20_fo_s, c20_fo_seta.
  apply cumulE_Sym.
  exact (cumulSpecE_eta_contract fo_Σ Γ Conv fo_na fo_N (tConstruct fo_ind 1 [])).
Qed.

Lemma c20_fo_spec : cumulSpecE fo_Σ [] (c20_fo_T c20_fo_s) (c20_fo_T c20_fo_seta).
Proof.
  unfold cumulSpecE, c20_fo_T.
  apply cumulE_Prod; [reflexivity|apply cumulE_Refl|].
  apply cumulE_Prod; [reflexivity| |].
  - apply cumulE_App; [apply cumulE_Refl|apply c20_fo_conv].
  - apply cumulE_App; [apply cumulE_Refl|apply c20_fo_conv].
Qed.

Lemma c20_fo_idt_eta_typed : fo_Σ ;;; [] |-E c20_fo_idt : c20_fo_T c20_fo_seta.
Proof.
  exact (typeE_Cumul _ _ c20_fo_idt (c20_fo_T c20_fo_s) (c20_fo_T c20_fo_seta) sProp
           (c20_fo_idt_typed [] localenv_nil)
           (c20_fo_T_typed c20_fo_seta c20_fo_seta_typed [] localenv_nil)
           c20_fo_spec).
Qed.

Lemma c20_fo_t_typed : fo_Σ ;;; [] |-E c20_fo_t : mkApps (tInd fo_ind []) [].
Proof.
  have hT := c20_fo_T_typed c20_fo_seta c20_fo_seta_typed [] localenv_nil.
  have wT : wf_localE fo_Σ ([] ,, vass fo_na (c20_fo_T c20_fo_seta)) :=
    iv_wf_vass fo_Σ [] fo_na (c20_fo_T c20_fo_seta) sProp localenv_nil hT
      Corelib.Init.Logic.eq_refl.
  have hlam : fo_Σ ;;; [] |-E tLambda fo_na (c20_fo_T c20_fo_seta) fo_sz
                : tProd fo_na (c20_fo_T c20_fo_seta) fo_N.
  { apply typeE_Lambda.
    - exact (iv_vass fo_Σ [] fo_na (c20_fo_T c20_fo_seta) sProp hT Corelib.Init.Logic.eq_refl).
    - exact (c20_fo_sz_typed _ wT). }
  have hprod : fo_Σ ;;; [] |-E tProd fo_na (c20_fo_T c20_fo_seta) fo_N
                 : tSort (Sort.sort_of_product sProp Sort.type1).
  { apply typeE_Prod.
    - exact (iv_vass_s fo_Σ [] fo_na (c20_fo_T c20_fo_seta) sProp hT Corelib.Init.Logic.eq_refl).
    - exact (fo_N_typed _ wT). }
  exact (typeE_App _ _ (tLambda fo_na (c20_fo_T c20_fo_seta) fo_sz) fo_na
           (c20_fo_T c20_fo_seta) fo_N _ c20_fo_idt hprod hlam c20_fo_idt_eta_typed).
Qed.

Lemma c20_fo_t_red1 : MetaRocq.PCUIC.PCUICReduction.red1 fo_Σ [] c20_fo_t fo_sz.
Proof.
  exact (MetaRocq.PCUIC.PCUICReduction.red_beta fo_Σ [] fo_na (c20_fo_T c20_fo_seta) fo_sz
           c20_fo_idt).
Qed.

Lemma c20_fo_t_red : red fo_Σ [] c20_fo_t fo_sz.
Proof. exact (red1_red _ _ _ _ c20_fo_t_red1). Qed.

Lemma c20_fo_axiom_free : axiom_free fo_Σ.
Proof.
  intros c decl h. exfalso. red in h. cbn in h.
  destruct h as [h|h]; [discriminate h|exact h].
Qed.

Lemma c20_fo_lookup :
  lookup_env fo_Σ (fo_ind.(inductive_mind)) = Some (InductiveDecl fo_mdecl).
Proof. reflexivity. Qed.

Lemma c20_fo_t_closed : on_free_vars (fun _ => false) c20_fo_t.
Proof. reflexivity. Qed.

Lemma c20_fo_sz_closed : on_free_vars (fun _ => false) fo_sz.
Proof. reflexivity. Qed.

Definition c20_ws_fo_t : ws_term (fun _ => false) :=
  @exist term (on_free_vars (fun _ => false)) c20_fo_t c20_fo_t_closed.
Definition c20_ws_fo_sz : ws_term (fun _ => false) :=
  @exist term (on_free_vars (fun _ => false)) fo_sz c20_fo_sz_closed.

Lemma c20_closed_red_fo : closed_red fo_Σ [] c20_ws_fo_t c20_ws_fo_sz.
Proof.
  exact (closed_red_of (Σ := fo_Σ) (Γ := []) (t := c20_fo_t) Corelib.Init.Logic.eq_refl
           Corelib.Init.Logic.eq_refl c20_fo_t_red).
Qed.

(** ** The η content of each witness, as a compiled statement *)

Lemma c20_eta_core :
  ((c20_eta_I <> c20_eta_Ieta) * convSpecE si_Σ [] c20_eta_I c20_eta_Ieta *
   (c20_eta_T c20_eta_I <> c20_eta_T c20_eta_Ieta) *
   cumulSpecE si_Σ [] (c20_eta_T c20_eta_I) (c20_eta_T c20_eta_Ieta) *
   (si_Σ ;;; [] |-E c20_eta_idt : c20_eta_T c20_eta_I) *
   (si_Σ ;;; [] |-E c20_eta_t : si_P))%type.
Proof.
  repeat split.
  - unfold c20_eta_I, c20_eta_Ieta. intros E. discriminate E.
  - exact (c20_eta_conv []).
  - unfold c20_eta_T, c20_eta_I, c20_eta_Ieta. intros E. discriminate E.
  - exact c20_eta_spec.
  - exact (c20_eta_idt_typed [] localenv_nil).
  - exact c20_eta_t_typed.
Qed.

Lemma c20_fo_eta_core :
  ((c20_fo_s <> c20_fo_seta) * convSpecE fo_Σ [] c20_fo_s c20_fo_seta *
   (c20_fo_T c20_fo_s <> c20_fo_T c20_fo_seta) *
   cumulSpecE fo_Σ [] (c20_fo_T c20_fo_s) (c20_fo_T c20_fo_seta) *
   (fo_Σ ;;; [] |-E c20_fo_idt : c20_fo_T c20_fo_s) *
   (fo_Σ ;;; [] |-E c20_fo_t : mkApps (tInd fo_ind []) []))%type.
Proof.
  repeat split.
  - unfold c20_fo_s, c20_fo_seta. intros E. discriminate E.
  - exact (c20_fo_conv []).
  - unfold c20_fo_T, c20_fo_s, c20_fo_seta. intros E. discriminate E.
  - exact c20_fo_spec.
  - exact (c20_fo_idt_typed [] localenv_nil).
  - exact c20_fo_t_typed.
Qed.

(** The η step inside the well-formedness proof of the environment the next instance runs in:
    a variable [F : Prop → Prop] against its η expansion. *)
Lemma c20_c17_eta_core :
  ((tLambda si_na si_P (tApp (tRel 1) (tRel 0)) <> tRel 0) *
   convSpecE PCUICTypingEtaCopy17Instances.c17_Σ ([] ,, vass si_na si_arity) (tRel 0)
     (tLambda si_na si_P (tApp (tRel 1) (tRel 0))))%type.
Proof.
  split.
  - intros E. discriminate E.
  - unfold convSpecE. apply cumulE_Sym.
    exact (cumulSpecE_eta_contract PCUICTypingEtaCopy17Instances.c17_Σ
             ([] ,, vass si_na si_arity) Conv si_na si_P (tRel 0)).
Qed.

(** ** The nondegeneracy lemma of each instance *)

Lemma wh_normalizationE_inst_nondeg :
  ((c20_eta_I <> c20_eta_Ieta) * convSpecE si_Σ [] c20_eta_I c20_eta_Ieta *
   (c20_eta_T c20_eta_I <> c20_eta_T c20_eta_Ieta) *
   cumulSpecE si_Σ [] (c20_eta_T c20_eta_I) (c20_eta_T c20_eta_Ieta) *
   (si_Σ ;;; [] |-E c20_eta_idt : c20_eta_T c20_eta_I) *
   (si_Σ ;;; [] |-E c20_eta_t : si_P))%type.
Proof. exact c20_eta_core. Qed.

Lemma SN_to_WNE_inst_nondeg :
  ((c20_eta_I <> c20_eta_Ieta) * convSpecE si_Σ [] c20_eta_I c20_eta_Ieta *
   (c20_eta_T c20_eta_I <> c20_eta_T c20_eta_Ieta) *
   cumulSpecE si_Σ [] (c20_eta_T c20_eta_I) (c20_eta_T c20_eta_Ieta) *
   (si_Σ ;;; [] |-E c20_eta_idt : c20_eta_T c20_eta_I) *
   (si_Σ ;;; [] |-E c20_eta_t : si_P))%type.
Proof. exact c20_eta_core. Qed.

Lemma wcbv_normalizationE_inst_nondeg :
  ((c20_eta_I <> c20_eta_Ieta) * convSpecE si_Σ [] c20_eta_I c20_eta_Ieta *
   (c20_eta_T c20_eta_I <> c20_eta_T c20_eta_Ieta) *
   cumulSpecE si_Σ [] (c20_eta_T c20_eta_I) (c20_eta_T c20_eta_Ieta) *
   (si_Σ ;;; [] |-E c20_eta_idt : c20_eta_T c20_eta_I) *
   (si_Σ ;;; [] |-E c20_eta_t : si_P))%type.
Proof. exact c20_eta_core. Qed.

Lemma ws_wcbv_standardizationE_inst_nondeg :
  ((c20_eta_I <> c20_eta_Ieta) * convSpecE si_Σ [] c20_eta_I c20_eta_Ieta *
   (c20_eta_T c20_eta_I <> c20_eta_T c20_eta_Ieta) *
   cumulSpecE si_Σ [] (c20_eta_T c20_eta_I) (c20_eta_T c20_eta_Ieta) *
   (si_Σ ;;; [] |-E c20_eta_idt : c20_eta_T c20_eta_I) *
   (si_Σ ;;; [] |-E c20_eta_t : si_P))%type.
Proof. exact c20_eta_core. Qed.

Lemma wcbv_standardizationE_inst_nondeg :
  ((c20_eta_I <> c20_eta_Ieta) * convSpecE si_Σ [] c20_eta_I c20_eta_Ieta *
   (c20_eta_T c20_eta_I <> c20_eta_T c20_eta_Ieta) *
   cumulSpecE si_Σ [] (c20_eta_T c20_eta_I) (c20_eta_T c20_eta_Ieta) *
   (si_Σ ;;; [] |-E c20_eta_idt : c20_eta_T c20_eta_I) *
   (si_Σ ;;; [] |-E c20_eta_t : si_P))%type.
Proof. exact c20_eta_core. Qed.

Lemma ws_wcbv_standardization_fstE_inst_nondeg :
  ((c20_fo_s <> c20_fo_seta) * convSpecE fo_Σ [] c20_fo_s c20_fo_seta *
   (c20_fo_T c20_fo_s <> c20_fo_T c20_fo_seta) *
   cumulSpecE fo_Σ [] (c20_fo_T c20_fo_s) (c20_fo_T c20_fo_seta) *
   (fo_Σ ;;; [] |-E c20_fo_idt : c20_fo_T c20_fo_s) *
   (fo_Σ ;;; [] |-E c20_fo_t : mkApps (tInd fo_ind []) []))%type.
Proof. exact c20_fo_eta_core. Qed.

Lemma wcbv_standardization_fstE_inst_nondeg :
  ((c20_fo_s <> c20_fo_seta) * convSpecE fo_Σ [] c20_fo_s c20_fo_seta *
   (c20_fo_T c20_fo_s <> c20_fo_T c20_fo_seta) *
   cumulSpecE fo_Σ [] (c20_fo_T c20_fo_s) (c20_fo_T c20_fo_seta) *
   (fo_Σ ;;; [] |-E c20_fo_idt : c20_fo_T c20_fo_s) *
   (fo_Σ ;;; [] |-E c20_fo_t : mkApps (tInd fo_ind []) []))%type.
Proof. exact c20_fo_eta_core. Qed.

Lemma wcbv_red1_evalE_inst_nondeg :
  ((tLambda si_na si_P (tApp (tRel 1) (tRel 0)) <> tRel 0) *
   convSpecE PCUICTypingEtaCopy17Instances.c17_Σ ([] ,, vass si_na si_arity) (tRel 0)
     (tLambda si_na si_P (tApp (tRel 1) (tRel 0))))%type.
Proof. exact c20_c17_eta_core. Qed.

(** ** The instance of the route lemma, which has no typing premise *)

Lemma c20_False_value :
  MetaRocq.PCUIC.PCUICWcbvEval.value PCUICTypingEtaCopy17Instances.c17_Σ iv_False.
Proof.
  unfold iv_False.
  apply MetaRocq.PCUIC.PCUICWcbvEval.value_atomic.
  apply MetaRocq.PCUIC.PCUICWcbvEval.atomic_atom.
  reflexivity.
Qed.

(* INSTANCE NONDEGEN MetaRocq.PCUIC.PCUICTypingEtaCopy20Instances.wcbv_red1_evalE_inst_nondeg
   The only typed premise of this lemma is [wfE Σ]. The environment
   [PCUICTypingEtaCopy17Instances.c17_Σ] declares a constant whose type is typed only through
   the η step of the lemma above, so that step is inside this instance's [wfE] premise. *)
Definition wcbv_red1_evalE_inst :
  MetaRocq.PCUIC.PCUICWcbvEval.eval PCUICTypingEtaCopy17Instances.c17_Σ
    (tApp iv_id iv_False) iv_False :=
  PCUICNormalizationEta.wcbv_red1_evalE (Σ := PCUICTypingEtaCopy17Instances.c17_Σ)
    (tApp iv_id iv_False) iv_False iv_False
    PCUICTypingEtaCopy17Instances.c17_wfE Corelib.Init.Logic.eq_refl
    (MetaRocq.PCUIC.PCUICWcbvEval.wcbv_red_beta PCUICTypingEtaCopy17Instances.c17_Σ si_na si_P
       (tRel 0) iv_False c20_False_value)
    (MetaRocq.PCUIC.PCUICWcbvEval.eval_atom PCUICTypingEtaCopy17Instances.c17_Σ iv_False
       Corelib.Init.Logic.eq_refl).

Section NormalizationEtaInstances.

(* Base's normalization premise, one per environment these instances use (by design, never
   discharged: it is strong normalization, as base's [NormalizationIn] is). *)
Context {nor : normalizing_flags} {nin_si : NormalizationInE si_Σ}
        {nin_fo : NormalizationInE fo_Σ}.

(** [s z] is [red1]-normal, by the copy's own [firstorder_value_irredE] on [fo_sz_value]. *)
Lemma c20_fo_sz_irred : ¬ { t' & fo_Σ ;;; [] |- fo_sz ⇝ t'}.
Proof.
  intros [t' H]. eapply firstorder_value_irredE; [exact fo_sz_value|exact H].
Qed.

(* INSTANCE NOT-BUILT: no η step was built into this instance's premise, and the cost of one is
   named. The lemma's only typed premise is [firstorder_valueE Σ [] t], whose typing is that of
   [mkApps (tConstruct i n ui) args] at [mkApps (tInd i u) pandi] with every argument again a
   first-order value. In [fo_Σ] every constructor argument has type [N], so no argument position
   can hold a function, and the only way to put [cumul_eta_l] into such a derivation is a detour
   on a type convertible to itself, which carries no η content. A non-vacuous witness therefore
   costs a NEW environment whose first-order values are typed through η while
   [firstorder_ind] still holds of its inductive: a declaration literal, its [on_inductive]
   obligations, a [wf] proof in the shape of [fo_wf], and the retyping of this instance on it.
   Not built here. *)
Definition firstorder_value_irredE_inst :
  forall t', MetaRocq.PCUIC.PCUICReduction.red1 fo_Σ [] fo_sz t' -> False :=
  fun t' H => firstorder_value_irredE fo_Σ fo_sz t' fo_sz_value H.

(* INSTANCE NONDEGEN MetaRocq.PCUIC.PCUICTypingEtaCopy20Instances.wh_normalizationE_inst_nondeg *)
Definition wh_normalizationE_inst :
  { v & whnf RedFlags.default si_Σ [] v * red si_Σ [] c20_eta_t v} :=
  PCUICNormalizationEta.wh_normalizationE (Σ := si_Σ) (t := c20_eta_t) si_wfE cli_axiom_free
    (si_P; c20_eta_t_typed).

(* INSTANCE NONDEGEN MetaRocq.PCUIC.PCUICTypingEtaCopy20Instances.SN_to_WNE_inst_nondeg
   The accessibility premise is [c20_eta_acc], a proof, not the normalization hypothesis. *)
Definition SN_to_WNE_inst : { v & MetaRocq.PCUIC.PCUICWcbvEval.eval si_Σ c20_eta_t v} :=
  SN_to_WNE (Σ := si_Σ) (A := si_P) (t := c20_eta_t) si_wfE cli_axiom_free c20_eta_acc
    c20_eta_t_typed.

(* INSTANCE NONDEGEN MetaRocq.PCUIC.PCUICTypingEtaCopy20Instances.wcbv_normalizationE_inst_nondeg *)
Definition wcbv_normalizationE_inst : { v & MetaRocq.PCUIC.PCUICWcbvEval.eval si_Σ c20_eta_t v} :=
  wcbv_normalizationE (Σ := si_Σ) (A := si_P) (t := c20_eta_t) si_wfE cli_axiom_free
    c20_eta_t_typed.

(* INSTANCE NONDEGEN MetaRocq.PCUIC.PCUICTypingEtaCopy20Instances.ws_wcbv_standardizationE_inst_nondeg *)
Definition ws_wcbv_standardizationE_inst :
  {v' & MetaRocq.PCUIC.PCUICWcbvEval.eval si_Σ c20_eta_t v' * (si_Σ ;;; [] ⊢ v' ⇝ iv_False)} :=
  ws_wcbv_standardizationE (Σ := si_Σ) (T := si_P) (t := c20_ws_eta_t) (v := c20_wsF)
    si_wfE cli_axiom_free c20_eta_t_typed c20_closed_red_eta_t c20_False_irred.

(* INSTANCE NONDEGEN MetaRocq.PCUIC.PCUICTypingEtaCopy20Instances.wcbv_standardizationE_inst_nondeg *)
Definition wcbv_standardizationE_inst :
  {v' & MetaRocq.PCUIC.PCUICWcbvEval.eval si_Σ c20_eta_t v' * (si_Σ ;;; [] ⊢ v' ⇝ iv_False)} :=
  wcbv_standardizationE (Σ := si_Σ) (T := si_P) (t := c20_eta_t) (v := iv_False)
    si_wfE cli_axiom_free c20_eta_t_typed c20_eta_t_red1 c20_False_irred.

(* INSTANCE NONDEGEN MetaRocq.PCUIC.PCUICTypingEtaCopy20Instances.ws_wcbv_standardization_fstE_inst_nondeg *)
Definition ws_wcbv_standardization_fstE_inst :
  MetaRocq.PCUIC.PCUICWcbvEval.eval fo_Σ c20_fo_t fo_sz :=
  ws_wcbv_standardization_fstE (Σ := fo_Σ) (i := fo_ind) (u := []) (args := []) (mind := fo_mdecl)
    (t := c20_ws_fo_t) (v := c20_ws_fo_sz) fo_wfE c20_fo_axiom_free c20_fo_t_typed
    c20_fo_lookup fo_firstorder c20_closed_red_fo c20_fo_sz_irred.

(* INSTANCE NONDEGEN MetaRocq.PCUIC.PCUICTypingEtaCopy20Instances.wcbv_standardization_fstE_inst_nondeg *)
Definition wcbv_standardization_fstE_inst :
  MetaRocq.PCUIC.PCUICWcbvEval.eval fo_Σ c20_fo_t fo_sz :=
  wcbv_standardization_fstE (Σ := fo_Σ) (i := fo_ind) (u := []) (args := []) (mind := fo_mdecl)
    (t := c20_fo_t) (v := fo_sz) fo_wfE c20_fo_axiom_free c20_fo_t_typed c20_fo_lookup
    fo_firstorder c20_fo_t_red c20_fo_sz_irred.

End NormalizationEtaInstances.
