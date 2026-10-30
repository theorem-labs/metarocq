(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the lemmas of [Bidirectional/BDUniqueEta] (row T6)

  **No forecast class.** Every lemma of [BDUniqueEta] uses soundness, validity or
  completeness, so it took the class of [BDToPCUICEta] as a premise until copy 18b landed
  (frac/eta 3e6b422d); the class is deleted. The instances below are applied in section
  [BDUniqueClassInstances] (which held it). Every derivation they need is built here, in
  [PCUICInversionEtaInstances], [BDTypingEtaInstances] or [BDToPCUICEtaInstances].

  **The environment** is [si_Σ] ([PCUICCumulativitySpecEtaClosureInstances]:
  [Inductive I (A : Prop) : Prop := c : I A], with [si_wfE]).

  **Non-degeneracy.** The uniqueness lemmas compare two derivations of one term. Inference is
  syntax-directed, so two derivations differ only where [▹Π], [▹□] or [▹{}] picks a reduct:
  - in [bu_ΓQ = [f : Π P : Prop. (λ x : Prop. x) P]], [f ▹Π] has two derivations, one keeping the
    β-redex in the codomain and one contracting it ([bu_f_prod1], [bu_f_prod2]), so [f (∀P.P)]
    infers the two different types [(λ x. x) (∀P.P)] and [∀P.P] ([bu_app_infer1],
    [bu_app_infer2], [bu_app_types_differ]); the main theorem, [infering_uniqueE],
    [infering_unique'E], [infering_prod_prodE], [infering_prod_prod'E] and
    [infering_prod_inferingE] are applied to them;
  - [c ((λ x. x) (∀P.P)) ▹{I}] has the argument lists [[(λ x. x) (∀P.P)]] and [[∀P.P]]
    ([bu_disc_ind1], [bu_disc_ind2]) for the three [▹{}] lemmas;
  - in [bu_Γd = [y : d; d := Prop : Type]], [y ▹ d] and [y ▹□ Prop] through the δ-step of the let
    ([bu_y_sort]), for [infering_sort_inferingE];
  - [infering_checkingE] is applied to the check [x ◃ G F] of [checkingE_eta_inst], whose
    [JoinE] premise is one η step.
  IMPOSSIBLE to make non-reflexive, by the statement: [infering_sort_sortE] and
  [isTypeRel_uniqueE] conclude an equality of sorts or relevances; their instances run through a
  let-reduction ([bu_y_sort]) or a real derivation. The two reduction facts the proofs use,
  [PCUICPrincipalityEta.closed_red_confluence_cb] and [invert_red_sort_cb], have their instances
  in [PCUICPrincipalityEtaInstances]. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICReduction PCUICWellScopedCumulativity PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICClosedBodies PCUICTypingEta
     PCUICTypingEtaNotions PCUICCumulativitySpecEtaClosureInstances PCUICEtaDefs PCUICEtaI5
     PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICWfUniversesEta
     PCUICInversionEtaInstances
     PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICSpineEta PCUICValidityEta PCUICSREta
     BDTyping BDTypingEta BDTypingEtaInstances BDToPCUICEta BDToPCUICEtaInstances BDFromPCUICEta
     BDUniqueEta.
From Equations.Type Require Import Relation.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

(** ** Derivations, without any class *)

(** [Q := Π P : Prop. (λ x : Prop. x) P] and the context [f : Q]. *)
Definition bu_Q : term := tProd si_na si_P (tApp iv_id (tRel 0)).
Definition bu_ΓQ : context := [vass si_na bu_Q].

Lemma bu_idP_typed (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ ,, vass si_na si_P |-E tApp iv_id (tRel 0) : si_P.
Proof.
  intros h. have w := iv_wf_P si_Σ Γ h.
  exact (typeE_App _ _ iv_id si_na si_P si_P _ (tRel 0) (iv_PP_typed si_Σ _ w) (iv_id_typed si_Σ _ w)
           (typeE_Rel _ _ 0 (vass si_na si_P) w eq_refl)).
Qed.

Lemma bu_Q_typed (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ |-E bu_Q : tSort (Sort.sort_of_product (Sort.super sProp) sProp).
Proof.
  intros h. unfold bu_Q. apply typeE_Prod.
  - exact (iv_vass_s si_Σ Γ si_na si_P _ (iv_P_typed si_Σ Γ h) eq_refl).
  - exact (bu_idP_typed Γ h).
Qed.

Lemma bu_wf_ΓQ : wf_localE si_Σ bu_ΓQ.
Proof. exact (iv_wf_vass si_Σ [] si_na bu_Q _ localenv_nil (bu_Q_typed [] localenv_nil) eq_refl). Qed.

Lemma bu_f_infer : si_Σ ;;; bu_ΓQ |-E tRel 0 ▹ bu_Q.
Proof. exact (inferE_Rel _ bu_ΓQ 0 (vass si_na bu_Q) eq_refl). Qed.

(** [f ▹Π] keeping the β-redex of the codomain, and contracting it. *)
Lemma bu_f_prod1 : si_Σ ;;; bu_ΓQ |-E tRel 0 ▹Π (si_na, si_P, tApp iv_id (tRel 0)).
Proof. econstructor; [exact bu_f_infer|apply rt_refl]. Qed.

Lemma bu_f_prod2 : si_Σ ;;; bu_ΓQ |-E tRel 0 ▹Π (si_na, si_P, tRel 0).
Proof.
  econstructor; [exact bu_f_infer|].
  apply rt_step. unfold bu_Q. apply prod_red_r. unfold iv_id. apply red_beta.
Qed.

(** [∀P:Prop. P ◃ Prop], in any context. *)
Lemma bu_False_check (Γ : context) : si_Σ ;;; Γ |-E iv_False ◃ si_P.
Proof.
  eapply checkE_Cumul.
  - unfold iv_False. apply inferE_Prod.
    + exact (bd_vass_s Γ si_na si_P _ (bd_P_sort Γ) eq_refl).
    + econstructor; [exact (inferE_Rel _ (Γ ,, vass si_na si_P) 0 (vass si_na si_P) eq_refl)|apply rt_refl].
  - apply JoinE_refl.
Qed.

Lemma bu_app_infer1 : si_Σ ;;; bu_ΓQ |-E tApp (tRel 0) iv_False ▹ tApp iv_id iv_False.
Proof. exact (inferE_App _ _ _ _ _ _ _ bu_f_prod1 (bu_False_check _)). Qed.

Lemma bu_app_infer2 : si_Σ ;;; bu_ΓQ |-E tApp (tRel 0) iv_False ▹ iv_False.
Proof. exact (inferE_App _ _ _ _ _ _ _ bu_f_prod2 (bu_False_check _)). Qed.

Lemma bu_app_types_differ : tApp iv_id iv_False <> iv_False.
Proof. discriminate. Qed.

(** [λ x : Prop. x ▹Π (_ : Prop, Prop)] and [(λ x. x) (∀P.P) ◃ Prop], in any context. *)
Lemma bu_id_prod (Γ : context) : si_Σ ;;; Γ |-E iv_id ▹Π (si_na, si_P, lift0 1 si_P).
Proof.
  econstructor; [|apply rt_refl].
  unfold iv_id. apply inferE_Lambda.
  - exact (bd_vass Γ si_na si_P _ (bd_P_sort Γ) eq_refl).
  - exact (inferE_Rel _ (Γ ,, vass si_na si_P) 0 (vass si_na si_P) eq_refl).
Qed.

Definition bu_idF : term := tApp iv_id iv_False.

Lemma bu_idF_check (Γ : context) : si_Σ ;;; Γ |-E bu_idF ◃ si_P.
Proof.
  eapply checkE_Cumul; [|apply JoinE_refl].
  exact (inferE_App _ _ _ _ _ _ _ (bu_id_prod Γ) (bu_False_check Γ)).
Qed.

(** [c ((λ x. x) (∀P.P)) ▹{I}], with the argument unreduced and reduced. *)
Definition bu_disc : term := tApp (tConstruct si_ind 0 []) bu_idF.

Lemma bu_disc_infer : si_Σ ;;; [] |-E bu_disc ▹ tApp (tInd si_ind []) bu_idF.
Proof. exact (inferE_App _ _ _ _ _ _ _ (bd_cstr_prod []) (bu_idF_check [])). Qed.

Lemma bu_disc_ind1 : si_Σ ;;; [] |-E bu_disc ▹{si_ind} ([], [bu_idF]).
Proof. econstructor; [exact bu_disc_infer|apply rt_refl]. Qed.

Lemma bu_disc_ind2 : si_Σ ;;; [] |-E bu_disc ▹{si_ind} ([], [iv_False]).
Proof.
  econstructor; [exact bu_disc_infer|].
  apply rt_step. apply app_red_r. unfold bu_idF, iv_id. apply red_beta.
Qed.

(** [d := Prop : Type, y : d]: [y ▹ d], and [y ▹□ Prop] by the δ-step of the let. *)
Definition bu_Γd : context := [vass si_na (tRel 0); vdef si_na si_P (tSort (Sort.super sProp))].

Lemma bu_wf_Γd : wf_localE si_Σ bu_Γd.
Proof.
  pose proof (typing_wf_sortE (Σ := si_Σ) si_wfE (iv_P_typed si_Σ [] localenv_nil)) as ws.
  pose proof (@typeE_Sort default_checker_flags si_Σ [] (Sort.super sProp) localenv_nil ws) as hT.
  assert (w1 : wf_localE si_Σ [vdef si_na si_P (tSort (Sort.super sProp))]).
  { apply localenv_cons_def; [constructor|].
    exact (iv_vdef si_Σ [] si_na si_P _ _ (iv_P_typed si_Σ [] localenv_nil) hT eq_refl). }
  exact (iv_wf_vass si_Σ _ si_na (tRel 0) (Sort.super sProp) w1
           (typeE_Rel _ _ 0 (vdef si_na si_P (tSort (Sort.super sProp))) w1 eq_refl) eq_refl).
Qed.

Lemma bu_y_infer : si_Σ ;;; bu_Γd |-E tRel 0 ▹ tRel 1.
Proof. exact (inferE_Rel _ bu_Γd 0 (vass si_na (tRel 0)) eq_refl). Qed.

Lemma bu_y_sort : si_Σ ;;; bu_Γd |-E tRel 0 ▹□ sProp.
Proof.
  econstructor; [exact bu_y_infer|].
  apply rt_step. exact (red_rel si_Σ bu_Γd 1 si_P eq_refl).
Qed.

(** ** The lemmas, applied (they took a forecast class until copy 18b landed) *)

Section BDUniqueClassInstances.

  (** The main theorem's inference component, on the two types of [f (∀P.P)]. *)
  Definition bidirectional_uniqueE_inst :
    ∑ T'', si_Σ ;;; bu_ΓQ ⊢ tApp iv_id iv_False ⇝ T'' × si_Σ ;;; bu_ΓQ ⊢ iv_False ⇝ T'' :=
    fst (snd (snd (snd (snd (bidirectional_uniqueE si_Σ si_wfE))))) bu_ΓQ _ _ bu_app_infer1
      bu_wf_ΓQ _ bu_app_infer2.

  Definition infering_uniqueE_inst :
    ∑ T'', si_Σ ;;; bu_ΓQ ⊢ tApp iv_id iv_False ⇝ T'' × si_Σ ;;; bu_ΓQ ⊢ iv_False ⇝ T'' :=
    infering_uniqueE (Σ := si_Σ) si_wfE bu_wf_ΓQ bu_app_infer1 bu_app_infer2.

  Definition infering_unique'E_inst : si_Σ ;;; bu_ΓQ ⊢E tApp iv_id iv_False = iv_False :=
    infering_unique'E (Σ := si_Σ) si_wfE bu_wf_ΓQ bu_app_infer1 bu_app_infer2.

  (** [x ◃ G F] by one η step; the comparison concluded is the η pair. *)
  Definition infering_checkingE_inst : si_Σ ;;; bd_Γη ⊢E lift0 1 bd_X ≤ tApp (tRel 2) (tRel 1) :=
    infering_checkingE (Σ := si_Σ) si_wfE bdi_wfη (T' := tApp (tRel 2) (tRel 1)) eq_refl
      (inferE_Rel _ bd_Γη 0 (vass si_na bd_X) eq_refl)
      checkingE_eta_inst.

  Definition infering_sort_sortE_inst : sProp = sProp :=
    infering_sort_sortE (Σ := si_Σ) si_wfE bu_wf_Γd bu_y_sort bu_y_sort.

  Definition infering_sort_inferingE_inst : si_Σ ;;; bu_Γd ⊢ tRel 1 ⇝ tSort sProp :=
    infering_sort_inferingE (Σ := si_Σ) si_wfE (wfΓ := bu_wf_Γd) bu_y_sort bu_y_infer.

  Definition infering_prod_prodE_inst :=
    infering_prod_prodE (Σ := si_Σ) si_wfE bu_wf_ΓQ bu_f_prod1 bu_f_prod2.

  Definition infering_prod_prod'E_inst :
    [× si_na = si_na, si_Σ ;;; bu_ΓQ ⊢E si_P = si_P &
       si_Σ ;;; bu_ΓQ ,, vass si_na si_P ⊢E tApp iv_id (tRel 0) = tRel 0] :=
    infering_prod_prod'E (Σ := si_Σ) si_wfE bu_wf_ΓQ bu_f_prod1 bu_f_prod2.

  Definition infering_prod_inferingE_inst :=
    infering_prod_inferingE (Σ := si_Σ) si_wfE bu_wf_ΓQ bu_f_prod2 bu_f_infer.

  Definition infering_ind_indE_inst :=
    infering_ind_indE (Σ := si_Σ) si_wfE localenv_nil bu_disc_ind1 bu_disc_ind2.

  Definition infering_ind_ind'E_inst :
    [× si_ind = si_ind, ([] : Instance.t) = [] & ws_cumul_pbE_terms si_Σ [] [bu_idF] [iv_False]] :=
    infering_ind_ind'E (Σ := si_Σ) si_wfE localenv_nil bu_disc_ind1 bu_disc_ind2.

  Definition infering_ind_inferingE_inst :=
    infering_ind_inferingE (Σ := si_Σ) si_wfE localenv_nil bu_disc_ind2 bu_disc_infer.

  Definition principal_typeE_inst :=
    BDUniqueEta.principal_typeE (Σ := si_Σ) si_wfE (iv_app_typed si_Σ [] localenv_nil).

  Definition isTypeRel_uniqueE_inst : Relevant = Relevant :=
    isTypeRel_uniqueE (Σ := si_Σ) si_wfE (Γ := []) (T := iv_PP)
      (iv_vass si_Σ [] si_na iv_PP _ (iv_PP_typed si_Σ [] localenv_nil) eq_refl)
      (iv_vass si_Σ [] si_na iv_PP _ (iv_PP_typed si_Σ [] localenv_nil) eq_refl).

End BDUniqueClassInstances.
