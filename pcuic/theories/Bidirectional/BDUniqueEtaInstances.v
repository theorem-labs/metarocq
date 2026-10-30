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
  syntax-directed, so two derivations differ only where [▹Π], [▹□] or [▹{}] picks a reduct.
  The comment above each instance carries its tag of the instance degeneracy gate; the
  declarations that are not instances are registered on the witness line after the imports.
  - in [bu_ΓQ = [f : Π P : Prop. (λ x : Prop. x) P]], [f ▹Π] has two derivations, one with the
    codomain [(λ x. x) P] and one with the codomain [P] ([bu_f_prod1], [bu_f_prod2]), which
    differ ([bu_f_prods_differ]), so [f (∀P.P)] infers the two different types
    [(λ x. x) (∀P.P)] and [∀P.P] ([bu_app_infer1], [bu_app_infer2], [bu_app_types_differ]); the
    main theorem, [infering_uniqueE], [infering_unique'E], [infering_prod_prodE],
    [infering_prod_prod'E] and [infering_prod_inferingE] are applied to them;
  - [c ((λ x. x) (∀P.P)) ▹{I}] has the argument lists [[(λ x. x) (∀P.P)]] and [[∀P.P]]
    ([bu_disc_ind1], [bu_disc_ind2], [bu_disc_args_differ]) for the three [▹{}] lemmas;
  - in [bu_Γd = [y : d; d := Prop : Type]], [y ▹ d] and [y ▹□ Prop] ([bu_y_infer], [bu_y_sort]):
    every type inferred for [y] is [d], which is not a sort and reduces to [Prop] in one step
    ([infering_sort_inferingE_inst_nondeg]), for [infering_sort_inferingE];
  - [infering_checkingE] is applied to the check [x ◃ G F] of [checkingE_eta_inst], and
    [BDUniqueEta.principal_typeE] to the typing [x : G F] of [checking_typingE_eta_inst]; every
    type inferred for [x] in [bd_Γη] is [G (λ y. F y)], which is not [G F] and η-contracts to it
    in one step ([BDToPCUICEtaInstances.bdi_eta_pair]).
  The two rows whose every instance is degenerate by the statement, [infering_sort_sortE] and
  [isTypeRel_uniqueE], are tagged at their instance. The two reduction facts the proofs use,
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

(** The declarations that are not instances: the contexts, derivations and non-degeneracy
    facts the instances are built from or name.
    WITNESSES: bu_* *)

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

(** The two products differ: the codomain [(λ x. x) P] is a β-redex, not [P], so [Q] is not
    [Π P. P]. *)
Lemma bu_f_prods_differ : tApp iv_id (tRel 0) <> tRel 0 /\ bu_Q <> tProd si_na si_P (tRel 0).
Proof. unfold bu_Q. split; discriminate. Qed.

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

(** The two argument lists differ: [(λ x. x) (∀P.P)] is not [∀P.P]. *)
Lemma bu_disc_args_differ : bu_idF <> iv_False.
Proof. unfold bu_idF, iv_False. discriminate. Qed.

(** [d := Prop : Type, y : d]: [y ▹ d] ([bu_y_infer]) and [y ▹□ Prop] ([bu_y_sort]); [d] reduces
    to [Prop] in one step ([infering_sort_inferingE_inst_nondeg]). *)
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

(** In [bu_Γd]: the declared type of [y], lifted, is not a sort; every type inferred for [y] is
    [d] ([tRel 1]); and [d], the let-variable of [d := Prop], reduces to [Prop] in one step. *)
Lemma infering_sort_inferingE_inst_nondeg :
  [/\ (forall d u, nth_error bu_Γd 0 = Some d -> lift0 1 (decl_type d) <> tSort u),
      (forall T', si_Σ ;;; bu_Γd |-E tRel 0 ▹ T' -> T' = tRel 1) &
      ∥ red1 si_Σ bu_Γd (tRel 1) si_P ∥].
Proof.
  split.
  - intros d u h. injection h as <-. discriminate.
  - intros T' h. inversion h; subst.
    match goal with hn : nth_error _ _ = Some _ |- _ => vm_compute in hn; injection hn as hd; subst end.
    reflexivity.
  - exact (sq (red_rel si_Σ bu_Γd 1 si_P eq_refl)).
Qed.

(** ** The lemmas, applied (they took a forecast class until copy 18b landed) *)

Section BDUniqueClassInstances.

  (** The main theorem's inference component; the two types it relates, [(λ x. x) (∀P.P)] and
      [∀P.P], differ ([bu_app_types_differ]).
      INSTANCE NONDEGEN BDUniqueEtaInstances.bu_app_types_differ *)
  Definition bidirectional_uniqueE_inst :
    ∑ T'', si_Σ ;;; bu_ΓQ ⊢ tApp iv_id iv_False ⇝ T'' × si_Σ ;;; bu_ΓQ ⊢ iv_False ⇝ T'' :=
    fst (snd (snd (snd (snd (bidirectional_uniqueE si_Σ si_wfE))))) bu_ΓQ (tApp (tRel 0) iv_False)
      (tApp iv_id iv_False) bu_app_infer1 bu_wf_ΓQ iv_False bu_app_infer2.

  (** INSTANCE NONDEGEN BDUniqueEtaInstances.bu_app_types_differ *)
  Definition infering_uniqueE_inst :
    ∑ T'', si_Σ ;;; bu_ΓQ ⊢ tApp iv_id iv_False ⇝ T'' × si_Σ ;;; bu_ΓQ ⊢ iv_False ⇝ T'' :=
    infering_uniqueE (Σ := si_Σ) si_wfE bu_wf_ΓQ (T := tApp iv_id iv_False) (T' := iv_False)
      bu_app_infer1 bu_app_infer2.

  (** INSTANCE NONDEGEN BDUniqueEtaInstances.bu_app_types_differ *)
  Definition infering_unique'E_inst : si_Σ ;;; bu_ΓQ ⊢E tApp iv_id iv_False = iv_False :=
    infering_unique'E (Σ := si_Σ) si_wfE bu_wf_ΓQ (T := tApp iv_id iv_False) (T' := iv_False)
      bu_app_infer1 bu_app_infer2.

  (** The comparison concluded is [lift0 1 bd_X ≤ G F]. Every type inferred for [x] in [bd_Γη]
      is [lift0 1 bd_X], that is [G (λ y. F y)], which is not [G F] and η-contracts to it in one
      step ([BDToPCUICEtaInstances.bdi_eta_pair]).
      INSTANCE NONDEGEN BDToPCUICEtaInstances.bdi_eta_pair *)
  Definition infering_checkingE_inst : si_Σ ;;; bd_Γη ⊢E lift0 1 bd_X ≤ tApp (tRel 2) (tRel 1) :=
    infering_checkingE (Σ := si_Σ) si_wfE bdi_wfη (T' := tApp (tRel 2) (tRel 1)) eq_refl
      (inferE_Rel _ bd_Γη 0 (vass si_na bd_X) eq_refl)
      checkingE_eta_inst.

  (** INSTANCE IMPOSSIBLE: the conclusion [u = u'] equates the sorts of two [▹□] derivations of one term; the two inferred types have a common reduct ([bidirectional_uniqueE], as in the proof of [infering_sort_sortE]), so by confluence the two sorts [tSort u] and [tSort u'] have one, and a sort has no reduct; so in every environment and context, whatever its [wfE], [u = u'] (here [sProp = sProp], for [bu_y_sort] twice). *)
  Definition infering_sort_sortE_inst : sProp = sProp :=
    infering_sort_sortE (Σ := si_Σ) si_wfE bu_wf_Γd bu_y_sort bu_y_sort.

  (** [y ▹ d] and [y ▹□ Prop]: every type inferred for [y] is [d], which is not a sort and
      reduces to [Prop] in one step ([infering_sort_inferingE_inst_nondeg]).
      INSTANCE NONDEGEN BDUniqueEtaInstances.infering_sort_inferingE_inst_nondeg *)
  Definition infering_sort_inferingE_inst : si_Σ ;;; bu_Γd ⊢ tRel 1 ⇝ tSort sProp :=
    infering_sort_inferingE (Σ := si_Σ) si_wfE (Γ := bu_Γd) (wfΓ := bu_wf_Γd) bu_y_sort bu_y_infer.

  (** The two products of [f], [Π P. (λ x. x) P] and [Π P. P] ([bu_f_prods_differ]).
      INSTANCE NONDEGEN BDUniqueEtaInstances.bu_f_prods_differ *)
  Definition infering_prod_prodE_inst :=
    infering_prod_prodE (Σ := si_Σ) si_wfE bu_wf_ΓQ (B := tApp iv_id (tRel 0)) (B' := tRel 0)
      bu_f_prod1 bu_f_prod2.

  (** INSTANCE NONDEGEN BDUniqueEtaInstances.bu_f_prods_differ *)
  Definition infering_prod_prod'E_inst :
    [× si_na = si_na, si_Σ ;;; bu_ΓQ ⊢E si_P = si_P &
       si_Σ ;;; bu_ΓQ ,, vass si_na si_P ⊢E tApp iv_id (tRel 0) = tRel 0] :=
    infering_prod_prod'E (Σ := si_Σ) si_wfE bu_wf_ΓQ (B := tApp iv_id (tRel 0)) (B' := tRel 0)
      bu_f_prod1 bu_f_prod2.

  (** [f ▹ Q] and [f ▹Π (_ : Prop, P)]: [Q] is not [Π P. P] ([bu_f_prods_differ]).
      INSTANCE NONDEGEN BDUniqueEtaInstances.bu_f_prods_differ *)
  Definition infering_prod_inferingE_inst :=
    infering_prod_inferingE (Σ := si_Σ) si_wfE bu_wf_ΓQ (T := bu_Q) bu_f_prod2 bu_f_infer.

  (** The two argument lists [[(λ x. x) (∀P.P)]] and [[∀P.P]] ([bu_disc_args_differ]).
      INSTANCE NONDEGEN BDUniqueEtaInstances.bu_disc_args_differ *)
  Definition infering_ind_indE_inst :=
    infering_ind_indE (Σ := si_Σ) si_wfE localenv_nil (args := [bu_idF]) (args' := [iv_False])
      bu_disc_ind1 bu_disc_ind2.

  (** INSTANCE NONDEGEN BDUniqueEtaInstances.bu_disc_args_differ *)
  Definition infering_ind_ind'E_inst :
    [× si_ind = si_ind, ([] : Instance.t) = [] & ws_cumul_pbE_terms si_Σ [] [bu_idF] [iv_False]] :=
    infering_ind_ind'E (Σ := si_Σ) si_wfE localenv_nil (args := [bu_idF]) (args' := [iv_False])
      bu_disc_ind1 bu_disc_ind2.

  (** [c ((λ x. x) (∀P.P)) ▹ I ((λ x. x) (∀P.P))] and [c ((λ x. x) (∀P.P)) ▹{I} ([], [∀P.P])]:
      the arguments [(λ x. x) (∀P.P)] and [∀P.P] differ ([bu_disc_args_differ]).
      INSTANCE NONDEGEN BDUniqueEtaInstances.bu_disc_args_differ *)
  Definition infering_ind_inferingE_inst :=
    infering_ind_inferingE (Σ := si_Σ) si_wfE localenv_nil (T := tApp (tInd si_ind []) bu_idF)
      bu_disc_ind2 bu_disc_infer.

  (** The typing [x : G F] in [bd_Γη] ([checking_typingE_eta_inst]): every type inferred for [x]
      there is [G (λ y. F y)], which is not [G F] and η-contracts to it in one step
      ([BDToPCUICEtaInstances.bdi_eta_pair]).
      INSTANCE NONDEGEN BDToPCUICEtaInstances.bdi_eta_pair
      TARGET BDUniqueEta.principal_typeE *)
  Definition principal_typeE_inst :=
    BDUniqueEta.principal_typeE (Σ := si_Σ) si_wfE (Γ := bd_Γη) checking_typingE_eta_inst.

  (** INSTANCE IMPOSSIBLE: the conclusion [rel = rel'] equates the relevances of two [isTypeRelE] judgments of one type; each relevance is that of a sort above the type's inferred sort ([typing_infering_sortE]), relevance is preserved along [leq_sort] ([leq_relevance_eq]) and the inferred sort is unique ([infering_sort_sortE]), as in the proof of [isTypeRel_uniqueE]; so in every environment and context, whatever its [wfE], [rel = rel'] (here [Relevant = Relevant]). *)
  Definition isTypeRel_uniqueE_inst : Relevant = Relevant :=
    isTypeRel_uniqueE (Σ := si_Σ) si_wfE (Γ := []) (T := iv_PP)
      (iv_vass si_Σ [] si_na iv_PP _ (iv_PP_typed si_Σ [] localenv_nil) eq_refl)
      (iv_vass si_Σ [] si_na iv_PP _ (iv_PP_typed si_Σ [] localenv_nil) eq_refl).

End BDUniqueClassInstances.
