(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the lemmas of [Bidirectional/BDStrengtheningEta] (row T6)

  **The environment** is [si_Σ] ([PCUICCumulativitySpecEtaClosureInstances]:
  [Inductive I (A : Prop) : Prop := c : I A], with [si_wfE]). The derivations are those of
  [BDTypingEtaInstances] ([bd_ΓFG = [F : Prop → Prop; G : (Prop → Prop) → Prop]], the [match]
  [bd_case] with the η-related parameters, the η check [x ◃ G F] in [bd_Γη]),
  [BDToPCUICEtaInstances] and [BDUniqueEtaInstances] ([bu_Γd = [y : d; d := Prop : Type]]).

  **The renamings** are weakenings by one assumption ([urenaming_lift0]), with the predicate
  [P] the scope of the source context ([shiftnP #|Γ| xpred0]), so the free-variable premises are
  the real ones.

  **Lemmas without a forecast class** are applied here; the four that use soundness,
  completeness, validity or subject reduction ([on_free_vars_typeE], [typing_renaming_cond_PE],
  [strengtheningE], [strengthening_typeE]) are applied in section [BDStrengtheningClassInstances],
  whose [Context] holds the two classes, as [BDToPCUICEtaInstances] does.

  **Non-degeneracy.**
  - [eta1_rename_inst], [RE_renameP_inst], [JoinE_renameP_inst], [cumul_renamePE_inst],
    [conv_renamePE_inst]: the η step [G (λ y. F y) ⇝η G F] of [bd_eta_step] and its join,
    weakened.
  - the scoping lemmas and [bidirectional_renamingE_inst] run on the [match] [bd_case], whose
    parameter comparison is an η step; [rename_mfix_on_ind_redE_inst] on the fixpoint
    [bd_mfix], whose reduction witness is a β-step; [rename_telescopeE_inst] on its parameter
    instance.
  - [typing_renaming_cond_PE_inst] and [on_free_vars_typeE_inst] on the η-typed [x : G F].
  - [strengtheningE_inst] and [strengthening_typeE_inst] remove the unused assumption [x : Prop]
    from [y : d; d := Prop : Type] for [y]: the inferred type of [y] after the lifting is the
    let-variable [d], not a sort, so [strengthening_typeE] reaches its T8 site
    ([PCUICEtaT8Probe.T8_Sort_r_two]) with a type that reduces to a sort only by the δ-step of
    the let. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICReduction PCUICWellScopedCumulativity PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICCumulativitySpecEtaClosure PCUICClosedBodies PCUICTypingEta PCUICTypingEtaNotions
     PCUICCumulativitySpecEtaClosureInstances PCUICEtaDefs PCUICEtaCanon PCUICEtaCanonRed PCUICEtaI5
     PCUICWellScopedCumulativityEta PCUICRenameTypEta PCUICInversionEtaInstances
     PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICSpineEta PCUICValidityEta PCUICSREta
     BDTyping BDTypingEta BDTypingEtaInstances BDToPCUICEta BDToPCUICEtaInstances BDFromPCUICEta
     BDUniqueEtaInstances BDStrengthening BDStrengtheningEta.
From MetaRocq.PCUIC Require Import PCUICSigmaCalculus PCUICRenameDef.
From MetaRocq.PCUIC Require PCUICRenameTyp.
From Equations.Type Require Import Relation.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

(** ** The weakenings *)

Definition bs_x : context := [vass si_na si_P].

Definition bs_ur (Γ : context) : urenaming (shiftnP #|Γ| xpred0) Γ (Γ ,,, bs_x) (rshiftk 1) :=
  urenaming_lift0 (shiftnP #|Γ| xpred0) Γ bs_x.

(** ** The η step and its join, weakened (no class) *)

Definition eta1_rename_inst :
  eta1 (rename (rshiftk 1) (tApp (tRel 2) (eta_redex si_na si_P (tRel 1))))
       (rename (rshiftk 1) (tApp (tRel 2) (tRel 1))) :=
  eta1_rename _ _ bd_eta_step (rshiftk 1).

Definition bs_chain :
  clos_refl_trans (union (R_c si_Σ bd_Γη) eta1)
    (tApp (tRel 2) (eta_redex si_na si_P (tRel 1))) (tApp (tRel 2) (tRel 1)) :=
  ltac:(apply rt_step; right; exact bd_eta_step).

Definition bs_lhs : term := tApp (tRel 2) (eta_redex si_na si_P (tRel 1)).
Definition bs_rhs : term := tApp (tRel 2) (tRel 1).

Definition RE_renameP_inst :=
  RE_renameP (Σ := si_Σ) (shiftnP #|bd_Γη| xpred0) bd_Γη (bd_Γη ,,, bs_x) (rshiftk 1) bs_lhs bs_rhs
    (bs_ur bd_Γη) eq_refl eq_refl bs_chain.

Definition bs_join : JoinE si_Σ bd_Γη Cumul (tApp (tRel 2) (eta_redex si_na si_P (tRel 1))) (tApp (tRel 2) (tRel 1)) :=
  JoinE_eta1_l si_Σ bd_Γη Cumul _ _ bd_eta_step.

Definition bs_join_conv : JoinE si_Σ bd_Γη Conv (tApp (tRel 2) (eta_redex si_na si_P (tRel 1))) (tApp (tRel 2) (tRel 1)) :=
  JoinE_eta1_l si_Σ bd_Γη Conv _ _ bd_eta_step.

Definition JoinE_renameP_inst :
  JoinE si_Σ (bd_Γη ,,, bs_x) Cumul (rename (rshiftk 1) (tApp (tRel 2) (eta_redex si_na si_P (tRel 1))))
    (rename (rshiftk 1) (tApp (tRel 2) (tRel 1))) :=
  JoinE_renameP (Σ := si_Σ) (shiftnP #|bd_Γη| xpred0) bd_Γη (bd_Γη ,,, bs_x) (rshiftk 1) Cumul bs_lhs bs_rhs
    (bs_ur bd_Γη) eq_refl eq_refl eq_refl bs_join.

Definition cumul_renamePE_inst :=
  cumul_renamePE (Σ := si_Σ) (A := bs_lhs) (B := bs_rhs) (bs_ur bd_Γη) eq_refl eq_refl eq_refl bs_join.

Definition conv_renamePE_inst :=
  conv_renamePE (Σ := si_Σ) (A := bs_lhs) (B := bs_rhs) (bs_ur bd_Γη) eq_refl eq_refl eq_refl bs_join_conv.

(** ** Free variables of the [match] [bd_case] (no class) *)

Definition on_free_vars_case_predicate_contextE_inst :
  on_free_vars_ctx (shiftnP #|bd_ΓFG| xpred0) (case_predicate_context si_ind si_mdecl si_idecl bd_case_p) :=
  on_free_vars_case_predicate_contextE si_Σ si_ind si_mdecl si_idecl bd_case_p (shiftnP #|bd_ΓFG| xpred0)
    si_wfE si_declared_inductive eq_refl bd_case_wf_pred
    (PCUICEtaCanon.eq_context_upto_names_refl' _).

Definition on_free_vars_case_branch_contextE_inst :=
  on_free_vars_case_branch_contextE (Σ := si_Σ) (wfΣ := si_wfE) (P := shiftnP #|bd_ΓFG| xpred0)
    (ci := (si_ind, 0)) (p := bd_case_p) (br := bd_case_br)
    si_declared_constructor bd_case_wf_pred ltac:(constructor) eq_refl.

Definition on_free_vars_case_branch_typeE_inst :=
  on_free_vars_case_branch_typeE (Σ := si_Σ) (wfΣ := si_wfE) (P := shiftnP #|bd_ΓFG| xpred0)
    (ci := bd_case_ci) (i := 0) (p := bd_case_p) (br := bd_case_br)
    si_declared_constructor bd_case_wf_pred (PCUICEtaCanon.eq_context_upto_names_refl' _)
    ltac:(constructor) eq_refl eq_refl.

(** The type inferred for [bd_case] is scoped in [bd_ΓFG]. *)
Definition infering_on_free_varsE_inst : on_free_vars (shiftnP #|bd_ΓFG| xpred0) (tApp bd_case_ptm bd_case_disc) :=
  infering_on_free_varsE si_Σ si_wfE (shiftnP #|bd_ΓFG| xpred0) bd_ΓFG BDTypingEtaInstances.bd_case _ eq_refl eq_refl inferingE_Case_inst.

Definition bidirectional_on_free_varsE_inst : on_free_vars (shiftnP #|bd_ΓFG| xpred0) (tApp bd_case_ptm bd_case_disc) :=
  fst (snd (snd (snd (snd (bidirectional_on_free_varsE si_Σ si_wfE))))) bd_ΓFG BDTypingEtaInstances.bd_case _ inferingE_Case_inst
    (shiftnP #|bd_ΓFG| xpred0) eq_refl eq_refl.

Definition infering_prod_on_free_varsE_inst :=
  infering_prod_on_free_varsE si_Σ si_wfE (shiftnP #|bd_ΓFG| xpred0) bd_ΓFG (tRel 1) si_na bd_FP si_P
    eq_refl eq_refl bd_G_prod.

(** ** Renaming (no class) *)

(** The reduction witness of [bd_mfix] (a β-step on the declared type), weakened. *)
Definition rename_mfix_on_ind_redE_inst :=
  rename_mfix_on_ind_redE (Σ := si_Σ) (wfΣ := si_wfE) (shiftnP #|bd_Γ1| xpred0) bd_Γ1 (bd_Γ1 ,,, bs_x)
    (rshiftk 1) bd_mfix (bs_ur bd_Γ1) eq_refl ltac:(constructor; [reflexivity|constructor])
    (PCUICRenameTyp.rename_check_one_fix (rshiftk 1) bd_mfix) bd_wf_fixpoint_red.2.2.

(** The [match] [bd_case], with its η-related parameters, weakened. *)
Definition bidirectional_renamingE_inst :
  si_Σ ;;; bd_ΓFG ,,, bs_x |-E rename (rshiftk 1) BDTypingEtaInstances.bd_case ▹ rename (rshiftk 1) (tApp bd_case_ptm bd_case_disc) :=
  fst (snd (snd (snd (snd (bidirectional_renamingE si_Σ si_wfE))))) bd_ΓFG BDTypingEtaInstances.bd_case _ inferingE_Case_inst
    (shiftnP #|bd_ΓFG| xpred0) (bd_ΓFG ,,, bs_x) (rshiftk 1) (bs_ur bd_ΓFG) eq_refl eq_refl.

(** The parameter instance [[G F]] of [bd_case], weakened. *)
Lemma rename_telescopeE_inst :
  PCUICTyping.ctx_inst (checkingE si_Σ) (bd_ΓFG ,,, bs_x) (map (rename (rshiftk 1)) [bd_GF])
    (PCUICSigmaCalculus.rename_telescope (rshiftk 1) [vass si_na si_P]).
Proof.
  eapply (rename_telescopeE si_Σ (shiftnP #|bd_ΓFG| xpred0) (rshiftk 1) bd_ΓFG (bd_ΓFG ,,, bs_x));
    [exact (bs_ur bd_ΓFG)|reflexivity|reflexivity|reflexivity|].
  econstructor; [|constructor].
  exact (fst (snd (snd (snd (bidirectional_renamingE si_Σ si_wfE)))) _ _ _ bd_GF_check).
Qed.

(** ** The lemmas with a forecast class, in a section that holds the classes *)

Section BDStrengtheningClassInstances.

  Context {F18 : SRForecastCopy18}.

  (** The η-typed [x : G F] in [bd_Γη]. *)
  Definition bs_eta_typed : si_Σ ;;; bd_Γη |-E tRel 0 : tApp (tRel 2) (tRel 1) :=
    checking_typingE si_Σ bd_Γη (tRel 0) (tApp (tRel 2) (tRel 1)) si_wfE bdi_wfη
      bdi_GF_eta_isType checkingE_eta_inst.

  Definition on_free_vars_typeE_inst :=
    on_free_vars_typeE (shiftnP #|bd_Γη| xpred0) si_Σ si_wfE bd_Γη (tRel 0) _ eq_refl eq_refl bs_eta_typed.

  Definition bs_renaming : renamingE (shiftnP #|bd_Γη| xpred0) si_Σ bd_Γη (bd_Γη ,,, bs_x) (rshiftk 1) :=
    (iv_wf_P si_Σ bd_Γη bdi_wfη, bs_ur bd_Γη).

  Definition typing_renaming_cond_PE_inst :=
    typing_renaming_cond_PE (Σ := si_Σ) (wfΣ := si_wfE) (t := tRel 0) bs_renaming eq_refl eq_refl bs_eta_typed.

  (** [y : d; d := Prop : Type] with the unused [x : Prop] inserted: [y] is [tRel 1] there, of
      type the let-variable [d] ([tRel 2]), which is [Prop] only by its δ-step. *)
  Definition bs_Γdx : context := bu_Γd ,,, bs_x ,,, lift_context #|bs_x| 0 [].

  Lemma bs_wf_Γdx : wf_localE si_Σ bs_Γdx.
  Proof. exact (iv_wf_P si_Σ bu_Γd bu_wf_Γd). Qed.

  Lemma bs_y_lifted_typed : si_Σ ;;; bs_Γdx |-E lift #|bs_x| #|([] : context)| (tRel 0) : tSort sProp.
  Proof.
    change (si_Σ ;;; bs_Γdx |-E tRel 1 : tSort sProp).
    pose proof (typeE_Rel si_Σ bs_Γdx 1 (vass si_na (tRel 0)) bs_wf_Γdx eq_refl) as hd.
    eapply (typeE_Cumul _ _ (tRel 1) (lift0 2 (tRel 0)) (tSort sProp) (Sort.super sProp) hd).
    - exact (iv_P_typed si_Σ _ bs_wf_Γdx).
    - exact (cumulE_rel si_Σ bs_Γdx Cumul 2 si_P eq_refl).
  Qed.

  Definition strengtheningE_inst :=
    strengtheningE (Σ := si_Σ) (wfΣ := si_wfE) bu_Γd bs_x [] (tRel 0) (tSort sProp) bs_y_lifted_typed.

  (** The T8 site, reached with the let-variable [d] as the inferred type. *)
  Definition strengthening_typeE_inst :
    ∑ s', si_Σ ;;; bu_Γd ,,, [] |-E tRel 0 : tSort s' × leq_sort si_Σ s' sProp :=
    strengthening_typeE (Σ := si_Σ) (wfΣ := si_wfE) bu_Γd bs_x [] (tRel 0) sProp bs_y_lifted_typed.

End BDStrengtheningClassInstances.
