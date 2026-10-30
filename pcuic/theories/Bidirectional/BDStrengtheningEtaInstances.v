(* Distributed under the terms of the MIT license. *)

(* NONDEGEN tags: an INSTANCE NONDEGEN tag is a reader judgment backed by a compiled nontriviality
   lemma, not a mechanical guarantee.
   Measured reader miss rate: 10 of 60 sampled instances (residual 16.7%, 95% upper bound 26.6%), seed 202610301905, measured on the pre-retag head; H' additionally corrects 10 tags and 7 prose rows that review found false, so the figure is conservative here. *)

(** * Satisfying instances of the lemmas of [Bidirectional/BDStrengtheningEta] (row T6)

  **The environment** is [si_Σ] ([PCUICCumulativitySpecEtaClosureInstances]:
  [Inductive I (A : Prop) : Prop := c : I A], with [si_wfE]). The derivations are those of
  [BDTypingEtaInstances] ([bd_ΓFG = [F : Prop → Prop; G : (Prop → Prop) → Prop]], the [match]
  [bd_case] with the η-related parameters, the η check [x ◃ G F] in [bd_Γη]),
  [BDToPCUICEtaInstances] and [BDUniqueEtaInstances] ([bu_Γd = [y : d; d := Prop : Type]]).

  **The renamings** are weakenings by one assumption ([urenaming_lift0]), with the predicate
  [P] the scope of the source context ([shiftnP #|Γ| xpred0]), so the free-variable premises are
  the real ones.

  **Every lemma** is applied here with no class: the four that use soundness, completeness,
  validity or subject reduction ([on_free_vars_typeE], [typing_renaming_cond_PE],
  [strengtheningE], [strengthening_typeE]) are applied in section [BDStrengtheningClassInstances],
  whose [Context] held T1's forecast class until copy 18b landed (frac/eta 3e6b422d).

  **Non-degeneracy.** Each instance carries a tag [INSTANCE NONDEGEN <lemma>] that names the
  compiled lemma stating the property below of its witnesses; the rows are tagged at each
  instance.
  - [eta1_rename_inst], [RE_renameP_inst], [JoinE_renameP_inst], [cumul_renamePE_inst],
    [conv_renamePE_inst]: the η step [G (λ y. F y) ⇝η G F] of [bd_eta_step] and its join,
    weakened: the two terms differ and the weakening moves each ([bs_eta_nondeg]).
  - the scoping lemmas run on objects that are not closed, so the scoping is not implied by
    closedness: the predicate context and the branch type of the [match] [bd_case], the type
    that [inferingE_Case_inst] infers for [bd_case], and [bd_case] itself ([bs_case_open]); the
    branch context [f : G F] of a branch of the record [R] of [iv_Σ] ([bs_rbr],
    [bs_rbranch_open]; the constructor of [I] has no argument, so a branch of [bd_case] has an
    empty context); the codomain [F y] of the product inferred for [h : Π y : Prop. F y]
    ([bs_h_prod], [bs_hB_open]).
  - [bidirectional_renamingE_inst] on the [match] [bd_case] and [rename_telescopeE_inst] on its
    parameter instance, both moved by the weakening; the parameter [G F] of [bd_case] is not
    [G (λ y. F y)] ([bs_case_moves]). [rename_mfix_on_ind_redE_inst] on the reduction witness of
    the fixpoint [bd_mfix], whose declared type fails [check_one_fix] and which the weakening
    moves ([bs_mfix_moves]).
  - [typing_renaming_cond_PE_inst] and [on_free_vars_typeE_inst] on the typing [x : G F] in
    [bd_Γη], at a type that no inference gives [x] there ([bs_eta_typed_nondeg]).
  - [strengtheningE_inst] and [strengthening_typeE_inst] remove the unused assumption [x : Prop]
    from [y : d; d := Prop : Type] for [y]: the term really is lifted, and no type inferred for
    the lifted [y] is a sort ([bs_strengthening_nondeg]). *)

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

(* WITNESSES: bs_* *)

(** ** The weakenings *)

Definition bs_x : context := [vass si_na si_P].

Definition bs_ur (Γ : context) : urenaming (shiftnP #|Γ| xpred0) Γ (Γ ,,, bs_x) (rshiftk 1) :=
  urenaming_lift0 (shiftnP #|Γ| xpred0) Γ bs_x.

(** ** The η step and its join, weakened (no class) *)

Definition bs_lhs : term := tApp (tRel 2) (eta_redex si_na si_P (tRel 1)).
Definition bs_rhs : term := tApp (tRel 2) (tRel 1).

(** [G (λ y. F y)] and [G F] differ, and the weakening by [x : Prop] moves each of them (both
    mention [F] and [G]). *)
Lemma bs_eta_nondeg :
  bs_lhs <> bs_rhs /\ rename (rshiftk 1) bs_lhs <> bs_lhs /\ rename (rshiftk 1) bs_rhs <> bs_rhs.
Proof. repeat split; discriminate. Qed.

(** INSTANCE NONDEGEN BDStrengtheningEtaInstances.bs_eta_nondeg *)
Definition eta1_rename_inst :
  eta1 (rename (rshiftk 1) (tApp (tRel 2) (eta_redex si_na si_P (tRel 1))))
       (rename (rshiftk 1) (tApp (tRel 2) (tRel 1))) :=
  eta1_rename bs_lhs bs_rhs bd_eta_step (rshiftk 1).

Definition bs_chain :
  clos_refl_trans (union (R_c si_Σ bd_Γη) eta1)
    (tApp (tRel 2) (eta_redex si_na si_P (tRel 1))) (tApp (tRel 2) (tRel 1)) :=
  ltac:(apply rt_step; right; exact bd_eta_step).

(** INSTANCE NONDEGEN BDStrengtheningEtaInstances.bs_eta_nondeg *)
Definition RE_renameP_inst :=
  RE_renameP (Σ := si_Σ) (shiftnP #|bd_Γη| xpred0) bd_Γη (bd_Γη ,,, bs_x) (rshiftk 1) bs_lhs bs_rhs
    (bs_ur bd_Γη) eq_refl eq_refl bs_chain.

Definition bs_join : JoinE si_Σ bd_Γη Cumul (tApp (tRel 2) (eta_redex si_na si_P (tRel 1))) (tApp (tRel 2) (tRel 1)) :=
  JoinE_eta1_l si_Σ bd_Γη Cumul _ _ bd_eta_step.

Definition bs_join_conv : JoinE si_Σ bd_Γη Conv (tApp (tRel 2) (eta_redex si_na si_P (tRel 1))) (tApp (tRel 2) (tRel 1)) :=
  JoinE_eta1_l si_Σ bd_Γη Conv _ _ bd_eta_step.

(** INSTANCE NONDEGEN BDStrengtheningEtaInstances.bs_eta_nondeg *)
Definition JoinE_renameP_inst :
  JoinE si_Σ (bd_Γη ,,, bs_x) Cumul (rename (rshiftk 1) (tApp (tRel 2) (eta_redex si_na si_P (tRel 1))))
    (rename (rshiftk 1) (tApp (tRel 2) (tRel 1))) :=
  JoinE_renameP (Σ := si_Σ) (shiftnP #|bd_Γη| xpred0) bd_Γη (bd_Γη ,,, bs_x) (rshiftk 1) Cumul bs_lhs bs_rhs
    (bs_ur bd_Γη) eq_refl eq_refl eq_refl bs_join.

(** INSTANCE NONDEGEN BDStrengtheningEtaInstances.bs_eta_nondeg *)
Definition cumul_renamePE_inst :=
  cumul_renamePE (Σ := si_Σ) (A := bs_lhs) (B := bs_rhs) (bs_ur bd_Γη) eq_refl eq_refl eq_refl bs_join.

(** INSTANCE NONDEGEN BDStrengtheningEtaInstances.bs_eta_nondeg *)
Definition conv_renamePE_inst :=
  conv_renamePE (Σ := si_Σ) (A := bs_lhs) (B := bs_rhs) (bs_ur bd_Γη) eq_refl eq_refl eq_refl bs_join_conv.

(** ** Free variables of the [match] [bd_case] (no class) *)

(** The predicate context [z : I (G F)], the branch type [(λ z : I (G F). Prop) (c (G F))], the
    type [(λ z : I (G F). Prop) (c (G (λ y. F y)))] (the one [inferingE_Case_inst] infers for
    [bd_case]) and [bd_case] itself mention [F] and [G]: none is closed, so their scoping in
    [bd_ΓFG] is not implied by closedness. *)
Lemma bs_case_open :
  [/\ closedn_ctx 0 (case_predicate_context si_ind si_mdecl si_idecl bd_case_p) = false,
      closedn 0 (case_branch_type bd_case_ci si_mdecl si_idecl bd_case_p bd_case_br
                   (it_mkLambda_or_LetIn (case_predicate_context bd_case_ci si_mdecl si_idecl bd_case_p)
                      (preturn bd_case_p)) 0 si_cdecl).2 = false,
      closedn 0 (tApp bd_case_ptm bd_case_disc) = false &
      closedn 0 BDTypingEtaInstances.bd_case = false].
Proof. split; reflexivity. Qed.

(** INSTANCE NONDEGEN BDStrengtheningEtaInstances.bs_case_open *)
Definition on_free_vars_case_predicate_contextE_inst :
  on_free_vars_ctx (shiftnP #|bd_ΓFG| xpred0) (case_predicate_context si_ind si_mdecl si_idecl bd_case_p) :=
  on_free_vars_case_predicate_contextE si_Σ si_ind si_mdecl si_idecl bd_case_p (shiftnP #|bd_ΓFG| xpred0)
    si_wfE si_declared_inductive eq_refl bd_case_wf_pred
    (PCUICEtaCanon.eq_context_upto_names_refl' _).

(** A [match] on the record [R] of [iv_Σ] ([PCUICInversionEtaInstances]) at the parameter [G F]
    of [bd_ΓFG]: the branch of [mkR] binds its field [f : A]. *)
Definition bs_rp : predicate term :=
  {| pparams := [bd_GF]; puinst := []; pcontext := ind_predicate_context iv_ind iv_mdecl iv_idecl;
     preturn := si_P |}.
Definition bs_rbr : branch term := {| bcontext := [vass iv_fna (tRel 0)]; bbody := tRel 0 |}.

Lemma bs_rp_wf : wf_predicate iv_mdecl iv_idecl bs_rp.
Proof. split; [reflexivity|]. constructor; [reflexivity|constructor]. Qed.

Lemma bs_rbr_wf : wf_branch iv_cdecl bs_rbr.
Proof. constructor; [reflexivity|constructor]. Qed.

(** The branch context of [bs_rbr] is [f : G F]: not empty, and it mentions [F] and [G]. *)
Lemma bs_rbranch_open :
  closedn_ctx 0 (case_branch_context iv_ind iv_mdecl bs_rp (forget_types (bcontext bs_rbr)) iv_cdecl) = false.
Proof. reflexivity. Qed.

(** INSTANCE NONDEGEN BDStrengtheningEtaInstances.bs_rbranch_open *)
Definition on_free_vars_case_branch_contextE_inst :=
  on_free_vars_case_branch_contextE (Σ := iv_Σ) (wfΣ := iv_wfE) (P := shiftnP #|bd_ΓFG| xpred0)
    (ci := (iv_ind, 0)) (p := bs_rp) (br := bs_rbr)
    iv_declared_constructor bs_rp_wf bs_rbr_wf eq_refl.

(** INSTANCE NONDEGEN BDStrengtheningEtaInstances.bs_case_open *)
Definition on_free_vars_case_branch_typeE_inst :=
  on_free_vars_case_branch_typeE (Σ := si_Σ) (wfΣ := si_wfE) (P := shiftnP #|bd_ΓFG| xpred0)
    (ci := bd_case_ci) (i := 0) (p := bd_case_p) (br := bd_case_br)
    si_declared_constructor bd_case_wf_pred (PCUICEtaCanon.eq_context_upto_names_refl' _)
    ltac:(constructor) eq_refl eq_refl.

(** The type that [inferingE_Case_inst] infers for [bd_case] is scoped in [bd_ΓFG]; it is not
    closed ([bs_case_open]).
    INSTANCE NONDEGEN BDStrengtheningEtaInstances.bs_case_open *)
Definition infering_on_free_varsE_inst : on_free_vars (shiftnP #|bd_ΓFG| xpred0) (tApp bd_case_ptm bd_case_disc) :=
  infering_on_free_varsE si_Σ si_wfE (shiftnP #|bd_ΓFG| xpred0) bd_ΓFG BDTypingEtaInstances.bd_case _ eq_refl eq_refl inferingE_Case_inst.

(** INSTANCE NONDEGEN BDStrengtheningEtaInstances.bs_case_open *)
Definition bidirectional_on_free_varsE_inst : on_free_vars (shiftnP #|bd_ΓFG| xpred0) (tApp bd_case_ptm bd_case_disc) :=
  fst (snd (snd (snd (snd (bidirectional_on_free_varsE si_Σ si_wfE))))) bd_ΓFG BDTypingEtaInstances.bd_case _ inferingE_Case_inst
    (shiftnP #|bd_ΓFG| xpred0) eq_refl eq_refl.

(** [h : Π y : Prop. F y] in front of [bd_ΓFG]: the product inferred for [h] has the codomain
    [bs_hB = F y], with [F] lifted past [h] and [y]. *)
Definition bs_hB : term := tApp (tRel 2) (tRel 0).
Definition bs_Γh : context := vass si_na (tProd si_na si_P (tApp (tRel 1) (tRel 0))) :: bd_ΓFG.

Lemma bs_h_prod : si_Σ ;;; bs_Γh |-E tRel 0 ▹Π (si_na, si_P, bs_hB).
Proof.
  econstructor; [exact (inferE_Rel _ bs_Γh 0 (vass si_na (tProd si_na si_P (tApp (tRel 1) (tRel 0)))) eq_refl)|].
  apply rt_refl.
Qed.

(** [bs_hB] mentions [F], a variable of [bs_Γh] (index 2 under the product's binder): the scoping
    of the codomain is not vacuous. *)
Lemma bs_hB_open : closedn 1 bs_hB = false.
Proof. reflexivity. Qed.

(** INSTANCE NONDEGEN BDStrengtheningEtaInstances.bs_hB_open *)
Definition infering_prod_on_free_varsE_inst :=
  infering_prod_on_free_varsE si_Σ si_wfE (shiftnP #|bs_Γh| xpred0) bs_Γh (tRel 0) si_na si_P bs_hB
    eq_refl eq_refl bs_h_prod.

(** ** Renaming (no class) *)

(** [bd_mfix]: [check_one_fix] fails on its declared type, and the weakening moves it (its type
    mentions [A]). *)
Lemma bs_mfix_moves :
  map check_one_fix bd_mfix = [None] /\
  map (map_def (rename (rshiftk 1)) (rename (shiftn #|bd_mfix| (rshiftk 1)))) bd_mfix <> bd_mfix.
Proof. split; [reflexivity|discriminate]. Qed.

(** The reduction witness of [bd_mfix] ([bd_wf_fixpoint_red]), weakened.
    INSTANCE NONDEGEN BDStrengtheningEtaInstances.bs_mfix_moves *)
Definition rename_mfix_on_ind_redE_inst :=
  rename_mfix_on_ind_redE (Σ := si_Σ) (wfΣ := si_wfE) (shiftnP #|bd_Γ1| xpred0) bd_Γ1 (bd_Γ1 ,,, bs_x)
    (rshiftk 1) bd_mfix (bs_ur bd_Γ1) eq_refl ltac:(constructor; [reflexivity|constructor])
    (PCUICRenameTyp.rename_check_one_fix (rshiftk 1) bd_mfix) bd_wf_fixpoint_red.2.2.

(** The [match] [bd_case]: its parameter [G F] is not [G (λ y. F y)], and the weakening moves
    [bd_case] and its parameter list. *)
Lemma bs_case_moves :
  [/\ bd_X <> bd_GF,
      rename (rshiftk 1) BDTypingEtaInstances.bd_case <> BDTypingEtaInstances.bd_case &
      map (rename (rshiftk 1)) [bd_GF] <> [bd_GF]].
Proof. split; [unfold bd_X, bd_GF, BDTypingEtaInstances.bd_lam; discriminate|discriminate|discriminate]. Qed.

(** The [match] [bd_case], weakened.
    INSTANCE NONDEGEN BDStrengtheningEtaInstances.bs_case_moves *)
Definition bidirectional_renamingE_inst :
  si_Σ ;;; bd_ΓFG ,,, bs_x |-E rename (rshiftk 1) BDTypingEtaInstances.bd_case ▹ rename (rshiftk 1) (tApp bd_case_ptm bd_case_disc) :=
  fst (snd (snd (snd (snd (bidirectional_renamingE si_Σ si_wfE))))) bd_ΓFG BDTypingEtaInstances.bd_case _ inferingE_Case_inst
    (shiftnP #|bd_ΓFG| xpred0) (bd_ΓFG ,,, bs_x) (rshiftk 1) (bs_ur bd_ΓFG) eq_refl eq_refl.

(** The parameter instance [[G F]] of [bd_case], weakened.
    INSTANCE NONDEGEN BDStrengtheningEtaInstances.bs_case_moves *)
Lemma rename_telescopeE_inst :
  PCUICTyping.ctx_inst (checkingE si_Σ) (bd_ΓFG ,,, bs_x) (map (rename (rshiftk 1)) [bd_GF])
    (PCUICSigmaCalculus.rename_telescope (rshiftk 1) [vass si_na si_P]).
Proof.
  eapply (rename_telescopeE si_Σ (shiftnP #|bd_ΓFG| xpred0) (rshiftk 1) bd_ΓFG (bd_ΓFG ,,, bs_x));
    [exact (bs_ur bd_ΓFG)|reflexivity|reflexivity|reflexivity|].
  econstructor; [|constructor].
  exact (fst (snd (snd (snd (bidirectional_renamingE si_Σ si_wfE)))) _ _ _ bd_GF_check).
Qed.

(** ** The lemmas that took a forecast class until copy 18b landed *)

Section BDStrengtheningClassInstances.

  (** The typing [x : G F] in [bd_Γη]: soundness on the check [checkingE_eta_inst]. *)
  Definition bs_eta_typed : si_Σ ;;; bd_Γη |-E tRel 0 : tApp (tRel 2) (tRel 1) :=
    checking_typingE si_Σ bd_Γη (tRel 0) (tApp (tRel 2) (tRel 1)) si_wfE bdi_wfη
      bdi_GF_eta_isType checkingE_eta_inst.

  (** [x : G F] in [bd_Γη]: no type inferred for [x] there is [G F]; [G F] mentions [G], the
      last variable of [bd_Γη]; the weakening moves it. *)
  Lemma bs_eta_typed_nondeg :
    [/\ (forall T', si_Σ ;;; bd_Γη |-E tRel 0 ▹ T' -> T' <> tApp (tRel 2) (tRel 1)),
        on_free_vars (shiftnP (#|bd_Γη| - 1) xpred0) (tApp (tRel 2) (tRel 1)) = false &
        rename (rshiftk 1) (tApp (tRel 2) (tRel 1)) <> tApp (tRel 2) (tRel 1)].
  Proof.
    split; [|reflexivity|discriminate].
    intros T' h. inversion h; subst.
    match goal with hn : nth_error _ _ = Some _ |- _ => vm_compute in hn; injection hn as hd; subst end.
    discriminate.
  Qed.

  (** INSTANCE NONDEGEN BDStrengtheningEtaInstances.bs_eta_typed_nondeg *)
  Definition on_free_vars_typeE_inst :=
    on_free_vars_typeE (shiftnP #|bd_Γη| xpred0) si_Σ si_wfE bd_Γη (tRel 0) _ eq_refl eq_refl bs_eta_typed.

  Definition bs_renaming : renamingE (shiftnP #|bd_Γη| xpred0) si_Σ bd_Γη (bd_Γη ,,, bs_x) (rshiftk 1) :=
    (iv_wf_P si_Σ bd_Γη bdi_wfη, bs_ur bd_Γη).

  (** INSTANCE NONDEGEN BDStrengtheningEtaInstances.bs_eta_typed_nondeg *)
  Definition typing_renaming_cond_PE_inst :=
    typing_renaming_cond_PE (Σ := si_Σ) (wfΣ := si_wfE) (t := tRel 0) bs_renaming eq_refl eq_refl bs_eta_typed.

  (** [y : d; d := Prop : Type] with the unused [x : Prop] inserted: [y] is [tRel 1] there, of
      declared type the let-variable [d] ([tRel 2]), whose body is [Prop]. *)
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

  (** Strengthening removes [x : Prop] from [bu_Γd ,,, [x : Prop]]: the term really is lifted
      ([tRel 0] becomes [tRel 1]), and no type inferred for the lifted [y] in [bs_Γdx] is a
      sort. *)
  Lemma bs_strengthening_nondeg :
    lift #|bs_x| #|([] : context)| (tRel 0) <> tRel 0 /\
    (forall T', si_Σ ;;; bs_Γdx |-E tRel 1 ▹ T' -> forall s, T' <> tSort s).
  Proof.
    split; [discriminate|].
    intros T' h s. inversion h; subst.
    match goal with hn : nth_error _ _ = Some _ |- _ => vm_compute in hn; injection hn as hd; subst end.
    discriminate.
  Qed.

  (** INSTANCE NONDEGEN BDStrengtheningEtaInstances.bs_strengthening_nondeg *)
  Definition strengtheningE_inst :=
    strengtheningE (Σ := si_Σ) (wfΣ := si_wfE) bu_Γd bs_x [] (tRel 0) (tSort sProp) bs_y_lifted_typed.

  (** [strengthening_typeE] at the lifted [y], no type inferred for which is a sort.
      INSTANCE NONDEGEN BDStrengtheningEtaInstances.bs_strengthening_nondeg *)
  Definition strengthening_typeE_inst :
    ∑ s', si_Σ ;;; bu_Γd ,,, [] |-E tRel 0 : tSort s' × leq_sort si_Σ s' sProp :=
    strengthening_typeE (Σ := si_Σ) (wfΣ := si_wfE) bu_Γd bs_x [] (tRel 0) sProp bs_y_lifted_typed.

End BDStrengtheningClassInstances.
