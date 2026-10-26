(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICEquality PCUICTyping PCUICReduction PCUICSigmaCalculus
     PCUICNamelessDef PCUICRenameDef PCUICInstDef.

(** The closure properties of the guard condition.  Under decision D1 the
    guard is [guard_cl] ([PCUICGuardClosure]), the least predicate closed
    under exactly these seven operations, so every field below is a theorem
    and [guard_checking_correct] is no longer an axiom.

    [guard_red1] and [guard_inst] carry the syntactic premises the closure
    needs: a reduction may bring syntax in from the environment or from the
    context, and a substitution brings in the images of [σ].  Both are
    discharged from typing at their call sites, through
    [Typing/PCUICCasesWfTyp]. *)

Definition nl_mfix mfix := map (map_def_anon nl nl) mfix.

Class GuardCheckerCorrect :=
{
  guard_red1 b Σ Γ mfix mfix' idx :
    wf_cases_env Σ.1 ->
    wf_cases_ctx Σ.1 Γ ->
    Σ.1 ;;; Γ |- tFixCoFix b mfix idx ⇝ tFixCoFix b mfix' idx ->
    guard b Σ Γ mfix ->
    guard b Σ Γ mfix' ;

  guard_eq_term b Σ Γ mfix mfix' idx :
    upto_names (tFixCoFix b mfix idx) (tFixCoFix b mfix' idx) ->
    guard b Σ Γ mfix ->
    guard b Σ Γ mfix' ;

  guard_extends b (Σ Σ':global_env_ext) Γ mfix :
    extends Σ Σ' ->
    guard b Σ Γ mfix ->
    guard b Σ' Γ mfix ;

  guard_context_cumulativity `{checker_flags} b Σ Γ Γ' mfix :
    All2_fold (cumul_decls cumulSpec0 Σ) Γ' Γ ->
    guard b Σ Γ mfix ->
    guard b Σ Γ' mfix ;

  guard_subst_instance `{checker_flags} b Σ Γ mfix u univs :
    consistent_instance_ext (Σ.1, univs) Σ.2 u ->
    guard b Σ Γ mfix ->
    guard b (Σ.1, univs) (subst_instance u Γ) (subst_instance_mfix mfix u) ;

  guard_inst `{checker_flags} b Σ Γ Δ mfix σ :
    Σ ;;; Γ ⊢ σ : Δ ->
    closedn_mfix #|Δ| mfix ->
    (forall x, x < #|Δ| -> wf_cases Σ.1 (σ x)) ->
    guard b Σ Δ mfix ->
    guard b Σ Γ (inst_mfix mfix σ) ;

  guard_rename `{checker_flags} b P Σ Γ Δ mfix f :
    urenaming P Γ Δ f ->
    guard b Σ Γ mfix ->
    guard b Σ Δ (rename_mfix mfix f) ;

}.

#[global]
Instance guard_checking_correct : GuardCheckerCorrect.
Proof.
  constructor.
  - intros b Σ Γ mfix mfix' idx henv hctx hred hg.
    eapply gc_red1; tea. now constructor.
  - intros b Σ Γ mfix mfix' idx heq hg.
    eapply gc_eq; tea. now constructor.
  - intros b Σ Σ' Γ mfix hext hg. now eapply gc_ext.
  - intros cf b Σ Γ Γ' mfix hcum hg.
    eapply gc_ctx; tea. now constructor.
  - intros cf b Σ Γ mfix u univs hcons hg. now eapply gc_univ.
  - intros cf b Σ Γ Δ mfix σ hσ hcl hwf hg. now eapply gc_inst.
  - intros cf b P Σ Γ Δ mfix f hren hg. now eapply gc_ren.
Qed.

Definition fix_guard_red1 := guard_red1 Fix.
Definition fix_guard_eq_term := guard_eq_term Fix.
Definition fix_guard_subst_instance `{checker_flags} := guard_subst_instance Fix.
Definition fix_guard_extends := guard_extends Fix.
Definition fix_guard_context_cumulativity `{checker_flags} := guard_context_cumulativity Fix.
Definition fix_guard_inst `{checker_flags} := guard_inst Fix.
Definition fix_guard_rename `{checker_flags} := guard_rename Fix.

Definition cofix_guard_red1 := guard_red1 CoFix.
Definition cofix_guard_eq_term := guard_eq_term CoFix.
Definition cofix_guard_subst_instance `{checker_flags} := guard_subst_instance CoFix.
Definition cofix_guard_extends := guard_extends CoFix.
Definition cofix_guard_context_cumulativity `{checker_flags} := guard_context_cumulativity CoFix.
Definition cofix_guard_inst `{checker_flags} := guard_inst CoFix.
Definition cofix_guard_rename `{checker_flags} := guard_rename CoFix.
