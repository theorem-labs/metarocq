(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances for [Bidirectional/BDTypingEta]

  Each judgment of [BDTypingEta] is inhabited by a small concrete derivation, and each
  lemma of that file with a premise is applied to a concrete case with every premise
  proved, so the premises are shown to be jointly satisfiable:

  - [inferingE_inst], [infering_sortE_inst], [infering_prodE_inst],
    [infering_induE_inst], [checkingE_inst], [wf_local_bdE_inst],
    [wf_local_bd_relE_inst]: one derivation of each judgment, in [si_Σ]
    ([PCUICCumulativitySpecEtaClosureInstances]: one inductive
    [I (A : Prop) : Prop] with one constructor [c : I A]);
  - [checkingE_eta_inst]: a check whose conversion premise is an η step: in the context
    [G : (Prop → Prop) → Prop, F : Prop → Prop, x : G (λ y : Prop. F y)], which is
    well formed for [wf_local_bdE] ([wf_local_bdE_eta_inst]), [x ◃ G F];
  - the size functions and the induction principle: [inferingE_size_pos_inst] and
    [bidir_ind_envE_inst] (every predicate [unit], so every case hypothesis holds);
  - the bridges to the checker's forecast form, [checkE_Cumul_ws_inst],
    [All2_ws_cumul_pbE_JoinE_inst], [JoinE_ws_cumul_pbE_inst], on that η pair;
  - the (co)fixpoint witness bridges, [wf_fixpoint_red_wf_fixpointE_inst],
    [wf_cofixpoint_red_wf_cofixpointE_inst], [mfix_on_ind_red_convE_inst], at a
    declared type whose witness is a β-reduct, not the type itself: [(λ B : Prop. I B) A]
    reduces to [I A]. The cofixpoint uses [bd_coenv], [si_env] with the block
    declared [CoFinite]; [bd_cocb] gives its [ClosedBodies]. The typed form gets its
    [wfE si_env] from [si_wfE] and types the declared type over [typingE]
    ([bd_fix_dtype_isTypeE]). *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICReduction PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICClosedBodies PCUICTypingEta
     PCUICCumulativitySpecEtaClosureInstances PCUICEtaDefs PCUICEtaI5 PCUICWellScopedCumulativity
     PCUICWellScopedCumulativityEta BDTyping BDTypingEta.
From Equations.Type Require Import Relation.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

(** ** Helpers in [si_Σ] *)

Lemma bd_vass (Γ : context) (na : aname) A s :
  si_Σ ;;; Γ |-E A ▹□ s -> isSortRel s na.(binder_relevance) ->
  lift_sorting (checkingE si_Σ Γ) (infering_sortE si_Σ Γ) (j_vass na A).
Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [exact I|exact r]. Qed.

Lemma bd_vass_s (Γ : context) (na : aname) A s :
  si_Σ ;;; Γ |-E A ▹□ s -> isSortRel s na.(binder_relevance) ->
  lift_sorting (checkingE si_Σ Γ) (infering_sortE si_Σ Γ) (j_vass_s na A s).
Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [reflexivity|exact r]. Qed.

Lemma bd_P_infer (Γ : context) : si_Σ ;;; Γ |-E si_P ▹ tSort (Sort.super sProp).
Proof. apply inferE_Sort. cbn; trivial. Qed.

Lemma bd_P_sort (Γ : context) : si_Σ ;;; Γ |-E si_P ▹□ Sort.super sProp.
Proof. econstructor; [exact (bd_P_infer Γ)|apply rt_refl]. Qed.

(** [x ◃ P] for the last variable [x : P]. *)
Lemma bd_rel0_check (Γ : context) : si_Σ ;;; Γ ,, vass si_na si_P |-E tRel 0 ◃ si_P.
Proof. econstructor; [exact (inferE_Rel _ (Γ ,, vass si_na si_P) 0 (vass si_na si_P) eq_refl)|apply JoinE_refl]. Qed.

Definition bd_Γ1 : context := [vass si_na si_P].

(** ** One derivation of each judgment *)

Lemma inferingE_inst : si_Σ ;;; [] |-E tSort sProp ▹ tSort (Sort.super sProp).
Proof. exact (bd_P_infer []). Qed.

Lemma infering_sortE_inst : si_Σ ;;; [] |-E tSort sProp ▹□ Sort.super sProp.
Proof. exact (bd_P_sort []). Qed.

(** [λ x : P. x ▹ Π x : P. P]. *)
Lemma bd_id_infer : si_Σ ;;; [] |-E tLambda si_na si_P (tRel 0) ▹ tProd si_na si_P (lift0 1 si_P).
Proof.
  apply inferE_Lambda.
  - exact (bd_vass [] si_na si_P _ (bd_P_sort []) eq_refl).
  - exact (inferE_Rel _ ([] ,, vass si_na si_P) 0 (vass si_na si_P) eq_refl).
Qed.

Lemma infering_prodE_inst :
  si_Σ ;;; [] |-E tLambda si_na si_P (tRel 0) ▹Π (si_na, si_P, lift0 1 si_P).
Proof. econstructor; [exact bd_id_infer|apply rt_refl]. Qed.

(** [c x ▹{I} ([], [x])] for [x : P]. *)
Lemma bd_cstr_infer (Γ : context) :
  si_Σ ;;; Γ |-E tConstruct si_ind 0 [] ▹ tProd si_na si_P (tApp (tInd si_ind []) (tRel 0)).
Proof.
  refine (inferE_Construct _ _ si_ind 0 [] si_mdecl si_idecl si_cdecl si_declared_constructor _).
  reflexivity.
Qed.

Lemma bd_cstr_prod (Γ : context) :
  si_Σ ;;; Γ |-E tConstruct si_ind 0 [] ▹Π (si_na, si_P, tApp (tInd si_ind []) (tRel 0)).
Proof. econstructor; [exact (bd_cstr_infer Γ)|apply rt_refl]. Qed.

Lemma bd_app_infer :
  si_Σ ;;; bd_Γ1 |-E tApp (tConstruct si_ind 0 []) (tRel 0) ▹ (tApp (tInd si_ind []) (tRel 0)) {0 := tRel 0}.
Proof. exact (inferE_App _ _ _ _ _ _ _ (bd_cstr_prod bd_Γ1) (bd_rel0_check [])). Qed.

Lemma infering_induE_inst :
  si_Σ ;;; bd_Γ1 |-E tApp (tConstruct si_ind 0 []) (tRel 0) ▹{si_ind} ([], [tRel 0]).
Proof. econstructor; [exact bd_app_infer|apply rt_refl]. Qed.

Lemma checkingE_inst : si_Σ ;;; bd_Γ1 |-E tRel 0 ◃ si_P.
Proof. exact (bd_rel0_check []). Qed.

Lemma wf_local_bdE_inst : wf_local_bdE si_Σ bd_Γ1.
Proof.
  unfold bd_Γ1.
  apply localenv_cons_abs; [constructor|exact (bd_vass [] si_na si_P _ (bd_P_sort []) eq_refl)].
Qed.

(** ** The size functions and the induction principle *)

Lemma inferingE_size_pos_inst : inferingE_size inferingE_inst > 0.
Proof. exact (inferingE_size_pos inferingE_inst). Qed.

(** Every predicate [unit]: each case hypothesis of [bidir_ind_envE] holds. *)
Lemma bidir_ind_envE_inst :
  env_prop_bdE si_Σ (fun _ _ _ => unit) (fun _ _ _ => unit) (fun _ _ _ => unit)
    (fun _ _ _ _ _ => unit) (fun _ _ _ _ _ => unit) (fun _ _ => unit) (fun _ => unit) (fun _ _ => unit).
Proof. eapply bidir_ind_envE; first [exact si_wfE | intros; exact tt]. Qed.

(** ** A check by an η step

  [G : (Prop → Prop) → Prop, F : Prop → Prop, x : G (λ y : Prop. F y)] ⊢ [x ◃ G F]:
  [λ y : Prop. F y] is [eta_redex si_na si_P F] ([bd_lam_eta_redex]); it η-contracts to [F]. *)

Definition bd_s1 : sort := Sort.sort_of_product (Sort.super sProp) (Sort.super sProp).
Definition bd_FP : term := tProd si_na si_P si_P.
Definition bd_GP : term := tProd si_na bd_FP si_P.
(** In [[F; G]]: [λ y : Prop. F y] and [G (λ y : Prop. F y)]. *)
Definition bd_lam : term := tLambda si_na si_P (tApp (tRel 1) (tRel 0)).
Definition bd_X : term := tApp (tRel 1) bd_lam.
Definition bd_ΓFG : context := [vass si_na bd_FP; vass si_na bd_GP].
Definition bd_Γη : context := vass si_na bd_X :: bd_ΓFG.

Lemma bd_lam_eta_redex : bd_lam = eta_redex si_na si_P (tRel 0).
Proof. reflexivity. Qed.

Lemma bd_FP_sort (Γ : context) : si_Σ ;;; Γ |-E bd_FP ▹□ bd_s1.
Proof.
  econstructor; [|apply rt_refl].
  unfold bd_FP, bd_s1. apply inferE_Prod.
  - exact (bd_vass_s Γ si_na si_P _ (bd_P_sort Γ) eq_refl).
  - exact (bd_P_sort _).
Qed.

Lemma bd_GP_sort (Γ : context) : si_Σ ;;; Γ |-E bd_GP ▹□ Sort.sort_of_product bd_s1 (Sort.super sProp).
Proof.
  econstructor; [|apply rt_refl].
  unfold bd_GP. apply inferE_Prod.
  - exact (bd_vass_s Γ si_na bd_FP _ (bd_FP_sort Γ) eq_refl).
  - exact (bd_P_sort _).
Qed.

Lemma bd_F_prod : si_Σ ;;; bd_ΓFG ,, vass si_na si_P |-E tRel 1 ▹Π (si_na, si_P, si_P).
Proof. econstructor; [exact (inferE_Rel _ (bd_ΓFG ,, vass si_na si_P) 1 (vass si_na bd_FP) eq_refl)|apply rt_refl]. Qed.

Lemma bd_lam_check : si_Σ ;;; bd_ΓFG |-E bd_lam ◃ bd_FP.
Proof.
  econstructor; [|apply JoinE_refl].
  unfold bd_lam. apply inferE_Lambda.
  - exact (bd_vass bd_ΓFG si_na si_P _ (bd_P_sort bd_ΓFG) eq_refl).
  - exact (inferE_App _ _ _ _ _ _ _ bd_F_prod (bd_rel0_check bd_ΓFG)).
Qed.

Lemma bd_G_prod : si_Σ ;;; bd_ΓFG |-E tRel 1 ▹Π (si_na, bd_FP, si_P).
Proof. econstructor; [exact (inferE_Rel _ bd_ΓFG 1 (vass si_na bd_GP) eq_refl)|apply rt_refl]. Qed.

Lemma bd_X_sort : si_Σ ;;; bd_ΓFG |-E bd_X ▹□ sProp.
Proof. econstructor; [exact (inferE_App _ _ _ _ _ _ _ bd_G_prod bd_lam_check)|apply rt_refl]. Qed.

Lemma wf_local_bdE_eta_inst : wf_local_bdE si_Σ bd_Γη.
Proof.
  unfold bd_Γη, bd_ΓFG.
  apply localenv_cons_abs; [|exact (bd_vass _ si_na bd_X _ bd_X_sort eq_refl)].
  apply localenv_cons_abs; [|exact (bd_vass _ si_na bd_FP _ (bd_FP_sort _) eq_refl)].
  apply localenv_cons_abs; [constructor|exact (bd_vass _ si_na bd_GP _ (bd_GP_sort _) eq_refl)].
Qed.

Lemma wf_local_bd_relE_inst : wf_local_bd_relE si_Σ [vass si_na bd_GP] [vass si_na bd_X; vass si_na bd_FP].
Proof.
  unfold All_local_rel.
  apply localenv_cons_abs; [|exact (bd_vass _ si_na bd_X _ bd_X_sort eq_refl)].
  apply localenv_cons_abs; [constructor|exact (bd_vass _ si_na bd_FP _ (bd_FP_sort _) eq_refl)].
Qed.

(** The η step: [G (λ y : Prop. F y)] contracts to [G F], in [bd_Γη]. *)
Definition bd_eta_step : eta1 (tApp (tRel 2) (eta_redex si_na si_P (tRel 1))) (tApp (tRel 2) (tRel 1)) :=
  app_eta_r _ _ (tRel 2) (eta_red si_na (tRel 1) si_P).

Lemma checkingE_eta_inst : si_Σ ;;; bd_Γη |-E tRel 0 ◃ tApp (tRel 2) (tRel 1).
Proof.
  econstructor; [exact (inferE_Rel _ bd_Γη 0 (vass si_na bd_X) eq_refl)|].
  apply JoinE_eta1_l. exact bd_eta_step.
Qed.

(** ** The bridges to the forecast form, on the η pair *)

Lemma checkE_Cumul_ws_inst : si_Σ ;;; bd_Γη |-E tRel 0 ◃ tApp (tRel 2) (tRel 1).
Proof.
  eapply checkE_Cumul_ws; [exact (inferE_Rel _ bd_Γη 0 (vass si_na bd_X) eq_refl)|].
  apply (eta1_ws_cumul_pbE (Σ := si_Σ)); [reflexivity|reflexivity|exact bd_eta_step].
Qed.

Lemma All2_ws_cumul_pbE_JoinE_inst :
  All2 (JoinE si_Σ bd_Γη Conv) [lift0 1 bd_X] [tApp (tRel 2) (tRel 1)].
Proof.
  apply All2_ws_cumul_pbE_JoinE. constructor; [|constructor].
  apply (eta1_ws_cumul_pbE (Σ := si_Σ)); [reflexivity|reflexivity|exact bd_eta_step].
Qed.

Lemma JoinE_ws_cumul_pbE_inst :
  ws_cumul_pbE Cumul si_Σ bd_Γη (lift0 1 bd_X) (tApp (tRel 2) (tRel 1)).
Proof.
  apply JoinE_ws_cumul_pbE; [reflexivity|reflexivity|reflexivity|].
  apply JoinE_eta1_l. exact bd_eta_step.
Qed.

(** ** The (co)fixpoint witness bridges

  The declared type has the domain (fixpoint) or is (cofixpoint) the β-redex
  [(λ B : Prop. I B) A], in [bd_Γ1 = [A : Prop]]; the witness is its reduct [I A].
  The check does not pass on the declared type itself ([bd_check_fix_dtype],
  [bd_check_cofix_dtype]). *)

Definition bd_fix_dom : term := tApp (tLambda si_na si_P (tApp (tInd si_ind []) (tRel 0))) (tRel 0).
Definition bd_fix_dtype : term := tProd si_na bd_fix_dom si_P.
Definition bd_fix_ty : term := tProd si_na (tApp (tInd si_ind []) (tRel 0)) si_P.
Definition bd_fix_d : def term :=
  {| dname := si_na; dtype := bd_fix_dtype; dbody := tLambda si_na bd_fix_dom (tRel 0); rarg := 0 |}.
Definition bd_mfix : mfixpoint term := [bd_fix_d].

Lemma bd_check_fix_dtype : check_one_fix bd_fix_d = None.
Proof. reflexivity. Qed.

Lemma bd_fix_dtype_red : red si_Σ bd_Γ1 bd_fix_dtype bd_fix_ty.
Proof.
  change (red si_Σ bd_Γ1
            (tProd si_na (tApp (tLambda si_na si_P (tApp (tInd si_ind []) (tRel 0))) (tRel 0)) si_P)
            (tProd si_na ((tApp (tInd si_ind []) (tRel 0)) {0 := tRel 0}) si_P)).
  apply rt_step. apply prod_red_l. apply red_beta.
Qed.

Lemma bd_wf_fixpoint_red : wf_fixpoint_red si_Σ bd_Γ1 bd_mfix.
Proof.
  split; [reflexivity|split; [reflexivity|]].
  exists si_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [|constructor].
  exists bd_fix_ty. split; [reflexivity|exact bd_fix_dtype_red].
Qed.

Lemma wf_fixpoint_red_wf_fixpointE_inst : wf_fixpointE si_Σ bd_Γ1 bd_mfix.
Proof.
  refine (@wf_fixpoint_red_wf_fixpointE _ si_Σ si_cb bd_Γ1 bd_mfix _ _ bd_wf_fixpoint_red).
  - reflexivity.
  - constructor; [reflexivity|constructor].
Qed.

(** [si_env] with the block declared coinductive. *)
Definition bd_comdecl : mutual_inductive_body :=
  {| ind_finite := CoFinite; ind_npars := 1; ind_params := si_params; ind_bodies := [si_idecl];
     ind_universes := Monomorphic_ctx; ind_variance := None |}.

Definition bd_coenv : global_env :=
  {| universes := ContextSet.empty; declarations := [(si_kn, InductiveDecl bd_comdecl)];
     retroknowledge := Retroknowledge.empty |}.

Definition bd_coΣ : global_env_ext := (bd_coenv, Monomorphic_ctx).

(** [bd_coenv] declares no constant, and one name. *)
Lemma bd_cocb : ClosedBodies bd_coenv.
Proof.
  apply Build_ClosedBodies.
  - intros cst decl body [h|[]] _. discriminate h.
  - cbn. constructor; [intros []|constructor].
Qed.

Definition bd_cofix_d : def term :=
  {| dname := si_na; dtype := bd_fix_dom; dbody := tRel 0; rarg := 0 |}.

Lemma bd_check_cofix_dtype : check_one_cofix bd_cofix_d = None.
Proof. reflexivity. Qed.

Lemma bd_wf_cofixpoint_red : wf_cofixpoint_red bd_coΣ bd_Γ1 [bd_cofix_d].
Proof.
  exists si_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [|constructor].
  exists (tApp (tInd si_ind []) (tRel 0)). split; [reflexivity|].
  change (red bd_coΣ bd_Γ1 (tApp (tLambda si_na si_P (tApp (tInd si_ind []) (tRel 0))) (tRel 0))
            ((tApp (tInd si_ind []) (tRel 0)) {0 := tRel 0})).
  apply rt_step. apply red_beta.
Qed.

Lemma wf_cofixpoint_red_wf_cofixpointE_inst : wf_cofixpointE bd_coΣ bd_Γ1 [bd_cofix_d].
Proof.
  refine (@wf_cofixpoint_red_wf_cofixpointE _ bd_coΣ bd_cocb bd_Γ1 [bd_cofix_d] _ _ bd_wf_cofixpoint_red).
  - reflexivity.
  - constructor; [reflexivity|constructor].
Qed.

(** *** The typed form: [wfE si_env], [wf_localE si_Σ bd_Γ1], and the declared type
    typed as a type over [typingE] *)

Lemma bd_P_typedE (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E si_P : tSort (Sort.super sProp).
Proof. intros h. apply typeE_Sort; [exact h|cbn; trivial]. Qed.

Lemma bd_wfE_P (Γ : context) : wf_localE si_Σ Γ -> wf_localE si_Σ (Γ ,, vass si_na si_P).
Proof.
  intros h. apply localenv_cons_abs; [exact h|].
  split; [exact tt|]. exists (Sort.super sProp). split; [exact (bd_P_typedE Γ h)|]. split; [exact I|reflexivity].
Qed.

Lemma bd_wfE_Γ1 : wf_localE si_Σ bd_Γ1.
Proof. apply (bd_wfE_P []). constructor. Qed.

Lemma bd_arity_typedE (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ |-E si_arity : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)).
Proof.
  intros h. apply typeE_Prod.
  - split; [exact tt|]. exists (Sort.super sProp). split; [exact (bd_P_typedE Γ h)|]. split; reflexivity.
  - apply typeE_Sort; [exact (bd_wfE_P Γ h)|cbn; trivial].
Qed.

Lemma bd_ind_typedE (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E tInd si_ind [] : si_arity.
Proof.
  intros h. refine (typeE_Ind _ _ si_ind [] si_mdecl si_idecl h si_declared_inductive _).
  reflexivity.
Qed.

(** [I B : Prop] for the last variable [B : Prop]. *)
Lemma bd_Ix0_typedE (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ ,, vass si_na si_P |-E tApp (tInd si_ind []) (tRel 0) : tSort sProp.
Proof.
  intros h. have w := bd_wfE_P Γ h.
  exact (typeE_App _ _ (tInd si_ind []) si_na si_P (tSort sProp) _ (tRel 0)
           (bd_arity_typedE _ w) (bd_ind_typedE _ w) (typeE_Rel _ _ 0 (vass si_na si_P) w eq_refl)).
Qed.

(** [(λ B : Prop. I B) A : Prop] in [bd_Γ1]. *)
Lemma bd_fix_dom_typedE : si_Σ ;;; bd_Γ1 |-E bd_fix_dom : tSort sProp.
Proof.
  have w := bd_wfE_Γ1.
  refine (typeE_App _ _ (tLambda si_na si_P (tApp (tInd si_ind []) (tRel 0))) si_na si_P (tSort sProp) _
            (tRel 0) (bd_arity_typedE _ w) _ (typeE_Rel _ _ 0 (vass si_na si_P) w eq_refl)).
  apply typeE_Lambda.
  - split; [exact tt|]. exists (Sort.super sProp). split; [exact (bd_P_typedE _ w)|]. split; [exact I|reflexivity].
  - exact (bd_Ix0_typedE _ w).
Qed.

Lemma bd_fix_dtype_isTypeE : on_type (lift_typing typingE) si_Σ bd_Γ1 bd_fix_dtype.
Proof.
  have hdom : lift_typing typingE si_Σ bd_Γ1 (j_vass si_na bd_fix_dom).
  { split; [exact tt|]. exists sProp. split; [exact bd_fix_dom_typedE|]. split; [exact I|reflexivity]. }
  split; [exact tt|]. exists (Sort.sort_of_product sProp (Sort.super sProp)). split; [|split; exact I].
  apply typeE_Prod.
  - split; [exact tt|]. exists sProp. split; [exact bd_fix_dom_typedE|]. split; reflexivity.
  - apply typeE_Sort; [|cbn; trivial].
    exact (localenv_cons_abs bd_wfE_Γ1 hdom).
Qed.

Lemma mfix_on_ind_red_convE_inst :
  mfix_on_ind check_one_fix (conv_witnessE si_Σ bd_Γ1)
    (fun mind => check_recursivity_kind (lookup_env si_Σ) mind Finite) bd_mfix.
Proof.
  refine (@mfix_on_ind_red_convE _ si_Σ si_wfE check_one_fix _ bd_Γ1 bd_mfix bd_wfE_Γ1 _ _).
  - constructor; [exact bd_fix_dtype_isTypeE|constructor].
  - exact (snd (snd bd_wf_fixpoint_red)).
Qed.
