(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the hypotheses of the typing copies over [typingE]

  Each instance below applies a lemma of the [typingE] copies of
  [Typing/PCUICWeakeningConfigTyp], [Typing/PCUICRenameTyp], [Typing/PCUICWeakeningTyp],
  [Typing/PCUICCasesWfTyp], [Typing/PCUICInstTyp] and [PCUICGuardClosure], or of the
  closedness lemmas added to [Typing/PCUICClosedTypEta], to a concrete case with
  every premise proved, so the premises are shown to be jointly satisfiable. The
  environments are [si_env] ([PCUICCumulativitySpecEtaClosureInstances]: one inductive
  [I (A : Prop) : Prop] with one constructor, well formed for [wf] and [wfE]) and,
  for the guard, the environment [Σ] of [PCUICGuardCheckerRegress] with its guarded
  cofixpoint [zeros_block]. Where a premise is a conversion or a context
  cumulativity, the instance relates an η-contraction ([cumulSpecE_eta_contract]). *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICEquality PCUICCases PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICCumulativitySpecEtaClosure PCUICClosedBodies PCUICClosedTyp PCUICTypingEta
     PCUICTypingEtaInd PCUICSigmaCalculus PCUICInstDef PCUICRenameDef PCUICRenameConv
     PCUICRenameTyp PCUICInstConv PCUICGuardClosure
     PCUICGuardCondition PCUICCumulativitySpecEtaClosureInstances
     PCUICClosedTypEta PCUICInstDefEta PCUICGuardClosureEta PCUICWeakeningConfigTypEta
     PCUICRenameTypEta PCUICWeakeningTypEta PCUICCasesWfTypEta PCUICInstTypEta.
From MetaRocq.PCUIC Require PCUICGuardCheckerRegress.

Local Open Scope sigma_scope.

(** ** Typing in [si_Σ] over [typingE], under any configuration *)

Lemma cp_vass {cf : checker_flags} (Γ : context) (na : aname) A s :
  si_Σ ;;; Γ |-E A : tSort s -> isSortRel s na.(binder_relevance) ->
  lift_typing typingE si_Σ Γ (j_vass na A).
Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [exact I|exact r]. Qed.

Lemma cp_P_typed {cf : checker_flags} (Γ : context) :
  wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E si_P : tSort (Sort.super sProp).
Proof. intros h. apply typeE_Sort; [exact h|cbn; trivial]. Qed.

Lemma cp_wf_P {cf : checker_flags} (Γ : context) :
  wf_localE si_Σ Γ -> wf_localE si_Σ (Γ ,, vass si_na si_P).
Proof.
  intros h. apply localenv_cons_abs; [exact h|].
  exact (cp_vass _ si_na _ _ (cp_P_typed Γ h) eq_refl).
Qed.

Definition cp_Γ1 : context := [vass si_na si_P].
Definition cp_Γ2 : context := [vass si_na si_P; vass si_na si_P].

Lemma cp_wf_Γ1 {cf : checker_flags} : wf_localE si_Σ cp_Γ1.
Proof. apply (cp_wf_P []). constructor. Qed.

Lemma cp_wf_Γ2 {cf : checker_flags} : wf_localE si_Σ cp_Γ2.
Proof. apply (cp_wf_P cp_Γ1). exact cp_wf_Γ1. Qed.

(** [tRel 0 : P] in [cp_Γ1]. *)
Lemma cp_rel0_typed {cf : checker_flags} : si_Σ ;;; cp_Γ1 |-E tRel 0 : lift0 1 si_P.
Proof. exact (typeE_Rel _ _ 0 (vass si_na si_P) cp_wf_Γ1 eq_refl). Qed.

(** A cofixpoint block whose declared type is [I P] with an η-expanded head; its witness
    for [check_one_cofix] is [I P] itself, related by an η-contraction. *)
Definition cp_dtype : term := tApp (sp_eta (tInd si_ind [])) si_P.
Definition cp_witness : term := tApp (tInd si_ind []) si_P.
Definition cp_block : mfixpoint term :=
  [{| dname := si_na; dtype := cp_dtype; dbody := tRel 0; rarg := 0 |}].

Lemma cp_block_on_ind {cf : checker_flags} Σ :
  mfix_on_ind check_one_cofix (conv_witnessE Σ []) (fun _ => true) cp_block.
Proof.
  exists si_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [|constructor].
  exists cp_witness. split; [reflexivity|]. split; [reflexivity|].
  apply cumulE_App; [apply cumulSpecE_eta_contract|apply cumulE_Refl].
Qed.

(** The same shape over the context [cp_Γ1], with the type [I x] of the context's variable
    [x : Prop], so renaming and instantiation change the block. *)
Definition cp_dtype1 : term := tApp (sp_eta (tInd si_ind [])) (tRel 0).
Definition cp_witness1 : term := tApp (tInd si_ind []) (tRel 0).
Definition cp_block1 : mfixpoint term :=
  [{| dname := si_na; dtype := cp_dtype1; dbody := tRel 0; rarg := 0 |}].

Lemma cp_block1_on_ind {cf : checker_flags} Σ :
  mfix_on_ind check_one_cofix (conv_witnessE Σ cp_Γ1) (fun _ => true) cp_block1.
Proof.
  exists si_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [|constructor].
  exists cp_witness1. split; [reflexivity|]. split; [reflexivity|].
  apply cumulE_App; [apply cumulSpecE_eta_contract|apply cumulE_Refl].
Qed.

(** ** Configuration weakening ([Typing/PCUICWeakeningConfigTypEta]) *)

(** A pair of configurations that are not equal: the default flags, and the same flags
    without universe checking. *)
Lemma cp_config_tit : config.impl default_checker_flags type_in_type.
Proof. reflexivity. Qed.

Lemma weakening_configE_inst :
  @typingE default_checker_flags si_Σ [] si_P (tSort Sort.type1).
Proof.
  apply (@weakening_configE extraction_checker_flags default_checker_flags); [exact sp_config_impl|].
  exact (@typeE_Prop extraction_checker_flags si_Σ).
Qed.

Lemma weakening_config_wf_localE_inst :
  @All_local_env (lift_typing1 (@typingE default_checker_flags si_Σ)) cp_Γ1.
Proof.
  exact (@weakening_config_wf_localE extraction_checker_flags default_checker_flags si_Σ cp_Γ1
           sp_config_impl (@cp_wf_Γ1 extraction_checker_flags)).
Qed.

Lemma weakening_config_wf_local_sizedE_inst :
  @All_local_env (lift_typing1 (@typingE default_checker_flags si_Σ)) cp_Γ1.
Proof.
  exact (@weakening_config_wf_local_sizedE extraction_checker_flags default_checker_flags si_Σ cp_Γ1
           (@cp_wf_Γ1 extraction_checker_flags)
           (fun Γ0 t0 T0 H0 _ =>
              @weakening_configE extraction_checker_flags default_checker_flags _ _ _ _ sp_config_impl H0)).
Qed.

Lemma weakening_config_wfE_inst : @wfE type_in_type si_env.
Proof.
  exact (@weakening_config_wfE default_checker_flags type_in_type si_env cp_config_tit si_wfE).
Qed.

Lemma weakening_config_mfix_on_indE_inst :
  mfix_on_ind check_one_cofix (@conv_witnessE default_checker_flags si_Σ []) (fun _ => true) cp_block.
Proof.
  exact (@weakening_config_mfix_on_indE extraction_checker_flags default_checker_flags si_Σ []
           check_one_cofix (fun _ => true) cp_block sp_config_impl
           (@cp_block_on_ind extraction_checker_flags si_Σ)).
Qed.

#[local] Existing Instance default_checker_flags.

(** ** The guard closure ([PCUICGuardClosureEta]) *)

Definition cp_gΣ : global_env_ext := (PCUICGuardCheckerRegress.Σ, Monomorphic_ctx).
Definition cp_zeros : mfixpoint term := PCUICGuardCheckerRegress.zeros_block.

(** The context of the guard instances, and its η-expanded variant: [λ _ : P. P↑ 0]
    contracts to [P]. *)
Definition cp_gΓ : context := [vass si_na si_P].
Definition cp_gΓ' : context := [vass si_na (sp_eta si_P)].

(** [cofix zeros : Stream := Cons 0 zeros] passes the executable check in a context of
    length one. *)
Lemma cp_zeros_check_ok Γ : #|Γ| = 1 -> check_ok CoFix cp_gΣ Γ cp_zeros.
Proof.
  intros hl. split.
  - vm_compute. reflexivity.
  - exists 30. rewrite hl. vm_compute. reflexivity.
Qed.

Lemma cp_zeros_guarded : guard_cl CoFix cp_gΣ cp_gΓ cp_zeros.
Proof. apply gc_check, cp_zeros_check_ok. reflexivity. Qed.

Lemma cp_ctx_cumul : All2_fold (cumul_decls cumulSpecE0 cp_gΣ) cp_gΓ' cp_gΓ.
Proof.
  constructor; [constructor|].
  constructor; [reflexivity|]. apply cumulSpecE_eta_contract.
Qed.

Lemma guard_cl_context_inst : guard_cl CoFix cp_gΣ [] cp_zeros.
Proof. exact (guard_cl_context CoFix cp_gΣ cp_gΓ [] cp_zeros cp_zeros_guarded). Qed.

Lemma gc_ctxE_inst : guard_cl CoFix cp_gΣ cp_gΓ' cp_zeros.
Proof. exact (gc_ctxE CoFix cp_gΣ cp_gΓ cp_gΓ' cp_zeros (sq cp_ctx_cumul) cp_zeros_guarded). Qed.

Lemma guard_context_cumulativityE_inst : guard CoFix cp_gΣ cp_gΓ' cp_zeros.
Proof.
  exact (guard_context_cumulativityE CoFix cp_gΣ cp_gΓ cp_gΓ' cp_zeros cp_ctx_cumul cp_zeros_guarded).
Qed.

(** A substitution well typed in [typingE]: [Prop] for a variable of type [Type₁]. *)
Definition cp_sΔ : context := [vass si_na (tSort Sort.type1)].
Definition cp_σ : nat -> term := si_P ⋅ ids.

Lemma cp_well_substE Σ : well_substE Σ cp_sΔ cp_σ [].
Proof.
  split.
  - intros x decl hx. destruct x as [|x]; cbn in hx; [|destruct x; discriminate].
    injection hx as <-. cbn. exact (typeE_Prop Σ).
  - intros x decl hx. destruct x as [|x]; cbn in hx; [|destruct x; discriminate].
    injection hx as <-. cbn. intros b hb. discriminate hb.
Qed.

Lemma guard_instE_inst : guard CoFix cp_gΣ [] (inst_mfix cp_zeros cp_σ).
Proof.
  eapply (guard_instE CoFix cp_gΣ [] cp_sΔ cp_zeros cp_σ (cp_well_substE cp_gΣ)).
  - vm_compute. reflexivity.
  - intros x hx. destruct x as [|x]; [reflexivity|cbn in hx; lia].
  - apply gc_check, cp_zeros_check_ok. reflexivity.
Qed.

(** ** Renaming ([Typing/PCUICRenameTypEta]) *)

(** Weakening [cp_Γ1] by one declaration is a renaming in [typingE]. *)
Lemma cp_renamingE : renamingE (shiftnP 1 xpred0) si_Σ cp_Γ1 cp_Γ2 (rshiftk 1).
Proof. split; [exact cp_wf_Γ2|]. exact (urenaming_lift0 _ cp_Γ1 [vass si_na si_P]). Qed.

Lemma typing_rename_PE_inst :
  si_Σ ;;; cp_Γ2 |-E rename (rshiftk 1) (tRel 0) : rename (rshiftk 1) (lift0 1 si_P).
Proof. exact (@typing_rename_PE _ xpred0 si_Σ cp_Γ1 cp_Γ2 _ _ _ si_wfE cp_renamingE cp_rel0_typed). Qed.

Lemma typing_renameE_inst :
  si_Σ ;;; cp_Γ2 |-E rename (rshiftk 1) (tRel 0) : rename (rshiftk 1) (lift0 1 si_P).
Proof.
  exact (typing_renameE (Σ := si_Σ) si_wfE cp_wf_Γ2 (urenaming_lift0 _ cp_Γ1 [vass si_na si_P])
           cp_rel0_typed).
Qed.

(** Renaming [cp_Γ1] into [cp_Γ2] shifts the variable of [cp_block1]'s type. *)
Lemma rename_mfix_on_indE_inst :
  mfix_on_ind check_one_cofix (conv_witnessE si_Σ cp_Γ2) (fun _ => true)
    (map (map_def (rename (rshiftk 1)) (rename (shiftn #|cp_block1| (rshiftk 1)))) cp_block1).
Proof.
  eapply (@rename_mfix_on_indE _ si_Σ si_cb xpred0 cp_Γ1 cp_Γ2 (rshiftk 1)).
  - exact (rename_check_one_cofix (rshiftk 1) cp_block1).
  - exact (urenaming_lift0 _ cp_Γ1 [vass si_na si_P]).
  - reflexivity.
  - reflexivity.
  - constructor; [reflexivity|constructor].
  - exact (cp_block1_on_ind si_Σ).
Qed.

(** The predicate of a [match] on [I P] returning [P]. *)
Definition cp_pred : predicate term :=
  {| pparams := [si_P]; puinst := []; pcontext := [vass si_na (tInd si_ind [])]; preturn := si_P |}.

Lemma cp_wf_pred : wf_predicate si_mdecl si_idecl cp_pred.
Proof. split; [reflexivity|]. constructor; [reflexivity|constructor]. Qed.

Lemma rename_case_predicate_contextE_inst :
  rename_context (rshiftk 1) (case_predicate_context si_ind si_mdecl si_idecl cp_pred) =
  case_predicate_context si_ind si_mdecl si_idecl (rename_predicate (rshiftk 1) cp_pred).
Proof.
  exact (@rename_case_predicate_contextE _ si_Σ si_wfE _ _ _ _ _ si_declared_inductive cp_wf_pred).
Qed.

(** ** Weakening ([Typing/PCUICWeakeningTypEta]) *)

Lemma weakening_typingE_inst :
  si_Σ ;;; [] ,,, cp_Γ1 ,,, lift_context #|cp_Γ1| 0 cp_Γ1 |-E
    lift #|cp_Γ1| #|cp_Γ1| (tRel 0) : lift #|cp_Γ1| #|cp_Γ1| (lift0 1 si_P).
Proof.
  exact (@weakening_typingE _ si_Σ si_wfE [] cp_Γ1 cp_Γ1 _ _ cp_wf_Γ1 cp_rel0_typed).
Qed.

Lemma weakeningE_inst :
  si_Σ ;;; cp_Γ1 ,,, [vass si_na si_P] |-E lift0 1 (tRel 0) : lift0 1 (lift0 1 si_P).
Proof. exact (weakeningE si_Σ cp_Γ1 [vass si_na si_P] _ _ si_wfE cp_wf_Γ2 cp_rel0_typed). Qed.

(** ** Case well-formedness ([Typing/PCUICCasesWfTypEta]) *)

Lemma wfE_wf_cases_env_inst : wf_cases_env si_env.
Proof. exact (@wfE_wf_cases_env _ si_env si_wfE). Qed.

Lemma subject_wf_casesE_inst : wf_cases si_Σ.1 (tRel 0).
Proof. exact (@subject_wf_casesE _ si_Σ si_wfE _ _ _ cp_rel0_typed). Qed.

Lemma well_substE_wf_cases_inst : wf_cases si_Σ.1 (cp_σ 0).
Proof. exact (@well_substE_wf_cases _ si_Σ si_wfE _ _ _ (cp_well_substE si_Σ) 0 ltac:(cbn; lia)). Qed.

(** ** Instantiation ([Typing/PCUICInstTypEta]) *)

(** [tRel 0 : Type₁] in [cp_sΔ], instantiated by [cp_σ] to [Prop : Type₁]. *)
Lemma cp_wf_sΔ : wf_localE si_Σ cp_sΔ.
Proof.
  apply localenv_cons_abs; [constructor|].
  apply (cp_vass _ si_na _ (Sort.super Sort.type1)); [|reflexivity].
  apply typeE_Sort; [constructor|].
  cbn. intros l hin%LevelExprSet.singleton_spec. subst l. cbn.
  apply global_ext_levels_InSet.
Qed.

Lemma typing_instE_inst : si_Σ ;;; [] |-E (tRel 0).[cp_σ] : (lift0 1 (tSort Sort.type1)).[cp_σ].
Proof.
  eapply (@typing_instE _ si_Σ cp_sΔ (tRel 0) _ [] cp_σ si_wfE).
  - constructor.
  - exact (cp_well_substE si_Σ).
  - exact (typeE_Rel _ _ 0 _ cp_wf_sΔ eq_refl).
Qed.

Lemma well_subst_UpE_inst :
  well_substE si_Σ (cp_sΔ ,, vass si_na si_P) (⇑ cp_σ) ([] ,, vass si_na si_P.[cp_σ]).
Proof.
  apply (@well_subst_UpE _ si_Σ si_wfE).
  - exact (cp_wf_P [] (localenv_nil)).
  - exact (cp_well_substE si_Σ).
Qed.

(** Instantiating [cp_Γ1]'s variable by [Prop] closes [cp_block1]'s type. *)
Lemma inst_mfix_on_indE_inst :
  mfix_on_ind check_one_cofix (conv_witnessE si_Σ []) (fun _ => true)
    (map (map_def (inst cp_σ) (inst (up #|cp_block1| cp_σ))) cp_block1).
Proof.
  eapply (@inst_mfix_on_indE _ si_Σ si_cb cp_Γ1 [] cp_σ).
  - exact (inst_check_one_cofix cp_σ cp_block1).
  - split; [reflexivity|split].
    + intros x decl hx. destruct x as [|x]; [reflexivity|destruct x; discriminate].
    + intros x decl hx. destruct x as [|x]; [|destruct x; discriminate].
      injection hx as <-. intros b hb. discriminate hb.
  - reflexivity.
  - constructor; [reflexivity|constructor].
  - exact (cp_block1_on_ind si_Σ).
Qed.

(** ** Closedness of declarations ([Typing/PCUICClosedTypEta]) *)

Lemma si_declared_inductive_closed_typeE : closed si_idecl.(ind_type).
Proof. exact (declared_inductive_closed_typeE si_Σ si_mdecl si_ind si_idecl si_wfE si_declared_inductive). Qed.

Lemma si_declared_inductive_closed_paramsE : closed_ctx si_mdecl.(ind_params).
Proof. exact (@declared_inductive_closed_paramsE _ si_Σ _ _ _ si_wfE si_declared_inductive). Qed.

Lemma si_declared_constructor_closed_typeE :
  closed (type_of_constructor si_mdecl si_cdecl (si_ind, 0) []).
Proof. exact (@declared_constructor_closed_typeE _ si_Σ _ _ _ _ [] si_wfE si_declared_constructor). Qed.

Lemma si_closed_cstr_branch_contextE :
  closedn_ctx (context_assumptions si_mdecl.(ind_params)) (cstr_branch_context si_ind si_mdecl si_cdecl).
Proof. exact (@closed_cstr_branch_contextE _ si_Σ si_wfE _ _ _ _ _ si_declared_constructor). Qed.

Lemma si_isTypeRel_closedE : closedn #|cp_Γ1| si_P.
Proof.
  exact (@isTypeRel_closedE _ si_Σ si_wfE _ _ _
           (cp_vass cp_Γ1 si_na si_P _ (cp_P_typed cp_Γ1 cp_wf_Γ1) eq_refl)).
Qed.
